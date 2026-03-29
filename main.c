#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <capstone.h>

#ifdef _WIN32
#include <io.h>
#include <fcntl.h>
#endif

#include "ndsdisasm.h"

struct ConfigLabel
{
    uint32_t addr;
    uint8_t type;
    const char *label;
};

uint8_t *gInputFileBuffer;
size_t gInputFileBufferSize;
uint32_t gRomStart;
uint32_t gRamStart;
bool isFullRom = true;
bool isArm7 = false;
bool dumpUnDisassembled = false;
int AutoloadNum = -1;
int ModuleNum = -1;
uint32_t CompressedStaticEnd = 0;
const char * outwriteFileName = NULL;

const char * functionPrefix = "FUN_";
const char * dataPrefix = "UNK_";
bool functionPrefixOverridden = false;
bool dataPrefixOverridden = false;

#define READ32(p) ((p)[0] | ((p)[1] << 8) | ((p)[2] << 16) | ((p)[3] << 24))
#define max(x, y) ((x) > (y) ? (x) : (y))
#define min(x, y) ((x) < (y) ? (x) : (y))

static void MIi_UncompressBackwards()
{
    if (CompressedStaticEnd == 0)                                              //     cmp r0, #0
        return;                                                                //     beq @.end
                                                                               //     stmfd sp!, {r4-r7}
    // Read the pointer to the end of the compressed image
    uint8_t * endptr = gInputFileBuffer + CompressedStaticEnd - gRamStart - 8; //     ldmdb r0, {r1, r2}
    uint32_t size = READ32(endptr);
    uint32_t offset = READ32(endptr + 4);
    gInputFileBufferSize = max(CompressedStaticEnd - gRamStart + offset, gInputFileBufferSize);
    gInputFileBuffer = realloc(gInputFileBuffer, gInputFileBufferSize);
    endptr = gInputFileBuffer + CompressedStaticEnd - gRamStart;
    uint8_t * dest_p = endptr + offset;                                        //     add r2, r0, r2
    uint8_t * end = endptr - ((uint8_t)(size >> 24));                          //     sub r3, r0, r1, lsr #24
                                                                               //     bic r1, r1, #0xff000000
    uint8_t * start = endptr - (size & ~0xFF000000);                           //     sub r1, r0, r1
    // uint8_t * dest_end = dest_p;
                                                                               //     mov r4, r2 ; not crucial
                                                                               // @.loop:
    while (end > start)                                                        //     cmp r3, r1
    {                                                                          //     ble @.dc_flush
        uint8_t r5 = *--end;                                                   //     ldrb r5, [r3, #-1]!
                                                                               //     mov r6, #8
                                                                               // @.byte_loop:
        for (int i = 0; i < 8; i++)                                            //     subs r6, r6, #1
        {                                                                      //     blt @.loop
            if ((r5 & 0x80) == 0)                                              //     tst r5, #0x80
            {                                                                  //     bne @.readback
                                                                               //     ldrb r0, [r3, #-1]!
                *--dest_p = *--end;                                            //     strb r0, [r2, #-1]!
            }                                                                  //     b @.byte_after
            else                                                               // @.readback:
            {
                int ip = *--end;                                               //     ldrb r12, [r3, #-1]!
                int r7 = *--end;                                               //     ldrb r7, [r3, #-1]!
                                                                               //     orr r7, r7, r12, lsl #8
                                                                               //     bic r7, r7, #0xf000
                r7 = ((r7 | (ip << 8)) & ~0xF000) + 2;                         //     add r7, r7, #0x0002
                ip += 0x20;                                                    //     add r12, r12, #0x0020
                while (ip >= 0)                                                // @.readback_loop:
                {
                    dest_p[-1] = dest_p[r7];                                   //     ldrb r0, [r2, r7]
                    dest_p--;                                                  //     strb r0, [r2, -1]!
                    ip -= 0x10;                                                //     subs r12, r12, #0x0010
                }                                                              //     bge @.readback_loop
            }                                                                  // @.byte_after:
            if (end <= start)                                                  //     cmp r3, r1
                break;                                                         //     mov r5, r5, lsl #1
            r5 <<= 1;                                                          //     bgt @.byte_loop
        }                                                                      // @.dc_flush:
    }
}

static uint32_t FindUncompressCall(FILE * file, uint32_t entry)
{
    static uint8_t code[0x1000];

    csh cap;
    cs_insn * insn;
    cs_open(CS_ARCH_ARM, CS_MODE_ARM, &cap);
    cs_option(cap, CS_OPT_DETAIL, CS_OPT_ON);
    fseek(file, entry - gRamStart + gRomStart, SEEK_SET);
    if (fread(code, 1, 0x1000, file) != 0x1000)
        fatal_error("read code");
    int count;
    int offset = 0;
    do {
        count = cs_disasm(cap, code + offset, 0x1000 - offset, entry + offset, 0x1000, &insn);
        if (count < 4)
        {
            offset += 4 * (count + 1);
            continue;
        }
        for (int i = 0; i < count - 4; i++)
        {
            cs_insn *cur_insn = &insn[i];
            if (
                // ldr rX, [pc, #YYY]
                cur_insn[0].id == ARM_INS_LDR
                && cur_insn[0].detail->arm.operands[1].type == ARM_OP_MEM
                && cur_insn[0].detail->arm.operands[1].mem.base == ARM_REG_PC
                // ldr r0, [rX, #20]
                && cur_insn[1].id == ARM_INS_LDR
                && cur_insn[1].detail->arm.operands[0].reg == ARM_REG_R0
                && cur_insn[1].detail->arm.operands[1].type == ARM_OP_MEM
                && cur_insn[1].detail->arm.operands[1].mem.base == (arm_reg) cur_insn[0].detail->arm.operands[0].reg
                && cur_insn[1].detail->arm.operands[1].mem.disp == 20
                // bl MIi_UncompressBackwards
                && cur_insn[2].id == ARM_INS_BL
                )
            {
                uint32_t pool_addr = cur_insn[0].address + cur_insn[0].detail->arm.operands[1].mem.disp + 8;
                uint32_t _start_ModuleParams_off = READ32(&code[pool_addr - entry]);
                CompressedStaticEnd = READ32(&code[_start_ModuleParams_off - entry + 20]);
                cs_close(&cap);
                cs_free(insn, count);
                return _start_ModuleParams_off;
            }
            else if (
                // ldr r0, =_start_ModuleParams
                cur_insn[0].id == ARM_INS_LDR
                && cur_insn[0].detail->arm.operands[0].reg == ARM_REG_R0
                && cur_insn[0].detail->arm.operands[1].type == ARM_OP_MEM
                && cur_insn[0].detail->arm.operands[1].mem.base == ARM_REG_PC
                // ldr r1, [r0]
                && cur_insn[1].id == ARM_INS_LDR
                && cur_insn[1].detail->arm.operands[0].reg == ARM_REG_R1
                && cur_insn[1].detail->arm.operands[1].type == ARM_OP_MEM
                && cur_insn[1].detail->arm.operands[1].mem.base == ARM_REG_R0
                && cur_insn[1].detail->arm.operands[1].mem.disp == 0
                // ldr r2, [r0, #4]
                && cur_insn[2].id == ARM_INS_LDR
                && cur_insn[2].detail->arm.operands[0].reg == ARM_REG_R2
                && cur_insn[2].detail->arm.operands[1].type == ARM_OP_MEM
                && cur_insn[2].detail->arm.operands[1].mem.base == ARM_REG_R0
                && cur_insn[2].detail->arm.operands[1].mem.disp == 4
                // ldr r3, [r0, #8]
                && cur_insn[3].id == ARM_INS_LDR
                && cur_insn[3].detail->arm.operands[0].reg == ARM_REG_R3
                && cur_insn[3].detail->arm.operands[1].type == ARM_OP_MEM
                && cur_insn[3].detail->arm.operands[1].mem.base == ARM_REG_R0
                && cur_insn[3].detail->arm.operands[1].mem.disp == 8
                )
            {
                uint32_t pool_addr = cur_insn[0].address + cur_insn[0].detail->arm.operands[1].mem.disp + 8;
                cs_close(&cap);
                cs_free(insn, count);
                return READ32(&code[pool_addr - entry]);
            }
        }
        offset = insn[count - 1].address + insn[count - 1].size - entry;
        cs_free(insn, count);
    } while (offset < 0x800);
    cs_close(&cap);
    return 0;
}

static void read_input_file(const char *fname)
{
    FILE *file = fopen(fname, "rb");

    if (file == NULL)
        fatal_error("could not open input file '%s'", fname);
    if (isFullRom) {
        uint32_t entry;
        fseek(file, 0x20 + 0x10 * isArm7, SEEK_SET);
        if (fread(&gRomStart, 4, 1, file) != 1)
            fatal_error("read gRomStart");
        if (fread(&entry, 4, 1, file) != 1)
            fatal_error("read entry");
        if (fread(&gRamStart, 4, 1, file) != 1)
            fatal_error("read gRamStart");
        if (fread(&gInputFileBufferSize, 4, 1, file) != 1)
            fatal_error("read gInputFileBufferSize");
        FindUncompressCall(file, entry);
    } else if (ModuleNum != -1) {
        uint32_t fat_offset, fat_size, ovy_offset, ovy_size, ovyfile, reserved;
        fseek(file, 0x48, SEEK_SET);
        if (fread(&fat_offset, 4, 1, file) != 1)
            fatal_error("read fat_offset");
        if (fread(&fat_size, 4, 1, file) != 1)
            fatal_error("read fat_size");
        fseek(file, 0x50 + 8 * isArm7, SEEK_SET);
        if (fread(&ovy_offset, 4, 1, file) != 1)
            fatal_error("read ovy_offset");
        if (fread(&ovy_size, 4, 1, file) != 1)
            fatal_error("read ovy_size");
        if (ModuleNum * 32u > ovy_size)
            fatal_error("Argument to -m is out of range for ARM%d target", isArm7 ? 7 : 9);
        fseek(file, ovy_offset + ModuleNum * 32 + 4, SEEK_SET);
        if (fread(&gRamStart, 4, 1, file) != 1)
            fatal_error("read gRamStart");
        if (fread(&gInputFileBufferSize, 4, 1, file) != 1)
            fatal_error("read gInputFileBufferSize");
        fseek(file, 12, SEEK_CUR); // bss_size, sinit_start, sinit_end
        if (fread(&ovyfile, 4, 1, file) != 1)
            fatal_error("read ovyfile");
        if (fread(&reserved, 4, 1, file) != 1)
            fatal_error("read reserved");
        fseek(file, fat_offset + ovyfile * 8, SEEK_SET);
        if (fread(&gRomStart, 4, 1, file) != 1)
            fatal_error("read gRomStart");
        if ((reserved >> 24) & 1) {
            CompressedStaticEnd = gRamStart + (reserved & 0xFFFFFF);
        }
    } else if (AutoloadNum != -1) {
        uint32_t offset, entry, addr;
        fseek(file, 0x20 + 0x10 * isArm7, SEEK_SET);
        if (fread(&offset, 4, 1, file) != 1)
            fatal_error("read offset");
        if (fread(&entry, 4, 1, file) != 1)
            fatal_error("read entry");
        if (fread(&addr, 4, 1, file) != 1)
            fatal_error("read addr");
        if (fread(&gInputFileBufferSize, 4, 1, file) != 1)
            fatal_error("read gInputFileBufferSize");
        gRomStart = offset;
        gRamStart = addr;
        uint32_t start_ModuleParams = FindUncompressCall(file, entry);

        fseek(file, offset, SEEK_SET);
        gInputFileBuffer = malloc(gInputFileBufferSize);
        if (gInputFileBuffer == NULL)
            fatal_error("failed to alloc file buffer for '%s'", fname);
        if (fread(gInputFileBuffer, 1, gInputFileBufferSize, file) != gInputFileBufferSize)
            fatal_error("failed to read from file '%s'", fname);
        MIi_UncompressBackwards();

        fseek(file, entry - addr + offset + (isArm7 ? 0x198 : 0x368), SEEK_SET);
        uint32_t autoload_start, autoload_end, first_autoload;
        autoload_start = READ32(gInputFileBuffer + start_ModuleParams - addr);
        autoload_end = READ32(gInputFileBuffer + start_ModuleParams + 4 - addr);
        first_autoload = READ32(gInputFileBuffer + start_ModuleParams + 8 - addr);
        
        gRomStart = first_autoload - addr + offset;
        if ((autoload_end - autoload_start) / 12 <= (uint32_t)AutoloadNum)
            fatal_error("Argument to -a is out of range for ARM%d target", isArm7 ? 7 : 9);
        fseek(file, autoload_start - addr + offset, SEEK_SET);
        for (int i = 0; i < AutoloadNum; i++) {
            gRomStart += READ32(gInputFileBuffer + 12 * i + 4 + autoload_start - addr);
        }
        gRamStart = READ32(gInputFileBuffer + 12 * AutoloadNum + autoload_start - addr);
        gInputFileBufferSize = READ32(gInputFileBuffer + 12 * AutoloadNum + autoload_start + 4 - addr);

        uint8_t * tmp_buffer = malloc(gInputFileBufferSize);
        if (tmp_buffer == NULL)
            fatal_error("failed to alloc final buffer for '%s' autoload %d", fname, AutoloadNum);
        memcpy(tmp_buffer, gInputFileBuffer + gRomStart - offset, gInputFileBufferSize);
        free(gInputFileBuffer);
        gInputFileBuffer = tmp_buffer;
        goto done;
    } else {
        fseek(file, 0, SEEK_END);
        gInputFileBufferSize = ftell(file);
        gRamStart = 0;
        gRomStart = 0;
    }
    fseek(file, gRomStart, SEEK_SET);
    gInputFileBuffer = malloc(gInputFileBufferSize);
    if (gInputFileBuffer == NULL)
        fatal_error("failed to alloc file buffer for '%s'", fname);
    if (fread(gInputFileBuffer, 1, gInputFileBufferSize, file) != gInputFileBufferSize)
        fatal_error("failed to read from file '%s'", fname);
    fclose(file);
    MIi_UncompressBackwards();
  done:
    if (outwriteFileName != NULL)
    {
        FILE *sbinfile = fopen(outwriteFileName, "wb");
        if (sbinfile == NULL)
        {
            fatal_error("failed to open uncompress dump destination for writing\n");
        }
        if (fwrite(gInputFileBuffer, 1, gInputFileBufferSize, sbinfile) != gInputFileBufferSize)
        {
            fatal_error("error writing uncompress dump");
        }
        fclose(sbinfile);
    }
}

static char *split_word(char *s)
{
    while (!isspace(*s))
    {
        if (*s == '\0')
            return s;
        s++;
    }
    *s++ = '\0';
    while (isspace(*s))
        s++;
    return s;
}

static char *split_line(char *s)
{
    while (*s != '\n' && *s != '\r')
    {
        if (*s == '\0')
            return s;
        s++;
    }
    *s++ = '\0';
    while (*s == '\n' || *s == '\r')
        s++;
    return s;
}

static char *skip_whitespace(char *s)
{
    while (isspace(*s))
        s++;
    return s;
}

static void read_config(const char *fname)
{
    FILE *file = fopen(fname, "rb");
    char *buffer;
    size_t size;
    char *line;
    char *next;
    int lineNum = 1;

    if (file == NULL)
        fatal_error("could not open config file '%s'", fname);
    fseek(file, 0, SEEK_END);
    size = ftell(file);
    fseek(file, 0, SEEK_SET);
    buffer = malloc(size + 1);
    if (buffer == NULL)
        fatal_error("could not alloc buffer for '%s'", fname);
    if (fread(buffer, 1, size, file) != size)
        fatal_error("failed to read from file '%s'", fname);
    buffer[size] = '\0';
    fclose(file);

    for (line = next = buffer; *line != '\0'; line = next, lineNum++)
    {
        char *tokens[3];
        char *name = NULL;
        int i;

        next = split_line(line);

        tokens[0] = line = skip_whitespace(line);
        for (i = 1; i < 3; i++)
            tokens[i] = line = split_word(line);

        if (tokens[0][0] == '#')
            continue;
        if (strcmp(tokens[0], "arm_func") == 0)
        {
            int addr;

            if (sscanf(tokens[1], "%i", &addr) == 1)
            {
                if (strlen(tokens[2]) != 0)
                    name = strdup(tokens[2]);
                disasm_add_label(addr, LABEL_ARM_CODE, name, true);
            }
            else
            {
                fatal_error("%s: syntax error on line %i", fname, lineNum);
            }
        }
        else if (strcmp(tokens[0], "thumb_func") == 0)
        {
            int addr;

            if (sscanf(tokens[1], "%i", &addr) == 1)
            {
                if (strlen(tokens[2]) != 0)
                    name = strdup(tokens[2]);
                disasm_add_label(addr, LABEL_THUMB_CODE, name, true);
            }
            else
            {
                fatal_error("%s: syntax error on line %i", fname, lineNum);
            }
        }
        else if (strcmp(tokens[0], "data") == 0)
        {
            int addr;

            if (sscanf(tokens[1], "%i", &addr) == 1)
            {
                if (strlen(tokens[2]) != 0)
                    name = strdup(tokens[2]);
                disasm_add_label(addr, LABEL_DATA, name, true);
            }
            else
            {
                fatal_error("%s: syntax error on line %i", fname, lineNum);
            }
        }
        else if (strcmp(tokens[0], "ascii") == 0)
        {
            int addr;

            if (sscanf(tokens[1], "%i", &addr) == 1)
            {
                if (strlen(tokens[2]) != 0)
                    name = strdup(tokens[2]);
                disasm_add_label(addr, LABEL_ASCII, name, true);
            }
            else
            {
                fatal_error("%s: syntax error on line %i", fname, lineNum);
            }
        }
        else if (strcmp(tokens[0], "prefix") == 0)
        {
            bool isValidSecondToken = strlen(tokens[2]) != 0;
            if (strcmp(tokens[1], "function") == 0)
            {
                if (!isValidSecondToken)
                    fatal_error("%s: missing second argument to prefix command on line %i", fname, lineNum);
                if (functionPrefixOverridden)
                {
                    fprintf(stderr, "%s: warning: duplicate \"prefix function\" command supercedes earlier ones on line %i\n", fname, lineNum);
                    free((char*)functionPrefix);
                }
                functionPrefix = strdup(tokens[2]);
                functionPrefixOverridden = true;
            }
            else if (strcmp(tokens[1], "data") == 0)
            {
                if (!isValidSecondToken)
                    fatal_error("%s: missing second argument to prefix command on line %i", fname, lineNum);
                if (dataPrefixOverridden)
                {
                    fprintf(stderr, "%s: warning: duplicate \"prefix data\" command supercedes earlier ones on line %i\n", fname, lineNum);
                    free((char*)dataPrefix);
                }
                dataPrefix = strdup(tokens[2]);
                dataPrefixOverridden = true;
            }
            else
            {
                fatal_error("%s: missing first argument to prefix command on line %i", fname, lineNum);
            }
        }
        else
        {
            fprintf(stderr, "%s: warning: unrecognized command '%s' on line %i\n", fname, tokens[0], lineNum);
        }
    }

    free(buffer);
}

static void usage(const char * program)
{
    printf("NDSDISASM v%d.%d.%d using libcapstone v%d.%d.%d\n\n"
           "USAGE: %s -c CONFIG [-m OVERLAY] [-a AUTOLOAD] [-7] [-h] [-d] [-Du] ROM\n\n"
           "    ROM        \tfile to disassemble\n"
           "    -c CONFIG  \tspace-delimited file with function types, offsets, and optionally names\n"
           "    -m OVERLAY \tDisassemble the overlay by index\n"
           "    -a AUTOLOAD\tDisassemble the autoload by index\n"
           "    -7         \tDisassemble the ARM7 binary\n"
           "    -d         \tDump remaining data as raw bytes\n"
           "    -h         \tPrint this message and exit\n"
           "    -Du BINFILE\tDump the (uncompressed) binary to file\n",
           NDSDISASM_VERMAJ,NDSDISASM_VERMIN,NDSDISASM_VERSTP,
           CS_VERSION_MAJOR,CS_VERSION_MINOR,CS_VERSION_EXTRA,
           program);
}

int main(int argc, char **argv)
{
    int i;
    const char *romFileName = NULL;
    const char *configFileName = NULL;
    //ROM_LOAD_ADDR = 0x08000000;

#ifdef _WIN32
    // Work around MinGW bug that prevents us from seeing the assert message
    setvbuf(stdout, NULL, _IONBF, 0);
    setvbuf(stderr, NULL, _IONBF, 0);
    _setmode(_fileno(stdout), _O_BINARY);
#endif

    for (i = 1; i < argc; i++)
    {
        if (strcmp(argv[i], "-c") == 0)
        {
            if (i + 1 >= argc)
            {
                usage(argv[0]);
                fatal_error("expected filename for option -c");
            }
            i++;
            configFileName = argv[i];
        }
        else if (strcmp(argv[i], "-h") == 0)
        {
            usage(argv[0]);
            exit(0);
        }
        else if (strcmp(argv[i], "-m") == 0)
        {
            if (!isFullRom)
            {
                usage(argv[0]);
                fatal_error("can't specify more than one of the following together: -a, -m, -O");
            }
            char * endptr;
            i++;
            if (i >= argc)
            {
                usage(argv[0]);
                fatal_error("expected integer for option -m");
            }
            ModuleNum = strtol(argv[i], &endptr, 0);
            if (ModuleNum == 0 && endptr == argv[i])
            {
                usage(argv[0]);
                fatal_error("Invalid integer value for option -m");
            }
            isFullRom = false;
        }
        else if (strcmp(argv[i], "-7") == 0)
        {
            isArm7 = true;
        }
        else if (strcmp(argv[i], "-a") == 0)
        {
            if (!isFullRom)
            {
                usage(argv[0]);
                fatal_error("can't specify more than one of the following together: -a, -m, -O");
            }
            char * endptr;
            i++;
            if (i >= argc)
            {
                usage(argv[0]);
                fatal_error("expected integer for option -a");
            }
            AutoloadNum = strtol(argv[i], &endptr, 0);
            if (AutoloadNum == 0 && endptr == argv[i])
            {
                usage(argv[0]);
                fatal_error("Invalid integer value for option -a");
            }
            isFullRom = false;
        }
        else if (strcmp(argv[i], "-O") == 0)
        {
            if (!isFullRom)
            {
                usage(argv[0]);
                fatal_error("can't specify more than one of the following together: -a, -m, -O");
            }
            isFullRom = false;
        }
        else if (strcmp(argv[i], "-d") == 0)
        {
            dumpUnDisassembled = true;
        }
        else if (strcmp(argv[i], "-Du") == 0)
        {
            ++i;
            if (i >= argc)
            {
                usage(argv[0]);
                fatal_error("missing filename argument to -Du");
            }
            outwriteFileName = argv[i];
        }
        else
        {
            romFileName = argv[i];
        }
    }

    if (romFileName == NULL)
    {
        usage(argv[0]);
        fatal_error("no ROM file specified");
    }
    read_input_file(romFileName);
    ROM_LOAD_ADDR = gRamStart;
    if (configFileName != NULL)
    {
        read_config(configFileName);
        disasm_disassemble();
    }
    else if (outwriteFileName == NULL)
    {
        usage(argv[0]);
        fatal_error("config file required");
    }
    free(gInputFileBuffer);
    return 0;
}
