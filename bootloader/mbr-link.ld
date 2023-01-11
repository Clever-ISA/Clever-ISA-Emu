ENTRY(_start)
PHDRS {
    text PT_LOAD;
    data PT_LOAD;
}

SECTIONS {
    .data 0x10000: {
        mbr/main.o(.text.init);
        *(.text);
        *(.rodata);
        *(.data);
        . = 0x1BE;
        __part_table_start = .;
        WORD(0);
        . = 0x1FE;
        SHORT(0xAA55);
    }



    .bss 0x20000: {
        *(.bss);
    }
}