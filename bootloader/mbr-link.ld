ENTRY(_start)
PHDRS {
    data PT_LOAD;
}

SECTIONS {
    .data 0x10000: {
        *(.text.init);
        *(.text);
        *(.rodata);
        *(.data);
        . = 0x1BE;
        WORD(0);
        . = 0x1FE;
        SHORT(0xAA55);
    }
}