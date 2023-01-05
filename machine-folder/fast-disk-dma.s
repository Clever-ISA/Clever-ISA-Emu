
.section .rodata.enumerate
.quad enumerate_dma_disks

.text

read_dma_disk:
    and r2, short 0xFF
    

enumerate_dma_disk:
    mov r4, r1
    mov r1, 0x100000001
    in byte # Don't care about capabilities in the bootloader, just get the device count
    mov r2, 0x100000000000001
    test r0, r0
    jz enumerate_dma_disk._L1
    enumerate_dma_disk._L0:
    





.bss
dma_buff:
.space 1024