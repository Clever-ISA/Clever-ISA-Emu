
.global __machine_serial_write

__machine_serial_write:
    test r4,r4
    jz __machine_serial_write._L0
    mov r1, r4
    mov r4, r5
    mov r2, 0x100000000
    repc out byte
    __machine_serial_write._L0:
    ret