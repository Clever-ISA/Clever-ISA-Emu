.text
_start:
    lea r8, [half __part_table_start+ip]
    mov r1, r0
    mov r9, 0
    mov r10, 9
    mov r11, 4
    _start._L0:
    mov r0, byte [r8+4]
    test byte r0, short 0x11
    jnz _start._L1
    lea r8, [r8+16]
    sub r11, 1
    jnz _start._L0
    jmp _hlt
    _start._L1:
    mov r0, single [r8+8]
    lsh r0, 9
    lea r2, [single __read_area+ip]
    mov r3, 512
    fcall
    mov r1, r0
    


    
.rodata
stage2_partty:
// 132eca04-8ddc-11ed-a729-bbae30dd5404
.quad 11ed8ddc132eca04
.quad bbae30dd5404a729