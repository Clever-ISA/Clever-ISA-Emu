
TARGET := clever-elf

BFD_NAME := elf64-clever

AS := $(TARGET)-as
LD := $(TARGET)-ld 
OBJCOPY := $(TARGET)-objcopy
STRIP := $(TARGET)-strip

MBR_OBJS = mbr/main.o

STAGE2_OBJS = 

MBR_OUTPUT = boot-mbr

STAGE2_OUTPUT = boot-stage2

OUTPUTS = $(MBR_OUTPUT)

ifndef DISABLE_STAGE2
	OUTPUTS += $(STAGE2_OUTPUT)
endif

all: stamp

stamp: $(OUTPUTS)
	touch stamp

$(MBR_OUTPUT): $(MBR_OUTPUT).elf $(MBR_OUTPUT).dbg
	$(OBJCOPY) -I $(BFD_NAME) -O binary --remove-section .bss --strip-debug $(MBR_OUTPUT).elf $(MBR_OUTPUT)

$(MBR_OUTPUT).dbg: $(MBR_OUTPUT).elf
	$(OBJCOPY) --only-keep-debug $(MBR_OUTPUT).elf $(MBR_OUTPUT).dbg

$(MBR_OUTPUT).elf: $(MBR_OBJS) mbr-link.ld
	$(LD) -T mbr-link.ld -o $(MBR_OUTPUT).elf $(MBR_OBJS)

$(STAGE2_OUTPUT): $(STAGE2_OUTPUT).elf $(STAGE2_OUTPUT).dbg
	$(OBJCOPY) -I $(BFD_NAME) -O binary --remove-section .bss --strip-debug $(STAGE2_OUTPUT).elf $(STAGE2_OUTPUT)

$(STAGE2_OUTPUT).dbg: $(STAGE2_OUTPUT).elf
	$(OBJCOPY) --only-keep-debug $(STAGE2_OUTPUT).elf $(STAGE2_OUTPUT).dbg

$(STAGE2_OUTPUT).elf: $(STAGE2_OBJS) stage2-link.ld
	$(LD) -T stage2-link.ld -o $(STAGE2_OUTPUT).elf $(STAGE2_OBJS)

%.o: %.s
	$(AS) -o $@ $^

clean:
	rm -f stamp $(OBJS) $(MS_OBJS) $(EFI_OBJS) $(BIOS_ONLY_OBJS) $(OUTPUT) $(OUTPUT).elf $(OUTPUT).dbg

.PHONY: all clean

.DEFAULT_GOAL: all