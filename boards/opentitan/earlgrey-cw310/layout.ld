MEMORY
{
  rom   (rx)  : ORIGIN = 0x20000000, LENGTH = 0x30000
  /* Support up to 0x2009_0000 for apps
   * and 0x2009_0000 to 0x2010_0000 is for flash storage.
   */
  prog  (rx)  : ORIGIN = 0x20030000, LENGTH = 0x60000
  ram   (!rx) : ORIGIN = 0x10000000, LENGTH = 0x10000
}

MPU_MIN_ALIGN = 1K;
SECTIONS {
    .manifest ORIGIN(rom):
    {
      . = . + 892;
      LONG(_stext)
    } > rom

    .vectors : ALIGN (256) {
      KEEP(*(.riscv.open_titan_trap_vectored));
    } > rom
}

INCLUDE ../../kernel_layout.ld
