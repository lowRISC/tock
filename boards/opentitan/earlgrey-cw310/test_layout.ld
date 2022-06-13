/*
 * This is used when building test binaries with `make test`.
 * It reduces the size for apps, as we don't use apps with the test
 * binaries.
 */

MEMORY
{
  rom   (rx)  : ORIGIN = 0x20000000, LENGTH = 0x60000
  /* Support up to 0x2009_0000 for apps
   * and 0x2009_0000 to 0x2010_0000 is for flash storage.
   */
  prog  (rx)  : ORIGIN = 0x20060000, LENGTH = 0x30000
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
