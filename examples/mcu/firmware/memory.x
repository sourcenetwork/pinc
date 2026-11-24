/* NUCLEO-H7S3L8 (STM32H7S3L8): the image runs in place from the board's external flash, which the boot stage maps at
 * 0x70000000. The chip's 620 KiB of RAM are in pieces, and the image uses three of them:
 *
 *   AXI SRAM (456 KiB)  the stack, in its lower 368 KiB, and the statics above it: a stack that outgrows its room
 *                       leaves the RAM at its lower end and faults there, where one above the statics would write
 *                       over them. The deepest path is a dial.
 *   DTCM RAM (64 KiB)   the session's memory: the pool's chunks and the stream table (60 KiB).
 *   ITCM RAM (64 KiB)   the endpoint (54 KiB). It starts at address zero, so the first 256 bytes are left alone.
 *
 * The AHB SRAM (32 KiB) is not used. */
MEMORY
{
  FLASH : ORIGIN = 0x70000000, LENGTH = 32M
  STACK : ORIGIN = 0x24000000, LENGTH = 368K
  RAM   : ORIGIN = 0x2405C000, LENGTH = 88K
  DTCM  : ORIGIN = 0x20000000, LENGTH = 64K
  ITCM  : ORIGIN = 0x00000100, LENGTH = 64K - 256
}

_stack_end = ORIGIN(STACK);
_stack_start = ORIGIN(STACK) + LENGTH(STACK);
__image_start = ORIGIN(FLASH);

SECTIONS
{
  /* Neither is loaded or zeroed: the program writes each before it reads it. */
  .dtcm (NOLOAD) : ALIGN(8)
  {
    *(.dtcm .dtcm.*);
  } > DTCM
  .itcm (NOLOAD) : ALIGN(8)
  {
    *(.itcm .itcm.*);
  } > ITCM
} INSERT AFTER .uninit;
