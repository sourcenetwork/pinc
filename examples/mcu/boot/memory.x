/* The boot stage, loaded into the DTCM RAM by the debug probe: it leaves the AXI SRAM to the image it starts, and the
 * chip's own flash as it found it. A board that starts with no probe would hold this stage in that flash, linked at
 * 0x08000000; that build is not made here. */
MEMORY
{
  FLASH : ORIGIN = 0x20000000, LENGTH = 16K
  RAM   : ORIGIN = 0x20004000, LENGTH = 16K
}
