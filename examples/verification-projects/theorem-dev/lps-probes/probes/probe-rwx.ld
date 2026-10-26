/* The writable variant of probe.ld, for probes that read into a buffer of
   their own image (JSON "image": "rwx"): one PT_LOAD (R+W+X) at 0x400000
   containing the ELF header, the program header table and every probe section. A byte's file offset equals its
   distance from 0x400000, so the Lean image is a prefix of the file. */
OUTPUT_FORMAT("elf64-x86-64")
OUTPUT_ARCH(i386:x86-64)
ENTRY(_start)
PHDRS { image PT_LOAD FILEHDR PHDRS FLAGS(7); }
SECTIONS {
  . = 0x400000 + SIZEOF_HEADERS;
  .text : { *(.text) *(.rodata) } :image
  /DISCARD/ : { *(.note*) *(.comment) *(.eh_frame*) *(.data) *(.bss) }
}
