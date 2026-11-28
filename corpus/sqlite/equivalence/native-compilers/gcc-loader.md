# GCC SQLite length-query loader premise

For the committed GCC 14 O2 SQLite 3.54.1 ELF, Lean proves that the exact
eleven bytes of `sqlite3_str_length` are fetchable at the placed address
`base + 0x10060` under the eager `ExeLoaded` model. The premises are the
standard ELF placement bounds and an instance of the model's successful
eager image relation with this object at the head of its own scope.

- `gccStrLength_codeAt` checks the file bytes inside its read-only executable
  `PT_LOAD` (`p_offset = p_vaddr = 0xf000`). The virtual and file ranges
  are both `[0x10060, 0x1006b)`.
- `gcc_noTextRel_eager` runs the loader's dynamic-header and relocation
  readers over the staged kernel bytes. It checks that every eight-byte
  `DT_RELA` and `DT_JMPREL` slot misses read-only load segments, then
  transports the result to the actual file.
- `gccStrLength_loaded` combines those facts with the existing loader
  bridge. It proves `Ext.Loaded` at the placed word address and rules
  out wraparound when computing the address from the file VA.

The pinned file is
`corpus/variants/sqlite/3.54.1/default/x86_64/O2/unstripped/libsqlite3.so`
with SHA-256
`fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8`.
The checked bytes are `31 c0 48 85 ff 74 03 8b 47 18 c3`. The proof
uses the existing staged parse of this file.

The result supplies fetchability once the modeled placement and image
hold. Reader and slot checks concern the modeled eager loader. Host
`dlopen`, symbol resolution at a call site, lazy binding, and the
Clang artifact are outside its scope.

```sh
lake build --wfail Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader.Thms
```

An ordinary Lean import of that module exposes all three theorems.
Use `#print axioms` with each theorem name in the
`Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader` namespace to inspect
its transitive footprint.
