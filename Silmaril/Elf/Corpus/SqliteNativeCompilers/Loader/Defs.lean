module

public import Silmaril.X86.Ext.SymExec
public import Silmaril.Elf.Exe.Defs
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader

/-- The pinned GCC O2 body of `sqlite3_str_length`, at ELF virtual address `0x10060`. -/
def gccStrLengthBytes : List (BitVec 8) :=
  [0x31, 0xc0, 0x48, 0x85, 0xff, 0x74, 0x03, 0x8b, 0x47, 0x18, 0xc3]

end Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader
