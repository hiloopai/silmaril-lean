module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.Loader.GccStrLength

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (F)
open Silmaril.Elf.Link.Dyn (ExeLoaded)
open Silmaril.X86 (Word)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)

/-- The pinned file's read-only executable segment maps the exact eleven length-query bytes. -/
theorem gccStrLength_codeAt : Silmaril.Elf.CodeAt F 0x10060 gccStrLengthBytes :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.Loader.gccStrLength_codeAt

/-- Every slot written by the modeled eager loader misses the file's read-only load segments. -/
theorem gcc_noTextRel_eager : Silmaril.Elf.Exe.NoTextRelD F false :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.Loader.gcc_noTextRel_eager

/-- The exact GCC body is fetchable at the non-wrapping placed address when the eager
loader relation holds with this file at the head of its own scope. -/
theorem gccStrLength_loaded {scope : List Blob} {base : Word} {bases : List Word}
    {ifunc : Word → Option Word} {resolver : Word} {memory : Memory}
    (placement : Silmaril.Elf.Placement F base.toNat)
    (image : ExeLoaded (F :: scope) (base :: bases) ifunc false resolver memory) :
    Silmaril.X86.Ext.Loaded memory (base + 0x10060) gccStrLengthBytes ∧
      (base + 0x10060).toNat = base.toNat + 0x10060 :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.Loader.gccStrLength_loaded placement image

end Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader
