module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader.Defs
import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Thms
import Silmaril.Elf.BindEq.Thms
import Silmaril.Elf.Exe.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.Loader

open Silmaril.Elf.Corpus.SqliteNativeCompilers.Loader (gccStrLengthBytes)
open Silmaril.Elf
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So
open Silmaril.X86
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Link.Dyn (frun ExeLoaded)

set_option maxRecDepth 8192

theorem gccStrLength_codeAt : Silmaril.Elf.CodeAt F 0x10060 gccStrLengthBytes :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

/-- Eager loading writes the slots named by DT_RELA and DT_JMPREL.
Check each eight-byte slot against the loader's read-only segment ranges. -/
private def checkEagerRelocations : Rd Bool := do
  let info ← Link.DynElf.Elf.dynInfo
  let relocations ← Link.DynElf.Elf.relas info
  pure ((relocations.1.map (·.off) ++ relocations.2.map (·.off)).all (Exe.avoidsRo info.phs))

private theorem checkedEagerRelocations :
    checkEagerRelocations.run (blobRead F) = some true :=
  Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel)

theorem gcc_noTextRel_eager : Exe.NoTextRelD F false := by
  intro info hinfo positions hpositions p hp
  have checked := checkedEagerRelocations
  unfold checkEagerRelocations at checked
  change (Link.DynElf.Elf.dynInfo.bind _).run _ = _ at checked
  rw [Rd.run_bind, show Link.DynElf.Elf.dynInfo.run (blobRead F) = some info from hinfo,
    Option.bind_some] at checked
  unfold Exe.slotPositions at hpositions
  cases relocations : frun F (Link.DynElf.Elf.relas info) with
  | none =>
    rw [relocations] at hpositions
    cases hpositions
  | some rs =>
    rw [relocations] at hpositions
    simp only [Bool.false_eq_true, false_and, ite_false, Option.map_some, List.nil_append,
      Option.some.injEq] at hpositions
    change ((Link.DynElf.Elf.relas info).bind _).run _ = _ at checked
    rw [Rd.run_bind, show (Link.DynElf.Elf.relas info).run (blobRead F) = some rs from relocations,
      Option.bind_some] at checked
    have all : (rs.1.map (·.off) ++ rs.2.map (·.off)).all (Exe.avoidsRo info.phs) = true :=
      Option.some.inj checked
    exact List.all_eq_true.mp all p (hpositions ▸ hp)

theorem gccStrLength_loaded {scope : List Blob} {base : Word} {bases : List Word}
    {ifunc : Word → Option Word} {resolver : Word} {memory : Memory}
    (placement : Silmaril.Elf.Placement F base.toNat)
    (image : ExeLoaded (F :: scope) (base :: bases) ifunc false resolver memory) :
    Ext.Loaded memory (base + 0x10060) gccStrLengthBytes ∧
      (base + 0x10060).toNat = base.toNat + 0x10060 := by
  have modelPlacement := (Silmaril.Proofs.Elf.BindEq.placement_iff _ _ _ parses rfl rfl).2 placement
  have ro := Exe.roLoaded_of_exeLoaded modelPlacement gcc_noTextRel_eager image
  exact Silmaril.Proofs.Elf.BindEq.directCall_of_roLoaded' parses rfl rfl
    gccStrLength_codeAt placement ro

end Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.Loader
