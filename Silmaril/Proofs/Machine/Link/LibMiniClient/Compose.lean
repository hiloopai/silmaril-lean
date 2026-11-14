module

public import Silmaril.Proofs.Machine.Link.LibMiniClient.Client
public import Silmaril.Machine.X86.Ladder.LibMini.Thms
public import Silmaril.Machine.X86.Safe.Open9.Thms

/-!
# Proofs: rung 12 composed and validated

* `units_objects`: the units' objects are exactly the objects the validator links
  (kernel evaluation).
* Per-unit contracts: `start_sat`, `main_sat` (all exports `unverified`), `client_sat'`
  (`client_sat` on the real `client.o`, facts by kernel evaluation), `libmini_sat` (the separation-logic layer's
  `exports_sat`, through `tu_sat_of_code`; libmini is not re-verified).
* `closed`, `abi`: the remaining hypotheses of `validated_compose`. (`exec_sections`, that
  every allocated section is executable, is still true of rung 12 but no longer needed.)
* `len1_addr`: the link places `len1` at `0x401060`.
* Rejection tests: `obj3_strlen_not_memcpy`, `abi_rejects_ms64`.
* `len1_composed`: **the end-to-end theorem**.
* `*_satOn`, `closedOn`, `len1_composedOn` prove the same for the logic
  `logicOn step` of every machine `step` with `[ExtendsOpen step]`; `len1_composed9` is the
  instance at `Open9.step`.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Link.LibMiniClient

open Silmaril.X86 (MState Word Byte)
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (allocated)
open Silmaril.X86.Linking (Relocation.link Relocation.relocate)
open Silmaril.Process.LPS.ELFImage (x86Policy)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.X86.Stencils.ByteLoop
open Silmaril.Machine.Link.Unit
open Silmaril.Machine.Link.Contract
open Silmaril.Machine.Link.Validate
open Silmaril.Machine.Link.FnSpec
open Silmaril.Machine.Link.Examples.LibMiniClient
open Silmaril.Machine.Link.Fixtures.LibMiniClientBfd
open Silmaril.Proofs.Machine.Link.FnSpec

set_option maxRecDepth 100000

theorem parsed_some : (objects.mapM fun b => Silmaril.Machine.Link.Blob.readObjectN b.n b.len) =
    some parsed := by
  have h : (objects.mapM fun b => Silmaril.Machine.Link.Blob.readObjectN b.n b.len).isSome = true := by
    decide +kernel
  unfold parsed
  cases e : (objects.mapM fun b => Silmaril.Machine.Link.Blob.readObjectN b.n b.len) with
  | none => rw [e] at h; cases h
  | some p => rfl

/-- The units' objects are the prepared inputs of the validated link. -/
theorem units_objects : units.map TU.object = prepared := by decide +kernel

theorem prep_of_parse : ∀ ps, (objects.map Silmaril.Machine.Link.Blob.bytes).mapM readObject = some ps →
    prepare ps witness.dropped = units.map TU.object := by
  intro ps h
  rw [mapM_readObject_bytes, parsed_some, Option.some.injEq] at h
  subst h
  exact units_objects.symm

/-! ## The unit contracts

each unit contract is proved once for the logic `logicOn step` of every machine
`step` that extends the open machine (`*On`), and instantiated at `Open.step` under the
round-2 names. -/

section

variable (step : MState → Option MState)

theorem start_satOn : (startTU (obj 0)).Sat (logicOn step) Relocation.relocate :=
  tu_sat_unverified _ fun e he => by simp [startTU] at he; rw [he]

theorem main_satOn : (mainTU (obj 1)).Sat (logicOn step) Relocation.relocate :=
  tu_sat_unverified _ fun e he => by simp [mainTU] at he; rw [he]

end

theorem start_sat : (startTU (obj 0)).Sat logic Relocation.relocate := start_satOn _

theorem main_sat : (mainTU (obj 1)).Sat logic Relocation.relocate := main_satOn _

theorem obj2_alloc : allocatedIndices (obj 2) = [4] := by decide +kernel
theorem obj2_rel : (obj 2).relocations = [⟨4, 5, 3, 4, -4⟩] := by decide +kernel
theorem obj2_text : (obj 2).sections[4]? = some lenText := by decide +kernel
theorem obj2_sym : (obj 2).symbols[3]? = some ⟨⟨15, 16, 0, 0, 0, 0⟩, nStrlen⟩ := by
  decide +kernel
theorem obj2_find : (obj 2).symbols.find? (fun symbol =>
    symbol.binding == 1 && symbol.raw.sectionIndex != 0 && symbol.name == nLen1) =
    some ⟨⟨10, 18, 0, 4, 0, 18⟩, nLen1⟩ := by decide +kernel

/-- **The client unit**, on the real `client.o`. -/
theorem client_satOn' (step : MState → Option MState) [Silmaril.Machine.X86.Safe.ExtendsOpen step] :
    (clientTU (obj 2)).Sat (logicOn step) Relocation.relocate :=
  client_sat (S := scanSpec) obj2_alloc obj2_rel obj2_text obj2_sym (by simp [nStrlen]) obj2_find
    rfl rfl

theorem obj3_rel : (obj 3).relocations = [] := by decide +kernel
theorem obj3_memcpy : exportCodeB (obj 3) nMemcpy
    Silmaril.Machine.X86.Ladder.LibMini.memcpyCode = true := by decide +kernel
theorem obj3_memset : exportCodeB (obj 3) nMemset
    Silmaril.Machine.X86.Ladder.LibMini.memsetCode = true := by decide +kernel
theorem obj3_strlen : exportCodeB (obj 3) nStrlen
    Silmaril.Machine.X86.Ladder.LibMini.strlenCode = true := by decide +kernel

theorem client_sat' : (clientTU (obj 2)).Sat logic Relocation.relocate := client_satOn' _

/-- **The libmini unit**, from the separation-logic layer's `exports_sat` (no re-verification). -/
theorem libmini_satOn (step : MState → Option MState) [Silmaril.Machine.X86.Safe.ExtendsOpen step] :
    (libminiTU (obj 3)).Sat (logicOn step) Relocation.relocate := by
  open Silmaril.Machine.X86.Ladder.LibMini in
  have hA := exports_sat
  refine tu_sat_of_code _ obj3_rel fun e he => ?_
  simp only [libminiTU, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨memcpyCode, exportCode_of_check obj3_memcpy,
      hA ⟨"memcpy", memcpyCode, copySpec⟩ (by simp [exports])⟩
  · exact .inl rfl
  · exact .inr ⟨memsetCode, exportCode_of_check obj3_memset,
      hA ⟨"memset", memsetCode, fillSpec⟩ (by simp [exports])⟩
  · exact .inl rfl
  · exact .inr ⟨strlenCode, exportCode_of_check obj3_strlen,
      hA ⟨"strlen", strlenCode, scanSpec⟩ (by simp [exports])⟩

theorem libmini_sat : (libminiTU (obj 3)).Sat logic Relocation.relocate := libmini_satOn _

theorem units_satOn (step : MState → Option MState) [Silmaril.Machine.X86.Safe.ExtendsOpen step] :
    ∀ u ∈ units, u.Sat (logicOn step) Relocation.relocate := by
  intro u hu
  simp only [units, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  exacts [start_satOn step, main_satOn step, client_satOn' step, libmini_satOn step]

theorem units_sat : ∀ u ∈ units, u.Sat logic Relocation.relocate := units_satOn _

/-! ## The other hypotheses -/

/-- Every import is served by an export with the same spec (on every machine: `Sub` does not
depend on it). -/
theorem closedOn (step : MState → Option MState) : ImportsClosed (logicOn step) units [] := by
  intro u hu i hi
  left
  simp only [units, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · simp only [startTU, List.mem_singleton] at hi; subst hi
    exact ⟨1, _, rfl, _, List.mem_singleton_self _, rfl, FnSpec.Sub.refl _⟩
  · simp only [mainTU, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact ⟨3, _, rfl, ⟨nMemset, .sysv64, fillSpec⟩, by simp [libminiTU], rfl, FnSpec.Sub.refl _⟩
    · exact ⟨3, _, rfl, ⟨nMemcpy, .sysv64, copySpec⟩, by simp [libminiTU], rfl, FnSpec.Sub.refl _⟩
    · exact ⟨2, _, rfl, _, List.mem_singleton_self _, rfl, FnSpec.Sub.refl _⟩
  · simp only [clientTU, List.mem_singleton] at hi; subst hi
    exact ⟨3, _, rfl, ⟨nStrlen, .sysv64, scanSpec⟩, by simp [libminiTU], rfl, FnSpec.Sub.refl _⟩
  · simp [libminiTU] at hi

theorem closed : ImportsClosed logic units [] := closedOn _

theorem abi : AbiCompatible Silmaril.Machine.Link.Abi.Policy.exact units := by
  unfold AbiCompatible; decide +kernel

theorem exec_sections : ∀ u ∈ units, ∀ part ∈ u.object.sections, allocated part = true →
    part.header.flags &&& 4 ≠ 0 := by decide +kernel

/-- `len1` is linked at `0x401060` (the witness places `client.o`'s `.text.len1` there). -/
theorem len1_addr : globalValuation (units.map TU.object) witness.layout witness.absolute nLen1 =
    some 0x401060 := by decide +kernel

/-! ## Rejection tests -/

/-- The code check is not vacuous: `strlen`'s symbol does not hold `memcpy`'s bytes. -/
theorem obj3_strlen_not_memcpy : exportCodeB (obj 3) nStrlen
    Silmaril.Machine.X86.Ladder.LibMini.memcpyCode = false := by decide +kernel

/-- The client's import tagged `ms64` against libmini's `sysv64` export is rejected. -/
theorem abi_rejects_ms64 : ¬ AbiCompatible Silmaril.Machine.Link.Abi.Policy.exact
    [startTU (obj 0), mainTU (obj 1),
      { clientTU (obj 2) with imports := [⟨nStrlen, .ms64, scanSpec⟩] }, libminiTU (obj 3)] := by
  unfold AbiCompatible; decide +kernel

/-! ## The end-to-end theorem -/

/-- **Rung 12, composed, on any machine that extends the open machine**: the same
proof, with every unit contract taken in the logic `logicOn step`. -/
theorem len1_composedOn (step : MState → Option MState) [Silmaril.Machine.X86.Safe.ExtendsOpen step] :
    ∃ records out, Silmaril.Process.LPS.ELFImage.parse x86Policy exe.bytes = some records ∧
      Relocation.link prepared witness.layout witness.absolute = some out ∧
      ∀ n, (logicOn step).Safe n 0x401060 len1Spec out ∧
        ∀ m, ImageLoaded (records.image exe.bytes) m →
          ∀ (x : len1Spec.Arg) (sp ret : Word), FnSpec.EntryAligned sp → 16 ≤ sp.toNat →
          ∀ F : SProp, (len1Spec.SysVPre x (BitVec.ofNat 64 0x401060) sp ret ∗ F)
              (offBytes (Dom out) (toFrag m)) →
            Silmaril.Machine.X86.Safe.SafeN step
              (fun m' => ((Code (Dom out) (byteOf m) ∗ len1Spec.SysVPost x sp ret) ∗ F)
                (toFrag m')) n m := by
  obtain ⟨records, out, hrec, hlink, h⟩ := validated_compose (step := step) sound prep_of_parse
    abi (units_satOn step) (closedOn step)
  rw [units_objects] at hlink
  refine ⟨records, out, hrec, hlink, fun n => ?_⟩
  have := h n 2 (clientTU (obj 2)) rfl ⟨nLen1, .sysv64, len1Spec⟩ (List.mem_singleton_self _)
    0x401060 len1_addr
  exact ⟨this.1, fun m hl x sp ret hA hst F hp => this.2 m hl x sp ret hA hst F hp⟩

/-- **Rung 12, composed.** For the validated ld.bfd output of rung 12: the executable parses,
the linker reproduces the link, and `len1` at `0x401060` meets `len1Spec` (libmini's
`scanSpec` plus one) at every step index, both in the linked image and on every machine
state that holds the executable's loader image. The proof uses libmini only through its
exported specs. -/
theorem len1_composed :
    ∃ records out, Silmaril.Process.LPS.ELFImage.parse x86Policy exe.bytes = some records ∧
      Relocation.link prepared witness.layout witness.absolute = some out ∧
      ∀ n, logic.Safe n 0x401060 len1Spec out ∧
        ∀ m, ImageLoaded (records.image exe.bytes) m →
          ∀ (x : len1Spec.Arg) (sp ret : Word), FnSpec.EntryAligned sp → 16 ≤ sp.toNat →
          ∀ F : SProp, (len1Spec.SysVPre x (BitVec.ofNat 64 0x401060) sp ret ∗ F)
              (offBytes (Dom out) (toFrag m)) →
            SafeN (fun m' => ((Code (Dom out) (byteOf m) ∗ len1Spec.SysVPost x sp ret) ∗ F)
              (toFrag m')) n m :=
  len1_composedOn _

/-- **Rung 12, composed on the open machine over `Ext9`**: the composition is
re-run with every unit contract in the logic of `Open9.step` (so a unit verified on `Open9`,
using `Ext9` forms or a jump table, could take any unit's place). The executable, the link
and the spec are those of `len1_composed`. -/
theorem len1_composed9 :
    ∃ records out, Silmaril.Process.LPS.ELFImage.parse x86Policy exe.bytes = some records ∧
      Relocation.link prepared witness.layout witness.absolute = some out ∧
      ∀ n, (logicOn Silmaril.Machine.X86.Open9.step).Safe n 0x401060 len1Spec out ∧
        ∀ m, ImageLoaded (records.image exe.bytes) m →
          ∀ (x : len1Spec.Arg) (sp ret : Word), FnSpec.EntryAligned sp → 16 ≤ sp.toNat →
          ∀ F : SProp, (len1Spec.SysVPre x (BitVec.ofNat 64 0x401060) sp ret ∗ F)
              (offBytes (Dom out) (toFrag m)) →
            Silmaril.Machine.X86.Safe.SafeN Silmaril.Machine.X86.Open9.step
              (fun m' => ((Code (Dom out) (byteOf m) ∗ len1Spec.SysVPost x sp ret) ∗ F)
                (toFrag m')) n m :=
  len1_composedOn _

end Silmaril.Proofs.Machine.Link.LibMiniClient
