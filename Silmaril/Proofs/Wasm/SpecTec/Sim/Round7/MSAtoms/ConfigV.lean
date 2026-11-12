module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.Bridge

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge: the converse at `configV`

`instrToV` still encodes the memory SIMD instructions by `schemaInstrV`, whose tags are the same
atoms `VLOAD`, `VLOAD_LANE`, `VSTORE`, `VSTORE_LANE` (`instrToV_ms_head`). So the converse holds at
`configV` too: an `adminsToV` image without a memory SIMD atom comes from memory-SIMD-free code
(`adminsMS_of_noAtomsV`), and `noAtoms_ms_configV_iff`: `NoAtoms msAtoms (configV hn c) ↔
NoMemSimd c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open Round6.MemSimd (memSimd instrMS instrsMS AdminMS AdminsMS StoreMS NoMemSimd)

variable {H : Type}

/-- **A memory SIMD instruction's `instrToV` image is a `case` of a memory SIMD atom.** -/
theorem instrToV_ms_head (i : Instr) (h : memSimd i = true) :
    ∃ a w, a ∈ msAtoms ∧ Sim.instrToV i = .case a w := by
  cases i <;> simp only [memSimd, reduceCtorEq] at h
  all_goals
    unfold Sim.instrToV
    simp only [Sim.schemaInstrV, Silmaril.Wasm.SpecTecEnc.encodeInstruction]
    exact ⟨_, _, by simp [msAtoms], rfl⟩

theorem not_na_ms {A : List MixopS} (hA : ∀ a ∈ msAtoms, a ∈ A) {i : Instr}
    (h : memSimd i = true) (hn : NoAtoms A (Sim.instrToV i)) : False := by
  obtain ⟨a, w, ha, he⟩ := instrToV_ms_head i h
  rw [he] at hn
  exact hn.1 (hA a ha)

section
variable {A : List MixopS} {cr : Bool}

mutual
/-- **An `instrToV` image without an atom of `A` satisfies `instrOk cr`.** -/
theorem instrOk_of_naV (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A) :
    ∀ i : Instr, NoAtoms A (Sim.instrToV i) → instrOk cr i = true
  | .block _ body, h => by
      unfold Sim.instrToV at h
      simpa only [instrOk] using instrsOk_of_naV hA hcr body h.2.2.1
  | .loop _ body, h => by
      unfold Sim.instrToV at h
      simpa only [instrOk] using instrsOk_of_naV hA hcr body h.2.2.1
  | .if_ _ b₁ b₂, h => by
      unfold Sim.instrToV at h
      simp only [instrOk, Bool.and_eq_true]
      exact ⟨instrsOk_of_naV hA hcr b₁ h.2.2.1, instrsOk_of_naV hA hcr b₂ h.2.2.2.1⟩
  | .tryTable _ _ body, h => by
      unfold Sim.instrToV at h
      simpa only [instrOk] using instrsOk_of_naV hA hcr body h.2.2.2.1
  | .callRef _, h => by
      simp only [instrOk]
      cases cr
      · unfold Sim.instrToV at h
        exact absurd (hcr rfl) h.1
      · rfl
  | .vecLoad .., h => (not_na_ms hA rfl h).elim
  | .vecLoadLane .., h => (not_na_ms hA rfl h).elim
  | .vecStore .., h => (not_na_ms hA rfl h).elim
  | .vecStoreLane .., h => (not_na_ms hA rfl h).elim
  | .nop, _ | .unreachable, _ | .drop, _ | .select _, _ | .br _, _ | .brIf _, _ | .brTable _ _, _
  | .brOnNull _, _ | .brOnNonNull _, _ | .brOnCast .., _ | .brOnCastFail .., _ | .call _, _
  | .callIndirect .., _ | .return_, _ | .returnCall _, _ | .returnCallRef _, _
  | .returnCallIndirect .., _ | .throw _, _ | .throwRef, _ | .localGet _, _ | .localSet _, _
  | .localTee _, _ | .globalGet _, _ | .globalSet _, _ | .tableGet _, _ | .tableSet _, _
  | .tableSize _, _ | .tableGrow _, _ | .tableFill _, _ | .tableCopy .., _ | .tableInit .., _
  | .elemDrop _, _ | .intLoad .., _ | .floatLoad .., _ | .intStore .., _ | .floatStore .., _
  | .memorySize _, _ | .memoryGrow _, _ | .memoryFill _, _ | .memoryCopy .., _
  | .memoryInit .., _ | .dataDrop _, _ | .refNull _, _ | .refIsNull, _ | .refAsNonNull, _
  | .refEq, _ | .refTest _, _ | .refCast _, _ | .refFunc _, _ | .refI31, _ | .i31Get _, _
  | .structNew _, _ | .structNewDefault _, _ | .structGet .., _ | .structSet .., _
  | .arrayNew _, _ | .arrayNewDefault _, _ | .arrayNewFixed .., _ | .arrayNewData .., _
  | .arrayNewElem .., _ | .arrayGet .., _ | .arraySet _, _ | .arrayLen, _ | .arrayFill _, _
  | .arrayCopy .., _ | .arrayInitData .., _ | .arrayInitElem .., _ | .externConvertAny, _
  | .anyConvertExtern, _ | .intConst .., _ | .floatConst .., _ | .intUnOp .., _ | .intBinOp .., _
  | .intTestOp .., _ | .intRelOp .., _ | .floatUnOp .., _ | .floatBinOp .., _ | .floatRelOp .., _
  | .convert _, _ | .vecConst _, _ | .vecUnOp _, _ | .vecBinOp _, _ | .vecTernOp _, _
  | .vecTestOp _, _ | .vecIntUnOp .., _ | .vecFloatUnOp .., _ | .vecIntBinOp .., _
  | .vecFloatBinOp .., _ | .vecIntTernOp .., _ | .vecFloatTernOp .., _ | .vecAllTrue _, _
  | .vecIntRelOp .., _ | .vecFloatRelOp .., _ | .vecShiftOp .., _ | .vecBitmask _, _
  | .vecSwizzle _, _ | .vecShuffle _, _ | .vecExtUnOp .., _ | .vecExtBinOp .., _
  | .vecExtTernOp .., _ | .vecNarrow .., _ | .vecConvert .., _ | .vecSplat _, _
  | .vecExtractLane .., _ | .vecReplaceLane .., _ => rfl

/-- `instrOk_of_naV` on a sequence. -/
theorem instrsOk_of_naV (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A) :
    ∀ is : List Instr, NoAtomsL A (Sim.instrsToV is) → instrsOk cr is = true
  | [], _ => rfl
  | i :: is, h => by
      simp only [instrsOk, Bool.and_eq_true]
      exact ⟨instrOk_of_naV hA hcr i h.1, instrsOk_of_naV hA hcr is h.2⟩
end

mutual
theorem adminOk_of_naV (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A) :
    ∀ a : Admin, NoAtoms A (Sim.adminToV a) → AdminOk cr a
  | .plain i, h => instrOk_of_naV hA hcr i h
  | .ref _, _ => trivial
  | .callRefType _, h => by
      simp only [AdminOk]
      cases cr
      · exact absurd (hcr rfl) h.1
      · rfl
  | .returnCallRefType _, _ => trivial
  | .label _ cont body, h =>
      ⟨instrsOk_of_naV hA hcr cont h.2.2.1, adminsOk_of_naV hA hcr body h.2.2.2.1⟩
  | .handler _ _ body, h => adminsOk_of_naV hA hcr body h.2.2.2.1
  | .frame _ _ body, h => adminsOk_of_naV hA hcr body h.2.2.2.1
  | .trap, _ => trivial

theorem adminsOk_of_naV (hA : ∀ a ∈ msAtoms, a ∈ A) (hcr : cr = false → "CALL_REF" ∈ A) :
    ∀ l : List Admin, NoAtomsL A (Sim.adminsToV l) → AdminsOk cr l
  | [], _ => trivial
  | a :: l, h => ⟨adminOk_of_naV hA hcr a h.1, adminsOk_of_naV hA hcr l h.2⟩
end

end

/-- **`adminsToV` code without a memory SIMD atom has no memory SIMD instruction.** -/
theorem adminsMS_of_noAtomsV {l : List Admin} (h : NoAtomsL msAtoms (Sim.adminsToV l)) :
    AdminsMS l :=
  (adminsOk_true_iff l).1 (adminsOk_of_naV (cr := true) ms_sub_ms (fun h => by cases h) l h)

/-- Memory-SIMD-free code has an `adminsToV` image without a memory SIMD atom. -/
theorem noAtomsV_of_adminsMS {l : List Admin} (h : AdminsMS l) :
    NoAtomsL msAtoms (Sim.adminsToV l) :=
  na_adminsToV msAtoms_sub_hAtoms (cr := true) (fun _ => callRef_not_ms) l
    ((adminsOk_true_iff l).2 h)

/-- **`configV hn c` has no memory SIMD atom iff `c` has no memory SIMD instruction.** -/
theorem noAtoms_ms_configV_iff (hn : H → String) (c : Config H) :
    NoAtoms msAtoms (Sim.configV hn c) ↔ NoMemSimd c := by
  refine ⟨fun h => ?_, noAtoms_ms_configV hn⟩
  have hs : NoAtoms msAtoms (Sim.storeV hn c.store) := h.2.1.2.1
  have hc : NoAtomsL msAtoms (Sim.adminsToV c.code) := h.2.2.1
  refine ⟨fun fi hfi fn hfc => ?_, adminsMS_of_noAtomsV hc⟩
  have hf : NoAtoms msAtoms (.list (c.store.funcs.map (Sim.funcInstV hn))) := hs.2.2.2.2.1
  have hfi' := noAtoms_of_list hf (Sim.funcInstV hn fi) (List.mem_map_of_mem hfi)
  have hcode := hfi'.2.2.1
  simp only [hfc] at hcode
  rw [← instrsOk_true]
  exact instrsOk_of_naV (cr := true) ms_sub_ms (fun h => by cases h) fn.body hcode.2.2.2.1

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
