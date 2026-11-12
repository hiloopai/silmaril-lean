module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.Config

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge

* `noAtoms_ms_configVD_iff`: **`configVD hn c` has no memory SIMD atom iff `c` has no memory SIMD
  instruction** (`NoMemSimd c`), at every configuration and every encoding of host functions.
  `noAtoms_ms_configV` is the forward direction at `configV`.
* `noAtoms_h_configVD_iff` (and `noAtoms_h_configV_iff` off memory SIMD code): the image has no memory SIMD atom and no
  `CALL_REF` iff `c` has no memory SIMD instruction and no `call_ref` (`NoCallRef c`).
* `easy_iff`: **`RMRed.Easy` in Core terms**: no memory SIMD code in `c` or in any Core successor,
  and no `call_ref` anywhere in `c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open HStep (hAtoms)
open Round6.MemSimd (memSimd instrMS instrsMS AdminMS AdminsMS StoreMS NoMemSimd)
open Round7.MemSimd (configVD)

variable {H : Type}

/-! ## `instrOk false` gives `instrOk true` -/

mutual
theorem instrOk_mono : ∀ i : Instr, instrOk false i = true → instrOk true i = true
  | .block _ body, h => instrsOk_mono body h
  | .loop _ body, h => instrsOk_mono body h
  | .if_ _ b₁ b₂, h => by
      simp only [instrOk, Bool.and_eq_true] at h ⊢
      exact ⟨instrsOk_mono b₁ h.1, instrsOk_mono b₂ h.2⟩
  | .tryTable _ _ body, h => instrsOk_mono body h
  | .callRef _, _ => rfl
  | .nop, h | .unreachable, h | .drop, h | .select _, h | .br _, h | .brIf _, h
  | .brTable _ _, h | .brOnNull _, h | .brOnNonNull _, h | .brOnCast .., h | .brOnCastFail .., h
  | .call _, h | .callIndirect .., h | .return_, h | .returnCall _, h | .returnCallRef _, h
  | .returnCallIndirect .., h | .throw _, h | .throwRef, h | .localGet _, h | .localSet _, h
  | .localTee _, h | .globalGet _, h | .globalSet _, h | .tableGet _, h | .tableSet _, h
  | .tableSize _, h | .tableGrow _, h | .tableFill _, h | .tableCopy .., h | .tableInit .., h
  | .elemDrop _, h | .intLoad .., h | .floatLoad .., h | .intStore .., h | .floatStore .., h
  | .vecLoad .., h | .vecLoadLane .., h | .vecStore .., h | .vecStoreLane .., h
  | .memorySize _, h | .memoryGrow _, h | .memoryFill _, h | .memoryCopy .., h
  | .memoryInit .., h | .dataDrop _, h | .refNull _, h | .refIsNull, h | .refAsNonNull, h
  | .refEq, h | .refTest _, h | .refCast _, h | .refFunc _, h | .refI31, h | .i31Get _, h
  | .structNew _, h | .structNewDefault _, h | .structGet .., h | .structSet .., h
  | .arrayNew _, h | .arrayNewDefault _, h | .arrayNewFixed .., h | .arrayNewData .., h
  | .arrayNewElem .., h | .arrayGet .., h | .arraySet _, h | .arrayLen, h | .arrayFill _, h
  | .arrayCopy .., h | .arrayInitData .., h | .arrayInitElem .., h | .externConvertAny, h
  | .anyConvertExtern, h | .intConst .., h | .floatConst .., h | .intUnOp .., h
  | .intBinOp .., h | .intTestOp .., h | .intRelOp .., h | .floatUnOp .., h
  | .floatBinOp .., h | .floatRelOp .., h | .convert _, h | .vecConst _, h | .vecUnOp _, h
  | .vecBinOp _, h | .vecTernOp _, h | .vecTestOp _, h | .vecIntUnOp .., h
  | .vecFloatUnOp .., h | .vecIntBinOp .., h | .vecFloatBinOp .., h | .vecIntTernOp .., h
  | .vecFloatTernOp .., h | .vecAllTrue _, h | .vecIntRelOp .., h | .vecFloatRelOp .., h
  | .vecShiftOp .., h | .vecBitmask _, h | .vecSwizzle _, h | .vecShuffle _, h
  | .vecExtUnOp .., h | .vecExtBinOp .., h | .vecExtTernOp .., h | .vecNarrow .., h
  | .vecConvert .., h | .vecSplat _, h | .vecExtractLane .., h | .vecReplaceLane .., h => h

theorem instrsOk_mono : ∀ is : List Instr, instrsOk false is = true → instrsOk true is = true
  | [], _ => rfl
  | i :: is, h => by
      simp only [instrsOk, Bool.and_eq_true] at h ⊢
      exact ⟨instrOk_mono i h.1, instrsOk_mono is h.2⟩
end

mutual
theorem adminOk_mono : ∀ a : Admin, AdminOk false a → AdminOk true a
  | .plain i, h => instrOk_mono i h
  | .ref _, _ => trivial
  | .callRefType _, _ => rfl
  | .returnCallRefType _, _ => trivial
  | .label _ cont body, h => ⟨instrsOk_mono cont h.1, adminsOk_mono body h.2⟩
  | .handler _ _ body, h => adminsOk_mono body h
  | .frame _ _ body, h => adminsOk_mono body h
  | .trap, _ => trivial

theorem adminsOk_mono : ∀ l : List Admin, AdminsOk false l → AdminsOk true l
  | [], _ => trivial
  | a :: l, h => ⟨adminOk_mono a h.1, adminsOk_mono l h.2⟩
end

theorem storeOk_mono {s : Store H} (h : StoreOk false s) : StoreOk true s :=
  fun fi hfi fn hc => instrsOk_mono _ (h fi hfi fn hc)

/-- `NoCallRef` gives `NoMemSimd`. -/
theorem noMemSimd_of_noCallRef {c : Config H} (h : NoCallRef c) : NoMemSimd c :=
  ⟨(storeOk_true_iff _).1 (storeOk_mono h.1), (adminsOk_true_iff _).1 (adminsOk_mono _ h.2)⟩

/-! ## The bridge -/

theorem ms_sub_ms : ∀ a ∈ msAtoms, a ∈ msAtoms := fun _ h => h

theorem callRef_not_ms : "CALL_REF" ∉ msAtoms := by simp [msAtoms]

theorem h_sub_h : ∀ a ∈ hAtoms, a ∈ hAtoms := fun _ h => h

theorem callRef_mem_h : "CALL_REF" ∈ hAtoms := by simp [hAtoms]

/-- **The `NoMemSimd → NoAtoms` bridge**, at `configV`. -/
theorem noAtoms_ms_configV (hn : H → String) {c : Config H} (h : NoMemSimd c) :
    NoAtoms msAtoms (configV hn c) :=
  na_configV msAtoms_sub_hAtoms (cr := true) (fun _ => callRef_not_ms) hn c
    ((storeOk_true_iff _).2 h.store) ((adminsOk_true_iff _).2 h.code)

/-- **`configVD hn c` has no memory SIMD atom iff `c` has no memory SIMD instruction.** -/
theorem noAtoms_ms_configVD_iff (hn : H → String) (c : Config H) :
    NoAtoms msAtoms (configVD hn c) ↔ NoMemSimd c := by
  constructor
  · intro h
    have ⟨hs, hc⟩ := ok_of_na_configVD (cr := true) ms_sub_ms (fun h => by cases h) hn c h
    exact ⟨(storeOk_true_iff _).1 hs, (adminsOk_true_iff _).1 hc⟩
  · intro h
    rw [Round7.MemSimd.configVD_eq_of_noMemSimd hn h]
    exact noAtoms_ms_configV hn h

/-- **`configVD hn c` has no memory SIMD atom and no `CALL_REF` iff `c` has no memory SIMD
instruction and no `call_ref`.** -/
theorem noAtoms_h_configVD_iff (hn : H → String) (c : Config H) :
    NoAtoms hAtoms (configVD hn c) ↔ NoCallRef c := by
  constructor
  · intro h
    exact ok_of_na_configVD (cr := false) msAtoms_sub_hAtoms (fun _ => callRef_mem_h) hn c h
  · intro h
    rw [Round7.MemSimd.configVD_eq_of_noMemSimd hn (noMemSimd_of_noCallRef h)]
    exact na_configV h_sub_h (cr := false) (fun h => by cases h) hn c h.1 h.2

/-- The same at `configV`, the encoding `RMRed.Easy` reads, at configurations without memory
SIMD code (where `configV` is `configVD`). -/
theorem noAtoms_h_configV_iff (hn : H → String) {c : Config H} (hm : NoMemSimd c) :
    NoAtoms hAtoms (configV hn c) ↔ NoCallRef c := by
  rw [← Round7.MemSimd.configVD_eq_of_noMemSimd hn hm]
  exact noAtoms_h_configVD_iff hn c

/-- **`RMRed.Easy` in Core terms.** -/
theorem easy_iff (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H) :
    RMRed.Easy hn P host c ↔
      NoMemSimd c ∧ (∀ c₁, Step P host c c₁ → NoMemSimd c₁) ∧ NoCallRef c := by
  constructor
  · rintro ⟨hm, hs, ha⟩
    exact ⟨hm, hs, (noAtoms_h_configV_iff hn hm).1 ha⟩
  · rintro ⟨hm, hs, hc⟩
    exact ⟨hm, hs, (noAtoms_h_configV_iff hn hm).2 hc⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
