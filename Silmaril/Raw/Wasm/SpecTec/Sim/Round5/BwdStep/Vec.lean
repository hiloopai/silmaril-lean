module

public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# Round 5: the vector rules of `Step_pure`, backward, given `VecAgree`

Family V's `Vec.bwd_vectorRules` proves `Backward.pure` for 20 of the 25 vector rules (54–78
except 64, 70–73) from three interfaces: `HasVectorRules` (the rule provenance, proved for every
`simEnv B`), `VecDecode` (syntactic decoding of the encoding) and `VecAgree` (what SpecTec's
vector operators denote). This file **discharges `VecDecode`** (`vecDecode`): every image with a
SIMD tag is the image of the instruction `vecInstrV?` encodes (`vecInstrV?` is total on the SIMD
instructions, and `instrToV` uses it for them), a `VCONST V128 c` image is a vector constant, and
a `CONST I32 c` image an `i32` constant (family C's decoder). `VecAgree` stays a hypothesis; it is
the same interface the forward direction needs (`Open4`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)

/-- An administrative instruction with the head `VCONST` is a vector constant. -/
theorem head_vconst {a : Admin} (h : Typing.adminHead a = "VCONST") :
    ∃ b, a = .plain (.vecConst b) := by
  revert h
  admin_head_inv

set_option maxHeartbeats 1000000 in
/-- An administrative instruction with a SIMD tag of `vecInstrV?` is a SIMD instruction, and its
image is `vecInstrV?`'s. -/
theorem vinstr_of_head {a : Admin} {tag : MixopS} {x : Value} (hm : tag ∈ Vec.vecTags)
    (h : adminToV a = .case tag x) : ∃ i, a = .plain i ∧ Vec.vecInstrV? i = some (.case tag x) := by
  have hh : Typing.adminHead a = tag := (Typing.adminToV_case h).symm
  subst hh
  cases a with
  | plain i =>
      refine ⟨i, rfl, ?_⟩
      cases i <;> simp only [Vec.vecTags, Typing.adminHead, Typing.instrHead, List.mem_cons,
        List.mem_nil_iff, or_false] at hm <;>
        first
          | (rw [← h]; rfl)
          | (simp at hm)
  | ref r => cases r <;> simp [Vec.vecTags, Typing.adminHead, Typing.refHead] at hm
  | _ => simp [Vec.vecTags, Typing.adminHead] at hm

/-- **Family V's `VecDecode`, discharged.** -/
theorem vecDecode : Vec.VecDecode where
  vconst a c h := by
    obtain ⟨b, rfl⟩ := head_vconst (Typing.adminToV_case h).symm
    refine ⟨b, rfl, ?_⟩
    have h' : Value.case "VCONST" (.tuple [caseNilV "V128", pctV b.toNat]) =
        .case "VCONST" (.tuple [Silmaril.SpecTec.Equiv.ExecVector.v128V, c]) := h
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h'
    exact h'.2.symm
  i32const a c h := by
    obtain ⟨n, rfl⟩ := (Typing.ctrlDecode_simEnv ⟨fun _ _ => none⟩).constI32 a c h
    refine ⟨n, rfl, ?_⟩
    have h' : Value.case "CONST" (.tuple [caseNilV "I32", pctV n.toNat]) =
        .case "CONST" (.tuple [Silmaril.SpecTec.Equiv.Execution.i32V, c]) := h
    simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and, and_true] at h'
    exact h'.2.symm
  vinstr _ _ _ hm h := vinstr_of_head hm h

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
