module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdNum
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeStoreVac

/-!
# `STORE` is never typed in 1.0 either: the store leaves are vacuous forward

1.0's `admininstr` gives `STORE` the payload `valtype; sz?; memarg`, a quantifier `Inn?` and the
premise `(if valtype = Inn /\ sz.0 < $size(Inn))?{Inn <- Inn?, sz <- sz?}`, the shape 2.0 has
(`Sim20.Whole.not_typedV_store20`). `Inn?` is not a defining quantifier and the payload does not
bind it, so the premise is undefined at every fuel and **no value is a 1.0 `STORE`**
(`not_typedV_store10`, kernel `rfl` for the case, 2.0's generic lemmas for the rest). Round 2's
encoding check had recorded this rejection as `knownRejectedInstrs`; this is the proof.

So the four V1 store leaves (`intStore`, `intStoreTrap`, `floatStore`, `floatStoreTrap`) hold
vacuously under `FwdAt10`, at every builtins (`fwdAt10_intStore`, …): their code is untypable.
As for 2.0, a meaningful forward statement for stores needs an erratum binding `Inn`; it is not
done here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config value setMemory storeInt storeFloat
  frameMemory effectiveAddress)
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim.Typing (findCaseQ)

set_option maxRecDepth 100000

variable {B : Builtins} {H : Type} {hn : H → String}

/-- The payload type of 1.0's `STORE`. -/
abbrev storeT10 : Typ := .tupT [.mk "valtype" (.varT "valtype" []),
  .mk "sz?" (.iterT (.varT "sz" []) .opt), .mk "memarg" (.varT "memarg" [])]

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 4000000 in
/-- 1.0's `STORE` case: its payload, and one premise iterating over `Inn?`. -/
theorem findCaseQ_store10 : ∃ cs qs pr ds, (simEnv10 B).findTyp? "admininstr" =
      some ([], [.instD [] [] (.variantT cs)]) ∧
    findCaseQ cs "STORE" = some (storeT10, qs, [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))]) ∧
    quantDefs qs [.iterPr pr (.mk .opt (.mk "Inn" (.varE "Inn?") :: ds))] = [] :=
  ⟨_, _, _, _, rfl, rfl, by simp [quantDefs]⟩

/-- `Inn?` is not bound by the `STORE` payload's binders. -/
theorem findVal_innOpt_caseScope10 (w : Value) :
    (caseScope VarEnv.empty storeT10 w).findVal? "Inn?" = none := by
  cases w with
  | tuple vs =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
      simp [caseScope, typBinds]
  | _ => rfl

/-- **No value is a 1.0 `STORE`**, at every builtins. -/
theorem not_typedV_store10 (w : Value) :
    ¬ TypedV (simEnv10 B) adminT10 (.case "STORE" w) := by
  intro h
  obtain ⟨cs, qs, pr, ds, htd, hf, hq⟩ := findCaseQ_store10 (B := B)
  obtain ⟨op, w', he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Sim20.Whole.hasTypDef_of_closed htd (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ : "STORE" = op ∧ w = w' := by simpa using he
  obtain ⟨-, ρq, hb, hp⟩ := Sim20.Whole.hasTypCase_inv_findCaseQ hc hf
  rw [hq, bindQuants_nil_iff] at hb
  subst hb
  exact Sim20.Whole.not_premsOk_unboundOpt (findVal_innOpt_caseScope10 w) hp

/-- Code whose third element is a `STORE` is untypable. -/
theorem not_typed_store3 {a b : Admin} {i : V1.Instr} (hi : ∃ w, instrToV i = .case "STORE" w)
    (h : TypedV (simEnv10 B) adminsT (.list (adminsToV [a, b, .source i]))) : False := by
  obtain ⟨w, hw⟩ := hi
  have h' : TypedV (simEnv10 B) adminT10 (instrToV i) := typedV_third10 h
  rw [hw] at h'
  exact not_typedV_store10 w h'

/-- **The integer store leaf is vacuous.** -/
theorem fwdAt10_intStore (s : Store H) (f : Frame) (t : IntType) (packed : Option V1.PackSize)
    (arg : V1.MemArg) (c : BitVec 32) (x : BitVec t.width) (s' : Store H) (code' : List Admin) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t packed arg)]⟩
      ⟨s', f, code'⟩ :=
  fun _ _ hc _ => (not_typed_store3 ⟨_, rfl⟩ hc).elim

/-- **The float store leaf is vacuous.** -/
theorem fwdAt10_floatStore (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg)
    (c : BitVec 32) (x : BitVec t.width) (s' : Store H) (code' : List Admin) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩
      ⟨s', f, code'⟩ :=
  fun _ _ hc _ => (not_typed_store3 ⟨_, rfl⟩ hc).elim

end Silmaril.Wasm.SpecTec.Sim10.Whole
