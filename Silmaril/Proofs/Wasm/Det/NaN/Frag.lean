module

public import Silmaril.Proofs.Wasm.Det.NaN.Canon

/-!
# The fragment: structural lemmas (proofs)

`NAdms` distributes over appending, holds of values, of `expression b` exactly when
`nanInstrs b`, and is invariant under canonicalisation (`nCfg_canon`); `nanCheck` decides
`NFuncs` (`nFuncs_of_nanCheck`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NaN

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Det.NaN

variable {set : Bool}

@[simp] theorem nAdms_nil : NAdms set [] := trivial

@[simp] theorem nAdms_cons {a : Admin} {l : List Admin} :
    NAdms set (a :: l) ↔ NAdm set a ∧ NAdms set l := Iff.rfl

@[simp] theorem nAdms_append : ∀ {l l' : List Admin},
    NAdms set (l ++ l') ↔ NAdms set l ∧ NAdms set l'
  | [], _ => by simp only [List.nil_append, nAdms_nil, true_and]
  | a :: l, l' => by simp only [List.cons_append, nAdms_cons, nAdms_append, and_assoc]

@[simp] theorem nAdm_toAdmin (v : Val) : NAdm set v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin, NAdm, nanInstr, floatOk]

@[simp] theorem nAdms_vals (vs : List Val) : NAdms set (vals vs) := by
  induction vs with
  | nil => trivial
  | cons v vs ih => exact ⟨nAdm_toAdmin v, ih⟩

@[simp] theorem nAdm_constI32 (b : BitVec 32) : NAdm set (constI32 b) := nAdm_toAdmin _

theorem nanInstrs_iff : ∀ {b : List Instr}, nanInstrs set b = true ↔ ∀ i ∈ b, nanInstr set i = true
  | [] => by simp [nanInstrs]
  | i :: b => by simp only [nanInstrs, Bool.and_eq_true, nanInstrs_iff, List.mem_cons,
      forall_eq_or_imp]

theorem nAdms_expression : ∀ {b : List Instr}, NAdms set (expression b) ↔ nanInstrs set b = true
  | [] => by simp [expression, nanInstrs]
  | i :: b => by
    simp only [expression, List.map_cons, nAdms_cons, nanInstrs, Bool.and_eq_true]
    exact and_congr Iff.rfl nAdms_expression

theorem nanInstr_canon (i : Instr) : nanInstr set (canonInstr i) = nanInstr set i := by
  cases i <;> rfl

mutual
theorem nAdm_canon : ∀ a : Admin, NAdm set (canonAdmin a) ↔ NAdm set a
  | .plain i => by simp only [canonAdmin_plain, NAdm, nanInstr_canon]
  | .label n cont body => by simp only [canonAdmin_label, NAdm, nAdms_canon body]
  | .handler n cs body => by simp only [canonAdmin_handler, NAdm]
  | .frame n f body => by simp only [canonAdmin_frame, NAdm, nAdms_canon body]
  | .ref _ => Iff.rfl
  | .callRefType _ => Iff.rfl
  | .returnCallRefType _ => Iff.rfl
  | .trap => Iff.rfl

theorem nAdms_canon : ∀ l : List Admin, NAdms set (canonAdmins l) ↔ NAdms set l
  | [] => Iff.rfl
  | a :: l => by simp only [canonAdmins_cons, nAdms_cons, nAdm_canon a, nAdms_canon l]
end

theorem nCfg_canon {c : Config Nat} : NCfg set (canonCfg c) ↔ NCfg set c := by
  simp only [NCfg, canonCfg, nAdms_canon, canonStore_funcs]

theorem nFuncs_of_nanCheck {s : Store Nat} (h : nanCheck set s = true) : NFuncs set s.funcs := by
  intro fi hfi fn hfn
  have h' := List.all_eq_true.mp h fi hfi
  simpa only [hfn] using h'

/-- The body of a Wasm function of an `NFuncs` store is in the fragment. -/
theorem nFuncs_body {F : List (FuncInst Nat)} (hF : NFuncs set F) {a : Nat} {fi : FuncInst Nat}
    (hfi : F[a]? = some fi) {fn : Func} (hcode : fi.code = .wasm fn) :
    NAdms set (expression fn.body) :=
  nAdms_expression.mpr (hF fi (List.mem_of_getElem? hfi) fn hcode)

/-- The invocation of any function of an `NFuncs` store is in the fragment. -/
theorem nCfg_invoke {s : Store Nat} (hF : NFuncs set s.funcs) (a : Nat) (vs : List Val) :
    NCfg set (invoke s a vs) := by
  refine ⟨?_, hF⟩
  simp only [invoke, nAdms_append, nAdms_vals, nAdms_cons, nAdms_nil, true_and]
  exact ⟨trivial, trivial, trivial⟩

end Silmaril.Proofs.Wasm.Det.NaN
