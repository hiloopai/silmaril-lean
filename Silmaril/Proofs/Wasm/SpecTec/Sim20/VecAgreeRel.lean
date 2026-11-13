module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeEnvV

/-!
# `simEnv20T` to `simEnv20V`: typing transfers at `VOk` values

* `qEq_exp`: the one quantifier type of the table, `exp`, types alike in `simEnv20X B` and
  `simEnv20V B` (an alias of `int`, never a scope's type variable in a `TN` scope).
* `instsOk_of_B`: the Boolean check `instsOkB` gives `InstsOk`.
* **`famRelV`**: `simEnv20X B` and `simEnv20V B` are a `FamRel` pair at `C = 16`.
* **`hasTyp_TtoV`, `typedV_TtoV`**: what `simEnv20T B` types at a `VOk` value, at a type that
  names no family directly, `simEnv20V B` types too: first across the `VEXTRACT_LANE` repair
  (`hasTyp_toX`, every value), then across the family repair (`VecAgree.hasTyp_vec`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (mem_of_find?)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (TypsOkT goodT_of_all)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (matchArgs_eq evalArgs_eq)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly)

/-! ## The quantifier type `exp` -/

theorem hasTypDef_num_eq {e₁ e₂ : Env} (k : Nat) (ρ : VarEnv) (t : NumTyp) (v : Value) :
    hasTypDef k e₂ ρ (.aliasT (.numT t)) v = hasTypDef k e₁ ρ (.aliasT (.numT t)) v := by
  rcases k with _ | _ | k <;> simp [hasTypDef, hasTyp]

theorem hasTypInsts_exp_eq {e₁ e₂ : Env} (hS : StoreAgree.EnvSame e₁ e₂) (n : Nat)
    (ws : List ArgV) (v : Value) :
    hasTypInsts n e₂ [.instD [] [] (.aliasT (.numT .intT))] ws v =
      hasTypInsts n e₁ [.instD [] [] (.aliasT (.numT .intT))] ws v := by
  rcases n with _ | n
  · simp [hasTypInsts]
  · have hnil : hasTypInsts n e₂ [] ws v = hasTypInsts n e₁ [] ws v := by
      cases n <;> simp [hasTypInsts]
    simp only [hasTypInsts, matchArgs_eq hS, hasTypDef_num_eq (e₁ := e₁) (e₂ := e₂), hnil]

theorem memTyp_expX (B : Builtins) : (simEnv20X B).memTyp "exp" = true := by
  have hf := findTyp_expX (B := B)
  simp only [Env.findTyp?] at hf
  simp only [Env.memTyp, Map.mem, hf, Option.isSome_some]

theorem qEq_exp (B : Builtins) : QEq (simEnv20X B) (simEnv20V B) (.varT "exp" []) := by
  intro n ρ v hN
  have hl : localTyp? ρ "exp" [] = none := by
    cases h : ρ.findTyp? "exp" with
    | none => simpa [localTyp?] using h
    | some t =>
      have hm := hN _ (mem_of_find? h)
      rw [memTyp_expX] at hm
      cases hm
  have hoff : (simEnv20V B).findTyp? "exp" = (simEnv20X B).findTyp? "exp" :=
    findTyp_off_simEnv20V B (by simp [fams])
  rcases n with _ | n
  · simp only [hasTyp]
  simp only [hasTyp, hl]
  rw [hoff, evalArgs_eq (envSameV B)]
  refine ElseAgree.bind_congr' fun td htd => ElseAgree.bind_congr' fun ws _ => ?_
  rw [findTyp_expX] at htd
  simp only [Res.ofOption_eq_ok, Option.some.injEq] at htd
  subst htd
  exact hasTypInsts_exp_eq (envSameV B) n ws v

/-! ## The table check gives `InstsOk` -/

theorem payF?_eq {t : Typ} {f : String} (h : payF? t = some f) : t = payT f := by
  unfold payF? at h
  split at h <;> simp_all [payT, payB, famT]

theorem qsOkB_mem {qs : List Param} (h : qsOkB qs = true) {x : IL.Id} {t : Typ}
    (hm : Param.expP x t ∈ qs) : t = .varT "exp" [] := by
  unfold qsOkB at h
  split at h <;> simp_all

theorem casesOk_of_B {e₁ e₂ : Env} (hq : QEq e₁ e₂ (.varT "exp" [])) {cs : List TypCase}
    (h : cs.all caseOkB = true) : CasesOk e₁ e₂ cs := by
  intro c hc
  obtain ⟨op, t, qs, prems⟩ := c
  have hb := List.all_eq_true.1 h _ hc
  simp only [caseOkB, Bool.and_eq_true, Bool.or_eq_true] at hb
  obtain ⟨hpay, hqs⟩ := hb
  refine ⟨?_, fun x t' hm => by rw [qsOkB_mem hqs hm]; exact hq⟩
  rcases hpay with hf | hp
  · exact Or.inl (goodT_of_all hf)
  · right
    revert hp
    cases hpf : payF? t with
    | none => simp
    | some f =>
      intro hp
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      exact ⟨f, by simpa using hp.1, payF?_eq hpf, hp.2⟩

theorem instsOk_of_B {e₁ e₂ : Env} (hq : QEq e₁ e₂ (.varT "exp" [])) {is : List Inst}
    (h : instsOkB is = true) : InstsOk e₁ e₂ is := by
  intro i hi
  obtain ⟨qs, pats, dt⟩ := i
  have hd := List.all_eq_true.1 h _ hi
  cases dt with
  | aliasT t => exact goodT_of_all hd
  | structT fs =>
    intro f hf
    obtain ⟨a, t, qs', prems⟩ := f
    exact goodT_of_all (List.all_eq_true.1 hd _ hf)
  | variantT cs => exact casesOk_of_B hq hd

/-! ## The pair -/

theorem instsOk_X (B : Builtins) {x : IL.Id} {td : TypDef} (hd : (simEnv20X B).findTyp? x = some td) :
    InstsOk (simEnv20X B) (simEnv20V B) td.2 := by
  have hm : (x, td) ∈ typsOfDefs fixedX20 := by
    have h' : (typsOfDefs fixedX20).find? x = some td := by
      simpa [simEnv20X, Env.withBuiltins, Env.findTyp?, envOfScript, envOfDefs_eq, Env.empty,
        Map.empty] using hd
    exact mem_of_find? h'
  exact instsOk_of_B (qEq_exp B) (List.all_eq_true.1 tableOkB_fixedX20 _ hm)

/-- One family of the pair. -/
theorem famRel_one {B : Builtins} {f : String} {d d' : Def} (hf : FamForm d d' f)
    (hX : (simEnv20X B).findTyp? f = some (typDecl d))
    (hV : (simEnv20V B).findTyp? f = some (typDecl d')) (hl : (fNames f).length ≤ 8) :
    ∀ td, (simEnv20X B).findTyp? f = some td → ∃ is₂, (simEnv20V B).findTyp? f = some (td.1, is₂) ∧
      (∀ a k v, ¬ FloatSh a → hasTypInsts (k + 16 + 2) (simEnv20V B) is₂ [.val a] v =
        hasTypInsts (k + 16) (simEnv20V B) td.2 [.val a] v) ∧
      (∀ a o k, FloatSh a → o ∈ fNames f →
        hasTypInsts (k + 16) (simEnv20V B) is₂ [.val a] (.case o (.tuple [])) = .ok true) := by
  intro td htd
  rw [hX] at htd
  cases htd
  obtain ⟨ps, ji, bs, pats, h₁, h₂⟩ := hf
  rw [h₁]
  rw [h₂] at hV
  exact ⟨_, hV, fun a k v ha => hasTypInsts_skip k ha, fun a o k ha ho => hasTypInsts_float k hl ha ho⟩

/-- **`simEnv20X B` and `simEnv20V B` are a `FamRel` pair.** -/
theorem famRelV (B : Builtins) : FamRel (simEnv20X B) (simEnv20V B) 16 := by
  obtain ⟨hV₁, hV₂, hV₃⟩ := findTyp_fam_simEnv20V B
  refine ⟨fun x td hx hd => (findTyp_off_simEnv20V B hx).trans hd, fun f hf => ?_,
    fun x td hd => instsOk_X B hd⟩
  simp only [fams, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact famRel_one famForm_vunop findTyp_vunopX hV₁ (by decide)
  · exact famRel_one famForm_vbinop findTyp_vbinopX hV₂ (by decide)
  · exact famRel_one famForm_vrelop findTyp_vrelopX hV₃ (by decide)

/-! ## The transfer -/

/-- **Typing transfers from `simEnv20T B` to `simEnv20V B` at `VOk` values.** -/
theorem hasTyp_TtoV {B : Builtins} {ρ : VarEnv} {t : Typ} {v : Value} (hT : TypsOkT fams ρ)
    (hN : TN (simEnv20X B) ρ) (ht : TOk ρ t v) (hv : VOk v) (h : HasTyp (simEnv20T B) ρ t v) :
    HasTyp (simEnv20V B) ρ t v :=
  hasTyp_vec (envSameV B) (famRelV B) hT hN ht hv (hasTyp_toX h)

/-- **`TypedV` transfers from `simEnv20T B` to `simEnv20V B`** at a `VOk` value, at a type that
names no family directly. -/
theorem typedV_TtoV {B : Builtins} {t : Typ} {v : Value} (ht : ffT t) (hv : VOk v)
    (h : TypedV (simEnv20T B) t v) : TypedV (simEnv20V B) t v := by
  intro ρ hρ
  refine hasTyp_TtoV ?_ ?_ (Or.inl ht) hv (h ρ hρ)
  · intro p hp; rw [hρ.1] at hp; cases hp
  · intro p hp; rw [hρ.1] at hp; cases hp

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
