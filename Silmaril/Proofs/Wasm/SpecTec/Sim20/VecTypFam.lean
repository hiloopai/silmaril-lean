module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTyp20

/-!
# A typed operator instruction types its operator at the family

The rules `vunop`, `vbinop-val` and `vrelop` of `Step_pure` quantify the operator at the family
`vunop_(sh)` (`vbinop_(sh)`, `vrelop_(sh)`). For the float operators round 7 computed that
typing (`VecLane.hasTyp_famFloat`). For the integer operators the family's integer instance has
premises (`POPCNT` only at `I8`, `MUL` only from 16 bits, …), so the operator is typed exactly
when the instruction is valid. Instead of computing the 79 valid pairs, this module reads the
family typing off a typed instruction:

* **`famInsts_of_admin`** (generic): if `admininstr` is a one-instance variant whose only case
  named `o` carries `payT f` (`shape` then `f(shape)`), then a typed `o(a, b)` makes `b` inhabit
  `f`'s instances at the argument `a`;
* `hasTyp_fam_scope`: so `b` has type `f(sh)` in every scope binding `sh` to `a`;
* `admin_simEnv20V` (by `rfl`): in `simEnv20V B` the cases `VUNOP`, `VBINOP` and `VRELOP` of
  `admininstr` are unique and carry `payT`;
* **`hasTyp_famOf_typedA`**: in `simEnv20V B`, a typed `VUNOP(a, b)` (`VBINOP`, `VRELOP`) gives
  `b : vunop_(sh)` wherever `sh` is bound to `a`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecAgree (payT payB famT)

/-- A variant case named `o`. -/
def caseNamed (o : String) (c : TypCase) : Bool :=
  match c with
  | .mk o' _ _ _ => o' == o

/-! ## Inversions -/

theorem evalArgs_nil_inv {env : Env} {ρ : VarEnv} {ws : List ArgV} (h : EvalArgs env ρ [] ws) :
    ws = [] := by
  obtain ⟨n, h⟩ := h
  rcases n with _ | n
  · simp [evalArgs] at h
  · simp only [evalArgs, List.mapM_nil] at h
    exact (Except.ok.inj h).symm

theorem evalArgs_var {env : Env} {ρ : VarEnv} {x : IL.Id} {a : Value}
    (hx : ρ.findVal? x = some a) : EvalArgs env ρ [.expA (.varE x)] [.val a] :=
  ⟨3, by simp [evalArgs, evalArg, evalExp, hx, Res.ofOption]⟩

theorem evalArgs_var_inv {env : Env} {ρ : VarEnv} {x : IL.Id} {a : Value} {ws : List ArgV}
    (hx : ρ.findVal? x = some a) (h : EvalArgs env ρ [.expA (.varE x)] ws) : ws = [.val a] := by
  obtain ⟨n, h⟩ := h
  have h' := (evalArgs_var (env := env) hx)
  obtain ⟨m, hm⟩ := h'
  have := ((monoAt_of_le (Nat.le_max_left n m)).args env ρ _).ok h
  have := ((monoAt_of_le (Nat.le_max_right n m)).args env ρ _).ok hm
  simp_all

theorem matchArgs_nil_inv {env : Env} {σ : VarEnv} (h : MatchArgs env VarEnv.empty [] [] σ) :
    σ = VarEnv.empty := by
  obtain ⟨n, h⟩ := h
  rcases n with _ | n
  · simp [matchArgs] at h
  · simp only [matchArgs] at h
    exact (Except.ok.inj h).symm

/-! ## The family typing of a typed operator instruction -/

/-- A typed `admininstr` case, when `admininstr` is a one-instance variant: its case typing. -/
theorem caseOf_admin {env : Env} {ρ : VarEnv} (hρ : ρ.typs = []) {cs : List TypCase}
    (hA : env.findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)])) {o : String}
    {w : Value} (h : HasTyp env ρ (.varT "admininstr" []) (.case o w)) :
    HasTypCase env VarEnv.empty cs o w := by
  have hl : localTyp? ρ "admininstr" [] = none := by
    simp [localTyp?, VarEnv.findTyp?, hρ]
  obtain ⟨td, ws, htd, hws, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  have htd' : td = ([], [.instD [] [] (.variantT cs)]) := by
    rw [hA] at htd
    exact (Option.some.inj htd).symm
  have hws' : ws = [] := evalArgs_nil_inv hws
  subst htd' hws'
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hi'
  · have hσ : σ = VarEnv.empty := matchArgs_nil_inv hm
    subst hσ
    obtain ⟨op, w', he, hcase⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨rfl, rfl⟩ : o = op ∧ w = w' := by simpa using he
    exact hcase
  · exact absurd hi' not_hasTypInsts_nil

/-- The case `o`, carrying `payT f`: the operator inhabits `f`'s instances at the shape. -/
theorem famInsts_of_case {env : Env} {cs : List TypCase} {o f : String}
    (hc : cs.filter (caseNamed o) = [.mk o (payT f) [] []]) {a b : Value}
    (h : HasTypCase env VarEnv.empty cs o (.tuple [a, b])) :
    ∃ td, env.findTyp? f = some td ∧ HasTypInsts env td.2 [.val a] b := by
  obtain ⟨t, qs, prems, hmem, ht, -⟩ := hasTypCase_mem h
  have hmem' : TypCase.mk o t qs prems ∈ [TypCase.mk o (payT f) [] []] := by
    rw [← hc]
    exact List.mem_filter.2 ⟨hmem, by simp [caseNamed]⟩
  have hcase : t = payT f ∧ qs = [] ∧ prems = [] := by simpa using hmem'
  have htf : t = payT f := hcase.1
  subst htf
  obtain ⟨vs, hv, htup⟩ := hasTyp_tupT_iff.1 ht
  obtain rfl : vs = [a, b] := (Value.tuple.inj hv).symm
  obtain ⟨w₁, ws₁, h₁, -, htup'⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ : w₁ = a ∧ ws₁ = [b] := by simpa using h₁.symm
  obtain ⟨w₂, ws₂, h₂, hb, -⟩ := hasTypTup_cons_iff.1 htup'
  obtain ⟨rfl, rfl⟩ : w₂ = b ∧ ws₂ = [] := by simpa using h₂.symm
  obtain ⟨td', ws', htd', hws', hi'⟩ := (hasTyp_varT_global_iff rfl).1 hb
  have hws'' : ws' = [.val w₁] := evalArgs_var_inv rfl hws'
  exact ⟨td', htd', hws'' ▸ hi'⟩

/-- **A typed operator instruction types its operator at the family's instances.** -/
theorem famInsts_of_admin {env : Env} {ρ : VarEnv} (hρ : ρ.typs = []) {cs : List TypCase}
    {o f : String} (hA : env.findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)]))
    (hc : cs.filter (caseNamed o) = [.mk o (payT f) [] []]) {a b : Value}
    (h : HasTyp env ρ (.varT "admininstr" []) (.case o (.tuple [a, b]))) :
    ∃ td, env.findTyp? f = some td ∧ HasTypInsts env td.2 [.val a] b :=
  famInsts_of_case hc (caseOf_admin hρ hA h)

/-- The family read in a scope binding `sh`. -/
theorem hasTyp_fam_scope {env : Env} {ρ : VarEnv} {f : String} {td : TypDef} {a b : Value}
    (hf : env.findTyp? f = some td) (hi : HasTypInsts env td.2 [.val a] b)
    (hx : ρ.findVal? "sh" = some a) : HasTyp env ρ (.varT f [.expA (.varE "sh")]) b :=
  (hasTyp_varT_global_iff rfl).2 ⟨td, _, hf, evalArgs_var hx, hi⟩

/-! ## The 2.0 instance -/

set_option maxRecDepth 100000 in
/-- **`admininstr` of `simEnv20V B`**: one instance, and the three operator cases are unique and
carry `payT` (by `rfl`). -/
theorem admin_simEnv20V (B : Builtins) : ∃ cs,
    (simEnv20V B).findTyp? "admininstr" = some ([], [.instD [] [] (.variantT cs)]) ∧
    cs.filter (caseNamed "VUNOP") = [.mk "VUNOP" (payT "vunop_") [] []] ∧
    cs.filter (caseNamed "VBINOP") = [.mk "VBINOP" (payT "vbinop_") [] []] ∧
    cs.filter (caseNamed "VRELOP") = [.mk "VRELOP" (payT "vrelop_") [] []] :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- **In `simEnv20V B`, a typed operator instruction types its operator at the family**, in
every scope binding `sh` to its shape. -/
theorem hasTyp_famOf_typedA {B : Builtins} {o f : String}
    (hof : (o = "VUNOP" ∧ f = "vunop_") ∨ (o = "VBINOP" ∧ f = "vbinop_") ∨
      (o = "VRELOP" ∧ f = "vrelop_")) {a b : Value}
    (h : TypedV (simEnv20V B) (.varT "admininstr" []) (.case o (.tuple [a, b]))) {ρ : VarEnv}
    (hx : ρ.findVal? "sh" = some a) :
    HasTyp (simEnv20V B) ρ (.varT f [.expA (.varE "sh")]) b := by
  obtain ⟨cs, hA, h₁, h₂, h₃⟩ := admin_simEnv20V B
  have hc : cs.filter (caseNamed o) = [.mk o (payT f) [] []] := by
    rcases hof with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h₁
    · exact h₂
    · exact h₃
  obtain ⟨td, hf, hi⟩ := famInsts_of_admin rfl hA hc (h VarEnv.empty ⟨rfl, rfl, rfl⟩)
  exact hasTyp_fam_scope hf hi hx

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
