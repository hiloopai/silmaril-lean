module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.Determ.Fwd

/-!
# Round 7, determination: evaluation on scopes that are `ExpFree` where it matters

`Round7.Determ.evalEF` needs every value of the scope to be `ExpFree`. A rule instance's scope may
also bind names that are not its quantifiers, to anything. The evaluator reads only the free
variables of the expression (`Silmaril.SpecTec.Sem.evalExp_agreeOn`), so it is enough that those
are `ExpFree`: the scope `efPart ρ`, which keeps only the `ExpFree` bindings of `ρ`, agrees with
`ρ` on them.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree)

open Classical in
/-- The `ExpFree` bindings of `ρ`. -/
noncomputable def efPart (ρ : VarEnv) : VarEnv :=
  { ρ with vals := ρ.vals.filter fun p => decide (ExpFree p.2) }

theorem allEF_efPart (ρ : VarEnv) : AllEF (efPart ρ) := by
  intro p hp
  simp only [efPart, List.mem_filter, decide_eq_true_eq] at hp
  exact hp.2

theorem defsOk_efPart {ρ : VarEnv} (h : DefsOk ρ) : DefsOk (efPart ρ) := h

open Classical in
theorem find?_filter_ef {x : IL.Id} :
    ∀ l : Map Value, (∀ w, Map.find? l x = some w → ExpFree w) →
      Map.find? (l.filter fun p => decide (ExpFree p.2)) x = Map.find? l x
  | [], _ => rfl
  | (y, v) :: l, h => by
    by_cases hy : y = x
    · subst hy
      have hv : ExpFree v := h v (by simp)
      simp [hv]
    · have hl : ∀ w, Map.find? l x = some w → ExpFree w := fun w hw => h w (by simp [hy, hw])
      by_cases hv : ExpFree v <;>
        simp [hv, hy, find?_filter_ef l hl]

theorem fvIn_mem {K : List IL.Id} {e : Exp} (h : fvIn K e = true) :
    ∀ x ∈ (freeExp e).varid, x ∈ K := of_decide_eq_true h

theorem agreeOn_efPart {ρ : VarEnv} {K : List IL.Id} {e : Exp} (hK : EFOn ρ K)
    (hfv : fvIn K e = true) : VarEnv.AgreeOn (freeExp e) ρ (efPart ρ) := by
  refine ⟨fun x hx => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hx' : ∀ w, Map.find? ρ.vals x = some w → ExpFree w := hK x (fvIn_mem hfv x hx)
  exact (find?_filter_ef ρ.vals hx').symm

/-- **The evaluator answers an `ExpFree` value** when the free variables of the expression are
bound to `ExpFree` values. -/
theorem ef_eval_on {B : Builtins} (hB : BuiltinsEF B) {ρ : VarEnv} {K : List IL.Id} {e : Exp}
    {v : Value} (hD : DefsOk ρ) (hG : GoodXs (evExp e)) (hK : EFOn ρ K) (hfv : fvIn K e = true)
    (h : EvalExp (utf8Env B) ρ e v) : ExpFree v := by
  obtain ⟨n, hn⟩ := h
  have heq : evalExp n (utf8Env B) ρ e = evalExp n (utf8Env B) (efPart ρ) e :=
    evalExp_agreeOn (agreeOn_efPart hK hfv)
  exact (evalEF B hB n).exp _ _ _ (allEF_efPart ρ) (defsOk_efPart hD) hG (heq ▸ hn)

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
