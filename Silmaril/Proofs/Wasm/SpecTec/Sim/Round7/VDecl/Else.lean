module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.VDecl.Der
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.Atom
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VDecl.CheckE
public import Silmaril.Wasm.SpecTec.Sim.Round7.VElse.Thms

/-!
# Round 7, memory SIMD: `otherwise` premises move across `withVBytes`

SpecTec's reading of `otherwise` (`Sim.otherwiseAt`): rule `i` of `x` may use its `otherwise`
premise at `v` when no earlier rule fires on the same left-hand side, the earlier rules' premise
relations read by `DDerives env noElse`. For builtins `B₁`, `B₂` that agree off `$vbytes_`:

* `otherwiseAt_agree`: the reading moves from `B₁` to `B₂` at `(i, v)` whenever `P i v`, for any
  `P` that passes to earlier rules on the same left-hand side and under which every rule of `x`
  that is not a `VAgree.GoodRule` never fires (`hbad`). The proof is strong induction on `i`,
  with `ruleBody_rel` (one `GoodRule` body moves across, in either direction) at each earlier
  rule.
* `otherwiseAt_goodRel`: every `GoodRel` relation (all of its rules are `GoodRule`), so the
  `otherwise` reading of every relation other than `Step` and `Step_read` moves across;
  `dderives_otherwise` then moves every `DDerives env (otherwise env)` derivation of a `GoodRel`
  relation.
* `otherwiseAt_read`: `Step_read` at `(i, v)` when `i ≤ 43` or the left-hand side of `v` does not
  end in `VLOAD` (`lhsAtom`). Rule 43 is the only rule of `Step_read` that is not a `GoodRule`,
  and it fires only on left-hand sides ending in `VLOAD` (`lhsAtom_of_eval`, `VElse.read_43_atom`):
  this is the semantic half of the argument of `Round7.VElse`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VDecl

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Round7.Script (evRule evPrems stepReach)
open Round7.VAgree (GoodEvs GoodRel GoodRule ArgOk AgreeOff agreeOff_symm goodEvs_append
  goodRules findRel?_simEnv)

variable {B₁ B₂ : Builtins}

/-! ## One rule body -/

/-- `DDerives _ noElse` of a `GoodRel` relation moves from `B₁` to `B₂`. -/
theorem dderives_noElse (hB : AgreeOff B₁ B₂) {x : IL.Id} {op : MixopS} {args : List ArgV}
    {v : Value} (hx : GoodRel x) (h : DDerives (simEnv B₁) noElse x op args v) :
    DDerives (simEnv B₂) noElse x op args v :=
  dderives_agree hB (fun _ _ _ _ _ h => h) hx h

theorem goodEvs_prems_of_rule {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp}
    {prems : List Prem} (h : GoodEvs (evRule (.ruleD nm qs op e prems))) :
    GoodEvs (evPrems prems) := by
  have h' : (GoodEvs (Round7.Script.evParams qs) ∧ GoodEvs (Round7.Script.evExp e)) ∧
      GoodEvs (evPrems prems) := by
    simpa only [evRule, goodEvs_append] using h
  exact h'.2

/-- **One `GoodRule` body of a relation `Step` reaches moves from `B₁` to `B₂`.** -/
theorem ruleBody_rel (hB : AgreeOff B₁ B₂) {x : IL.Id} (hx : (0, x) ∈ stepReach) {j : Nat}
    (hg : GoodRule x j) {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule}
    (hrel : (simEnv B₁).findRel? x = some (ps, op, t, rules)) (hr : rules[j]? = some r)
    {D₁ D₂ : Interp}
    (hD : ∀ x op args v, GoodRel x → (∀ w ∈ args, ArgOk w) → D₁ x op args v → D₂ x op args v)
    {els₁ els₂ : Prop} (hels : els₁ → els₂) {args : List ArgV} {op' : MixopS} {w : Value}
    (h : RuleBody (simEnv B₁) D₁ els₁ ps args op' r w) :
    RuleBody (simEnv B₂) D₂ els₂ ps args op' r w := by
  have hF := relFacts_of_find hrel hx
  have hps : ps = [] := hF.1
  have hRF : ruleFactsB r = true := hF.2 r (List.mem_of_getElem? hr)
  have hG : GoodEvs (evRule r) := hg B₁ _ r hrel hr
  rw [hps] at h ⊢
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  exact ruleBody_agree hB hD (quant_rg hRF) (alt_rg hRF e List.mem_cons_self)
    (goodEvs_prems_of_rule hG) (fun _ => hels) h

/-! ## `otherwise`, by strong induction -/

/-- The rules of `x` that are not `GoodRule` never fire where `P` holds. -/
def BadSilent (x : IL.Id) (args : List ArgV) (P : Nat → Value → Prop) : Prop :=
  ∀ i v j w, P i v → j < i → SameLhs v w → ¬ GoodRule x j →
    ∀ (B : Builtins) (D : Interp) (els : Prop) ps op t rules r,
      (simEnv B).findRel? x = some (ps, op, t, rules) → rules[j]? = some r →
      ¬ RuleBody (simEnv B) D els ps args op r w

/-- `P` passes to earlier rules on the same left-hand side. -/
def Inherits (P : Nat → Value → Prop) : Prop :=
  ∀ i v j w, P i v → j < i → SameLhs v w → P j w

/-- **`otherwise` moves from `B₁` to `B₂` where `P` holds.** -/
theorem otherwiseAt_agree {x : IL.Id} (hx : (0, x) ∈ stepReach) {args : List ArgV}
    {P : Nat → Value → Prop} (hP : Inherits P) (hbad : BadSilent x args P) (i : Nat) :
    ∀ (B₁ B₂ : Builtins), AgreeOff B₁ B₂ → ∀ v, P i v →
      otherwiseAt (simEnv B₁) x args i v → otherwiseAt (simEnv B₂) x args i v := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro B₁ B₂ hB v hPv h
    rw [otherwiseAt] at h ⊢
    intro j hj ps op t rules r hrel hr w hw hbody
    by_cases hg : GoodRule x j
    · have hB' := agreeOff_symm hB
      have hels : otherwiseAt (simEnv B₂) x args j w → otherwiseAt (simEnv B₁) x args j w :=
        ih j hj B₂ B₁ hB' w (hP i v j w hPv hj hw)
      exact h j hj ps op t rules r ((findRel?_simEnv B₁ B₂ x).trans hrel) hr w hw
        (ruleBody_rel hB' hx hg hrel hr (fun _ _ _ _ hy _ hd => dderives_noElse hB' hy hd) hels
          hbody)
    · exact hbad i v j w hPv hj hw hg B₂ _ _ ps op t rules r hrel hr hbody

/-- Every rule of a `GoodRel` relation is a `GoodRule`. -/
theorem goodRule_of_goodRel {x : IL.Id} (hx : GoodRel x) (j : Nat) : GoodRule x j :=
  fun B _ r hd hr => goodRules B hx hd r (List.mem_of_getElem? hr)

/-- **The `otherwise` reading of a `GoodRel` relation moves from `B₁` to `B₂`.** -/
theorem otherwiseAt_goodRel (hB : AgreeOff B₁ B₂) {x : IL.Id} (hx : GoodRel x)
    (args : List ArgV) (i : Nat) (v : Value) :
    otherwiseAt (simEnv B₁) x args i v → otherwiseAt (simEnv B₂) x args i v :=
  otherwiseAt_agree (P := fun _ _ => True) hx.1 (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ j _ _ _ _ hg => absurd (goodRule_of_goodRel hx j) hg) i B₁ B₂ hB v trivial

/-- **A `DDerives env (otherwise env)` derivation of a `GoodRel` relation moves from `B₁` to
`B₂`.** -/
theorem dderives_otherwise (hB : AgreeOff B₁ B₂) {x : IL.Id} {op : MixopS} {args : List ArgV}
    {v : Value} (hx : GoodRel x) (h : DDerives (simEnv B₁) (otherwise (simEnv B₁)) x op args v) :
    DDerives (simEnv B₂) (otherwise (simEnv B₂)) x op args v :=
  dderives_agree hB (fun _ args i w hy => otherwiseAt_goodRel hB hy args i w) hx h

/-! ## `Step_read` and rule 43 -/

theorem onRel_of_find {α : Type} {B : Builtins} {x : IL.Id} {ps : List Param} {op : MixopS}
    {t : Typ} {rules : List Rule} (f : List Rule → α)
    (h : (simEnv B).findRel? x = some (ps, op, t, rules)) : VElse.onRel x f = some (f rules) := by
  rw [VBytes.findRel?_simEnv_eq] at h
  simp only [VElse.onRel, h, Option.map_some]

/-- Rule 43 of `Step_read` has the atom `VLOAD`. -/
theorem read43_atom {B : Builtins} {ps : List Param} {op : MixopS} {t : Typ} {rules : List Rule}
    {r : Rule} (h : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hr : rules[43]? = some r) : VElse.ruleAtom r = some "VLOAD" := by
  have h₁ := onRel_of_find (fun rules => rules[43]?.bind VElse.ruleAtom) h
  rw [VElse.read_43_atom, hr] at h₁
  simpa only [Option.bind_some, Option.some.injEq] using h₁.symm

/-- **Rule 43 of `Step_read` fires only on left-hand sides ending in `VLOAD`.** -/
theorem lhsAtom_of_read43 {B : Builtins} {D : Interp} {els : Prop} {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule} {args : List ArgV} {op' : MixopS}
    {w : Value} (h : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hr : rules[43]? = some r) (hb : RuleBody (simEnv B) D els ps args op' r w) :
    lhsAtom w = some "VLOAD" := by
  have ha := read43_atom h hr
  obtain ⟨nm, qs, op'', e, prems⟩ := r
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := hb
  exact lhsAtom_of_eval ha he

/-- The condition under which the `otherwise` premises of `Step_read` move across. -/
def ReadP (i : Nat) (v : Value) : Prop := i ≤ 43 ∨ lhsAtom v ≠ some "VLOAD"

theorem readP_inherits : Inherits ReadP := by
  intro i v j w h hj hw
  rcases h with h | h
  · exact .inl (by omega)
  · exact .inr (by rw [← lhsAtom_sameLhs hw]; exact h)

theorem readP_badSilent (args : List ArgV) : BadSilent "Step_read" args ReadP := by
  intro i v j w h hj hw hg B D els ps op t rules r hrel hr hb
  have h43 : j = 43 := by
    by_contra hne
    exact hg (VAgree.goodRule_read hne)
  rw [h43] at hr hj
  have hw' : lhsAtom w = some "VLOAD" := lhsAtom_of_read43 hrel hr hb
  rcases h with h | h
  · omega
  · exact h (by rw [lhsAtom_sameLhs hw]; exact hw')

theorem read_mem_stepReach : (0, "Step_read") ∈ stepReach := by decide +kernel

/-- **The `otherwise` premises of `Step_read` move from `B₁` to `B₂`** at rules up to 43, and
after 43 on left-hand sides that do not end in `VLOAD`. -/
theorem otherwiseAt_read (hB : AgreeOff B₁ B₂) (args : List ArgV) {i : Nat} {v : Value}
    (h : ReadP i v) :
    otherwiseAt (simEnv B₁) "Step_read" args i v → otherwiseAt (simEnv B₂) "Step_read" args i v :=
  otherwiseAt_agree read_mem_stepReach readP_inherits (readP_badSilent args) i B₁ B₂ hB v h

end Silmaril.Wasm.SpecTec.Sim.Round7.VDecl
