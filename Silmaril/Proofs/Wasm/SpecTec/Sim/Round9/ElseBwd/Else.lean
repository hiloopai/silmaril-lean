module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseBwd.Head

/-!
# Round 9, `otherwise` rules: the transfer along a map, from heads and the pairs left

For any map `ε` of values that takes pairs to pairs and keeps heads (`vHead`):

* `otherwiseAtB_map` (SpecTec's reading, RE): if rule `i` fired at `v` and its `otherwise` premise
  holds there, it holds at `ε v` on the image side, given `PairReflectB` at every earlier rule
  whose head is not known to differ.
* `otherwiseAt_map` (the declarative reading, RM): the same for `Sim.otherwiseAt`, given
  `PairReflectD`.

At an earlier rule whose head differs, the rule cannot fire at `(ε a, c')`: its conclusion has
another head than `ε v`, whose head is that of `v` (`vHead_eval`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (DDerivesB RuleBodyB otherwiseAtB conclAlts)

theorem headNe_true {e₁ e₂ : Exp} (h : headNe e₁ e₂ = true) :
    ∃ o₁ o₂, lhsHead e₁ = some o₁ ∧ lhsHead e₂ = some o₂ ∧ o₁ ≠ o₂ := by
  unfold headNe at h
  split at h
  · rename_i o₁ o₂ h₁ h₂
    exact ⟨o₁, o₂, h₁, h₂, by simpa using h⟩
  · cases h

/-- Heads that differ at two alternatives of two rules. -/
theorem headsDiffer_alt {nm₁ nm₂ : IL.Id} {qs₁ qs₂ : List Param} {op₁ op₂ : MixopS}
    {e₁ e₂ : Exp} {ps₁ ps₂ : List Prem}
    (h : headsDiffer (.ruleD nm₁ qs₁ op₁ e₁ ps₁) (.ruleD nm₂ qs₂ op₂ e₂ ps₂) = true)
    {a b : Exp} (ha : a ∈ conclAlts e₁) (hb : b ∈ conclAlts e₂) : headNe a b = true := by
  simp only [headsDiffer, List.all_eq_true] at h
  exact h a ha b hb

/-- **Two firings at the same left-hand side have the same head**: if `ε` keeps heads, the
conclusion alternatives `e₁` (at `v`) and `e₂` (at `(ε a, c')`, where `ε v = (ε a, b')`) cannot
have different known heads. -/
theorem heads_clash {env : Env} {ε : Value → Value} (hh : ∀ v, vHead (ε v) = vHead v)
    {ρ₁ ρ₂ : VarEnv} {e₁ e₂ : Exp} {a b b' c' : Value}
    (hv : ε (.tuple [a, b]) = .tuple [ε a, b']) (h₁ : EvalExp env ρ₁ e₁ (.tuple [a, b]))
    (h₂ : EvalExp env ρ₂ e₂ (.tuple [ε a, c'])) (hne : headNe e₁ e₂ = true) : False := by
  obtain ⟨o₁, o₂, ho₁, ho₂, hne⟩ := headNe_true hne
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  have hv₁ := vHead_eval ho₁ hn₁
  have hv₂ := vHead_eval ho₂ hn₂
  rw [vHead_pair _ _ b', ← hv, hh, hv₁] at hv₂
  exact hne (Option.some.inj hv₂)

/-! ## SpecTec's reading -/

/-- **SpecTec's `otherwise` goes along `ε`**, given the backward firing at the pairs left. -/
theorem otherwiseAtB_map {env : Env} {ε : Value → Value}
    (hε : ∀ v a' b', ε v = .tuple [a', b'] → ∃ a b, v = .tuple [a, b] ∧ a' = ε a)
    (hh : ∀ v, vHead (ε v) = vHead v) {x : IL.Id} {args args' : List ArgV} {i : Nat} {v : Value}
    (hF : Round8.NxElse.Fired env x args i v)
    (hR : ∀ j < i, ∀ ps op t rules ri rj, env.findRel? x = some (ps, op, t, rules) →
      rules[i]? = some ri → rules[j]? = some rj → headsDiffer ri rj = false →
      PairReflectB env ε x args args' i j)
    (h : otherwiseAtB env x args i v) : otherwiseAtB env x args' i (ε v) := by
  rw [otherwiseAtB] at h ⊢
  intro j hj ps op t rules r hrel hr w hw hbody
  obtain ⟨a₀, b₀, c', hv, rfl⟩ := hw
  obtain ⟨a, b, rfl, rfl⟩ := hε _ _ _ hv
  have hF' := hF
  obtain ⟨ps', op', t', rules', nm, qs, e, prems, e', ρ₀, σ, hrel', hrule, -, halt, -, -, hev⟩ := hF'
  rw [hrel] at hrel'
  cases hrel'
  cases hd : headsDiffer (.ruleD nm qs op e prems) r with
  | false =>
    obtain ⟨c, hc⟩ := hR j hj ps op t rules _ r hrel hrule hr hd ps op t rules r hrel hr a b c' hF
      hbody
    exact h j hj ps op t rules r hrel hr (.tuple [a, c]) ⟨a, b, c, rfl, rfl⟩ hc
  | true =>
    obtain ⟨nm₂, qs₂, op₂, e₂, prems₂⟩ := r
    obtain ⟨e'', halt'', -, ρ₂, σ₂, -, -, hev₂, -⟩ := hbody
    exact heads_clash hh hv hev hev₂ (headsDiffer_alt hd halt halt'')

/-! ## The declarative reading -/

/-- **The declarative `otherwise` goes along `ε`**, given the backward firing at the pairs
left. -/
theorem otherwiseAt_map {env : Env} {ε : Value → Value}
    (hε : ∀ v a' b', ε v = .tuple [a', b'] → ∃ a b, v = .tuple [a, b] ∧ a' = ε a)
    (hh : ∀ v, vHead (ε v) = vHead v) {x : IL.Id} {args args' : List ArgV} {i : Nat} {v : Value}
    (hF : FiredD env x args i v)
    (hR : ∀ j < i, ∀ ps op t rules ri rj, env.findRel? x = some (ps, op, t, rules) →
      rules[i]? = some ri → rules[j]? = some rj → headsDiffer ri rj = false →
      PairReflectD env ε x args args' i j)
    (h : Sim.otherwiseAt env x args i v) : Sim.otherwiseAt env x args' i (ε v) := by
  rw [Sim.otherwiseAt] at h ⊢
  intro j hj ps op t rules r hrel hr w hw hbody
  obtain ⟨a₀, b₀, c', hv, rfl⟩ := hw
  obtain ⟨a, b, rfl, rfl⟩ := hε _ _ _ hv
  have hF' := hF
  obtain ⟨ps', op', t', rules', nm, qs, e, prems, ρ₀, σ, hrel', hrule, -, -, hev⟩ := hF'
  rw [hrel] at hrel'
  cases hrel'
  cases hd : headsDiffer (.ruleD nm qs op e prems) r with
  | false =>
    obtain ⟨c, hc⟩ := hR j hj ps op t rules _ r hrel hrule hr hd ps op t rules r hrel hr a b c' hF
      hbody
    exact h j hj ps op t rules r hrel hr (.tuple [a, c]) ⟨a, b, c, rfl, rfl⟩ hc
  | true =>
    obtain ⟨nm₂, qs₂, op₂, e₂, prems₂⟩ := r
    obtain ⟨-, ρ₂, σ₂, -, -, hev₂, -⟩ := hbody
    exact heads_clash hh hv hev hev₂
      (headsDiffer_alt hd (List.mem_cons_self) (List.mem_cons_self))

/-! ## The two erasures -/

theorem eraseV_tuple2 (a b : Value) :
    Swap.eraseV (.tuple [a, b]) = .tuple [Swap.eraseV a, Swap.eraseV b] := rfl

theorem eraseC_tuple2 (a b : Value) :
    Round8.CodeErase.Swap.eraseC (.tuple [a, b]) =
      .tuple [Round8.CodeErase.Swap.eraseC a, Round8.CodeErase.Swap.eraseC b] := rfl

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
