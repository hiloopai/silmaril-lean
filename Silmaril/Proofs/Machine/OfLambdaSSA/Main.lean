module

public import Silmaril.Proofs.Machine.OfLambdaSSA.RootIff

/-!
# `ofLambdaSSA` is correct on its fragment
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.OfLambdaSSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.OfLambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {sigs : List Silmaril.Machine.RTL.Signature} {oracle : CallOracle}

/-- A run outcome determines the root exit it came from. -/
theorem eval_of_outcome {fn : SSA.Func ℕ} {fr : Frame ℕ} {m m' : Memory} {results ℓ : ℕ}
    {v : Value Word} {P : ℕ → Value Word → Memory → Prop}
    (back : ∀ out, Func.Exec oracle fn 0 fr m out →
      ∃ ℓ' vs m'', P ℓ' (packValues vs) m'' ∧ ExitOk [results, 0] ℓ' (packValues vs) ∧
        out = rootExit ℓ' vs m'')
    (h : RootOutcome oracle fn fr m ℓ v m') : P ℓ v m' := by
  rcases h with ⟨rfl, vs, rfl, hex⟩ | ⟨rfl, rfl, hex⟩
  · obtain ⟨ℓ', vs', m'', hP, ⟨w, ws, hw, hv, -⟩, hout⟩ := back _ hex
    match ℓ', hw, hout with
    | 0, _, hout =>
      obtain ⟨rfl, rfl⟩ := Exit.returned.inj hout
      exact hP
    | 1, _, hout => simp [rootExit] at hout
  · obtain ⟨ℓ', vs', m'', hP, ⟨w, ws, hw, hv, hlen⟩, hout⟩ := back _ hex
    match ℓ', hw, hout with
    | 0, _, hout => simp [rootExit] at hout
    | 1, hw, hout =>
      obtain rfl : m'' = m' := (Exit.trapped.inj hout).symm
      obtain rfl : w = 0 := by simpa using hw.symm
      obtain rfl := packValues_injective hv
      obtain rfl : vs' = [] := List.eq_nil_of_length_eq_zero hlen
      exact hP

/-- The wrapper root compiles its block as block `0`. -/
theorem rootOps_wrapper {blocks : Fin 1 → Region (Opcode sigs)} {ab : Ann} {params results : ℕ}
    {ops : List (Op ℕ)} {t : Term ℕ} {e : Emit}
    (hroot : rootOps sigs (.cfg (.br 0 (.var 0)) 1 blocks) (.cfg [params] .br [ab]) params results =
      some (ops, t, e)) :
    regionOps (blocks 0) ab [freshRegs 0 params]
      (inner 0 [params] 1 ++ rootLabels results) (start params) = some (ops, t, e) := by
  have labels : inner 0 [params] 1 ++ rootLabels results =
      [(.block 0, params), (.ret, results), (.trap, 0)] := by
    rw [inner_one]
    rfl
  unfold rootOps at hroot
  split at hroot
  · rename_i heq hw
    cases heq
    cases hw
    rw [ite_eq_left rfl] at hroot
    rw [labels]
    exact hroot
  · rename_i hnot
    exact absurd rfl fun h => hnot _ _ _ h rfl

/-- What `rootOps` compiles to, on a root of the fragment. -/
theorem root_cases {r : Region (Opcode sigs)} {a : Ann} {params results : ℕ}
    (hfit : RootFits sigs r a params results) {ops : List (Op ℕ)} {t : Term ℕ} {e : Emit}
    (hroot : rootOps sigs r a params results = some (ops, t, e)) :
    (∃ blocks ab, r = .cfg (.br 0 (.var 0)) 1 blocks ∧
        RegionFits sigs [.tuple params] (blocks 0) ab [params, results, 0] ∧
        regionOps (blocks 0) ab [freshRegs 0 params]
          (inner 0 [params] 1 ++ rootLabels results) (start params) = some (ops, t, e)) ∨
      (RegionFits sigs [.tuple params] r a [results, 0] ∧
        regionOps r a [freshRegs 0 params] (rootLabels results) (start params) = some (ops, t, e)) := by
  unfold RootFits at hfit
  split at hfit
  · rename_i blocks w ab
    obtain ⟨rfl, hfits⟩ := hfit
    exact Or.inl ⟨blocks, ab, rfl, hfits, rootOps_wrapper hroot⟩
  · rename_i hnot
    unfold rootOps at hroot
    split at hroot
    · rename_i blocks w ab
      exact absurd rfl fun h => hnot blocks w ab h rfl
    · exact Or.inr ⟨hfit, hroot⟩

/-- **The compiled function runs exactly as the region evaluates.** -/
theorem eval_iff_outcome (hsigs : CallOracle.MatchesSigs oracle sigs) {r : Region (Opcode sigs)}
    {a : Ann} {params results : ℕ} (hfit : RootFits sigs r a params results) {ops : List (Op ℕ)}
    {t : Term ℕ} {e : Emit} (hroot : rootOps sigs r a params results = some (ops, t, e))
    {fr : Frame ℕ} {args : List Word} (hfr : fr.readAll (freshRegs 0 params) = some args)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m m' : Memory} {ℓ : ℕ}
    {v : Value Word} :
    Semantics.Region.Eval (Opcode.step oracle) env r m ℓ v m' ↔
      RootOutcome oracle (rootFn params results ops t e) fr m ℓ v m' := by
  rcases root_cases hfit hroot with ⟨blocks, ab, rfl, hfits, hc⟩ | ⟨hfits, hc⟩
  · exact ⟨wrap_forward hsigs hfits hc hfr henv,
      eval_of_outcome fun _ hex => wrap_backward hfits hc hfr henv hex⟩
  · exact ⟨plain_forward hsigs hfits hc hfr henv,
      eval_of_outcome fun _ hex => plain_backward hfits hc hfr henv hex⟩

/-- **Correctness of `ofLambdaSSA` on the fragment.** -/
theorem ofLambdaSSA_eval_iff (hsigs : CallOracle.MatchesSigs oracle sigs)
    {r : Region (Opcode sigs)} {a : Ann} {params results : ℕ}
    (hc : Compiles sigs r a params results) (hfit : RootFits sigs r a params results)
    {fr : Frame ℕ} {args : List Word} (hfr : fr.readAll (freshRegs 0 params) = some args)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m m' : Memory} {label : ℕ}
    {value : Value Word} :
    Semantics.Region.Eval (Opcode.step oracle) env r m label value m' ↔
      (label = 0 ∧ ∃ vs, value = packValues vs ∧
          Func.Exec oracle (ofLambdaSSA sigs r a params results) 0 fr m (.returned vs m')) ∨
      (label = 1 ∧ value = .unit ∧
          Func.Exec oracle (ofLambdaSSA sigs r a params results) 0 fr m (.trapped m')) := by
  obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp hc
  rw [ofLambdaSSA?, Option.map_eq_some_iff] at hfn
  obtain ⟨⟨ops, t, e⟩, hroot, hfn⟩ := hfn
  have same : ofLambdaSSA sigs r a params results = rootFn params results ops t e := by
    rw [ofLambdaSSA, ofLambdaSSA?, hroot]
    rfl
  rw [same]
  exact eval_iff_outcome hsigs hfit hroot hfr henv

end Silmaril.Proofs.Machine.OfLambdaSSA
