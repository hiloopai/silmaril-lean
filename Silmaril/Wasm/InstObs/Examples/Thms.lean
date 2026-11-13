module

public import Silmaril.Wasm.Institution.Api.Defs

/-!
# The observational builders of the facade, in use

Checks for the pass-2 changes to `Silmaril.Wasm.InstObs.Defs`:

1. **Reducible output.** `Institution.ofObs outs` unfolds under `rw` to the observational
   semantics, so validity of a concrete refinement is proved by `rw` and `simp`.
2. **Noncomputable output.** `Comorphism.ofObs` and `ExpTranslation.comorphism` are
   `noncomputable`, so no code is generated for comorphisms (they are proof objects): a
   computable `def` naming one is rejected with Lean's ordinary hint (a compiled `#guard_msgs`
   test), and a `noncomputable def` is accepted.
3. **The canonical `⊨`.** `β ⊨ s` (class `Silmaril.Inst.Satisfies`) reads observational
   satisfaction (instance `ObsSemantics.instSatisfies`), and agrees with
   `β ⊨[Institution.ofObs S] s`.
-/

@[expose] public section

namespace Silmaril.Wasm.InstObs.Examples

open CategoryTheory Silmaril.Inst
open Silmaril.Wasm.Institution (ObsSemantics Sig)
open Silmaril.Wasm.Institution.ObsSemantics (Translation ExpTranslation)

/-- Outputs over `ℕ` at a single interface (the guide's `natOut`, declared with `abbrev`). -/
abbrev outs : ObsSemantics (Discrete Unit) where
  Sem _ := Set ℕ
  restrict _ s := s
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl
  Prog := List ℕ
  den _ p := {n | n ∈ p}
  Op := Unit
  op _ _ s := s ∪ {0}
  Le _ s t := s ⊆ t

/-- The only interface. -/
abbrev pt : Discrete Unit := ⟨()⟩

/-! ## 1. Reducible output -/

/-- The institution, at the facade shape `Institution₁`. -/
example : Institution₁ := Institution.ofObs outs

/-- Validity in the facade institution of a concrete refinement, by rewriting. -/
theorem outs_one_le : (Institution.ofObs outs).Valid (outs.leSen pt [1] [1, 2]) := by
  rw [valid_ofObs_iff, ObsSemantics.valid_leSen_iff]
  intro n (h : n ∈ [1])
  show n ∈ [1, 2]
  simp_all

/-! ## 2. Noncomputable output -/

/-- The identity translation as a facade comorphism (`noncomputable def`). -/
noncomputable def idCo : Comorphism (Institution.ofObs outs) (Institution.ofObs outs) :=
  (ExpTranslation.id outs).comorphism

-- A computable `def` is rejected with the ordinary hint, not a code-generator crash.
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'ExpTranslation.comorphism', which is 'noncomputable'
-/
#guard_msgs in
def idCoComputable : Comorphism (Institution.ofObs outs) (Institution.ofObs outs) :=
  (ExpTranslation.id outs).comorphism

theorem idCo_modelExpansive : idCo.ModelExpansive := (ExpTranslation.id outs).modelExpansive

/-- Borrowing validity along it needs no surjectivity hypothesis. -/
example {K : Sig (Discrete Unit)} (s : ObsSemantics.Sen outs K) :
    (Institution.ofObs outs).Valid s ↔ (Institution.ofObs outs).Valid (idCo.sen K s) :=
  idCo.valid_iff idCo_modelExpansive s

/-! ## 3. The canonical `⊨` -/

/-- Observational satisfaction under the canonical notation. -/
example {K : Sig (Discrete Unit)} (β : outs.Model K) (s : ObsSemantics.Sen outs K) :
    β ⊨ s ↔ outs.Sat K β s := by
  simp

/-- The canonical `⊨` and the institution-indexed `⊨[A]` agree. -/
example {K : Sig (Discrete Unit)} (β : outs.Model K) (s : ObsSemantics.Sen outs K) :
    β ⊨ s ↔ β ⊨[Institution.ofObs outs] s :=
  ObsSemantics.sat_iff_ofObs outs β s

/-- The satisfaction condition of a facade comorphism, by `simp`. (The model is typed at the
translated signature `idCo.sig K`: `idCo` is a `def`, so `idCo.sig K` is not `K` reducibly.) -/
example {K : Sig (Discrete Unit)} (β : (Institution.ofObs outs).Mod (idCo.sig K))
    (s : ObsSemantics.Sen outs K) :
    β ⊨[Institution.ofObs outs] idCo.sen K s ↔ idCo.mod K β ⊨[Institution.ofObs outs] s := by
  simp

end Silmaril.Wasm.InstObs.Examples
