module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.NxQuant.Typ

/-!
# Round 7, REH route 2: the induction on `hasTyp`'s fuel (unrefined)
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.NxSites
open Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)

/-- The entries of `sigX` agree with the records `fs` of `x` at the atoms of `fs`. -/
def FF (x : String) (fs : List TypField) : Prop :=
  (∀ p ∈ sigX.fields, p.1 = x → ∀ t, fieldOf p.2.1 fs = some t → toAT t = p.2.2) ∧
    nodupS (fieldAtoms fs) = true

/-- **Values of a checked type conform, at fuel `n`.** -/
structure VtTyp (env : Env) (n : Nat) : Prop where
  typ : ∀ ρ t v, TypsNx sigX.good ρ → hasTyp n env ρ t v = .ok true →
    vtB sigX (toAT t) v = true
  tup : ∀ ρ bs vs, TypsNx sigX.good ρ → hasTypTup n env ρ bs vs = .ok true →
    vtT sigX (toATBinds bs) vs = true
  list : ∀ ρ t vs, TypsNx sigX.good ρ → hasTypList n env ρ t vs = .ok true →
    ∀ w ∈ vs, vtB sigX (toAT t) w = true
  defT : ∀ x ρ dt v (A : List AT), XF x dt → ρ.typs = [] → hasTypDef n env ρ dt v = .ok true →
    vtB sigX (.name x A) v = true
  fields : ∀ x ρ fs gs, FF x fs → ρ.typs = [] → hasTypFields n env ρ fs gs = .ok true →
    vtF sigX x gs = true
  case : ∀ x ρ cs op w, (∀ p ∈ sigX.cases, p.1 = x → p.2.1 = op → ∀ t, caseOf op cs = some t →
      toAT t = p.2.2) → ρ.typs = [] → hasTypCase n env ρ cs op w = .ok true →
    vtB sigX (caseAT sigX x op) w = true
  insts : ∀ x insts ws v (A : List AT), IF x insts → hasTypInsts n env insts ws v = .ok true →
    vtB sigX (.name x A) v = true

theorem vtTyp_zero (env : Env) : VtTyp env 0 where
  typ := by intros; simp_all [hasTyp]
  tup := by intros; simp_all [hasTypTup]
  list := by intros; simp_all [hasTypList]
  defT := by intros; simp_all [hasTypDef]
  fields := by intros; simp_all [hasTypFields]
  case := by intros; simp_all [hasTypCase]
  insts := by intros; simp_all [hasTypInsts]

theorem typsNx_nil {ρ : VarEnv} (h : ρ.typs = []) : TypsNx sigX.good ρ := by
  intro p hp; rw [h] at hp; cases hp

end Silmaril.Wasm.SpecTec.Sim.Round7.NxQuant
