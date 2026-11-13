module

public import Silmaril.Proofs.Wasm.Component.FXRefV.Inst
public import Silmaril.Wasm.Component.EngineRef.Thms

/-!
# The run facts of `fxEV P` for components with FX functions, and the machine half

The reference machine runs an export call of `c : SimpleFX` over `fxEV P` in the store
`cs = csOf c f' cs₁` at host type `H = CanonHost (fxEV P)`; the engine's specification
`exportSpecE (fxEV P) c.emb` runs it in the `Nat` instance `J`, whose store is `cs` renamed
(`instOf_fxV`). Since `cs` is host-free (`hostFree_cs`) and engine steps keep the functions:

* `reach_inv`: every thread reached from an export activation is in a host-free store and is not
  parked, so it is never at a callout (`no_callout_fxV`), whatever FX code it runs (`suspend`,
  `resume`, `switch`, `cont.bind`, `resume_throw` included);
* `values_fxV`, `trap_fxV`, `diverges_fxV`: returned, trapping and diverging runs are, renamed,
  runs of `J` (`steps_mapC`, `statusV_mapC_returned`, `diverges_mapC`);
* `runFacts_fxV`: **the run facts** (`EngineRef.RunFacts`) with the outcomes of `J`, given
  `SimpleFX.Typed` (the typing of returned values);
* `refToSpecFX`: **`RefToSpecFX P`**, through `EngineRef.refToSpecE_of_facts`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXRefV

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.EngineRef
open Silmaril.Wasm.Component.FXRefV
open Silmaril.Proofs.Wasm.Component.Reference (inst_once)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component.Runtime (CanonHost)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps Diverges)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-! ## Reached threads -/

/-- A thread that is not parked. -/
def NotParked (t : ThreadV H) : Prop := ∀ K f E Ec hh args, t ≠ .parked K f E Ec hh args

/-- **Every reached thread is in a host-free store with the same functions, and not parked.** -/
theorem reach_inv {s₀ : Store (FXCode H)} (hs : HostFree s₀) {t₀ : ThreadV H}
    (hp : NotParked t₀) {y : Store (FXCode H) × ThreadV H}
    (h : Relation.ReflTransGen (InternalV P) (s₀, t₀) y) :
    y.1.funcs = s₀.funcs ∧ HostFree y.1 ∧ NotParked y.2 := by
  induction h with
  | refl => exact ⟨rfl, hs, hp⟩
  | @tail b c _ hstep ih =>
    obtain ⟨hf, hb, hpb⟩ := ih
    have hf' := internalV_funcs (s := b.1) (t := b.2) (s' := c.1) (t' := c.2) hstep
    exact ⟨hf'.trans hf, hostFree_of_funcs hb hf',
      internalV_not_parked (s := b.1) (t := b.2) (s' := c.1) (t' := c.2) hb hstep hpb⟩

theorem notParked_invoke (a : Nat) (xs : List Flat) :
    NotParked ((fxEV P).invoke (H := H) a xs) := by
  intro K f E Ec hh args e
  cases e

/-! ## The run facts -/

/-- An inhabitant of the machine's host type. -/
def h₀ : CanonHost (fxEV P) := .embedder "" ⟨[], []⟩

variable {cs : Store (FXCode H)} {J : EInstance (fxEV P)} {a : Nat} {k : Nat} {xs : List Flat}

/-- No run of the activation reaches a callout. -/
theorem no_callout_fxV (hs : HostFree cs) {s' : Store (FXCode H)} {t' : ThreadV H} (h : H)
    (args : List Flat) (run : Steps (fxEV P) (cs, (fxEV P).invoke a xs) (s', t')) :
    (fxEV P).status s' t' ≠ .callout h args := by
  obtain ⟨-, hs', hp'⟩ := reach_inv hs (notParked_invoke a xs) run
  exact no_callout_of_hostFree hs' hp' h args

/-- A returned run of the activation is, renamed, a returned run of `J`. -/
theorem returned_fxV (g : H → Nat) (g' : Nat → H) (hs : HostFree cs)
    (hJs : J.store = SM g cs) (hJa : J.addrs[k]? = some a) {s' : Store (FXCode H)}
    {t' : ThreadV H} {R : Silmaril.Wasm.Component.Engine.CallResult}
    (run : Steps (fxEV P) (cs, (fxEV P).invoke a xs) (s', t'))
    (hst : (fxEV P).status s' t' = .returned R) :
    ∃ (a' : Nat) (s'' : Store (FXCode Nat)) (t'' : ThreadV Nat), J.addrs[k]? = some a' ∧
      Steps (fxEV P) (J.store, (fxEV P).invoke a' xs) (s'', t'') ∧
      (fxEV P).status s'' t'' = .returned R := by
  obtain ⟨-, hs', -⟩ := reach_inv hs (notParked_invoke a xs) run
  refine ⟨a, SM g s', thrC g t', hJa, ?_, statusV_mapC_returned hs' g g' hst⟩
  rw [hJs]
  exact steps_mapC g run

/-- **The run facts** of an export activation of a component with FX functions. -/
theorem runFacts_fxV (g : H → Nat) (g' : Nat → H) (hs : HostFree cs)
    (hJs : J.store = SM g cs) (hJa : J.addrs[k]? = some a) {rts : List NumType}
    (hT : ∀ ys, some ys ∈ engineOut (fxEV P) J k xs → ys.map (·.type) = rts) :
    RunFacts (fxEV P) cs a xs rts (engineOut (fxEV P) J k xs) (engineDiverges (fxEV P) J k xs) where
  no_callout h args run := no_callout_fxV hs h args run
  values ys run hst := by
    obtain ⟨a', s'', t'', ha', run', hst'⟩ := returned_fxV g g' hs hJs hJa run hst
    have hmem : some ys ∈ engineOut (fxEV P) J k xs :=
      ⟨a', s'', t'', ha', run', Or.inl ⟨ys, hst', rfl⟩⟩
    exact ⟨hmem, hT ys hmem⟩
  trap run hst := by
    obtain ⟨a', s'', t'', ha', run', hst'⟩ := returned_fxV g g' hs hJs hJa run hst
    exact ⟨a', s'', t'', ha', run', Or.inr ⟨hst', rfl⟩⟩
  diverges hd := by
    refine ⟨a, hJa, ?_⟩
    show Silmaril.InfiniteTrace (InternalV P) _
    rw [hJs]
    exact diverges_mapC (x := (cs, (fxEV P).invoke a xs)) g hd

/-! ## The machine half -/

/-- The run outcomes of a typed call are in the engine's specification. -/
theorem specOut_sub_fxV {c : SimpleFX}
    (hJ : instOf (fxEV P) (c.emb c.mod) [] c.mod.exports = some J) (x : SimpleExport)
    (vs : List Silmaril.Wasm.Component.Val) (hvs : ValTy.checkList x.ty.params vs = true) :
    specOut x (engineOut (fxEV P) J x.core (lowerArgs x.ty.params vs))
        (engineDiverges (fxEV P) J x.core (lowerArgs x.ty.params vs)) ⊆
      exportSpecE (fxEV P) c.emb c.toSimple x vs := by
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd hvs h)]
  intro b hb
  unfold exportSpecE
  rw [hl]
  rcases hb with ⟨r, hr, rfl⟩ | ⟨rfl, hd⟩
  · exact Or.inl ⟨J, hJ, r, hr, rfl⟩
  · exact Or.inr ⟨rfl, J, hJ, hd⟩

/-- **The reference-machine half for components whose modules carry FX functions.** -/
theorem refToSpecFX (P : Profile) : RefToSpecFX P := by
  intro prof c hc hf hi ha ht x hx vs hvs
  obtain ⟨I, mt, cs₁, f', -, hv, hmt, ho, -, haddr⟩ :=
    inst_once (H := FXCode (CanonHost (fxEV P))) (fun _ => (0 : Nat)) hi.core
  obtain ⟨J, hJ, hJs, hJa⟩ := instOf_fxV (P := P) hi (fun _ => (0 : Nat)) hv hmt ho haddr
  obtain ⟨nm, hn⟩ := hc.core x hx
  have hRF := runFacts_fxV (P := P) (fun _ => (0 : Nat)) (fun _ => h₀) (hostFree_cs ho) hJs
    (hJa x.core _ hn) (xs := lowerArgs x.ty.params vs)
    (rts := ValTy.flatList x.ty.results) (ht J hJ x hx vs hvs)
  exact (refToSpecE_of_facts prof c.toSimple hc hf ha (instFacts_fxV hc hi hv hmt ho haddr)
    x hx vs hvs hRF).trans (specOut_sub_fxV hJ x vs hvs)

end Silmaril.Proofs.Wasm.Component.FXRefV
