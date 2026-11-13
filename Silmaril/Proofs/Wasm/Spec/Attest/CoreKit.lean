module

public import Silmaril.Proofs.Wasm.Spec.Attest.Runs
public import Silmaril.Proofs.Wasm.Spec.Attest.Safe
public import Silmaril.Proofs.Wasm.Spec.Attest.Encode

/-!
# The Core 3.0 kit satisfies the kit laws

* `mayCall_iff_not_neverCall`: a Core program may call `attest` (a play of its strategy asks the
  import) iff it violates the `neverCall` sentence of `inst neverCall (wasmSem P)`;
* `leaf_trapProp`: Core programs propagate traps;
* `ff_neverCall`: the `false` module never attests, by the verifier (`check_sound`);
* **`coreKit_ok`**: `(coreKit P).Ok trapAns`, every profile.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm.Verify Silmaril.Wasm.Spec.Attest
  Silmaril.Wasm.Spec.Attest.Core Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- The only import of a Core leaf. -/
def attImp {exps : List FnType} : (⟨[unitFn], exps⟩ : WIface).Imp := ⟨0, Nat.one_pos⟩

/-- **May attest is the negation of the `neverCall attest` sentence**, for every Core program
whose only import is `attest`, at every profile. -/
theorem mayCall_iff_not_neverCall (P : Profile) (L : CoreLeaf) :
    MayCall (L.toAMod P).σ ↔
      ¬ Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) L.prog attImp := by
  rw [models_iff]
  constructor
  · rintro ⟨p, hp, m, hm⟩ hall
    have hev : (Event.icall attImp m.2.1 : WEvent ⟨[unitFn], L.exports⟩) ∈ p.map moveEvent := by
      have hmap : moveEvent (X := ⟨[unitFn], L.exports⟩) (.inl (.ask m)) ∈ p.map moveEvent :=
        List.mem_map_of_mem hm
      have hi : m.1 = attImp (exps := L.exports) := Fin.ext (Nat.lt_one_iff.1 m.1.2)
      simpa [moveEvent, evOf, hi] using hmap
    exact hall _ ⟨p, hp, rfl⟩ _ hev
  · intro h
    by_contra hno
    refine h fun t ⟨p, hp, ht⟩ a hmem => ?_
    rw [← ht] at hmem
    obtain ⟨o, ho, he⟩ := List.mem_map.1 hmem
    rcases o with (m | ⟨m, n⟩) | o
    · exact hno ⟨p, hp, m, ho⟩
    · cases he
    · cases he

/-- **Core programs propagate traps** (every profile). -/
theorem leaf_trapProp (P : Profile) (L : CoreLeaf) :
    TrapProp (L.toAMod P).σ trapAns (L.toAMod P).stop :=
  strategy_trapProp L.prog.inst P L.prog.store

/-- The leaf of a module whose import is `attest` has the module's instance. -/
theorem leafOf_inst {m : Module} (h : (instOf m).imports = [unitFn]) :
    (leafOf m).prog.inst = instOf m := by
  show (⟨[unitFn], (instOf m).exports, (instOf m).addrs, (instOf m).store⟩ : ScalarInstance) =
    instOf m
  rw [← h]

/-- **The `false` module never attests**: the verifier proves `neverCall attest` (every
profile). -/
theorem ff_neverCall (P : Profile) :
    Models (neverCall FnType (List Val) (Behaviour Val)) (wasmSem P) (leafOf ffMod).prog attImp := by
  obtain ⟨mt, hI⟩ := isInstance_instOf ff_instance
  rw [← leafOf_inst ff_imports] at hI
  exact check_sound (i := attImp) hI ff_check P

/-- A trap answer read through a cast of answer types is a trap. -/
theorem cast_trap {a b : FnType} (e : a = b) :
    cast (congrArg Answer e) (Answer.trap : Answer a) = Answer.trap := by
  subst e
  rfl

/-- **The Core 3.0 kit satisfies the kit laws**, every profile. -/
theorem coreKit_ok (P : Profile) : (coreKit P).Ok trapAns where
  gate_tp := strategy_trapProp gateI P gateI.store
  stop₁ e := cast_trap (get_unitFn e.1 0)
  stop₂ e := cast_trap (get_unitFn e.1 1)
  disjoint _ _ h := (show (0 : Fin 2) ≠ 1 by decide) (congrArg Sigma.fst h)
  safe := gate_safe P
  live _ _ := gate_live P
  tt_may := by
    obtain ⟨f, e, h⟩ := tt_play P
    exact ⟨_, h, e, List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩
  ff_not := (mayCall_iff_not_neverCall P (leafOf ffMod)).not.2 (not_not.2 (ff_neverCall P))
  tt_tp := leaf_trapProp P (leafOf ttMod)
  ff_tp := leaf_trapProp P (leafOf ffMod)

end Silmaril.Proofs.Wasm.Spec.Attest
