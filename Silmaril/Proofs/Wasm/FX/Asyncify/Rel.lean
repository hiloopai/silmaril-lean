module

public import Silmaril.Wasm.FX.Asyncify.Defs
public import Silmaril.Wasm.Models.FXAsync.Thms
public import Silmaril.Wasm.FX.Asyncify.RelSim.Thms

/-!
# Behaviours under a relational stuttering simulation

`SimRel s t R` (the family's hypothesis, `Silmaril.Wasm.FX.Asyncify.Defs`) and `RelSim.RSim R s t`
(`Silmaril.Wasm.FX.Asyncify.RelSim`, used by the shadow and selective strategies) are the same
stuttering relational simulation (`simRel_iff_rsim`, through `resRel_iff_rres`). There is one
proof that it preserves behaviours, `RelSim.beh_eq_of_rsim` (exported by the `RelSim` header);
`beh_eq_of_simRel` is that theorem for `SimRel`. A functional translation is the relation
`y = g x` (`simRel_of_simStep`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify
open Silmaril.Proofs.Wasm.Models.FXAsync (SimStep)

variable {C D V : Type}

/-- A matched `next` lands in a related `next`. -/
theorem resRel_next {R : C → D → Prop} {x' : C} {r : Res D V} (h : ResRel R (.next x') r) :
    ∃ y', r = .next y' ∧ R x' y' := by
  cases r with
  | next y' => exact ⟨y', rfl, h⟩
  | stop o => exact h.elim

/-- A matched `stop` is the same `stop`. -/
theorem resRel_stop {R : C → D → Prop} {o : Outcome V} {r : Res D V} (h : ResRel R (.stop o) r) :
    r = .stop o := by
  cases r with
  | next y' => exact h.elim
  | stop o' => exact congrArg Res.stop h.symm

/-- Related results are related step results of `RelSim`. -/
theorem resRel_iff_rres {R : C → D → Prop} {a : Res C V} {b : Res D V} :
    ResRel R a b ↔ RelSim.RRes R a b := by
  constructor
  · intro h
    cases a with
    | next x =>
      obtain ⟨y, rfl, hR⟩ := resRel_next h
      exact .next hR
    | stop o =>
      have hb : b = .stop o := resRel_stop h
      rw [hb]
      exact .stop o
  · intro h
    cases h with
    | next hR => exact hR
    | stop o => exact rfl

/-- **`SimRel` is `RelSim.RSim`**: the two names state the same stuttering simulation. -/
theorem simRel_iff_rsim {s : C → Res C V} {t : D → Res D V} {R : C → D → Prop} :
    SimRel s t R ↔ RelSim.RSim R s t :=
  ⟨fun h x y hxy => (h x y hxy).imp fun _ ⟨hn, hr⟩ => ⟨hn, resRel_iff_rres.mp hr⟩,
    fun h x y hxy => (h x y hxy).imp fun _ ⟨hn, hr⟩ => ⟨hn, resRel_iff_rres.mpr hr⟩⟩

/-- **Equal behaviours under a relational stuttering simulation of deterministic machines.** -/
theorem beh_eq_of_simRel {s : C → Res C V} {t : D → Res D V} {R : C → D → Prop}
    (hsim : SimRel s t R) {x : C} {y : D} (hxy : R x y) : beh s x = beh t y :=
  RelSim.beh_eq_of_rsim (simRel_iff_rsim.mp hsim) hxy

/-- A functional stuttering simulation is a relational one, for the graph of the translation. -/
theorem simRel_of_simStep {s : C → Res C V} {t : D → Res D V} {g : C → D}
    (h : SimStep s t g) : SimRel s t (fun x y => y = g x) := by
  rintro x y rfl
  obtain ⟨n, hn, hrun⟩ := h x
  refine ⟨n, hn, ?_⟩
  rw [hrun]
  cases s x with
  | next x' => exact rfl
  | stop o => exact rfl

end Silmaril.Proofs.Wasm.FX.Asyncify
