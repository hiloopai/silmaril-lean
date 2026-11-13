module

public import Silmaril.Wasm.Category.Linking.Defs
public import Silmaril.Wasm.Game.Linking.Thms
public import Silmaril.Wasm.Game.Adequacy.Thms
public import Silmaril.Wasm.Game.DivAdequacy.Thms

@[expose] public section

/-!
# Static linking is composition, as a functor

* `sem_map_path`: an instance denotes its strategy `I.σ P`.
* **`sem_link` (M3 as functoriality)**: for every static link `S` in the scalar fragment and
  every profile `P`, the semantic functor identifies the formal composite of provider and
  consumer with the linked module:
  `(sem P).map ((provArrow S).path ≫ (consArrow S).path) = (sem P).map (linkArrow S).path`.
  This is `Silmaril.Wasm.Game.Linking.Setup.link_is_composition_profile`, proved from the forward
  simulations and the backward simulations of the linker relation, for every profile.
* `linked_behaviours`: the Core 3.0 closed-world behaviours of an export call of the linked
  module are the observations of the image of the composite path under `sem P`, together with
  may-divergence.
* `dsem_forget`: forgetting divergence maps the divergence-observing functor to `sem P`.

Not shown: `dsem P` identifies the provider–consumer path with the linked module (a
divergence-observing M3); see `docs/projects/games.md`, Open points.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable (P : Profile)

/-- An instance denotes its strategy. -/
theorem sem_map_path {X Y : WObj} (a : WArrow X Y) :
    (sem P).map a.path = (WArrow.inst a).σ P :=
  Paths.lift_toPath (semPre P) a

/-- An instance denotes its divergence-observing strategy. -/
theorem dsem_map_path {X Y : WObj} (a : WArrow X Y) :
    (dsem P).map a.path = (WArrow.inst a).dstrategy P (WArrow.inst a).store :=
  Paths.lift_toPath (dsemPre P) a

/-- **Forgetting divergence maps `dsem P` to `sem P`.** -/
theorem dsem_forget : dsem P ⋙ forgetDiv = sem P := by
  refine Paths.lift_unique (semPre P) _ (Prefunctor.ext (fun _ => rfl) fun X Y a => ?_)
  have h₁ : forgetDiv.map ((dsem P).map (WArrow.path a)) =
      ((WArrow.inst a).dstrategy P (WArrow.inst a).store).forget :=
    congrArg DStrategy.forget (dsem_map_path P a)
  have h₂ : ((WArrow.inst a).dstrategy P (WArrow.inst a).store).forget = (WArrow.inst a).σ P :=
    ScalarInstance.forget_dstrategy P _
  exact h₁.trans h₂

namespace Linking.Setup

variable (S : Linking.Setup)

/-- **Static linking is composition, as functoriality** (M3, every profile): the semantic
functor maps the formal composite of provider and consumer to the strategy of the linked
module. -/
theorem sem_link (hS : S.Scalar) :
    (sem P).map ((provArrow S).path ≫ (consArrow S).path) =
      (sem P).map (linkArrow S).path := by
  rw [Functor.map_comp, sem_map_path, sem_map_path, sem_map_path]
  exact (S.link_is_composition_profile hS P).symm

/-- An environment of a closed instance throws nothing. -/
theorem throwsBelow_nil (K : Env (ifaceSig [])) (n : Nat) : ThrowsBelow K n :=
  fun e => (ifaceSig_nil_op_isEmpty.false e).elim

/-- **The closed-world behaviours of the linked module** are the observations of the composite
of provider and consumer under the semantic functor, with may-divergence. -/
theorem linked_behaviours (hS : S.Scalar) (K : Env (ifaceSig [])) (f : (ifaceSig S.exportTypes).Op) :
    behaviours P (hostOf [] K) S.sl (S.linkedI.addr f.1) f.2.1 =
      compositeObs (K.strategy.comp ((sem P).map ((provArrow S).path ≫ (consArrow S).path))) f ∪
        {b | b = .diverges ∧ Diverges P (hostOf [] K) (invoke S.sl (S.linkedI.addr f.1) f.2.1)} := by
  have hA := ScalarInstance.adequacy_profile (I := S.linkedI) (P := P) hS.linked K
    (throwsBelow_nil K _) f
  have hσ : (sem P).map ((provArrow S).path ≫ (consArrow S).path) = S.linkedI.σ P := by
    rw [sem_link P S hS, sem_map_path]
    rfl
  have e : S.linkedI.closedWith P S.linkedI.store K =
      K.strategy.comp ((sem P).map ((provArrow S).path ≫ (consArrow S).path)) :=
    (congrArg K.strategy.comp hσ).symm
  exact hA.trans (congrArg (fun σ => compositeObs σ f ∪
    {b | b = .diverges ∧ Diverges P (hostOf [] K) (invoke S.sl (S.linkedI.addr f.1) f.2.1)}) e)

end Linking.Setup

end Silmaril.Wasm.Category
