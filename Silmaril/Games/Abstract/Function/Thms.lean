module

public import Silmaril.Games.Abstract.Function.Defs
import Silmaril.Proofs.Games.Abstract.Function.Basic

/-!
# Abstract functions: theorems

**Observations.** Composing an observation with any map gives a coarser
equivalence (`ObsEquiv.comp`): tagged ⇒ trap ≈ divergence, tagged ⇒
state-forgotten, and so on. The identity observation is equality
(`obsEquiv_id_iff`).

**Congruence.** Trap ≈ divergence is a congruence for sequencing
(`seq_obsCollapse`). Forgetting the final state is *not*: two functions that
set the state to different values are equivalent when the state is
forgotten, but followed by a function that reads the state they are not
(`exists_forgetState_not_congr`). An observation can serve as a module-level
equivalence only if it keeps what later code can depend on.

**Determinism.** Under a fixed host, a deterministic function has at most one
behaviour at each state and argument (`Det.under_subsingleton`). Determinism
is relative to inputs: without a host, different import answers may give
different behaviours.

**Lattice.** Abstract functions are ordered pointwise by inclusion. This is
Mathlib's complete lattice on functions into sets, lawful with no closure
condition, because `AFun` imposes none. Properties need not be closed under
its joins:

* state preservation is closed under sequencing and arbitrary joins
  (`StatePreserving.seq`, `statePreserving_sSup`);
* determinism is not closed under joins (`exists_det_sup_not_det`). The
  deterministic functions are not a sublattice, and a "join" of
  deterministic functions taken pointwise is not deterministic.

**May and must.** `MustTrap` excludes `MayDiv`, and `MustReturn` excludes
`MayAbort`. Must-properties quantify over every environment answer unless
restricted with `under`.
-/

public section

namespace Silmaril.Games.Abstract.AFun

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-- A coarser observation gives a coarser equivalence. -/
theorem ObsEquiv.comp {O O' : Type u} {κ : CallBeh E S B → O} (g : O → O')
    {f f' : AFun E S A B} (h : ObsEquiv κ f f') : ObsEquiv (g ∘ κ) f f' :=
  Silmaril.Proofs.Games.Abstract.Function.obsEquiv_comp g h

/-- The identity observation is equality. -/
theorem obsEquiv_id_iff {f f' : AFun E S A B} : ObsEquiv obsId f f' ↔ f = f' := by
  simp only [ObsEquiv, obsId, Set.image_id]
  exact ⟨fun h => funext fun s => funext fun a => h s a, fun h _ _ => h ▸ rfl⟩

/-- Trap ≈ divergence is a congruence for sequencing. -/
theorem seq_obsCollapse {f f' : AFun E S A B} {g g' : AFun E S B C}
    (hf : ObsEquiv obsCollapse f f') (hg : ObsEquiv obsCollapse g g') :
    ObsEquiv obsCollapse (seq f g) (seq f' g') :=
  Silmaril.Proofs.Games.Abstract.Function.seq_collapse hf hg

/-- Forgetting the final state is not a congruence for sequencing. -/
theorem exists_forgetState_not_congr :
    ∃ (f f' : AFun Sig.empty Bool PUnit PUnit) (g : AFun Sig.empty Bool PUnit Bool),
      ObsEquiv obsForgetState f f' ∧ ¬ ObsEquiv obsForgetState (seq f g) (seq f' g) :=
  open Silmaril.Proofs.Games.Abstract.Function in
  ⟨setTo true, setTo false, readState, setTo_forget, forget_not_congr⟩

/-- Under a host, a deterministic function has at most one behaviour. -/
theorem Det.under_subsingleton {f : AFun E S A B} (hf : Det f) (h : Host E) (s : S) (a : A) :
    (under h f s a).Subsingleton :=
  Silmaril.Proofs.Games.Abstract.Function.det_under_subsingleton hf h s a

/-- Behaviours under a host are behaviours. -/
theorem under_le (h : Host E) (f : AFun E S A B) : under h f ≤ f := fun _ _ _ hx => hx.1

/-- State preservation is closed under sequencing. -/
theorem StatePreserving.seq {f : AFun E S A B} {g : AFun E S B C} (hf : StatePreserving f)
    (hg : StatePreserving g) : StatePreserving (AFun.seq f g) :=
  Silmaril.Proofs.Games.Abstract.Function.seq_statePreserving hf hg

/-- State preservation is closed under arbitrary joins. -/
theorem statePreserving_sSup {F : Set (AFun E S A B)} (hF : ∀ f ∈ F, StatePreserving f) :
    StatePreserving (sSup F) :=
  Silmaril.Proofs.Games.Abstract.Function.sSup_statePreserving hF

/-- Determinism is not closed under joins. -/
theorem exists_det_sup_not_det :
    ∃ f g : AFun Sig.empty PUnit PUnit Bool, Det f ∧ Det g ∧ ¬ Det (f ⊔ g) :=
  open Silmaril.Proofs.Games.Abstract.Function in
  ⟨const true, const false, const_det true, const_det false, sup_not_det⟩

/-- A function that must trap cannot diverge. -/
theorem MustTrap.not_mayDiv {f : AFun E S A B} {s : S} {a : A} (h : MustTrap f s a) :
    ¬ MayDiv f s a := fun ⟨_, hc⟩ => by simpa using h.2 _ hc

/-- A function that must return cannot trap or diverge. -/
theorem MustReturn.not_mayAbort {f : AFun E S A B} {s : S} {a : A} (h : MustReturn f s a) :
    ¬ MayAbort f s a := fun ⟨x, hx, ha⟩ => h.2 x hx ha

/-- Inputs that may trap are exactly those with a trap observation. -/
theorem mem_trapInputs {f : AFun E S A B} {i : S × A} : i ∈ trapInputs f ↔ MayTrap f i.1 i.2 :=
  Iff.rfl

end Silmaril.Games.Abstract.AFun
