module

public import Silmaril.Wasm.Binaryen.Equiv
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Submonoid.Defs

@[expose] public section

/-! # Pass contracts: refinement is a preorder, sound passes form a monoid

`ExportRefines R P host` (`Binaryen/Equiv.lean`) is the correctness criterion of a
pass: the output implements the input. This file packages the facts a pass pipeline
needs, for any behaviour relation `R` that is a preorder (`Eq`, `TrapsUB`, ...):

* `ExportRefines` is reflexive and transitive (`Contract.refines_refl`,
  `Contract.refines_trans`), and `ExportEquiv` is an equivalence relation when `R` is
  one (and symmetric up to flipping `R` in general).
* A **sound pass** (`SoundPass`) maps every valid module to a valid module that
  refines it. Sound passes contain the identity and are closed under composition, so
  they form a submonoid of `Function.End BModule` (`soundPasses`). Running a pipeline
  of sound passes is sound (`SoundPass.pipeline`).

Transitivity under `TrapsUB` rests on `SessionRel.trans`, whose `ub` case is where a
middle program traps: the licence to do anything after a trap is granted by the
specification's session and survives composition (see `SessionRel`).

The monoid is the single-IR shadow of a category: objects are IRs with a lowering to
Core, morphisms are translations that refine along the lowerings. Here there is one
object (layer-D `BModule`), so the hom-set is a monoid.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

variable {H : Type}

namespace Contract

variable {R : Behaviour Val → Behaviour Val → Prop} {P : Profile} {host : HostSemantics H}

/-- A behaviour relation fit for contracts: reflexive and transitive. -/
structure Rel (R : Behaviour Val → Behaviour Val → Prop) : Prop where
  refl : ∀ b, R b b
  trans : ∀ x y z, R x y → R y z → R x z

theorem Rel.eq : Rel (· = · : Behaviour Val → Behaviour Val → Prop) :=
  ⟨fun _ => rfl, fun _ _ _ h h' => h.trans h'⟩

theorem Rel.trapsUB : Rel (TrapsUB (V := Val)) :=
  ⟨TrapsUB.refl, fun _ _ _ h h' => TrapsUB.trans h h'⟩

/-- The flipped relation of a preorder is a preorder. -/
theorem Rel.flip (hR : Rel R) : Rel (fun b b' => R b' b) :=
  ⟨hR.refl, fun _ _ _ h h' => hR.trans _ _ _ h' h⟩

/-! ## `ExportRefines` is a preorder -/

theorem refines_refl (hR : Rel R) (m : Module) : ExportRefines R P host m m :=
  ExportRefines.refl hR.refl m

theorem refines_trans (hR : Rel R) {m m' m'' : Module}
    (h : ExportRefines R P host m m') (h' : ExportRefines R P host m' m'') :
    ExportRefines R P host m m'' :=
  h.trans hR.trans h'

/-- `ExportRefines R` under a preorder `R`, as a reflexivity–transitivity pair. -/
theorem refines_isPreorder (hR : Rel R) :
    (∀ m, ExportRefines R P host m m) ∧
    (∀ m m' m'', ExportRefines R P host m m' → ExportRefines R P host m' m'' →
      ExportRefines R P host m m'') :=
  ⟨refines_refl hR, fun _ _ _ => refines_trans hR⟩

/-- Trap-licensed refinement composes: the `trapsNeverHappen` contract is a preorder. -/
theorem trapsUB_trans {m m' m'' : Module}
    (h : ExportRefines TrapsUB P host m m') (h' : ExportRefines TrapsUB P host m' m'') :
    ExportRefines TrapsUB P host m m'' :=
  refines_trans Rel.trapsUB h h'

/-! ## `ExportEquiv` -/

theorem equiv_refl (hR : Rel R) (m : Module) : ExportEquiv R P host m m :=
  ⟨refines_refl hR m, refines_refl hR.flip m⟩

/-- Symmetry, flipping the behaviour relation. -/
theorem equiv_symm {m m' : Module} (h : ExportEquiv R P host m m') :
    ExportEquiv (fun b b' => R b' b) P host m' m :=
  ⟨h.2, h.1⟩

/-- Symmetry for a symmetric behaviour relation (e.g. `Eq`). -/
theorem equiv_symm_of_symm (hs : ∀ x y, R x y → R y x) {m m' : Module}
    (h : ExportEquiv R P host m m') : ExportEquiv R P host m' m :=
  ⟨h.2.mono fun x y h => hs y x h, h.1.mono fun x y h => hs x y h⟩

theorem equiv_trans (hR : Rel R) {m m' m'' : Module}
    (h : ExportEquiv R P host m m') (h' : ExportEquiv R P host m' m'') :
    ExportEquiv R P host m m'' :=
  ⟨refines_trans hR h.1 h'.1, refines_trans hR.flip h'.2 h.2⟩

/-- `ExportEquiv Eq` is an equivalence relation on modules. -/
theorem equiv_eq_equivalence :
    Equivalence (ExportEquiv (· = · : Behaviour Val → Behaviour Val → Prop) P host) :=
  ⟨equiv_refl Rel.eq, equiv_symm_of_symm (fun _ _ h => h.symm),
    equiv_trans Rel.eq⟩

theorem refines_of_equiv {m m' : Module} (h : ExportEquiv R P host m m') :
    ExportRefines R P host m m' :=
  h.1

end Contract

/-! ## Sound passes -/

/-- **A sound pass** under the contract `R`: it maps every valid module to a valid
module whose lowering implements the input's. -/
def SoundPass (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (f : BModule → BModule) : Prop :=
  ∀ m : BModule, m.Ok → (f m).Ok ∧ ExportRefines R P host (f m).lower m.lower

namespace SoundPass

variable {R : Behaviour Val → Behaviour Val → Prop} {P : Profile} {host : HostSemantics H}

theorem id (hR : Contract.Rel R) : SoundPass R P host _root_.id :=
  fun _ hm => ⟨hm, Contract.refines_refl hR _⟩

/-- Running `g` and then `f` is sound. -/
theorem comp (hR : Contract.Rel R) {f g : BModule → BModule}
    (hf : SoundPass R P host f) (hg : SoundPass R P host g) : SoundPass R P host (f ∘ g) :=
  fun m hm =>
    let ⟨hgm, hg'⟩ := hg m hm
    let ⟨hfm, hf'⟩ := hf (g m) hgm
    ⟨hfm, Contract.refines_trans hR hf' hg'⟩

theorem mono {R' : Behaviour Val → Behaviour Val → Prop} (hRR : ∀ x y, R x y → R' x y)
    {f : BModule → BModule} (hf : SoundPass R P host f) : SoundPass R' P host f :=
  fun m hm => let ⟨h₁, h₂⟩ := hf m hm; ⟨h₁, h₂.mono hRR⟩

/-- An `Eq`-sound pass is `TrapsUB`-sound. -/
theorem trapsUB_of_eq {f : BModule → BModule} (hf : SoundPass (· = ·) P host f) :
    SoundPass TrapsUB P host f :=
  hf.mono fun _ _ h => TrapsUB.of_eq h

/-- A pass whose output has the same lowering as its input is sound (`Pass/Free.lean`). -/
theorem of_lower_eq (hR : Contract.Rel R) {f : BModule → BModule}
    (h : ∀ m, (f m).lower = m.lower) : SoundPass R P host f :=
  fun m hm => by
    refine ⟨?_, ?_⟩
    · obtain ⟨t, ht⟩ := hm; exact ⟨t, (h m).symm ▸ ht⟩
    · rw [h m]; exact Contract.refines_refl hR _

/-- **Pipelines.** Composing a list of sound passes (the head runs last) is sound. -/
theorem pipeline (hR : Contract.Rel R) :
    ∀ fs : List (BModule → BModule), (∀ f ∈ fs, SoundPass R P host f) →
      SoundPass R P host (fs.foldr (· ∘ ·) _root_.id)
  | [], _ => SoundPass.id hR
  | f :: fs, h =>
    comp (f := f) (g := fs.foldr (· ∘ ·) _root_.id) hR (h f List.mem_cons_self)
      (pipeline hR fs fun g hg => h g (List.mem_cons_of_mem _ hg))

end SoundPass

/-- **Sound passes form a monoid**: the submonoid of `Function.End BModule` (whose
multiplication is composition, `(f * g) m = f (g m)`) of passes sound under a
preorder contract `R`. -/
def soundPasses (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (hR : Contract.Rel R) : Submonoid (Function.End BModule) where
  carrier := {f | SoundPass R P host f}
  one_mem' := SoundPass.id hR
  mul_mem' hf hg := SoundPass.comp hR hf hg

theorem mem_soundPasses {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {host : HostSemantics H} {hR : Contract.Rel R} {f : Function.End BModule} :
    f ∈ soundPasses R P host hR ↔ SoundPass R P host f :=
  Iff.rfl

/-- `Eq`-sound passes sit inside `TrapsUB`-sound ones. -/
theorem soundPasses_eq_le_trapsUB {P : Profile} {host : HostSemantics H} :
    soundPasses (· = ·) P host Contract.Rel.eq ≤
      soundPasses TrapsUB P host Contract.Rel.trapsUB :=
  fun _ hf => SoundPass.trapsUB_of_eq hf

end Silmaril.Wasm.Binaryen
