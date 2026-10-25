module

public import Silmaril.Wasm.Binaryen.Pass.Free
public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.Binaryen.Contracts
public import Silmaril.Wasm.Binaryen.PassAPI.Category

@[expose] public section

/-! # Pass API: Binaryen contracts

The semantic domains of the Binaryen formalization (`Binaryen/Equiv.lean`), as
`Domain`s on Core 3.0 modules, and the two IRs over them:

* `exportDomain R P host hR`: `Rel a b := ExportRefines R P host b a` (`b` implements
  `a`), for any behaviour preorder `R` (`hR : Binaryen.Contract.Rel R`);
* `equivDomain P host`: `Rel a b := ExportEquiv Eq P host b a`;
* `coreIR`: Core modules, denotation `id`; `birIR`: Binaryen IR modules, denotation
  `BModule.lower` (the lowering is the defining semantics).

Reflexivity and transitivity come from `Binaryen/Contracts.lean`
(`Contract.refines_refl`/`refines_trans`/`equiv_refl`/`equiv_trans`, resting on the
proved `SessionRel.trans`); no domain takes a transitivity parameter. The two concrete
contracts on Binaryen modules are `equivContract P host` (`ExportEquiv Eq`) and
`trapsUBContract P host` (`ExportRefines TrapsUB`, Binaryen's `trapsNeverHappen`).

Morphisms: `lowerT : birIR ⟶ coreIR` and `liftT : coreIR ⟶ birIR`, with
`liftT ≫ lowerT = 𝟙` (`liftT_lowerT`, from `lower_lift`): Core Wasm is a retract of the
Binaryen IR in the category of IRs. The other composite `lowerT ≫ liftT` is the
**unfold** pass of `Pass/Free.lean` (`endEquiv_lowerT_liftT`).

Inclusions: `equiv ≤ refines Eq ≤ refines TrapsUB` (`equiv_le_refines`,
`refines_le_trapsUB`), so equivalence passes weaken to refinement passes as monoid homs.

**Relation to `soundPasses`** (`Binaryen/Contracts.lean`). For a refinement contract the
two monoids are the same: `passEquivSoundPasses : Pass (refinesContract R P host hR) ≃*
(soundPasses R P host hR)ᵐᵒᵖ`. They are kept apart because they model different things:
`soundPasses` is a *predicate* on bare `BModule → BModule` functions, a submonoid of
`Function.End BModule` multiplied by `∘`, specific to `BModule` and to `ExportRefines`;
`Pass C` is a *structure* over an arbitrary carrier and abstract contract (Core modules,
the toy IR of `Checked.lean`, other IRs over Wasm), multiplied diagrammatically, with
contracts such as `ExportEquiv` that are not a single `ExportRefines`. Equivalence
passes map into the `Eq`-sound passes by a monoid hom (`equivToSoundPasses`) that
forgets the reverse refinement.
-/

namespace Silmaril.Wasm.Binaryen.PassAPI

open Silmaril.Wasm.Binaryen Execution.Core Numerics Validation CategoryTheory

variable {H : Type}

/-- Behaviour preorders (`Binaryen/Contracts.lean`); named here because `Contract` in
this namespace is the pass-API structure. -/
abbrev BRel (R : Behaviour Val → Behaviour Val → Prop) : Prop :=
  Silmaril.Wasm.Binaryen.Contract.Rel R

/-! ## Domains -/

/-- Export refinement on Core modules: `Rel a b` iff `b` implements `a`. -/
def exportDomain (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (hR : BRel R) : Domain Module where
  Rel a b := ExportRefines R P host b a
  refl m := Silmaril.Wasm.Binaryen.Contract.refines_refl hR m
  trans h₁ h₂ := Silmaril.Wasm.Binaryen.Contract.refines_trans hR h₂ h₁

/-- Export equivalence (under `Eq`) on Core modules. -/
def equivDomain (P : Profile) (host : HostSemantics H) : Domain Module where
  Rel a b := ExportEquiv (· = ·) P host b a
  refl m := Silmaril.Wasm.Binaryen.Contract.equiv_refl Silmaril.Wasm.Binaryen.Contract.Rel.eq m
  trans h₁ h₂ := Silmaril.Wasm.Binaryen.Contract.equiv_trans
    Silmaril.Wasm.Binaryen.Contract.Rel.eq h₂ h₁

/-! ## The two IRs -/

/-- Core 3.0 modules as an IR over `D`. -/
abbrev coreIR (D : Domain Module) (Inv : Module → Prop) : IR D := ⟨Module, id, Inv⟩

/-- The Binaryen IR over `D`: denotation is lowering. -/
abbrev birIR (D : Domain Module) (Inv : BModule → Prop) : IR D := ⟨BModule, BModule.lower, Inv⟩

/-- Core validity. -/
def CoreOk (m : Module) : Prop := ∃ t, ModuleOk m t

/-- Lowering, as a translation (sound by reflexivity: lowering *is* the semantics). -/
def lowerT (D : Domain Module) :
    birIR D BModule.Ok ⟶ coreIR D CoreOk where
  run := BModule.lower
  inv_run h := h
  sound {_} _ := D.refl _

/-- Lifting every instruction into a leaf, as a translation. -/
def liftT (D : Domain Module) :
    coreIR D CoreOk ⟶ birIR D BModule.Ok where
  run := BModule.lift
  inv_run {m} h := by
    show ∃ t, ModuleOk (BModule.lift (m : Module)).lower t
    rw [lower_lift]; exact h
  sound {m} _ := by
    show D.Rel (m : Module) (BModule.lift (m : Module)).lower
    rw [lower_lift]; exact D.refl _

/-- **Core Wasm is a retract of the Binaryen IR.** -/
theorem liftT_lowerT (D : Domain Module) :
    liftT D ≫ lowerT D = 𝟙 _ :=
  Translation.ext (funext lower_lift)

/-- **The other composite is the unfold pass** (`Pass/Free.lean`). -/
theorem endEquiv_lowerT_liftT (D : Domain Module) :
    (endEquiv _ (lowerT D ≫ liftT D)).run = unfoldPass := rfl

/-! ## Contracts on Binaryen modules -/

/-- The contract of Binaryen passes for domain `D`, invariant `BModule.Ok`. -/
abbrev birContract (D : Domain Module) : Contract BModule :=
  (birIR D BModule.Ok).contract

/-- **Free passes** (lowering-preserving rewrites) are passes for every domain. -/
def freePass (D : Domain Module) (pass : BModule → BModule)
    (h : ∀ m, (pass m).lower = m.lower) : Pass (birContract D) where
  run := pass
  inv_run {m} hm := by
    show ∃ t, ModuleOk (pass m).lower t
    rw [h]; exact hm
  sound {m} _ := by
    show D.Rel m.lower (pass m).lower
    rw [h]; exact D.refl _

/-- The unfold pass. -/
def unfoldP (D : Domain Module) : Pass (birContract D) :=
  freePass D unfoldPass unfoldPass_lower

/-- The fold pass (any arity table). -/
def foldP (D : Domain Module) (arity : Instr → Option Nat) :
    Pass (birContract D) :=
  freePass D (foldPass arity) (foldPass_lower arity)

/-- **The refinement contract** on Binaryen modules: invariant `BModule.Ok`, and
`Rel m m'` iff `m'.lower` export-refines `m.lower` under `R`. -/
abbrev refinesContract (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (hR : BRel R) : Contract BModule :=
  birContract (exportDomain R P host hR)

/-- **The equivalence contract** `ExportEquiv Eq` on Binaryen modules. -/
abbrev equivContract (P : Profile) (host : HostSemantics H) : Contract BModule :=
  birContract (equivDomain P host)

/-- **The `trapsNeverHappen` contract** `ExportRefines TrapsUB` on Binaryen modules. -/
abbrev trapsUBContract (P : Profile) (host : HostSemantics H) : Contract BModule :=
  refinesContract TrapsUB P host Silmaril.Wasm.Binaryen.Contract.Rel.trapsUB

/-- `ExportRefines Eq` on Binaryen modules. -/
abbrev eqRefinesContract (P : Profile) (host : HostSemantics H) : Contract BModule :=
  refinesContract (· = ·) P host Silmaril.Wasm.Binaryen.Contract.Rel.eq

/-! ## Inclusions -/

/-- **Equivalence passes are refinement passes.** -/
theorem equiv_le_refines (P : Profile) (host : HostSemantics H) :
    equivContract P host ≤ eqRefinesContract P host :=
  ⟨fun _ => Iff.rfl, fun _ _ _ h => h.1⟩

/-- **`Eq`-refinement passes are `TrapsUB`-refinement passes.** -/
theorem refines_le_trapsUB (P : Profile) (host : HostSemantics H) :
    eqRefinesContract P host ≤ trapsUBContract P host :=
  ⟨fun _ => Iff.rfl, fun _ _ _ h => ExportRefines.trapsUB_of_eq h⟩

theorem equiv_le_trapsUB (P : Profile) (host : HostSemantics H) :
    equivContract P host ≤ trapsUBContract P host :=
  le_trans (equiv_le_refines P host) (refines_le_trapsUB P host)

/-! ## Relation to `soundPasses` (`Binaryen/Contracts.lean`) -/

section SoundPasses

variable {R : Behaviour Val → Behaviour Val → Prop} {P : Profile} {host : HostSemantics H}

/-- A pass for the refinement contract is a sound pass. -/
theorem Pass.soundPass {hR : BRel R} (p : Pass (refinesContract R P host hR)) :
    SoundPass R P host p.run :=
  fun _ hm => ⟨p.inv_run hm, p.sound hm⟩

/-- **The pass monoid of a refinement contract is the `soundPasses` submonoid**, up to
the opposite (`Pass` multiplies diagrammatically, `Function.End` by `∘`). -/
def passEquivSoundPasses (hR : BRel R) :
    Pass (refinesContract R P host hR) ≃* (soundPasses R P host hR)ᵐᵒᵖ where
  toFun p := MulOpposite.op ⟨p.run, mem_soundPasses.mpr p.soundPass⟩
  invFun f :=
    { run := f.unop.1
      inv_run := fun hm => (mem_soundPasses.mp f.unop.2 _ hm).1
      sound := fun hm => (mem_soundPasses.mp f.unop.2 _ hm).2 }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem passEquivSoundPasses_apply (hR : BRel R)
    (p : Pass (refinesContract R P host hR)) :
    ((passEquivSoundPasses hR p).unop : Function.End BModule) = p.run := rfl

/-- **Equivalence passes are `Eq`-sound passes** (forgetting the reverse refinement), as a
monoid hom. -/
def equivToSoundPasses :
    Pass (equivContract P host) →*
      (soundPasses (· = ·) P host Silmaril.Wasm.Binaryen.Contract.Rel.eq)ᵐᵒᵖ :=
  (passEquivSoundPasses Silmaril.Wasm.Binaryen.Contract.Rel.eq).toMonoidHom.comp
    (Pass.weaken (equiv_le_refines P host))

end SoundPasses

end Silmaril.Wasm.Binaryen.PassAPI
