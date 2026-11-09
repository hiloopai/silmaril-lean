module

public import Silmaril.Logic.Institution.Basic
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Category.Preorder
public import Silmaril.X86.Loose.Thms

/-!
# The institution of loose x86 machine models

An x86 **signature** fixes what the machine is required to do: a decode table (the
instruction byte strings of an image, each with a form), form specifications (what a step of
each specified form may do), and a syscall interface (a slot, trivial for now). Its loose
machine `X86Loose.rel` is the *top* of the signature: at a specified form a step does what
every specification allows, anywhere else anything may happen. A **model** of the signature
is a machine below the top (`RelIsa.Le`) that always has an outcome; a **sentence** is a
family of System V function contracts; **satisfaction** is demonic total correctness from
every placement. So a sentence holds in every model as soon as it holds on the top
(`sat_of_top` in `Thms`).

Over a fixed state type `σ` with views `V : Views σ` and a form index `Φ`:

* `Sig Φ`: a signature `⟨table, forms, sys⟩`;
* `Sig.Tightens G G'` (the order `G ≤ G'`, the signature morphisms `G ⟶ G'`): `G'` lists
  every entry of `G` and specifies every form `G` specifies, each more tightly. Tighter
  signatures have smaller tops (`Sig.top_le`), so fewer models;
* `Sig.top V G`: the loose machine of `G`;
* `Model V G`: `{C // Le C (top V G) ∧ Progress C}`, and `Model.reduct` along a morphism;
* `Sen σ`, `Sat C φ`: spec families `Word → Spec σ` and `∀ entry, (φ entry).MustTotal C`;
* `room V G`: the room `(Sen σ, Model V G, Sat)`, models ordered by refinement (a thin
  category: `M ⟶ M'` when `Le M M'`); `corridor V h` the corridor of a morphism;
* `inst V : Sig Φ ⥤ Room`, `classic V : ClassicInstitution (Sig Φ)` and `bundled Φ V : Inst`:
  the institution (the last one a node for silmaril's logic graphs, `Hets.LogicGraph`).

**Design.** Sentences do not mention the signature: a function contract is about states,
not about which instructions are specified, so a signature morphism translates sentences by
the identity and the satisfaction condition is `Iff.rfl`. All the content is in the model
functor, which exists because tightening a signature shrinks its top. A model is related to
the top by same-state refinement, so a concrete machine is a model exactly when, at every
listed entry, each of its steps is one the form specifications allow
(`Silmaril.X86.Exact`).

The syscall slot `SysIface` has one value. A syscall instruction is a form like any other,
so a kernel model enters as a form specification; the slot is where a later interface (the
system calls a process may issue, with their specifications) will sit, and morphisms will
then be required to preserve or extend it.

Lean reserves `Σ`, so signatures are named `G`, `G'` in the code.
-/

@[expose] public section

namespace Silmaril.X86.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.X86 (Word RelIsa)
open Silmaril.X86.RelIsa (Views)
open Silmaril.X86.Loose (DTable FormSpec)
open Silmaril.X86.FnContract (Spec)

variable {Φ σ : Type}

/-- The syscall interface of a signature. Trivial for now: system calls are modelled by the
form specification of the `syscall` form, like any other instruction. -/
structure SysIface : Type where
  deriving DecidableEq

/-- **An x86 signature**: a decode table, form specifications, and a syscall interface. -/
structure Sig (Φ : Type) : Type where
  /-- The listed instructions: byte strings with their forms. -/
  table : DTable Φ
  /-- What each form may do; `none` is unspecified (anything goes). -/
  forms : Loose.Sigma Φ
  /-- The syscall interface (trivial for now). -/
  sys : SysIface := {}

/-- **`G'` tightens `G`**: it lists every entry of `G`, and specifies every form `G`
specifies, more tightly. -/
structure Sig.Tightens (G G' : Sig Φ) : Prop where
  table : ∀ e ∈ G.table, e ∈ G'.table
  forms : ∀ i F, G.forms i = some F → ∃ F', G'.forms i = some F' ∧ F.Tightens F'

/-- Signatures ordered by tightening; `G ⟶ G'` is `G ≤ G'` (`Preorder.smallCategory`). -/
instance : Preorder (Sig Φ) where
  le := Sig.Tightens
  le_refl _ := ⟨fun _ h => h, fun _ F h => ⟨F, h, FormSpec.Tightens.refl F⟩⟩
  le_trans _ _ _ h₁ h₂ :=
    ⟨fun e he => h₂.table e (h₁.table e he), fun i F hF => by
      obtain ⟨F₁, hF₁, h₁₂⟩ := h₁.forms i F hF
      obtain ⟨F₂, hF₂, h₂₃⟩ := h₂.forms i F₁ hF₁
      exact ⟨F₂, hF₂, h₁₂.trans h₂₃⟩⟩

/-- **The top of a signature**: its loose machine. -/
def Sig.top (V : Views σ) (G : Sig Φ) : RelIsa σ := Loose.X86Loose.rel G.table G.forms V

/-- **Tightening shrinks the top**. -/
theorem Sig.top_le (V : Views σ) {G G' : Sig Φ} (h : G ≤ G') :
    RelIsa.Le (G'.top V) (G.top V) :=
  (Loose.X86Loose.antitone_S (D := G'.table) (V := V) h.forms).trans
    (Loose.X86Loose.antitone_D (S := G.forms) (V := V) h.table)

/-- **A model of `G`**: a machine below the top that has an outcome from every live state. -/
def Model (V : Views σ) (G : Sig Φ) : Type :=
  {C : RelIsa σ // RelIsa.Le C (G.top V) ∧ RelIsa.Progress C}

/-- Models ordered by refinement: `M ≤ M'` when `M` has fewer behaviours than `M'`. -/
instance (V : Views σ) (G : Sig Φ) : Preorder (Model V G) where
  le M M' := RelIsa.Le M.1 M'.1
  le_refl M := RelIsa.Le.refl M.1
  le_trans _ _ _ h₁ h₂ := RelIsa.Le.trans h₁ h₂

/-- **The reduct**: a model of a tighter signature is a model of the looser one. -/
def Model.reduct {V : Views σ} {G G' : Sig Φ} (h : G ≤ G') (M : Model V G') : Model V G :=
  ⟨M.1, M.2.1.trans (Sig.top_le V h), M.2.2⟩

/-- **Sentences**: System V function contracts, one per placement of the function. -/
abbrev Sen (σ : Type) : Type := Word → Spec σ

/-- **Satisfaction**: from every placement, the contract is demonically totally correct
on `C`. -/
def Sat (C : RelIsa σ) (φ : Sen σ) : Prop := ∀ entry, (φ entry).MustTotal C

/-- **The room of a signature**: contracts, models (ordered by refinement) and
satisfaction. -/
def room (V : Views σ) (G : Sig Φ) : Room.{0, 0, 0} :=
  ⟨Sen σ, Cat.of (Model V G), fun M φ => Sat M.1 φ⟩

/-- The corridor of a morphism: sentences unchanged, models reduced. -/
def corridor (V : Views σ) {G G' : Sig Φ} (h : G ≤ G') : room V G ⟶ room V G' :=
  ⟨id, (Monotone.functor (f := fun M : Model V G' => M.reduct h) fun _ _ hle => hle :
    Model V G' ⥤ Model V G), fun _ _ => Iff.rfl⟩

/-- **The institution of loose x86 models**, as a functor into rooms. -/
def inst (V : Views σ) : Sig Φ ⥤ Room.{0, 0, 0} where
  obj := room V
  map f := corridor V f.le
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The institution of loose x86 models**, in the classic presentation. -/
def classic (V : Views σ) : ClassicInstitution.{0, 0, 0, 0, 0} (Sig Φ) :=
  ClassicInstitution.ofRoomFunctor (inst V)

/-- **The institution as a bundled `Inst`**: a node of a silmaril logic graph, the source or
target of institution (co)morphisms. -/
def bundled (Φ : Type) (V : Views σ) : Inst.{0, 0, 0, 0, 0} := ⟨Sig Φ, inst V⟩

end Silmaril.X86.Institution
