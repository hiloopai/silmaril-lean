module

public import Silmaril.Prelude.Defs
public import Mathlib.Logic.Equiv.Sum

/-!
# Effect signatures

An effect signature `E : Sig` lists the operations `E.Op` a component may
perform, and for each operation `m` the type `E.Ar m` of its possible answers.
Signatures are the objects of the game category (`Silmaril.Games.Category`): a
strategy `E ↠ F` implements the operations of `F` while calling those of `E`.

This module gives the empty signature, binary sums `E ⊕ₛ F`, renamings
(`Sig.Hom`) and equivalences (`Sig.Equiv`), with the basic sum equivalences.
-/

@[expose] public section

namespace Silmaril.Games

universe u

/-- An effect signature: operations, each with a type of answers (its arity). -/
structure Sig : Type (u + 1) where
  /-- The operations (questions) of the signature. -/
  Op : Type u
  /-- The possible answers to each operation. -/
  Ar : Op → Type u

namespace Sig

/-- The empty signature: no operations. -/
def empty : Sig.{u} := ⟨PEmpty, fun _ => PEmpty⟩

/-- The sum of two signatures: the operations of either, with their answers. -/
def sum (E F : Sig.{u}) : Sig.{u} := ⟨E.Op ⊕ F.Op, Sum.elim E.Ar F.Ar⟩

@[inherit_doc] infixl:65 " ⊕ₛ " => Sig.sum

/-- Operations of a sum. -/
@[simp] theorem sum_Op (E F : Sig.{u}) : (E ⊕ₛ F).Op = (E.Op ⊕ F.Op) := rfl

/-- Answers of a left operation of a sum. -/
@[simp] theorem sum_Ar_inl (E F : Sig.{u}) (m : E.Op) : (E ⊕ₛ F).Ar (.inl m) = E.Ar m := rfl

/-- Answers of a right operation of a sum. -/
@[simp] theorem sum_Ar_inr (E F : Sig.{u}) (m : F.Op) : (E ⊕ₛ F).Ar (.inr m) = F.Ar m := rfl

/-- A renaming of `E` into `F`: each operation of `E` is sent to an operation of
`F`, and answers of the image are translated back. A renaming is exactly the
data needed to implement `E` by forwarding every call to `F`
(`Silmaril.Games.Handler.ofHom`). -/
structure Hom (E F : Sig.{u}) where
  /-- The image of each operation. -/
  op : E.Op → F.Op
  /-- Translate an answer of the image back to the source. -/
  ar : (m : E.Op) → F.Ar (op m) → E.Ar m

namespace Hom

/-- The identity renaming. -/
def id (E : Sig.{u}) : Hom E E := ⟨fun m => m, fun _ n => n⟩

/-- Composition of renamings (diagrammatic order: first `f`, then `g`). -/
def comp {E F G : Sig.{u}} (f : Hom E F) (g : Hom F G) : Hom E G :=
  ⟨fun m => g.op (f.op m), fun m n => f.ar m (g.ar (f.op m) n)⟩

/-- The left injection into a sum. -/
def inl (E F : Sig.{u}) : Hom E (E ⊕ₛ F) := ⟨Sum.inl, fun _ n => n⟩

/-- The right injection into a sum. -/
def inr (E F : Sig.{u}) : Hom F (E ⊕ₛ F) := ⟨Sum.inr, fun _ n => n⟩

/-- Copairing of renamings out of a sum. -/
def case {E F G : Sig.{u}} (f : Hom E G) (g : Hom F G) : Hom (E ⊕ₛ F) G where
  op := Sum.elim f.op g.op
  ar
    | .inl m, n => f.ar m n
    | .inr m, n => g.ar m n

/-- The unique renaming out of the empty signature. -/
def ofEmpty (E : Sig.{u}) : Hom empty E := ⟨PEmpty.elim, fun m => PEmpty.elim m⟩

end Hom

/-- An equivalence of signatures: a bijection of operations together with
bijections of the corresponding answer types. -/
structure Equiv (E F : Sig.{u}) where
  /-- The bijection of operations. -/
  op : E.Op ≃ F.Op
  /-- The bijection of answers, along `op`. -/
  ar : (m : E.Op) → E.Ar m ≃ F.Ar (op m)

namespace Equiv

/-- The identity equivalence. -/
def refl (E : Sig.{u}) : Equiv E E := ⟨_root_.Equiv.refl _, fun _ => _root_.Equiv.refl _⟩

/-- Composition of equivalences. -/
def trans {E F G : Sig.{u}} (f : Equiv E F) (g : Equiv F G) : Equiv E G :=
  ⟨f.op.trans g.op, fun m => (f.ar m).trans (g.ar (f.op m))⟩

/-- The inverse of an equivalence. -/
def symm {E F : Sig.{u}} (f : Equiv E F) : Equiv F E where
  op := f.op.symm
  ar m := (_root_.Equiv.cast (congrArg F.Ar (f.op.apply_symm_apply m).symm)).trans
    (f.ar (f.op.symm m)).symm

/-- The renaming underlying an equivalence: forwards `E` to `F`. -/
def toHom {E F : Sig.{u}} (f : Equiv E F) : Hom E F := ⟨f.op, fun m => (f.ar m).symm⟩

/-- `E ⊕ₛ F ≃ F ⊕ₛ E`. -/
def sumComm (E F : Sig.{u}) : Equiv (E ⊕ₛ F) (F ⊕ₛ E) where
  op := _root_.Equiv.sumComm _ _
  ar
    | .inl _ => _root_.Equiv.refl _
    | .inr _ => _root_.Equiv.refl _

/-- `(E ⊕ₛ F) ⊕ₛ G ≃ E ⊕ₛ (F ⊕ₛ G)`. -/
def sumAssoc (E F G : Sig.{u}) : Equiv ((E ⊕ₛ F) ⊕ₛ G) (E ⊕ₛ (F ⊕ₛ G)) where
  op := _root_.Equiv.sumAssoc _ _ _
  ar
    | .inl (.inl _) => _root_.Equiv.refl _
    | .inl (.inr _) => _root_.Equiv.refl _
    | .inr _ => _root_.Equiv.refl _

/-- `E ⊕ₛ empty ≃ E`. -/
def sumEmpty (E : Sig.{u}) : Equiv (E ⊕ₛ empty) E where
  op := _root_.Equiv.sumEmpty E.Op PEmpty
  ar
    | .inl _ => _root_.Equiv.refl _
    | .inr m => PEmpty.elim m

/-- `empty ⊕ₛ E ≃ E`. -/
def emptySum (E : Sig.{u}) : Equiv (empty ⊕ₛ E) E where
  op := _root_.Equiv.emptySum PEmpty E.Op
  ar
    | .inl m => PEmpty.elim m
    | .inr _ => _root_.Equiv.refl _

end Equiv

end Sig

end Silmaril.Games
