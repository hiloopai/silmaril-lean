module

public import Mathlib.Algebra.BigOperators.Fin
public import Silmaril.SSA.Peggy.Bridge.Equational.Defs

/-! # Preorder numbering of typed term occurrences -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Equational

open Silmaril.Logic.Algebraic
open scoped BigOperators

variable {S : Type} {A B : ManySorted.Signature S} {k : Nat} {Γ : Fin k → S}

abbrev Occurrence (A : ManySorted.Signature S) (Γ : Fin k → S) := Σ s, ManySorted.Term A Γ s

/-- A later row containing the required child term, with its sort. -/
structure Child {n : Nat} (rows : Fin n → Occurrence A Γ) (parent : Fin n)
    (t : Occurrence A Γ) where
  id : Fin n
  after : parent.val < id.val
  term_eq : rows id = t

/-- A variable has no edges. An application names one later row per argument. -/
structure Wiring {n : Nat} (rows : Fin n → Occurrence A Γ) (i : Fin n)
    {s : S} (t : ManySorted.Term A Γ s) where
  children : match t with
    | .var _ => Unit
    | .app _ args => ∀ j, Child rows i ⟨_, args j⟩

namespace Wiring

variable {n : Nat} {rows : Fin n → Occurrence A Γ} {i : Fin n}

def var (v : Fin k) : Wiring rows i (.var v) := ⟨()⟩

def app {arity : Nat} {inputs : Fin arity → S} {s : S} (op : A.operations arity inputs s)
    (args : ∀ j, ManySorted.Term A Γ (inputs j)) (children : ∀ j, Child rows i ⟨inputs j, args j⟩) :
    Wiring rows i (.app op args) := ⟨children⟩

end Wiring

/-- The table is nonempty, with the source expression at position zero. -/
structure Numbered {s : S} (t : ManySorted.Term A Γ s) where
  tailSize : Nat
  rows : Fin (tailSize + 1) → Occurrence A Γ
  root : rows 0 = ⟨s, t⟩
  wiring : ∀ i, Wiring rows i (rows i).2

namespace Numbered

protected def var (i : Fin k) : Numbered (A := A) (Γ := Γ) (.var i) :=
  ⟨0, fun _ => ⟨Γ i, .var i⟩, rfl, fun _ => .var i⟩

variable {arity : Nat} {inputs : Fin arity → S}
variable {args : ∀ j, ManySorted.Term A Γ (inputs j)}

abbrev Tail (subs : ∀ j, Numbered (args j)) := ∑ j, ((subs j).tailSize + 1)

/-- After row zero, each argument contributes a contiguous block in argument order. -/
def embed (subs : ∀ j, Numbered (args j)) (j : Fin arity) (i : Fin ((subs j).tailSize + 1)) :
    Fin (Tail subs + 1) := (finSigmaFinEquiv ⟨j, i⟩).succ

theorem embed_lt (subs : ∀ j, Numbered (args j)) (j : Fin arity)
    {i i' : Fin ((subs j).tailSize + 1)} (h : i.val < i'.val) :
    (embed subs j i).val < (embed subs j i').val := by
  simp only [embed, Fin.val_succ, finSigmaFinEquiv_apply]
  omega

/-- Every non-root address identifies a row in one argument's block. -/
def casesRow (subs : ∀ j, Numbered (args j))
    (motive : Fin (Tail subs + 1) → Sort*) (root : motive 0)
    (child : ∀ j i, motive (embed subs j i)) (i : Fin (Tail subs + 1)) : motive i :=
  Fin.cases root ((Equiv.piCongrLeft (fun j => motive j.succ) finSigmaFinEquiv)
    (fun p => child p.1 p.2)) i

@[simp] theorem casesRow_zero (subs : ∀ j, Numbered (args j))
    (motive : Fin (Tail subs + 1) → Sort*) (root : motive 0)
    (child : ∀ j i, motive (embed subs j i)) : casesRow subs motive root child 0 = root := rfl

@[simp] theorem casesRow_embed (subs : ∀ j, Numbered (args j))
    (motive : Fin (Tail subs + 1) → Sort*) (root : motive 0)
    (child : ∀ j i, motive (embed subs j i)) (j : Fin arity) (i : Fin ((subs j).tailSize + 1)) :
    casesRow subs motive root child (embed subs j i) = child j i :=
  Equiv.piCongrLeft_apply_apply (fun j : Fin (Tail subs) => motive j.succ)
    (@finSigmaFinEquiv arity (fun j => (subs j).tailSize + 1)) (fun p => child p.1 p.2) ⟨j, i⟩

def appRows (head : Occurrence A Γ) (subs : ∀ j, Numbered (args j)) :
    Fin (Tail subs + 1) → Occurrence A Γ :=
  casesRow subs (fun _ => Occurrence A Γ) head (fun j i => (subs j).rows i)

@[simp] theorem appRows_embed (head : Occurrence A Γ) (subs : ∀ j, Numbered (args j))
    (j : Fin arity) (i : Fin ((subs j).tailSize + 1)) :
    appRows head subs (embed subs j i) = (subs j).rows i :=
  casesRow_embed subs _ _ _ j i

/-- Transport a row's wiring into its argument block. -/
def liftWiring (head : Occurrence A Γ) (subs : ∀ j, Numbered (args j)) (j : Fin arity)
    {i : Fin ((subs j).tailSize + 1)} {s : S} {t : ManySorted.Term A Γ s}
    (w : Wiring (subs j).rows i t) : Wiring (appRows head subs) (embed subs j i) t :=
  match t with
  | .var v => .var v
  | .app op args => .app op args fun slot =>
      let c := w.children slot
      ⟨embed subs j c.id, embed_lt subs j c.after,
        (appRows_embed head subs j c.id).trans c.term_eq⟩

protected def app {s : S} (op : A.operations arity inputs s) (subs : ∀ j, Numbered (args j)) :
    Numbered (.app op args) where
  tailSize := Tail subs
  rows := appRows ⟨s, .app op args⟩ subs
  root := rfl
  wiring := casesRow subs (fun i => Wiring _ i ((appRows ⟨s, .app op args⟩ subs) i).2)
    (.app op args fun j =>
      ⟨embed subs j 0, Nat.zero_lt_succ _, (appRows_embed _ subs j 0).trans (subs j).root⟩)
    (fun j i => (appRows_embed _ subs j i).symm ▸ liftWiring _ subs j ((subs j).wiring i))

/-- Use one row per occurrence, leaving the source parameter context intact. -/
def compile {s : S} (t : ManySorted.Term A Γ s) : Numbered t :=
  match t with
  | .var v => Numbered.var v
  | .app op args => Numbered.app op (fun j => compile (args j))

end Numbered
end Silmaril.SSA.Peggy.Bridge.Equational
