module

public import Silmaril.Games.Abstract.Module.Defs

/-!
# Closing with productive runs inside one function

`Shape.closeInf m` gives the productive runs of a closed module that come from unbounded
internal recursion (`InfChain`). Its scope note: a single function that keeps calling imports
(a loop around a host call) has no infinite behaviour as an `AFun`, so it is not covered. This
module adds such runs, given as data next to the open module:

* `streamAppend l ω` (`l ++ω ω`): a finite list in front of a stream;
* `StreamConcat l ω`: the stream `ω` is the concatenation of the lists `l 0, l 1, …`, of
  unbounded total length (the style of `InfChain`);
* `OpenInf sh`: per call, a set of infinite streams of open calls (imports and internal calls,
  each with its answer), the productive runs of one function of the open module;
* `Res1 c x l`: one open call resolved through a closed module `c`: an import call stays
  (`l = [x]`), an internal call answered `(b, s')` becomes the import calls `l` of a returning
  behaviour of the callee with that answer;
* `SubstInf c ν ω`: an infinite open stream `ν` resolved through `c`, **one choice per
  position**: lists `l i` resolving `ν i`, whose concatenation is `ω` with infinitely many
  import calls in total. The prefixes of `ν` are not resolved independently;
* `closeInfL m mi`: `closeInf m` plus, after the import calls of every finite descent path to a
  call `z`, the resolution of a productive run of `z`'s own function (`mi z`).

Theorems in `Silmaril.Games.Abstract.ModuleInf.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.Shape

open Silmaril.Games

universe u

variable {sh : Shape.{u}}

/-- **A list in front of a stream.** -/
def streamAppend {α : Type u} (l : List α) (ω : Nat → α) : Nat → α := fun i =>
  if h : i < l.length then l[i] else ω (i - l.length)

@[inherit_doc] infixr:65 " ++ω " => streamAppend

/-- **`ω` is the concatenation of the lists `l n`**, of unbounded total length. -/
def StreamConcat {α : Type u} (l : Nat → List α) (ω : Nat → α) : Prop :=
  (∀ n, StreamPrefix ((List.range n).flatMap l) ω) ∧
    ∀ N, ∃ n, N ≤ ((List.range n).flatMap l).length

variable (sh) in
/-- **Productive runs of the functions of an open module**: per call, infinite streams of
open calls, each with its answer. -/
abbrev OpenInf : Type u :=
  (f : sh.F) → sh.S → sh.A f → Set (Nat → Call (sh.E ⊕ₛ sh.self))

/-- **One open call resolved through `c`**: an import call stays; an internal call answered
`(b, s')` becomes the import calls of a returning behaviour of the callee with that answer. -/
inductive Res1 (c : sh.ClosedMod) : Call (sh.E ⊕ₛ sh.self) → List (Call sh.E) → Prop
  | ext {m : sh.E.Op} {n : sh.E.Ar m} : Res1 c ⟨.inl m, n⟩ [⟨m, n⟩]
  | int {g : sh.F} {a : sh.A g} {s : sh.S} {b : sh.B g} {s' : sh.S} {c₁ : List (Call sh.E)} :
      (c₁, .ret b s') ∈ c g s a → Res1 c ⟨.inr ⟨g, (a, s)⟩, (b, s')⟩ c₁

/-- **An infinite open stream resolved through `c`**, one choice per position: `l i`
resolves `ν i`, and `ω` is the concatenation of the `l i`, with infinitely many import
calls. -/
def SubstInf (c : sh.ClosedMod) (ν : Nat → Call (sh.E ⊕ₛ sh.self)) (ω : Nat → Call sh.E) :
    Prop :=
  ∃ l : Nat → List (Call sh.E), (∀ i, Res1 c (ν i) (l i)) ∧ StreamConcat l ω

/-- **Closing with productive runs inside one function.** `closeInf m` plus, after the import
calls `qs` of every finite descent path to a call `z`, the resolution through `close m` of a
productive open run `ν ∈ mi z` of `z`'s own function. -/
def closeInfL (m : sh.OpenMod) (mi : OpenInf sh) (f : sh.F) (s : sh.S) (a : sh.A f) :
    Set (Nat → Call sh.E) :=
  closeInf m f s a ∪ {ω | ∃ (z : sh.self.Op) (qs : List (Call sh.E))
    (ν : Nat → Call (sh.E ⊕ₛ sh.self)) (ω' : Nat → Call sh.E),
    DescPath m (close m) ⟨f, (a, s)⟩ qs z ∧ ν ∈ mi z.1 z.2.2 z.2.1 ∧
      SubstInf (close m) ν ω' ∧ ω = qs ++ω ω'}

end Silmaril.Games.Abstract.Shape
