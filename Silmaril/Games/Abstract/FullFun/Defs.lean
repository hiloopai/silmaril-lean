module

public import Silmaril.Games.Abstract.HostRunInf.Defs
public import Mathlib.Data.Stream.Init

/-!
# Full observations of functions: finite behaviours and productive runs

A function's **full observation** pairs its finite behaviours (`AFun`: finished ends, a trap
with its store erased, and divergence after finitely many import calls) with its productive
runs (`PInf`: infinite streams of answered import calls, each one coherent run). `AFun` alone
cannot show a productive run (`Silmaril.Games.Abstract.HostRunInf`).

* `FullFun.seq`: sequencing. The finite part is `AFun.seq`. A productive run of `f ; g` is a
  productive run of `f`, or a finished return of `f` followed by a productive run of `g` on
  its result and state, joined into one stream (`Stream'.appendStream'`);
* `FullFun.pure`: the identity (return the argument, no productive run).

For the finite part to observe quiescent divergence, the `AFun` must be divergence-aware
(`div` ends, as in `Shape.closeDL`/`closeDLog`), not a divergence-omitting closing.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

/-- **A full observation**: finite behaviours and productive runs. -/
abbrev FullFun (E : Sig.{u}) (S A B : Type u) : Type u := AFun E S A B × PInf E S A

namespace FullFun

variable {E : Sig.{u}} {S A B C : Type u}

/-- **Sequencing of full observations.** -/
def seq (f : FullFun E S A B) (g : FullFun E S B C) : FullFun E S A C :=
  (AFun.seq f.1 g.1, fun s a => f.2 s a ∪
    {ω | ∃ (c : List (Call E)) (b : B) (s₁ : S) (ω' : Nat → Call E),
      (c, End.ret b s₁) ∈ f.1 s a ∧ ω' ∈ g.2 s₁ b ∧ ω = c ++ₛ ω'})

/-- **The identity**: return the argument in the same state, with no productive run. -/
def pure : FullFun E S A A := (fun s a => {([], End.ret a s)}, fun _ _ => ∅)

end FullFun

end Silmaril.Games.Abstract
