module

public import Silmaril.Games.Abstract.HostRunInf.Defs
public import Silmaril.Games.Abstract.FunctionIter.Defs
public import Silmaril.Games.Abstract.ModuleInf.Defs
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
* `FullFun.pure`: the identity (return the argument, no productive run);
* `FullFun.iter`: iteration of a loop body (`inl` exits, `inr` continues). The finite part is
  `AFun.iter`. A productive run is either (a) a finite chain of finished continuing iterations
  (`ContChain`) followed by a productive run of the next iteration, or (b) an infinite chain of
  finished continuing iterations whose logs, **one choice per iteration**, concatenate to the
  stream with unbounded total length (`Shape.StreamConcat`). In (b) finitely many iterations
  may be silent; infinitely many must make import calls, which unboundedness says.

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

/-- **A finite chain of finished continuing iterations** of a loop body `f`: from `(s, a)`,
iterations each returning `inr`, with logs concatenating to `c`, reach `(s', a')`. -/
inductive ContChain (f : AFun E S A (B ⊕ A)) : S → A → List (Call E) → S → A → Prop
  /-- No iteration. -/
  | refl {s a} : ContChain f s a [] s a
  /-- One continuing iteration with log `c₁`, then the rest of the chain. -/
  | step {s a c₁ s' a' c₂ s'' a''} : (c₁, End.ret (.inr a') s') ∈ f s a →
      ContChain f s' a' c₂ s'' a'' → ContChain f s a (c₁ ++ c₂) s'' a''

/-- **Iteration of full observations.** The finite part is `AFun.iter`; the productive runs
are (a) a finite continuing chain then a productive run of the next iteration, or (b) an
infinite continuing chain whose logs, one per iteration, concatenate to the stream. -/
def iter (F : FullFun E S A (B ⊕ A)) : FullFun E S A B :=
  (AFun.iter F.1, fun s a =>
    {ω | ∃ (c : List (Call E)) (s' : S) (a' : A) (ω' : Nat → Call E),
      ContChain F.1 s a c s' a' ∧ ω' ∈ F.2 s' a' ∧ ω = c ++ₛ ω'} ∪
    {ω | ∃ (σ : Nat → S × A) (l : Nat → List (Call E)), σ 0 = (s, a) ∧
      (∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ F.1 (σ n).1 (σ n).2) ∧
      Shape.StreamConcat l ω})

end FullFun

end Silmaril.Games.Abstract
