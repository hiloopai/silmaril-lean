module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Silmaril.Proofs.Games.Abstract.FullFun.Basic
import Silmaril.Proofs.Games.Abstract.FullFun.Laws

/-!
# Full observations of functions: theorems

Proofs in `Silmaril.Proofs.Games.Abstract.FullFun`.

* `consistent_append`: consistency of a joined stream `c ++ₛ ω` splits exactly into the
  finished prefix `c` and the tail `ω`;
* `hostObsInf_seq` (**host preservation of sequencing**): the productive observations of
  `FullFun.seq f g` against a relational host are those of `f`, or a finished return of `f`
  with a consistent log followed by a productive observation of `g`;
* `pure_inf`, `pure_seq_inf`: the identity has no productive run, and does not change the
  productive runs of what follows;
* `FullFun.seq_assoc_fin`, `FullFun.seq_assoc_inf`, `FullFun.seq_assoc`: sequencing is
  associative, finite part (`AFun.seq`) and productive runs;
* `FullFun.seq_pure_inf`, `FullFun.seq_pure`, `FullFun.pure_seq`: the identity is a unit on
  both sides;
* `FullFun.iter_fin`: the finite part of iteration is `AFun.iter`;
* `streamPrefix_appendStream`, `appendStream_chain`, `streamConcat_of_appendChain`: stream
  bookkeeping for `++ₛ`, as `Shape.streamAppend_chain` for `++ω`;
* `consistent_streamConcat`: consistency of a concatenated stream (`Shape.StreamConcat`) is
  consistency of every segment;
* `hostObsInf_iter` (**host preservation of iteration**): the productive observations of
  `FullFun.iter F` against a relational host are (a) a consistent finite continuing chain
  followed by a productive observation of the next iteration, or (b) an infinite continuing
  chain with every segment consistent.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S A B C : Type u}

/-- Consistency of a joined stream splits into the prefix and the tail. -/
theorem consistent_append {R : HostRel E} (c : List (Call E)) (ω : Nat → Call E) :
    (∀ n, R ((c ++ₛ ω) n).1 (.answer ((c ++ₛ ω) n).2)) ↔
      R.Consistent c ∧ ∀ n, R (ω n).1 (.answer (ω n).2) :=
  Silmaril.Proofs.Games.Abstract.FullFun.consistent_append c ω

/-- **Host preservation of sequencing** (productive part). -/
theorem hostObsInf_seq {R : HostRel E} (f : FullFun E S A B) (g : FullFun E S B C) (s : S)
    (a : A) (ω : Nat → Call E) :
    ω ∈ hostObsInf R (FullFun.seq f g).2 s a ↔
      ω ∈ hostObsInf R f.2 s a ∨
        ∃ (c : List (Call E)) (b : B) (s₁ : S) (ω' : Nat → Call E),
          (c, End.ret b s₁) ∈ f.1 s a ∧ R.Consistent c ∧ ω' ∈ hostObsInf R g.2 s₁ b ∧
          ω = c ++ₛ ω' :=
  Silmaril.Proofs.Games.Abstract.FullFun.hostObsInf_seq f g s a ω

/-- The identity has no productive run. -/
theorem FullFun.pure_inf (s : S) (a : A) : (FullFun.pure : FullFun E S A A).2 s a = ∅ := rfl

/-- Sequencing after the identity keeps the productive runs. -/
theorem FullFun.pure_seq_inf (g : FullFun E S A B) (s : S) (a : A) :
    (FullFun.seq FullFun.pure g).2 s a = g.2 s a :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_seq_inf g s a

/-- **Associativity of sequencing**, finite part. -/
theorem FullFun.seq_assoc_fin {D : Type u} (f : AFun E S A B) (g : AFun E S B C)
    (h : AFun E S C D) : AFun.seq (AFun.seq f g) h = AFun.seq f (AFun.seq g h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_assoc_fin f g h

/-- **Associativity of sequencing**, productive runs. -/
theorem FullFun.seq_assoc_inf {D : Type u} (f : FullFun E S A B) (g : FullFun E S B C)
    (h : FullFun E S C D) :
    (FullFun.seq (FullFun.seq f g) h).2 = (FullFun.seq f (FullFun.seq g h)).2 :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_assoc_inf f g h

/-- **Associativity of sequencing.** -/
theorem FullFun.seq_assoc {D : Type u} (f : FullFun E S A B) (g : FullFun E S B C)
    (h : FullFun E S C D) : FullFun.seq (FullFun.seq f g) h = FullFun.seq f (FullFun.seq g h) :=
  Prod.ext (FullFun.seq_assoc_fin f.1 g.1 h.1) (FullFun.seq_assoc_inf f g h)

/-- The identity is a right unit. -/
theorem FullFun.seq_pure (f : FullFun E S A B) : FullFun.seq f FullFun.pure = f :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_pure f

/-- Sequencing before the identity keeps the productive runs. -/
theorem FullFun.seq_pure_inf (f : FullFun E S A B) (s : S) (a : A) :
    (FullFun.seq f FullFun.pure).2 s a = f.2 s a := by
  rw [FullFun.seq_pure]

/-- The identity is a left unit. -/
theorem FullFun.pure_seq (g : FullFun E S A B) : FullFun.seq FullFun.pure g = g :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_seq g

/-- The finite part of iteration is `AFun.iter`. -/
theorem FullFun.iter_fin (F : FullFun E S A (B ⊕ A)) : (FullFun.iter F).1 = AFun.iter F.1 := rfl

/-- A list is a prefix of itself in front of a stream. -/
theorem streamPrefix_appendStream {α : Type u} (c : List α) (ω : Nat → α) :
    Shape.StreamPrefix c (c ++ₛ ω) :=
  Silmaril.Proofs.Games.Abstract.FullFun.streamPrefix_appendStream c ω

/-- A chain of streams, each a segment in front of the next. -/
theorem appendStream_chain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ₛ w (n + 1)) (n : Nat) :
    w 0 = ((List.range n).flatMap cs) ++ₛ w n :=
  Silmaril.Proofs.Games.Abstract.FullFun.appendStream_chain h n

/-- A chain of streams of unbounded total length is the concatenation of its segments. -/
theorem streamConcat_of_appendChain {α : Type u} {w : Nat → Nat → α} {cs : Nat → List α}
    (h : ∀ n, w n = cs n ++ₛ w (n + 1))
    (hu : ∀ N, ∃ n, N ≤ ((List.range n).flatMap cs).length) : Shape.StreamConcat cs (w 0) :=
  Silmaril.Proofs.Games.Abstract.FullFun.streamConcat_of_appendChain h hu

/-- Consistency of a concatenated stream is consistency of every segment. -/
theorem consistent_streamConcat {R : HostRel E} {l : Nat → List (Call E)} {ω : Nat → Call E}
    (h : Shape.StreamConcat l ω) :
    (∀ n, R (ω n).1 (.answer (ω n).2)) ↔ ∀ n, R.Consistent (l n) :=
  Silmaril.Proofs.Games.Abstract.FullFun.consistent_streamConcat h

/-- **Host preservation of iteration** (productive part). -/
theorem hostObsInf_iter {R : HostRel E} (F : FullFun E S A (B ⊕ A)) (s : S) (a : A)
    (ω : Nat → Call E) :
    ω ∈ hostObsInf R (FullFun.iter F).2 s a ↔
      (∃ (c : List (Call E)) (s' : S) (a' : A) (ω' : Nat → Call E),
          FullFun.ContChain F.1 s a c s' a' ∧ R.Consistent c ∧ ω' ∈ hostObsInf R F.2 s' a' ∧
          ω = c ++ₛ ω') ∨
        ∃ (σ : Nat → S × A) (l : Nat → List (Call E)), σ 0 = (s, a) ∧
          (∀ n, (l n, End.ret (.inr (σ (n + 1)).2) (σ (n + 1)).1) ∈ F.1 (σ n).1 (σ n).2) ∧
          (∀ n, R.Consistent (l n)) ∧ Shape.StreamConcat l ω :=
  Silmaril.Proofs.Games.Abstract.FullFun.hostObsInf_iter F s a ω

end Silmaril.Games.Abstract
