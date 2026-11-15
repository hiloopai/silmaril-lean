module

public import Silmaril.Games.Abstract.FullFun.Defs
public import Silmaril.Games.Abstract.HostRunInf.Thms
import Silmaril.Proofs.Games.Abstract.FullFun.Basic
import Silmaril.Proofs.Games.Abstract.FullFun.Laws
import Silmaril.Proofs.Games.Abstract.FullFun.Tensor

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

**Pure maps and whiskering** (`Silmaril.Proofs.Games.Abstract.FullFun.Tensor`):

* `FullFun.mem_map`: the finite behaviours of `f.map h` are those of `f` with `h` applied to
  returned values;
* `FullFun.map_id`, `FullFun.map_map`, `FullFun.comap_id`, `FullFun.comap_comap`,
  `FullFun.map_comap`: functoriality of post- and pre-composition;
* `FullFun.seq_pure_map`, `FullFun.pure_map_seq`, `FullFun.seq_map`, `FullFun.map_seq`,
  `FullFun.comap_seq`: interaction with sequencing;
* `FullFun.whiskerRight_pure`, `FullFun.whiskerRight_seq`, `FullFun.whiskerLeft_pure`,
  `FullFun.whiskerLeft_seq`: whiskering is functorial (`(- ⋉ C)` and `(C ⋊ -)` preserve the
  identity and sequencing);
* `FullFun.interchange_pure_left`, `FullFun.interchange_pure_right`: the interchange law holds
  when one of the two functions is a pure map;
* `FullFun.not_interchange`: it fails for two effectful functions (two single calls are logged
  in the order they run), so full observations form a premonoidal and not a monoidal
  structure;
* `hostObsInf_map`, `hostObsInf_comap`, `hostObsInf_whiskerRight`, `hostObsInf_whiskerLeft`:
  host preservation; the productive observations are those of the original function.
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

/-! ## Pure maps and whiskering -/

variable {D : Type u}

/-- The finite behaviours of a pure post-composition. -/
theorem FullFun.mem_map (f : FullFun E S A B) (h : B → C) (s : S) (a : A)
    (x : CallBeh E S C) :
    x ∈ (f.map h).1 s a ↔ ∃ c e, (c, e) ∈ f.1 s a ∧ x = (c, FullFun.endMap h e) :=
  Silmaril.Proofs.Games.Abstract.FullFun.mem_map f h s a x

/-- The productive runs of a pure post-composition are those of the original. -/
theorem FullFun.map_inf (f : FullFun E S A B) (h : B → C) : (f.map h).2 = f.2 := rfl

/-- Post-composition with the identity. -/
theorem FullFun.map_id (f : FullFun E S A B) : f.map id = f :=
  Silmaril.Proofs.Games.Abstract.FullFun.map_id f

/-- Post-composition is functorial. -/
theorem FullFun.map_map (f : FullFun E S A B) (h : B → C) (h' : C → D) :
    (f.map h).map h' = f.map (h' ∘ h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.map_map f h h'

/-- Pre-composition with the identity. -/
theorem FullFun.comap_id (f : FullFun E S A B) : f.comap id = f := rfl

/-- Pre-composition is functorial. -/
theorem FullFun.comap_comap {A' A'' : Type u} (f : FullFun E S A B) (k : A' → A)
    (k' : A'' → A') : (f.comap k).comap k' = f.comap (k ∘ k') := rfl

/-- Pre- and post-composition commute. -/
theorem FullFun.map_comap {A' : Type u} (f : FullFun E S A B) (k : A' → A) (h : B → C) :
    (f.comap k).map h = (f.map h).comap k := rfl

/-- Sequencing with a pure map is that map. -/
theorem FullFun.seq_pure_map (f : FullFun E S A B) (h : B → C) :
    FullFun.seq f (FullFun.pure.map h) = f.map h :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_pure_map f h

/-- Sequencing after a pure map is pre-composition. -/
theorem FullFun.pure_map_seq (h : A → B) (g : FullFun E S B C) :
    FullFun.seq (FullFun.pure.map h) g = g.comap h :=
  Silmaril.Proofs.Games.Abstract.FullFun.pure_map_seq h g

/-- A pure map can be moved across sequencing. -/
theorem FullFun.seq_map (f : FullFun E S A B) (h : B → C) (g : FullFun E S C D) :
    FullFun.seq (f.map h) g = FullFun.seq f (g.comap h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.seq_map f h g

/-- A pure map after a sequence is a pure map after its second part. -/
theorem FullFun.map_seq (f : FullFun E S A B) (g : FullFun E S B C) (h : C → D) :
    (FullFun.seq f g).map h = FullFun.seq f (g.map h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.map_seq f g h

/-- Pre-composition of a sequence is pre-composition of its first part. -/
theorem FullFun.comap_seq {A' : Type u} (f : FullFun E S A B) (g : FullFun E S B C)
    (k : A' → A) : (FullFun.seq f g).comap k = FullFun.seq (f.comap k) g := rfl

/-- Right whiskering preserves the identity. -/
theorem FullFun.whiskerRight_pure :
    (FullFun.pure : FullFun E S A A).whiskerRight C = FullFun.pure :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerRight_pure

/-- **Right whiskering preserves sequencing.** -/
theorem FullFun.whiskerRight_seq (f : FullFun E S A B) (g : FullFun E S B D) (C : Type u) :
    (FullFun.seq f g).whiskerRight C = FullFun.seq (f.whiskerRight C) (g.whiskerRight C) :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerRight_seq f g C

/-- Left whiskering preserves the identity. -/
theorem FullFun.whiskerLeft_pure :
    (FullFun.pure : FullFun E S A A).whiskerLeft C = FullFun.pure :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerLeft_pure

/-- **Left whiskering preserves sequencing.** -/
theorem FullFun.whiskerLeft_seq (f : FullFun E S A B) (g : FullFun E S B D) (C : Type u) :
    (FullFun.seq f g).whiskerLeft C = FullFun.seq (f.whiskerLeft C) (g.whiskerLeft C) :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerLeft_seq f g C

/-- Right whiskering of a pure map is a pure map. -/
theorem FullFun.whiskerRight_pure_map (h : A → B) (C : Type u) :
    ((FullFun.pure : FullFun E S A A).map h).whiskerRight C =
      FullFun.pure.map (Prod.map h id) :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerRight_pure_map h C

/-- Left whiskering of a pure map is a pure map. -/
theorem FullFun.whiskerLeft_pure_map (h : A → B) (C : Type u) :
    ((FullFun.pure : FullFun E S A A).map h).whiskerLeft C =
      FullFun.pure.map (Prod.map id h) :=
  Silmaril.Proofs.Games.Abstract.FullFun.whiskerLeft_pure_map h C

/-- **Interchange when the first component is a pure map.** -/
theorem FullFun.interchange_pure_left (h : A → B) (g : FullFun E S C D) :
    FullFun.seq (((FullFun.pure : FullFun E S A A).map h).whiskerRight C) (g.whiskerLeft B) =
      FullFun.seq (g.whiskerLeft A)
        (((FullFun.pure : FullFun E S A A).map h).whiskerRight D) :=
  Silmaril.Proofs.Games.Abstract.FullFun.interchange_pure_left h g

/-- **Interchange when the second component is a pure map.** -/
theorem FullFun.interchange_pure_right (f : FullFun E S A B) (k : C → D) :
    FullFun.seq (f.whiskerRight C) (((FullFun.pure : FullFun E S C C).map k).whiskerLeft B) =
      FullFun.seq (((FullFun.pure : FullFun E S C C).map k).whiskerLeft A)
        (f.whiskerRight D) :=
  Silmaril.Proofs.Games.Abstract.FullFun.interchange_pure_right f k

/-- **The interchange law fails** for effectful functions: with two operations, each with one
answer, calling `true` on the first component and `false` on the second gives the log
`[true, false]` in one order and `[false, true]` in the other. -/
theorem FullFun.not_interchange :
    ∃ (E : Sig.{0}) (f g : FullFun E PUnit PUnit PUnit),
      FullFun.seq (f.whiskerRight PUnit) (g.whiskerLeft PUnit) ≠
        FullFun.seq (g.whiskerLeft PUnit) (f.whiskerRight PUnit) :=
  ⟨_, _, _, Silmaril.Proofs.Games.Abstract.FullFun.not_interchange⟩

/-- Host preservation of post-composition: the same productive observations. -/
theorem hostObsInf_map {R : HostRel E} (f : FullFun E S A B) (h : B → C) :
    hostObsInf R (f.map h).2 = hostObsInf R f.2 := rfl

/-- Host preservation of pre-composition. -/
theorem hostObsInf_comap {A' : Type u} {R : HostRel E} (f : FullFun E S A B) (k : A' → A)
    (s : S) (a : A') : hostObsInf R (f.comap k).2 s a = hostObsInf R f.2 s (k a) := rfl

/-- Host preservation of right whiskering: the productive observations at `(a, c)` are those
at `a`. -/
theorem hostObsInf_whiskerRight {R : HostRel E} (f : FullFun E S A B) (s : S) (a : A) (c : C) :
    hostObsInf R (f.whiskerRight C).2 s (a, c) = hostObsInf R f.2 s a := rfl

/-- Host preservation of left whiskering: the productive observations at `(c, a)` are those
at `a`. -/
theorem hostObsInf_whiskerLeft {R : HostRel E} (f : FullFun E S A B) (s : S) (c : C) (a : A) :
    hostObsInf R (f.whiskerLeft C).2 s (c, a) = hostObsInf R f.2 s a := rfl

end Silmaril.Games.Abstract
