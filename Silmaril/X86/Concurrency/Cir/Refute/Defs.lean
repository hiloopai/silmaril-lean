module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs
public import Silmaril.X86.MemoryModel.Xl.Defs

/-!
# Refuting bad outcomes by forced cycles, without enumerating coherence

The axiomatic
enumerator (`Test.axJudge`) tries, for every choice of one trace per thread, every `rf` choice
and **every coherence order of every cell**, and judges each candidate. For a channel that sends
three values, the payload cell alone has `3! = 6` orders and the flags more, so the product is
far too large for a kernel `decide`.

This module gives a cheaper check for **safety** (forbidden outcomes) only. For one choice of
traces it enumerates only the `rf` source of the **first byte** of each read (the *key byte*),
which the read's expected bytes usually fix uniquely, and derives edges that every XL-consistent
well-formed candidate with these sources must have:

* `ppoXl` between two units (static: it depends only on the units);
* `rfe` from the key-byte source to the read, when the threads differ;
* `fr` from a read to every write of its key byte that is **forced** after the read's source:
  every write when the source is the initial value, and every later write of the same thread
  when the source is a write (`coF`): `po-loc` plus XL's `uniproc` force that coherence order.

All these edges are edges of `ghbXl`. If they contain a cycle (`hasCycle`), no XL-consistent
candidate has these sources (`Cir.Refute.refuteCombo_sound`), and so neither has a TSO- or
SC-consistent one. Coherence orders are never enumerated.

`safeCheck t T good`: for every choice of traces, either the condition `good` holds of the
final state (registers from the traces; each byte the condition reads has at most one writer,
so its final value is known without `co`), or the choice is refuted. Then every behaviour under
XL, TSO and SC satisfies `good` (`Cir.Refute.safe_of_check`).

The check is sound but not complete: a choice it cannot refute makes it fail, and the outcome
may still be forbidden. Allowed outcomes are shown by explicit witness candidates instead.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Refute

open Silmaril.X86.MemoryModel.Litmus (Test XTrace units seqL Final finalOf dummyEv Cond Atom Byte)
open Silmaril.X86.MemoryModel.Axiomatic (Ev)

/-- The unit at an index (the dummy fence out of range, as `Exec.evN`). -/
def evAt (evs : List Ev) (i : Nat) : Ev := evs.getD i dummyEv

/-- `ppoXl` between two units: same thread, earlier, `W→W` or `R→M`, neither a weak store. -/
def ppoE (a b : Ev) : Bool :=
  a.tid == b.tid && decide (a.pos < b.pos) && ((a.isW && b.isW) || (a.isR && b.isM)) &&
    !a.weak && !b.weak

/-- The key byte of a unit: its first byte. -/
def key (evs : List Ev) (r : Nat) : Nat := (evAt evs r).addr

/-- The expected key byte of read `r`. -/
def expB (exps : List (List Byte)) (r : Nat) : Byte := ((exps.getD r []).head?).getD 0

/-- The possible sources of read `r`'s key byte: the initial value if it matches, and every
write covering the byte with the expected value. -/
def srcs (t : Test) (evs : List Ev) (exps : List (List Byte)) (r : Nat) : List (Option Nat) :=
  (if t.initB (key evs r) == expB exps r then [none] else []) ++
    ((List.range evs.length).filter fun w =>
      (evAt evs w).isW && (evAt evs w).covers (key evs r) &&
        (evAt evs w).byte (key evs r) == expB exps r).map some

/-- The read units. -/
def readIdx (evs : List Ev) : List Nat := (List.range evs.length).filter fun r => (evAt evs r).isR

/-- `v` is forced before `w` in the coherence order of byte `y`: both write it, in one thread,
`v` first. -/
def coF (evs : List Ev) (y v w : Nat) : Bool :=
  (evAt evs v).isW && (evAt evs w).isW && (evAt evs v).covers y && (evAt evs w).covers y &&
    (evAt evs v).tid == (evAt evs w).tid && decide ((evAt evs v).pos < (evAt evs w).pos)

/-- The `rfe` and `fr` edges of one read with key-byte source `s`. -/
def readEdges (evs : List Ev) (r : Nat) (s : Option Nat) : List (Nat × Nat) :=
  (match s with
    | some w => if (evAt evs w).tid != (evAt evs r).tid then [(w, r)] else []
    | none => []) ++
  ((List.range evs.length).filter fun w =>
    (evAt evs w).isW && (evAt evs w).covers (key evs r) &&
      match s with
      | none => true
      | some v => coF evs (key evs r) v w).map (r, ·)

/-- The static `ppoXl` edges. -/
def ppoEdges (evs : List Ev) : List (Nat × Nat) :=
  (List.range evs.length).flatMap fun a =>
    ((List.range evs.length).filter fun b => ppoE (evAt evs a) (evAt evs b)).map (a, ·)

/-- **The forced edges** of a choice of key-byte sources (read, source). -/
def edges (evs : List Ev) (σ : List (Nat × Option Nat)) : List (Nat × Nat) :=
  ppoEdges evs ++ σ.flatMap fun p => readEdges evs p.1 p.2

/-! ## Cycles -/

/-- The successors of a node. -/
def succs (E : List (Nat × Nat)) (a : Nat) : List Nat :=
  E.filterMap fun p => if p.1 == a then some p.2 else none

/-- Add the elements of `l` not yet in `S`. -/
def addNew (S : List Nat) (l : List Nat) : List Nat :=
  l.foldl (fun acc b => if acc.contains b then acc else acc ++ [b]) S

/-- Grow a set of nodes by successors, at most `k` times, stopping at a fixpoint. -/
def grow (E : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, S => S
  | k + 1, S =>
    let S' := addNew S (S.flatMap (succs E))
    if S'.length = S.length then S else grow E k S'

/-- Some node of `starts` reaches itself (searching at most `n` rounds). Every cycle of the
forced edges passes through a read (`ppoXl` alone is acyclic), so the reads are the starts. -/
def hasCycle (E : List (Nat × Nat)) (n : Nat) (starts : List Nat) : Bool :=
  starts.any fun a => (grow E n (succs E a)).contains a

/-! ## The checks -/

/-- **Refute one choice of traces**: every choice of key-byte sources gives a cycle. -/
def refuteCombo (t : Test) (trs : List XTrace) : Bool :=
  let evs := (units trs).map Prod.fst
  let exps := (units trs).map Prod.snd
  let rs := readIdx evs
  (seqL (rs.map (srcs t evs exps))).all fun c => hasCycle (edges evs (rs.zip c)) evs.length rs

/-- The write units covering byte `y`. -/
def writers (evs : List Ev) (y : Nat) : List Nat :=
  (List.range evs.length).filter fun w => (evAt evs w).isW && (evAt evs w).covers y

/-- The final value of byte `y` when it is known without coherence: its initial value if no
unit writes it, the one writer's byte if exactly one does, unknown (`none`) otherwise. -/
def guess (t : Test) (evs : List Ev) (y : Nat) : Option (Option Byte) :=
  match writers evs y with
  | [] => some (t.initMem y)
  | [w] => some (some ((evAt evs w).byte y))
  | _ => none

/-- The memory bytes a condition reads. -/
def condBytes : Cond → List Nat
  | .tt => []
  | .atom (.reg ..) => []
  | .atom (.mem a n _) => List.range' a n
  | .not p => condBytes p
  | .and p q | .or p q => condBytes p ++ condBytes q

/-- The condition holds of every final state of the choice: its bytes are known, and it holds
with the traces' registers. -/
def goodCombo (t : Test) (good : Cond) (trs : List XTrace) : Bool :=
  let evs := (units trs).map Prod.fst
  (condBytes good).all (fun y => (guess t evs y).isSome) &&
    good.eval (finalOf trs fun y => (guess t evs y).getD none)

/-- **The safety check**: every choice of traces satisfies `good` or is refuted. -/
def safeCheck (t : Test) (T : List (List XTrace)) (good : Cond) : Bool :=
  (seqL T).all fun trs => goodCombo t good trs || refuteCombo t trs

/-! ## Witnesses -/

open Silmaril.X86.MemoryModel.Litmus (mkExec rmwPairs readsOkB finalAx) in
/-- **An explicit SC witness**: the traces of index `ks` (one per thread), the candidate of the
per-unit `rf` sources `rfA` and the per-cell coherence orders `coA` is well formed, its reads
return the traces' bytes, it is SC-consistent, and its final state satisfies `w`. -/
def witnessCheck (t : Test) (T : List (List XTrace)) (ks : List Nat)
    (rfA : List (Nat × Option Nat)) (coA : List ((Nat × Nat) × List Nat)) (w : Cond) : Bool :=
  match (T.zip ks).mapM (fun p => p.1[p.2]?) with
  | some trs =>
    let evs := (units trs).map Prod.fst
    let x := mkExec evs (rmwPairs evs) rfA coA
    T.length == ks.length && x.Wf && readsOkB t x ((units trs).map Prod.snd) && decide x.Sc &&
      w.eval (finalAx t trs x)
  | none => false

open Silmaril.X86.MemoryModel.Litmus (cellsOf writesIn) in
/-- A witness whose `rf` takes each read from the first key-byte source and whose coherence
orders are the unit order (program order for single-writer cells). Everything is checked by
`witnessCheck`; the choice is only a heuristic. -/
def witnessAuto (t : Test) (T : List (List XTrace)) (ks : List Nat) (w : Cond) : Bool :=
  match (T.zip ks).mapM (fun p => p.1[p.2]?) with
  | some trs =>
    let evs := (units trs).map Prod.fst
    let exps := (units trs).map Prod.snd
    let rfA := (readIdx evs).map fun r => (r, ((srcs t evs exps r).head?).getD none)
    let coA := (cellsOf evs).map fun c => (c, writesIn evs c)
    witnessCheck t T ks rfA coA w
  | none => false

end Silmaril.X86.Concurrency.Cir.Refute
