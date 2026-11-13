module

public import Silmaril.X86.MemoryModel.Axiomatic.Defs
public import Silmaril.X86.MemoryModel.Tso.Defs
public import Silmaril.X86.MemoryModel.Litmus.Models.Defs

/-!
# Operational x86-TSO against axiomatic x86-TSO: definitions

The general
refinement "every run of the store-buffer machine `Tso.XStep`/`Tso.XFlush` is a consistent
axiomatic x86-TSO candidate execution (`Axiomatic.Exec.Tso`)", for arbitrary finite thread
programs given as `Tso.XEvent` lists.

## Timed candidates (`TimedOk`)

The proof factors through a purely combinatorial notion. A candidate execution `x` together
with `Timing` data — an execution time `e u` for every unit, a memory time `f w` for every
write unit (when its bytes reach memory), and the list `wo` of write units in memory order —
is `TimedOk` when the timing behaves like a store-buffer run: program order is execution order;
coherence is `wo` restricted to each byte; writes reach memory in program order (FIFO) and not
before they execute; no write reaches memory at the time a read executes; a locked write
executes and reaches memory one tick after its read, so nothing reaches memory in between; `mfence` and
locked accesses wait for their thread's earlier writes; every read byte comes from its thread's
newest earlier write still buffered (forwarding) or else from the newest write already in
memory; and (`cells`) two memory units of **one thread** that share a byte have the same
footprint.

`Silmaril.X86.MemoryModel.OpAx.Thms` proves `TimedOk → Exec.Tso` (`tso_of_timedOk`), by two
ranking functions (OSS09's timestamp argument): `ghb` edges increase "execution time for reads,
memory time for writes", and `uniproc` edges increase a lexicographic rank in which a forwarded
read sits just after the memory time of the store it forwards from.

## Program units and operational runs

`progUnits P` are the access units of a program `P` (thread `i` is `P[i]`): event `k` of thread
`i` gives units at program position `2k` (and `2k + 1` for the write half of an `rmw`), each with
the bytes it must read. `Run P init s` is a complete run of `Litmus`'s composition of the
machine (`Litmus.ACfg`/`Litmus.AStep`): every thread runs to its end and every buffer drains.

## The cells condition

`ThreadCells P`: two memory events of one thread have equal or disjoint footprints. It is needed:
`OpAx.Thms` proves that with a 1-byte store followed by a 2-byte load of the same thread
(partial store forwarding) the machine reaches an outcome that no TSO-consistent candidate
over the program's units has (`partialForward_not_explained`).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.OpAx

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Tso (XEvent XState XStep XFlush Byte Mem)

/-! ## Timed candidates -/

/-- Two units share a byte. -/
def Ev.overlap (a b : Ev) : Bool := a.bytes.any b.covers

/-- Timing data for a candidate: execution times `e`, memory times `f` (meaningful for write
units) and the write units in memory order `wo`. -/
structure Timing where
  e : Nat → Nat
  f : Nat → Nat
  wo : List Nat

/-- Where read unit `r` takes byte `y` from, against the timing: from its thread's newest
earlier write of `y` that reaches memory after `r` executes (store forwarding), or, if every
earlier write of its thread to `y` reached memory before `r` executed, from the newest write of
`y` in memory (`none`: no write of `y` is in memory yet, and the thread has none earlier). -/
def RfSpec (x : Exec) (T : Timing) (r y : Nat) : Prop :=
  match x.rf r y with
  | some s =>
    s < x.n ∧ (x.evN s).isW = true ∧ (x.evN s).covers y = true ∧
      ((((x.evN s).tid = (x.evN r).tid ∧ (x.evN s).pos < (x.evN r).pos ∧ T.e r < T.f s) ∧
          ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers y = true →
            (x.evN w).tid = (x.evN r).tid → (x.evN w).pos < (x.evN r).pos → T.e r < T.f w →
              (x.evN w).pos ≤ (x.evN s).pos) ∨
        (T.f s < T.e r ∧
          (∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers y = true → T.f w < T.e r →
            T.f w ≤ T.f s) ∧
          ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers y = true →
            (x.evN w).tid = (x.evN r).tid → (x.evN w).pos < (x.evN r).pos → T.f w < T.e r))
  | none =>
    ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers y = true →
      ¬ T.f w < T.e r ∧ ¬ ((x.evN w).tid = (x.evN r).tid ∧ (x.evN w).pos < (x.evN r).pos)

/-- A candidate with a timing that behaves like a store-buffer run (see the module doc). -/
structure TimedOk (x : Exec) (T : Timing) : Prop where
  uniq : ∀ a < x.n, ∀ b < x.n, (x.evN a).tid = (x.evN b).tid → (x.evN a).pos = (x.evN b).pos →
    a = b
  poE : ∀ a < x.n, ∀ b < x.n, (x.evN a).tid = (x.evN b).tid → (x.evN a).pos < (x.evN b).pos →
    T.e a < T.e b
  coDef : ∀ y, x.co y = T.wo.filter fun w => (x.evN w).covers y
  woW : ∀ w ∈ T.wo, w < x.n ∧ (x.evN w).isW = true
  woSorted : T.wo.Pairwise fun a b => T.f a < T.f b
  eLeF : ∀ w < x.n, (x.evN w).isW = true → T.e w ≤ T.f w
  fifo : ∀ a < x.n, ∀ b < x.n, (x.evN a).isW = true → (x.evN b).isW = true →
    (x.evN a).tid = (x.evN b).tid → (x.evN a).pos < (x.evN b).pos → T.f a < T.f b
  lockedW : ∀ w < x.n, (x.evN w).isW = true → (x.evN w).locked = true → T.f w = T.e w
  drain : ∀ u < x.n, ∀ w < x.n, (x.evN w).isW = true → (x.evN w).tid = (x.evN u).tid →
    (x.evN w).pos < (x.evN u).pos → ((x.evN u).isFence .mfence = true ∨ (x.evN u).isA = true) →
      T.f w < T.e u
  rmwOk : ∀ p ∈ x.rmw, p.1 < x.n ∧ p.2 < x.n ∧ (x.evN p.1).isR = true ∧
    (x.evN p.2).isW = true ∧ (x.evN p.1).tid = (x.evN p.2).tid ∧ T.f p.2 = T.e p.1 + 1
  clash : ∀ r < x.n, ∀ w < x.n, (x.evN r).isR = true → (x.evN w).isW = true → T.f w ≠ T.e r
  rfOk : ∀ r < x.n, (x.evN r).isR = true → ∀ y ∈ (x.evN r).bytes, RfSpec x T r y
  cells : ∀ a < x.n, ∀ b < x.n, (x.evN a).tid = (x.evN b).tid → (x.evN a).isM = true →
    (x.evN b).isM = true → Ev.overlap (x.evN a) (x.evN b) = true →
      (x.evN a).addr = (x.evN b).addr ∧ (x.evN a).size = (x.evN b).size

/-! ## Programs and their units -/

/-- The unit used out of range (`Exec.evN`). -/
def dflt : Ev := { tid := 0, pos := 0, act := .fence .lfence }

/-- The units of event `ev`, the `k`-th of thread `i`, each with the bytes it must read: a load
is a read at position `2k`, a store a write, a locked read-modify-write a locked read at `2k`
and a locked write at `2k + 1`, a fence an `mfence`. -/
def evUnits (i k : Nat) : XEvent Nat → List (Ev × List Byte)
  | .load _ a bs => [({ tid := i, pos := 2 * k, act := .read, addr := a, size := bs.length }, bs)]
  | .store _ a bs =>
    [({ tid := i, pos := 2 * k, act := .write, addr := a, size := bs.length, data := bs }, [])]
  | .rmw _ a old new =>
    [({ tid := i, pos := 2 * k, act := .read, addr := a, size := old.length, locked := true },
        old),
      ({ tid := i, pos := 2 * k + 1, act := .write, addr := a, size := new.length,
          locked := true, data := new }, [])]
  | .fence _ => [({ tid := i, pos := 2 * k, act := .fence .mfence }, [])]

/-- The units of thread `i` running `es`. -/
def threadUnits (i : Nat) (es : List (XEvent Nat)) : List (Ev × List Byte) :=
  (es.mapIdx fun k ev => evUnits i k ev).flatten

/-- The units of a program (thread `i` runs `P[i]`), with the bytes each read must return. -/
def progUnits (P : List (List (XEvent Nat))) : List (Ev × List Byte) :=
  (P.mapIdx threadUnits).flatten

/-- Every event of thread `i` names thread `i`. -/
def ThreadsOk (P : List (List (XEvent Nat))) : Prop :=
  ∀ (i : Nat) (es : List (XEvent Nat)), P[i]? = some es → ∀ ev ∈ es, XEvent.thread ev = i

/-- The footprints (address, size) of an event's memory units. -/
def footOf : XEvent Nat → List (Nat × Nat)
  | .load _ a bs => [(a, bs.length)]
  | .store _ a bs => [(a, bs.length)]
  | .rmw _ a old new => [(a, old.length), (a, new.length)]
  | .fence _ => []

/-- Two footprints share a byte. -/
def footOverlap (p q : Nat × Nat) : Prop := ∃ y, p.1 ≤ y ∧ y < p.1 + p.2 ∧ q.1 ≤ y ∧ y < q.1 + q.2

/-- **Cells within a thread**: any two memory footprints of one thread are equal or disjoint
(no partial store forwarding). Different threads may overlap arbitrarily. -/
def ThreadCells (P : List (List (XEvent Nat))) : Prop :=
  ∀ (i : Nat) (es : List (XEvent Nat)), P[i]? = some es → ∀ ev₁ ∈ es, ∀ ev₂ ∈ es, ∀ p ∈ footOf ev₁, ∀ q ∈ footOf ev₂,
    footOverlap p q → p = q

/-- A complete run of the store-buffer machine on `P` from memory `init` (empty buffers), as
composed in the litmus models: every thread runs to its end, ending in state `s` with every
buffer drained. -/
def Run (P : List (List (XEvent Nat))) (init : Tso.Mem) (s : XState Nat) : Prop :=
  Relation.ReflTransGen Litmus.AStep ⟨P, ⟨init, fun _ => []⟩⟩ ⟨P.map fun _ => [], s⟩ ∧
    ∀ t, s.buffer t = []

/-- What a consistent axiomatic candidate for a complete run of `P` from `init` ending in `s`
must satisfy under model `M`: its units are the program's units (in some order), its reads
return the bytes the events read, `rf` takes each read byte from a write covering it, `co y`
orders exactly the writes covering byte `y`, without repetition, and the coherence-last write
of each byte (else the initial memory) is the final memory. -/
def Explains (M : Exec → Prop) (P : List (List (XEvent Nat))) (init : Tso.Mem) (s : XState Nat)
    (x : Exec) : Prop :=
  ∃ us : List (Ev × List Byte), us.Perm (progUnits P) ∧ x.evs = us.map Prod.fst ∧ M x ∧
    (∀ r < x.n, (x.evN r).isR = true → x.readBytes (fun y => (init y).getD 0) r = (us.getD r (dflt, [])).2) ∧
    (∀ r y w, x.rf r y = some w → w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true) ∧
    (∀ y w, w ∈ x.co y ↔ w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true) ∧
    (∀ y, (x.co y).Nodup) ∧
    ∀ y, s.memory y = match (x.co y).getLast? with
      | none => init y
      | some w => some ((x.evN w).byte y)

/-! ## Side conditions of the converse (`Task.axToOp` in `OpAx.Thms`) -/

/-- Every locked read-modify-write of `P` writes as many bytes as it reads (`Tso.XStep.rmw`
needs this). -/
def RmwSized (P : List (List (XEvent Nat))) : Prop :=
  ∀ (i : Nat) (es : List (XEvent Nat)), P[i]? = some es → ∀ ev ∈ es, ∀ t a old new,
    ev = XEvent.rmw t a old new → new.length = old.length

/-- The initial memory is defined on every byte `P` accesses (the machine's loads need it;
the axiomatic reads use `0` for an undefined byte). -/
def InitCovers (P : List (List (XEvent Nat))) (init : Tso.Mem) : Prop :=
  ∀ (i : Nat) (es : List (XEvent Nat)), P[i]? = some es → ∀ ev ∈ es, ∀ p ∈ footOf ev,
    ∀ y, p.1 ≤ y → y < p.1 + p.2 → (init y).isSome = true

/-- The candidate pairs the two halves of each locked read-modify-write (`Explains` leaves
`x.rmw` free; the converse needs atomicity). -/
def RmwPaired (x : Exec) : Prop :=
  ∀ a < x.n, ∀ b < x.n, (x.evN a).isR = true → (x.evN b).isW = true →
    (x.evN a).locked = true → (x.evN b).locked = true → (x.evN a).tid = (x.evN b).tid →
      (x.evN b).pos = (x.evN a).pos + 1 → (a, b) ∈ x.rmw

end Silmaril.X86.MemoryModel.OpAx
