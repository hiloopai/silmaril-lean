module

public import Mathlib.Logic.Relation
public import Mathlib.Logic.Function.Basic
public import Silmaril.Raw.X86.MemoryModel.TSOFence

/-!
# x86-TSO store-buffer models: definitions

Two layers.

* **Word-granular.** A FIFO store-buffer TSO over abstract addresses and values
  (`Silmaril/Raw/X86/MemoryModel/{Execution,SC,TSO,TSOFence}.lean`, namespaces
  `Silmaril.Memory{,.SC,.TSO}`). Each store writes one value at one abstract address. `State`,
  `Step`, `WeakStep`, `Flush` and the SC heap step are re-exported here as abbreviations.
* **Byte-granular, mixed-size.** `XState` has a partial byte memory `Nat → Option Byte`
  and a per-thread FIFO of `(address, bytes)` entries, oldest first. A load of `n` bytes reads
  each byte from the newest buffered entry of its own thread that covers it, falling back to
  memory (`viewMem`/`readView`). A store enqueues one entry. `XFlush` moves the oldest entry of
  one thread to memory, **whole span at once**. A locked read-modify-write (`rmw`) and `mfence`
  require the issuing thread's buffer to be empty. The `rmw` reads and writes memory in one
  transition.

Known over-approximation of atomicity: flushing a whole entry gives
every store single-copy atomicity, including misaligned and line-crossing stores, which is
stronger than hardware. Not modelled:
non-temporal stores and `sfence`, split locks, memory types, faults on unmapped bytes (a load
of an unmapped byte is simply not enabled, while a store, once flushed, *maps* the bytes it
writes, since `writeMem` ignores whether they were mapped), address wrap-around (addresses are
unbounded `Nat`s), and fairness.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Tso

universe u

/-! ## The word-granular model -/

/-- Observable memory events `load`/`store`/`fence` (with the loaded value). -/
abbrev Event (Tid Addr Val : Type u) := Silmaril.Memory.Event Tid Addr Val

/-- Finite labelled executions of a transition relation. -/
abbrev Execution {S : Type u} {L : Type u} (step : S → L → S → Prop) : S → List L → S → Prop :=
  Silmaril.Memory.Execution step

/-- Program-order-preserving binary parallel composition. -/
abbrev Concurrent {S : Type u} {L : Type u} (step : S → L → S → Prop) (initial : S)
    (left right : List L) : Prop :=
  Silmaril.Memory.Concurrent step initial left right

/-- Word-granular TSO state: memory plus per-thread FIFO buffers. -/
abbrev State (Tid Addr Val : Type u) := Silmaril.Memory.TSO.State Tid Addr Val

section Word
variable {Tid Addr Val : Type u} [DecidableEq Tid] [DecidableEq Addr]

/-- Observable TSO step (no implicit commits). -/
abbrev Step : State Tid Addr Val → Event Tid Addr Val → State Tid Addr Val → Prop :=
  Silmaril.Memory.TSO.Step

/-- Internal propagation of the oldest buffered store. -/
abbrev Flush : State Tid Addr Val → State Tid Addr Val → Prop := Silmaril.Memory.TSO.Flush

/-- Observable step surrounded by finite flushes. -/
abbrev WeakStep : State Tid Addr Val → Event Tid Addr Val → State Tid Addr Val → Prop :=
  Silmaril.Memory.TSO.WeakStep

end Word

/-! ## Byte-granular mixed-size x86-TSO -/

/-- A byte. -/
abbrev Byte := BitVec 8

/-- Partial byte memory; `none` is an unmapped byte. -/
abbrev Mem := Nat → Option Byte

/-- Byte-level observable events. Loads, and the read half of an `rmw`, carry the bytes read. -/
inductive XEvent (Tid : Type) where
  | load (thread : Tid) (addr : Nat) (bytes : List Byte)
  | store (thread : Tid) (addr : Nat) (bytes : List Byte)
  | rmw (thread : Tid) (addr : Nat) (old new : List Byte)
  | fence (thread : Tid)
  deriving DecidableEq, Repr

/-- The issuing thread of an event. -/
def XEvent.thread {Tid : Type} : XEvent Tid → Tid
  | .load t _ _ => t
  | .store t _ _ => t
  | .rmw t _ _ _ => t
  | .fence t => t

/-- Byte-granular TSO state. Buffers are oldest first. -/
structure XState (Tid : Type) where
  memory : Mem
  buffer : Tid → List (Nat × List Byte)

/-- The byte that the span `bs` at `a` holds at address `x`, if it covers `x`. -/
def entryByte (a : Nat) (bs : List Byte) (x : Nat) : Option Byte :=
  if a ≤ x then bs[x - a]? else none

/-- Write the span `bs` at `a`. -/
def writeMem (m : Mem) (a : Nat) (bs : List Byte) : Mem :=
  fun x => (entryByte a bs x).or (m x)

/-- Read `n` consecutive bytes starting at `a`; `none` if any byte is unmapped. -/
def readMem (m : Mem) : Nat → Nat → Option (List Byte)
  | _, 0 => some []
  | a, n + 1 =>
      match m a, readMem m (a + 1) n with
      | some b, some bs => some (b :: bs)
      | _, _ => none

/-- Store forwarding for one byte: the newest buffered entry covering `x` wins. -/
def readBufByte (x : Nat) : List (Nat × List Byte) → Option Byte
  | [] => none
  | (a, bs) :: rest => (readBufByte x rest).or (entryByte a bs x)

/-- Thread `t`'s view of memory: its own buffer overlaid on shared memory, per byte. -/
def viewMem {Tid : Type} (s : XState Tid) (t : Tid) : Mem :=
  fun x => (readBufByte x (s.buffer t)).or (s.memory x)

/-- What a load of `n` bytes at `a` by thread `t` returns. -/
def readView {Tid : Type} (s : XState Tid) (t : Tid) (a n : Nat) : Option (List Byte) :=
  readMem (viewMem s t) a n

/-- Append an entry to thread `t`'s buffer. -/
def enqueue {Tid : Type} [DecidableEq Tid] (s : XState Tid) (t : Tid) (a : Nat)
    (bs : List Byte) : XState Tid :=
  { s with buffer := Function.update s.buffer t (s.buffer t ++ [(a, bs)]) }

/-- All buffers empty, over the given memory. -/
def xembed {Tid : Type} (m : Mem) : XState Tid := ⟨m, fun _ => []⟩

section Byte
variable {Tid : Type} [DecidableEq Tid]

/-- Observable byte-granular TSO steps. Instructions never commit buffered stores. -/
inductive XStep : XState Tid → XEvent Tid → XState Tid → Prop
  | load (s : XState Tid) (t : Tid) (a : Nat) (bs : List Byte)
      (h : readView s t a bs.length = some bs) : XStep s (.load t a bs) s
  | store (s : XState Tid) (t : Tid) (a : Nat) (bs : List Byte) :
      XStep s (.store t a bs) (enqueue s t a bs)
  | rmw (s : XState Tid) (t : Tid) (a : Nat) (old new : List Byte)
      (empty : s.buffer t = []) (h : readMem s.memory a old.length = some old)
      (len : new.length = old.length) :
      XStep s (.rmw t a old new) { s with memory := writeMem s.memory a new }
  | fence (s : XState Tid) (t : Tid) (empty : s.buffer t = []) : XStep s (.fence t) s

/-- Internal propagation: the oldest entry of one thread reaches memory, whole span at once. -/
inductive XFlush : XState Tid → XState Tid → Prop
  | head (s : XState Tid) (t : Tid) (a : Nat) (bs : List Byte) (rest : List (Nat × List Byte))
      (oldest : s.buffer t = (a, bs) :: rest) :
      XFlush s ⟨writeMem s.memory a bs, Function.update s.buffer t rest⟩

/-- Finitely many flushes. -/
abbrev XFlushes : XState Tid → XState Tid → Prop := Relation.ReflTransGen XFlush

/-- An observable step surrounded by any finite number of flushes. -/
def XWeakStep (s : XState Tid) (e : XEvent Tid) (s' : XState Tid) : Prop :=
  ∃ before after, XFlushes s before ∧ XStep before e after ∧ XFlushes after s'

end Byte

/-- Byte-granular sequential consistency: every access takes effect in memory at once. -/
inductive SCStep {Tid : Type} : Mem → XEvent Tid → Mem → Prop
  | load (m : Mem) (t : Tid) (a : Nat) (bs : List Byte)
      (h : readMem m a bs.length = some bs) : SCStep m (.load t a bs) m
  | store (m : Mem) (t : Tid) (a : Nat) (bs : List Byte) :
      SCStep m (.store t a bs) (writeMem m a bs)
  | rmw (m : Mem) (t : Tid) (a : Nat) (old new : List Byte)
      (h : readMem m a old.length = some old) (len : new.length = old.length) :
      SCStep m (.rmw t a old new) (writeMem m a new)
  | fence (m : Mem) (t : Tid) : SCStep m (.fence t) m

/-! ## Litmus programs (threads `false`/`true`, `x` at address 0, `y` at address 1) -/

namespace Litmus

/-- Every byte mapped and zero. -/
def zeroMem : Mem := fun _ => some 0

/-- Zero memory, empty buffers. -/
def xinitial : XState Bool := xembed zeroMem

/-- SB, thread `false`: `x := 1; r0 := y` with `r0 = 0`. -/
def sbLeft : List (XEvent Bool) := [.store false 0 [1], .load false 1 [0]]
/-- SB, thread `true`: `y := 1; r1 := x` with `r1 = 0`. -/
def sbRight : List (XEvent Bool) := [.store true 1 [1], .load true 0 [0]]

/-- SB+mfence, thread `false`: `x := 1; mfence; r0 := y` with `r0 = 0`. -/
def sbFenceLeft : List (XEvent Bool) := [.store false 0 [1], .fence false, .load false 1 [0]]
/-- SB+mfence, thread `true`: `y := 1; mfence; r1 := x` with `r1 = 0`. -/
def sbFenceRight : List (XEvent Bool) := [.store true 1 [1], .fence true, .load true 0 [0]]

end Litmus

end Silmaril.X86.MemoryModel.Tso
