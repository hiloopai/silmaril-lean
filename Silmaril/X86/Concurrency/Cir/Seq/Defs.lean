module

public import Silmaril.X86.Concurrency.Cir.Defs

/-!
# The single-threaded lift: definitions

The single-threaded lift says
that one thread, on its own, cannot tell the memory models apart: under every model `M` with
`SC ⊑ M ⊑ XL` its behaviours are exactly its **sequential** behaviours on one flat byte memory.
The statement is made at three levels, each one a small sequential semantics:

* **access units** (`uReplay`): the units `units` gives the axiomatic models, replayed in list
  order on a flat memory — a read unit must find its expected bytes, a write unit stores its
  data;
* **memory actions** (`actsReplay`): per-instruction actions (`X86.Litmus.Act`), replayed on
  a flat memory — the sequential meaning of an extracted x86 trace;
* **CIR labels**: `Cir.replay`, the sequential semantics of `Cir.Defs` (`SeqRun`).

`ActOk` lists the shape facts the lift needs of an action (positive access sizes, read and
write byte lists of the access size, `locked` only on read-modify-writes); `Lab.ok` is the CIR
form (read values fit their access, positive sizes, no `spawn`/`join`). Every run of a
thread-free CIR statement with positive sizes has only `ok` labels (`run_ok` in the theorems).

The theorems are in `Silmaril.X86.Concurrency.Cir.Seq.Thms`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Seq

open Silmaril.X86.MemoryModel.Litmus (Byte XAct)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec)

/-! ## Flat byte memories -/

/-- The bytes of `[a, a + sz)`, unmapped bytes read as `0` (as in `AxReach`). -/
def bytesAt (m : Mem) (a sz : Nat) : List Byte := (List.range' a sz).map fun y => (m y).getD 0

/-- Store the bytes `d` at `[a, a + sz)` (a missing byte of `d` stores `0`, as `Ev.byte`). -/
def putBytes (m : Mem) (a sz : Nat) (d : List Byte) : Mem :=
  fun y => if a ≤ y ∧ y < a + sz then some ((d[y - a]?).getD 0) else m y

/-! ## Units -/

/-- Replay one access unit with its expected bytes: a read must find them, a write stores its
data, a fence does nothing. -/
def uStep (m : Mem) (u : Ev × List Byte) : Option Mem :=
  match u.1.act with
  | .read => if bytesAt m u.1.addr u.1.size = u.2 then some m else none
  | .write => some (putBytes m u.1.addr u.1.size u.1.data)
  | .fence _ => some m

/-- Replay a list of units in order. -/
def uReplay (m : Mem) : List (Ev × List Byte) → Option Mem
  | [] => some m
  | u :: us => (uStep m u).bind fun m' => uReplay m' us

/-- The index of the last write unit before position `k` of `evs` that covers byte `y`. -/
def lastW (evs : List Ev) (y : Nat) : Nat → Option Nat
  | 0 => none
  | k + 1 =>
    match evs[k]? with
    | some e => if e.isW && e.covers y then some k else lastW evs y k
    | none => lastW evs y k

/-- The memory after the first `k` units of `evs`, from `m0`: each byte is its last write, or its
initial value. -/
def memAt (evs : List Ev) (m0 : Mem) (k y : Nat) : Option Byte :=
  match lastW evs y k with
  | some i => some ((evs.getD i Silmaril.X86.MemoryModel.Litmus.dummyEv).byte y)
  | none => m0 y

/-! ## Memory actions -/

/-- Replay one litmus action on a flat memory. -/
def actStep (m : Mem) (a : XAct) : Option Mem :=
  match a.ev.kind with
  | .load => if bytesAt m a.ev.addr a.ev.size = a.rd then some m else none
  | .store => some (putBytes m a.ev.addr a.ev.size a.wr)
  | .rmw => if bytesAt m a.ev.addr a.ev.size = a.rd then some (putBytes m a.ev.addr a.ev.size a.wr)
      else none
  | .fence _ => some m

/-- **The sequential semantics of a litmus trace**: replay its actions in order on one flat memory. -/
def actsReplay (m : Mem) : List XAct → Option Mem
  | [] => some m
  | a :: as => (actStep m a).bind fun m' => actsReplay m' as

/-- The shape facts the lift needs of an action: memory accesses have a positive size and read
and write byte lists of that size, and only read-modify-writes are `locked`. -/
def ActOk (a : XAct) : Prop :=
  (a.ev.locked = true → a.ev.kind = .rmw) ∧
  match a.ev.kind with
  | .load => 0 < a.ev.size ∧ a.rd.length = a.ev.size
  | .store => 0 < a.ev.size ∧ a.wr.length = a.ev.size
  | .rmw => 0 < a.ev.size ∧ a.rd.length = a.ev.size ∧ a.wr.length = a.ev.size
  | .fence _ => True

/-- `ActOk` is decidable, so it can be checked per test by `decide`. -/
instance : DecidablePred ActOk := fun a => by
  unfold ActOk; cases a.ev.kind <;> infer_instance

/-! ## CIR labels -/

/-- A CIR label the lift accepts: the values it reads fit their access, its accesses have a
positive size, and it is not a `spawn` or `join` (whose control events have no sequential
meaning). -/
def _root_.Silmaril.X86.Concurrency.Cir.Lab.ok : Lab → Prop
  | .rd _ _ _ sz v => 0 < sz ∧ v < 2 ^ (8 * sz)
  | .wr _ _ _ sz _ => 0 < sz
  | .rmw _ _ sz o _ => 0 < sz ∧ o < 2 ^ (8 * sz)
  | .fence _ => True
  | .fwait _ _ seen r => seen < 2 ^ 32 ∧ r < 2 ^ 8
  | .fwake _ _ q => q < 2 ^ 8
  | .fblock _ _ => False
  | .spawn _ => False
  | .join _ => False
  | .blk _ ins outs _ => (∀ c ∈ ins, 0 < c.2.1 ∧ c.2.2 < 2 ^ (8 * c.2.1)) ∧ ∀ c ∈ outs, 0 < c.2.1

/-- The one-thread program of a statement. -/
def solo (locs : List Silmaril.X86.MemoryModel.Litmus.Loc) (s : Stmt) : Prog := ⟨locs, [⟨s, false⟩]⟩

/-- The final state of a one-thread sequential run: thread `0` has `rs`, every other thread
zero registers, and the memory is `m`. -/
def soloFinal (rs : Regs) (m : Mem) : Silmaril.X86.MemoryModel.Litmus.Final :=
  ⟨fun i r => if i = 0 then rs r else 0, m⟩

/-! ## One thread under a memory model, from any memory -/

/-- An litmus trace with the actions `acts` (one step; the cores are irrelevant to the units). -/
def trOf (acts : List XAct) : Silmaril.X86.MemoryModel.Litmus.XTrace :=
  ⟨[⟨acts, coreOf Regs.zero⟩], coreOf Regs.zero⟩

/-- The final memory of a candidate from `m0`: a written byte is its coherence-last write, any
other byte its initial value (as ``finalAx``). -/
def finalMem (m0 : Mem) (x : Exec) : Mem := fun y =>
  if Silmaril.X86.MemoryModel.Litmus.writtenByte x y then
    some (x.finalByte (fun y => (m0 y).getD 0) y) else m0 y

/-- **One thread under the axiomatic model `M`, from the memory `m0`**: the action list `acts`
of one thread has a well-formed candidate over its units (`units`, tearable accesses
split), whose reads return the actions' bytes, consistent under `M`, with final memory `m`.
This is `AxReach` for one fixed trace and an arbitrary initial memory. -/
def OneSem (M : Exec → Prop) (m0 : Mem) (acts : List XAct) (m : Mem) : Prop :=
  ∃ x : Exec, x.evs = (Silmaril.X86.MemoryModel.Litmus.units [trOf acts]).map Prod.fst ∧
    x.rmw = Silmaril.X86.MemoryModel.Litmus.rmwPairs x.evs ∧ x.Wf = true ∧
    (∀ r < x.n, (x.evN r).isR = true → x.readBytes (fun y => (m0 y).getD 0) r =
      ((Silmaril.X86.MemoryModel.Litmus.units [trOf acts]).map Prod.snd).getD r []) ∧
    M x ∧ m = finalMem m0 x

end Silmaril.X86.Concurrency.Cir.Seq
