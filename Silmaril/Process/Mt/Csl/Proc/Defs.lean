module

public import Silmaril.Process.Mt.Csl.Defs
public import Silmaril.Process.Mt.Defs

/-!
# The decomposition on the multithreaded process model

The thread-modular system of `Silmaril.Process.Mt.Csl`, instantiated on the multithreaded
process `MtStep U sc P base` (`Silmaril.Process.Mt`, sequential consistency): `procT U P base`
is a thread machine whose steps are the process's, one thread at a time. `Proc/Thms` proves
that every process step is a run of `procT` (`step_reach`), so the decomposition's adequacy
holds of the process (`mt_adequacy`).

## Shared state as cells

The shared state `Glob γ` (memory, the primitives' lock table, the library ghost, the
multithreaded-mode bit, the exit status) is read cell by cell (`store`) at locations `Loc`:
each memory byte, the mapping list, each lock's owner and depth, the ghost, the mode bit and
the status. So a thread or the invariant can **own a lock's abstract state or the ghost** as it
owns bytes: a lock invariant owns the lock cell and, while it is free, the protected bytes.

## The thread machine `procT U P base`

Thread states are the process's thread records (`TRec`: running, waiting on a futex word, or
exited; with the `clear_child_tid` address). Every step needs a live process (no exit status,
library not ended).

* **plain** steps (`PPlain`): an instruction (`UOut.step`). Its footprint is the bytes of its
  access list (every byte when the list is unknown, `none`);
* **atomic** steps (`PAtom`): a library-contract step, a trusted primitive (one step of its
  spec), `gettid`, `set_tid_address`, `futex` wait (block or `-EAGAIN`), `futex` wake (returns
  any count up to `n`; the woken waiters are separate `wake` steps), a waiter's wake-up,
  `exit` (clearing the `clear_child_tid` word, or setting the status to none or the code),
  `exit_group`, and a base system call;
* `clone` (`PSpawn`): `pthread_create`'s `clone`, the child at a fresh id `0 < u < pidMax`;
* finished: exited.

Faults: a plain step that is `stop`; a primitive call outside its precondition (`MtFault`).

The thread machine over-approximates the process where the process reads other threads'
records: a `futex` wake may report any count up to `n`, and `exit` may set the status (ending
the process) or not, whether or not other threads live. Safety proved of `procT` therefore
holds of the process.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Csl.Proc

open Silmaril.Process.Mt
open Silmaril.X86 (Word)
open Silmaril.X86.MemEvent (Event)

/-- **The shared state** of the process. -/
structure Glob (γ : Type) where
  mem : Memory
  ps : PrimSt
  g : γ
  mt : Bool
  status : Option Nat

/-- Locations of the shared state. -/
inductive Loc where
  | byte (a : Nat)
  | regions
  | lock (a : Nat)
  | ghost
  | mode
  | status

/-- Values at locations. -/
inductive Val (γ : Type) where
  | byte (b : Byte)
  | regions (rs : List Region)
  | lock (o : Option (Nat × Nat))
  | ghost (g : γ)
  | mode (b : Bool)
  | status (o : Option Nat)

/-- **The shared state read cell by cell.** -/
def store (γ : Type) : Store (Glob γ) Loc (Val γ) where
  get G
    | .byte a => (G.mem.bytes.get? a).map .byte
    | .regions => some (.regions G.mem.regions)
    | .lock a => some (.lock (G.ps.locks a))
    | .ghost => some (.ghost G.g)
    | .mode => some (.mode G.mt)
    | .status => some (.status G.status)

variable {γ : Type}

/-- The process is running. -/
def Glob.Live (U : UIsa γ) (G : Glob γ) : Prop := G.status = none ∧ U.ended G.g = none

/-- What primitives see. -/
def Glob.sh (G : Glob γ) : Sh γ := ⟨G.mem, G.ps, G.g, G.mt⟩

/-- The locations an access list touches (every byte if it is unknown). -/
def accLocs : Option (List Event) → Loc → Prop
  | none, .byte _ => True
  | some es, .byte a => ∃ e ∈ es, e.Covers a
  | _, _ => False

section
variable (U : UIsa γ) (P : PrimTable γ) (base : Base γ) (t : Nat)

/-- **Plain steps** of thread `t`. -/
inductive PPlain : TRec U.St → Glob γ → TRec U.St → Glob γ → Prop
  | user {r : TRec U.St} {G : Glob γ} {s s' : U.St} {es : Option (List Event)} {m : Memory}
      (hr : r.st = .run s) (hs : U.step t s G.mem G.g (.step s' es m)) :
      PPlain r G { r with st := .run s' } { G with mem := m }

/-- **Atomic steps** of thread `t`. -/
inductive PAtom : TRec U.St → Glob γ → TRec U.St → Glob γ → Prop
  | lib {r : TRec U.St} {G : Glob γ} {s s' : U.St} {m : Memory} {g' : γ} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.lib s' m g')) :
      PAtom r G { r with st := .run s' } { G with mem := m, g := g' }
  | prim {r : TRec U.St} {G : Glob γ} {s : U.St} {p : Nat} {args : List Word} {k : Word → U.St}
      {sp : Mt.PrimSpec γ} {ret : Word} {sh2 : Sh γ} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.prim p args k)) (hp : P p = some sp)
      (hpre : sp.pre t args G.sh) (hpost : sp.post t args G.sh ret sh2) :
      PAtom r G { r with st := .run (k ret) } { G with mem := sh2.mem, ps := sh2.ps, g := sh2.g }
  | gettid {r : TRec U.St} {G : Glob γ} {s : U.St} {args : List Word} {k : Word → U.St}
      {ch : U.St} (hr : r.st = .run s) (hs : U.step t s G.mem G.g (.sys nrGettid args k ch)) :
      PAtom r G { r with st := .run (k (BitVec.ofNat 64 t)) } G
  | setTid {r : TRec U.St} {G : Glob γ} {s : U.St} {a : Word} {args : List Word}
      {k : Word → U.St} {ch : U.St} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nrSetTid (a :: args) k ch)) :
      PAtom r G { st := .run (k (BitVec.ofNat 64 t)), ctid := some a.toNat } G
  | futexBlock {r : TRec U.St} {G : Glob γ} {s : U.St} {a op v : Word} {args : List Word}
      {k : Word → U.St} {ch : U.St} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nrFutex (a :: op :: v :: args) k ch)) (hop : WaitOp op)
      (hal : a.toNat % 4 = 0) (hw : G.mem.readBytes a.toNat 4 = some (le 4 v)) :
      PAtom r G { r with st := .wait a.toNat k } G
  | futexAgain {r : TRec U.St} {G : Glob γ} {s : U.St} {a op v : Word} {args : List Word}
      {k : Word → U.St} {ch : U.St} {w : List Byte} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nrFutex (a :: op :: v :: args) k ch)) (hop : WaitOp op)
      (hal : a.toNat % 4 = 0) (hw : G.mem.readBytes a.toNat 4 = some w) (hne : w ≠ le 4 v) :
      PAtom r G { r with st := .run (k errAgain) } G
  /-- `futex` wake: any count up to `n` (the woken waiters take their own `wake` steps). -/
  | futexWake {r : TRec U.St} {G : Glob γ} {s : U.St} {a op n : Word} {args : List Word}
      {k : Word → U.St} {ch : U.St} {c : Nat} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nrFutex (a :: op :: n :: args) k ch)) (hop : WakeOp op)
      (hal : a.toNat % 4 = 0) (hc : c ≤ n.toNat) :
      PAtom r G { r with st := .run (k (BitVec.ofNat 64 c)) } G
  /-- A waiter wakes up (woken, or spuriously). -/
  | wake {r : TRec U.St} {G : Glob γ} {a : Nat} {k : Word → U.St} (hr : r.st = .wait a k) :
      PAtom r G { r with st := .run (k 0) } G
  | exitClear {r : TRec U.St} {G : Glob γ} {s : U.St} {code : Word} {args : List Word}
      {k : Word → U.St} {ch : U.St} {a : Nat} {m' : Memory} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nrExit (code :: args) k ch)) (hct : r.ctid = some a)
      (hmap : G.mem.writeBytes a (le 4 0) = some m') :
      PAtom r G { r with st := .exited } { G with mem := m' }
  | exitPlain {r : TRec U.St} {G : Glob γ} {s : U.St} {code : Word} {args : List Word}
      {k : Word → U.St} {ch : U.St} {st' : Option Nat} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nrExit (code :: args) k ch))
      (hst : st' = none ∨ st' = some (code.toNat % 256)) :
      PAtom r G { r with st := .exited } { G with status := st' }
  | exitGroup {r : TRec U.St} {G : Glob γ} {s : U.St} {code : Word} {args : List Word}
      {k : Word → U.St} {ch : U.St} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nrExitGroup (code :: args) k ch)) :
      PAtom r G r { G with status := some (code.toNat % 256) }
  | base {r : TRec U.St} {G : Glob γ} {s : U.St} {nr : Nat} {args : List Word}
      {k : Word → U.St} {ch : U.St} {ret : Word} {m' : Memory} {g' : γ} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nr args k ch)) (hn : ¬ threadNr nr)
      (hb : base nr t args G.mem G.g ret m' g') :
      PAtom r G { r with st := .run (k ret) } { G with mem := m', g := g' }

/-- **`clone`** by thread `t` creating thread `u`. -/
inductive PSpawn (u : Nat) : TRec U.St → Glob γ → TRec U.St → TRec U.St → Glob γ → Prop
  | clone {r : TRec U.St} {G : Glob γ} {s : U.St} {fl sp ptid ctid tls : Word}
      {args : List Word} {k : Word → U.St} {ch : U.St} {m' : Memory} (hr : r.st = .run s)
      (hs : U.step t s G.mem G.g (.sys nrClone (fl :: sp :: ptid :: ctid :: tls :: args) k ch))
      (hf : CloneOk fl) (h0 : 0 < u) (hmax : u < pidMax)
      (hpt : G.mem.writeBytes ptid.toNat (le 4 (BitVec.ofNat 64 u)) = some m') :
      PSpawn u r G { r with st := .run (k (BitVec.ofNat 64 u)) }
        { st := .run ch, ctid := some ctid.toNat } { G with mem := m', mt := true }

end

/-- **The process's threads as a thread machine** (see the module documentation). -/
def procT (U : UIsa γ) (P : PrimTable γ) (base : Base γ) : TIsa (store γ) where
  St := TRec U.St
  step t r G r' G' := G.Live U ∧ PPlain U t r G r' G'
  fault t r G := G.Live U ∧ ∃ s, r.st = .run s ∧ U.step t s G.mem G.g .stop
  fp t r G l := ∃ s s' es m, r.st = .run s ∧ U.step t s G.mem G.g (.step s' es m) ∧ accLocs es l
  atom t r G r' G' := G.Live U ∧ PAtom U P base t r G r' G'
  afault t r G := G.Live U ∧ ∃ s p args k, r.st = .run s ∧ U.step t s G.mem G.g (.prim p args k) ∧
    ∀ sp, P p = some sp → ¬ sp.pre t args G.sh
  spawn t u r G r₁ r₂ G' := G.Live U ∧ PSpawn U t u r G r₁ r₂ G'
  done r := r.st.isExited = true

/-- A process configuration (SC) as a configuration of the thread machine. -/
def enc {U : UIsa γ} (P : PrimTable γ) (base : Base γ) (C : MtCfg U.St γ sc.S) :
    Cfg (procT U P base) :=
  ⟨C.th, ⟨C.ms, C.ps, C.g, C.mt, C.status⟩⟩

/-! ## The x86-TSO process as a concrete model (statement) -/

/-- **Plain steps are local**: a plain step with a known access list `es` writes exactly the
bytes of its write events (the memory after is the memory before with `writesOf es` applied),
keeps the mapping, and behaves the same on every memory that agrees on the mapping and on the
bytes `es` touches. (What `MemEvent`'s `Local` executors give per instruction.) -/
def LocalAcc (U : UIsa γ) : Prop :=
  ∀ t s m g s' es m₁, U.step t s m g (.step s' (some es) m₁) →
    m₁ = overlay m (writesOf es m₁) ∧
    ∀ m₂ : Memory, m₂.regions = m.regions →
      (∀ e ∈ es, ∀ i < e.size, m₂.bytes.get? (e.addr + i) = m.bytes.get? (e.addr + i)) →
      U.step t s m₂ g (.step s' (some es) (overlay m₂ (writesOf es m₁)))

/-- A TSO process configuration stands for a thread-machine configuration: the same threads,
primitive state, ghost, mode and status, and the memory with every pending write installed
(each byte from the one thread whose view differs from memory there, if any). -/
def tsoAbs (U : UIsa γ) (P : PrimTable γ) (base : Base γ) (c : MtCfg U.St γ tso.S)
    (C : Cfg (procT U P base)) : Prop :=
  C.th = c.th ∧ C.mem.ps = c.ps ∧ C.mem.g = c.g ∧ C.mem.mt = c.mt ∧ C.mem.status = c.status ∧
  C.mem.mem.regions = c.ms.mem.regions ∧
  ∀ a, ∃ t, C.mem.mem.bytes.get? a = (tso.view c.ms t).bytes.get? a ∧
    ∀ u, u ≠ t → (tso.view c.ms u).bytes.get? a = c.ms.mem.bytes.get? a

/-- **The multithreaded process under x86-TSO** (`MtStep U tso`) as a concrete model of the
thread machine. -/
def tsoModel (U : UIsa γ) (P : PrimTable γ) (base : Base γ) : Model (procT U P base) where
  Conf := MtCfg U.St γ tso.S
  step := MtStep U tso P base
  fault := MtFault U tso P
  abs := tsoAbs U P base

/-- **Open: DRF for the TSO process.** If plain steps are local, the TSO process refines SC
with atomic steps on every certified program: every TSO run from a configuration standing for a
certified start ends standing for an SC-reachable configuration, and TSO faults are SC faults.
The proof idea is moria's `csl_buffered` (ownership: a byte in a store buffer is owned by its
thread, ownership moves only at synchronised steps, so other threads never read it), on byte
buffers. Not proved here. -/
def Task.tsoSound (U : UIsa γ) (P : PrimTable γ) (base : Base γ) : Prop :=
  LocalAcc U → ∀ I Q, (tsoModel U P base).Sound I Q

end Silmaril.Process.Mt.Csl.Proc
