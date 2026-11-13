module

public import Silmaril.Machine.Process.IoSpec.Defs

/-!
# `IoSpecNet`: LPS events extended with socket events

`Silmaril.Process.LPS.Event` (the external `silmaril` package) has four constructors, `readEv`,
`writeEv`, `exitEv` and `killEv`: LPS models files and pipes, and nothing about sockets. This
module extends the vocabulary on the Silmaril side, without editing `silmaril`:

* `SockEv V`: socket events, parametric in the type `V` of addresses, names and datagrams (the
  WASI layer takes `V := Val`; the OS layer does not fix an address encoding):
  `bind s local`, `connect s remote outcome` (`none`: accepted; `some k`: refused with the code
  `k`), `accept s local peer`, `recv local dgram` (a datagram delivered to a local address),
  `send s dgram`, `resolve name addr`.
* `XEvent V`: an LPS event (`lps`) or a socket event (`sock`). `liftT` embeds LPS traces,
  `lpsPart` and `sockPart` project an extended trace; `lpsPart (liftT t) = t`.
* `NetEnv V`: the network as seen by a process: the outcome of a connection to each address,
  the datagrams delivered to each local address (`inbox`), the peers of each local address
  and the addresses of each name. `SockEv.Admits N` says one socket event is an outcome the
  network `N` allows; `NetOk N tr`: every socket event of `tr` is admitted.
* **The extended `IoSpec`**: `XIoOut`, `XSysEnv`, `XIoOut.Next`, `XIoSafeN` are `IoOut`,
  `SysEnv`, `IoOut.Next`, `IoSafeN` of `Silmaril.Machine.Process.IoSpec` with `XEvent V` traces.
  `SysEnv.lift E` is the environment `E` with its events embedded, `liftA A` the trace predicate
  `A` read on the LPS part, `liftQ Q` the frame exits. `IoSpecNet.Thms` proves that the
  embedding preserves and reflects `IoSafeN` (`xioSafe_lift_iff`), so `ioSafe_psafe` (LPS
  soundness) transports to lifted environments (`xioSafe_psafe`).
* `sockArm N H`: socket syscalls (the traps `H`) answered by events the network `N` admits,
  with the model unchanged. **An assumption, not an LPS arm**: LPS has no socket syscalls, so
  no `Sound` statement exists for it. `withNet E N H` is `E` lifted, plus `sockArm N H`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Machine.Process.IoSpecNet

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec

/-! ## Events -/

/-- **Socket events**, parametric in the type `V` of addresses, names and datagrams. -/
inductive SockEv (V : Type) where
  /-- The socket `s` is bound to the local address `local`. -/
  | bind (s : Word) (loc : V)
  /-- A connection of `s` to `remote` has the outcome `o` (`none`: accepted, `some k`: the
  error code `k`). -/
  | connect (s : Word) (remote : V) (o : Option Nat)
  /-- The socket `s` bound to `local` accepted a connection from `peer`. -/
  | accept (s : Word) (loc : V) (peer : V)
  /-- The datagram `d` was received at the local address `local`. -/
  | recv (loc : V) (d : V)
  /-- The socket `s` sent the datagram `d`. -/
  | send (s : Word) (d : V)
  /-- The name `name` resolved to the address `addr`. -/
  | resolve (name : V) (addr : V)

/-- **Extended events**: an LPS event or a socket event. -/
inductive XEvent (V : Type) where
  /-- An event of LPS. -/
  | lps (e : Event)
  /-- A socket event. -/
  | sock (e : SockEv V)

variable {V : Type}

/-- The LPS event of an extended event. -/
def XEvent.toLps : XEvent V → Option Event
  | .lps e => some e
  | .sock _ => none

/-- The socket event of an extended event. -/
def XEvent.toSock : XEvent V → Option (SockEv V)
  | .lps _ => none
  | .sock e => some e

/-- **The embedding** of LPS traces. -/
def liftT (t : List Event) : List (XEvent V) := t.map .lps

/-- The LPS part of an extended trace. -/
def lpsPart (t : List (XEvent V)) : List Event := t.filterMap XEvent.toLps

/-- The socket part of an extended trace. -/
def sockPart (t : List (XEvent V)) : List (SockEv V) := t.filterMap XEvent.toSock

/-- A trace predicate on LPS traces, read on the LPS part of an extended trace. -/
def liftA (A : List Event → Prop) : List (XEvent V) → Prop := fun tr => A (lpsPart tr)

/-! ## The network -/

/-- **The network as seen by a process.** -/
structure NetEnv (V : Type) where
  /-- The outcome of a connection to each remote address. -/
  conn : V → Option Nat
  /-- The datagrams delivered to each local address. -/
  inbox : V → V → Bool
  /-- The peers that connect to each local address. -/
  peer : V → V → Bool
  /-- The addresses of each name. -/
  resolver : V → V → Bool

/-- **A socket event the network admits.** `bind` and `send` do not observe the network. -/
def SockEv.Admits (N : NetEnv V) : SockEv V → Prop
  | .bind _ _ => True
  | .connect _ remote o => N.conn remote = o
  | .accept _ loc peer => N.peer loc peer = true
  | .recv loc d => N.inbox loc d = true
  | .send _ _ => True
  | .resolve name addr => N.resolver name addr = true

/-- **Every socket event of the trace is admitted by the network.** -/
def NetOk (N : NetEnv V) (tr : List (XEvent V)) : Prop := ∀ e ∈ sockPart tr, e.Admits N

/-! ## The extended `IoSpec` -/

/-- What an environment may answer at a trap, with extended events. -/
inductive XIoOut (Model V : Type) where
  /-- The process continues at `m` with environment `e`, after events `evs`. -/
  | resume (m : MState) (e : Model) (evs : List (XEvent V))
  /-- The process ends; `evs` is the complete trace segment. -/
  | halt (evs : List (XEvent V))

/-- **A syscall environment with extended events.** -/
structure XSysEnv (V : Type) where
  /-- The environment model. -/
  Model : Type
  /-- How an environment model abstracts LPS's model. -/
  Abs : Model → Silmaril.Process.LPS.Model → Prop
  /-- The traps the environment answers. -/
  Handles : X86State → Model → Prop
  /-- Its answers. -/
  arm : X86State → Model → XIoOut Model V → Prop

/-- The obligation after an extended answer. -/
def XIoOut.Next {Model : Type} (k : MState → Model → (List (XEvent V) → Prop) → Prop)
    (A : List (XEvent V) → Prop) : XIoOut Model V → Prop
  | .resume m' e' evs => k m' e' (fun tr => A (evs ++ tr))
  | .halt evs => A evs

/-- **Step-indexed safety through syscalls, with extended events** (`IoSafeN` over `XEvent`). -/
def XIoSafeN (step : MState → Option MState) (E : XSysEnv V)
    (Q : MState → E.Model → (List (XEvent V) → Prop) → Prop) :
    Nat → MState → E.Model → (List (XEvent V) → Prop) → Prop
  | 0, _, _, _ => True
  | n + 1, m, e, A => A [] ∧
      (Q m e A ∨ (∃ m', step m = some m' ∧ XIoSafeN step E Q n m' e A) ∨
        (AtSyscall m ∧ ∀ ch : X86FlagChoices.Choice, E.Handles (trapped ⟨m, none⟩ ch) e ∧
          ∀ o, E.arm (trapped ⟨m, none⟩ ch) e o → o.Next (XIoSafeN step E Q n) A))

/-- An LPS answer with its events embedded. -/
def IoOut.lift {Model : Type} : IoOut Model → XIoOut Model V
  | .resume m e evs => .resume m e (liftT evs)
  | .halt evs => .halt (liftT evs)

/-- **The embedding of environments**: the same model, traps and answers, events embedded. -/
def SysEnv.lift (E : SysEnv) : XSysEnv V where
  Model := E.Model
  Abs := E.Abs
  Handles := E.Handles
  arm s e o := ∃ o', E.arm s e o' ∧ o = IoOut.lift o'

/-- The frame exits on extended predicates: `Q` on the predicate read through `liftT`. -/
def liftQ {Model : Type} (Q : MState → Model → (List Event → Prop) → Prop) :
    MState → Model → (List (XEvent V) → Prop) → Prop :=
  fun m e A => Q m e (fun t => A (liftT t))

/-! ## Socket syscalls (assumed) -/

/-- **Socket syscalls answered by the network** (an assumption: LPS has no socket syscalls).
At the traps `H`, the process resumes at some state with the model unchanged, after socket
events that `N` admits. -/
def sockArm {Model : Type} (N : NetEnv V) (H : X86State → Model → Prop) :
    X86State → Model → XIoOut Model V → Prop :=
  fun s e o => H s e ∧ ∃ (m' : MState) (evs : List (SockEv V)), o = .resume m' e (evs.map .sock) ∧
    ∀ ev ∈ evs, ev.Admits N

/-- **`E` with socket syscalls**: the traps of `E` (events embedded) and the socket traps `H`
answered by `sockArm N H`. -/
def withNet (E : SysEnv) (N : NetEnv V) (H : X86State → E.Model → Prop) : XSysEnv V where
  Model := E.Model
  Abs := E.Abs
  Handles s e := E.Handles s e ∨ H s e
  arm s e o := (∃ o', E.arm s e o' ∧ o = IoOut.lift o') ∨ sockArm N H s e o

end Silmaril.Machine.Process.IoSpecNet
