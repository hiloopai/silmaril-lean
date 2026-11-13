module

public import Silmaril.Process.Mt.Prim.Defs
public import Silmaril.X86.Str9FsXN.Defs

/-!
# The multithreaded x86-64 process (first pass)

`mtX X : UIsa γ` is the x86-64 user ISA of the multithreaded process model `MtStep`, for a
statically linked executable: each thread is a **`Str9FsXN` core** (`Core`: the sixteen
general registers, `rip`, the flags, `fsBase` — the thread's TLS base — and the sixteen XMM
registers) on the shared memory. What a thread does next, in this order:

1. at an entry point of a **trusted primitive** (`X.prims`, address ↦ primitive number):
   a call of the primitive (`UOut.prim`) with the System V argument registers
   (`rdi, rsi, rdx, rcx, r8, r9`), returning to the address on top of the stack with the
   result in `rax`, `rsp + 8`, and the callee-saved registers (`rbx, rbp, r12–r15`) and
   `fsBase` kept; every other register (the XMM registers included) is left arbitrary
   (`PrimRet`). An unreadable return address is a fault;
2. at an entry point of a **library function with a contract** (`X.libs`): one library
   step (`UOut.lib`), as the contract relation `LibFn` allows (`none`: a fault). This is
   `Elf.Link.Dyn.Proc`'s convention (one atomic step from call to return), per thread: the
   contract sees the calling thread's id;
3. at `syscall` (`0F 05`): `arch_prctl (ARCH_SET_FS, a)` sets the thread's `fsBase` (a
   thread-local step); any other number is a system call (`UOut.sys`) with the Linux argument
   registers (`rdi, rsi, rdx, r10, r8, r9`). The thread resumes after the `syscall` with the
   result in `rax`, `rcx` the return address, `r11` the flags image (any word), everything else
   kept (`sysK`). A `clone` child starts in the same state with `rax = 0`, `rsp` the new stack
   (unless `0`) and `fsBase` the `tls` argument (`cloneChild`);
4. otherwise one **`Str9FsXN` instruction** (`UOut.step`), on the thread's memory view, with
   the access list `X.acc` (default: unknown, so a non-SC memory system runs it as a barrier);
   an undecoded instruction or a fault is `stop`.

`Thms` gives an executable scheduler for SC runs (`run`) and proves it sound
(`run_sound`); the examples in `Silmaril.Proofs.Process.Mt.Examples` run it.

**Trusted**, beyond `MtStep`'s assumptions: the `Str9FsXN` instruction semantics; that the
primitives at `X.prims` implement their specifications as single atomic steps; the library
contracts `X.libs`. **Not modelled**: signals, `CLONE_CHILD_SETTID`, `clone` flag words other
than `pthread_create`'s, the red zone below `rsp` across a primitive call (a primitive may
not write it; nothing here says so), and access lists of `Str9FsXN` (open Task: a `Local`
access list per instruction, as `MemEvent` has for `Open9`/`Atomic9`/`Sse9`).
-/

@[expose] public section

namespace Silmaril.Process.Mt.X86

open Silmaril.X86 (Word Byte State Reg)
open Silmaril.X86.Sse9 (XFile)
open Silmaril.X86.MemEvent (Event)

/-- A thread's core: the integer core (with the TLS base `fsBase`) and the XMM file. -/
structure Core where
  core : State
  xmm : XFile

/-- A library function's contract, for the calling thread: from the core at entry, the
memory and the ghost, the outcome (`none`: a fault). -/
abbrev LibFn (γ : Type) := Nat → Core → Memory → γ → Option (Core × Memory × γ) → Prop

/-- **The executable's environment**: where the primitives and the library functions are,
and the access lists of plain steps. -/
structure Env (γ : Type) where
  prims : List (Word × Nat) := []
  libs : List (Word × LibFn γ) := []
  acc : Core → Memory → Option (List Event) := fun _ _ => none
  ended : γ → Option Nat := fun _ => none

/-- `syscall`. -/
def syscallBytes : List Byte := [0x0F, 0x05]

/-- `arch_prctl`, `ARCH_SET_FS`. -/
def nrArchPrctl : Nat := 158
def archSetFs : Nat := 0x1002

/-- The System V integer argument registers. -/
def callArgs (c : State) : List Word := [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9].map c.read

/-- The Linux system-call argument registers. -/
def sysArgs (c : State) : List Word := [Reg.rdi, .rsi, .rdx, .r10, .r8, .r9].map c.read

/-- The return from a primitive called at `c` with return address `ra` and result `w`: what
the System V ABI fixes. -/
def PrimRet (c : State) (ra w : Word) (c' : Core) : Prop :=
  c'.core.rip = ra ∧ c'.core.read .rsp = c.read .rsp + 8 ∧ c'.core.read .rax = w ∧
    (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], c'.core.read r = c.read r) ∧
    c'.core.fsBase = c.fsBase

/-- The canonical return from a primitive: only `rip`, `rsp` and `rax` change. -/
def primK (c : Core) (ra w : Word) : Core :=
  ⟨{ (c.core.write .rsp (c.core.read .rsp + 8)).write .rax w with rip := ra }, c.xmm⟩

/-- The return address on top of the stack. -/
def retAddr (c : State) (m : Memory) : Option Word :=
  (Prim.rd m (c.read .rsp).toNat 8).map (BitVec.ofNat 64)

/-- The resumption after `syscall` (`rip` already past it) with result `w` and flags image
`fl`. -/
def sysK (c : Core) (fl w : Word) : Core :=
  ⟨((c.core.write .rax w).write .rcx c.core.rip).write .r11 fl, c.xmm⟩

/-- A `clone` child: the parent's resumption with `0`, the new stack (unless `0`) and the TLS
base `tls` (`args = flags, newsp, ptid, ctid, tls`). -/
def cloneChild (c : Core) (fl : Word) (args : List Word) : Core :=
  let c1 := sysK c fl 0
  let sp := args.getD 1 0
  ⟨{ (if sp = 0 then c1.core else c1.core.write .rsp sp) with fsBase := args.getD 4 0 }, c1.xmm⟩

/-- Past the `syscall` instruction. -/
def pastSys (c : Core) : Core := ⟨{ c.core with rip := c.core.rip + 2 }, c.xmm⟩

variable {γ : Type}

/-- The outcome of a library contract. -/
def libOut : Option (Core × Memory × γ) → UOut Core γ
  | some (c, m, g) => .lib c m g
  | none => .stop

/-- **What thread `t` does next.** -/
def step (X : Env γ) (t : Nat) (c : Core) (m : Memory) (g : γ) (o : UOut Core γ) : Prop :=
  match X.prims.find? (·.1 == c.core.rip) with
  | some (_, p) =>
    match retAddr c.core m with
    | some ra => ∃ k, (∀ w, PrimRet c.core ra w (k w)) ∧ o = .prim p (callArgs c.core) k
    | none => o = .stop
  | none =>
    match X.libs.find? (·.1 == c.core.rip) with
    | some (_, f) => ∃ r, f t c m g r ∧ o = libOut r
    | none =>
      if m.fetchBytes c.core.rip.toNat 2 = some syscallBytes then
        let c1 := pastSys c
        ∃ fl : Word,
          if (c.core.read .rax).toNat = nrArchPrctl ∧ (c.core.read .rdi).toNat = archSetFs then
            o = .step (sysK ⟨{ c1.core with fsBase := c.core.read .rsi }, c1.xmm⟩ fl 0) none m
          else
            o = .sys (c.core.read .rax).toNat (sysArgs c.core) (sysK c1 fl)
              (cloneChild c1 fl (sysArgs c.core))
      else
        match Silmaril.X86.Str9FsXN.step ⟨⟨c.core, m⟩, c.xmm⟩ with
        | some y => o = .step ⟨y.m.core, y.xmm⟩ (X.acc c m) y.m.memory
        | none => o = .stop

/-- **The multithreaded x86-64 user ISA.** -/
def mtX (X : Env γ) : UIsa γ where
  St := Core
  step := step X
  ended := X.ended

/-- **The multithreaded x86-64 process** under memory system `M`, primitives `P` and base
system calls `base`. -/
abbrev MtProc (X : Env γ) (M : MemSys) (P : PrimTable γ) (base : Base γ) :=
  MtStep (mtX X) M P base

/-! ## An executable scheduler (SC, standard primitives)

`exec1 X tids C t` runs one step of thread `t` under SC with the standard primitives
(`Prim.table`) and no base system calls, choosing the canonical outcome where the model is
nondeterministic: the primitive return keeps every register but `rip`, `rsp` and `rax`; the
`syscall` flags image is `0`; `FUTEX_WAKE` wakes the first waiters in `tids` order; a `clone`
child gets the tid one above the largest in `tids`. `tids` lists the thread ids in use (the
executor needs it to enumerate waiters and live threads). Library steps are not run.
`run` runs a schedule (a list of thread ids). `Thms.run_sound` proves every run is a run of
`MtProc X sc Prim.table (Base.none γ)`. -/

/-- A configuration of the SC x86 process. -/
abbrev XCfg (γ : Type) := MtCfg Core γ sc.S

/-- A present thread that has not exited. -/
def liveB : Option (TRec Core) → Bool
  | some r => !r.st.isExited
  | none => false

/-- A thread waiting on `a`. -/
def waitingB (a : Nat) : Option (TRec Core) → Bool
  | some ⟨.wait b _, _⟩ => b == a
  | _ => false

/-- The executable system calls. -/
def execSys (tids : List Nat) (C : XCfg γ) (t : Nat) (r : TRec Core) (c : Core) :
    Option (XCfg γ × List Nat) :=
  let c1 := pastSys c
  let args := sysArgs c.core
  let k := sysK c1 0
  let nr := (c.core.read .rax).toNat
  if nr = nrArchPrctl ∧ (c.core.read .rdi).toNat = archSetFs then
    let c2 := sysK ⟨{ c1.core with fsBase := c.core.read .rsi }, c1.xmm⟩ 0 0
    some ({ C with th := setTh C.th t { r with st := .run c2 } }, tids)
  else if nr = nrGettid then
    some ({ C with th := setTh C.th t { r with st := .run (k (BitVec.ofNat 64 t)) } }, tids)
  else if nr = nrExitGroup then
    some ({ C with status := some ((args.getD 0 0).toNat % 256) }, tids)
  else if nr = nrFutex then
    let a := args.getD 0 0
    let op := args.getD 1 0
    let v := args.getD 2 0
    if a.toNat % 4 = 0 then
      if WaitOp op then
        match C.ms.readBytes a.toNat 4 with
        | some w =>
          if w = le 4 v then some ({ C with th := setTh C.th t { r with st := .wait a.toNat k } }, tids)
          else some ({ C with th := setTh C.th t { r with st := .run (k errAgain) } }, tids)
        | none => none
      else if WakeOp op then
        let ws := (tids.filter fun u => waitingB a.toNat (C.th u)).take v.toNat
        let r' := { r with st := .run (k (BitVec.ofNat 64 ws.length)) }
        some ({ C with th := setTh (wakeAll C.th ws) t r' }, tids)
      else none
    else none
  else if nr = nrExit then
    let th1 := setTh C.th t { r with st := .exited }
    let other := tids.any fun u => liveB (th1 u)
    let code := (args.getD 0 0).toNat % 256
    let plain := some ({ C with th := th1, status := if other then none else some code }, tids)
    match r.ctid with
    | some a =>
      match C.ms.writeBytes a (le 4 0) with
      | some m' =>
        if other then
          let ws := (tids.filter fun u => waitingB a (th1 u)).take 1
          some ({ C with th := wakeAll th1 ws, ms := m' }, tids)
        else plain
      | none => plain
    | none => plain
  else if nr = nrClone then
    let t' := tids.foldr max 0 + 1
    if CloneOk (args.getD 0 0) ∧ t' < pidMax then
      match C.ms.writeBytes (args.getD 2 0).toNat (le 4 (BitVec.ofNat 64 t')) with
      | some m' => some ({ C with
          th := setTh (setTh C.th t { r with st := .run (k (BitVec.ofNat 64 t')) }) t'
            { st := .run (cloneChild c1 0 args), ctid := some (args.getD 3 0).toNat }
          ms := m', mt := true }, tids ++ [t'])
      | none => none
    else none
  else none

/-- One step of thread `t`. -/
def exec1 (X : Env γ) (tids : List Nat) (C : XCfg γ) (t : Nat) : Option (XCfg γ × List Nat) :=
  if C.status = none ∧ X.ended C.g = none then
    match C.th t with
    | some r =>
      match r.st with
      | .run c =>
        match X.prims.find? (·.1 == c.core.rip) with
        | some (_, p) =>
          match retAddr c.core C.ms with
          | some ra =>
            match Prim.execTable p t (callArgs c.core) (C.sh sc) with
            | some (w, sh2) => some ({ C with
                th := setTh C.th t { r with st := .run (primK c ra w) }
                ms := sh2.mem
                ps := sh2.ps
                g := sh2.g }, tids)
            | none => none
          | none => none
        | none =>
          match X.libs.find? (·.1 == c.core.rip) with
          | some _ => none
          | none =>
            if C.ms.fetchBytes c.core.rip.toNat 2 = some syscallBytes then execSys tids C t r c
            else
              match Silmaril.X86.Str9FsXN.step ⟨⟨c.core, C.ms⟩, c.xmm⟩ with
              | some y => some ({ C with
                  th := setTh C.th t { r with st := .run ⟨y.m.core, y.xmm⟩ }
                  ms := y.m.memory }, tids)
              | none => none
      | _ => none
    | none => none
  else none

/-- Run a schedule. -/
def run (X : Env γ) : List Nat → XCfg γ × List Nat → Option (XCfg γ × List Nat)
  | [], p => some p
  | t :: ts, (C, tids) => (exec1 X tids C t).bind (run X ts)

/-- `tids` lists every present thread, once. -/
def Cover {σ γ S : Type} (tids : List Nat) (C : MtCfg σ γ S) : Prop :=
  tids.Nodup ∧ ∀ u, (C.th u).isSome → u ∈ tids

end Silmaril.Process.Mt.X86
