module

public import Silmaril.Process.Mt.Pthread.Defs

/-!
# A simple pthread-based multithreading model

The multi-threaded process model specialised to programs whose threads **exist only through
`pthread_create`/`pthread_join`** and **synchronise only through pthread primitives**, which
are single atomic steps of their specifications (`Pthread/Defs`). It is the model to validate
basic pthread binaries against (`scripts/pthread-hw`, and the problems of erebor-lean's
`Erebor.Pthread`).

## Programs

A program (`Prog`) is a table of functions (function `0` is `main`), each a list of
instructions (`Ins`) over per-thread registers (`Nat → Nat`, all `0` at the start of a
thread except register `0`, the start routine's argument) and one shared memory of cells
(`Nat → Nat`, all `0` at the start, as static storage is):

| instruction | kind | meaning |
|---|---|---|
| `movi d v`, `add d a b`, `addi d a v` | plain, no access | register arithmetic (naturals) |
| `ld d base idx`, `st base idx s` | plain, one cell | `d := [base + idx]`, `[base + idx] := s` (`idx`: an optional register) |
| `beq r v l`, `bne r v l`, `beqr a b l`, `bner a b l`, `jmp l` | plain, no access | branches (on a register and an immediate, or two registers) |
| `call o args d` | atomic | the pthread primitive `o` (`Pthread.Op`) with `args`; `d` gets the result |
| `create f a d` | spawn | `pthread_create`: a fresh thread runs function `f` with register `0 = a`; `d` gets its id |
| `out r` | atomic | appends register `r` to the output (one `write(2)` of the program's output) |
| `ret r` | atomic | the start routine returns `r`: `pthread_exit(r)`, and the thread has finished |
| `halt` | plain, no access | `main` returns (after its last output): the thread has finished |

A program reaches **undefined behaviour** (`Csl.Fault`) when a primitive's precondition fails
or a thread runs off its function. A data race (`WRace`) is two threads whose next plain
steps access a common cell, at least one of them writing it (`Csl.Race` also counts two reads,
so programs whose threads read a shared cell are not `Csl.Race`-free); the semantics below interleaves racing accesses (sequential
consistency), which is a statement about the program's x86 code only under the memory model's
DRF theorem (`Mt/Drf`) or, for racy programs, an explicit assumption.

## The model

`tisa P : Csl.TIsa store` is the thread machine: plain steps are the plain instructions (with
their one-cell footprints), atomic steps are the pthread primitives (`Pthread.prims` through the
lens `lens` onto the memory's pthread state), `out` and `ret`, and spawns are `create`. The
multi-threaded system is `Csl.Step (tisa P)` from `start P` (only `main`, thread `0`).

`Outcome P o`: some run ends with `main` finished and output `o`. `Deterministic P o`: every
run in which `main` finishes outputs `o`, and none reaches undefined behaviour.

## Refinement of the full model

`Refines X P`: a concrete model `X` of the program (its machine code, with glibc's pthread code,
under a memory model: the full multithreaded process model) refines the simple model: every
concrete run stands for a run of `tisa P`, and a concrete fault for an abstract one.
`Simple/Thms` proves that refinement transfers outcomes, and that implementations of the
primitives that linearize (`Lin`: each call takes one specification step at its linearization
point and touches no client cell) compose into a refinement (`Impl.refines`).
-/

@[expose] public section

namespace Silmaril.Process.Mt.Pthread.Simple

open Silmaril.Process.Mt.Csl

/-- Registers. -/
abbrev Reg := Nat

/-- An argument: an immediate or a register. -/
inductive Arg where
  | imm (v : Nat)
  | reg (r : Reg)
  deriving DecidableEq, Repr

/-- Instructions. -/
inductive Ins where
  | movi (d : Reg) (v : Nat)
  | add (d a b : Reg)
  | addi (d a : Reg) (v : Nat)
  | ld (d : Reg) (base : Nat) (idx : Option Reg)
  | st (base : Nat) (idx : Option Reg) (s : Reg)
  | beq (r : Reg) (v : Nat) (l : Nat)
  | bne (r : Reg) (v : Nat) (l : Nat)
  | beqr (a b : Reg) (l : Nat)
  | bner (a b : Reg) (l : Nat)
  | jmp (l : Nat)
  | call (o : Op) (args : List Arg) (d : Reg)
  | create (f : Nat) (a : Arg) (d : Reg)
  | out (r : Reg)
  | ret (r : Reg)
  | halt

/-- A program: function `f`'s instructions (`main` is `0`). -/
structure Prog where
  code : Nat → List Ins

/-- A thread: its function, position, registers, and whether it has finished. -/
structure TSt where
  fn : Nat
  pc : Nat
  regs : Nat → Nat
  fin : Bool := false

/-- The memory: the cells, the pthread state, the output so far. -/
structure SM where
  cells : Nat → Nat
  ps : PSt
  out : List Nat := []

/-- Cells are read one by one. -/
def store : Store SM Nat Nat := ⟨fun m a => some (m.cells a)⟩

/-- The lens onto the pthread state. -/
def lens : Lens SM := ⟨SM.ps, fun m p => { m with ps := p }⟩

/-- Set a register. -/
def setReg (rs : Nat → Nat) (d : Reg) (v : Nat) : Nat → Nat := fun r => if r = d then v else rs r

/-- An argument's value. -/
def Arg.val (rs : Nat → Nat) : Arg → Nat
  | .imm v => v
  | .reg r => rs r

/-- The address `base + idx`. -/
def addr (rs : Nat → Nat) (base : Nat) : Option Reg → Nat
  | none => base
  | some r => base + rs r

/-- The instruction a running thread is at. -/
def fetch (P : Prog) (s : TSt) : Option Ins := if s.fin then none else (P.code s.fn)[s.pc]?

/-- Continue at the next instruction with registers `rs`. -/
def TSt.next (s : TSt) (rs : Nat → Nat) : TSt := { s with pc := s.pc + 1, regs := rs }

/-- **Plain steps** (memory `m` to `m'`). -/
def plain (P : Prog) (s : TSt) (m : SM) (s' : TSt) (m' : SM) : Prop :=
  match fetch P s with
  | some (.movi d v) => s' = s.next (setReg s.regs d v) ∧ m' = m
  | some (.add d a b) => s' = s.next (setReg s.regs d (s.regs a + s.regs b)) ∧ m' = m
  | some (.addi d a v) => s' = s.next (setReg s.regs d (s.regs a + v)) ∧ m' = m
  | some (.ld d b i) => s' = s.next (setReg s.regs d (m.cells (addr s.regs b i))) ∧ m' = m
  | some (.st b i r) => s' = s.next s.regs ∧
      m' = { m with cells := fun x => if x = addr s.regs b i then s.regs r else m.cells x }
  | some (.beq r v l) => s' = (if s.regs r = v then { s with pc := l } else s.next s.regs) ∧ m' = m
  | some (.bne r v l) => s' = (if s.regs r = v then s.next s.regs else { s with pc := l }) ∧ m' = m
  | some (.beqr a b l) => s' = (if s.regs a = s.regs b then { s with pc := l } else s.next s.regs) ∧ m' = m
  | some (.bner a b l) => s' = (if s.regs a = s.regs b then s.next s.regs else { s with pc := l }) ∧ m' = m
  | some (.jmp l) => s' = { s with pc := l } ∧ m' = m
  | some .halt => s' = { s with fin := true } ∧ m' = m
  | _ => False

/-- The footprint of the next plain step (it depends on the registers only). -/
def fp (P : Prog) (s : TSt) (_m : SM) (a : Nat) : Prop :=
  match fetch P s with
  | some (.ld _ b i) => a = addr s.regs b i
  | some (.st b i _) => a = addr s.regs b i
  | _ => False

/-- The pthread call a thread is at. -/
def callOf (P : Prog) (s : TSt) : Option (Op × List Nat) :=
  match fetch P s with
  | some (.call o args _) => some (o, args.map (Arg.val s.regs))
  | _ => none

/-- Resume after a pthread call with result `r`. -/
def resume (P : Prog) (s : TSt) (r : Nat) : TSt :=
  match fetch P s with
  | some (.call _ _ d) => s.next (setReg s.regs d r)
  | _ => s

/-- The pthread primitives of a program. -/
def prims (P : Prog) : Prims TSt SM := Pthread.prims lens (callOf P) (resume P)

/-- **Atomic steps**: pthread primitives, output, and the start routine's return
(`pthread_exit`). -/
def atom (P : Prog) (t : Nat) (s : TSt) (m : SM) (s' : TSt) (m' : SM) : Prop :=
  (prims P).atom t s m s' m' ∨
  (∃ r, fetch P s = some (.out r) ∧ s' = s.next s.regs ∧ m' = { m with out := m.out ++ [s.regs r] }) ∨
  (∃ r p', fetch P s = some (.ret r) ∧ Pthread.exit.step t [s.regs r] m.ps 0 p' ∧
    s' = { s with fin := true } ∧ m' = { m with ps := p' })

/-- Atomic faults: a primitive's precondition, `pthread_exit` of a thread that is not
running, or a thread that ran off its function. -/
def afault (P : Prog) (t : Nat) (s : TSt) (m : SM) : Prop :=
  (prims P).afault t s m ∨
  (∃ r, fetch P s = some (.ret r) ∧ Pthread.exit.fault t [s.regs r] m.ps) ∨
  (s.fin = false ∧ fetch P s = none)

/-- **`pthread_create`**: a fresh thread `u` (in the pthread state too) running function `f`
with register `0 = a`. -/
def spawn (P : Prog) (_t u : Nat) (s : TSt) (m : SM) (s₁ s₂ : TSt) (m' : SM) : Prop :=
  ∃ f a d p', fetch P s = some (.create f a d) ∧ createRel u m.ps p' ∧
    m' = { m with ps := p' } ∧ s₁ = s.next (setReg s.regs d u) ∧
    s₂ = { fn := f, pc := 0, regs := fun r => if r = 0 then a.val s.regs else 0 }

/-- **The thread machine of a program.** -/
def tisa (P : Prog) : TIsa store where
  St := TSt
  step _ s m s' m' := plain P s m s' m'
  fault _ _ _ := False
  fp _ s m a := fp P s m a
  atom := atom P
  afault := afault P
  spawn := spawn P
  done s := s.fin = true

/-- **The start**: `main` (thread `0`) at its first instruction, cells `0`, no output. -/
def start (P : Prog) : Cfg (tisa P) :=
  ⟨fun t => if t = 0 then some ({ fn := 0, pc := 0, regs := fun _ => 0 } : TSt) else none,
   { cells := fun _ => 0, ps := PSt.init 0 }⟩

/-- `main` has finished. -/
def MainDone {P : Prog} (C : Cfg (tisa P)) : Prop := ∃ s : TSt, C.th 0 = some s ∧ s.fin = true

/-- **An outcome**: some run ends with `main` finished and output `o`. -/
def Outcome (P : Prog) (o : List Nat) : Prop :=
  ∃ C, Reach (tisa P) (start P) C ∧ MainDone C ∧ C.mem.out = o

/-- No reachable configuration has undefined behaviour. -/
def NoUB (P : Prog) : Prop := ∀ C, Reach (tisa P) (start P) C → ¬ Fault (tisa P) C

/-- **Deterministic output `o`**: no undefined behaviour, and every run in which `main`
finishes outputs `o`. -/
def Deterministic (P : Prog) (o : List Nat) : Prop :=
  NoUB P ∧ ∀ C, Reach (tisa P) (start P) C → MainDone C → C.mem.out = o

/-- The cell the next plain step **writes** (a `st`), if any. -/
def wr (P : Prog) (s : TSt) (a : Nat) : Prop :=
  match fetch P s with
  | some (.st b i _) => a = addr s.regs b i
  | _ => False

/-- **A data race**: two different threads whose next plain steps access a common cell, the
first one writing it. Two reads of one cell are not a race (`Csl.Race` counts them too). -/
def WRace (P : Prog) (C : Cfg (tisa P)) : Prop :=
  ∃ t u s s' a, t ≠ u ∧ C.th t = some s ∧ C.th u = some s' ∧ wr P s a ∧ fp P s' C.mem a

/-- No reachable configuration has a data race (a write racing with a read or a write). -/
def RaceFree (P : Prog) : Prop := ∀ C, Reach (tisa P) (start P) C → ¬ WRace P C

/-- **A concrete model refines the simple model** (from a concrete start standing for
`start P`): every concrete run stands for a run of the simple model, and a concrete fault for
an abstract one. -/
def Refines {P : Prog} (X : Model (tisa P)) : Prop :=
  ∀ c₀ c, X.abs c₀ (start P) → Star X.step c₀ c →
    ∃ C, Reach (tisa P) (start P) C ∧ X.abs c C ∧ (X.fault c → Fault (tisa P) C)

/-! ## The full model: the program with implemented primitives -/

/-- **Implementations of the pthread primitives** over object states `ι` (the memory glibc
keeps its objects in, which the client never touches), seen through `β : ι → PSt`: for each
call `o args`, a code state type, its start, its steps (thread, code state, objects, to code
state, objects) and its return value once finished; `lin q` is the result recorded at the
linearization point (`none` before it). `create u` and `exit t v` are the object updates of
`pthread_create` (thread `u`) and of a start routine returning `v`. -/
structure Impl (ι : Type) where
  St : Type
  start : Op → List Nat → St
  step : Nat → Op → List Nat → St → ι → St → ι → Prop
  ret : St → Option Nat
  lin : St → Option Nat
  β : ι → PSt
  create : Nat → ι → ι → Prop
  exit : Nat → Nat → ι → ι → Prop

/-- **The glibc obligations, in linearization form** (under sequential consistency): a fresh
call is before its linearization point; a step before it (of a call whose specification does
not fault) keeps the abstract state or is the linearization point, one specification step of
the call with the result it records; steps after it keep the abstract state and the result; a
call returns the recorded result; `create` and `exit` are their specification steps. -/
structure Impl.Lin {ι : Type} (I : Impl ι) : Prop where
  start : ∀ o args, I.lin (I.start o args) = none
  pre : ∀ t o args q x q' x', I.step t o args q x q' x' → I.lin q = none →
    ¬ (o.spec).fault t args (I.β x) →
    (I.β x' = I.β x ∧ I.lin q' = none) ∨ ∃ r, (o.spec).step t args (I.β x) r (I.β x') ∧ I.lin q' = some r
  post : ∀ t o args q x q' x' r, I.step t o args q x q' x' → I.lin q = some r →
    I.β x' = I.β x ∧ I.lin q' = some r
  ret : ∀ q r, I.ret q = some r → I.lin q = some r
  create : ∀ u x x', I.create u x x' → createRel u (I.β x) (I.β x')
  exit : ∀ t v x x', I.exit t v x x' → ¬ Pthread.exit.fault t [v] (I.β x) →
    Pthread.exit.step t [v] (I.β x) 0 (I.β x')

/-- A thread of the full model: its client state, and the code state of the call it is in. -/
structure CT (κ : Type) where
  cl : TSt
  call : Option κ := none

/-- A configuration of the full model: threads, cells, objects, output. -/
structure CCfg (κ ι : Type) where
  th : Nat → Option (CT κ)
  cells : Nat → Nat
  obj : ι
  out : List Nat

section
variable {ι : Type} (P : Prog) (I : Impl ι)

/-- The client memory a configuration stands for. -/
def absM (c : CCfg I.St ι) : SM := ⟨c.cells, I.β c.obj, c.out⟩

/-- The client state a thread stands for: inside a call after its linearization point, the
state after the call. -/
def absT (x : CT I.St) : TSt :=
  match x.call with
  | none => x.cl
  | some q => match I.lin q with
    | none => x.cl
    | some r => resume P x.cl r

/-- The configuration of the simple model a configuration stands for. -/
def absC (c : CCfg I.St ι) : Cfg (tisa P) := ⟨fun t => (c.th t).map (absT P I), absM I c⟩

/-- Update thread `t`. -/
def CCfg.set (c : CCfg I.St ι) (t : Nat) (x : CT I.St) : Nat → Option (CT I.St) := Heap.upd c.th t (some x)

/-- **One step of the full model** (sequential consistency): a client instruction, entering a
pthread call, a step of its code, returning from it, output, the start routine's return, or
`pthread_create`. -/
inductive CStep : CCfg I.St ι → CCfg I.St ι → Prop
  | plain {c t s s' m'} (h : c.th t = some ⟨s, none⟩) (hp : Simple.plain P s (absM I c) s' m') :
      CStep c { c with th := c.set I t ⟨s', none⟩, cells := m'.cells }
  | enter {c t s o args} (h : c.th t = some ⟨s, none⟩) (hc : callOf P s = some (o, args)) :
      CStep c { c with th := c.set I t ⟨s, some (I.start o args)⟩ }
  | code {c t s q o args q' x'} (h : c.th t = some ⟨s, some q⟩) (hc : callOf P s = some (o, args))
      (hs : I.step t o args q c.obj q' x') :
      CStep c { c with th := c.set I t ⟨s, some q'⟩, obj := x' }
  | leave {c t s q r} (h : c.th t = some ⟨s, some q⟩) (hr : I.ret q = some r) :
      CStep c { c with th := c.set I t ⟨resume P s r, none⟩ }
  | out {c t s r} (h : c.th t = some ⟨s, none⟩) (hf : fetch P s = some (.out r)) :
      CStep c { c with th := c.set I t ⟨s.next s.regs, none⟩, out := c.out ++ [s.regs r] }
  | ret {c t s r x'} (h : c.th t = some ⟨s, none⟩) (hf : fetch P s = some (.ret r))
      (he : I.exit t (s.regs r) c.obj x') :
      CStep c { c with th := c.set I t ⟨{ s with fin := true }, none⟩, obj := x' }
  | create {c t s f a d u x'} (h : c.th t = some ⟨s, none⟩) (hf : fetch P s = some (.create f a d))
      (hu : c.th u = none) (hc : I.create u c.obj x') :
      CStep c { c with
        th := Heap.upd (c.set I t ⟨s.next (setReg s.regs d u), none⟩) u
          (some ⟨{ fn := f, pc := 0, regs := fun r => if r = 0 then a.val s.regs else 0 }, none⟩)
        obj := x' }

/-- **The full model** of program `P` with the implementations `I`, as a concrete model of the
simple model: steps from configurations whose abstraction has no undefined behaviour. -/
def Impl.model : Model (tisa P) where
  Conf := CCfg I.St ι
  step c c' := ¬ Fault (tisa P) (absC P I c) ∧ CStep P I c c'
  fault c := Fault (tisa P) (absC P I c)
  abs c C := C = absC P I c

end

end Silmaril.Process.Mt.Pthread.Simple
