module

public import Silmaril.Process.Mt.X86.Defs

/-!
# Towards the memory-model bridge: statements (open)

The multithreaded process model `MtStep` is parametric in its memory system. This file states,
as **open goals** (`Task` definitions, not assumed anywhere), the first two facts the bridge from
x86-TSO to SC needs; nothing here is proved.

It lives under `Process/Mt/Drf/Proc` beside the generic bridge `Silmaril.Process.Mt.Drf`
(store-buffer machines over an abstract thread system `Drf.Sys`, with ownership certificates);
its declarations stay in `Silmaril.Process.Mt` because they extend the process model's types
(`MtCfg.toTso`, `UOut.Buffered`). Race freedom here is `RaceFree`, so that `Silmaril.Process.Mt.Drf`
names only the bridge's namespace.

* `EvLocal U`: the access lists of `U`'s plain steps are exact (`MemEvent`'s locality): the
  outcome depends only on the read set, and the step changes exactly the write set. This is
  what lets `tso` run a plain step on the thread's buffered view.
* `Task.x86Acc`: `Str9FsXN` has such access lists, one per decoded instruction (`MemEvent`
  has them today for `Open9`, `Atomic9` and `Sse9`, not for the string, FS and narrow forms).
  The instruction fetch must be among the loads: under TSO a thread could otherwise see code
  bytes another thread has not yet flushed.
* `Race`, `RaceFree`: in some SC-reachable configuration, two different threads have possible next
  actions that conflict on a byte (one may write it, the other may read or write it), and at
  least one of them is a **buffered** plain step (known access list, not locked or fencing).
  Two synchronising actions (primitive calls, library steps, system calls, locked or fencing
  steps, steps with no access list) never race; a synchronising action races with a plain
  access to its footprint (`PrimSpec.fp`; library steps and unknown system calls: all of
  memory).
* **`Task.drfSc`**: a data-race-free process (under SC, from `C0`) with exact access lists has,
  under x86-TSO, only SC outcomes: every TSO run from `C0` (empty buffers) that ends with every
  buffer drained ends in a configuration SC reaches. This is the DRF-SC theorem for the process
  model (moria's `drf_sc` proves its analogue for CIR programs over a cell heap); with
  `X86.MemoryModel`'s operational/axiomatic TSO equivalence it would carry over to axiomatic TSO,
  and to the loose model `Xl` on tame accesses (`xl_iff_tso_of_tame`).

`Race` here is about plain accesses only. Trusted primitives are atomic in `MtStep`; that a
primitive's **implementation** refines its atomic specification under TSO/XL is a separate
assumption per primitive, not stated here.
-/

@[expose] public section

namespace Silmaril.Process.Mt

open Silmaril.X86.MemEvent (Event Agree Patched readSet writeSet)

variable {γ : Type}

/-- **Exact access lists**: a plain step with access list `es` from memory `m` can be replayed on
any memory `n` that agrees with `m` on the read set, with the same thread outcome, patching
exactly the write set. -/
def EvLocal (U : UIsa γ) : Prop :=
  ∀ t s m g s' es m', U.step t s m g (.step s' (some es) m') →
    ∀ n, Agree (readSet es) m n → ∃ n', U.step t s n g (.step s' (some es) n') ∧
      Patched (writeSet es) m m' n n'

/-- **Open**: `Str9FsXN` has exact access lists, one for every instruction it decodes. -/
def Task.x86Acc : Prop :=
  ∀ (X : X86.Env γ), ∃ acc : X86.Core → Memory → Option (List Event),
    EvLocal (X86.mtX { X with acc := acc }) ∧
    ∀ c m, (Silmaril.X86.Str9FsXN.step ⟨⟨c.core, m⟩, c.xmm⟩).isSome → (acc c m).isSome

/-- A plain step with a known access list, not locked or fencing: the only actions that run
on a thread's buffered view under `tso`. Every other action is **synchronising**. -/
def UOut.Buffered {σ : Type} : UOut σ γ → Prop
  | .step _ (some es) _ => barrier es = false
  | _ => False

/-- The 4 bytes at `a`. -/
def word4 (a : Nat) (b : Nat) : Prop := a ≤ b ∧ b < a + 4

/-- The bytes an action may **write** (thread record `r`): a plain step's write set (no access
list: every byte); a primitive's footprint; the kernel's: `FUTEX_WAIT` none, `clone` the `ptid`
word, `exit` the `clear_child_tid` word, `gettid`, `set_tid_address`, `exit_group` and
`FUTEX_WAKE` none, any other call every byte; a library step every byte. -/
def UOut.Writes {σ : Type} (P : PrimTable γ) (r : TRec σ) : UOut σ γ → Nat → Prop
  | .step _ (some es) _ => writeSet es
  | .step _ none _ => fun _ => True
  | .lib .. => fun _ => True
  | .prim p args _ => fun a => match P p with
    | some sp => sp.fp 0 args a
    | none => True
  | .sys nr args _ _ => fun a =>
    if nr = nrFutex ∨ nr = nrGettid ∨ nr = nrSetTid ∨ nr = nrExitGroup then False
    else if nr = nrClone then word4 (args.getD 2 0).toNat a
    else if nr = nrExit then ∃ c, r.ctid = some c ∧ word4 c a
    else True
  | .stop => fun _ => False

/-- The bytes an action may **read or write**: as `Writes`, plus a plain step's read set and
`FUTEX_WAIT`'s word. -/
def UOut.Touches {σ : Type} (P : PrimTable γ) (r : TRec σ) (o : UOut σ γ) (a : Nat) : Prop :=
  o.Writes P r a ∨ match o with
    | .step _ (some es) _ => readSet es a
    | .sys nr args _ _ => nr = nrFutex ∧ word4 (args.getD 0 0).toNat a
    | _ => False

/-- Two actions (of threads with records `r`, `r'`) conflict: not both synchronising, and some
byte one may write the other may touch. -/
def Conflict {σ : Type} (P : PrimTable γ) (r r' : TRec σ) (o o' : UOut σ γ) : Prop :=
  (o.Buffered ∨ o'.Buffered) ∧
    ∃ a, (o.Writes P r a ∧ o'.Touches P r' a) ∨ (o'.Writes P r' a ∧ o.Touches P r a)

/-- **A data race** in the SC configuration `C`: two running threads have possible next actions
that conflict. The primitives' footprints use thread id `0` (`Std` footprints ignore it). -/
def Race (U : UIsa γ) (P : PrimTable γ) (C : MtCfg U.St γ sc.S) : Prop :=
  ∃ t u r r' s s' o o', t ≠ u ∧ C.th t = some r ∧ r.st = .run s ∧ C.th u = some r' ∧ r'.st = .run s' ∧
    U.step t s C.ms C.g o ∧ U.step u s' C.ms C.g o' ∧ Conflict P r r' o o'

/-- **Data-race freedom** of the process from `C0`, under SC. -/
def RaceFree (U : UIsa γ) (P : PrimTable γ) (base : Base γ) (C0 : MtCfg U.St γ sc.S) : Prop :=
  ∀ C, MtReach U sc P base C0 C → ¬ Race U P C

/-- An SC configuration as a TSO one, with empty store buffers. -/
def MtCfg.toTso {σ : Type} (C : MtCfg σ γ sc.S) : MtCfg σ γ tso.S :=
  { C with ms := (⟨C.ms, fun _ => []⟩ : TsoS) }

/-- Every store buffer is empty. -/
def MtCfg.Drained {σ : Type} (C : MtCfg σ γ tso.S) : Prop := ∀ t, C.ms.buf t = []

/-- A TSO configuration as an SC one (its shared memory). -/
def MtCfg.ofTso {σ : Type} (C : MtCfg σ γ tso.S) : MtCfg σ γ sc.S := { C with ms := C.ms.mem }

/-- **Open: DRF-SC for the process model.** -/
def Task.drfSc : Prop :=
  ∀ {γ : Type} (U : UIsa γ) (P : PrimTable γ) (base : Base γ) (C0 : MtCfg U.St γ sc.S)
    (C : MtCfg U.St γ tso.S),
    EvLocal U → RaceFree U P base C0 → MtReach U tso P base C0.toTso C → C.Drained →
      MtReach U sc P base C0 C.ofTso

end Silmaril.Process.Mt
