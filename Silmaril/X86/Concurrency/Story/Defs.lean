module

public import Silmaril.X86.MemoryModel.Litmus.Verdicts.Defs
public import Silmaril.X86.Concurrency.Cir.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Defs
public import Silmaril.X86.Concurrency.Cir.Mutex.Defs

/-!
# The concurrency story: the front door (definitions)

This header and `Story.Thms` collect the
concurrency track's results into one place, stated in the words "behaviour B is allowed" and
"behaviour B is not allowed". Almost everything here is a re-export or an instantiation of a
theorem proved elsewhere; the one new proof is the counter client of `Story.Counter` (in
`Silmaril/Proofs/X86/Concurrency/Story/Counter.lean`).

## Verdicts on the bytes

A litmus test `t` (`MemoryModel.Litmus.Corpus`) has the x86 bytes of its threads. Its
**traces** are extracted from those bytes by the decoder-driven extractor (`Test.traces`,
`extract_sound`). Over them:

* `Allowed t M`: some candidate execution consistent with the axiomatic model `M` ends in the
  test's witness (the outcome the test asks about);
* `Forbidden t M`: none does;
* `OpAllowed t`, `OpForbidden t`: the same for the operational store-buffer machine (x86-TSO);
* `ForbiddenBelowXl t`: the witness is forbidden under **every** model `M ⊑ XL` (SC, TSO, XL
  and anything between);
* `LooseAllowed`, `LooseForbidden`: as `Allowed`/`Forbidden`, over `Test.looseTraces` (the
  `Weak9` extractor, which also decodes `movnti` and `rep stosb`).

On CIR, for a test translation-validated from the bytes (`Tv.TvTest`):

* `CirAllowed c M`, `CirForbidden c M`: some/no behaviour of the CIR program over the test's
  value domain under `M` ends in the witness.

## The counter client (`Counter`)

`Counter.client N` is a `Mutex.Client`: `N` threads, each running
`lock(m); rbx := [x]; [x] := rbx + 1; unlock(m)` with plain (`na`) 8-byte accesses, and the
counter `x` initially `0`. The client also owns `2N` **token cells** that no code accesses
(`Counter.permit t`, `Counter.receipt k`, all `0`). The logic has no ghost state, so, as for
the lock token (`Mutex.Spin.tok`), the proof moves ownership of real cells that no
instruction touches: a thread hands its permit to the lock's resource and takes the receipt
numbered by the value it read. The goal is `Counter.Goal N`: the final counter is `N`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Story

open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (Test Verdict AxReach OpReach)
open Silmaril.X86.Concurrency.Cir (BehavIn MLe)
open Silmaril.X86.Concurrency.Cir.Tv (TvTest)

/-! ## Verdicts on the bytes -/

/-- **Behaviour allowed on the bytes**: over the traces extracted from the test's x86 bytes,
some execution consistent with `M` ends in the witness. -/
def Allowed (t : Test) (M : Exec → Prop) : Prop :=
  ∃ T, t.traces = some T ∧ Verdict.allowed.Holds t (AxReach t T M)

/-- **Behaviour not allowed on the bytes**: the traces extract and no execution consistent with
`M` ends in the witness. -/
def Forbidden (t : Test) (M : Exec → Prop) : Prop :=
  ∃ T, t.traces = some T ∧ Verdict.forbidden.Holds t (AxReach t T M)

/-- Allowed by the operational x86-TSO store-buffer machine over the extracted traces. -/
def OpAllowed (t : Test) : Prop :=
  ∃ T, t.traces = some T ∧ Verdict.allowed.Holds t (OpReach t T)

/-- Not allowed by the operational x86-TSO store-buffer machine over the extracted traces. -/
def OpForbidden (t : Test) : Prop :=
  ∃ T, t.traces = some T ∧ Verdict.forbidden.Holds t (OpReach t T)

/-- **Not allowed under any model at most as weak as XL** (`M ⊑ XL`: SC, x86-TSO, XL, ...). -/
def ForbiddenBelowXl (t : Test) : Prop :=
  ∃ T, t.traces = some T ∧ ∀ M : Exec → Prop, MLe M Exec.Xl →
    Verdict.forbidden.Holds t (AxReach t T M)

/-- Allowed over the `Weak9` traces of the bytes (`movnti`, `rep stosb` decoded). -/
def LooseAllowed (t : Test) (M : Exec → Prop) : Prop :=
  ∃ T, t.looseTraces = some T ∧ Verdict.allowed.Holds t (AxReach t T M)

/-- Not allowed over the `Weak9` traces of the bytes. -/
def LooseForbidden (t : Test) (M : Exec → Prop) : Prop :=
  ∃ T, t.looseTraces = some T ∧ Verdict.forbidden.Holds t (AxReach t T M)

/-! ## Verdicts on CIR -/

/-- **Behaviour allowed on CIR**: some behaviour of the translation-validated CIR program over
the test's value domain, consistent with `M`, ends in the witness. -/
def CirAllowed (c : TvTest) (M : Exec → Prop) : Prop :=
  Verdict.allowed.Holds c.test (BehavIn c.prog c.test.domain M)

/-- **Behaviour not allowed on CIR.** -/
def CirForbidden (c : TvTest) (M : Exec → Prop) : Prop :=
  Verdict.forbidden.Holds c.test (BehavIn c.prog c.test.domain M)

/-! ## The counter client -/

namespace Counter

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl

/-- The mutex's address (an 8-byte slot). -/
def m : Nat := 0x100

/-- The counter. -/
def x : Nat := 0x200

/-- The base of the token cells. -/
def tb : Nat := 0x10000

/-- Thread `t`'s permit (a token cell no code accesses). -/
def permit (t : Nat) : Nat := tb + 16 * t

/-- The receipt for the increment that read `k` (a token cell no code accesses). -/
def receipt (k : Nat) : Nat := tb + 16 * k + 8

/-- The critical section: `rbx := [x]; [x] := rbx + 1` (plain 8-byte accesses). -/
def inc : Stmt :=
  .seq (.load .rbx .na 8 .wb (.lit x))
    (.store .na 8 .wb (.lit x) (.bin .add (.reg .rbx) (.lit 1)))

/-- Thread `t` with holes `lk`, `ul` for the mutex's derived ops. -/
def body (lk ul : Expr → Stmt) (_t : Nat) : Stmt := .seq (lk (.lit m)) (.seq inc (ul (.lit m)))

/-- A token cell of a client with `N` threads: a permit or a receipt numbered below `N`. -/
def isTok (N a : Nat) : Prop := tb ≤ a ∧ ((a - tb) % 16 = 0 ∨ (a - tb) % 16 = 8) ∧ (a - tb) / 16 < N

instance (N a : Nat) : Decidable (isTok N a) := by unfold isTok; infer_instance

/-- The client's cells: the counter and the `2N` token cells, all `0`. -/
def mem (N : Nat) : Heap := fun a => if a = x ∨ isTok N a then some 0 else none

/-- **The counter client** with `N` threads: one mutex at `m` with an 8-byte slot. -/
def client (N : Nat) : Mutex.Client := ⟨N, body, mem N, [m], 8⟩

/-- **The counter's goal**: the final counter is `N`. -/
def Goal (N : Nat) (mem : Heap) : Prop := mem x = some N

/-! ### A concrete instance for the explorer (non-vacuity) -/

namespace Inst

open Silmaril.X86.Concurrency.Cir.Robust

/-- The cells of the two-thread instance: the counter, the spin mutex's word and token, and the
four token cells. -/
def cells : List (Nat × Nat) :=
  [(x, 0), (m, 0), (m + 4, 0), (permit 0, 0), (receipt 0, 0), (permit 1, 0), (receipt 1, 0)]

/-- **The counter client with two threads, linked with the spin mutex** (loop bound 2). -/
def spinC : CSt :=
  start [(body (Mutex.Inst.call (Prim.SpinLock.cert.body 2))
      (Mutex.Inst.call (Mutex.Spin.unlockCert.body 2)) 0, Regs.zero),
    (body (Mutex.Inst.call (Prim.SpinLock.cert.body 2))
      (Mutex.Inst.call (Mutex.Spin.unlockCert.body 2)) 1, Regs.zero)] cells

/-- The client's own cells of the two-thread instance: the counter and the four token cells. -/
def ownCells : List (Nat × Nat) :=
  [(x, 0), (permit 0, 0), (receipt 0, 0), (permit 1, 0), (receipt 1, 0)]

/-- **The racy mutant**: the same two threads with both holes empty (no lock). -/
def racyC : CSt :=
  start [(body Mutex.Inst.noOp Mutex.Inst.noOp 0, Regs.zero),
    (body Mutex.Inst.noOp Mutex.Inst.noOp 1, Regs.zero)] ownCells

/-- The counter holds `n`. -/
def countIs (n : Nat) (c : CSt) : Bool := memOf c.mem x == some n

end Inst

end Counter

end Silmaril.X86.Concurrency.Story
