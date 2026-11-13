module

public import Silmaril.X86.Concurrency.Cir.Prim.Defs
public import Silmaril.X86.Concurrency.Cir.Robust.Defs

/-!
# Closed clients of the synchronisation primitives, for the CIR explorer

Each client is a closed CIR
program of two threads built from the translation-validated function bodies (`f.cert.body L`,
every loop bounded by `L = 2`), glue code that is not from a binary (setting argument registers,
a critical section), and initial cells. Function calls are inlined: the CIR body of a callee runs
in the caller's registers, which is what the x86 calling convention gives for these leaf
functions (their only clobbers are caller-saved registers), but the `call`/`ret` pair itself is
not validated.

* `spinC`: twice `spin_lock; x = x + 1 (plain); spin_unlock`; lock at `0x100`, `x` at `0x200`;
* `tickC`: twice `ticket_lock; x = x + 1; ticket_unlock`; `next`, `serving` at `0x100`,
  `0x104`, `x` at `0x200`;
* `seqC`: `seq_write(s, 1, 1)` ∥ `seq_read(s, out)`; `seq`, `a`, `b` at `0x100`, `0x104`,
  `0x108`, `out` at `0x200`;
* `tornC`: `seq_write(s, 1, 1)` ∥ two plain loads of `a`, `b` (no sequence check);
* `spscC`: `push(1); push(2); push(3)` ∥ `pop(&o0); pop(&o1)`; `head`, `tail` and the slots
  at `0x100`–`0x10c`, `o0`, `o1` at `0x200`, `0x204`.

Bounded loops make every instance finite. A run that would need a third spin iteration has no
CIR step there (it does not finish), so the final-state properties below are about the runs
within the bound.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Prim.Clients

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Robust

/-- The loop bound of the clients. -/
def L : Nat := 2

/-- Registers from a list (others zero). -/
def regs (l : List (Reg × Nat)) : Regs :=
  fun r => ((l.find? (·.1 == r)).map fun p => BitVec.ofNat 64 p.2).getD 0

/-- The critical section: `x = x + 1` with plain accesses at `0x200`. -/
def cs : List Stmt :=
  [.load .rbx .na 4 .wb (.lit 0x200),
    .store .na 4 .wb (.lit 0x200) (.bin .add (.reg .rbx) (.lit 1))]

/-! ## Locks -/

/-- A spinlock thread. -/
def spinT : Stmt := Tv.chain ([SpinLock.cert.body L] ++ cs ++ [SpinUnlock.cert.body L])

/-- **The spinlock client.** -/
def spinC : CSt :=
  start [(spinT, regs [(.rdi, 0x100)]), (spinT, regs [(.rdi, 0x100)])] [(0x100, 0), (0x200, 0)]

/-- A ticket-lock thread. -/
def tickT : Stmt := Tv.chain ([TicketLock.cert.body L] ++ cs ++ [TicketUnlock.cert.body L])

/-- **The ticket-lock client.** -/
def tickC : CSt :=
  start [(tickT, regs [(.rdi, 0x100)]), (tickT, regs [(.rdi, 0x100)])]
    [(0x100, 0), (0x104, 0), (0x200, 0)]

/-- **Mutual exclusion, observed**: the counter is `2` at the end. -/
def countIs2 (c : CSt) : Bool := memOf c.mem 0x200 == some 2

/-! ## Seqlock -/

/-- The writer: `seq_write(s, 1, 1)`. -/
def writerT : Stmt := Tv.chain [.assign .rsi (.lit 1), .assign .rdx (.lit 1), SeqWrite.cert.body L]

/-- The reader: `seq_read(s, out)`. -/
def readerT : Stmt := SeqRead.cert.body L

/-- The cells of the seqlock clients. -/
def seqMem : List (Nat × Nat) := [(0x100, 0), (0x104, 0), (0x108, 0), (0x200, 0), (0x204, 0)]

/-- **The seqlock client.** -/
def seqC : CSt :=
  start [(writerT, regs [(.rdi, 0x100)]), (readerT, regs [(.rdi, 0x100), (.rsi, 0x200)])] seqMem

/-- A reader without the protocol: two plain loads of the data words, then the output stores. -/
def tornT : Stmt := Tv.chain [SeqRead.ldA, SeqRead.ldB, SeqRead.stA, SeqRead.stB]

/-- **The seqlock writer against a reader that skips the sequence check.** -/
def tornC : CSt :=
  start [(writerT, regs [(.rdi, 0x100)]), (tornT, regs [(.rdi, 0x100), (.rsi, 0x200)])] seqMem

/-- **A consistent snapshot**: the reader's two output words are equal (the writer writes
`(1, 1)` over `(0, 0)`). -/
def snapshotOk (c : CSt) : Bool := memOf c.mem 0x200 == memOf c.mem 0x204

/-! ## SPSC ring -/

/-- `push(v)`. -/
def push (v : Nat) : List Stmt := [.assign .rsi (.lit v), SpscPush.cert.body L]

/-- `pop(out)`. -/
def pop (o : Nat) : List Stmt := [.assign .rsi (.lit o), SpscPop.cert.body L]

/-- The producer: `push(1); push(2); push(3)`. -/
def prodT : Stmt := Tv.chain (push 1 ++ push 2 ++ push 3)

/-- The consumer: `pop(&o0); pop(&o1)`. -/
def consT : Stmt := Tv.chain (pop 0x200 ++ pop 0x204)

/-- **The SPSC client.** -/
def spscC : CSt :=
  start [(prodT, regs [(.rdi, 0x100)]), (consT, regs [(.rdi, 0x100)])]
    [(0x100, 0), (0x104, 0), (0x108, 0), (0x10c, 0), (0x200, 0), (0x204, 0)]

/-- **The store-buffering outcome**: the first pop got `1`, the second pop found the ring empty
(`rax = 0` in the consumer), and the third push found it full (`rax = 0` in the producer). -/
def sbOutcome (c : CSt) : Bool :=
  ((c.th 0).2 .rax).toNat == 0 && ((c.th 1).2 .rax).toNat == 0 && memOf c.mem 0x200 == some 1

/-- **FIFO, observed**: the values the successful pops returned (the nonzero outputs; the pushed
values are nonzero) are the first values pushed, in order; `head` counts them; and
`head ≤ tail ≤ head + 2`. -/
def fifoOk (c : CSt) : Bool :=
  let o0 := (memOf c.mem 0x200).getD 0
  let o1 := (memOf c.mem 0x204).getD 0
  let h := (memOf c.mem 0x100).getD 0
  let t := (memOf c.mem 0x104).getD 0
  let got := [o0, o1].filter (· != 0)
  got == [1, 2].take got.length && h == got.length && decide (h ≤ t) && decide (t ≤ h + 2)

/-! ## Exploration budgets -/

/-- Fuel for the explorations (an upper bound on expansions; the checks verify closure). -/
def fuel : Nat := 100000

end Silmaril.X86.Concurrency.Cir.Prim.Clients
