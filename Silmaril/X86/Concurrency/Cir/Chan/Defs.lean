module

public import Silmaril.X86.Concurrency.Cir.Defs
public import Silmaril.X86.Concurrency.Cir.Refute.Defs

/-!
# Channels on CIR: a one-slot mailbox and an SPSC ring of capacity 2

The two protocols of `examples/litmus-c/chan/` as CIR programs, statement for statement in the shape
the compilers produce (`gcc`/`clang -O2`): every `while (LD_ACQ(c) <cond>) ;` is a **spin**
`r = load.acq c; loop n (cond r) (r = load.acq c)`, and the consumer keeps the three payloads in
registers and stores them to `r1`, `r2`, `r3` at the end.

* **Mailbox** (`mailbox n`). Locations `data`, `seq`, `ack`, `r1`–`r3`. The producer, for
  `k = 1, 2, 3`: spin until `ack = k - 1`; `data := k` (`na`); `seq := k` (`rel`). The consumer,
  for `k = 1, 2, 3`: spin until `seq = k`; read `data` (`na`); `ack := k` (`rel`).
* **Ring** (`ring n`). Locations `s0`, `s1`, `tail`, `head`, `r1`–`r3`. Message `k` lives in
  slot `(k - 1) % 2`. The producer, for `k = 1, 2, 3`: if `k > 2`, spin until `head ≥ k - 2`;
  slot `:= k` (`na`); `tail := k` (`rel`). The consumer: spin until `tail ≥ k`; read the slot
  (`na`); `head := k` (`rel`).

Every control word has one writer, so coherence on it is forced by program order; the payload
cells have one writer too. All cells are aligned 4-byte write-back locations (`uniformB`), so
no access can tear.

`n` bounds the retries of each spin. The verdicts are proved for `n = 0` (every spin succeeds at
its first read; `Cir.Chan.Thms`) and lifted to every `n` by `Task.spinRetry`, proved in
`Cir.Chan.Thms` (`spinRetry_holds`).

**Mutants** (`swapped := true`): the producer publishes the control word **before** writing the
payload. Then the consumer can see message 1 announced and read the old payload, already
under SC.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Chan

open Silmaril.X86.MemoryModel.Litmus (Test Cond Atom Loc)

/-- A 4-byte store of a constant. -/
def st (m : Mode) (a v : Nat) : Stmt := .store m 4 .wb (.lit a) (.lit v)

/-- A 4-byte store of a register. -/
def stR (m : Mode) (a : Nat) (r : Reg) : Stmt := .store m 4 .wb (.lit a) (.reg r)

/-- A 4-byte load. -/
def ld (m : Mode) (r : Reg) (a : Nat) : Stmt := .load r m 4 .wb (.lit a)

/-- **A spin**: `r = load.acq a; while (c r) r = load.acq a`, with at most `n` retries. -/
def spin (n : Nat) (r : Reg) (a : Nat) (c : Expr) : Stmt :=
  .seq (ld .acq r a) (.loop n c (ld .acq r a))

/-- The spin condition "`r ≠ k`". -/
def neq (r : Reg) (k : Nat) : Expr := .bin .ne (.reg r) (.lit k)

/-- The spin condition "`r < k`" (unsigned). -/
def ltu (r : Reg) (k : Nat) : Expr := .bin .ltu (.reg r) (.lit k)

/-- The results of the consumer. -/
abbrev r1 : Nat := 0x100c0
abbrev r2 : Nat := 0x10100
abbrev r3 : Nat := 0x10140

/-- The payload write then the publication (or, swapped, the other way round). -/
def publish (swapped : Bool) (pay ctl : Stmt) : List Stmt := if swapped then [ctl, pay] else [pay, ctl]

/-! ## Mailbox -/

namespace Mailbox

abbrev data : Nat := 0x10000
abbrev seq : Nat := 0x10040
abbrev ack : Nat := 0x10080

/-- `send(k, k)`. -/
def send (n : Nat) (swapped : Bool) (k : Nat) : List Stmt :=
  spin n .rax ack (neq .rax (k - 1)) :: publish swapped (st .na data k) (st .rel seq k)

/-- `recv(k)` into `r`. -/
def recv (n : Nat) (k : Nat) (r : Reg) : List Stmt :=
  [spin n .rax seq (neq .rax k), ld .na r data, st .rel ack k]

def producer (n : Nat) (swapped : Bool) : Stmt :=
  Stmt.block (send n swapped 1 ++ send n swapped 2 ++ send n swapped 3)

def consumer (n : Nat) : Stmt :=
  Stmt.block (recv n 1 .rcx ++ recv n 2 .rdx ++ recv n 3 .rsi ++
    [stR .na r1 .rcx, stR .na r2 .rdx, stR .na r3 .rsi])

def locs : List Loc :=
  [⟨"data", data, 4, 0⟩, ⟨"seq", seq, 4, 0⟩, ⟨"ack", ack, 4, 0⟩,
    ⟨"r1", r1, 4, 0⟩, ⟨"r2", r2, 4, 0⟩, ⟨"r3", r3, 4, 0⟩]

/-- **The mailbox program** with spin bound `n`. -/
def prog (n : Nat) (swapped : Bool := false) : Prog :=
  ⟨locs, [⟨producer n swapped, false⟩, ⟨consumer n, false⟩]⟩

end Mailbox

/-! ## SPSC ring of capacity 2 -/

namespace Ring

abbrev s0 : Nat := 0x10000
abbrev s1 : Nat := 0x10040
abbrev tail : Nat := 0x10080
abbrev head : Nat := 0x100c0

/-- The ring's results. -/
abbrev q1 : Nat := 0x10100
abbrev q2 : Nat := 0x10140
abbrev q3 : Nat := 0x10180

/-- The slot of message `k`. -/
def slot (k : Nat) : Nat := if (k - 1) % 2 = 0 then s0 else s1

/-- `send(k, k)`. -/
def send (n : Nat) (swapped : Bool) (k : Nat) : List Stmt :=
  (if k > 2 then [spin n .rax head (ltu .rax (k - 2))] else []) ++
    publish swapped (st .na (slot k) k) (st .rel tail k)

/-- `recv(k)` into `r`. -/
def recv (n : Nat) (k : Nat) (r : Reg) : List Stmt :=
  [spin n .rax tail (ltu .rax k), ld .na r (slot k), st .rel head k]

def producer (n : Nat) (swapped : Bool) : Stmt :=
  Stmt.block (send n swapped 1 ++ send n swapped 2 ++ send n swapped 3)

def consumer (n : Nat) : Stmt :=
  Stmt.block (recv n 1 .rcx ++ recv n 2 .rdx ++ recv n 3 .rsi ++
    [stR .na q1 .rcx, stR .na q2 .rdx, stR .na q3 .rsi])

def locs : List Loc :=
  [⟨"s0", s0, 4, 0⟩, ⟨"s1", s1, 4, 0⟩, ⟨"tail", tail, 4, 0⟩, ⟨"head", head, 4, 0⟩,
    ⟨"r1", q1, 4, 0⟩, ⟨"r2", q2, 4, 0⟩, ⟨"r3", q3, 4, 0⟩]

/-- **The ring program** with spin bound `n`. -/
def prog (n : Nat) (swapped : Bool := false) : Prog :=
  ⟨locs, [⟨producer n swapped, false⟩, ⟨consumer n, false⟩]⟩

end Ring

/-! ## Conditions -/

/-- The consumer received `1, 2, 3` in order: its result cells at `a`, `b`, `c` hold them. -/
def inOrder (a b c : Nat) : Cond :=
  .and (.atom (.mem a 4 1)) (.and (.atom (.mem b 4 2)) (.atom (.mem c 4 3)))

/-- The first message was received stale: its result cell holds the initial payload `0`. -/
def staleFirst (a : Nat) : Cond := .atom (.mem a 4 0)

/-- The value domain: the initial value and the three messages. -/
def dom : List Nat := [0, 1, 2, 3]

/-! ## Modes -/

/-- The accesses of a statement as (mode, address) pairs, for literal addresses. -/
def accesses : Stmt → List (Mode × Nat)
  | .load _ m _ _ (.lit a) | .store m _ _ (.lit a) _ | .rmw _ m _ _ (.lit a) _ => [(m, a)]
  | .seq s t | .ite _ s t => accesses s ++ accesses t
  | .loop _ _ b => accesses b
  | _ => []

/-- Every access to a payload cell is non-atomic (`na`), and every access to a control cell is
an acquire load or a release store: the payload is plain data protected by the protocol. -/
def modesOk (P : Prog) (payload control : List Nat) : Bool :=
  P.threads.all fun th => (accesses th.body).all fun p =>
    (!payload.contains p.2 || p.1 == .na) &&
      (!control.contains p.2 || p.1 == .acq || p.1 == .rel)

/-! ## Checker regressions

Two four-location programs on the same cells, to show that `Cir.Refute.safeCheck` is neither
trivially true nor trivially false: store buffering (SB), where TSO and XL allow both reads to
see `0`, and message passing (MP) with plain stores and loads, where TSO and XL forbid the
reader seeing the flag but not the data. -/

namespace Checks

abbrev x : Nat := 0x10000
abbrev y : Nat := 0x10040
abbrev a : Nat := 0x10080
abbrev b : Nat := 0x100c0

def locs : List Loc := [⟨"x", x, 4, 0⟩, ⟨"y", y, 4, 0⟩, ⟨"a", a, 4, 0⟩, ⟨"b", b, 4, 0⟩]

/-- SB: `x := 1; a := y` ‖ `y := 1; b := x`. -/
def sb : Prog :=
  ⟨locs, [⟨Stmt.block [st .rel x 1, ld .acq .rax y, stR .na a .rax], false⟩,
    ⟨Stmt.block [st .rel y 1, ld .acq .rax x, stR .na b .rax], false⟩]⟩

/-- SB's weak outcome excluded: not both reads `0`. -/
def sbSc : Cond := .not (.and (.atom (.mem a 4 0)) (.atom (.mem b 4 0)))

/-- MP: `x := 1; y := 1` ‖ `r := y; s := x; a := r; b := s`. -/
def mp : Prog :=
  ⟨locs, [⟨Stmt.block [st .rel x 1, st .rel y 1], false⟩,
    ⟨Stmt.block [ld .acq .rax y, ld .acq .rcx x, stR .na a .rax, stR .na b .rcx], false⟩]⟩

/-- MP's weak outcome excluded: not flag `1` with data `0`. -/
def mpOk : Cond := .not (.and (.atom (.mem a 4 1)) (.atom (.mem b 4 0)))

end Checks

/-! ## Spin retries (proved: `Cir.Chan.Thms.spinRetry_holds`) -/

/-- Set the bound of every loop to `n`. -/
def withBound (n : Nat) : Stmt → Stmt
  | .loop _ c b => .loop n c (withBound n b)
  | .seq s t => .seq (withBound n s) (withBound n t)
  | .ite c s t => .ite c (withBound n s) (withBound n t)
  | s => s

/-- A program with every loop bound set to `n`. -/
def boundProg (P : Prog) (n : Nat) : Prog :=
  ⟨P.locs, P.threads.map fun th => ⟨withBound n th.body, th.spawned⟩⟩

/-- Every loop is a spin: it follows a load of the register it reloads, from the same address
with the same mode, size and flavour. -/
def spinsOnly : Stmt → Bool
  | .seq (.load r m sz fl a) (.loop _ _ (.load r' m' sz' fl' a')) =>
    r == r' && m == m' && sz == sz' && fl == fl' && a == a'
  | .seq s t | .ite _ s t => spinsOnly s && spinsOnly t
  | .loop .. => false
  | _ => true

/-- **Spin retries are invisible** (PROVED: `Cir.Chan.spinRetry_holds`, proof in
`Silmaril/Proofs/X86/Concurrency/Cir/Chan/Spin.lean`). In a uniform program whose loops are all spins,
every behaviour with spin bound `n` is a behaviour with spin bound `0`, under SC, TSO and XL.

Why it should hold: a run with retries reads the spun-on cell several times; the last read sees
the value that ends the spin, the earlier ones are failed reads whose values are not used again
(the register is overwritten). Drop the failed reads' units from the candidate execution and
keep the last read as the spin's first load. The remaining units keep their order (`po`, `sm`
only compare positions), `rf` and `co` are unchanged on them, and no fence or locked unit is
removed, so `fencerel` and `lockXl` keep their edges among the remaining units. Every relation
of SC, TSO and XL restricted to the remaining units is contained in the relation computed on
them, so consistency is kept. The final memory (coherence-last writes) and registers are
unchanged, and the run with bound `0` exists because the kept read's value ends the spin.
The proof is the plan above: a sub-execution lemma for candidates (`Drop.cand_drop`: drop
a block of unlocked read units that each have a kept twin of the same access footprint,
renumbering positions monotonically per thread), lifted to dropping twinned plain loads from a
choice of traces (`Drop.cand_drops`), and the run correspondence for `withBound`
(`Spin.spin_run`). Tearing turned out not to need uniformity: a dropped read's twin has its
footprint, so it witnesses the same tearing. Uniformity is used only for literal addresses
(`Stmt.onCells`): with an address computed from the spun-on register the failed reads would be
at other addresses than the kept one. -/
def Task.spinRetry : Prop :=
  ∀ (P : Prog), P.uniformB = true → (P.threads.all fun th => spinsOnly th.body) = true →
    ∀ (n : Nat) (dom : List Nat) (M : Silmaril.X86.MemoryModel.Litmus.Model)
      (f : Silmaril.X86.MemoryModel.Litmus.Final),
      BehavIn (boundProg P n) dom M.Holds f → BehavIn (boundProg P 0) dom M.Holds f

end Silmaril.X86.Concurrency.Cir.Chan
