module

public import Silmaril.X86.Concurrency.Cir.TvCfg.Defs
public import Silmaril.X86.Concurrency.Cir.Prim.Code.Defs

/-!
# The synchronisation primitives as CIR programs, with their translation-validation certificates

The four primitives of
`examples/litmus-c/sync-prims/` (a test-and-set spinlock, a ticket lock, a one-writer seqlock and
a capacity-2 SPSC ring), compiled by gcc 13.3.0 at `-O2`, pinned in `Prim.Code`, and
translation-validated into the CIR programs below (`Cir.TvCfg.tvCfg`, checked by `decide` in
`Prim/Thms.lean`).

Each function `f` has a certificate `f.cert`; its CIR program is `f.cert.body L` (every loop
bounded by `L`), which is `f.prog` below with the bounds set. The CIR programs are written in
the order of the x86 code, one CIR statement per x86 instruction with a CIR effect (`nop`,
`pause`, `jmp`, `test` and `cmp` have none; `test`/`cmp` + `je`/`jne` become the condition of
an `ite` or a `loop`). Registers are the x86 registers; a 32-bit result is masked
(`mask32`), as the x86 zero-extends it.

The C11 modes are the source's (`acq` for an acquire load or exchange, `rel` for a release
store, `rlx` for relaxed atomics, `na` for plain C accesses). The checker compares modes away:
the modes are the certificate's claim about intent, not checked against the binary.

Every memory address is `rdi + disp` (the primitive's object) or `rsi + disp` (an output
pointer), or `rdi + 4·rdx + 8` (the ring's slot).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Prim

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg

/-! ## Expressions -/

/-- `[r + d]`, as the checker writes it. -/
def at_ (r : Reg) (d : Nat) : Expr := .bin .add (.bin .add (.reg r) (.lit 0)) (.lit d)

/-- `[r + 4·i + d]`, as the checker writes it. -/
def atIdx (r i : Reg) (d : Nat) : Expr := .bin .add (.bin .add (.reg r) (idxE i 2)) (.lit d)

/-- A 32-bit register value. -/
def r32 (r : Reg) : Expr := mask32 (.reg r)

/-- The zero flag of `test r, r`: `r` is `0` (32 bits). -/
def zTest (r : Reg) : Expr := .bin .eq (mask32 (.bin .and (.reg r) (.reg r))) (.lit 0)

/-- The zero flag of `cmp a, b` (32 bits). -/
def zCmp (a b : Reg) : Expr := .bin .eq (r32 a) (r32 b)

/-- The zero flag of `cmp a, imm` (32 bits). -/
def zCmpI (a : Reg) (v : Nat) : Expr := .bin .eq (r32 a) (.lit v)

/-- `a ∘ b` at 32 bits. -/
def op32 (o : BinOp) (a : Reg) (b : Expr) : Expr := mask32 (.bin o (.reg a) b)

/-- Build a certificate entry. -/
def ent (off : Nat) (cir : List Stmt) (zf : Option Expr := none) : Entry := ⟨off, cir, zf⟩

/-! ## Test-and-set spinlock -/

namespace SpinLock

/-- `xchg [rdi], eax` (acquire). -/
def xchg : Stmt := .rmw .rax .acq 4 .xchg (at_ .rdi 0) (.reg .rax)
/-- `mov eax, edx`. -/
def movAX : Stmt := .assign .rax (r32 .rdx)
/-- `mov eax, [rdi]` (relaxed). -/
def ld : Stmt := .load .rax .rlx 4 .wb (at_ .rdi 0)
/-- The spin: `while (eax ≠ 0) eax = [rdi]`. -/
def spin : Stmt := .loop 0 (notE (zTest .rax)) ld
/-- The retry loop: `while (eax ≠ 0) { eax = [rdi]; spin; eax = edx; xchg }`. -/
def retry : Stmt := .loop 0 (notE (zTest .rax)) (Stmt.block [ld, spin, movAX, xchg])

/-- **`spin_lock` in CIR.** -/
def prog : List Stmt := [.assign .rdx (.lit 1), movAX, xchg, retry]

/-- The continuation inside the retry loop. -/
def inner : List Stmt := [ld, spin, movAX, xchg, retry]

/-- The certificate. -/
def cert : GCert where
  start := prog
  entries :=
    [ ent 0 prog, ent 5 [movAX, xchg, retry], ent 8 [movAX, xchg, retry], ent 0xa [xchg, retry],
      ent 0xc [retry], ent 0xe [retry] (some (zTest .rax)),
      ent 0x10 inner, ent 0x12 inner.tail, ent 0x14 inner.tail (some (zTest .rax)),
      ent 0x16 inner, ent 0x18 inner, ent 0x20 [] ]

end SpinLock

namespace SpinUnlock

/-- `mov dword [rdi], 0` (release). -/
def st : Stmt := .store .rel 4 .wb (at_ .rdi 0) (.lit 0)

/-- **`spin_unlock` in CIR.** -/
def prog : List Stmt := [st]

/-- The certificate. -/
def cert : GCert where
  start := prog
  entries := [ent 0 prog, ent 6 []]

end SpinUnlock

/-! ## Ticket lock -/

namespace TicketLock

/-- `lock xadd [rdi], edx`: take a ticket. -/
def take : Stmt := .rmw .rdx .rlx 4 .fadd (at_ .rdi 0) (.reg .rdx)
/-- `mov eax, [rdi+4]` (acquire): read `serving`. -/
def ld : Stmt := .load .rax .acq 4 .wb (at_ .rdi 4)
/-- The wait: `while (eax ≠ edx) eax = [rdi+4]`. -/
def wait : Stmt := .loop 0 (notE (zCmp .rax .rdx)) ld

/-- **`ticket_lock` in CIR.** -/
def prog : List Stmt := [.assign .rdx (.lit 1), take, ld, wait]

/-- The certificate. -/
def cert : GCert where
  start := prog
  entries :=
    [ ent 0 prog, ent 5 [take, ld, wait], ent 9 [ld, wait], ent 0x12 [ld, wait], ent 0x15 [wait],
      ent 0x17 [wait] (some (zCmp .rax .rdx)), ent 0x10 [ld, wait], ent 0x19 [] ]

end TicketLock

namespace TicketUnlock

/-- `mov eax, [rdi+4]` (relaxed). -/
def ld : Stmt := .load .rax .rlx 4 .wb (at_ .rdi 4)
/-- `add eax, 1`. -/
def inc : Stmt := .assign .rax (op32 .add .rax (.lit 1))
/-- `mov [rdi+4], eax` (release). -/
def st : Stmt := .store .rel 4 .wb (at_ .rdi 4) (.reg .rax)

/-- **`ticket_unlock` in CIR.** -/
def prog : List Stmt := [ld, inc, st]

/-- The certificate. -/
def cert : GCert where
  start := prog
  entries := [ent 0 prog, ent 3 [inc, st], ent 6 [st], ent 9 []]

end TicketUnlock

/-! ## Seqlock -/

namespace SeqWrite

/-- `mov eax, [rdi]` (relaxed): read `seq`. -/
def ld : Stmt := .load .rax .rlx 4 .wb (at_ .rdi 0)
/-- `lea ecx, [rax+1]`. -/
def odd : Stmt := .assign .rcx (mask32 (.bin .add (.bin .add (.reg .rax) (.lit 0)) (.lit 1)))
/-- `add eax, 2`. -/
def even : Stmt := .assign .rax (op32 .add .rax (.lit 2))
/-- `mov [rdi], ecx`: `seq` odd. -/
def stOdd : Stmt := .store .rlx 4 .wb (at_ .rdi 0) (.reg .rcx)
/-- `mov [rdi+4], esi`: data word `a`. -/
def stA : Stmt := .store .rlx 4 .wb (at_ .rdi 4) (.reg .rsi)
/-- `mov [rdi+8], edx`: data word `b`. -/
def stB : Stmt := .store .rlx 4 .wb (at_ .rdi 8) (.reg .rdx)
/-- `mov [rdi], eax` (release): `seq` even. -/
def stEven : Stmt := .store .rel 4 .wb (at_ .rdi 0) (.reg .rax)

/-- **`seq_write` in CIR.** -/
def prog : List Stmt := [ld, odd, even, stOdd, stA, stB, stEven]

/-- The certificate. -/
def cert : GCert where
  start := prog
  entries := [ ent 0 prog, ent 2 (prog.drop 1), ent 5 (prog.drop 2), ent 8 (prog.drop 3),
    ent 0xa (prog.drop 4), ent 0xd (prog.drop 5), ent 0x10 (prog.drop 6), ent 0x12 [] ]

end SeqWrite

namespace SeqRead

/-- `mov eax, [rdi]` (acquire): `seq` before. -/
def ldQ : Stmt := .load .rax .acq 4 .wb (at_ .rdi 0)
/-- `mov ecx, [rdi+4]` (relaxed): `a`. -/
def ldA : Stmt := .load .rcx .rlx 4 .wb (at_ .rdi 4)
/-- `mov edx, [rdi+8]` (relaxed): `b`. -/
def ldB : Stmt := .load .rdx .rlx 4 .wb (at_ .rdi 8)
/-- `mov r8d, [rdi]` (relaxed): `seq` after. -/
def ldR : Stmt := .load .r8 .rlx 4 .wb (at_ .rdi 0)
/-- The zero flag of `test al, 1`: `seq` was even. -/
def zEven : Expr := .bin .eq (.bin .and (.reg .rax) (.lit 1)) (.lit 0)
/-- One read of the snapshot. -/
def snap : Stmt := Stmt.block [ldQ, ldA, ldB]
/-- `while (seq odd) snap`. -/
def inner : Stmt := .loop 0 (notE zEven) snap
/-- `while (seq changed) { snap; inner; r8 = [rdi] }`. -/
def outer : Stmt := .loop 0 (notE (zCmp .r8 .rax)) (Stmt.block [snap, inner, ldR])
/-- `mov [rsi], ecx` (plain): `out[0] = a`. -/
def stA : Stmt := .store .na 4 .wb (at_ .rsi 0) (.reg .rcx)
/-- `mov [rsi+4], edx` (plain): `out[1] = b`. -/
def stB : Stmt := .store .na 4 .wb (at_ .rsi 4) (.reg .rdx)

/-- **`seq_read` in CIR.** -/
def prog : List Stmt := [ldQ, ldA, ldB, inner, ldR, outer, stA, stB]

/-- The certificate. -/
def cert : GCert where
  start := prog
  entries := [ ent 0 prog, ent 2 (prog.drop 1), ent 5 (prog.drop 2), ent 8 (prog.drop 3),
    ent 0xa (prog.drop 3) (some zEven), ent 0xc (prog.drop 4), ent 0xf (prog.drop 5),
    ent 0x12 (prog.drop 5) (some (zCmp .r8 .rax)), ent 0x14 (prog.drop 6),
    ent 0x16 (prog.drop 7), ent 0x19 [] ]

end SeqRead

/-! ## SPSC ring -/

namespace SpscPush

/-- `mov eax, [rdi+4]` (relaxed): `tail`. -/
def ldT : Stmt := .load .rax .rlx 4 .wb (at_ .rdi 4)
/-- `mov edx, [rdi]` (acquire): `head`. -/
def ldH : Stmt := .load .rdx .acq 4 .wb (at_ .rdi 0)
/-- `mov ecx, eax`. -/
def a1 : Stmt := .assign .rcx (r32 .rax)
/-- `sub ecx, edx`. -/
def a2 : Stmt := .assign .rcx (op32 .sub .rcx (.reg .rdx))
/-- `xor edx, edx`. -/
def a3 : Stmt := .assign .rdx (op32 .xor .rdx (.reg .rdx))
/-- `mov edx, eax`. -/
def b1 : Stmt := .assign .rdx (r32 .rax)
/-- `add eax, 1`. -/
def b2 : Stmt := .assign .rax (op32 .add .rax (.lit 1))
/-- `and edx, 1`. -/
def b3 : Stmt := .assign .rdx (op32 .and .rdx (.lit 1))
/-- `mov [rdi+4*rdx+8], esi` (plain): the slot. -/
def b4 : Stmt := .store .na 4 .wb (atIdx .rdi .rdx 8) (.reg .rsi)
/-- `mov edx, 1`. -/
def b5 : Stmt := .assign .rdx (.lit 1)
/-- `mov [rdi+4], eax` (release): publish `tail`. -/
def b6 : Stmt := .store .rel 4 .wb (at_ .rdi 4) (.reg .rax)
/-- `mov eax, edx`: the result. -/
def ret : Stmt := .assign .rax (r32 .rdx)
/-- The zero flag of `cmp ecx, 2`: the ring is full. -/
def zFull : Expr := zCmpI .rcx 2
/-- `if (full) {} else push`. -/
def br : Stmt := .ite zFull .skip (Stmt.block [b1, b2, b3, b4, b5, b6])

/-- **`spsc_push` in CIR.** -/
def prog : List Stmt := [ldT, ldH, a1, a2, a3, br, ret]

/-- The pushing branch's continuation. -/
def push : List Stmt := [b1, b2, b3, b4, b5, b6, ret]

/-- The certificate. -/
def cert : GCert where
  start := prog
  entries := [ ent 0 prog, ent 3 (prog.drop 1), ent 5 (prog.drop 2), ent 7 (prog.drop 3),
    ent 9 (prog.drop 4), ent 0xb (prog.drop 5), ent 0xe (prog.drop 5) (some zFull),
    ent 0x10 push, ent 0x12 (push.drop 1), ent 0x15 (push.drop 2), ent 0x18 (push.drop 3),
    ent 0x1c (push.drop 4), ent 0x21 (push.drop 5), ent 0x24 [ret], ent 0x26 [] ]

end SpscPush

namespace SpscPop

/-- `mov eax, [rdi]` (relaxed): `head`. -/
def ldH : Stmt := .load .rax .rlx 4 .wb (at_ .rdi 0)
/-- `mov ecx, [rdi+4]` (acquire): `tail`. -/
def ldT : Stmt := .load .rcx .acq 4 .wb (at_ .rdi 4)
/-- `xor edx, edx`. -/
def a1 : Stmt := .assign .rdx (op32 .xor .rdx (.reg .rdx))
/-- `mov edx, eax`. -/
def b1 : Stmt := .assign .rdx (r32 .rax)
/-- `add eax, 1`. -/
def b2 : Stmt := .assign .rax (op32 .add .rax (.lit 1))
/-- `and edx, 1`. -/
def b3 : Stmt := .assign .rdx (op32 .and .rdx (.lit 1))
/-- `mov edx, [rdi+4*rdx+8]` (plain): the slot. -/
def b4 : Stmt := .load .rdx .na 4 .wb (atIdx .rdi .rdx 8)
/-- `mov [rsi], edx` (plain): `*out`. -/
def b5 : Stmt := .store .na 4 .wb (at_ .rsi 0) (.reg .rdx)
/-- `mov edx, 1`. -/
def b6 : Stmt := .assign .rdx (.lit 1)
/-- `mov [rdi], eax` (release): publish `head`. -/
def b7 : Stmt := .store .rel 4 .wb (at_ .rdi 0) (.reg .rax)
/-- `mov eax, edx`: the result. -/
def ret : Stmt := .assign .rax (r32 .rdx)
/-- The zero flag of `cmp eax, ecx`: the ring is empty. -/
def zEmpty : Expr := zCmp .rax .rcx
/-- `if (empty) {} else pop`. -/
def br : Stmt := .ite zEmpty .skip (Stmt.block [b1, b2, b3, b4, b5, b6, b7])

/-- **`spsc_pop` in CIR.** -/
def prog : List Stmt := [ldH, ldT, a1, br, ret]

/-- The popping branch's continuation. -/
def pop : List Stmt := [b1, b2, b3, b4, b5, b6, b7, ret]

/-- The certificate. -/
def cert : GCert where
  start := prog
  entries := [ ent 0 prog, ent 2 (prog.drop 1), ent 5 (prog.drop 2), ent 7 (prog.drop 3),
    ent 9 (prog.drop 3) (some zEmpty), ent 0xb pop, ent 0xd (pop.drop 1), ent 0x10 (pop.drop 2),
    ent 0x13 (pop.drop 3), ent 0x17 (pop.drop 4), ent 0x19 (pop.drop 5), ent 0x1e (pop.drop 6),
    ent 0x20 [ret], ent 0x22 [] ]

end SpscPop

/-! ## The lock invariant (CSL) -/

/-- **The spinlock's resource invariant** for a lock word at `l` protecting `R`: either the word is
`0` and the invariant holds `R` next to it, or the word is nonzero and the holder owns `R`. -/
def lockInv (l : Nat) (R : Csl.HProp) : Csl.HProp := fun h =>
  (∃ hR, R hR ∧ Csl.Heap.Disjoint (Csl.Heap.single l 0) hR ∧
      h = Csl.Heap.union (Csl.Heap.single l 0) hR) ∨
    (∃ v, v ≠ 0 ∧ h = Csl.Heap.single l v)

/-! ## The x86 threads -/

/-- An x86 thread with the given code (base, regions and initial core are irrelevant to the
checker, which reads only the code; `TvCfg.tvCfg_code`). -/
def thr (code : List (BitVec 8)) : Tv.XThread :=
  ⟨0x1000, code, [], Silmaril.X86.Litmus.initCore 0x1000 []⟩

/-- The eight functions: name, code, certificate. -/
def all : List (String × List (BitVec 8) × GCert) :=
  [ ("spin_lock", Code.spinLock, SpinLock.cert), ("spin_unlock", Code.spinUnlock, SpinUnlock.cert),
    ("ticket_lock", Code.ticketLock, TicketLock.cert),
    ("ticket_unlock", Code.ticketUnlock, TicketUnlock.cert),
    ("seq_write", Code.seqWrite, SeqWrite.cert), ("seq_read", Code.seqRead, SeqRead.cert),
    ("spsc_push", Code.spscPush, SpscPush.cert), ("spsc_pop", Code.spscPop, SpscPop.cert) ]

end Silmaril.X86.Concurrency.Cir.Prim
