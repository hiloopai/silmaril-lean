module

public import Silmaril.X86.Concurrency.Cir.Prim.Defs
public import Silmaril.X86.Concurrency.Cir.Prim.Clients.Defs

/-!
# Mutants of the primitives' translation-validation certificates and bytes

Each mutant changes one thing that matters for concurrency, and
`Prim/Thms.lean` proves (by kernel `decide`) that the CFG checker rejects it:

* `flipCond`: `spin_lock`'s retry loop runs while the exchange returned `0` (the condition
  not negated);
* `xchgToMov`: `spin_lock`'s bytes with `xchg [rdi], eax` (`87 07`) replaced by
  `mov eax, [rdi]` (`8b 07`);
* `dropStore`: `seq_write`'s certificate without the store of the second data word;
* `noEnd`: `spin_unlock`'s certificate without its end entry;
* `wrongAddr`: `spsc_push`'s slot store at `rdi + 4·rdx + 12` instead of `+ 8`;
* `allSc` (a control, accepted: modes are free): every mode of `spin_lock`'s certificate
  set to `sc`.

A CIR-level mutant for the explorer: `ttsC`, the spinlock client with the
exchange split into a relaxed load and a relaxed store (a test-then-set lock). `Prim/Thms.lean`
proves that it loses an increment on TSO, so `spin_mutex` is not vacuous.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Prim.Mutants

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Prim
open Silmaril.X86.Concurrency.Cir.TvCfg

/-- Apply a map to every statement of a certificate. -/
def mapCert (f : Stmt → Stmt) (c : GCert) : GCert :=
  ⟨c.start.map f, c.entries.map fun e => ⟨e.off, e.cir.map f, e.zf⟩⟩

/-- Replace a statement by another, everywhere inside loops, branches and sequences. -/
def subst (a b : Stmt) : Stmt → Stmt
  | .seq x y => if sbeq (.seq x y) a then b else .seq (subst a b x) (subst a b y)
  | .ite c x y => if sbeq (.ite c x y) a then b else .ite c (subst a b x) (subst a b y)
  | .loop n c x => if sbeq (.loop n c x) a then b else .loop n c (subst a b x)
  | s => if sbeq s a then b else s

/-- The retry loop with its condition not negated. -/
def flipCond : GCert :=
  let bad : Stmt := .loop 0 (zTest .rax) (Stmt.block [SpinLock.ld, SpinLock.spin, SpinLock.movAX,
    SpinLock.xchg])
  mapCert (subst SpinLock.retry bad) SpinLock.cert

/-- `spin_lock`'s bytes with the exchange replaced by a plain load. -/
def xchgToMov : List (BitVec 8) := Code.spinLock.set 10 0x8b

/-- `seq_write` without the second data store. -/
def dropStore : GCert := mapCert (subst SeqWrite.stB .skip) SeqWrite.cert

/-- `spin_unlock` without its end entry. -/
def noEnd : GCert := ⟨SpinUnlock.cert.start, SpinUnlock.cert.entries.take 1⟩

/-- The slot store at the wrong offset. -/
def wrongAddr : GCert :=
  mapCert (subst SpscPush.b4 (.store .na 4 .wb (atIdx .rdi .rdx 12) (.reg .rsi))) SpscPush.cert

/-- Every mode `sc`. -/
def setSc : Stmt → Stmt
  | .load d _ sz fl a => .load d .sc sz fl a
  | .store _ sz fl a v => .store .sc sz fl a v
  | .rmw d _ sz op a arg => .rmw d .sc sz op a arg
  | .seq x y => .seq (setSc x) (setSc y)
  | .ite c x y => .ite c (setSc x) (setSc y)
  | .loop n c x => .loop n c (setSc x)
  | s => s

/-- `spin_lock` with every mode `sc` (control). -/
def allSc : GCert := mapCert setSc SpinLock.cert

/-! ## A CIR mutant for the explorer -/

/-- A test-then-set "lock": spin until the word reads `0`, then store `1` (no atomic exchange). -/
def ttsLock : Stmt :=
  Tv.chain [.assign .rdx (.lit 1), SpinLock.ld,
    .loop Clients.L (notE (zTest .rax)) SpinLock.ld,
    .store .rlx 4 .wb (at_ .rdi 0) (.reg .rdx)]

/-- A thread of the test-then-set client. -/
def ttsT : Stmt := Tv.chain ([ttsLock] ++ Clients.cs ++ [SpinUnlock.cert.body Clients.L])

/-- **The spinlock client with the test-then-set mutant.** -/
def ttsC : Robust.CSt :=
  Robust.start [(ttsT, Clients.regs [(.rdi, 0x100)]), (ttsT, Clients.regs [(.rdi, 0x100)])]
    [(0x100, 0), (0x200, 0)]

end Silmaril.X86.Concurrency.Cir.Prim.Mutants
