module

public import Silmaril.X86.Concurrency.Cir.Tv.Chan.Defs
public import Silmaril.X86.Concurrency.Cir.Chan.Defs

/-!
# Channel C programs: per-test kernel checks

One `decide +kernel` per test: `STest.safeOk` for
the four `ok` tests (certificates, domain, extraction, and the forced-cycle safety check of the
validated CIR program), `STest.witnessOk` for the four `swap` mutants (an explicit SC execution
of the validated CIR program with a stale first message) and for the `ok` tests' in-order
outcome (non-vacuity). What they give is in `Silmaril.X86.Concurrency.Cir.Tv.Chan.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvChan

open Silmaril.X86.Concurrency.Cir.Tv Silmaril.X86.Concurrency.Cir.Tv.Chan

set_option maxHeartbeats 4000000 in
theorem mailbox_gcc_safe : «Mailbox+ok@gcc».safeOk = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem mailbox_clang_safe : «Mailbox+ok@clang».safeOk = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem ring_gcc_safe : «Ring+ok@gcc».safeOk = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem ring_clang_safe : «Ring+ok@clang».safeOk = true := by decide +kernel

theorem mailbox_gcc_good : «Mailbox+ok@gcc».witnessOk [0, 27] = true := by decide +kernel

theorem mailbox_clang_good : «Mailbox+ok@clang».witnessOk [0, 27] = true := by decide +kernel

theorem ring_gcc_good : «Ring+ok@gcc».witnessOk [0, 43] = true := by decide +kernel

theorem ring_clang_good : «Ring+ok@clang».witnessOk [0, 43] = true := by decide +kernel

theorem mailbox_gcc_stale : «Mailbox+swap@gcc».witnessOk [0, 6] = true := by decide +kernel

theorem mailbox_clang_stale : «Mailbox+swap@clang».witnessOk [0, 6] = true := by decide +kernel

theorem ring_gcc_stale : «Ring+swap@gcc».witnessOk [0, 1] = true := by decide +kernel

theorem ring_clang_stale : «Ring+swap@clang».witnessOk [0, 1] = true := by decide +kernel

/-! ## Further checks -/

open Silmaril.X86.Concurrency.Cir.Chan (modesOk) in
/-- The validated CIR programs (all 8) label the payload and result accesses `na` and the
control accesses `acq`/`rel`. Modes are free for the checker (`Stmt.demode`), so the labels
are the proposer's, but they are now the protocol's. -/
theorem modes_ok :
    ([«Mailbox+ok@gcc», «Mailbox+ok@clang», «Mailbox+swap@gcc», «Mailbox+swap@clang»].all fun c =>
        modesOk (c.prog 0) [0x10000] [0x10040, 0x10080]) &&
      ([«Ring+ok@gcc», «Ring+ok@clang», «Ring+swap@gcc», «Ring+swap@clang»].all fun c =>
        modesOk (c.prog 0) [0x10000, 0x10040] [0x10080, 0x100c0]) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- Every thread of each `ok` test has at least one x86 trace with spin bound `0`
(the bytes' hypothesis `XBehav 0` does not fail for want of per-thread traces). -/
theorem xtraces_nonempty :
    ([«Mailbox+ok@gcc», «Mailbox+ok@clang», «Ring+ok@gcc», «Ring+ok@clang»].all fun c =>
      match c.xtraces 0 with
      | some T => T.length == 2 && T.all fun ts => !ts.isEmpty
      | none => false) = true := by
  decide +kernel

end Silmaril.Proofs.X86.Concurrency.Cir.TvChan
