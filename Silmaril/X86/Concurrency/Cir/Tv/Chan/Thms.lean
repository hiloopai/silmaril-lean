module

public import Silmaril.X86.Concurrency.Cir.Tv.Chan.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Spin.Thms
public import Silmaril.X86.Concurrency.Cir.Chan.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.TvChan

/-!
# Channel C programs, translation-validated: what is proved

The compiled mailbox and ring (`examples/litmus-c/chan`, gcc 13.3 and
clang 23.1.3, `-O2`) are translation-validated into CIR (`Cir.Tv.stvRun`), and everything else
is proved on the validated CIR programs. PROVED (standard axioms only), under each of SC, TSO
and XL:

* `mailbox_gcc`, `mailbox_clang`, `ring_gcc`, `ring_clang`: **for the x86 bytes**, every
  behaviour in which every spin succeeds at its first read ends with `r1, r2, r3 = 1, 2, 3`: the
  consumer receives exactly the sent values, in order;
* `*_good`: the validated CIR program has a behaviour with that outcome (non-vacuity);
* `*_stale` (mutants, payload and control stores swapped): the validated CIR program has a
  behaviour where the first message is received stale (`r1 = 0`).

With `Cir.Chan.spinRetry_holds` (proved): `all_in_order` gives the in-order
outcome for the bytes **for every spin bound `n`**, unconditionally.

Not proved: allowed outcomes do not transfer from CIR to x86 (refinement goes from x86 to CIR
only), so the mutants' stale outcome is proved for the validated CIR program and observed on
hardware for the bytes (not proved).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv.Chan

open Silmaril.X86.MemoryModel.Litmus (Model Final Cond)
open Silmaril.X86.Concurrency.Cir.Chan (boundProg spinsOnly)
open Silmaril.Proofs.X86.Concurrency.Cir.TvChan

/-- **Every spin bound** (by `Cir.Chan.spinRetry_holds`): a passing `safeOk` proves the condition of a
`forall` test for every x86 behaviour, whatever the number of spin retries. -/
theorem STest.safe_all {c : STest} (h : c.safeOk = true) (hq : c.test.quant = .forall_)
    (hb : ∀ n, c.prog n = boundProg (c.prog 0) n) (hu : (c.prog 0).uniformB = true)
    (hsp : ((c.prog 0).threads.all fun th => spinsOnly th.body) = true)
    (n : Nat) (M : Model) {f : Final}
    (hf : c.XBehav n M.Holds f) : c.test.cond.eval f = true := by
  have h' := h
  simp only [STest.safeOk, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨htv, hd⟩, _⟩, hs⟩ := h'
  obtain ⟨f', hf', hw⟩ := STest.refines htv hd hf
  rw [← cond_of_witness hq hw]
  rw [hb n] at hf'
  have h0 := Silmaril.X86.Concurrency.Cir.Chan.spinRetry_holds _ hu hsp n c.dom M f' hf'
  rw [← hb 0] at h0
  exact Refute.behavIn_safe hs M h0

/-- The mailbox compiled by gcc delivers `1, 2, 3` (spin bound `0`, SC/TSO/XL). -/
theorem mailbox_gcc (M : Model) {f : Final} (hf : «Mailbox+ok@gcc».XBehav 0 M.Holds f) :
    (Silmaril.X86.Concurrency.Cir.Chan.inOrder 0x100c0 0x10100 0x10140).eval f = true :=
  STest.safe mailbox_gcc_safe rfl M hf

/-- The mailbox compiled by clang delivers `1, 2, 3` (spin bound `0`, SC/TSO/XL). -/
theorem mailbox_clang (M : Model) {f : Final} (hf : «Mailbox+ok@clang».XBehav 0 M.Holds f) :
    (Silmaril.X86.Concurrency.Cir.Chan.inOrder 0x100c0 0x10100 0x10140).eval f = true :=
  STest.safe mailbox_clang_safe rfl M hf

/-- The ring compiled by gcc delivers `1, 2, 3` (spin bound `0`, SC/TSO/XL). -/
theorem ring_gcc (M : Model) {f : Final} (hf : «Ring+ok@gcc».XBehav 0 M.Holds f) :
    (Silmaril.X86.Concurrency.Cir.Chan.inOrder 0x10100 0x10140 0x10180).eval f = true :=
  STest.safe ring_gcc_safe rfl M hf

/-- The ring compiled by clang delivers `1, 2, 3` (spin bound `0`, SC/TSO/XL). -/
theorem ring_clang (M : Model) {f : Final} (hf : «Ring+ok@clang».XBehav 0 M.Holds f) :
    (Silmaril.X86.Concurrency.Cir.Chan.inOrder 0x10100 0x10140 0x10180).eval f = true :=
  STest.safe ring_clang_safe rfl M hf

theorem mailbox_good (M : Model) :
    (∃ f, BehavIn («Mailbox+ok@gcc».prog 0) «Mailbox+ok@gcc».dom M.Holds f ∧
      «Mailbox+ok@gcc».test.cond.eval f = true) ∧
    (∃ f, BehavIn («Mailbox+ok@clang».prog 0) «Mailbox+ok@clang».dom M.Holds f ∧
      «Mailbox+ok@clang».test.cond.eval f = true) :=
  ⟨STest.cir_witness mailbox_gcc_good M, STest.cir_witness mailbox_clang_good M⟩

theorem ring_good (M : Model) :
    (∃ f, BehavIn («Ring+ok@gcc».prog 0) «Ring+ok@gcc».dom M.Holds f ∧
      «Ring+ok@gcc».test.cond.eval f = true) ∧
    (∃ f, BehavIn («Ring+ok@clang».prog 0) «Ring+ok@clang».dom M.Holds f ∧
      «Ring+ok@clang».test.cond.eval f = true) :=
  ⟨STest.cir_witness ring_gcc_good M, STest.cir_witness ring_clang_good M⟩

/-- **Mutants**: with the stores swapped, the validated CIR program can receive the first
message stale (`r1 = 0`), for both compilers. -/
theorem mailbox_stale (M : Model) :
    (∃ f, BehavIn («Mailbox+swap@gcc».prog 0) «Mailbox+swap@gcc».dom M.Holds f ∧
      (Silmaril.X86.Concurrency.Cir.Chan.staleFirst 0x100c0).eval f = true) ∧
    (∃ f, BehavIn («Mailbox+swap@clang».prog 0) «Mailbox+swap@clang».dom M.Holds f ∧
      (Silmaril.X86.Concurrency.Cir.Chan.staleFirst 0x100c0).eval f = true) :=
  ⟨STest.cir_witness mailbox_gcc_stale M, STest.cir_witness mailbox_clang_stale M⟩

/-- **Mutants**: with the stores swapped, the validated CIR program can receive the first
message stale (`r1 = 0`), for both compilers. -/
theorem ring_stale (M : Model) :
    (∃ f, BehavIn («Ring+swap@gcc».prog 0) «Ring+swap@gcc».dom M.Holds f ∧
      (Silmaril.X86.Concurrency.Cir.Chan.staleFirst 0x10100).eval f = true) ∧
    (∃ f, BehavIn («Ring+swap@clang».prog 0) «Ring+swap@clang».dom M.Holds f ∧
      (Silmaril.X86.Concurrency.Cir.Chan.staleFirst 0x10100).eval f = true) :=
  ⟨STest.cir_witness ring_gcc_stale M, STest.cir_witness ring_clang_stale M⟩

theorem mailbox_gcc_bound (n : Nat) : «Mailbox+ok@gcc».prog n = boundProg («Mailbox+ok@gcc».prog 0) n := rfl
theorem mailbox_clang_bound (n : Nat) : «Mailbox+ok@clang».prog n = boundProg («Mailbox+ok@clang».prog 0) n := rfl
theorem ring_gcc_bound (n : Nat) : «Ring+ok@gcc».prog n = boundProg («Ring+ok@gcc».prog 0) n := rfl
theorem ring_clang_bound (n : Nat) : «Ring+ok@clang».prog n = boundProg («Ring+ok@clang».prog 0) n := rfl

theorem shapes :
    ((«Mailbox+ok@gcc».prog 0).uniformB && («Mailbox+ok@clang».prog 0).uniformB &&
      («Ring+ok@gcc».prog 0).uniformB && («Ring+ok@clang».prog 0).uniformB &&
      ((«Mailbox+ok@gcc».prog 0).threads.all fun th => spinsOnly th.body) &&
      ((«Mailbox+ok@clang».prog 0).threads.all fun th => spinsOnly th.body) &&
      ((«Ring+ok@gcc».prog 0).threads.all fun th => spinsOnly th.body) &&
      ((«Ring+ok@clang».prog 0).threads.all fun th => spinsOnly th.body)) = true := by
  decide +kernel

/-- **Every spin bound**: the four compiled channels deliver `1, 2, 3` in order, for the x86
bytes, under SC, TSO and XL. -/
theorem all_in_order (n : Nat) (M : Model)
    {f : Final} :
    («Mailbox+ok@gcc».XBehav n M.Holds f → «Mailbox+ok@gcc».test.cond.eval f = true) ∧
    («Mailbox+ok@clang».XBehav n M.Holds f → «Mailbox+ok@clang».test.cond.eval f = true) ∧
    («Ring+ok@gcc».XBehav n M.Holds f → «Ring+ok@gcc».test.cond.eval f = true) ∧
    («Ring+ok@clang».XBehav n M.Holds f → «Ring+ok@clang».test.cond.eval f = true) := by
  have hs := shapes
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hs
  exact ⟨STest.safe_all mailbox_gcc_safe rfl mailbox_gcc_bound h1 h5 n M,
    STest.safe_all mailbox_clang_safe rfl mailbox_clang_bound h2 h6 n M,
    STest.safe_all ring_gcc_safe rfl ring_gcc_bound h3 h7 n M,
    STest.safe_all ring_clang_safe rfl ring_clang_bound h4 h8 n M⟩

/-- **Modes**: in all 8 validated CIR programs the payload accesses are `na` and the
control accesses `acq`/`rel`. The checker ignores modes (`Stmt.demode`), so this records the
labelling, not a fact about the bytes. -/
theorem modes :
    ([«Mailbox+ok@gcc», «Mailbox+ok@clang», «Mailbox+swap@gcc», «Mailbox+swap@clang»].all fun c =>
        Silmaril.X86.Concurrency.Cir.Chan.modesOk (c.prog 0) [0x10000] [0x10040, 0x10080]) &&
      ([«Ring+ok@gcc», «Ring+ok@clang», «Ring+swap@gcc», «Ring+swap@clang»].all fun c =>
        Silmaril.X86.Concurrency.Cir.Chan.modesOk (c.prog 0) [0x10000, 0x10040]
          [0x10080, 0x100c0]) = true :=
  modes_ok

/-- Partial non-vacuity for the bytes: every thread of each `ok` test has an x86 trace
with spin bound `0`. That some choice of them forms an XL-consistent execution of the bytes is
not proved (it needs backward simulation). -/
theorem xtraces_nonempty' :
    ([«Mailbox+ok@gcc», «Mailbox+ok@clang», «Ring+ok@gcc», «Ring+ok@clang»].all fun c =>
      match c.xtraces 0 with
      | some T => T.length == 2 && T.all fun ts => !ts.isEmpty
      | none => false) = true :=
  xtraces_nonempty

/-! ## Checker mutants -/

/-- Flip every spin condition `≠` to `=` in the certificate. -/
def flipCond : SPiece → SPiece
  | .spin l r m a (.bin .ne x y) => .spin l r m a (.bin .eq x y)
  | p => p

/-- The test with every certificate's spin conditions flipped. -/
def mutCond (c : STest) : STest :=
  { c with certs := c.certs.map fun ct => { ct with pieces := ct.pieces.map flipCond } }

/-- The test with byte `i` of thread `k`'s code replaced by `b`. -/
def mutByte (c : STest) (k i : Nat) (b : Silmaril.X86.MemoryModel.Litmus.Byte) : STest :=
  { c with threads := c.threads.modify k fun th => { th with code := th.code.set i b } }

/-- **The checker rejects** a certificate whose spin conditions are flipped, the bytes with the
producer's first `jne` turned into `je` (`75` → `74`), and the bytes with that jump's target
moved one byte (`f5` → `f6`); it accepts the unchanged test (control). -/
theorem checker_mutants :
    (mutCond «Mailbox+ok@gcc»).tvOk = false ∧ (mutByte «Mailbox+ok@gcc» 0 9 0x74).tvOk = false ∧
      (mutByte «Mailbox+ok@gcc» 0 10 0xf6).tvOk = false ∧ «Mailbox+ok@gcc».tvOk = true := by
  decide +kernel

end Silmaril.X86.Concurrency.Cir.Tv.Chan
