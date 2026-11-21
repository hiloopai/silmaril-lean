module

public import Silmaril.X86.Concurrency.Cir.C11.Corpus.Defs

/-!
# C11 tests on CIR: mutants

Each mutant changes one thing in a validated test, and `check` must
reject it (`Cir.C11.Mutants.mutants_rejected`, kernel `decide`):

* `scStoreMov`: a plain `mov` store labelled `sc` (`SB+rlx@gcc`, thread 0's store of `x`). The
  mapping check rejects it: an `sc` store needs a locked instruction.
* `relLoad`: a `mov` load labelled `rel` (`MP+ra@gcc`). Rejected by the mapping check.
* `mpRaRlx`: `MP+ra@gcc` with its acquire load of the flag weakened to `rlx`. The modes are
  implementable and TV still passes, but RC11 now allows the witness, so the recorded verdict
  `forbidden` is rejected: the modes reach the RC11 verdict.
* `sbScAllowed`: `SB+sc@gcc` with the expected verdict flipped to `allowed`.
* `mpRlxNotStronger`: `MP+rlx@gcc` with `stronger` cleared.
* `sbFencesPlain`: `SB+fences+rlx@gcc` with the stack slot made a location of the test, so the
  locked `or 0` is an ordinary `sc` read-modify-write and no longer an SC fence: RC11 then allows
  the store-buffering witness, and the recorded `forbidden` is rejected.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.C11.Mutants

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv

/-- Replace the statements of item `j` of thread `k`'s certificate. -/
def setOps (c : C11Test) (k j : Nat) (ops : List Stmt) : C11Test :=
  { c with tv := { c.tv with certs := c.tv.certs.modify k fun ct =>
      { ct with items := ct.items.modify j fun it => { it with ops := ops } } } }

def scStoreMov : C11Test :=
  setOps Corpus.«SB+rlx@gcc» 0 0 [.store .sc 4 .wb (.lit 0x10000) (.lit 0x1)]

def relLoad : C11Test :=
  setOps Corpus.«MP+ra@gcc» 1 0 [.load .rax .rel 4 .wb (.lit 0x10040)]

def mpRaRlx : C11Test :=
  setOps Corpus.«MP+ra@gcc» 1 0 [.load .rax .rlx 4 .wb (.lit 0x10040)]

def sbScAllowed : C11Test := { Corpus.«SB+sc@gcc» with expected := .allowed }

def mpRlxNotStronger : C11Test := { Corpus.«MP+rlx@gcc» with stronger := false }

def sbFencesPlain : C11Test :=
  let c := Corpus.«SB+fences+rlx@gcc»
  { c with tv := { c.tv with test := { c.tv.test with
      locs := c.tv.test.locs ++ [⟨"sp0", 0x10800, 8, 0⟩, ⟨"sp1", 0x10840, 8, 0⟩] } } }

/-- Every mutant. -/
def all : List C11Test := [scStoreMov, relLoad, mpRaRlx, sbScAllowed, mpRlxNotStronger, sbFencesPlain]

end Silmaril.X86.Concurrency.Cir.C11.Mutants
