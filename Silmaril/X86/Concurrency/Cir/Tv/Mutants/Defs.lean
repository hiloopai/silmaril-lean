module

public import Silmaril.X86.Concurrency.Cir.Tv.Corpus.Defs

/-!
# Translation validation x86 → CIR: mutation tests

Each mutant changes either the **bytes** of one corpus thread (the
CIR program and certificate kept, with item lengths adjusted where the change alters an
instruction's length, so that the rejection is semantic and not a length mismatch) or the
**CIR program** (the bytes kept), and records whether `tvCheck` must accept it. The check
`Mutant.ok` is proved for every mutant by kernel `decide` (`Tv/Mutants/Thms.lean`).

Rejected: a dropped `mfence` (from the bytes, and from the CIR program), a dropped `lock` prefix
(`xadd`, `cmpxchg`, `inc`), swapped stores (in the bytes, and in the CIR program), a changed
stored value, a non-temporal flavour for a plain `mov`, and a `cmpxchg` whose CIR destination
is not `rax` (the hand-written `SB+lock-cmpxchgs` used `rdx`; `matchesX86` accepted it
because it compares only the observed registers). Accepted (controls): the unchanged
certificate, and the same certificate with every mode changed to `sc` (modes are not checked;
the C11 mode-mapping check is separate).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Tv.Mutants

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv
open Silmaril.X86.MemoryModel.Litmus (Test Insn)

/-- Thread `k` of a test with its instruction list changed by `f`, placed as the litmus tests place
it. -/
def mutBytes (t : Test) (k : Nat) (f : List MemoryModel.Litmus.Insn →
    List MemoryModel.Litmus.Insn) : XThread :=
  match t.threads[k]? with
  | some th => t.xthread k { th with insns := f th.insns }
  | none => t.xthread k ⟨[], []⟩

/-- Drop the first byte (a `lock` prefix) of instruction `j`. -/
def dropLock (j : Nat) (l : List MemoryModel.Litmus.Insn) : List MemoryModel.Litmus.Insn :=
  l.modify j fun i => { i with bytes := i.bytes.drop 1 }

/-- Replace item `j` of a certificate. -/
def setItem (c : Cert) (j : Nat) (it : Item) : Cert := { c with items := c.items.set j it }

/-- Set every mode of a statement to `sc`. -/
def toSc : Stmt → Stmt
  | .load d _ sz fl a => .load d .sc sz fl a
  | .store _ sz fl a v => .store .sc sz fl a v
  | .rmw d _ sz op a arg => .rmw d .sc sz op a arg
  | s => s

/-- A mutant: a thread's bytes, a certificate, and whether `tvCheck` must accept. -/
structure Mutant where
  name : String
  thread : XThread
  cert : Cert
  accept : Bool

/-- The checker gives the expected answer. -/
def Mutant.ok (m : Mutant) : Bool := tvCheck m.thread m.cert == m.accept

/-- The original thread `k` of a validated test. -/
def orig (c : TvTest) (k : Nat) : XThread := mutBytes c.test k id

/-- `movl %eax, 0x10040`. -/
def stEax : MemoryModel.Litmus.Insn :=
  ⟨"movl %eax, 0x10040", [0x89, 0x04, 0x25, 0x40, 0x00, 0x01, 0x00],
    some [⟨.store, 0x10040, 4, false⟩]⟩

/-- `RMW+lock-inc+W` thread 0 followed by `stEax`, with scratch register `d` for the
`lock inc`. -/
def incStore (d : Reg) : Cert :=
  { pro := [],
    items := [⟨8, [.rmw d .sc 4 (.op .add) (.lit 0x10000) (.lit 1)]⟩,
      ⟨7, [.store .rel 4 .wb (.lit 0x10040) (.reg .rax)]⟩] }

/-- Thread `k` of a test with its initial registers replaced. -/
def withRegs (t : Test) (k : Nat) (rs : List (Reg × Nat)) : XThread :=
  match t.threads[k]? with
  | some th => t.xthread k { th with regs := rs }
  | none => t.xthread k ⟨[], []⟩

/-- The mutants. -/
def all : List Mutant :=
  let sbm := Corpus.«SB+mfences»
  let xadd := Corpus.«RMW+lock-xadds»
  let cas := Corpus.«SB+lock-cmpxchgs»
  let inc := Corpus.«RMW+lock-inc+W»
  let mp := Corpus.«MP»
  let sb := Corpus.«SB»
  [ ⟨"SB: unchanged (control)", orig sb 0, sb.cert 0, true⟩,
    ⟨"SB: every mode sc (control)", orig sb 0,
      { sb.cert 0 with items := (sb.cert 0).items.map fun it => ⟨it.len, it.ops.map toSc⟩ },
      true⟩,
    ⟨"SB+mfences: mfence dropped from the bytes", mutBytes sbm.test 0 (·.eraseIdx 1),
      setItem (sbm.cert 0) 1 ⟨7, [.fence .mfence]⟩, false⟩,
    ⟨"SB+mfences: mfence dropped from the bytes, certificate unchanged",
      mutBytes sbm.test 0 (·.eraseIdx 1), sbm.cert 0, false⟩,
    ⟨"SB+mfences: fence dropped from the CIR program", orig sbm 0,
      setItem (sbm.cert 0) 1 ⟨3, []⟩, false⟩,
    ⟨"RMW+lock-xadds: lock prefix dropped (xadd)", mutBytes xadd.test 0 (dropLock 0),
      setItem (xadd.cert 0) 0 ⟨8, [.rmw .rax .sc 4 .fadd (.lit 0x10000) (.reg .rax)]⟩, false⟩,
    ⟨"SB+lock-cmpxchgs: lock prefix dropped (cmpxchg)", mutBytes cas.test 0 (dropLock 0),
      setItem (cas.cert 0) 0
        ⟨8, [.rmw .rax .sc 4 (.cas (.reg .rax)) (.lit 0x10000) (.reg .rcx)]⟩, false⟩,
    ⟨"RMW+lock-inc+W: lock prefix dropped (inc)", mutBytes inc.test 0 (dropLock 0),
      setItem (inc.cert 0) 0 ⟨7, [.rmw .r11 .sc 4 (.op .add) (.lit 0x10000) (.lit 1)]⟩, false⟩,
    ⟨"MP: stores swapped in the bytes", mutBytes mp.test 0 List.reverse, mp.cert 0, false⟩,
    ⟨"MP: stores swapped in the CIR program", orig mp 0,
      { mp.cert 0 with items := (mp.cert 0).items.reverse }, false⟩,
    ⟨"SB: stored value changed in the CIR program", orig sb 0,
      setItem (sb.cert 0) 0 ⟨11, [.store .rel 4 .wb (.lit 0x10000) (.lit 2)]⟩, false⟩,
    ⟨"SB: plain store given a non-temporal flavour", orig sb 0,
      setItem (sb.cert 0) 0 ⟨11, [.store .rel 4 .nt (.lit 0x10000) (.lit 1)]⟩, false⟩,
    ⟨"SB+lock-cmpxchgs: cmpxchg with destination rdx (the hand translation)", orig cas 0,
      setItem (cas.cert 0) 0
        ⟨9, [.rmw .rdx .sc 4 (.cas (.lit 0)) (.lit 0x10000) (.lit 1)]⟩, false⟩,
    -- The clobber set `K` and the fitting set `Z` are load-bearing.
    ⟨"RMW+lock-inc+W + store of rax: scratch rax then stored (K)",
      mutBytes inc.test 0 (· ++ [stEax]), incStore .rax, false⟩,
    ⟨"RMW+lock-inc+W + store of rax: scratch r11 (control)",
      mutBytes inc.test 0 (· ++ [stEax]), incStore .r11, true⟩,
    ⟨"SB+lock-cmpxchgs: 32-bit cmpxchg with rax = 2^32 (Z)",
      withRegs cas.test 0 [(.rcx, 1), (.rax, 2 ^ 32)],
      { cas.cert 0 with pro := [(.rcx, 1), (.rax, 2 ^ 32)] }, false⟩,
    ⟨"SB+lock-cmpxchgs: 32-bit cmpxchg with rax = 2^32 - 1 (control)",
      withRegs cas.test 0 [(.rcx, 1), (.rax, 2 ^ 32 - 1)],
      { cas.cert 0 with pro := [(.rcx, 1), (.rax, 2 ^ 32 - 1)] }, true⟩ ]

/-! ## Test-level mutants: the observed registers must not be clobbered -/

/-- `SB+lock-adds` with thread 0's `lock add` moved after its load of the observed `rax`, and
the CIR scratch register of that `lock add` set to `d`. -/
def sbAddsLate (d : Reg) : TvTest :=
  let c := Corpus.«SB+lock-adds»
  let perm : List MemoryModel.Litmus.Insn → List MemoryModel.Litmus.Insn := fun
    | [a, b, e] => [a, e, b]
    | l => l
  { test := { c.test with
      threads := c.test.threads.modify 0 fun th => { th with insns := perm th.insns } }
    certs := [
      { pro := [],
        items := [
          ⟨11, [.store .rel 4 .wb (.lit 0x10000) (.lit 0x1)]⟩,
          ⟨7, [.load .rax .acq 4 .wb (.lit 0x10040)]⟩,
          ⟨9, [.rmw d .sc 4 (.op .add) (.lit 0x10080) (.lit 0x0)]⟩] },
      c.cert 1] }

/-- Test-level mutants: a name, the validated test, and whether `tvOk` must hold. -/
def testMutants : List (String × TvTest × Bool) :=
  [ ("SB+lock-adds, late lock add with scratch rax (observed)", sbAddsLate .rax, false),
    ("SB+lock-adds, late lock add with scratch r11 (control)", sbAddsLate .r11, true) ]

end Silmaril.X86.Concurrency.Cir.Tv.Mutants
