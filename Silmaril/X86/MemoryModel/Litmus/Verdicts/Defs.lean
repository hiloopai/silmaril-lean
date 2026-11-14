module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs
public import Silmaril.X86.MemoryModel.Litmus.Corpus.Defs
public import Silmaril.X86.MemoryModel.Litmus.Weak.Defs

/-!
# Litmus verdicts: trace sets of the loose-corner tests

Every x86-TSO-covered corpus test and the two plain loose corners (`MS+halves`, `MIS+straddle`)
take their traces from their **bytes** (`Test.traces`, the `Atomic9` extractor). The other six loose
corners use `movnti` or `rep stosb`, which `Atomic9` does not decode (see
`movnti_not_decoded`, `stosb_not_decoded`). They too take **every** thread from the
bytes, with the `Weak9` extractor (`Test.wtraces`, `Silmaril.X86.MemoryModel.Litmus.Weak`):
`movnti` becomes a non-temporal store, and each element of `rep stosb` a one-byte string store.

The writer traces that were transcribed by hand from the instruction text are kept below
(`Hand.*`) as a cross-check: it is proved by `decide` that each is, action for action, one of
the traces extracted from the bytes (`Weak.Thms`, `hand_writers_extracted`):

* `movntil %eax, x` (with `rax = 1`) is one 4-byte non-temporal store of `1`
  (`Flavor.nonTemporal`, so the unit is annotated `nt`);
* `rep stosb` (with `al = 1`, `rcx = n`, `rdi = x`, `DF` clear) is `n` one-byte string stores of
  `1` at `x, x + 1, ...`, in that order, each its own access (`Flavor.string`, annotated `str`);
* `sfence` is one `sfence` event; `lock addl $0, s` (with `s = 0`) is one locked
  read-modify-write of `s` reading and writing `0`; `movl $1, y` is a plain store of `1`.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

open Silmaril.X86.Litmus (Flavor Act StepRec Trace)
open Silmaril.X86.MemEvent (Event)

/-- The candidate traces of thread `k` alone, extracted from its bytes over `dom`. -/
def Test.extractThread (t : Test) (k : Nat) (dom : List Nat) : Option (List XTrace) :=
  (t.threads[k]?).bind fun th => Silmaril.X86.Litmus.extract (t.xthread k th) dom t.fuel

/-- A hand-written writer and the extracted reader (thread 1), over `dom`. -/
def Test.handWriter (t : Test) (writer : XTrace) (dom : List Nat) : Option (List (List XTrace)) :=
  (t.extractThread 1 dom).map fun rd => [[writer], rd]

namespace Hand

/-- A store action. -/
def st (fl : Flavor) (a : Nat) (bs : List Byte) : Act := ⟨⟨.store, a, bs.length, false⟩, fl, [], bs⟩

/-- An `sfence` action. -/
def sfence : Act := ⟨⟨.fence .sfence, 0, 0, false⟩, .plain, [], []⟩

/-- `lock addl $0, s` with `s = 0`: a locked read-modify-write reading and writing zero. -/
def lockAdd0 (a : Nat) : Act := ⟨⟨.rmw, a, 4, true⟩, .plain, [0, 0, 0, 0], [0, 0, 0, 0]⟩

/-- A writer trace of thread 0 of `t`: one step per instruction, the core unchanged. -/
def writer (t : Test) (steps : List (List Act)) : XTrace :=
  let s0 := ((t.threads[0]?).map fun th => (t.xthread 0 th).init).getD
    (Silmaril.X86.Litmus.initCore 0 [])
  ⟨steps.map fun acts => ⟨acts, s0⟩, s0⟩

/-- `x` and `y`. -/
abbrev x : Nat := 0x10000
abbrev y : Nat := 0x10040

/-- One store of `1` as four little-endian bytes. -/
abbrev one4 : List Byte := [1, 0, 0, 0]

/-- `MP+movnti`, thread 0: `movnti x, 1; y := 1`. -/
def mpMovnti : XTrace :=
  writer Corpus.«MP+movnti» [[st .nonTemporal x one4], [st .plain y one4]]

/-- `MP+movnti+sfence`, thread 0: `movnti x, 1; sfence; y := 1`. -/
def mpMovntiSfence : XTrace :=
  writer Corpus.«MP+movnti+sfence» [[st .nonTemporal x one4], [sfence], [st .plain y one4]]

/-- `MP+movnti+lock`, thread 0: `movnti x, 1; lock add s, 0; y := 1`. -/
def mpMovntiLock : XTrace :=
  writer Corpus.«MP+movnti+lock» [[st .nonTemporal x one4], [lockAdd0 0x10080], [st .plain y one4]]

/-- `MP+stosb`, thread 0: `rep stosb` of four bytes of `1` at `x`; `y := 1`. -/
def mpStosb : XTrace :=
  writer Corpus.«MP+stosb»
    [[st .string x [1], st .string (x + 1) [1], st .string (x + 2) [1], st .string (x + 3) [1]],
     [st .plain y one4]]

/-- `MP+stosb+sfence`, thread 0: as `mpStosb` with an `sfence` before `y := 1`. -/
def mpStosbSfence : XTrace :=
  writer Corpus.«MP+stosb+sfence»
    [[st .string x [1], st .string (x + 1) [1], st .string (x + 2) [1], st .string (x + 3) [1]],
     [sfence], [st .plain y one4]]

/-- `STOS+internal`, thread 0: `rep stosb` of two bytes of `1` at `x`. -/
def stosInternal : XTrace :=
  writer Corpus.«STOS+internal» [[st .string x [1], st .string (x + 1) [1]]]

end Hand

/-- The six loose corners whose writer uses `movnti` or `rep stosb`. -/
def weakNames : List String :=
  ["MP+movnti", "MP+movnti+sfence", "MP+movnti+lock", "MP+stosb", "MP+stosb+sfence",
    "STOS+internal"]

/-- The trace sets of the loose corners: the six with `movnti`/`rep stosb` writers extracted
over `Weak9` (`Test.wtraces`), the others over `Atomic9` (`Test.traces`). All from the bytes. -/
def Test.looseTraces (t : Test) : Option (List (List XTrace)) :=
  if t.name ∈ weakNames then t.wtraces else t.traces

/-- The check of a loose corner on its trace sets (`Test.checkLoose`: the recorded XL verdict,
TSO and SC forbid, some SC execution exists). -/
def Test.checkXlLoose (t : Test) : Bool :=
  match t.looseTraces with
  | some T => t.checkLoose T
  | none => false

/-- The check of a plain loose corner on the traces of its bytes. -/
def Test.checkPlainLooseBytes (t : Test) : Bool :=
  match t.traces with
  | some T => t.checkPlainLoose T
  | none => false

end Silmaril.X86.MemoryModel.Litmus
