module
public import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Darkhttpd.N117.Default.X8664.Og.Unstripped.DarkhttpdBinary.Bytes
public import Silmaril.Project.Shapes.SysV.Defs
public import Silmaril.X86.Open.Thms
/-! Actual O0/Og byte-predicate pair; UNPROVED. Both excerpts inhabit the same
caller memory, not two complete ELF loads. No desired return, safety, refinement
or termination premise occurs in entry. This does not extend the O0 C/Core claim
to Og, nor establish full-server or hardware semantics. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence
open Silmaril.Project.Shapes
open Silmaril.X86 (MState FnContract)
def left : Silmaril.Project.Shapes.Placement := ⟨address, code, 0⟩
def rightCode : List (BitVec 8) :=
  [0x8d,0x47,0xe0,0x3c,0x5e,0x0f,0x97,0xc0,0x40,0x80,0xff,0x22,0x0f,0x94,0xc2,0x09,0xd0,0x0f,0xb6,0xc0,0xc3]
def right : Silmaril.Project.Shapes.Placement := ⟨10262, rightCode, 0⟩
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[.uint8], some .int32⟩

/-- Every byte input; arbitrary common caller registers, flags, memory and upper
56 RDI bits. Distinct RIP values select the actual bodies. No heap/global/callee. -/
def initial (input : BitVec 8) (a b : MState) : Prop :=
  SysV.CallEntry left signature 12 (.cons input .nil) a ∧
  SysV.CallEntry right signature 0 (.cons input .nil) b ∧
  a.memory = b.memory ∧
  (∀ r, a.core.read r = b.core.read r) ∧ a.core.flags = b.core.flags ∧
  Silmaril.X86.Open.isa.live a ∧ Silmaril.X86.Open.isa.live b ∧
  FnContract.AbiEntry a.core a.memory ∧ FnContract.AbiEntry b.core b.memory

/-- Compare actual EAX results. Demand each ABI return and complete memory and
mapping preservation outside O0's twelve private bytes (Og has no private frame).
Caller-clobbered registers/flags and private bytes are not compared as results. -/
def outcome (a b x y : MState) : Prop :=
  FnContract.AbiReturn a.core a.memory x.core ∧
  FnContract.AbiReturn b.core b.memory y.core ∧
  a.memory.WritesWithin x.memory (SysV.StackBelow a 12) ∧
  b.memory.WritesWithin y.memory (SysV.StackBelow b 0) ∧
  (x.core.read .rax).setWidth 32 = (y.core.read .rax).setWidth 32 ∧
  (∀ location, ¬ SysV.StackBelow a 12 location →
    x.memory.bytes.get? location = y.memory.bytes.get? location) ∧
  x.memory.regions = y.memory.regions

/-- Joint entry existence for every byte prevents empty contexts. First-return
existence and every first-return outcome are demanded, never entry assumptions. -/
@[problem "silmaril.corpus.darkhttpd.needs_logencoding.optimization_equivalence"
  (title := "Actual darkhttpd all-byte O0/Og contextual binary equivalence")]
def Task.optimization : Prop :=
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.CorpusVariants.Darkhttpd.N117.Default.X8664.O0.Unstripped.DarkhttpdBinary.F address code ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.CorpusVariants.Darkhttpd.N117.Default.X8664.Og.Unstripped.DarkhttpdBinary.F 10262 rightCode ∧
  (∀ input, ∃ a b, initial input a b) ∧
  (∀ input a b, initial input a b →
    (∃ x, FnContract.FirstReturn Silmaril.X86.Open.isa a x) ∧
    (∃ y, FnContract.FirstReturn Silmaril.X86.Open.isa b y) ∧
    ∀ x y, FnContract.FirstReturn Silmaril.X86.Open.isa a x →
      FnContract.FirstReturn Silmaril.X86.Open.isa b y → outcome a b x y)
end Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Equivalence
