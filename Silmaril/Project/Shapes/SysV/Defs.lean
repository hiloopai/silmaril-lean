module

public import Silmaril.Project.Shapes.X86.Defs
public import Silmaril.X86.SystemV.Defs
public import Silmaril.Compiler.CompilesTo.Sim.Defs

/-!
# Standard problem shapes: System V functions, function by function

Translation validation of compiled x86-64 code one function at a time, at the System V AMD64
boundary: **this placed machine function implements that function meaning**. A *meaning* of a
function with the C signature `sig` (INTEGER-class scalars, `Silmaril.X86.SystemV.CApi`) says,
for each argument tuple, whether a call is *safe* (no undefined behaviour, and it terminates)
and which results it may return (`Meaning`). The source of a row is any meaning: a C function
under Cerberus (`Silmaril.Project.Shapes.C`), a function of an IR (`Ir`), or a specification.

| name | statement |
|---|---|
| `silmaril.shapes.sysv.implements` | `Implements M p sig frame spec`: every System V call of the function placed by `p` with arguments on which `spec` is safe returns, at its first return, a result `spec` may return, writing only the `frame` stack bytes below its entry `rsp`; the call can be entered for every argument tuple and `spec` is safe on one |
| `silmaril.shapes.sysv.implements.{open,open9,str9}` | the same on a standard model |
| `silmaril.shapes.sysv.lifts` | `Lifts M p frame I f`: the IR function `f` is a lift of the placed machine function: the machine function implements `f`, and `f` is safe on every argument tuple from which the machine returns |
| `silmaril.shapes.sysv.lifts.{open,open9,str9}` | the same on a standard model |
| `silmaril.shapes.elf.object_fn` | `ObjectFn obj fn code`: the ELF object `obj` has the function symbol `fn` in `.text`, with exactly the bytes `code` and no relocation inside them |

`Silmaril.Project.Shapes.C` adds the C side (the IR-to-C row and the composition: x86 to IR and
IR to C give x86 to C). `docs/projects/sysv-tv.md` is the guide.

## Why these hypotheses

* **Undefined behaviour is explicit.** A call is constrained only on arguments where the source
  meaning is safe (`spec.Safe a`). Source undefined behaviour therefore permits any machine
  behaviour; a source that may diverge is not covered (safety includes termination).
* **Not vacuous.** `Implements` asks that the function can be entered for every argument tuple
  (`Enterable`: some live System V entry state has the code loaded, `rip` at the entry, the
  arguments in their registers and stack slots and a usable frame) and that `spec` is safe on
  some tuple (`Meaning.Inhabited`). A spec with an unsatisfiable entry or a source that is never
  safe does not fill it.
* **True for a correct compilation.** The entry gives the machine what a caller gives a System V
  callee: the code loaded, the arguments, the return address, `rsp ≡ 8 (mod 16)`, `frame` bytes
  of readable and writable stack below `rsp` (with the return address) apart from the code.
  The contract is first-return (`FnContract.Spec.Strict`): the result is read at the
  function's own return, not at some later state of the caller.
* **The bytes are the artifact's.** `p.code` is a literal; `ObjectFn` ties it to a registered
  object file by a kernel-checked fact (`ObjectFn.of_blob`, in `Thms`), not by a tool's word.

## The IR interface

An IR (`Ir`) has functions, each with a C signature and a meaning. `SmallStep` builds one from a
small-step semantics with the System V reading of arguments (`init`) and results (`final`); the
public instances are in `Silmaril.Project.Shapes.SysV.Thms`. `Lifts` asks for more than
`Implements`: the IR must be safe wherever the machine returns (`Faithful`), so that an IR that
is undefined on all but one input is not a lift.

## Profile and limits

INTEGER-class scalar arguments and results (`int`, `unsigned`, `long`, pointers as words), the
first six in registers and the rest on the stack. The function may write only its stack frame;
functions that write caller memory, read globals or call other functions need a richer meaning
(a memory footprint and a heap model) and are not covered. The machine is a parameter
(`Silmaril.Project.Shapes.Model`).
-/

@[expose] public section

namespace Silmaril.Project.Shapes.SysV

open Silmaril.X86 (MState Word Byte FnContract)
open Silmaril.X86.SystemV.CApi (Signature Scalar Arguments ReturnValue)

/-! ## Function meanings -/

/-- **The meaning of a function with C signature `sig`** at the System V boundary: on the
argument tuple `a`, whether a call is safe (`Safe a`: no undefined behaviour and it
terminates), and which results it may return (`Returns a r`). -/
structure Meaning (sig : Signature) where
  Safe : Arguments sig.arguments → Prop
  Returns : Arguments sig.arguments → ReturnValue sig.result → Prop

/-- The meaning is safe on some argument tuple. -/
def Meaning.Inhabited {sig : Signature} (m : Meaning sig) : Prop := ∃ a, m.Safe a

/-- **`lo` refines `hi`** (total correctness, undefined behaviour permissive): on every argument
tuple where `hi` is safe, `lo` is safe, returns, and returns only results `hi` may return. -/
structure Meaning.Refines {sig : Signature} (lo hi : Meaning sig) : Prop where
  safe : ∀ a, hi.Safe a → lo.Safe a
  returns : ∀ a, hi.Safe a → ∃ r, lo.Returns a r
  sound : ∀ a r, hi.Safe a → lo.Returns a r → hi.Returns a r

/-! ## IRs -/

/-- **An IR for function-level lifting**: its functions, each with a C signature and a meaning
at the System V boundary. -/
structure Ir where
  Fn : Type
  sig : Fn → Signature
  meaning : (f : Fn) → Meaning (sig f)

/-- **An IR given by a small-step semantics**: for each function, its states, the System V
reading of an argument tuple as initial states (`init`), steps, the states that have gone wrong
(undefined behaviour or a fault), and the reading of a final state's result (`final`). -/
structure SmallStep where
  Fn : Type
  State : Type
  sig : Fn → Signature
  init : (f : Fn) → Arguments (sig f).arguments → State → Prop
  step : Fn → State → State → Prop
  wrong : Fn → State → Prop
  final : (f : Fn) → State → ReturnValue (sig f).result → Prop

/-- The runs of one function of a small-step IR, as a source semantics of the cut-point
simulation (`Silmaril.Compiler.CompilesTo.Source`). -/
def SmallStep.source (L : SmallStep) (f : L.Fn) :
    Silmaril.Compiler.CompilesTo.Source L.State (ReturnValue (L.sig f).result) where
  step := L.step f
  wrong := L.wrong f
  final := L.final f

/-- The meaning of a function of a small-step IR: safe on `a` when every initial state is
`Source.Safe` (no reachable wrong state, every run finite); `r` is a result when some initial
state runs to a final state with result `r`. -/
def SmallStep.meaning (L : SmallStep) (f : L.Fn) : Meaning (L.sig f) where
  Safe a := ∀ s, L.init f a s → (L.source f).Safe s
  Returns a r := ∃ s t, L.init f a s ∧ Relation.ReflTransGen (L.step f) s t ∧ L.final f t r

/-- A small-step IR as an IR. -/
def SmallStep.toIr (L : SmallStep) : Ir := ⟨L.Fn, L.sig, L.meaning⟩

/-! ## The machine side -/

/-- The `rsp` of a state, as a number. -/
def rspOf (m : MState) : Nat := (m.core.read .rsp).toNat

/-- The stack a call entered in `m0` may write: the `frame` bytes below its entry `rsp`. -/
def StackBelow (m0 : MState) (frame : Nat) (a : Nat) : Prop :=
  rspOf m0 - frame ≤ a ∧ a < rspOf m0

/-- **A System V call of the function placed by `p`** with C signature `sig`, arguments `a` and
`frame` bytes of stack: the region loaded and `rip` at the entry (`p.Entered`), the arguments in
their registers and stack slots (`SystemV.ArgumentsAt`), room for the frame below `rsp`, the
frame and the return address readable and writable, and the frame and the return address apart
from the code (so a write to the frame cannot change the code). The ABI obligations
(`rsp ≡ 8 (mod 16)`, a readable return address) are `FnContract.AbiEntry`, which every
contract assumes. -/
structure CallEntry (p : Placement) (sig : Signature) (frame : Nat)
    (a : Arguments sig.arguments) (m : MState) : Prop where
  entered : p.Entered m
  args : Silmaril.X86.SystemV.ArgumentsAt m a 0
  room : frame ≤ rspOf m
  read : m.memory.Permitted .read (rspOf m - frame) (frame + 8)
  write : m.memory.Permitted .write (rspOf m - frame) (frame + 8)
  apart : p.base.toNat + p.code.length ≤ rspOf m - frame ∨ rspOf m + 8 ≤ p.base.toNat

/-- **The System V contract of the placed function against `spec`**: entered by a System V
call whose arguments `spec` is safe on; writes only the frame; at the return, the result is
one `spec` may return for those arguments. -/
def sysvSpec (p : Placement) (sig : Signature) (frame : Nat) (spec : Meaning sig) :
    FnContract.Spec MState where
  entry m := ∃ a, CallEntry p sig frame a m ∧ spec.Safe a
  footprint m := StackBelow m frame
  post m t := ∀ a, Silmaril.X86.SystemV.ArgumentsAt m a 0 → spec.Safe a →
    ∃ r, spec.Returns a r ∧ Silmaril.X86.SystemV.ResultAt t sig.result r

/-- **The placed function can be entered for every argument tuple** on `M`: for each `a`, some
live state meets the System V entry obligations and is a `CallEntry` with `a`. A property of the
placement (the code fits in the address space with room for a stack), not of a source. -/
def Enterable (M : Model) (p : Placement) (sig : Signature) (frame : Nat) : Prop :=
  ∀ a, ∃ m, M.live m ∧ FnContract.AbiEntry m.core m.memory ∧ CallEntry p sig frame a m

/-- **The placed function implements `spec`** on the x86-64 model `M`: it can be entered for
every argument tuple (`Enterable`), `spec` is safe on some tuple (`Meaning.Inhabited`), and its
System V contract against `spec` holds to the first return (`ContractStrict`). -/
@[problem "silmaril.shapes.sysv.implements"
  (title := "A placed x86-64 function implements a function meaning at the System V boundary")]
def Implements (M : Model) (p : Placement) (sig : Signature) (frame : Nat)
    (spec : Meaning sig) : Prop :=
  Enterable M p sig frame ∧ spec.Inhabited ∧ ContractStrict M (sysvSpec p sig frame spec)

/-- The contract of a call with arguments `a` that only asks the function to return: entered
by a `CallEntry` with `a`, writing only the frame, no postcondition. -/
def callSpec (p : Placement) (sig : Signature) (frame : Nat)
    (a : Arguments sig.arguments) : FnContract.Spec MState where
  entry m := CallEntry p sig frame a m
  footprint m := StackBelow m frame
  post _ _ := True

/-- **The placed function returns on `a`** on `M`: every System V call with arguments `a`
reaches its first return, writing only its frame. -/
def MachineReturns (M : Model) (p : Placement) (sig : Signature) (frame : Nat)
    (a : Arguments sig.arguments) : Prop :=
  ContractStrict M (callSpec p sig frame a)

/-- **An IR meaning is faithful to the placed function**: it is safe on every argument tuple from
which the machine returns. -/
def Faithful (M : Model) (p : Placement) (sig : Signature) (frame : Nat) (m : Meaning sig) :
    Prop :=
  ∀ a, MachineReturns M p sig frame a → m.Safe a

/-- **The IR function `f` is a lift of the placed function** on `M`: the placed function
implements `f`'s meaning, and that meaning is faithful (safe wherever the machine returns). -/
@[problem "silmaril.shapes.sysv.lifts"
  (title := "An IR function is a lift of a placed x86-64 function at the System V boundary")]
def Lifts (M : Model) (p : Placement) (frame : Nat) (I : Ir) (f : I.Fn) : Prop :=
  Implements M p (I.sig f) frame (I.meaning f) ∧ Faithful M p (I.sig f) frame (I.meaning f)

/-! ## The bytes of an object file -/

/-- ASCII name bytes, as ELF symbol and section names are read. -/
def nameBytes (s : String) : List Byte := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The index and the bytes of the section named `name`. -/
def sectionOf (o : Silmaril.Formats.ELF.ObjectFile) (name : String) : Option (Nat × List Byte) :=
  o.sections.zipIdx.findSome? fun (sec, i) =>
    if sec.name == nameBytes name then some (i, sec.data.toList) else none

/-- **The object's code for `fn`**: its `.text` holds `code` at offset `off`, its symbol `fn` is
a function (`STT_FUNC`) of `.text` at `off` of size `code.length`, and no relocation patches
those bytes. A decidable check of a read object file. -/
def objectCode (o : Silmaril.Formats.ELF.ObjectFile) (fn : String) (off : Nat)
    (code : List Byte) : Bool :=
  match sectionOf o ".text" with
  | none => false
  | some (i, text) =>
    (text.drop off).take code.length == code && decide (off + code.length ≤ text.length) &&
      o.symbols.any (fun s => s.name == nameBytes fn && s.raw.sectionIndex == i &&
        s.raw.value == off && s.raw.size == code.length && s.raw.info % 16 == 2) &&
      o.relocations.all fun r =>
        r.targetSection != i || r.offset < off || off + code.length ≤ r.offset

/-- **The ELF object `obj` has the function `fn` with exactly the bytes `code`** (at some offset
of `.text`, with no relocation inside them): the public reader
`Silmaril.Formats.ELF.readObject` accepts the bytes of `obj`, and `objectCode` holds. -/
@[problem "silmaril.shapes.elf.object_fn"
  (title := "An ELF object file defines a function with given bytes and no relocations")]
def ObjectFn {V : Type} (obj : Value V) (fn : String) (code : List Byte) : Prop :=
  ∃ o off, Silmaril.Formats.ELF.readObject (Silmaril.Project.Formats.elfBytes obj.bytes) = some o ∧
    objectCode o fn off code = true

end Silmaril.Project.Shapes.SysV

end

silmaril instance silmaril.shapes.sysv.implements.open
    (title := "implements, on the open machine (Open)") :=
  silmaril.shapes.sysv.implements (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.sysv.implements.open9
    (title := "implements, on the open machine (Open9)") :=
  silmaril.shapes.sysv.implements (M := Silmaril.X86.Open9.isa)
silmaril instance silmaril.shapes.sysv.implements.str9
    (title := "implements, on the open machine with string forms (Str9)") :=
  silmaril.shapes.sysv.implements (M := Silmaril.X86.Str9.isa)
silmaril instance silmaril.shapes.sysv.lifts.open
    (title := "lifts, on the open machine (Open)") :=
  silmaril.shapes.sysv.lifts (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.sysv.lifts.open9
    (title := "lifts, on the open machine (Open9)") :=
  silmaril.shapes.sysv.lifts (M := Silmaril.X86.Open9.isa)
silmaril instance silmaril.shapes.sysv.lifts.str9
    (title := "lifts, on the open machine with string forms (Str9)") :=
  silmaril.shapes.sysv.lifts (M := Silmaril.X86.Str9.isa)
