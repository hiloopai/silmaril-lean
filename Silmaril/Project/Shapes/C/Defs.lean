module

public import Silmaril.Project.Shapes.SysV.Defs
public import Silmaril.Cerberus.Core.CallReach.Defs
public import Silmaril.Cerberus.Elaboration.Functions.Defs
public import Silmaril.Compiler.Native.TargetCoherence.Defs
public import Silmaril.Compiler.Native.Frontend.Defs
public import Silmaril.Compiler.Core.ParameterCallReturn.Defs
public import Silmaril.Compiler.Core.Verified.StateMem.Defs

/-!
# Standard problem shapes: C functions, their IRs and their compilations

The C side of function-by-function translation validation (`Silmaril.Project.Shapes.SysV`).
A C function has its **Cerberus meaning**: the Core procedure that the Lean port of Cerberus's
elaborator gives for its typed Ail, run by the Core dynamics
(`Silmaril.Cerberus.Core.Dynamics.Step`, concrete memory). The shapes relate it to IR functions
and to placed machine code, so that one C function can be checked against several compilations
(compilers, optimization levels), each lifted to its own IR.

| name | statement |
|---|---|
| `silmaril.shapes.c.elaborates_to` | `ElaboratesTo ail name F`: the elaborator takes the typed Ail `ail` to a file whose procedure `name` is `F`'s Core |
| `silmaril.shapes.c.ir_refines` | `IrRefines I f F`: the IR function `f` corresponds to the C function `F`: wherever `F` is safe, `f` is safe, returns, and returns only what `F` may return; and `F` is safe somewhere |
| `silmaril.shapes.c.compiles_to` | `CompilesTo M p frame F`: the placed machine function implements the C function `F` (`SysV.Implements` with `F`'s meaning) |
| `silmaril.shapes.c.compiles_to.{open,open9,str9}` | the same on a standard model |
| `silmaril.shapes.c.compiles_to.builds` | `CompilesToBuilds M F builds`: every build of the list implements `F` |

The composition is proved once (`CompilesTo.of_lift` in `Thms`): **x86 to IR and IR to C give
x86 to C**, a row of `c.compiles_to` from a row of `sysv.lifts` and a row of `c.ir_refines`.
`CompilesToBuilds.of_lifts` does it for every build of a source function.

## Same source, several builds

A row group is one source function (`CFn`: its signature and Core) and its builds (`Build`: the
compiler configuration, the placed code and its frame). Each build has its own lift
(`sysv.lifts`, a row per build, against the IR of that build); all builds share the C side
(`c.elaborates_to` once, `c.ir_refines` once per IR function).

## The Cerberus meaning (`CFn.meaning`)

* **Entry.** The Core procedure body in control with its procedure frame on a caller
  continuation `k0`, the parameters bound to `int` objects holding the argument values, under
  the invariant of the verified Core library (`Silmaril.Compile.Core.Verified.StateMem.Inv`), with
  allocator room for the body's own objects (`AllocRoom`).
* **Safe** on `a`: from every entry state, in every caller continuation, no Core run goes wrong
  (`Control.halt` other than a defined end: undefined behaviour, an `error`, an `unsupported`
  construct of the port, `abort`) and every run is finite (`Silmaril.Compiler.CompilesTo.Source.Safe`).
* **Returns** `r` on `a`: from some entry state some run returns, with only the procedure frame
  above the caller continuation, the specified integer the signature's return scalar reads as
  `r` (for a `void` result, any value).

So C undefined behaviour on `a` permits any machine behaviour on `a`; a construct the port does
not support counts as undefined, which is the conservative reading for the row's *source*
(it weakens what the row promises, never makes a correct compilation fail it).

## Assumptions

* `ElabAil`: the Lean elaborator for the LP64 target configuration
  `Silmaril.Compiler.Native.TargetCoherence.linuxLP64`, with no enums, the explicitly constructed
  conversion runtime of `Silmaril.Compiler.Core.ParameterCallReturn` (not Cerberus's `std.core`)
  and fresh symbols from 100. It is kernel-computable.
* C text to typed Ail: `FrontendAil` runs the Lean port of Cerberus's frontend; its typing pass
  uses `partial` definitions, so a row checks that step by compiled evaluation (`#guard`), and
  the shapes take the typed Ail as data.
* The profile: `int` parameters (the verified Core library's objects), an `int`-like scalar
  result, no memory beyond the parameters' objects, no calls.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.C

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.X86.SystemV.CApi (Signature Scalar Arguments ReturnValue)
open Silmaril.Project.Shapes.SysV (Meaning Ir)

/-! ## A C function as Cerberus Core -/

/-- The verified Core library's local objects. -/
abbrev Local := Silmaril.Compile.Core.Verified.StateMem.Local
/-- The definitions of the locals: each key's value as a closed `int` term. -/
abbrev Defs := Silmaril.Compile.Core.Verified.StateExpr.Key →
  Option Silmaril.Compile.Core.Verified.IntExpr.Term

/-- **A C function as Cerberus Core**: its C signature (System V INTEGER scalars), the Core
file it is part of (with the label environment and enum tags it runs under), its parameter
objects with their C types and its procedure body. -/
structure CFn (sig : Signature) where
  file : Program
  labels : Labels := ∅
  params : List (Sym × Ctype)
  body : EE

namespace CFn

variable {sig : Signature} (F : CFn sig)

/-- The label environment of the procedure body (`CallReach.bodyLabels`). -/
def bodyLabels : Labels := Silmaril.Cerberus.Core.CallReach.bodyLabels F.body

/-- The Core run of the procedure in the caller's continuation `k0`: Core's steps; a state has
gone wrong when the Core machine halts other than by a defined end; it is final when the body
has evaluated to a value with only the procedure frame on top of `k0`. -/
def source (k0 : List Frame) : Silmaril.Compiler.CompilesTo.Source State Val where
  step s t := ∃ a, Step F.file F.labels s a t
  wrong s := ∃ o, s.control = .halt o ∧ ∀ v, o ≠ .defined v
  final s v := s.control = .value v ∧ s.stack = .procedureReturn F.bodyLabels :: k0

/-- The definitions of the parameters with the argument values (literals). -/
def paramDefs (params : List (Sym × Ctype)) (args : List Int) : Defs := fun q =>
  ((params.zip args).find? fun x => x.1.1.key == q).map fun x => .lit x.2

/-- The allocator's room for the body's own objects, below the parameters' objects `ls`. -/
structure AllocRoom (mem : Mem.Concrete.State) (ls : List Local) : Prop where
  dead : ∀ id ∈ mem.dead, id < mem.nextId
  ids : ∀ l ∈ ls, l.id < mem.nextId
  addrs : ∀ l ∈ ls, mem.lastAddress ≤ l.addr
  aligned : mem.lastAddress % 4 = 0
  room : 4096 < mem.lastAddress

/-- **The Core entry** with argument values `args`: control at the body, the procedure frame on
`k0`, and the parameters the verified Core library's locals `ls` (same keys, in order) under its
invariant with the argument values as definitions, with allocator room below them. -/
def CoreEntry (k0 : List Frame) (args : List Int) (s : State) : Prop :=
  s.stack = .procedureReturn F.bodyLabels :: k0 ∧ ∃ env, s.control = .effectExpr F.body env ∧
    args.length = F.params.length ∧
    ∃ ls : List Local, ls.map (·.sym.key) = F.params.map (·.1.key) ∧
      Silmaril.Compile.Core.Verified.StateMem.Inv env s.memory ls (paramDefs F.params args) ∧
      AllocRoom s.memory ls

end CFn

/-- The mathematical values of C arguments (`Scalar.signed`). -/
def argValues : {kinds : List Scalar} → Arguments kinds → List Int
  | _, .nil => []
  | _, .cons (kind := kind) v rest => kind.signed v :: argValues rest

/-- The Core value `v` is the C result `r` of the return scalar `kind`: a specified integer
whose mathematical value is `r`'s (for `void`, any value). -/
def ValueIs : (kind : Option Scalar) → Val → ReturnValue kind → Prop
  | none, _, _ => True
  | some kind, v, r => v = .loaded (.specified (.integer (kind.signed r)))

/-- **The Cerberus meaning of a C function** (see the module docstring). -/
def CFn.meaning {sig : Signature} (F : CFn sig) : Meaning sig where
  Safe a := ∀ k0 s, F.CoreEntry k0 (argValues a) s → (F.source k0).Safe s
  Returns a r := ∃ k0 s t v, F.CoreEntry k0 (argValues a) s ∧
    Relation.ReflTransGen (F.source k0).step s t ∧ (F.source k0).final t v ∧
    ValueIs sig.result v r

/-! ## C to Core -/

/-- **The C frontend**: the Lean port of Cerberus's parser, desugarer and typing
(`Silmaril.Compiler.Native.Frontend.run`), giving the typed Ail of a C text. Checked by compiled
evaluation in a row (its typing pass is `partial`). -/
def FrontendAil (text : String) : Except String Ail.TypedProgram :=
  (Silmaril.Compiler.Native.Frontend.run text.toUTF8).map (·.program)

/-- **The elaborator** (`Silmaril.Cerberus.Elaboration.Functions.elaborate`), from typed Ail to
Core, for the LP64 configuration `TargetCoherence.linuxLP64` with no enums, the conversion
runtime of `Silmaril.Compiler.Core.ParameterCallReturn` and fresh symbols from 100. -/
def ElabAil (ail : Ail.TypedProgram) :
    Except Silmaril.Cerberus.Elaboration.State.Error Codec.FileBindings :=
  (Silmaril.Cerberus.Elaboration.Functions.elaborate
    Silmaril.Compiler.Native.TargetCoherence.linuxLP64 ⟨Map.ofList []⟩
    Silmaril.Compiler.Core.ParameterCallReturn.Example.runtime ail ⟨⟨[]⟩, 100, 100000⟩).1

/-- The procedure named `name` (by its C identifier) of an elaborated file. -/
def procedureNamed (b : Codec.FileBindings) (name : String) :
    Option (Sym × FunDecl Codec.wireModel Unit Unit) :=
  b.funs.find? fun (s, _) => s.description == .id name

/-- **The C function `name` of `ail` elaborates to `F`**: the elaborator accepts `ail`, `F`'s
file is the elaborated file, and its procedure `name` has `F`'s parameter objects (with their C
types, as the file's function information records them) and body. -/
@[problem "silmaril.shapes.c.elaborates_to"
  (title := "A C function elaborates to a given Cerberus Core procedure")]
def ElaboratesTo {sig : Signature} (ail : Ail.TypedProgram) (name : String) (F : CFn sig) :
    Prop :=
  ∃ b, ElabAil ail = .ok b ∧ F.file = b.toFile ∧
    ∃ sym loc marker ret, procedureNamed b name =
      some (sym, .procedure loc marker ret (F.params.map fun x => (x.1, BaseType.object .pointer))
        F.body) ∧
      ∃ info, b.funInfo.find? (fun e => e.1.key == sym.key) = some (sym, info) ∧
        info.2.2.2.1 = F.params.map fun x => (some x.1, x.2)

/-! ## IR to C, x86 to C, and builds -/

/-- **The IR function `f` corresponds to the C function `F`**: `f`'s meaning refines `F`'s
Cerberus meaning (wherever `F` is safe, `f` is safe, returns, and returns only what `F` may
return), and `F` is safe on some argument tuple. -/
@[problem "silmaril.shapes.c.ir_refines"
  (title := "An IR function refines a C function under its Cerberus meaning")]
def IrRefines (I : Ir) (f : I.Fn) (F : CFn (I.sig f)) : Prop :=
  (I.meaning f).Refines F.meaning ∧ F.meaning.Inhabited

/-- **The placed machine function implements the C function `F`** on `M`: function-level
translation validation of one build (`SysV.Implements` against `F`'s Cerberus meaning). -/
@[problem "silmaril.shapes.c.compiles_to"
  (title := "A placed x86-64 function implements a C function under its Cerberus meaning")]
def CompilesTo {sig : Signature} (M : Model) (p : Placement) (frame : Nat) (F : CFn sig) :
    Prop :=
  SysV.Implements M p sig frame F.meaning

/-- **One build of a source function**: the compiler configuration it was built with (for
example `gcc 14.2.0 -O2`, documentary), the placed code and the stack bytes it may write. -/
structure Build where
  config : String
  placement : Placement
  frame : Nat

/-- **Every build implements the source function**: same source, N builds. -/
@[problem "silmaril.shapes.c.compiles_to.builds"
  (title := "Every build of a C function implements it under its Cerberus meaning")]
def CompilesToBuilds {sig : Signature} (M : Model) (F : CFn sig) (builds : List Build) : Prop :=
  ∀ b ∈ builds, CompilesTo M b.placement b.frame F

end Silmaril.Project.Shapes.C

end

silmaril instance silmaril.shapes.c.compiles_to.open
    (title := "compiles_to, on the open machine (Open)") :=
  silmaril.shapes.c.compiles_to (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.c.compiles_to.open9
    (title := "compiles_to, on the open machine (Open9)") :=
  silmaril.shapes.c.compiles_to (M := Silmaril.X86.Open9.isa)
silmaril instance silmaril.shapes.c.compiles_to.str9
    (title := "compiles_to, on the open machine with string forms (Str9)") :=
  silmaril.shapes.c.compiles_to (M := Silmaril.X86.Str9.isa)
