module

public import Silmaril.Project.Shapes.C.Defs
public import Silmaril.Compiler.CompilesTo.Sim.Defs
public import Silmaril.X86.FnContract.Defs
public import Silmaril.X86.SystemV.Defs
public import Silmaril.Compiler.Core.Verified.ExitCall.Defs
public import Silmaril.Compiler.Core.Verified.Locals.Defs

/-!
# "This C compiles to this x86 code", segment by segment

What a compiler explorer shows for a C function, as statements: the C function, its Cerberus
Core (`Silmaril.Project.Shapes.C.CFn`, the C side of the System V translation-validation shapes)
and the machine code a real compiler emitted for it share numbered **program points**, and each
segment between two points is a goal. `docs/projects/compiles-to.md` is the guide;
`tools/c-tv` generates the instances from a C file and its object file.

## Three layers

1. **Generic cut-point simulation** (`Silmaril.Compiler.CompilesTo.Sim`: `Source`, `Corr`,
   `Corr.Segment`, `Corr.Whole`, and the composition theorem `Corr.whole_of_segments`).
2. **The instance for C functions** (`FnData`, `FnData.corr`, this module): the source is the
   Core procedure of a `CFn` (`Silmaril.Cerberus.Core.Dynamics.Step`, the concrete memory model)
   running until it returns to its caller's continuation `k0`; the target is an x86-64 model
   (`Silmaril.Project.Shapes.Model`, e.g. `Silmaril.X86.Open.isa`) running the function's bytes
   placed at `addr`. Points are an entry (`PointKind.entry`: the System V call), statement
   boundaries at which every C object in scope is in its DWARF frame slot (`PointKind.slots`,
   gcc `-O0`), and the return label (`PointKind.ret`, the value in `eax`).
3. **C ↔ Core** (`StmtAt`, `RetAt`, `stmtCont`): each point's Core fragment is the Core of its
   source statement, located by its `Aloc`/`Astmt` annotations in the procedure that
   `Silmaril.Project.Shapes.C.ElaboratesTo` relates to the C text.

The function-level statement is the System V shape `c.compiles_to`
(`Silmaril.Project.Shapes.C.CompilesTo`); `Silmaril.Project.Shapes.CompilesTo` proves it from the
segments.

## Undefined behaviour and the result

A source state has *gone wrong* when the Core machine halts other than by a defined end
(undefined behaviour, an `error`, an `unsupported` construct of the port, or `abort`).
`Source.Safe s` says that no run from `s` goes wrong and every run is finite. The segment
statements assume `Safe`: **source UB permits any machine behaviour**, and a source that may
diverge is not covered. The machine must return a value the source can return (the existential
over source runs), so the statements stay true for a correct compiler when Core is
nondeterministic (unsequenced operands).

## Assumptions in the statements

* the target model is a parameter (`I`); rows use `Silmaril.X86.Open.isa`;
* the entry is a System V AMD64 call (`FnContract.AbiEntry`, `Silmaril.X86.SystemV.ArgumentsAt`
  for the integer arguments) with the code loaded at `addr` and `frame` bytes of stack below
  the entry `rsp` (`StackRoom`);
* the C implementation is the elaborator's (`Silmaril.Project.Shapes.C.ElabAil`: LP64,
  `TargetCoherence.linuxLP64`, the explicitly constructed conversion runtime of
  `Silmaril.Compiler.Core.ParameterCallReturn`, not Cerberus's `std.core`);
* the result is read as the signature's return scalar (`Silmaril.X86.SystemV.Encodes`).
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo (Source Corr)


/-! ## The x86-64 side -/

/-- The open x86-64 machine state. -/
abbrev MState := Silmaril.X86.MState

/-- A byte. -/
abbrev Byte := BitVec 8

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics

/-- An x86-64 model (as `Silmaril.Project.Shapes.Model`): a segment-VC machine on the open state. -/
abbrev Model := Silmaril.X86.SegVC.Isa MState

/-- The canonical frame address (DWARF CFA) of a call entered in `m0`: the entry `rsp + 8`. -/
def cfa (m0 : MState) : Int := ((m0.core.read .rsp).toNat : Int) + 8

/-- The stack below the entry `rsp` that a function may write: `frame` bytes. -/
def StackBelow (m0 : MState) (frame : Nat) (a : Nat) : Prop :=
  (m0.core.read .rsp).toNat - frame ≤ a ∧ a < (m0.core.read .rsp).toNat

/-- Room for `frame` bytes below the entry stack pointer (no wrap-around of the frame). -/
def StackRoom (m0 : MState) (frame : Nat) : Prop := frame ≤ (m0.core.read .rsp).toNat

/-- The frame is ordinary stack memory: the `frame` bytes below the entry `rsp` are readable and
writable, and so is the return address above them. -/
def StackRW (m0 : MState) (frame : Nat) : Prop :=
  m0.memory.Permitted .read ((m0.core.read .rsp).toNat - frame) (frame + 8) ∧
    m0.memory.Permitted .write ((m0.core.read .rsp).toNat - frame) (frame + 8)

/-- The frame (the `frame` bytes below the entry `rsp` and the return address above it) and the
code at `addr` do not overlap: no write to the frame can change the code. -/
def ApartFromCode (m0 : MState) (frame addr len : Nat) : Prop :=
  addr + len ≤ (m0.core.read .rsp).toNat - frame ∨ (m0.core.read .rsp).toNat + 8 ≤ addr

/-- The value `n` (a Core integer) is the C scalar `kind` held in the low bits of `word`. -/
def WordHolds (kind : Silmaril.X86.SystemV.CApi.Scalar) (word : BitVec 64) (n : Int) : Prop :=
  ∃ w : kind.Value, Silmaril.X86.SystemV.Encodes kind w word ∧ kind.signed w = n

/-- The machine entry of a System V call of the function placed at `addr`: its bytes `code`
are loaded there, `rip` is at it, the ABI entry obligations hold, the integer arguments are in
their registers, and the stack has room for the frame. -/
structure MachineEntry (sig : Silmaril.X86.SystemV.CApi.Signature) (addr : Nat) (code : List Byte)
    (frame : Nat) (args : Silmaril.X86.SystemV.CApi.Arguments sig.arguments) (m : MState) : Prop where
  loaded : Silmaril.X86.Ext.Loaded m.memory (BitVec.ofNat 64 addr) code
  rip : m.core.rip = BitVec.ofNat 64 addr
  abi : Silmaril.X86.FnContract.AbiEntry m.core m.memory
  args : Silmaril.X86.SystemV.ArgumentsAt m args 0
  room : StackRoom m frame
  rw : StackRW m frame
  apart : ApartFromCode m frame addr code.length

/-- The machine has returned from the call entered in `m0`: `rip` at its return address and
`rsp` popped past it (`FnContract.Returned` on the open state). -/
def Returned (m0 m : MState) : Prop :=
  m.core.rip = Silmaril.X86.FnContract.retOf m0.core m0.memory ∧
    m.core.read .rsp = m0.core.read .rsp + 8#64

/-- The System V return of a call entered in `m0`, besides `rip`/`rsp`: the callee-saved
registers are restored and memory changed only in the `frame` bytes below the entry `rsp`. -/
structure ReturnFrame (frame : Nat) (m0 m : MState) : Prop where
  calleeSaved : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, m.core.read r = m0.core.read r
  writes : m0.memory.WritesWithin m.memory (StackBelow m0 frame)

/-! ## The Core side -/

/-- The verified Core library's local objects (`Silmaril.Project.Shapes.C.Local`). -/
abbrev Local := Silmaril.Project.Shapes.C.Local
/-- The definitions of the locals (`Silmaril.Project.Shapes.C.Defs`). -/
abbrev Defs := Silmaril.Project.Shapes.C.Defs

/-- Allocate an `int` object and store `n` in it, as a caller does for an argument (the
verified Core library's `Actions.created` and `Locals.stored`). -/
def argAlloc (m : Mem.Concrete.State) (n : Int) : Mem.Concrete.State :=
  Silmaril.Compile.Core.Verified.Locals.stored
    (Silmaril.Compile.Core.Verified.Actions.created .malloc [] m) m.nextId
    (Mem.Concrete.nextIntAddress m) n

/-- A C object and its machine home: the Core symbol bound to its address, its C type, the
integer scalar class of its value, its DWARF frame slot `DW_OP_fbreg off` (frame base =
CFA, gcc's `DW_OP_call_frame_cfa`) of `size` bytes, and whether it holds a value at the point
(`defined`: a parameter, or a local whose declaration with an initialiser precedes the point;
an object without one, such as a local before its initialisation, may hold anything). -/
structure Slot where
  name : String
  sym : Sym
  ty : Ctype
  kind : Silmaril.X86.SystemV.CApi.Scalar
  off : Int
  size : Nat
  defined : Bool := false

/-- The address of the slot of `o` for the call entered in `m0`: the CFA plus its offset. -/
def slotAddr (m0 : MState) (o : Slot) : Nat := (cfa m0 + o.off).toNat

/-- The slot of `o` holds the Core integer `n` (in `m`, for the call entered in `m0`): its
`size` bytes are the little-endian bytes of `n` (`Ext.HoldsLE`, two's complement). -/
def SlotHolds (m0 m : MState) (o : Slot) (n : Int) : Prop :=
  Silmaril.X86.Ext.HoldsLE m.memory (slotAddr m0 o) o.size (BitVec.ofInt 64 n)

/-- **Every object in scope is in its slot**: the Core objects of `objs` are the verified Core
library's locals `ls` (same keys, in order) under its invariant (`StateMem.Inv`: every symbol of
a local's key is bound to it in `env`, the objects are live 4-byte `int`s with pairwise disjoint
bytes, and each definition `d` of `ds` is in its local's bytes with `d.Ok 0`), the allocator has
room (`ExitCall.Budget`), every object marked `defined` has a definition, and each definition is
in the object's frame slot. -/
def ObjectsAgree (env : Env) (mem : Mem.Concrete.State) (objs : List Slot) (m0 m : MState) :
    Prop :=
  ∃ (ls : List Local) (ds : Defs),
    Silmaril.Compile.Core.Verified.StateMem.Inv env mem ls ds ∧
    Silmaril.Compile.Core.Verified.ExitCall.Budget mem ∧
    ls.map (·.sym.key) = objs.map (·.sym.key) ∧
    ∀ o ∈ objs, (o.defined = true → (ds o.sym.key).isSome = true) ∧
      ∀ d, ds o.sym.key = some d → SlotHolds m0 m o (d.val 0)

/-- The environment `env₀` of a pending continuation binds the objects' symbols as `env` does
(the statement in control may have bound fresh symbols since). -/
def SameObjects (objs : List Slot) (env₀ env : Env) : Prop :=
  ∀ o ∈ objs, ∀ y : Sym, y.key = o.sym.key → env₀.lookup y = env.lookup y

/-- The frame of a leaf function compiled by gcc `-O0`, after its prologue
(`push %rbp; mov %rsp,%rbp`), relative to the entry state `m0`: the code is still loaded,
`rbp = rsp = entry rsp - 8`, the caller's `rbp` is saved there, the other callee-saved
registers are unchanged, and memory changed only in the `frame` bytes below the entry `rsp`
(the saved `rbp` and the red zone the slots live in). -/
structure Frame0 (addr : Nat) (code : List Byte) (frame : Nat) (m0 m : MState) : Prop where
  loaded : Silmaril.X86.Ext.Loaded m.memory (BitVec.ofNat 64 addr) code
  abi : Silmaril.X86.FnContract.AbiEntry m0.core m0.memory
  room : StackRoom m0 frame
  rw : StackRW m0 frame
  apart : ApartFromCode m0 frame addr code.length
  rbp : m.core.read .rbp = m0.core.read .rsp - 8#64
  rsp : m.core.read .rsp = m0.core.read .rsp - 8#64
  savedRbp : m.memory.readBytes ((m0.core.read .rsp).toNat - 8) 8 =
    some (Silmaril.Machine.LittleEndian.encodeWords [m0.core.read .rbp])
  calleeSaved : ∀ r ∈ [Silmaril.X86.Reg.rbx, .r12, .r13, .r14, .r15],
    m.core.read r = m0.core.read r
  writes : m0.memory.WritesWithin m.memory (StackBelow m0 frame)

/-- The return register holds the Core return value `v` read as the scalar `kind` (for
`void`, nothing): `v` is a specified integer `n` and `rax` holds `n` (`WordHolds`). -/
def ResultAt : Option Silmaril.X86.SystemV.CApi.Scalar → Val → MState → Prop
  | none, _, _ => True
  | some kind, v, m => ∃ n, v = .loaded (.specified (.integer n)) ∧
      WordHolds kind (m.core.read .rax) n

/-! ## A function's correspondence -/

/-- The kind of a program point, with the relation between Core and machine states there. -/
inductive PointKind where
  /-- The function's entry: the Core procedure body with its parameters bound, the machine in
  a System V entry state at the function's address. -/
  | entry
  /-- A statement boundary at `-O0`: the Core continuation of the statement is `cont` (the
  pattern and right-hand side of the innermost sequence it is the left side of, and whether the
  sequence is strong: `StmtCont`, pushed in an environment that binds the objects as the current
  one does), and every object in `objs` is in its frame slot. -/
  | slots (cont : Option (Pattern Sym × EE × Bool)) (objs : List Slot)
  /-- The return label at `-O0`: its parameter `ret` holds the returned value, which is in
  `eax`. -/
  | ret (sym : Sym)

/-- A program point: the Core fragment in control there (`Control.effectExpr frag env`), the
offset of the machine address from the function's address, and its kind. -/
structure Point where
  frag : EE
  off : Nat
  kind : PointKind

/-- **A C function and the code compiled for it**: its C signature (System V INTEGER scalars);
its Cerberus Core (`cfn`: the file, the procedure's parameters with their C types and its body,
the C side of the System V shapes); the bytes placed at `addr`; the stack bytes below the entry
`rsp` it may write; its program points (`points[0]` is the entry). -/
structure FnData where
  sig : Silmaril.X86.SystemV.CApi.Signature
  cfn : Silmaril.Project.Shapes.C.CFn sig
  addr : Nat
  code : List Byte
  frame : Nat
  points : List Point

namespace FnData

variable (F : FnData)

/-! The C side, from `F.cfn`. -/

/-- The Core file. -/
abbrev file : Program := F.cfn.file
/-- The label environment the Core runs under. -/
abbrev labels : Labels := F.cfn.labels
/-- The parameter objects with their C types. -/
abbrev params : List (Sym × Ctype) := F.cfn.params
/-- The procedure body. -/
abbrev body : EE := F.cfn.body
/-- The label environment of the procedure body (`CFn.bodyLabels`). -/
abbrev bodyLabels : Labels := F.cfn.bodyLabels
/-- The Core run of the procedure in the caller's continuation `k0` (`CFn.source`). -/
abbrev source (k0 : List Frame) : Source State Val := F.cfn.source k0
/-- The Core entry (`CFn.CoreEntry`). -/
abbrev CoreEntry (k0 : List Frame) (args : List Int) (s : State) : Prop :=
  F.cfn.CoreEntry k0 args s
/-- The definitions of the parameters with the argument values (`CFn.paramDefs`). -/
abbrev paramDefs := Silmaril.Project.Shapes.C.CFn.paramDefs
/-- The allocator's room for the body's own objects (`CFn.AllocRoom`). -/
abbrev AllocRoom := Silmaril.Project.Shapes.C.CFn.AllocRoom
/-- The mathematical values of the C arguments (`Silmaril.Project.Shapes.C.argValues`). -/
abbrev argValues := @Silmaril.Project.Shapes.C.argValues

/-- The function's placement for the System V shapes: its bytes at `addr`, entered at their
start. -/
def placement : Silmaril.Project.Shapes.Placement := ⟨BitVec.ofNat 64 F.addr, F.code, 0⟩

/-- A frame a Core jump stops at (`Dynamics.hasBoundary`). -/
def Boundary : Frame → Prop
  | .procedureReturn _ => True
  | .globalResult _ _ _ _ _ => True
  | _ => False

/-- The frame a statement's sequencing continuation pushes, in the environment `env`. -/
def contFrames : Option (Pattern Sym × EE × Bool) → Env → List Frame
  | some (p, b, true), env => [.strongBind p b env]
  | some (p, b, false), env => [.effectBind p b env]
  | none, _ => []

/-- The relation at a point of kind `kind`, for the call entered in `m0`. -/
def Holds (k0 : List Frame) : PointKind → MState → State → MState → Prop
  | .entry, m0, s, m => m = m0 ∧ ∃ args : Silmaril.X86.SystemV.CApi.Arguments F.sig.arguments,
      MachineEntry F.sig F.addr F.code F.frame args m0 ∧ F.CoreEntry k0 (argValues args) s
  | .slots cont objs, m0, s, m => Frame0 F.addr F.code F.frame m0 m ∧
      ∃ E env env₀ J, s.control = .effectExpr E env ∧
        s.stack = contFrames cont env₀ ++ J ++ .procedureReturn F.bodyLabels :: k0 ∧
        (∀ f ∈ J, ¬ Boundary f) ∧ SameObjects objs env₀ env ∧ ObjectsAgree env s.memory objs m0 m
  | .ret sym, m0, s, m => Frame0 F.addr F.code F.frame m0 m ∧
      s.stack = .procedureReturn F.bodyLabels :: k0 ∧
      ∃ E env, s.control = .effectExpr E env ∧ ∃ kind n, F.sig.result = some kind ∧
        env.lookup sym = some (.loaded (.specified (.integer n))) ∧
        WordHolds kind (m.core.read .rax) n

/-- The machine's result for a Core return value `v`: the System V return frame, and, for a
scalar result, `v` is a specified integer that the return register holds (for `void`,
nothing). As `Silmaril.Project.Shapes.C.ValueIs`, an unspecified or non-integer value is no
result of a scalar function. -/
def Result (m0 : MState) (v : Val) (m : MState) : Prop :=
  ReturnFrame F.frame m0 m ∧ ResultAt F.sig.result v m

/-- **The correspondence** of the function, in the caller's continuation `k0`, on the model `I`. -/
def corr (I : Model) (k0 : List Frame) : Corr State MState Val where
  src := F.source k0
  tgt := I.step
  srcAt k s := ∃ p, F.points[k]? = some p ∧ ∃ env, s.control = .effectExpr p.frag env
  tgtAt k m := ∃ p, F.points[k]? = some p ∧ (I.core m).rip = BitVec.ofNat 64 (F.addr + p.off)
  rel k m0 s m := ∃ p, F.points[k]? = some p ∧ F.Holds k0 p.kind m0 s m
  tgtFinal m0 m := Returned m0 m
  result m0 v m := F.Result m0 v m

/-- **The segment at point `k` is simulated** on `I`, in every caller continuation. -/
def Segment (I : Model) (k : Nat) : Prop := ∀ k0, (F.corr I k0).Segment k

/-- **End to end** on `I`: from every System V call (with the Core procedure entered with the
same arguments in any caller continuation), if the Core run cannot go wrong and terminates, the
machine returns, and its result corresponds to a value the Core procedure returns. The
composition of the segments (`FnData.whole_of_segments`); the System V shape `c.compiles_to`
asks more (the first return, every argument tuple: `Silmaril.Project.Shapes.CompilesTo`). -/
def Whole (I : Model) : Prop := ∀ k0, (F.corr I k0).Whole 0

end FnData

/-! ## C ↔ Core -/

/-! The C function itself, its typed Ail and the elaborator are the C side of the System V
shapes (`Silmaril.Project.Shapes.C`: `FrontendAil`, `ElabAil`, `procedureNamed`,
`ElaboratesTo`). A point adds which statement of the procedure body its Core fragment is. -/

/-! ### Locating a point's Core fragment -/

/-- The source location of an expression, if its annotations carry one. -/
def exprLoc (e : EE) : Option Loc :=
  match e with
  | .mk annots _ => annots.findSome? fun | .loc l => some l | _ => none

/-- The first line of a location. -/
def firstLine : Loc → Option Int
  | .point _ line _ => some line
  | .region _ line _ _ _ _ => some line
  | _ => none

mutual
/-- Every sub-expression of `e`, `e` first (pre-order), through the sequencing, binding,
branching, label and grouping forms. -/
def subexprs : EE → List EE
  | e@(.mk _ node) => e :: subexprsNode node
/-- The sub-expressions below a node. -/
def subexprsNode : ExprNode Codec.wireModel Unit Unit Sym → List EE
  | .sseq _ a b | .wseq _ a b | .if_ _ a b => subexprs a ++ subexprs b
  | .let_ _ _ a | .bound a | .save _ _ a | .annot _ a => subexprs a
  | .case_ _ bs => subexprsCases bs
  | .unseq es | .nd es | .par es => subexprsList es
  | _ => []
/-- The sub-expressions of a list. -/
def subexprsList : List EE → List EE
  | [] => []
  | e :: es => subexprs e ++ subexprsList es
/-- The sub-expressions of case arms. -/
def subexprsCases : List (Pattern Sym × EE) → List EE
  | [] => []
  | (_, e) :: es => subexprs e ++ subexprsCases es
end

/-- The expression is a statement (annotation `Astmt`) located at `line`. -/
def isStmtAt (line : Int) (e : EE) : Bool :=
  match e with
  | .mk annots _ =>
    annots.any (fun | .stmt => true | _ => false) &&
      (exprLoc e).bind firstLine == some line

/-- The Core statements located at `line` in `body`, outermost first. -/
def stmtsAt (body : EE) (line : Int) : List EE := (subexprs body).filter (isStmtAt line)

mutual
/-- The sequencing continuation of the statement at `line` below `e`, given the continuation
`acc` of `e` itself: the innermost `sseq`/`wseq` whose left side holds it, through branches,
`let` and `case` bodies and `save` bodies (which push no frame). `none` when there is no
statement at `line`; `some none` when it has no enclosing sequence. -/
def contAt (line : Int) (acc : Option (Pattern Sym × EE × Bool)) :
    EE → Option (Option (Pattern Sym × EE × Bool))
  | e@(.mk _ node) => if isStmtAt line e then some acc else contAtNode line acc node
/-- `contAt` below a node. -/
def contAtNode (line : Int) (acc : Option (Pattern Sym × EE × Bool)) :
    ExprNode Codec.wireModel Unit Unit Sym → Option (Option (Pattern Sym × EE × Bool))
  | .sseq p a b => (contAt line (some (p, b, true)) a).or (contAt line acc b)
  | .wseq p a b => (contAt line (some (p, b, false)) a).or (contAt line acc b)
  | .if_ _ a b => (contAt line acc a).or (contAt line acc b)
  | .let_ _ _ a | .save _ _ a => contAt line acc a
  | .case_ _ bs => contAtCases line acc bs
  | _ => none
/-- `contAt` in case arms. -/
def contAtCases (line : Int) (acc : Option (Pattern Sym × EE × Bool)) :
    List (Pattern Sym × EE) → Option (Option (Pattern Sym × EE × Bool))
  | [] => none
  | (_, e) :: es => (contAt line acc e).or (contAtCases line acc es)
end

/-- The sequencing continuation of the statement at `line` of `body` (`none` if there is none
or no such statement). -/
def stmtCont (body : EE) (line : Int) : Option (Pattern Sym × EE × Bool) :=
  (contAt line none body).getD none

/-- **The point's fragment is the Core of the statement at `line`** (C ↔ Core, segment level):
it is the only Core statement located there. -/
def StmtAt (body : EE) (line : Int) (frag : EE) : Prop := stmtsAt body line = [frag]

/-- The return labels of `body`: each `save` annotated `Alabel LAreturn`, with its parameters
and body. -/
def returnSaves (body : EE) : List (Sym × List Sym × EE) :=
  (subexprs body).filterMap fun
    | .mk annots (.save (l, _) ps b) =>
      if annots.any (fun | .label .return_ => true | _ => false) then
        some (l, ps.map Prod.fst, b) else none
    | _ => none

/-- **The point is the procedure's return label** (C ↔ Core, the closing brace): `body` has one
return label, with the single parameter `sym` and the body `frag`. -/
def RetAt (body : EE) (sym : Sym) (frag : EE) : Prop :=
  ∃ l, returnSaves body = [(l, [sym], frag)]

/-! ### Return-label names

The elaborator names a procedure's return label `s!"ret_{n}"`
(`Functions.Defs`, `Sym.description`, which Cerberus uses only for printing). A Core document
quoted from text carries the evaluated string, which the kernel cannot match against
`s!"ret_{n}"` from outside the module that defines `Nat.repr`. `fixRet` rewrites the description
of every return label (and of every `run` to it) back to `s!"ret_{n}"`, so the quoted file and
the elaborator's output are the same term. Symbols are compared by `Sym.key`, so this changes
no Core behaviour. -/

/-- The return label's own description, as the elaborator writes it. -/
def retLabelSym (keys : List (Digest × Nat)) (s : Sym) : Sym :=
  if keys.contains s.key then { s with description := .id s!"ret_{s.number}" } else s

mutual
/-- `retLabelSym` on every `save` label and `run` target of an expression. -/
def fixRetE (keys : List (Digest × Nat)) : EE → EE
  | .mk a node => .mk a (fixRetN keys node)
/-- `fixRetE` below a node. -/
def fixRetN (keys : List (Digest × Nat)) :
    ExprNode Codec.wireModel Unit Unit Sym → ExprNode Codec.wireModel Unit Unit Sym
  | .sseq p x y => .sseq p (fixRetE keys x) (fixRetE keys y)
  | .wseq p x y => .wseq p (fixRetE keys x) (fixRetE keys y)
  | .if_ c x y => .if_ c (fixRetE keys x) (fixRetE keys y)
  | .let_ p e x => .let_ p e (fixRetE keys x)
  | .bound x => .bound (fixRetE keys x)
  | .annot d x => .annot d (fixRetE keys x)
  | .save (l, t) ps x => .save (retLabelSym keys l, t) ps (fixRetE keys x)
  | .run a l ps => .run a (retLabelSym keys l) ps
  | .case_ c bs => .case_ c (fixRetCases keys bs)
  | .unseq es => .unseq (fixRetList keys es)
  | .nd es => .nd (fixRetList keys es)
  | .par es => .par (fixRetList keys es)
  | n => n
/-- `fixRetE` on a list. -/
def fixRetList (keys : List (Digest × Nat)) : List EE → List EE
  | [] => []
  | e :: es => fixRetE keys e :: fixRetList keys es
/-- `fixRetE` on case arms. -/
def fixRetCases (keys : List (Digest × Nat)) :
    List (Pattern Sym × EE) → List (Pattern Sym × EE)
  | [] => []
  | (p, e) :: es => (p, fixRetE keys e) :: fixRetCases keys es
end

/-- `fixRetE` on a procedure, for the keys of its own return labels. -/
def fixRetDecl : FunDecl Codec.wireModel Unit Unit → FunDecl Codec.wireModel Unit Unit
  | .procedure loc m ret ps body =>
    .procedure loc m ret ps (fixRetE ((returnSaves body).map (·.1.key)) body)
  | d => d

/-- `fixRetDecl` on every procedure of a file. -/
def fixRet (b : Codec.FileBindings) : Codec.FileBindings :=
  { b with funs := b.funs.map fun (s, d) => (s, fixRetDecl d) }

/-! ### Reading a procedure out of an elaborated file -/

/-- A placeholder fragment, never a located statement: the fragment of a point whose Core
statement was not found (no state is at such a point). -/
def noFrag : EE := .mk [] (.pure (.mk [] () (.val .unit)))

/-- The parameters and body of the procedure `name`. -/
def procParts (b : Codec.FileBindings) (name : String) : List (Sym × BaseType) × EE :=
  match Silmaril.Project.Shapes.C.procedureNamed b name with
  | some (_, .procedure _ _ _ ps body) => (ps, body)
  | _ => ([], noFrag)

/-- The parameter objects of the procedure `name` with their C types (the file's function
information). -/
def paramsOf (b : Codec.FileBindings) (name : String) : List (Sym × Ctype) :=
  match Silmaril.Project.Shapes.C.procedureNamed b name with
  | some (sym, _) =>
    match b.funInfo.find? (fun e => e.1.key == sym.key) with
    | some (_, (_, _, _, ps, _, _)) => ps.filterMap fun (s, ty) => s.map (·, ty)
    | none => []
  | none => []

/-- The fragment of the statement at `line`, if it is the only one there. -/
def stmtFrag (body : EE) (line : Int) : EE :=
  match stmtsAt body line with
  | [e] => e
  | _ => noFrag

/-- The body of the procedure's return label, if it has exactly one. -/
def retFrag (body : EE) : EE :=
  match returnSaves body with
  | [(_, [_], e)] => e
  | _ => noFrag

/-- The parameter of the procedure's return label, if it has exactly one. -/
def retParam (body : EE) : Sym :=
  match returnSaves body with
  | [(_, [s], _)] => s
  | _ => ⟨⟨[]⟩, 0, .none⟩

/-- The C type `int` (no annotations). -/
def intTy : Ctype := .mk [] (.basic (.integer (.signed .int)))

/-- The C type `unsigned int` (no annotations). -/
def uintTy : Ctype := .mk [] (.basic (.integer (.unsigned .int)))

/-! ## The decoder -/

/-! The object's bytes are tied to the registered object file by the shape `elf.object_fn`
(`Silmaril.Project.Shapes.SysV.ObjectFn`, proved with `ObjectFn.of_blob`). -/

/-- **`code` is the listing `L`** (checked by kernel evaluation): from offset `pos`, each entry
`(offset, instruction, length)` starts where the previous one ended, the model's decoder
`Silmaril.X86.Ext.decode` reads exactly that instruction and length there, and the listing ends
at the end of `code`. -/
def decodesAs (code : List Byte) : Nat → List (Nat × Silmaril.X86.Ext.Instr × Nat) → Bool
  | pos, [] => pos == code.length
  | pos, (off, i, len) :: rest =>
    off == pos && Silmaril.X86.Ext.decode (code.drop off) == some (i, len) &&
      decodesAs code (pos + len) rest

end Silmaril.Project.CompilesTo

end
