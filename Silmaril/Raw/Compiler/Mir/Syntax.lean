module

public import Silmaril.Machine.CBackend.Lir.Syntax.Defs

/-! # Mir: the linkable middle IR

Mir is the language-independent, target-independent unit of compilation of the C
compiler (`docs/projects/cerberus.md`), designed so that other front ends (Rust, LLVM IR/MLIR,
CakeML, WebAssembly) can produce it too. It is Lir (`Silmaril.Machine.Lir`) over
unbounded virtual registers, plus **symbols**:

* a function is named, and a call names its callee (`call`), or computes it
  (`callIndirect`, a function pointer);
* `addr` loads the address of a data object, or the pointer of a function, by name;
* a data object is a named, aligned byte range of the linear memory with an initial
  image and relocations (addresses written into the image).

Nothing in Mir is C-specific: C's types, lvalues, promotions and layout are resolved by
the front end (`Silmaril.Compile.C.ToMir`); calling conventions, stack frames and
register classes are resolved by `Lir.Alloc` and the backends. `Mir.link`
(`Silmaril.Compile.Mir.Link`) resolves the symbols of several units into one
`Lir.Prog Nat` and one initial linear-memory image.

## Semantics

The meaning of a set of units is the Lir semantics (`Lir.sem`) of their link, from the
entry function, with the initial memory of the link. `Contract.MirSem`
(`Silmaril/Compile/Contract.lean`) is a small-step semantics of Mir of its own, which
resolves symbols by name; the checked link refines it (`Mir.LinkCorrect`). The intended statement for each Mir pass `f`
(`Silmaril/Compile/Category`) is that `f` is a compiler at the identity convention:
for every set of units `us`, `Lir.sem (link (f us))` refines `Lir.sem (link us)`.

## Neighbours

* **Lir** (`Silmaril.Machine.Lir`): `Mir.link` is the lowering, and it is the whole
  relation: a Mir function body is a Lir block list over `Nat` registers, symbols become
  constants and function indices.
* **RTL** (`Silmaril.Machine.RTL`) and **RTL.SSA / λSSA**
  : per-function IRs with the same operator vocabulary
  (`Lir.Unop`, `Lir.Binop`, …). A Mir function lifts to an RTL CFG node by node; SSA
  passes run there and lower back to Lir blocks. Casts between Mir and RTL are future
  work; Mir keeps the symbols and data objects that per-function IRs lack.

## Conventions (`Silmaril/Compile/Category`)

* front end → Mir (e.g. `Compile.C.compileUnit`): a compiler at the convention that
  observes the source's result, output and exit, read back from the Lir behaviour of the
  link (returned value and final memory, or trap and memory);
* Mir → Mir passes: the identity convention (refinement of the linked Lir program);
* `Mir.link`: refinement of `Contract.MirSem` (checked, `Mir.LinkCheck`);
* the backends: `Lir.Alloc.spill_refines` and `X86.Backend.compile_refines`
  (`⟨.strict, .allowed⟩`, stack exhaustion allowed).

A reference interpreter for Mir (or for its link, through `Lir.run`) is a seeded idea of
the campaign: it gives Mir an executable semantics and a differential test against the
x86-64 runs.

## Limits (by design, for now)

A call passes at most `maxArgs` registers and returns at most one register; front ends
pass more through memory. These are the limits of the x86-64 backend (six argument
registers), the smaller of the two backends.
-/

@[expose] public section

namespace Silmaril.Compile.Mir

open Silmaril.Machine

/-- Virtual registers. -/
abbrev Reg := Nat

/-- Names of functions and data objects, shared by all units of a link. -/
abbrev Symbol := String

/-- Arguments of one call, the x86-64 backend's register limit. -/
def maxArgs : Nat := 6

/-- Instructions. -/
inductive Instr where
  /-- A Lir operation on virtual registers. -/
  | op (o : Lir.Op Reg)
  /-- A Lir floating-point operation (`Lir.Instr.fop`) on virtual registers. -/
  | fop (op : Lir.FOp) (dest first second : Reg)
  /-- `dest := &sym + offset` for a data object, or the function pointer of `sym`. -/
  | addr (dest : Reg) (sym : Symbol) (offset : Nat)
  /-- A direct call; `results` has at most one register. -/
  | call (callee : Symbol) (args : List Reg) (results : List Reg)
  /-- A call through a function pointer. -/
  | callIndirect (target : Reg) (args : List Reg) (results : List Reg)
  deriving Repr, Inhabited

/-- A basic block: instructions and a Lir terminator over virtual registers. -/
structure Block where
  instrs : Array Instr
  term : Lir.Term Reg
  deriving Repr

instance : Inhabited Block := ⟨⟨#[], .trap⟩⟩

/-- A function: its name, parameter registers, number of results (0 or 1), and blocks;
block 0 is the entry. `exported` functions are visible to other units. -/
structure Func where
  name : Symbol
  params : List Reg
  results : Nat
  blocks : Array Block
  exported : Bool := true
  /-- A weak definition yields to a non-weak one of the same name (library code). -/
  weak : Bool := false
  deriving Repr, Inhabited

/-- An address written into a data image: at byte `offset`, the 8-byte little-endian
address of `sym` plus `addend`. -/
structure Reloc where
  offset : Nat
  sym : Symbol
  addend : Int
  deriving Repr, Inhabited

/-- A data object: `size` bytes aligned to `align`, starting with `init` (the rest is
zero), patched by `relocs`. -/
structure Data where
  name : Symbol
  size : Nat
  align : Nat
  init : ByteArray := .empty
  relocs : List Reloc := []
  exported : Bool := true
  readonly : Bool := false
  weak : Bool := false
  deriving Inhabited

/-- A unit of compilation. -/
structure Unit where
  funcs : Array Func := #[]
  data : Array Data := #[]
  deriving Inhabited

/-- Mark every definition of a unit weak (a library). -/
def Unit.weaken (u : Unit) : Unit :=
  ⟨u.funcs.map ({ · with weak := true }), u.data.map ({ · with weak := true })⟩

/-- The units of a link, in order. -/
def Unit.append (a b : Unit) : Unit := ⟨a.funcs ++ b.funcs, a.data ++ b.data⟩

end Silmaril.Compile.Mir
