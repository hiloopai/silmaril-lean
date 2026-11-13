module

public import Silmaril.Wasm.JcoTool.ToolI.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Perf.CoreMod.Defs

/-!
# The `shim` and `fixup` helper modules, checked by silmaril's verified decoder

`wasm-jco` writes the two helper core modules of wit-component's indirect-call pattern (`shim`:
a `funcref` table and one trampoline per slot; `fixup`: imports the real functions and the
shim's table and fills it) with a small hand-written encoder (`CMod.encode`). This module states
what those modules are, over silmaril's Core AST, and checks every helper module of an output
against it after decoding it with silmaril's decoder (`decode?`, sound for the Core binary
grammar, which is unambiguous):

* `IsShim m`: for slot types `tys` (the module's own types, `n = tys.length`), `m` has exactly
  the function types `tys`, no imports, one table of `n` to `n` `funcref`s exported as
  `$imports`, and `n` functions, function `i` of type `i`, without locals, whose body passes its
  parameters on (`local.get 0 … local.get (p-1)`) to `call_indirect` of table slot `i` at type
  `i`, exported as `"i"`; nothing else (no memory, global, tag, data, element segment, start).
* `IsFixup m`: for types `tys`, `m` has exactly those types, imports `actual."i"` at type `i`
  for every slot and then `shim.$imports` (a table of `n` to `n` `funcref`s), and has one
  active element segment of type `funcref` filling table `0` from offset `0` with
  `ref.func 0 … ref.func (n-1)`; nothing else.
* `helperOk b`: the bytes decode, and the module is a shim or a fixup.
* `ToolV.newFullV`: `wasm-jco new` (thin wrapper, every world) with the check of every helper
  module of the output (the core modules after the input).

The theorem (`Helpers.Thms`, `newFullV_correct`): every helper module of an output **encodes**
(in silmaril's binary grammar) a module of the shape above. This verifies the encoder's output
by translation validation for every run, not the encoder for all inputs.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Helpers

open Silmaril.Wasm

/-- `funcref`. -/
def funcref : RefType := ⟨true, .abstract .func⟩

/-- A table type of `n` to `n` `funcref`s. -/
def tableOk (n : Nat) (t : TableType) : Bool :=
  t.address == .i32 && t.limits.min.val == n && (t.limits.max.map (·.val)) == some n &&
    t.element == funcref

/-- A function type (any finality, no supertypes). -/
def funcTypeOf : RecType → Option FuncType
  | ⟨[⟨_, [], .func ft⟩]⟩ => some ft
  | _ => none

/-- The number of an index. -/
def ix {k : IndexKind} (i : Idx k) : Nat := i.value.val

def isLocalGet (i : Nat) : Instr → Bool
  | .localGet j => ix j == i
  | _ => false

def isI32Const (n : Nat) : Instr → Bool
  | .intConst .i32 b => b.toNat == n
  | _ => false

def isCallIndirect (ty : Nat) : Instr → Bool
  | .callIndirect tb t => ix tb == 0 && ix t == ty
  | _ => false

def isRefFunc (i : Nat) : Expr → Bool
  | [.refFunc j] => ix j == i
  | _ => false

/-- The body of trampoline `i` with `p` parameters. -/
def trampOk (p i : Nat) (body : Expr) : Bool :=
  body.length == p + 2 &&
    (List.range p).all (fun j => match body[j]? with
      | some x => isLocalGet j x
      | none => false) &&
    (match body[p]? with
      | some x => isI32Const i x
      | none => false) &&
    (match body[p + 1]? with
      | some x => isCallIndirect i x
      | none => false)

/-- Export `i` of a shim with `n` slots: function `i` as `"i"`, then the table as `$imports`. -/
def shimExportOk (n i : Nat) (e : Export) : Bool :=
  if i < n then e.name == toString i && (match e.index with
    | .func j => ix j == i
    | _ => false)
  else e.name == "$imports" && (match e.index with
    | .table j => ix j == 0
    | _ => false)

/-- Import `i` of a fixup with `n` slots: `actual."i"` at type `i`, then `shim.$imports`. -/
def fixupImportOk (n i : Nat) (im : Import) : Bool :=
  if i < n then im.moduleName == "actual" && im.name == toString i && (match im.type with
    | .func t => ix t == i
    | _ => false)
  else im.moduleName == "shim" && im.name == "$imports" && (match im.type with
    | .table tt => tableOk n tt
    | _ => false)

/-- **The shim**, as a check of the decoded module. -/
def isShim (m : Module) : Bool :=
  let n := m.types.length
  (m.types.all fun r => (funcTypeOf r).isSome) &&
  m.imports.isEmpty && m.tags.isEmpty && m.globals.isEmpty && m.memories.isEmpty &&
  m.data.isEmpty && m.elems.isEmpty && m.start.isNone &&
  (match m.tables with
    | [t] => tableOk n t.type
    | _ => false) &&
  m.funcs.length == n &&
  (List.range n).all (fun i => match m.funcs[i]?, (m.types[i]?).bind funcTypeOf with
    | some f, some ft => ix f.type == i && f.locals.isEmpty && trampOk ft.params.length i f.body
    | _, _ => false) &&
  m.exports.length == n + 1 && (List.range (n + 1)).all (fun i => match m.exports[i]? with
    | some e => shimExportOk n i e
    | none => false)

/-- **The fixup**, as a check of the decoded module. -/
def isFixup (m : Module) : Bool :=
  let n := m.types.length
  (m.types.all fun r => (funcTypeOf r).isSome) &&
  m.tags.isEmpty && m.globals.isEmpty && m.memories.isEmpty && m.tables.isEmpty &&
  m.funcs.isEmpty && m.data.isEmpty && m.start.isNone && m.exports.isEmpty &&
  m.imports.length == n + 1 && (List.range (n + 1)).all (fun i => match m.imports[i]? with
    | some im => fixupImportOk n i im
    | none => false) &&
  (match m.elems with
    | [e] => e.type == funcref && e.init.length == n &&
        (List.range n).all (fun i => match e.init[i]? with
          | some x => isRefFunc i x
          | none => false) &&
        (match e.mode with
          | .active tb [x] => ix tb == 0 && isI32Const 0 x
          | _ => false)
    | _ => false)

/-- A helper module of an output: decoded by silmaril, a shim or a fixup. -/
def helperOk (b : ByteArray) : Bool :=
  match Silmaril.Wasm.Perf.CoreDecode.decodeF b with
  | some m => isShim m || isFixup m
  | none => false

/-- Every core module of an output after the input is a checked helper. -/
def helpersOk (o : Tool.Out) : Bool := (o.cores.drop 1).all helperOk

end Silmaril.Wasm.JcoTool.Helpers

namespace Silmaril.Wasm.JcoTool.ToolV

/-- **`wasm-jco new`** (thin wrapper) with every helper module checked. -/
def newFullV (core : ByteArray) (wf : Silmaril.Wasm.Wit.Binary.WorldFull) : Except String Tool.Out := do
  let o ← ToolI.newFull core wf
  New.require (Helpers.helpersOk o)
    "a helper core module (shim or fixup) failed the check against its specification"
  pure { o with summary := o.summary ++
    [s!"helpers: {o.cores.length - 1} shim/fixup module(s) decoded by silmaril and checked (Helpers.newFullV_correct)"] }

/-- **`wasm-jco new --lime`** with every helper module checked. -/
def newLimeFullV (core : ByteArray) (wf : Silmaril.Wasm.Wit.Binary.WorldFull) : Except String Tool.Out := do
  let o ← ToolI.newLimeFull core wf
  New.require (Helpers.helpersOk o)
    "a helper core module (shim or fixup) failed the check against its specification"
  pure { o with summary := o.summary ++
    [s!"helpers: {o.cores.length - 1} shim/fixup module(s) decoded by silmaril and checked (Helpers.newFullV_correct)"] }

end Silmaril.Wasm.JcoTool.ToolV
