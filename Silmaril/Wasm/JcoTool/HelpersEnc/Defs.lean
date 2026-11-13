module

public import Silmaril.Wasm.JcoTool.Helpers.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# The `shim` and `fixup` helper modules as Core 3.0 modules

`wasm-jco` writes the helper core modules of wit-component's indirect-call pattern with a small
encoder of its own (`CMod.encode`, applied to `New.shimMod tys` and `New.fixupMod tys`).
`Silmaril.Wasm.JcoTool.Helpers` checks each output after decoding it (translation validation).
This module gives the two modules over silmaril's Core AST, for every list of slot types:

* `shimAst tys`: the types `tys`, a table of `n` to `n` `funcref`s (`n = tys.length`), function
  `i` of type `i` passing its parameters on to `call_indirect` of slot `i` at type `i`
  (`trampAst`), exported as `"i"`, and the table exported as `$imports`;
* `fixupAst tys`: the types `tys`, the imports `actual."i"` at type `i` and `shim.$imports`, and
  one active `funcref` segment filling the table from `0` with `ref.func 0 … ref.func (n-1)`.

The theorems (`HelpersEnc.Thms`): for fewer than `2 ^ 31` slots, **every** successful output
of `CMod.encode` on a shim or a fixup is the canonical encoding of `shimAst tys` /
`fixupAst tys` by silmaril's verified encoder (byte for byte), so it encodes that module in
the Core binary grammar, and those modules pass the checks `isShim` / `isFixup`. The helper
encoder is thereby proved for all inputs it is used on, not only checked per output.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.HelpersEnc

open Silmaril.Wasm
open Silmaril.Wasm.Component (CoreFuncTy)

/-- An index (modulo `2 ^ 32`). -/
def ixn {k : IndexKind} (n : Nat) : Idx k := ⟨Fin.ofNat _ n⟩

/-- A slot type as a type-section entry. -/
def ftAst (t : CoreFuncTy) : RecType :=
  ⟨[⟨true, [], .func ⟨t.params.map .num, t.results.map .num⟩⟩]⟩

/-- The table type of `n` to `n` `funcref`s. -/
def tableTy (n : Nat) : TableType := ⟨.i32, ⟨Fin.ofNat _ n, some (Fin.ofNat _ n)⟩, Helpers.funcref⟩

/-- The body of trampoline `i` with `p` parameters. -/
def trampAst (p i : Nat) : Expr :=
  (List.range p).map (fun j => .localGet (ixn j)) ++
    [.intConst .i32 (BitVec.ofNat 32 i), .callIndirect (ixn 0) (ixn i)]

/-- **The shim** of the slot types `tys`. -/
def shimAst (tys : List CoreFuncTy) : Module where
  types := tys.map ftAst
  tables := [⟨tableTy tys.length, [.refNull (.abstract .func)]⟩]
  funcs := ((List.range tys.length).zip tys).map fun (i, t) =>
    ⟨ixn i, [], trampAst t.params.length i⟩
  exports := ((List.range tys.length).map fun i => ⟨toString i, .func (ixn i)⟩) ++
    [⟨"$imports", .table (ixn 0)⟩]

/-- **The fixup** of the slot types `tys`. -/
def fixupAst (tys : List CoreFuncTy) : Module where
  types := tys.map ftAst
  imports := ((List.range tys.length).map fun i => ⟨"actual", toString i, .func (ixn i)⟩) ++
    [⟨"shim", "$imports", .table (tableTy tys.length)⟩]
  elems := [⟨Helpers.funcref, (List.range tys.length).map fun i => [.refFunc (ixn i)],
    .active (ixn 0) [.intConst .i32 (BitVec.ofNat 32 0)]⟩]

end Silmaril.Wasm.JcoTool.HelpersEnc
