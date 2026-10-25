module

public import Silmaril.Wasm.Binaryen.Exe.MemoryEncode
public import Silmaril.Wasm.Binaryen.Exe.GcEncode

@[expose] public section

/-! # Table encoding

Defined `i32` or `i64` tables of any reference type (`encRefType`: `funcref` is the byte
`0x70`) with the default (null) initializer, and the full `u32`
table-index immediate of `call_indirect`. Element segments need `encExpr` and are
in `Exe/Encode.lean`. `encTable` retains its default-initializer interface;
`encTableWith` adds explicit initializers through an expression-encoder callback.
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm

/-- The Core 3.0 `u32` table index of `call_indirect`. Table zero retains the
legacy reserved byte `0x00`. Every `TableIdx` already fits in `u32`. -/
def encTableIdx (x : TableIdx) : Except String (List UInt8) :=
  pure (encIdx x)

/-- A table type: its reference type, then the address-width-specific limits codec. -/
def encTableType (tt : TableType) : Except String (List UInt8) := do
  let limits ← encMemory ⟨tt.address, tt.limits⟩
  pure (encRefType tt.element ++ limits)

/-- A table with the default initializer `ref.null` of its element heap type. -/
def encTable (t : Table) : Except String (List UInt8) :=
  match t.init with
  | [.refNull ht] =>
    if ht = t.type.element.heap then encTableType t.type
    else throw "encoder: table initializer is not the default"
  | _ => throw "encoder: explicit table initializers are not supported"

/-- Encode a table with an arbitrary initializer using an expression encoder.
Default-null tables retain exactly `encTable`'s bytes. The callback avoids a
circular dependency: expression encoding is defined after instruction encoding. -/
def encTableWith (emitExpr : Expr → Except String (List UInt8)) (t : Table) :
    Except String (List UInt8) :=
  match encTable t with
  | .ok bytes => .ok bytes
  | .error _ => do
    let typeBytes ← encTableType t.type
    let initBytes ← emitExpr t.init
    pure ([0x40, 0x00] ++ typeBytes ++ initBytes)

/-- Extending initializer coverage preserves every successful original encoding. -/
theorem encTableWith_of_encTable {emitExpr : Expr → Except String (List UInt8)}
    {t : Table} {bytes : List UInt8} (h : encTable t = .ok bytes) :
    encTableWith emitExpr t = .ok bytes := by
  simp only [encTableWith, h]

/-- The function indices of a list of `ref.func` initializers. -/
def elemFuncs? : List Expr → Option (List FuncIdx)
  | [] => some []
  | [.refFunc y] :: es => (elemFuncs? es).map (y :: ·)
  | _ => none

end Silmaril.Wasm.Binaryen.Exe
