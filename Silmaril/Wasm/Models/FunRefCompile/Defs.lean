module

public import Silmaril.Wasm.Models.FunRef.Defs
public import Silmaril.Wasm.Models.FunCompile.Defs

/-!
# Compiling FunRef to mutable-GC functional Wasm

The representation of `Silmaril.Wasm.Models.FunCompile` (every value an `anyref`: `i31` integers and
booleans, immutable `$box` pairs and injections), extended by **cells**: a FunRef location is a
structure of the type `$cell = (struct (field (mut anyref)))`.

* `ref e`: the code of `e`, then `struct.new $cell`;
* `get e`: the code of `e`, `ref.cast (ref $cell)`, `struct.get $cell 0`;
* `set a b`: the code of `a`, `ref.cast (ref $cell)`, the code of `b`, `struct.set $cell 0`, then
  the `i31` of `true`.

The type section is `$box`, `main` and `$cell` (index `2`), so the code of every FunLang construct
is unchanged. The code uses `struct.set`, so it is of `micro functionalMutGC`
(`Thms.compile_inFeat`), not of `micro functional`.

`compile`, `mainBody`, `funcOf`, `moduleOf`, `storeOf`, `ptOf` as in `FunCompile`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FunRef (Tm Prog)
open Silmaril.Wasm.Models.FunCompile (anyref i31Ref boxIdx boxRef boxSub mainSub dBox dMain lx fx unbox
  getField)

/-- The type index of `$cell`. -/
def cellIdx : TypeIdx := ⟨2⟩

/-- `(ref $cell)`. -/
def cellRef : RefType := ⟨false, .typeIdx cellIdx⟩

/-- `$cell = (struct (field (mut anyref)))`, final. -/
def cellSub : SubType := ⟨true, [], .struct [⟨.var, .val anyref⟩]⟩

/-- The type section. -/
def recTypes : List RecType := [⟨[boxSub]⟩, ⟨[mainSub]⟩, ⟨[cellSub]⟩]

/-- The defined type of `$cell`. -/
def dCell : DefType :=
  .defn (.group (.cons (.sub true .nil (.struct (.cons (.field .var (.val (.refv
    (.ref true (.abs .any))))) .nil))) .nil)) 0

/-- The defined types of the module instance. -/
def modTypes : List DefType := [dBox, dMain, dCell]

/-- **The code of a term at binder depth `d`.** -/
def compile (d : Nat) : Tm → List Instr
  | .var i => [.localGet (lx (d - i))]
  | .int n => [.intConst .i32 (n.setWidth 32), .refI31]
  | .bool b => [.intConst .i32 (if b then 1 else 0), .refI31]
  | .arith op a b => compile d a ++ unbox ++ compile d b ++ unbox ++
      [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31]
  | .cmp op a b => compile d a ++ unbox ++ compile d b ++ unbox ++
      [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31]
  | .ite c t e => compile d c ++ unbox ++ [.if_ (.value anyref) (compile d t) (compile d e)]
  | .let_ a b => compile d a ++ .localSet (lx (d + 1)) :: compile (d + 1) b
  | .pair a b => compile d a ++ compile d b ++ [.structNew boxIdx]
  | .fst e => compile d e ++ [.refCast boxRef, .structGet none boxIdx (fx 0)]
  | .snd e => compile d e ++ [.refCast boxRef, .structGet none boxIdx (fx 1)]
  | .inl e => .intConst .i32 0 :: .refI31 :: compile d e ++ [.structNew boxIdx]
  | .inr e => .intConst .i32 1 :: .refI31 :: compile d e ++ [.structNew boxIdx]
  | .case e l r => compile d e ++ .localSet (lx (d + 1)) :: getField (d + 1) 0 ++ unbox ++
      [.if_ (.value anyref) (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) r)
        (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) l)]
  | .ref e => compile d e ++ [.structNew cellIdx]
  | .get e => compile d e ++ [.refCast cellRef, .structGet none cellIdx (fx 0)]
  | .set a b => compile d a ++ .refCast cellRef :: compile d b ++
      [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31]

/-- The body of `main`. -/
def mainBody (p : Prog) : List Instr :=
  [.localGet (lx 0), .refI31, .localSet (lx 1)] ++ compile 1 p.body ++ unbox

/-- The compiled function `main`. -/
def funcOf (p : Prog) : Func := ⟨⟨1⟩, List.replicate (p.body.depth + 1) anyref, mainBody p⟩

/-- The compiled module. -/
def moduleOf (p : Prog) : Module :=
  { types := recTypes, funcs := [funcOf p], exports := [⟨"main", .func ⟨0⟩⟩] }

/-- The module instance of `main`. -/
def instOf : ModuleInst := { types := modTypes, funcs := [0] }

/-- The function instance of `main`. -/
def mainInst (p : Prog) : FuncInst Nat := ⟨dMain, instOf, .wasm (funcOf p)⟩

/-- The store of a program: `main` at address `0`. -/
def storeOf (p : Prog) : Store Nat := { funcs := [mainInst p] }

/-- The Core point of a program. -/
def ptOf (p : Prog) : Silmaril.Wasm.Atlas.Core.Pt Nat := (storeOf p, FunCompile.noHost)

end Silmaril.Wasm.Models.FunRefCompile
