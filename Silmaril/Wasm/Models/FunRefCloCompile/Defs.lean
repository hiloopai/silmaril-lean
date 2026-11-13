module

public import Silmaril.Wasm.Models.FunRefClo.Defs
public import Silmaril.Wasm.Models.FunCloCompile.Defs
public import Silmaril.Wasm.Models.FunRefCompile.Defs

/-!
# Compiling FunRefClo to mutable-GC functional Wasm

FunRefClo (closures and references, `Silmaril.Wasm.Models.FunRefClo`) is compiled by combining the
two earlier compilers:

* FunCloCompile's closure conversion (`Silmaril.Wasm.Models.FunCloCompile`): a closure is a `$box`
  `(i31 tag, env)` with `env` a `$box` list of the environment, `app` calls the defunctionalised
  `apply` (function `1`), which dispatches on the tag; `envCode` and `unpack` are reused;
* FunRefCompile's cells (`Silmaril.Wasm.Models.FunRefCompile`): a location is a structure of
  `$cell = (struct (field (mut anyref)))`; `ref`, `get` and `set` are `struct.new $cell`,
  `struct.get $cell 0` and `struct.set $cell 0`.

The type section is `$box`, `main`, `$cell` (index `2`, as in FunRefCompile, so `cellIdx`,
`cellRef`, `cellSub` and `dCell` are reused) and `apply` (index `3`). The code uses
`struct.set`, so it is of `micro functionalMutGC`, not of `micro functional`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FunRefClo (Tm Prog tableLocals)
open Silmaril.Wasm.Models.FunCompile (anyref i31Ref boxIdx boxRef boxSub mainSub dBox dMain lx fx
  unbox getField)
open Silmaril.Wasm.Models.FunCloCompile (applySub dApply envCode unpack)
open Silmaril.Wasm.Models.FunRefCompile (cellIdx cellRef cellSub dCell)

/-- The type section: `$box`, `main`, `$cell`, `apply`. -/
def recTypes : List RecType := [⟨[boxSub]⟩, ⟨[mainSub]⟩, ⟨[cellSub]⟩, ⟨[applySub]⟩]

/-- The defined types of the module instance. -/
def modTypes : List DefType := [dBox, dMain, dCell, dApply]

/-- The table index of the `fix` at depth `d` with body `b`. -/
def tagOf (L : List (Nat × Tm)) (d : Nat) (b : Tm) : Nat := L.idxOf (d, b)

/-- **The code of a term at binder depth `d`** with the closure table `L`. -/
def compile (L : List (Nat × Tm)) (d : Nat) : Tm → List Instr
  | .var i => [.localGet (lx (d - i))]
  | .int n => [.intConst .i32 (n.setWidth 32), .refI31]
  | .bool b => [.intConst .i32 (if b then 1 else 0), .refI31]
  | .arith op a b => compile L d a ++ unbox ++ compile L d b ++ unbox ++
      [.intBinOp .i32 (FunCompile.Arith.wasm op), .refI31]
  | .cmp op a b => compile L d a ++ unbox ++ compile L d b ++ unbox ++
      [.intRelOp .i32 (FunCompile.Cmp.wasm op), .refI31]
  | .ite c t e => compile L d c ++ unbox ++
      [.if_ (.value anyref) (compile L d t) (compile L d e)]
  | .let_ a b => compile L d a ++ .localSet (lx (d + 1)) :: compile L (d + 1) b
  | .pair a b => compile L d a ++ compile L d b ++ [.structNew boxIdx]
  | .fst e => compile L d e ++ [.refCast boxRef, .structGet none boxIdx (fx 0)]
  | .snd e => compile L d e ++ [.refCast boxRef, .structGet none boxIdx (fx 1)]
  | .inl e => .intConst .i32 0 :: .refI31 :: compile L d e ++ [.structNew boxIdx]
  | .inr e => .intConst .i32 1 :: .refI31 :: compile L d e ++ [.structNew boxIdx]
  | .case e l r => compile L d e ++ .localSet (lx (d + 1)) :: getField (d + 1) 0 ++ unbox ++
      [.if_ (.value anyref)
        (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile L (d + 1) r)
        (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile L (d + 1) l)]
  | .fix b => [.intConst .i32 (BitVec.ofNat 32 (tagOf L d b)), .refI31] ++ envCode d ++
      [.structNew boxIdx]
  | .app f a => compile L d f ++ compile L d a ++ [.call ⟨1⟩]
  | .ref e => compile L d e ++ [.structNew cellIdx]
  | .get e => compile L d e ++ [.refCast cellRef, .structGet none cellIdx (fx 0)]
  | .set a b => compile L d a ++ .refCast cellRef :: compile L d b ++
      [.structSet cellIdx (fx 0), .intConst .i32 1, .refI31]

/-- The entry of the `fix` at depth `d` with body `b` in `apply`. -/
def entry (L : List (Nat × Tm)) (d : Nat) (b : Tm) : List Instr :=
  [.localGet (lx 1), .localSet (lx (d + 2)), .localGet (lx 0), .refCast boxRef,
    .structGet none boxIdx (fx 1), .localSet (lx (d + 1))] ++ unpack (d + 1) d ++
    [.localGet (lx 0), .localSet (lx (d + 1))] ++ compile L (d + 2) b

/-- The dispatch on the closure's tag over the table entries `k, k + 1, …`. -/
def dispatch (L : List (Nat × Tm)) : Nat → List (Nat × Tm) → List Instr
  | _, [] => [.unreachable]
  | k, (d, b) :: rest => getField 0 0 ++ unbox ++
      [.intConst .i32 (BitVec.ofNat 32 k), .intRelOp .i32 .eq,
        .if_ (.value anyref) (entry L d b) (dispatch L (k + 1) rest)]

/-- **The `apply` function** (type index `3`). -/
def applyFunc (L : List (Nat × Tm)) : Func :=
  ⟨⟨3⟩, List.replicate (tableLocals L) anyref, dispatch L 0 L⟩

/-- The body of `main`. -/
def mainBody (p : Prog) : List Instr :=
  [.localGet (lx 0), .refI31, .localSet (lx 1)] ++ compile p.table 1 p.body ++ unbox

/-- **The function `main`** (type index `1`). -/
def mainFunc (p : Prog) : Func := ⟨⟨1⟩, List.replicate (p.body.depth + 1) anyref, mainBody p⟩

/-- **The compiled module.** -/
def moduleOf (p : Prog) : Module :=
  { types := recTypes, funcs := [mainFunc p, applyFunc p.table],
    exports := [⟨"main", .func ⟨0⟩⟩] }

/-- The module instance of the compiled module. -/
def instOf : ModuleInst :=
  { types := modTypes, funcs := [0, 1], exports := [⟨"main", .func 0⟩] }

/-- The function instance of `main`. -/
def mainInst (p : Prog) : FuncInst Nat := ⟨dMain, instOf, .wasm (mainFunc p)⟩

/-- The function instance of `apply`. -/
def applyInst (p : Prog) : FuncInst Nat := ⟨dApply, instOf, .wasm (applyFunc p.table)⟩

/-- **The store of a program**: `main` at address `0`, `apply` at address `1`. -/
def storeOf (p : Prog) : Store Nat := { funcs := [mainInst p, applyInst p] }

/-- The Core point of a program. -/
def ptOf (p : Prog) : Silmaril.Wasm.Atlas.Core.Pt Nat := (storeOf p, FunCompile.noHost)

end Silmaril.Wasm.Models.FunRefCloCompile
