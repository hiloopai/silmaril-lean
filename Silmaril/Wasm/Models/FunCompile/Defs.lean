module

public import Silmaril.Wasm.Models.FunLang.Defs
public import Silmaril.Wasm.Models.Model.Thms

/-!
# Compiling FunLang to functional Wasm

A uniform representation in the style of `wasm_of_ocaml`: every FunLang value is an `anyref`.

* integers and booleans are `i31` references (`true` is `1`); arithmetic unboxes with
  `ref.cast (ref i31)` and `i31.get_u`, computes in `i32` and boxes again with `ref.i31`;
* pairs are immutable structures of the single type `$box = (struct (field anyref) (field
  anyref))`; an injection is a `$box` whose first field is the tag (`i31` `0` or `1`) and whose
  second field is the payload;
* variables are locals: local `0` is the `i32` argument, local `1` its boxed copy, and the binder
  at depth `d` (`let`, `case`) is local `d + 1`;
* `ite` and `case` compile to `if` with result `anyref`.

The compiled code uses locals, `if`, `i32` arithmetic, `ref.i31`, `i31.get_u`, `ref.cast`,
`struct.new` and `struct.get` only: the immutable-GC, memory-free, table-free, global-free and
float-free profile `micro functional` (`Thms.compile_inFeat`).

* `compile d e`: the code of `e` at binder depth `d`;
* `funcOf p`, `moduleOf p`: the function `main : [i32] → [i32]` and its module (types `$box`
  and the function type, one function, one export);
* `storeOf p`: the store holding `main` at address `0`, its instance having the module's
  defined types `modTypes`. It is built directly, not by instantiating `moduleOf p`;
* `ptOf p`, `callOf n`: the Core point and call of program `p` on `n` (a host that is never
  called, as the store has no imports);
* `valWord`, `readWord`: read an `i32` result back as a 31-bit word.
* The compiled module of a well-typed program passes Core 3.0 validation and is of
  `micro functional` (`Thms.moduleOf_valid`): all locals are `anyref`s, and every use of a value
  is preceded by a cast.

The semantic preservation theorem is `Thms.behaviours_compile`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FunLang (Tm Prog Arith Cmp)

/-! ## Types -/

/-- `anyref`, the type of every compiled value. -/
def anyref : ValType := .ref ⟨true, .abstract .any⟩

/-- `(ref i31)`. -/
def i31Ref : RefType := ⟨false, .abstract .i31⟩

/-- The type index of `$box`. -/
def boxIdx : TypeIdx := ⟨0⟩

/-- `(ref $box)`. -/
def boxRef : RefType := ⟨false, .typeIdx boxIdx⟩

/-- `$box = (struct (field anyref) (field anyref))`, final. -/
def boxSub : SubType := ⟨true, [], .struct [⟨.const, .val anyref⟩, ⟨.const, .val anyref⟩]⟩

/-- `[i32] → [i32]`, final. -/
def mainSub : SubType := ⟨true, [], .func ⟨[.num (.int .i32)], [.num (.int .i32)]⟩⟩

/-- The type section: two singleton recursion groups. -/
def recTypes : List RecType := [⟨[boxSub]⟩, ⟨[mainSub]⟩]

/-- The defined type of `$box`. -/
def dBox : DefType :=
  .defn (.group (.cons (.sub true .nil (.struct (.cons (.field .const (.val (.refv
    (.ref true (.abs .any))))) (.cons (.field .const (.val (.refv (.ref true (.abs .any)))))
    .nil)))) .nil)) 0

/-- The defined type of `main`. -/
def dMain : DefType :=
  .defn (.group (.cons (.sub true .nil (.func (.cons (.num (.int .i32)) .nil)
    (.cons (.num (.int .i32)) .nil))) .nil)) 0

/-- The defined types of the module instance. -/
def modTypes : List DefType := [dBox, dMain]

/-! ## Code -/

/-- A local index. -/
def lx (n : Nat) : LocalIdx := ⟨Fin.ofNat _ n⟩

/-- A field index. -/
def fx (n : Nat) : FieldIdx := ⟨Fin.ofNat _ n⟩

/-- Unbox an `i31` reference to an `i32`. -/
def unbox : List Instr := [.refCast i31Ref, .i31Get .unsigned]

/-- The Wasm operation of an integer operation. -/
def Arith.wasm : Arith → IntBinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-- The Wasm comparison of a comparison. -/
def Cmp.wasm : Cmp → IntRelOp
  | .eq => .eq
  | .ltu => .lt .unsigned

/-- Field `i` of a `$box` held in local `x`. -/
def getField (x i : Nat) : List Instr :=
  [.localGet (lx x), .refCast boxRef, .structGet none boxIdx (fx i)]

/-- **The code of a term at binder depth `d`** (the environment is in locals `1 … d`, `var i`
in local `d - i`). -/
def compile (d : Nat) : Tm → List Instr
  | .var i => [.localGet (lx (d - i))]
  | .int n => [.intConst .i32 (n.setWidth 32), .refI31]
  | .bool b => [.intConst .i32 (if b then 1 else 0), .refI31]
  | .arith op a b => compile d a ++ unbox ++ compile d b ++ unbox ++
      [.intBinOp .i32 (Arith.wasm op), .refI31]
  | .cmp op a b => compile d a ++ unbox ++ compile d b ++ unbox ++
      [.intRelOp .i32 (Cmp.wasm op), .refI31]
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

/-- The body of `main`: box the argument into local `1`, run the program, unbox the result. -/
def mainBody (p : Prog) : List Instr :=
  [.localGet (lx 0), .refI31, .localSet (lx 1)] ++ compile 1 p.body ++ unbox

/-- **The compiled function** `main` (type index `1`), with `anyref` locals `1 … depth + 1`. -/
def funcOf (p : Prog) : Func := ⟨⟨1⟩, List.replicate (p.body.depth + 1) anyref, mainBody p⟩

/-- **The compiled module**: the types, `main`, and its export. -/
def moduleOf (p : Prog) : Module :=
  { types := recTypes, funcs := [funcOf p], exports := [⟨"main", .func ⟨0⟩⟩] }

/-! ## The Core point of a program -/

/-- The module instance of `main`. -/
def instOf : ModuleInst := { types := modTypes, funcs := [0] }

/-- The function instance of `main`. -/
def mainInst (p : Prog) : FuncInst Nat := ⟨dMain, instOf, .wasm (funcOf p)⟩

/-- **The store of a program**: `main` at address `0`. -/
def storeOf (p : Prog) : Store Nat := { funcs := [mainInst p] }

/-- The host relation of the point: the store has no imports, so it never answers. -/
def noHost : HostSemantics Nat := fun _ _ _ _ => False

/-- **The Core point of a program.** -/
def ptOf (p : Prog) : Silmaril.Wasm.Atlas.Core.Pt Nat := (storeOf p, noHost)

/-- **The Core call of an argument**: `main` on the argument as an `i32`. -/
def callOf (n : BitVec 31) : Silmaril.Wasm.Atlas.Core.Call := (0, [.i32 (n.setWidth 32)])

/-- An `i32` read back as a 31-bit word (other values read as `0`). -/
def valWord : Val → BitVec 31
  | .num ⟨.int .i32, k⟩ => k.setWidth 31
  | _ => 0

/-- Behaviours read back as behaviours over words. -/
def readWord : Behaviour Val → Behaviour (BitVec 31) := Behaviour.map valWord

end Silmaril.Wasm.Models.FunCompile
