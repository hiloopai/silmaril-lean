module

public import Silmaril.Wasm.Models.FunClo.Defs
public import Silmaril.Wasm.Models.FunCompile.Defs

/-!
# Compiling FunClo to functional Wasm: closure conversion with a defunctionalised `apply`

FunClo (`Silmaril.Wasm.Models.FunClo`) is FunLang with recursive first-class functions. The
compiler keeps FunCompile's uniform `anyref` representation for the FunLang constructs
(`i31` integers and booleans, `$box` pairs and injections, binders in locals) and adds closures:

* **Closure table.** `Prog.table p` lists the `fix` subterms of the program with their binder
  depths. The code of the `fix` at depth `d` with body `b` has index `L.idxOf (d, b)`.
* **Closures** are `$box` structures `(tag, env)`: `tag` is the table index as an `i31`, and
  `env` is the environment as a linked list of `$box`es, each `(tail, head)` and ending in
  `i31 0`. A `fix` at depth `d` builds the list from locals `1 … d` (`envCode d`), so every
  closure captures its whole environment.
* **`apply`** (function `1`, `[anyref anyref] → [anyref]`) is the defunctionalised dispatcher.
  It reads the closure's tag and compares it with `0, 1, …` (`dispatch`). The matching
  `entry d b` stores the argument in local `d + 2`, unpacks the environment into locals
  `1 … d` (`unpack`), stores the closure itself in local `d + 1` (the recursive `var 1`), and
  runs the body at depth `d + 2`. An unknown tag reaches `unreachable`, which cannot happen
  for a closure the compiled code built.
* **Application** `app f a` evaluates `f` and `a` and makes a direct `call 1`. Recursion is a
  closure that calls `apply` on itself.

The compiled code uses only `local.get/set`, `if`, `i32` arithmetic, `ref.i31`, `i31.get_u`,
`ref.cast`, `struct.new`, `struct.get`, `call` and `unreachable`. These are all in the profile
`micro functional`.

* `moduleOf p`: types `$box`, `main : [i32] → [i32]`, `apply`; the functions `main` and `apply`;
  the export of `main`.
* `instOf`, `storeOf p`: the module instance and the store **that instantiation of `moduleOf p`
  produces** (`Thms.instantiate_moduleOf`): `main` at address `0` and `apply` at address `1`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunCloCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FunClo (Tm Prog tableLocals)
open Silmaril.Wasm.Models.FunCompile (anyref i31Ref boxIdx boxRef boxSub mainSub dBox dMain lx fx
  unbox getField)

/-! ## Types -/

/-- `apply : [anyref anyref] → [anyref]`, final. -/
def applySub : SubType := ⟨true, [], .func ⟨[anyref, anyref], [anyref]⟩⟩

/-- The type section: three singleton recursion groups. -/
def recTypes : List RecType := [⟨[boxSub]⟩, ⟨[mainSub]⟩, ⟨[applySub]⟩]

/-- The defined type of `apply`. -/
def dApply : DefType :=
  .defn (.group (.cons (.sub true .nil (.func
    (.cons (.refv (.ref true (.abs .any))) (.cons (.refv (.ref true (.abs .any))) .nil))
    (.cons (.refv (.ref true (.abs .any))) .nil))) .nil)) 0

/-- The defined types of the module instance. -/
def modTypes : List DefType := [dBox, dMain, dApply]

/-! ## Code -/

/-- The table index of the `fix` at depth `d` with body `b`. -/
def tagOf (L : List (Nat × Tm)) (d : Nat) (b : Tm) : Nat := L.idxOf (d, b)

/-- Build the environment list from locals `1 … j`: `i31 0`, then `(tail, local i)` for
`i = 1 … j`, so the head is local `j`, the innermost variable. -/
def envCode : Nat → List Instr
  | 0 => [.intConst .i32 0, .refI31]
  | j + 1 => envCode j ++ [.localGet (lx (j + 1)), .structNew boxIdx]

/-- **The code of a term at binder depth `d`** with the closure table `L` (the environment is
in locals `1 … d`, `var i` in local `d - i`). -/
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

/-- Unpack `j` environment entries from the list in local `c` into locals `j, j - 1, …, 1`
(advancing local `c` along the list). -/
def unpack (c : Nat) : Nat → List Instr
  | 0 => []
  | j + 1 => [.localGet (lx c), .refCast boxRef, .structGet none boxIdx (fx 1),
      .localSet (lx (j + 1)), .localGet (lx c), .refCast boxRef, .structGet none boxIdx (fx 0),
      .localSet (lx c)] ++ unpack c j

/-- The entry of the `fix` at depth `d` with body `b`, in `apply` (local `0` the closure,
local `1` the argument): the argument to local `d + 2`, the environment to locals `1 … d`, the
closure to local `d + 1`, then the body at depth `d + 2`. -/
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

/-- **The `apply` function** of a closure table (type index `2`). -/
def applyFunc (L : List (Nat × Tm)) : Func :=
  ⟨⟨2⟩, List.replicate (tableLocals L) anyref, dispatch L 0 L⟩

/-- The body of `main`: box the argument into local `1`, run the program, unbox the result. -/
def mainBody (p : Prog) : List Instr :=
  [.localGet (lx 0), .refI31, .localSet (lx 1)] ++ compile p.table 1 p.body ++ unbox

/-- **The function `main`** (type index `1`), with `anyref` locals `1 … depth + 1`. -/
def mainFunc (p : Prog) : Func := ⟨⟨1⟩, List.replicate (p.body.depth + 1) anyref, mainBody p⟩

/-- **The compiled module**: the types, `main` and `apply`, and the export of `main`. -/
def moduleOf (p : Prog) : Module :=
  { types := recTypes, funcs := [mainFunc p, applyFunc p.table],
    exports := [⟨"main", .func ⟨0⟩⟩] }

/-! ## The Core point of a program -/

/-- The module instance of the compiled module. -/
def instOf : ModuleInst :=
  { types := modTypes, funcs := [0, 1], exports := [⟨"main", .func 0⟩] }

/-- The function instance of `main`. -/
def mainInst (p : Prog) : FuncInst Nat := ⟨dMain, instOf, .wasm (mainFunc p)⟩

/-- The function instance of `apply`. -/
def applyInst (p : Prog) : FuncInst Nat := ⟨dApply, instOf, .wasm (applyFunc p.table)⟩

/-- **The store of a program**: `main` at address `0` and `apply` at address `1`. It is what
instantiating `moduleOf p` in the empty store produces (`Thms.instantiate_moduleOf`). -/
def storeOf (p : Prog) : Store Nat := { funcs := [mainInst p, applyInst p] }

/-- **The Core point of a program.** -/
def ptOf (p : Prog) : Silmaril.Wasm.Atlas.Core.Pt Nat := (storeOf p, FunCompile.noHost)

end Silmaril.Wasm.Models.FunCloCompile
