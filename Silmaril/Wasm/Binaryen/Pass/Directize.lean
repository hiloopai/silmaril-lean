module

public import Silmaril.Wasm.Binaryen.Profile

public import Silmaril.Wasm.Binaryen.Exe.Fold
public import Silmaril.Wasm.Binaryen.Exe.Valid

@[expose] public section

/-! # Directize: turn an indirect call through a known table slot into a direct call

Binaryen's Directize (`src/passes/Directize.cpp`, version_133) replaces
`call_indirect $t $ty (args..., i32.const k)` by `call $f (args...)` when slot `k` of
table `$t` is known to hold `ref.func $f` and `$f` has type `$ty` (and the same for
`return_call_indirect`). Like Binaryen it returns at once when the module has no
table. The verified implementation also requires i32 table addresses and offsets, and
`ref.func` element entries.

The slot contents are known only when nothing can change the table after
instantiation:

* no table is imported and none is exported (the host cannot reach a table);
* no function body contains `table.set`, `table.fill`, `table.copy`, `table.init` or
  `table.grow`, or a structured instruction outside the tree structure;
* every active element segment of the table has an `i32.const` offset.

Slot `k` is then the entry of the last active segment that covers it. Instantiation
fails unless every segment fits in the table, so a covered slot is in bounds. The
callee's type must be the call's type index itself. This file contains executable
definitions only.
-/

namespace Silmaril.Wasm.Binaryen

namespace Directize

open Exe

/-- Instructions that can change a table entry. -/
def mutates : Instr → Bool
  | .tableSet _ | .tableFill _ | .tableCopy .. | .tableInit .. | .tableGrow _ => true
  | i => structuredInstr i

mutual
/-- Some instruction of the tree can change a table. -/
def mutatesExpr : BExpr → Bool
  | .op i args => mutates i || mutatesList args
  | .block _ b | .loop _ b | .tryTable _ _ b => mutatesList b
  | .if_ _ c t e => mutatesList c || mutatesList t || mutatesList e
/-- `mutatesExpr` on a list. -/
def mutatesList : List BExpr → Bool
  | [] => false
  | e :: es => mutatesExpr e || mutatesList es
end

/-- The tables are private and immutable after instantiation. -/
def frozen (m : BModule) : Bool :=
  m.base.imports.all (fun i => match i.type with | .table _ => false | _ => true) &&
  m.base.exports.all (fun e => match e.index with | .table _ => false | _ => true) &&
  !m.funcs.any (fun f => mutatesList f.body)

/-- Every active element segment names a table of the module (true of valid modules). -/
def elemsOk (m : BModule) : Bool :=
  m.base.elems.all fun e => match e.mode with
    | .active y _ => decide (y.toNat < m.base.tables.length)
    | _ => true

/-- The instantiation simulation currently supports only 32-bit tables and offsets,
and segments whose entries are all `ref.func`. The pipeline profile also accepts
table64 modules and `ref.null func` entries; leave those unchanged. -/
def i32Only (m : BModule) : Bool :=
  m.base.tables.all (fun t => t.type.address == .i32) &&
  m.base.elems.all (fun e => match e.mode with
    | .active _ [.intConst .i32 _] => true
    | .active .. => false
    | _ => true) &&
  m.base.elems.all (fun e => e.init.all fun x => match x with
    | [.refFunc _] => true
    | _ => false)

/-- The function an element-segment entry denotes, if it is a plain `ref.func`. -/
def entryFunc : Expr → Option Nat
  | [.refFunc f] => some f.toNat
  | _ => none

/-- Apply one element segment to the knowledge of slot `k` of table `t`: `none` gives
up (a non-constant offset), `some none` is a slot with no known function. -/
def step (t k : Nat) (acc : Option (Option Nat)) (el : Elem) : Option (Option Nat) :=
  match acc, el.mode with
  | none, _ => none
  | some v, .active tbl off =>
    if tbl.toNat != t then some v
    else match off with
      | [.intConst .i32 o] =>
        if o.toNat ≤ k && k < o.toNat + el.init.length then
          some (el.init[k - o.toNat]?.bind entryFunc)
        else some v
      | _ => none
  | some v, _ => some v

/-- The function in slot `k` of table `t`, when it is known. -/
def slot? (m : BModule) (t k : Nat) : Option Nat :=
  if t < m.base.tables.length then
    match m.base.elems.foldl (step t k) (some none) with
    | some (some f) => some f
    | _ => none
  else none

/-- The direct callee of `call_indirect t ty` with constant index `k`. -/
def target? (m : BModule) (tys : List TypeIdx) (t : TableIdx) (ty : TypeIdx) (k : Nat) :
    Option FuncIdx := do
  let f ← slot? m t.toNat k
  let fty ← tys[f]?
  if fty == ty && m.numImportedFuncs ≤ f then Idx.ofNat? f else none

/-- The direct form of an indirect call whose last operand is an `i32.const`. -/
def direct (m : BModule) (tys : List TypeIdx) (i : Instr) (args : List BExpr) :
    Option (Instr × List BExpr) :=
  match args.getLast? with
  | some (.op (.intConst .i32 k) []) =>
    match i with
    | .callIndirect t ty => (target? m tys t ty k.toNat).map fun f => (.call f, args.dropLast)
    | .returnCallIndirect t ty =>
      (target? m tys t ty k.toNat).map fun f => (.returnCall f, args.dropLast)
    | _ => none
  | _ => none

mutual
/-- Directize every indirect call of a tree. -/
def expr (m : BModule) (tys : List TypeIdx) : BExpr → BExpr
  | .op i args =>
    let args := exprs m tys args
    match direct m tys i args with
    | some (j, args') => .op j args'
    | none => .op i args
  | .block bt b => .block bt (exprs m tys b)
  | .loop bt b => .loop bt (exprs m tys b)
  | .if_ bt c t e => .if_ bt (exprs m tys c) (exprs m tys t) (exprs m tys e)
  | .tryTable bt cs b => .tryTable bt cs (exprs m tys b)
/-- `expr` on a list. -/
def exprs (m : BModule) (tys : List TypeIdx) : List BExpr → List BExpr
  | [] => []
  | e :: es => expr m tys e :: exprs m tys es
end

end Directize

/-- The rewritten module, before the validity check. -/
def Directize.run (m : BModule) : BModule :=
  let tys := Exe.funcTypeIdxs { m.base with funcs := m.funcs.map fun f => ⟨f.type, [], []⟩ }
  { m with funcs := m.funcs.map fun f => { f with body := Directize.exprs m tys f.body } }

/-- **Directize**: indirect calls through a known slot of a private, immutable table
become direct calls. The identity on modules without tables or with table64 tables
or non-i32 active element offsets, and on modules whose data offsets fall outside
`profileData` (the instantiation simulation's original i32-constant boundary). -/
def directize (m : BModule) : BModule :=
  if !m.base.data.all profileData then m
  else if m.base.tables.isEmpty || !Directize.frozen m || !Directize.elemsOk m ||
      !Directize.i32Only m then m
  else if Exe.validOk (Directize.run m) then Directize.run m else m

end Silmaril.Wasm.Binaryen
