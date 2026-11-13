module

public import Silmaril.Wasm.V1.Execution.Step

/-!
# A big-step semantics for WebAssembly 1.0

This is the Lean counterpart of the big-step semantics of Watt, Maksimović,
Krishnaswami and Gardner, *A Program Logic for First-Order Encapsulated
WebAssembly* (ECOOP 2019), Appendix A. Execution of a code sequence yields a
`BigResult`: a normal value stack, an in-progress branch, an in-progress
return, or a trap. The in-progress branch and return results replace the
official semantics' single-step jump out of arbitrarily many enclosing
constructs, which is hard to reason about inductively.

Two presentational choices differ from the paper, both forced by matching
`Silmaril.Wasm.V1.Execution.Step` exactly rather than the paper's small-step
semantics; `docs/projects/wasm-wasi.md` records them.

* The operand stack is a separate list of values rather than a prefix of
  `const` instructions inside the code. This follows the prose semantics, makes
  every rule driven by the head of the code list, and is reconciled with the
  concatenated form by `BigStep.values_append_iff`.
* Branch and return results carry the *whole* operand stack present at the
  branch, and the arity is checked where the branch lands, at the enclosing
  `label` or `frame`. The paper instead fixes the arity at the branch itself
  using the `labs`/`ret` indices of its judgement. Our `label` reduction rule
  `Execution.PureStep.labelBranchOuter` accumulates operands the same way, so
  the indices would make the two semantics inequivalent on ill-typed code.
  The paper's arity side condition has no counterpart at the branch itself:
  with no `labs` index there is nothing to compare the transferred stack
  against. It is discharged where the branch lands, at `BigStep.labelBrZero`
  and `BigStep.frameRet`, and in the logic by the fixed stack length of the
  label assertion.

Two premises are forced by the machine rather than chosen: `frameNormal` checks
the retiring frame's arity, which the paper's `local` value congruence does not,
and `invokeWasm` requires `ft.results.length ≤ 1`, which the paper's `callcl`
rule does not. `docs/projects/wasm-wasi.md` records both.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1 Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- The four execution results of the paper: `Normal`, `Break`, `Return`, `Trap`. -/
inductive BigResult where
  | normal (values : List Value)
  | br (label : LabelIdx) (values : List Value)
  | ret (values : List Value)
  | trap

/-- A completed execution: the final store, the final frame, and the result. -/
structure Outcome (H : Type*) where
  store : Store H
  frame : Frame
  result : BigResult

/-- Operand and state effect of a non-control instruction that does not trap.

`args` are the operands consumed, bottom-first, and `rets` those produced. The
surrounding operand stack is supplied by `BigStep.plain`, so every rule here
mentions only what the instruction touches. -/
inductive Plain {H : Type*} : Store H → Frame → List Value → Silmaril.Wasm.V1.Instr →
    Store H → Frame → List Value → Prop where
  | nop (s : Store H) (f : Frame) : Plain s f [] .nop s f []
  | drop (s : Store H) (f : Frame) (v : Value) : Plain s f [v] .drop s f []
  | selectZero (s : Store H) (f : Frame) (a b : Value) (sameType : a.type = b.type) :
      Plain s f [a, b, .int .i32 0] .select s f [b]
  | selectNonzero (s : Store H) (f : Frame) (a b : Value) (sameType : a.type = b.type)
      (c : BitVec 32) (nonzero : c ≠ 0) :
      Plain s f [a, b, .int .i32 c] .select s f [a]
  | intConst (s : Store H) (f : Frame) (t : IntType) (bits : BitVec t.width) :
      Plain s f [] (.intConst t bits) s f [.int t bits]
  | floatConst (s : Store H) (f : Frame) (t : FloatType) (bits : BitVec t.width) :
      Plain s f [] (.floatConst t bits) s f [.float t bits]
  | localGet (s : Store H) (f : Frame) (i : LocalIdx) (v : Value)
      (found : f.locals[i.toNat]? = some v) :
      Plain s f [] (.localGet i) s f [v]
  | localSet (s : Store H) (f : Frame) (i : LocalIdx) (v old : Value)
      (found : f.locals[i.toNat]? = some old) :
      Plain s f [v] (.localSet i) s {f with locals := f.locals.set i.toNat v} []
  | localTee (s : Store H) (f : Frame) (i : LocalIdx) (v old : Value)
      (found : f.locals[i.toNat]? = some old) :
      Plain s f [v] (.localTee i) s {f with locals := f.locals.set i.toNat v} [v]
  | globalGet (s : Store H) (f : Frame) (i : GlobalIdx) (a : GlobalAddr) (g : GlobalInst)
      (index : f.module.globals[i.toNat]? = some a) (found : s.globals[a.value]? = some g) :
      Plain s f [] (.globalGet i) s f [g.value]
  | globalSet (s : Store H) (f : Frame) (i : GlobalIdx) (a : GlobalAddr) (g : GlobalInst)
      (v : Value) (index : f.module.globals[i.toNat]? = some a)
      (found : s.globals[a.value]? = some g) (mutable : g.mutability = .var) :
      Plain s f [v] (.globalSet i) (setGlobal s a {g with value := v}) f []
  | intLoad (s : Store H) (f : Frame) (t : IntType) (packed : Option (Silmaril.Wasm.V1.PackSize × Signedness))
      (arg : Silmaril.Wasm.V1.MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst) (v : Value)
      (memory : frameMemory s f = some (a, m))
      (loaded : loadInt t packed m.data (effectiveAddress c arg) = some v) :
      Plain s f [.int .i32 c] (.intLoad t packed arg) s f [v]
  | floatLoad (s : Store H) (f : Frame) (t : FloatType) (arg : Silmaril.Wasm.V1.MemArg) (c : BitVec 32)
      (a : MemAddr) (m : MemInst) (v : Value) (memory : frameMemory s f = some (a, m))
      (loaded : loadFloat t m.data (effectiveAddress c arg) = some v) :
      Plain s f [.int .i32 c] (.floatLoad t arg) s f [v]
  | intStore (s : Store H) (f : Frame) (t : IntType) (packed : Option Silmaril.Wasm.V1.PackSize)
      (arg : Silmaril.Wasm.V1.MemArg) (c : BitVec 32) (x : BitVec t.width) (a : MemAddr) (m : MemInst)
      (bytes : Memory.Bytes) (memory : frameMemory s f = some (a, m))
      (stored : storeInt t packed m.data (effectiveAddress c arg) x = some bytes) :
      Plain s f [.int .i32 c, .int t x] (.intStore t packed arg)
        (setMemory s a {m with data := bytes}) f []
  | floatStore (s : Store H) (f : Frame) (t : FloatType) (arg : Silmaril.Wasm.V1.MemArg) (c : BitVec 32)
      (x : BitVec t.width) (a : MemAddr) (m : MemInst) (bytes : Memory.Bytes)
      (memory : frameMemory s f = some (a, m))
      (stored : storeFloat t m.data (effectiveAddress c arg) x = some bytes) :
      Plain s f [.int .i32 c, .float t x] (.floatStore t arg)
        (setMemory s a {m with data := bytes}) f []
  | memorySize (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst)
      (memory : frameMemory s f = some (a, m)) :
      Plain s f [] .memorySize s f [.int .i32 (BitVec.ofNat 32 (Memory.size m.data))]
  | memoryGrow (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst) (c r : BitVec 32)
      (bytes : Memory.Bytes) (memory : frameMemory s f = some (a, m))
      (grown : Memory.Grow m.data m.max c.toNat bytes r) :
      Plain s f [.int .i32 c] .memoryGrow (setMemory s a {m with data := bytes}) f
        [.int .i32 r]
  | intUnary (s : Store H) (f : Frame) (t : IntType) (op : Silmaril.Wasm.V1.IntUnOp) (x : BitVec t.width) :
      Plain s f [.int t x] (.intUnOp t op) s f [.int t (Numerics.intUnOp t op.toCore x)]
  | intBinary (s : Store H) (f : Frame) (t : IntType) (op : IntBinOp) (x y z : BitVec t.width)
      (result : Numerics.intBinOp t op x y = .ok z) :
      Plain s f [.int t x, .int t y] (.intBinOp t op) s f [.int t z]
  | intTest (s : Store H) (f : Frame) (t : IntType) (op : IntTestOp) (x : BitVec t.width) :
      Plain s f [.int t x] (.intTestOp t op) s f [.int .i32 (Numerics.intTestOp t op x)]
  | intRel (s : Store H) (f : Frame) (t : IntType) (op : IntRelOp) (x y : BitVec t.width) :
      Plain s f [.int t x, .int t y] (.intRelOp t op) s f
        [.int .i32 (Numerics.intRelOp t op x y)]
  | floatUnary (s : Store H) (f : Frame) (t : FloatType) (op : FloatUnOp) (x y : BitVec t.width)
      (result : Numerics.floatUnOpRel t op x y) :
      Plain s f [.float t x] (.floatUnOp t op) s f [.float t y]
  | floatBinary (s : Store H) (f : Frame) (t : FloatType) (op : FloatBinOp)
      (x y z : BitVec t.width) (result : Numerics.floatBinOpRel t op x y z) :
      Plain s f [.float t x, .float t y] (.floatBinOp t op) s f [.float t z]
  | floatRel (s : Store H) (f : Frame) (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width) :
      Plain s f [.float t x, .float t y] (.floatRelOp t op) s f
        [.int .i32 (Numerics.floatRelOp t op x y)]
  | convert (s : Store H) (f : Frame) (op : Silmaril.Wasm.V1.ConvertOp) (x : Numerics.NumValue op.toCore.source)
      (y : Numerics.NumValue op.toCore.target) (result : Numerics.convertRel op.toCore x (.ok y)) :
      Plain s f [⟨op.toCore.source, x⟩] (.convert op) s f [⟨op.toCore.target, y⟩]

/-- Operand configurations of a non-control instruction that trap.

No trapping instruction of WebAssembly 1.0 changes the store or the frame. -/
inductive PlainTrap {H : Type*} : Store H → Frame → List Value → Silmaril.Wasm.V1.Instr → Prop where
  | unreachable (s : Store H) (f : Frame) : PlainTrap s f [] .unreachable
  | intBinary (s : Store H) (f : Frame) (t : IntType) (op : IntBinOp) (x y : BitVec t.width)
      (err : Numerics.IntTrap) (result : Numerics.intBinOp t op x y = .error err) :
      PlainTrap s f [.int t x, .int t y] (.intBinOp t op)
  | convert (s : Store H) (f : Frame) (op : Silmaril.Wasm.V1.ConvertOp) (x : Numerics.NumValue op.toCore.source)
      (err : Numerics.FloatTrap) (result : Numerics.convertRel op.toCore x (.error err)) :
      PlainTrap s f [⟨op.toCore.source, x⟩] (.convert op)
  | intLoad (s : Store H) (f : Frame) (t : IntType) (packed : Option (Silmaril.Wasm.V1.PackSize × Signedness))
      (arg : Silmaril.Wasm.V1.MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst)
      (memory : frameMemory s f = some (a, m))
      (loaded : loadInt t packed m.data (effectiveAddress c arg) = none) :
      PlainTrap s f [.int .i32 c] (.intLoad t packed arg)
  | floatLoad (s : Store H) (f : Frame) (t : FloatType) (arg : Silmaril.Wasm.V1.MemArg) (c : BitVec 32)
      (a : MemAddr) (m : MemInst) (memory : frameMemory s f = some (a, m))
      (loaded : loadFloat t m.data (effectiveAddress c arg) = none) :
      PlainTrap s f [.int .i32 c] (.floatLoad t arg)
  | intStore (s : Store H) (f : Frame) (t : IntType) (packed : Option Silmaril.Wasm.V1.PackSize)
      (arg : Silmaril.Wasm.V1.MemArg) (c : BitVec 32) (x : BitVec t.width) (a : MemAddr) (m : MemInst)
      (memory : frameMemory s f = some (a, m))
      (stored : storeInt t packed m.data (effectiveAddress c arg) x = none) :
      PlainTrap s f [.int .i32 c, .int t x] (.intStore t packed arg)
  | floatStore (s : Store H) (f : Frame) (t : FloatType) (arg : Silmaril.Wasm.V1.MemArg) (c : BitVec 32)
      (x : BitVec t.width) (a : MemAddr) (m : MemInst)
      (memory : frameMemory s f = some (a, m))
      (stored : storeFloat t m.data (effectiveAddress c arg) x = none) :
      PlainTrap s f [.int .i32 c, .float t x] (.floatStore t arg)

/-- `BigStep host s f vs code o` runs `code` from store `s`, frame `f` and
operand stack `vs` (bottom-first) to the outcome `o`.

There is no rule for a diverging host call, and none for a branch or return
escaping a `frame`; those configurations have no derivation, matching the
corresponding stuck or infinite small-step reductions. -/
inductive BigStep {H : Type*} (host : HostSemantics H) :
    Store H → Frame → List Value → List Admin → Outcome H → Prop where
  /-- An exhausted code sequence returns the whole operand stack. -/
  | nil (s : Store H) (f : Frame) (vs : List Value) :
      BigStep host s f vs [] ⟨s, f, .normal vs⟩
  | plain {s s' : Store H} {f f' : Frame} {args rets : List Value} {i : Silmaril.Wasm.V1.Instr}
      {vs : List Value} {es : List Admin} {o : Outcome H}
      (step : Plain s f args i s' f' rets) (rest : BigStep host s' f' (vs ++ rets) es o) :
      BigStep host s f (vs ++ args) (.source i :: es) o
  | plainTrap {s : Store H} {f : Frame} {args : List Value} {i : Silmaril.Wasm.V1.Instr}
      {vs : List Value} {es : List Admin} (step : PlainTrap s f args i) :
      BigStep host s f (vs ++ args) (.source i :: es) ⟨s, f, .trap⟩
  /-- A trap in the code discards the rest of the configuration. -/
  | trap (s : Store H) (f : Frame) (vs : List Value) (es : List Admin) :
      BigStep host s f vs (.trap :: es) ⟨s, f, .trap⟩
  | block {s : Store H} {f : Frame} {vs : List Value} {bt : Silmaril.Wasm.V1.BlockType} {body : Silmaril.Wasm.V1.Expr}
      {es : List Admin} {o : Outcome H}
      (rest : BigStep host s f vs (.label bt.toList.length [] (expression body) :: es) o) :
      BigStep host s f vs (.source (.block bt body) :: es) o
  | loop {s : Store H} {f : Frame} {vs : List Value} {bt : Silmaril.Wasm.V1.BlockType} {body : Silmaril.Wasm.V1.Expr}
      {es : List Admin} {o : Outcome H}
      (rest : BigStep host s f vs (.label 0 [.loop bt body] (expression body) :: es) o) :
      BigStep host s f vs (.source (.loop bt body) :: es) o
  | ifZero {s : Store H} {f : Frame} {vs : List Value} {bt : Silmaril.Wasm.V1.BlockType} {left right : Silmaril.Wasm.V1.Expr}
      {es : List Admin} {o : Outcome H}
      (rest : BigStep host s f vs (.source (.block bt right) :: es) o) :
      BigStep host s f (vs ++ [.int .i32 0]) (.source (.if_ bt left right) :: es) o
  | ifNonzero {s : Store H} {f : Frame} {vs : List Value} {bt : Silmaril.Wasm.V1.BlockType} {left right : Silmaril.Wasm.V1.Expr}
      {es : List Admin} {o : Outcome H} {c : BitVec 32} (nonzero : c ≠ 0)
      (rest : BigStep host s f vs (.source (.block bt left) :: es) o) :
      BigStep host s f (vs ++ [.int .i32 c]) (.source (.if_ bt left right) :: es) o
  /-- A branch abandons the code after it, carrying the operand stack along. -/
  | br (s : Store H) (f : Frame) (vs : List Value) (l : LabelIdx) (es : List Admin) :
      BigStep host s f vs (.source (.br l) :: es) ⟨s, f, .br l vs⟩
  | brIfZero {s : Store H} {f : Frame} {vs : List Value} {l : LabelIdx} {es : List Admin}
      {o : Outcome H} (rest : BigStep host s f vs es o) :
      BigStep host s f (vs ++ [.int .i32 0]) (.source (.brIf l) :: es) o
  | brIfNonzero {s : Store H} {f : Frame} {vs : List Value} {l : LabelIdx} {es : List Admin}
      {o : Outcome H} {c : BitVec 32} (nonzero : c ≠ 0)
      (rest : BigStep host s f vs (.source (.br l) :: es) o) :
      BigStep host s f (vs ++ [.int .i32 c]) (.source (.brIf l) :: es) o
  | brTable {s : Store H} {f : Frame} {vs : List Value} {ls : List LabelIdx} {dflt : LabelIdx}
      {es : List Admin} {o : Outcome H} {c : BitVec 32}
      (rest : BigStep host s f vs (.source (.br (ls[c.toNat]?.getD dflt)) :: es) o) :
      BigStep host s f (vs ++ [.int .i32 c]) (.source (.brTable ls dflt) :: es) o
  | return_ (s : Store H) (f : Frame) (vs : List Value) (es : List Admin) :
      BigStep host s f vs (.source .return_ :: es) ⟨s, f, .ret vs⟩
  | call {s : Store H} {f : Frame} {vs : List Value} {i : FuncIdx} {a : FuncAddr}
      {es : List Admin} {o : Outcome H} (found : f.module.funcs[i.toNat]? = some a)
      (rest : BigStep host s f vs (.invoke a :: es) o) :
      BigStep host s f vs (.source (.call i) :: es) o
  | callIndirect {s : Store H} {f : Frame} {vs : List Value} {i : TypeIdx} {c : BitVec 32}
      {table : TableInst} {a : FuncAddr} {fn : FuncInst Silmaril.Wasm.V1.Func H} {ft : Silmaril.Wasm.V1.FuncType}
      {es : List Admin} {o : Outcome H}
      (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
      (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
      (typeMatch : fn.type = ft) (rest : BigStep host s f vs (.invoke a :: es) o) :
      BigStep host s f (vs ++ [.int .i32 c]) (.source (.callIndirect i) :: es) o
  | callIndirectBounds {s : Store H} {f : Frame} {vs : List Value} {i : TypeIdx} {c : BitVec 32}
      {table : TableInst} {es : List Admin} (tableFound : frameTable s f = some table)
      (outOfBounds : table.refs[c.toNat]? = none) :
      BigStep host s f (vs ++ [.int .i32 c]) (.source (.callIndirect i) :: es) ⟨s, f, .trap⟩
  | callIndirectNull {s : Store H} {f : Frame} {vs : List Value} {i : TypeIdx} {c : BitVec 32}
      {table : TableInst} {es : List Admin} (tableFound : frameTable s f = some table)
      (null : table.refs[c.toNat]? = some none) :
      BigStep host s f (vs ++ [.int .i32 c]) (.source (.callIndirect i) :: es) ⟨s, f, .trap⟩
  | callIndirectType {s : Store H} {f : Frame} {vs : List Value} {i : TypeIdx} {c : BitVec 32}
      {table : TableInst} {a : FuncAddr} {fn : FuncInst Silmaril.Wasm.V1.Func H} {ft : Silmaril.Wasm.V1.FuncType}
      {es : List Admin} (tableFound : frameTable s f = some table)
      (typeFound : f.module.types[i.toNat]? = some ft)
      (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
      (typeMismatch : fn.type ≠ ft) :
      BigStep host s f (vs ++ [.int .i32 c]) (.source (.callIndirect i) :: es) ⟨s, f, .trap⟩
  | invokeWasm {s : Store H} {f : Frame} {vs args : List Value} {a : FuncAddr} {ft : Silmaril.Wasm.V1.FuncType}
      {md : ModuleInst} {fn : Silmaril.Wasm.V1.Func} {es : List Admin} {o : Outcome H}
      (found : s.funcs[a.value]? = some (.wasm ft md fn))
      (arity : args.length = ft.params.length) (resultArity : ft.results.length ≤ 1)
      (rest : BigStep host s f vs
        (.frame ft.results.length ⟨args ++ fn.locals.map Value.zero, md⟩
          [.label ft.results.length [] (expression fn.body)] :: es) o) :
      BigStep host s f (vs ++ args) (.invoke a :: es) o
  | invokeHost {s s' : Store H} {f : Frame} {vs args : List Value} {a : FuncAddr}
      {ft : Silmaril.Wasm.V1.FuncType} {fn : H} {r : Result} {es : List Admin} {o : Outcome H}
      (found : s.funcs[a.value]? = some (.host ft fn)) (arity : args.length = ft.params.length)
      (behavior : host fn s args (.returned s' r))
      (rest : BigStep host s' f vs (result r ++ es) o) :
      BigStep host s f (vs ++ args) (.invoke a :: es) o
  /-- A label exited normally pushes the label's values onto the enclosing stack. -/
  | labelNormal {s s' : Store H} {f f' : Frame} {vs ws : List Value} {n : Nat} {cont : Silmaril.Wasm.V1.Expr}
      {body es : List Admin} {o : Outcome H}
      (inner : BigStep host s f [] body ⟨s', f', .normal ws⟩)
      (rest : BigStep host s' f' (vs ++ ws) es o) :
      BigStep host s f vs (.label n cont body :: es) o
  /-- A branch to this label transfers `n` values and continues with `cont`. -/
  | labelBrZero {s s' : Store H} {f f' : Frame} {vs extra ws : List Value} {n : Nat}
      {cont : Silmaril.Wasm.V1.Expr} {body es : List Admin} {l : LabelIdx} {o : Outcome H}
      (inner : BigStep host s f [] body ⟨s', f', .br l (extra ++ ws)⟩) (target : l.toNat = 0)
      (arity : ws.length = n) (rest : BigStep host s' f' (vs ++ ws) (expression cont ++ es) o) :
      BigStep host s f vs (.label n cont body :: es) o
  /-- A branch past this label keeps going, picking up the enclosing operands. -/
  | labelBrSucc {s s' : Store H} {f f' : Frame} {vs ws : List Value} {n : Nat} {cont : Silmaril.Wasm.V1.Expr}
      {body es : List Admin} {l : LabelIdx}
      (inner : BigStep host s f [] body ⟨s', f', .br l ws⟩) (outer : l.toNat ≠ 0) :
      BigStep host s f vs (.label n cont body :: es) ⟨s', f', .br (lowerLabel l) (vs ++ ws)⟩
  | labelRet {s s' : Store H} {f f' : Frame} {vs ws : List Value} {n : Nat} {cont : Silmaril.Wasm.V1.Expr}
      {body es : List Admin} (inner : BigStep host s f [] body ⟨s', f', .ret ws⟩) :
      BigStep host s f vs (.label n cont body :: es) ⟨s', f', .ret (vs ++ ws)⟩
  | labelTrap {s s' : Store H} {f f' : Frame} {vs : List Value} {n : Nat} {cont : Silmaril.Wasm.V1.Expr}
      {body es : List Admin} (inner : BigStep host s f [] body ⟨s', f', .trap⟩) :
      BigStep host s f vs (.label n cont body :: es) ⟨s', f', .trap⟩
  | frameNormal {s s' : Store H} {f fr fr' : Frame} {vs ws : List Value} {n : Nat}
      {body es : List Admin} {o : Outcome H}
      (inner : BigStep host s fr [] body ⟨s', fr', .normal ws⟩) (arity : ws.length = n)
      (rest : BigStep host s' f (vs ++ ws) es o) :
      BigStep host s f vs (.frame n fr body :: es) o
  | frameRet {s s' : Store H} {f fr fr' : Frame} {vs extra ws : List Value} {n : Nat}
      {body es : List Admin} {o : Outcome H}
      (inner : BigStep host s fr [] body ⟨s', fr', .ret (extra ++ ws)⟩) (arity : ws.length = n)
      (rest : BigStep host s' f (vs ++ ws) es o) :
      BigStep host s f vs (.frame n fr body :: es) o
  | frameTrap {s s' : Store H} {f fr fr' : Frame} {vs : List Value} {n : Nat}
      {body es : List Admin} (inner : BigStep host s fr [] body ⟨s', fr', .trap⟩) :
      BigStep host s f vs (.frame n fr body :: es) ⟨s', f, .trap⟩

/-! ## The height-indexed relation

`BigStepN host n` is `BigStep host` restricted to derivations of height at most
`n`. The index is what makes the soundness proof of Wasm Logic go through: both
the `[loop]` rule and the `[module]` rule for mutually recursive functions are
sound only by well-founded recursion on the execution, and a `Prop`-valued
inductive relation carries no such measure.

It is also the natural interface for an executing interpreter, where `n` is
fuel: `BigStepN host n` is decidable-in-principle progress bounded by `n`.

Everything else about the relation is identical to `BigStep`, and
`bigStep_iff_exists_height` says so. -/

/-- `BigStep host` restricted to derivations of height at most `n`. -/
inductive BigStepN {H : Type*} (host : HostSemantics H) :
    Nat → Store H → Frame → List Value → List Admin → Outcome H → Prop where
  /-- An exhausted code sequence returns the whole operand stack. -/
  | nil {n : Nat} (s : Store H) (f : Frame) (vs : List Value) :
      BigStepN host (n + 1) s f vs [] ⟨s, f, .normal vs⟩
  | plain {n : Nat} {s s' : Store H} {f f' : Frame} {args rets : List Value} {i : Silmaril.Wasm.V1.Instr}
      {vs : List Value} {es : List Admin} {o : Outcome H}
      (step : Plain s f args i s' f' rets) (rest : BigStepN host n s' f' (vs ++ rets) es o) :
      BigStepN host (n + 1) s f (vs ++ args) (.source i :: es) o
  | plainTrap {n : Nat} {s : Store H} {f : Frame} {args : List Value} {i : Silmaril.Wasm.V1.Instr}
      {vs : List Value} {es : List Admin} (step : PlainTrap s f args i) :
      BigStepN host (n + 1) s f (vs ++ args) (.source i :: es) ⟨s, f, .trap⟩
  /-- A trap in the code discards the rest of the configuration. -/
  | trap {n : Nat} (s : Store H) (f : Frame) (vs : List Value) (es : List Admin) :
      BigStepN host (n + 1) s f vs (.trap :: es) ⟨s, f, .trap⟩
  | block {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {bt : Silmaril.Wasm.V1.BlockType} {body : Silmaril.Wasm.V1.Expr}
      {es : List Admin} {o : Outcome H}
      (rest : BigStepN host n s f vs (.label bt.toList.length [] (expression body) :: es) o) :
      BigStepN host (n + 1) s f vs (.source (.block bt body) :: es) o
  | loop {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {bt : Silmaril.Wasm.V1.BlockType} {body : Silmaril.Wasm.V1.Expr}
      {es : List Admin} {o : Outcome H}
      (rest : BigStepN host n s f vs (.label 0 [.loop bt body] (expression body) :: es) o) :
      BigStepN host (n + 1) s f vs (.source (.loop bt body) :: es) o
  | ifZero {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {bt : Silmaril.Wasm.V1.BlockType}
      {left right : Silmaril.Wasm.V1.Expr} {es : List Admin} {o : Outcome H}
      (rest : BigStepN host n s f vs (.source (.block bt right) :: es) o) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 0]) (.source (.if_ bt left right) :: es) o
  | ifNonzero {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {bt : Silmaril.Wasm.V1.BlockType}
      {left right : Silmaril.Wasm.V1.Expr} {es : List Admin} {o : Outcome H} {c : BitVec 32} (nonzero : c ≠ 0)
      (rest : BigStepN host n s f vs (.source (.block bt left) :: es) o) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 c]) (.source (.if_ bt left right) :: es) o
  /-- A branch abandons the code after it, carrying the operand stack along. -/
  | br {n : Nat} (s : Store H) (f : Frame) (vs : List Value) (l : LabelIdx) (es : List Admin) :
      BigStepN host (n + 1) s f vs (.source (.br l) :: es) ⟨s, f, .br l vs⟩
  | brIfZero {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {l : LabelIdx} {es : List Admin}
      {o : Outcome H} (rest : BigStepN host n s f vs es o) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 0]) (.source (.brIf l) :: es) o
  | brIfNonzero {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {l : LabelIdx}
      {es : List Admin} {o : Outcome H} {c : BitVec 32} (nonzero : c ≠ 0)
      (rest : BigStepN host n s f vs (.source (.br l) :: es) o) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 c]) (.source (.brIf l) :: es) o
  | brTable {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {ls : List LabelIdx}
      {dflt : LabelIdx} {es : List Admin} {o : Outcome H} {c : BitVec 32}
      (rest : BigStepN host n s f vs (.source (.br (ls[c.toNat]?.getD dflt)) :: es) o) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 c]) (.source (.brTable ls dflt) :: es) o
  | return_ {n : Nat} (s : Store H) (f : Frame) (vs : List Value) (es : List Admin) :
      BigStepN host (n + 1) s f vs (.source .return_ :: es) ⟨s, f, .ret vs⟩
  | call {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {i : FuncIdx} {a : FuncAddr}
      {es : List Admin} {o : Outcome H} (found : f.module.funcs[i.toNat]? = some a)
      (rest : BigStepN host n s f vs (.invoke a :: es) o) :
      BigStepN host (n + 1) s f vs (.source (.call i) :: es) o
  | callIndirect {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {i : TypeIdx} {c : BitVec 32}
      {table : TableInst} {a : FuncAddr} {fn : FuncInst Silmaril.Wasm.V1.Func H} {ft : Silmaril.Wasm.V1.FuncType}
      {es : List Admin} {o : Outcome H}
      (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
      (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
      (typeMatch : fn.type = ft) (rest : BigStepN host n s f vs (.invoke a :: es) o) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 c]) (.source (.callIndirect i) :: es) o
  | callIndirectBounds {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {i : TypeIdx}
      {c : BitVec 32} {table : TableInst} {es : List Admin}
      (tableFound : frameTable s f = some table) (outOfBounds : table.refs[c.toNat]? = none) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 c]) (.source (.callIndirect i) :: es)
        ⟨s, f, .trap⟩
  | callIndirectNull {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {i : TypeIdx}
      {c : BitVec 32} {table : TableInst} {es : List Admin}
      (tableFound : frameTable s f = some table) (null : table.refs[c.toNat]? = some none) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 c]) (.source (.callIndirect i) :: es)
        ⟨s, f, .trap⟩
  | callIndirectType {n : Nat} {s : Store H} {f : Frame} {vs : List Value} {i : TypeIdx}
      {c : BitVec 32} {table : TableInst} {a : FuncAddr} {fn : FuncInst Silmaril.Wasm.V1.Func H} {ft : Silmaril.Wasm.V1.FuncType}
      {es : List Admin} (tableFound : frameTable s f = some table)
      (typeFound : f.module.types[i.toNat]? = some ft)
      (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
      (typeMismatch : fn.type ≠ ft) :
      BigStepN host (n + 1) s f (vs ++ [.int .i32 c]) (.source (.callIndirect i) :: es)
        ⟨s, f, .trap⟩
  | invokeWasm {n : Nat} {s : Store H} {f : Frame} {vs args : List Value} {a : FuncAddr}
      {ft : Silmaril.Wasm.V1.FuncType} {md : ModuleInst} {fn : Silmaril.Wasm.V1.Func} {es : List Admin} {o : Outcome H}
      (found : s.funcs[a.value]? = some (.wasm ft md fn))
      (arity : args.length = ft.params.length) (resultArity : ft.results.length ≤ 1)
      (rest : BigStepN host n s f vs
        (.frame ft.results.length ⟨args ++ fn.locals.map Value.zero, md⟩
          [.label ft.results.length [] (expression fn.body)] :: es) o) :
      BigStepN host (n + 1) s f (vs ++ args) (.invoke a :: es) o
  | invokeHost {n : Nat} {s s' : Store H} {f : Frame} {vs args : List Value} {a : FuncAddr}
      {ft : Silmaril.Wasm.V1.FuncType} {fn : H} {r : Result} {es : List Admin} {o : Outcome H}
      (found : s.funcs[a.value]? = some (.host ft fn)) (arity : args.length = ft.params.length)
      (behavior : host fn s args (.returned s' r))
      (rest : BigStepN host n s' f vs (result r ++ es) o) :
      BigStepN host (n + 1) s f (vs ++ args) (.invoke a :: es) o
  /-- A label exited normally pushes the label's values onto the enclosing stack. -/
  | labelNormal {k : Nat} {s s' : Store H} {f f' : Frame} {vs ws : List Value} {n : Nat}
      {cont : Silmaril.Wasm.V1.Expr} {body es : List Admin} {o : Outcome H}
      (inner : BigStepN host k s f [] body ⟨s', f', .normal ws⟩)
      (rest : BigStepN host k s' f' (vs ++ ws) es o) :
      BigStepN host (k + 1) s f vs (.label n cont body :: es) o
  /-- A branch to this label transfers `n` values and continues with `cont`. -/
  | labelBrZero {k : Nat} {s s' : Store H} {f f' : Frame} {vs extra ws : List Value} {n : Nat}
      {cont : Silmaril.Wasm.V1.Expr} {body es : List Admin} {l : LabelIdx} {o : Outcome H}
      (inner : BigStepN host k s f [] body ⟨s', f', .br l (extra ++ ws)⟩) (target : l.toNat = 0)
      (arity : ws.length = n) (rest : BigStepN host k s' f' (vs ++ ws) (expression cont ++ es) o) :
      BigStepN host (k + 1) s f vs (.label n cont body :: es) o
  /-- A branch past this label keeps going, picking up the enclosing operands. -/
  | labelBrSucc {k : Nat} {s s' : Store H} {f f' : Frame} {vs ws : List Value} {n : Nat}
      {cont : Silmaril.Wasm.V1.Expr} {body es : List Admin} {l : LabelIdx}
      (inner : BigStepN host k s f [] body ⟨s', f', .br l ws⟩) (outer : l.toNat ≠ 0) :
      BigStepN host (k + 1) s f vs (.label n cont body :: es)
        ⟨s', f', .br (lowerLabel l) (vs ++ ws)⟩
  | labelRet {k : Nat} {s s' : Store H} {f f' : Frame} {vs ws : List Value} {n : Nat} {cont : Silmaril.Wasm.V1.Expr}
      {body es : List Admin} (inner : BigStepN host k s f [] body ⟨s', f', .ret ws⟩) :
      BigStepN host (k + 1) s f vs (.label n cont body :: es) ⟨s', f', .ret (vs ++ ws)⟩
  | labelTrap {k : Nat} {s s' : Store H} {f f' : Frame} {vs : List Value} {n : Nat} {cont : Silmaril.Wasm.V1.Expr}
      {body es : List Admin} (inner : BigStepN host k s f [] body ⟨s', f', .trap⟩) :
      BigStepN host (k + 1) s f vs (.label n cont body :: es) ⟨s', f', .trap⟩
  | frameNormal {k : Nat} {s s' : Store H} {f fr fr' : Frame} {vs ws : List Value} {n : Nat}
      {body es : List Admin} {o : Outcome H}
      (inner : BigStepN host k s fr [] body ⟨s', fr', .normal ws⟩) (arity : ws.length = n)
      (rest : BigStepN host k s' f (vs ++ ws) es o) :
      BigStepN host (k + 1) s f vs (.frame n fr body :: es) o
  | frameRet {k : Nat} {s s' : Store H} {f fr fr' : Frame} {vs extra ws : List Value} {n : Nat}
      {body es : List Admin} {o : Outcome H}
      (inner : BigStepN host k s fr [] body ⟨s', fr', .ret (extra ++ ws)⟩) (arity : ws.length = n)
      (rest : BigStepN host k s' f (vs ++ ws) es o) :
      BigStepN host (k + 1) s f vs (.frame n fr body :: es) o
  | frameTrap {k : Nat} {s s' : Store H} {f fr fr' : Frame} {vs : List Value} {n : Nat}
      {body es : List Admin} (inner : BigStepN host k s fr [] body ⟨s', fr', .trap⟩) :
      BigStepN host (k + 1) s f vs (.frame n fr body :: es) ⟨s', f, .trap⟩

/-! ## Results -/

/-- Every result other than normal termination abandons the enclosing code. -/
def BigResult.Abrupt : BigResult → Prop
  | .normal _ => False
  | _ => True

/-- Push extra operands underneath a result's value stack. -/
def BigResult.extend (us : List Value) : BigResult → BigResult
  | .normal ws => .normal (us ++ ws)
  | .br l ws => .br l (us ++ ws)
  | .ret ws => .ret (us ++ ws)
  | .trap => .trap

/-- The terminal small-step code shape a result corresponds to. -/
def BigResult.code : BigResult → List Admin
  | .normal ws => values ws
  | .br l ws => values ws ++ [.source (.br l)]
  | .ret ws => values ws ++ [.source .return_]
  | .trap => [.trap]

section Reaches

variable {H : Type*}

/-- The small-step configuration that an outcome is realised by. -/
def Outcome.Reaches (host : HostSemantics H) (c : Config H) (o : Outcome H) : Prop :=
  match o.result with
  | .normal ws => Steps host c ⟨o.store, o.frame, values ws⟩
  | .trap => Steps host c ⟨o.store, o.frame, [.trap]⟩
  | .br l ws => ∃ tail, Steps host c ⟨o.store, o.frame, values ws ++ [.source (.br l)] ++ tail⟩
  | .ret ws => ∃ tail, Steps host c ⟨o.store, o.frame, values ws ++ [.source .return_] ++ tail⟩

end Reaches

end Silmaril.Wasm.Logic.V1
