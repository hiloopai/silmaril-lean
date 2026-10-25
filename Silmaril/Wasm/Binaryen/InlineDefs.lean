module

public import Silmaril.Wasm.Binaryen.NTyping

@[expose] public section

/-! # Inlining: the syntactic transformations

The definitions `inlineSite`/`inlineN` are built from (`Binaryen/Inline.lean`):
layer D relocation (`shiftLocalsL`, `retToBrL`) and the D-level site
(`siteCode`); layer N relocation (`NExpr.shiftLocals`, `NExpr.returnToBr`) and
Binaryen's named block (`inlineN`). Kept apart so that the resolution lemmas
(`Binaryen/InlineResolve.lean`) can be imported by `Inline.lean`.
-/

namespace Silmaril.Wasm.Binaryen

open Validation


/-- Shift an index by `base` (unchanged on overflow; overflow is excluded by the
callers' validity hypotheses). -/
def shiftIdx {k : IndexKind} (base : Nat) (x : Idx k) : Idx k :=
  (Idx.ofNat? (x.toNat + base)).getD x

/-- A label index from a depth. -/
def labelIdx (d : Nat) : LabelIdx := (Idx.ofNat? d).getD ⟨⟨0, by decide⟩⟩

/-- Shift the local accesses of a flat instruction. -/
def shiftLocalInstr (base : Nat) : Instr → Instr
  | .localGet x => .localGet (shiftIdx base x)
  | .localSet x => .localSet (shiftIdx base x)
  | .localTee x => .localTee (shiftIdx base x)
  | i => i

mutual
/-- Shift every local index by `base` (callee locals move after the caller's). -/
def shiftLocalsE (base : Nat) : BExpr → BExpr
  | .op i args => .op (shiftLocalInstr base i) (shiftLocalsL base args)
  | .block bt b => .block bt (shiftLocalsL base b)
  | .loop bt b => .loop bt (shiftLocalsL base b)
  | .if_ bt c t e => .if_ bt (shiftLocalsL base c) (shiftLocalsL base t) (shiftLocalsL base e)
  | .tryTable bt cs b => .tryTable bt cs (shiftLocalsL base b)
/-- `shiftLocalsE` on a list. -/
def shiftLocalsL (base : Nat) : List BExpr → List BExpr
  | [] => []
  | e :: es => shiftLocalsE base e :: shiftLocalsL base es
end

mutual
/-- `return` at nesting depth `d` becomes `br d` (to the inlined block). -/
def retToBrE (d : Nat) : BExpr → BExpr
  | .op .return_ args => .op (.br (labelIdx d)) (retToBrL d args)
  | .op i args => .op i (retToBrL d args)
  | .block bt b => .block bt (retToBrL (d + 1) b)
  | .loop bt b => .loop bt (retToBrL (d + 1) b)
  | .if_ bt c t e => .if_ bt (retToBrL d c) (retToBrL (d + 1) t) (retToBrL (d + 1) e)
  | .tryTable bt cs b => .tryTable bt cs (retToBrL (d + 1) b)
/-- `retToBrE` on a list. -/
def retToBrL (d : Nat) : List BExpr → List BExpr
  | [] => []
  | e :: es => retToBrE d e :: retToBrL d es
end

/-- The zero constant of a defaultable numeric or vector type. -/
def zeroInstr : ValType → Option Instr
  | .num (.int t) => some (.intConst t 0)
  | .num (.float t) => some (.floatConst t 0)
  | .vec _ => some (.vecConst 0)
  | .ref _ => none

/-- **The inlined site** (layer D): operands, then a block of the callee's type that
stores the parameters into caller locals `base ..`, re-zeroes the callee's vars
and runs the shifted callee body with `return` as `br`. -/
def siteCode (ty : TypeIdx) (base np : Nat) (ls : List ValType) (args body : List BExpr) :
    Option (List BExpr) := do
  let sets ← (List.range np).reverse.mapM fun j => do
    let x : LocalIdx ← Idx.ofNat? (base + j)
    pure (BExpr.op (.localSet x) [])
  let zeros ← (List.range ls.length).mapM fun j => do
    let t ← ls[j]?
    let z ← zeroInstr t
    let x : LocalIdx ← Idx.ofNat? (base + np + j)
    pure (BExpr.op (.localSet x) [.op z []])
  let body' := retToBrL 0 (shiftLocalsL base body)
  pure (args ++ [BExpr.block (.typeIdx ty) (sets ++ zeros ++ body')])

/-- `__inlined_func$<f>`. -/
def inlinedName (f : Name) : Name := "__inlined_func$" ++ f

/-- The zero literal of a profile type. -/
def zeroLit : ValType → Lit
  | .num (.int .i64) => .i64 0
  | _ => .i32 0

mutual
/-- Shift local indices by `base`. -/
def NExpr.shiftLocals (base : Nat) : NExpr → NExpr
  | .block l body ty => .block l (NExpr.shiftLocalsList base body) ty
  | .loop l body ty => .loop l (NExpr.shiftLocals base body) ty
  | .if_ c t e ty => .if_ (NExpr.shiftLocals base c) (NExpr.shiftLocals base t)
      (NExpr.shiftLocalsOpt base e) ty
  | .br l v c => .br l (NExpr.shiftLocalsOpt base v) (NExpr.shiftLocalsOpt base c)
  | .switch ls d v c => .switch ls d (NExpr.shiftLocalsOpt base v) (NExpr.shiftLocals base c)
  | .call f args => .call f (NExpr.shiftLocalsList base args)
  | .localGet i => .localGet (i + base)
  | .localSet i v tee => .localSet (i + base) (NExpr.shiftLocals base v) tee
  | .globalSet g v => .globalSet g (NExpr.shiftLocals base v)
  | .unary op v => .unary op (NExpr.shiftLocals base v)
  | .drop v => .drop (NExpr.shiftLocals base v)
  | .binary op a b => .binary op (NExpr.shiftLocals base a) (NExpr.shiftLocals base b)
  | .select a b c => .select (NExpr.shiftLocals base a) (NExpr.shiftLocals base b)
      (NExpr.shiftLocals base c)
  | .return_ v => .return_ (NExpr.shiftLocalsOpt base v)
  | .globalGet g => .globalGet g
  | .const c => .const c
  | .nop => .nop
  | .unreachable => .unreachable
/-- On a list. -/
def NExpr.shiftLocalsList (base : Nat) : List NExpr → List NExpr
  | [] => []
  | e :: es => NExpr.shiftLocals base e :: NExpr.shiftLocalsList base es
/-- On an optional child. -/
def NExpr.shiftLocalsOpt (base : Nat) : Option NExpr → Option NExpr
  | none => none
  | some e => some (NExpr.shiftLocals base e)
end

mutual
/-- `return v` becomes `br fresh v` (`ReturnUpdater`, `Inlining.cpp:340`). -/
def NExpr.returnToBr (fresh : Name) : NExpr → NExpr
  | .return_ v => .br fresh (NExpr.returnToBrOpt fresh v) none
  | .block l body ty => .block l (NExpr.returnToBrList fresh body) ty
  | .loop l body ty => .loop l (NExpr.returnToBr fresh body) ty
  | .if_ c t e ty => .if_ (NExpr.returnToBr fresh c) (NExpr.returnToBr fresh t)
      (NExpr.returnToBrOpt fresh e) ty
  | .br l v c => .br l (NExpr.returnToBrOpt fresh v) (NExpr.returnToBrOpt fresh c)
  | .switch ls d v c => .switch ls d (NExpr.returnToBrOpt fresh v) (NExpr.returnToBr fresh c)
  | .call f args => .call f (NExpr.returnToBrList fresh args)
  | .localSet i v tee => .localSet i (NExpr.returnToBr fresh v) tee
  | .globalSet g v => .globalSet g (NExpr.returnToBr fresh v)
  | .unary op v => .unary op (NExpr.returnToBr fresh v)
  | .drop v => .drop (NExpr.returnToBr fresh v)
  | .binary op a b => .binary op (NExpr.returnToBr fresh a) (NExpr.returnToBr fresh b)
  | .select a b c => .select (NExpr.returnToBr fresh a) (NExpr.returnToBr fresh b)
      (NExpr.returnToBr fresh c)
  | .localGet i => .localGet i
  | .globalGet g => .globalGet g
  | .const c => .const c
  | .nop => .nop
  | .unreachable => .unreachable
/-- On a list. -/
def NExpr.returnToBrList (fresh : Name) : List NExpr → List NExpr
  | [] => []
  | e :: es => NExpr.returnToBr fresh e :: NExpr.returnToBrList fresh es
/-- On an optional child. -/
def NExpr.returnToBrOpt (fresh : Name) : Option NExpr → Option NExpr
  | none => none
  | some e => some (NExpr.returnToBr fresh e)
end

/-- **Binaryen's inlined block** (`doCodeInlining`): operands are stored inside the
named block, vars are re-zeroed, `return` branches to the block. -/
def inlineN (callee : NFunc) (base : Nat) (args : List NExpr) (fresh : Name) : NExpr :=
  let np := callee.params.length
  let sets := args.mapIdx fun j a => NExpr.localSet (base + j) a false
  let zeros := callee.vars.mapIdx fun j t =>
    NExpr.localSet (base + np + j) (.const (zeroLit t)) false
  let body := (callee.body.shiftLocals base).returnToBr fresh
  .block (some fresh) (sets ++ zeros ++ [body]) (resultTy callee.results)

end Silmaril.Wasm.Binaryen
