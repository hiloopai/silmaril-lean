module

public import Silmaril.Wasm.Binaryen.Uniform
public import Silmaril.Wasm.Binaryen.Exe.Valid
public import Silmaril.Wasm.Binaryen.FastChecks

@[expose] public section

/-! # Experimental RemoveUnusedBrs

Remove branch-free block wrappers and turn an initial conditional exit from an empty
block into an inverted `if`. The latter retains a label around the tail, so its branch
depths do not change. Wrapper removal requires *no* free labels, rather than merely no
branch to zero: this conservative subset needs no label renumbering.

A parameterized wrapper `block (typeIdx t) { local.set xn; ...; local.set x1; body }`, as
inlining emits it, first stores its parameters: the stores move before the block, which
keeps its label and its result (`block (result r) body`), so branches to it (an inlined
`return`) are unchanged. Without such branches the block is then spliced like any other.

Run functions only. The verified stage is `invertGuardsChecked`: the guard conversion
alone (`invertGuards`), kept when the validator accepts its result; its contract is in
`Exe/RemoveUnusedBrsSound.lean`. Wrapper removal is not a code simulation of the
closure kind (the left side runs a body that the right side runs under a label), so
`removeUnusedBrs` with it stays unverified and is in neither pipeline (its contract is
not established here).
-/

namespace Silmaril.Wasm.Binaryen

namespace RemoveUnusedBrs

/-- Parameterized wrappers are first rewritten by `hoistParams`. -/
def canUnwrap (m : BModule) (bt : BlockType) (body : List BExpr) : Bool :=
  (BExpr.labelsList body).isEmpty && match bt with
  | .empty | .value _ => true
  | .typeIdx t => match m.funcType? t with
    | some ft => ft.params.isEmpty
    | none => false

/-- `canUnwrap` with the label test done without building the label list. -/
def canUnwrapFast (m : BModule) (bt : BlockType) (body : List BExpr) : Bool :=
  !BExpr.escL 0 body && match bt with
  | .empty | .value _ => true
  | .typeIdx t => match m.funcType? t with
    | some ft => ft.params.isEmpty
    | none => false

/-- Compiled code runs `canUnwrapFast`. -/
@[csimp] theorem canUnwrap_eq_fast : @canUnwrap = @canUnwrapFast := by
  funext m bt body
  rw [canUnwrap.eq_def, canUnwrapFast.eq_def, BExpr.labelsList_isEmpty]

/-- Split off the `n` flat stores that begin a body. -/
def paramSets : Nat → List BExpr → Option (List BExpr × List BExpr)
  | 0, body => some ([], body)
  | n + 1, s@(.op (.localSet _) []) :: body =>
      (paramSets n body).map fun (ss, rest) => (s :: ss, rest)
  | _ + 1, _ => none

/-- A wrapper with parameters, at most one result and a body that starts by storing all
its parameters: the stores, the block type without parameters, and the rest of the body.
The stores contain no branch, so moving them out of the label changes no depth. -/
def hoistParams (m : BModule) (bt : BlockType) (body : List BExpr) :
    Option (List BExpr × BlockType × List BExpr) :=
  match bt with
  | .typeIdx t => match m.funcType? t with
    | some ft =>
      let bt' : Option BlockType := match ft.results with
        | [] => some .empty
        | [r] => some (.value r)
        | _ => none
      match ft.params, bt', paramSets ft.params.length body with
      | _ :: _, some b, some (ss, rest) => some (ss, b, rest)
      | _, _, _ => none
    | none => none
  | _ => none

/-- A local read produces exactly the guard's one operand and cannot branch. Keeping
this shape narrow also avoids moving a stack prefix across an empty `if` boundary. -/
def invertGuard (body : List BExpr) : Option (List BExpr × List BExpr) :=
  match body with
  | .op (.brIf l) [.op (.localGet x) []] :: rest =>
      if l.toNat == 0 && !(BExpr.labelsList rest).contains 0 then
        some ([.op (.intTestOp .i32 .eqz) [.op (.localGet x) []]], rest)
      else none
  | .op (.localGet x) [] :: .op (.brIf l) [] :: rest =>
      if l.toNat == 0 && !(BExpr.labelsList rest).contains 0 then
        some ([.op (.intTestOp .i32 .eqz) [.op (.localGet x) []]], rest)
      else none
  | _ => none

/-- Rewrite a block after visiting its body. Guard conversion retains the block's
label for the tail; no other exit may target that label. -/
def block (m : BModule) (bt : BlockType) (body : List BExpr) : List BExpr :=
  let (pre, bt, body) := (hoistParams m bt body).getD ([], bt, body)
  pre ++ match bt, invertGuard body with
  | .empty, some (cond, rest) => [.if_ .empty cond rest []]
  | _, _ => if canUnwrap m bt body then body else [.block bt body]

mutual
/-- Bottom-up rewriting can splice a wrapper even inside an operator's operands. -/
def expr (m : BModule) : BExpr → List BExpr
  | .op i args => [.op i (seq m args)]
  | .block bt body => block m bt (seq m body)
  | .loop bt body => [.loop bt (seq m body)]
  | .if_ bt cond thn els => [.if_ bt (seq m cond) (seq m thn) (seq m els)]
  | .tryTable bt cs body => [.tryTable bt cs (seq m body)]
/-- Sequence traversal preserves the order of the spliced instructions. -/
def seq (m : BModule) : List BExpr → List BExpr
  | [] => []
  | e :: es => expr m e ++ seq m es
end

end RemoveUnusedBrs

/-- Branch cleanup, including wrappers left by the inliner (unverified). -/
def removeUnusedBrs (m : BModule) : BModule := m.mapBodies (RemoveUnusedBrs.seq m)

/-! ## Guard conversion alone -/

namespace RemoveUnusedBrs

/-- Convert an empty-typed block that opens with a guard (after visiting its body). -/
def guardBlock (bt : BlockType) (body : List BExpr) : BExpr :=
  match bt, invertGuard body with
  | .empty, some (cond, rest) => .if_ .empty cond rest []
  | _, _ => .block bt body

mutual
/-- Guard conversion of a tree, bottom-up. -/
def guardE : BExpr → BExpr
  | .op i args => .op i (guardL args)
  | .block bt body => guardBlock bt (guardL body)
  | .loop bt body => .loop bt (guardL body)
  | .if_ bt cond thn els => .if_ bt (guardL cond) (guardL thn) (guardL els)
  | .tryTable bt cs body => .tryTable bt cs (guardL body)
/-- Guard conversion of a sequence. -/
def guardL : List BExpr → List BExpr
  | [] => []
  | e :: es => guardE e :: guardL es
end

end RemoveUnusedBrs

/-- The guard conversion of every function body. -/
def invertGuards (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := RemoveUnusedBrs.guardL f.body } }

/-- **The RemoveUnusedBrs stage**: the guard conversion, kept when the validator accepts
it. -/
def invertGuardsChecked (m : BModule) : BModule :=
  if Exe.validOk (invertGuards m) then invertGuards m else m

end Silmaril.Wasm.Binaryen
