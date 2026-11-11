module

public import Silmaril.Wasm.SSA.Dialect.Defs

/-!
# Out of SSA: structured dialect regions back to the fragment

`decompileFunc` maps an SSA function back to a fragment function, for the
structured subset of the dialect that the translation and the passes produce:

* every SSA variable is located (`VLoc`) in Wasm locals: an atom is a local
  (with its type) or a constant, tuples are trees of locations. Variables,
  `()`, pairs and constants bound by `let₁`/`let₂` emit no code; an operator
  `let₁` assigns a fresh local, provided the operator cannot trap there
  (`opSafe`: the SSA `Prim.op` is stuck on a trap, while Wasm would trap);
* `case` on `Prim.truthy` becomes `if`; `case` on `Prim.opT o` whose `inr`
  branch is a jump to the trap exit with `()` becomes the (trapping) operator
  itself;
* a `cfg` with one block becomes `block { entry } loop { block-body }`: a
  branch to the block assigns its parameter's locals (a parallel copy,
  through temporaries when a sequential copy would clobber a source) and
  branches to the Wasm `block` (from the entry) or `loop` (from the block). A
  block whose label the entry never mentions is dead and dropped;
* exit `0` is `return`, exit `1` (only with the argument `()`) is `unreachable`.

These restrictions make the decompiler exact: the decompiled function and the
SSA function have the same terminating outcomes (`Thms`).

Each SSA variable gets its own Wasm local (no coalescing). Local types are
inferred from the operators (`Op.resultType`) and parameter types (a final
check confirms that the allocated locals are exactly the declared ones); the
shape of a block's parameter is found by `findShape`, a heuristic whose
result is checked at every branch, so it needs no proof. Anything else
(several blocks in one `cfg`, other primitives in conditions, ill-typed
operators) makes the decompiler fail (`none`).
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm (IntType)
open Silmaril.Isotope.LambdaSSA (Tm Region)

/-- Where a value lives. -/
inductive VLoc where
  | loc (x : Nat) (t : IntType)
  | const (w : WVal)
  | unit
  | pair (a b : VLoc)
  deriving DecidableEq, Repr

/-- The shape of a value: typed atoms, `()` and pairs. -/
inductive Shape where
  | atom (t : IntType)
  | unit
  | pair (a b : Shape)
  deriving DecidableEq, Repr

namespace VLoc

def shape : VLoc → Shape
  | .loc _ t => .atom t
  | .const w => .atom w.type
  | .unit => .unit
  | .pair a b => .pair a.shape b.shape

/-- The expression reading an atom. -/
def atomExpr : VLoc → Option Expr
  | .loc x _ => some (.localGet x)
  | .const w => some (.op (.const w) [])
  | _ => none

/-- The atoms of a location, left to right. -/
def atoms : VLoc → List VLoc
  | .pair a b => a.atoms ++ b.atoms
  | .unit => []
  | v => [v]

/-- Decode a tuple of atoms ending in `()`. -/
def args? : VLoc → Option (List VLoc)
  | .unit => some []
  | .pair a r => match a with
    | .loc .. | .const _ => (args? r).map (a :: ·)
    | _ => none
  | _ => none

end VLoc

/-- The atom type of a shape. -/
def Shape.atomType? : Shape → Option IntType
  | .atom t => some t
  | _ => none

/-- The result type of an operator on arguments of the given shapes. -/
def Op.resultType : Op → List Shape → Option IntType
  | .const w, _ => some w.type
  | .un (.int t _), _ => some t
  | .un (.test _), _ => some .i32
  | .un .wrap, _ => some .i32
  | .un (.extend _), _ => some .i64
  | .bin (.int t _), _ => some t
  | .bin (.rel _ _), _ => some .i32
  | .select, a :: _ => a.atomType?
  | .select, [] => none

/-- What an SSA label is in the output. -/
inductive DLabel where
  | trap
  | ret
  /-- A Wasm `block`/`loop` at a Wasm label level, with the parameter's locals. -/
  | block (wlvl : Nat) (layout : VLoc)
  deriving DecidableEq, Repr

/-- The decompiler's context, by de Bruijn index. -/
structure DCtx where
  vars : List VLoc
  labels : List DLabel
  wdepth : Nat
  fty : Option IntType
  deriving Repr

/-- The allocation state: the next local and the types allocated (reversed). -/
structure DState where
  next : Nat
  types : List IntType
  deriving Repr

/-- Allocate a local. -/
def DState.alloc (s : DState) (t : IntType) : Nat × DState :=
  (s.next, ⟨s.next + 1, t :: s.types⟩)

/-- Allocate fresh locals for a shape. -/
def allocShape : Shape → DState → VLoc × DState
  | .atom t, s => let (x, s) := s.alloc t; (.loc x t, s)
  | .unit, s => (.unit, s)
  | .pair a b, s =>
      let (la, s) := allocShape a s
      let (lb, s) := allocShape b s
      (.pair la lb, s)

/-- Locations of terms that need no code. -/
def staticLoc (vars : List VLoc) : Tm Prim → Option VLoc
  | .var i => vars[i]?
  | .unit => some .unit
  | .pair a b => do pure (.pair (← staticLoc vars a) (← staticLoc vars b))
  | .op (.op (.const w)) .unit => some (.const w)
  | _ => none

/-- Shapes of terms that need no code. -/
def staticShape (shapes : List Shape) : Tm Prim → Option Shape
  | .var i => shapes[i]?
  | .unit => some .unit
  | .pair a b => do pure (.pair (← staticShape shapes a) (← staticShape shapes b))
  | .op (.op (.const w)) .unit => some (.atom w.type)
  | _ => none

/-- Decode a shape tuple of atoms. -/
def Shape.args? : Shape → Option (List Shape)
  | .unit => some []
  | .pair (.atom t) r => (Shape.args? r).map (.atom t :: ·)
  | _ => none

/-- The shape of the argument of the first branch to label `target` (heuristic). -/
def findShape (shapes : List Shape) (target : Nat) : Region Prim → Option Shape
  | .br l a => if l = target then staticShape shapes a else none
  | .let₁ t r =>
      let sh : Option Shape := match staticShape shapes t with
        | some s => some s
        | none => match t with
          | .op (.op o) a => do
              let args ← (← staticShape shapes a).args?
              pure (.atom (← o.resultType args))
          | _ => none
      match sh with
      | some s => findShape (s :: shapes) target r
      | none => none
  | .let₂ t r =>
      match staticShape shapes t with
      | some (.pair a b) => findShape (b :: a :: shapes) target r
      | _ => none
  | .case t l r =>
      let sh : Option Shape := match t with
        | .op .truthy _ => some .unit
        | .op (.opT o) a => do
            let args ← (← staticShape shapes a).args?
            pure (.atom (← o.resultType args))
        | _ => none
      match sh with
      | some s => (findShape (s :: shapes) target l).orElse fun _ => findShape (s :: shapes) target r
      | none => none
  | .cfg e n bs =>
      (findShape shapes (target + n) e).orElse fun _ =>
        if h : 0 < n then
          match findShape shapes 0 e with
          | some s => findShape (s :: shapes) (target + n) (bs ⟨0, h⟩)
          | none => none
        else none

/-- Does a region mention label `ℓ`? -/
def Region.mentionsLabel : Nat → Region Prim → Bool
  | ℓ, .br l _ => l == ℓ
  | ℓ, .let₁ _ r => Region.mentionsLabel ℓ r
  | ℓ, .let₂ _ r => Region.mentionsLabel ℓ r
  | ℓ, .case _ l r => Region.mentionsLabel ℓ l || Region.mentionsLabel ℓ r
  | ℓ, .cfg e n bs =>
      Region.mentionsLabel (ℓ + n) e || (List.finRange n).any fun j => Region.mentionsLabel (ℓ + n) (bs j)

/-- Sequential assignments of atoms to locals. -/
def assignCode : List (Nat × VLoc) → Option (List Expr)
  | [] => some []
  | (x, a) :: rest => do pure (.localSet x (← a.atomExpr) :: (← assignCode rest))

/-- The locals a location uses. -/
def VLoc.locs : VLoc → List Nat
  | .loc x _ => [x]
  | .const _ => []
  | .unit => []
  | .pair a b => a.locs ++ b.locs

/-- A sequential copy is correct if no source reads an earlier destination. -/
def seqSafe : List Nat → List VLoc → Bool
  | x :: xs, _ :: srcs => srcs.all (fun c => !(c.locs.contains x)) && seqSafe xs srcs
  | _, _ => true

/-- The destination locals of a layout. -/
def VLoc.dests : VLoc → Option (List Nat)
  | v => v.atoms.mapM fun a => match a with | .loc x _ => some x | _ => none

/-- Allocate one temporary per atom. -/
def allocTmps : List VLoc → DState → List (Nat × IntType) × DState
  | [], s => ([], s)
  | a :: as, s =>
      let t := a.shape.atomType?.getD .i32
      let (x, s₁) := s.alloc t
      let (ts, s₂) := allocTmps as s₁
      ((x, t) :: ts, s₂)

/-- Copy the value at `src` into the layout `dst` (same shape). -/
def copyCode (dst src : VLoc) (s : DState) : Option (List Expr × DState) := do
  guard (dst.shape = src.shape)
  let xs ← dst.dests
  guard xs.Nodup
  let moves := xs.zip src.atoms
  if seqSafe xs src.atoms then
    pure (← assignCode moves, s)
  else
    -- through fresh temporaries
    let (tmps, s') := allocTmps src.atoms s
    let first ← assignCode ((tmps.map (·.1)).zip src.atoms)
    let second ← assignCode (xs.zip (tmps.map fun (x, t) => VLoc.loc x t))
    pure (first ++ second, s')

/-- Is a region a jump to the trap exit? -/
def isTrapExit (c : DCtx) : Region Prim → Bool
  | .br l .unit => c.labels[l]? == some .trap
  | _ => false

/-- A divisor for which division/remainder of type `t` cannot trap. -/
def divSafe (t : IntType) (op : Silmaril.Wasm.IntBinOp) (w : WVal) : Bool :=
  match op, w.asInt t with
  | .div .unsigned, some d | .rem .unsigned, some d | .rem .signed, some d => d != 0
  | .div .signed, some d => d != 0 && d != -1
  | _, _ => false

/-- The operator cannot trap on these arguments: it never traps, or it divides by
a constant for which division cannot trap. -/
def opSafe (vars : List VLoc) (o : Op) (a : Tm Prim) : Bool :=
  !o.mayTrap ||
    match o, (staticLoc vars a).bind VLoc.args? with
    | .bin (.int t op), some [_, .const d] => divSafe t op d
    | _, _ => false

/-- An operator applied to the located arguments: its expression and result type. -/
def opExpr (vars : List VLoc) (o : Op) (a : Tm Prim) : Option (Expr × IntType) := do
  let args ← (← staticLoc vars a).args?
  let ty ← o.resultType (args.map VLoc.shape)
  let es ← args.mapM VLoc.atomExpr
  pure (.op o es, ty)

/-- Decompile a region. -/
def dR : DCtx → Region Prim → DState → Option (List Expr × DState)
  | c, .br l a, s =>
      match c.labels[l]? with
      | some .trap =>
          match a with
          | .unit => some ([.unreachable], s)
          | _ => none
      | some .ret => do
          match ← staticLoc c.vars a with
          | .unit => pure ([.return_ []], s)
          | v => do
              guard c.fty.isSome
              pure ([.return_ [← v.atomExpr]], s)
      | some (.block w L) => do
          let (code, s') ← copyCode L (← staticLoc c.vars a) s
          pure (code ++ [.br (c.wdepth - 1 - w) []], s')
      | none => none
  | c, .let₁ t r, s =>
      match staticLoc c.vars t with
      | some v => dR { c with vars := v :: c.vars } r s
      | none =>
          match t with
          | .op (.op o) a => do
              guard (opSafe c.vars o a)
              let (e, ty) ← opExpr c.vars o a
              let (x, s₁) := s.alloc ty
              let (code, s₂) ← dR { c with vars := .loc x ty :: c.vars } r s₁
              pure (.localSet x e :: code, s₂)
          | _ => none
  | c, .let₂ t r, s =>
      match staticLoc c.vars t with
      | some (.pair a b) => dR { c with vars := b :: a :: c.vars } r s
      | _ => none
  | c, .case t l r, s =>
      match t with
      | .op .truthy a => do
          let e ← (← staticLoc c.vars a).atomExpr
          let c' := { c with vars := .unit :: c.vars, wdepth := c.wdepth + 1 }
          let (cl, s₁) ← dR c' l s
          let (cr, s₂) ← dR c' r s₁
          pure ([.if_ none e cl cr], s₂)
      | .op (.opT o) a => do
          guard (isTrapExit c r)
          let (e, ty) ← opExpr c.vars o a
          let (x, s₁) := s.alloc ty
          let (code, s₂) ← dR { c with vars := .loc x ty :: c.vars } l s₁
          pure (.localSet x e :: code, s₂)
      | _ => none
  | c, .cfg e n bs, s =>
      if h : n = 1 then
        if Region.mentionsLabel 0 e then do
          let sh ← findShape (c.vars.map VLoc.shape) 0 e
          let (L, s₁) := allocShape sh s
          let c' := { c with labels := .block c.wdepth L :: c.labels, wdepth := c.wdepth + 1 }
          let (ce, s₂) ← dR c' e s₁
          let (cb, s₃) ← dR { c' with vars := L :: c.vars } (bs ⟨0, by omega⟩) s₂
          pure ([.block none ce, .loop none cb], s₃)
        else do
          let c' := { c with labels := .trap :: c.labels, wdepth := c.wdepth + 1 }
          let (ce, s₁) ← dR c' e s
          pure ([.block none ce, .unreachable], s₁)
      else none

/-- Decompile an SSA function. -/
def decompileFunc (f : SFunc) : Option FragFunc := do
  let c : DCtx :=
    { vars := (f.params.mapIdx fun j t => VLoc.loc j t).reverse
      labels := [.ret, .trap]
      wdepth := 1
      fty := f.result }
  let (code, s) ← dR c f.body ⟨f.params.length, []⟩
  guard (s.next = f.params.length + s.types.length)
  pure { params := f.params, locals := s.types.reverse, result := f.result,
         body := code ++ [.unreachable] }

end Silmaril.Wasm.SSA
