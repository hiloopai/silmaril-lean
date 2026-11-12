module

public import Silmaril.Wasm.SSA.Dialect.Defs

/-!
# From the fragment into the Wasm lambda-SSA dialect

A continuation-passing translation. A compile-time context `Ctx` records the
number of bound SSA variables, the **level** (position from the outside) of
the SSA variable holding each Wasm local, and the SSA label level of each Wasm
label. The continuation `k : Ctx → Option Nat → Region` receives the context
after an expression and the level of its result, so locals disappear:

* `local.get i` emits nothing and passes on the level of local `i`;
  `local.set i e` rebinds local `i` to the level of `e`'s value;
* a non-trapping operator is a `let₁` of `Prim.op`; a trapping one cases on
  `Prim.opT`, sending `inr` to the trap exit;
* `block`, `if` and `loop` become `cfg`s with one join block per construct
  (and a loop-header block for `loop`). Control transfers pass all locals and
  the carried value as a tuple `(l₀, (l₁, …, r))` (`Ctx.pack`), which the
  target block unpacks with `let₂` (`unpack`): maximal block parameters, so no
  dominance or φ placement is needed;
* `br` to a block jumps to its join, `br` to a loop to its header, `br` to the
  function label or `return` to external label `0`, traps to label `1`.

Code the fragment semantics gets stuck on (ill-typed or out-of-range) is
translated to `stuck`, which has no evaluation.

Source: the maximal construction follows `Silmaril.Calculi.ToLambdaSSA` (and
silmaril's `Machine/RTL/Construct`); the continuation-passing, level-indexed
presentation is new here.
-/

@[expose] public section

namespace Silmaril.Wasm.SSA

open Silmaril.Wasm (IntType)
open Silmaril.Isotope.LambdaSSA (Tm Region)

/-- What a Wasm label means in SSA: a join (or loop-header) block at an SSA
label level, or the function's return. -/
inductive LabelK where
  | join (lvl : Nat)
  | ret
  deriving DecidableEq, Repr

/-- The compile-time context. -/
structure Ctx where
  /-- Number of SSA variables in scope. -/
  depth : Nat
  /-- The level of the variable holding each Wasm local. -/
  locals : List Nat
  /-- Number of SSA labels in scope. -/
  ldepth : Nat
  /-- The Wasm label stack, innermost first. -/
  labels : List LabelK
  /-- Levels of the return and trap exits. -/
  ret : Nat
  trap : Nat
  /-- The function's result type. -/
  fty : Option IntType
  deriving Repr

namespace Ctx

/-- The variable at a level. -/
def var (c : Ctx) (lvl : Nat) : Tm Prim := .var (c.depth - 1 - lvl)

/-- The label index of a label level. -/
def lbl (c : Ctx) (m : Nat) : Nat := c.ldepth - 1 - m

/-- Bind one more variable. -/
def bind (c : Ctx) : Ctx := { c with depth := c.depth + 1 }

/-- Enter a `cfg` of one block whose label is not a Wasm label. -/
def enter (c : Ctx) : Ctx := { c with ldepth := c.ldepth + 1 }

/-- Enter a `cfg` of one block whose label is the new innermost Wasm label. -/
def pushLabel (c : Ctx) : Ctx :=
  { c with labels := .join c.ldepth :: c.labels, ldepth := c.ldepth + 1 }

/-- A carried value: `()` or the atom at a level. -/
def resTm (c : Ctx) : Option Nat → Tm Prim
  | none => .unit
  | some l => c.var l

/-- The block argument `(l₀, (l₁, …, r))`. -/
def pack (c : Ctx) (r : Option Nat) : Tm Prim :=
  c.locals.foldr (fun l t => .pair (c.var l) t) (c.resTm r)

/-- An operator's arguments. -/
def argTm (c : Ctx) (ls : List Nat) : Tm Prim :=
  ls.foldr (fun l t => .pair (c.var l) t) .unit

end Ctx

/-- A region with no evaluation. -/
def stuck : Region Prim := .br 0 (.abort .unit)

/-- Leave towards a Wasm label. -/
def jump (c : Ctx) : LabelK → Option Nat → Region Prim
  | .join m, r => .br (c.lbl m) (c.pack r)
  | .ret, r => .br (c.lbl c.ret) (c.resTm (if c.fty.isSome then r else none))

/-- Unpack `n` components of the tuple at level `t`; the continuation receives
their levels and the level of the remaining tail. -/
def unpack : Nat → Ctx → Nat → (Ctx → List Nat → Nat → Region Prim) → Region Prim
  | 0, c, t, k => k c [] t
  | n + 1, c, t, k =>
      .let₂ (c.var t) (unpack n { c with depth := c.depth + 2 } (c.depth + 1)
        fun c' ls t' => k c' (c.depth :: ls) t')

/-- A join block: its parameter (bound at level `c.depth`) is unpacked into the
locals and, for a typed construct, the result. A typed construct's result is
passed through `select r r 1`, which checks that it is an atom (the fragment
requires a typed block to produce a value). -/
def joinBlock (c : Ctx) (ty : Option IntType) (k : Ctx → Option Nat → Region Prim) :
    Region Prim :=
  unpack c.locals.length c.bind c.depth fun c' ls t =>
    match ty with
    | none => k { c' with locals := ls } none
    | some _ =>
        .let₁ (.op (.op .select) (.pair (c'.var t) (.pair (c'.var t)
            (.pair (.op (.op (.const (.i32 1))) .unit) .unit))))
          (k { c'.bind with locals := ls } (some c'.depth))

mutual

/-- Translate an expression in context `c`, continuing with `k`. -/
def cE : Expr → Ctx → (Ctx → Option Nat → Region Prim) → Region Prim
  | .op o args, c, k => cArgs args c fun c ls =>
      if o.mayTrap then
        .case (.op (.opT o) (c.argTm ls)) (k c.bind (some c.depth)) (.br (c.lbl c.trap) .unit)
      else .let₁ (.op (.op o) (c.argTm ls)) (k c.bind (some c.depth))
  | .localGet i, c, k =>
      match c.locals[i]? with
      | some l => k c (some l)
      | none => stuck
  | .localSet i e, c, k => cE e c fun c r =>
      match r with
      | some l => k { c with locals := c.locals.set i l } none
      | none => stuck
  | .localTee i e, c, k => cE e c fun c r =>
      match r with
      | some l => k { c with locals := c.locals.set i l } (some l)
      | none => stuck
  | .drop e, c, k => cE e c fun c _ => k c none
  | .nop, c, k => k c none
  | .unreachable, c, _ => .br (c.lbl c.trap) .unit
  | .block ty body, c, k =>
      .cfg (cSeq body c.pushLabel none fun c' r => .br (c'.lbl c.ldepth) (c'.pack r)) 1
        fun _ => joinBlock c.enter ty k
  | .loop ty body, c, k =>
      .cfg
        (.cfg (.br 0 (c.pack none)) 1 fun _ =>
          unpack c.locals.length
            { c with depth := c.depth + 1, ldepth := c.ldepth + 2,
                     labels := .join (c.ldepth + 1) :: c.labels } c.depth
            fun c' ls _ => cSeq body { c' with locals := ls } none
              fun c'' r => .br (c''.lbl c.ldepth) (c''.pack r))
        1 fun _ => joinBlock c.enter ty k
  | .if_ ty cnd t e, c, k => cE cnd c fun c r =>
      match r with
      | some l =>
          .cfg (.case (.op .truthy (c.var l))
              (cSeq t c.pushLabel.bind none fun c' r => .br (c'.lbl c.ldepth) (c'.pack r))
              (cSeq e c.pushLabel.bind none fun c' r => .br (c'.lbl c.ldepth) (c'.pack r)))
            1 fun _ => joinBlock c.enter ty k
      | none => stuck
  | .br l args, c, _ => cArgs args c fun c' vs =>
      match c.labels[l]? with
      | some lk => jump c' lk vs.head?
      | none => stuck
  | .brIf l args, c, k => cArgs args c fun c' vs =>
      match vs.getLast? with
      | some cl =>
          .case (.op .truthy (c'.var cl))
            (match c.labels[l]? with
              | some lk => jump c'.bind lk vs.dropLast.head?
              | none => stuck)
            (k c'.bind vs.dropLast.head?)
      | none => stuck
  | .return_ args, c, _ => cArgs args c fun c' vs => jump c' .ret vs.head?

/-- Translate operands left to right; the continuation receives their levels. -/
def cArgs : List Expr → Ctx → (Ctx → List Nat → Region Prim) → Region Prim
  | [], c, k => k c []
  | e :: es, c, k => cE e c fun c r =>
      match r with
      | some l => cArgs es c fun c ls => k c (l :: ls)
      | none => stuck

/-- Translate a body, carrying the level of the last result. -/
def cSeq : List Expr → Ctx → Option Nat → (Ctx → Option Nat → Region Prim) → Region Prim
  | [], c, r, k => k c r
  | e :: es, c, _, k => cE e c fun c r => cSeq es c r k

end

/-- Bind zero-initialised declared locals, then continue. -/
def initZeros : List IntType → Ctx → (Ctx → Region Prim) → Region Prim
  | [], c, k => k c
  | t :: ts, c, k =>
      .let₁ (.op (.op (.const (WVal.zero t))) .unit)
        (initZeros ts { c.bind with locals := c.locals ++ [c.depth] } k)

/-- The initial context of a function with `p` parameters. -/
def Ctx.initial (p : Nat) (fty : Option IntType) : Ctx where
  depth := p
  locals := List.range p
  ldepth := 2
  labels := [.ret]
  ret := 1
  trap := 0
  fty := fty

/-- Translate a function. -/
def compileFunc (f : FragFunc) : SFunc where
  params := f.params
  result := f.result
  body := initZeros f.locals (Ctx.initial f.params.length f.result) fun c =>
    cSeq f.body c none fun c r => jump c .ret r

end Silmaril.Wasm.SSA
