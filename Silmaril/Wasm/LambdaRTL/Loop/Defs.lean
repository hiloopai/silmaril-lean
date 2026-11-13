module

public import Silmaril.Wasm.LambdaRTL.Defs
public import Silmaril.SSA.LambdaRTL.Loop.Defs

/-!
# The whole structured Wasm fragment in λRTL with loops

The translation of `Silmaril.Wasm.LambdaRTL` (loop-free fragment → acyclic λRTL) extended to the
whole fragment `Silmaril.Wasm.SSA.Expr`, `loop` included, into λRTL with loops
(`Silmaril.SSA.LambdaRTL.Loop.Region`, whose `loop r ℓ x t` is `r where { ℓ(x) => t }` with `ℓ` in
scope in the handler `t`). The acyclic API of `Silmaril.Wasm.LambdaRTL` is unchanged; the new
definitions carry the suffix `L`.

## The model

Registers `WReg`, values `RVal`, instructions `WOp` and the instruction semantics `app` are those
of the loop-free translation. Labels `LLab` add `cont d`, the label that re-enters the loop of
depth `d`. The monad `LM := ExceptT WErr Part` has errors (`.trap`, `.stuck`) and divergence
(`Part.none`); its iteration (`Iterate LM`) runs `Part`'s iteration (`Silmaril.Elgot.Part.run`: the
result of the finite successful run, if any) on the step with returns *and errors* routed to the
left (`routeE`), so an error leaves the loop. The model `modelL` lifts the model of the
loop-free translation (`liftE`), so primitive steps always terminate.

## The translation

As `trE`/`trArgs`/`trSeq`, with one more construct: `loop ty body` at label depth `d` becomes
`loopJoin d BODY k = (loop (br (cont d) ()) (cont d) junk BODY) where { blk d(junk) => k }`: the
loop is entered at once, a Wasm branch to the loop's label is a λRTL jump to `cont d` (re-enter
the body with the current store; the carried value is dropped, as the fragment's `loop_back`
does), and the body's fallthrough leaves through `blk d` (with the same typed-result check as a
`block`). `block`/`if` are joins as before. Every fragment function is translated
(`trBodyL`); there is no partial `trFunc` any more.

The simulation theorems are in `Silmaril.Wasm.LambdaRTL.Loop.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL (Val Op Model upd)
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Res)
open Silmaril.Wasm (IntType)

/-- λRTL labels with loops: the function exit, the join of the construct at depth `d`, and the
re-entry of the loop at depth `d`. -/
inductive LLab where
  | ret
  | blk (d : Nat)
  | cont (d : Nat)
  deriving DecidableEq, Repr

/-- The monad: errors and divergence. -/
abbrev LM := ExceptT WErr Part

/-- λRTL regions with loops of the translation. -/
abbrev LRegion := Silmaril.SSA.LambdaRTL.Loop.Region WReg LLab WOp

/-- A terminating result. -/
def liftE {α : Type} (x : Except WErr α) : LM α := ExceptT.mk (Part.some x)

/-- Route one step of an iteration: returns and errors leave the loop, `inr` continues. -/
def routeE {A B : Type} : Except WErr (B ⊕ A) → Except WErr B ⊕ A
  | .ok (.inl b) => .inl (.ok b)
  | .ok (.inr a) => .inr a
  | .error e => .inl (.error e)

/-- The iteration of `LM`: `Part`'s iteration of the routed step. -/
noncomputable instance instIterateLM : Silmaril.Elgot.Iterate LM where
  iter f a := ExceptT.mk (Silmaril.Elgot.iter (fun a => routeE <$> (f a).run) a)

/-- The model of the fragment with errors and divergence. -/
def modelL : Model WOp LM RVal where
  unit := .unit
  pair := .pair
  inl := .inl
  inr := .inr
  unpair v := liftE (model.unpair v)
  split v := liftE (model.split v)
  app f v := liftE (app f v)
  abort v := liftE (model.abort v)

/-! ## The translation -/

/-- A Wasm label: a `block`/`if` (join depth, result slot, type) or a `loop` (depth, slot). -/
inductive TgtL where
  | blk (d slot : Nat) (ty : Option IntType)
  | lp (d slot : Nat)
  deriving DecidableEq, Repr

/-- The label depth of a target. -/
def TgtL.d : TgtL → Nat
  | .blk d _ _ => d
  | .lp d _ => d

/-- The operand-stack slot of a target. -/
def TgtL.slot : TgtL → Nat
  | .blk _ s _ => s
  | .lp _ s => s

/-- A region without result. -/
def stuckRL : LRegion := .let1 .junk (.app .stuck .unit) (.br .ret .unit)

/-- A register move. -/
def mvL (dst src : WReg) (k : LRegion) : LRegion := .let1 dst (.val (.var src)) k

/-- Leave the function with result type `res`; `hv` says whether slot `sd` holds a value. -/
def retRL (res : Option IntType) (sd : Nat) (hv : Bool) : LRegion :=
  if res.isSome && hv then .br .ret (.var (.tmp sd)) else .br .ret .unit

/-- Branch to Wasm label `l`, carrying the value of slot `sd` when `hv`; a loop label
re-enters the loop and drops the value. -/
def jumpToL (ks : List TgtL) (res : Option IntType) (l sd : Nat) (hv : Bool) : LRegion :=
  match ks[l]? with
  | some (.blk d slot ty) =>
      if ty.isSome && !hv then stuckRL
      else if hv then mvL (.tmp slot) (.tmp sd) (.br (.blk d) .unit)
      else .br (.blk d) .unit
  | some (.lp d _) => .br (.cont d) .unit
  | none => if l = ks.length then retRL res sd hv else stuckRL

/-- The end of a body of type `ty`: a typed construct needs a value. -/
def fallRL (d : Nat) (ty : Option IntType) (hv : Bool) : LRegion :=
  if ty.isSome && !hv then stuckRL else .br (.blk d) .unit

/-- Continue with `k` when a value is present (`hv`), else stuck. -/
def needValL (hv : Bool) (k : LRegion) : LRegion := if hv then k else stuckRL

/-- Write slot `sd` to local `i`; nothing when `i` is out of range, as `List.set`. -/
def setLocalL (nloc i sd : Nat) (k : LRegion) : LRegion :=
  if i < nloc then mvL (.loc i) (.tmp sd) k else k

/-- The join of an `if` at label depth `d`: test slot `sd`, run a branch, then `k`. -/
def ifJoinL (d sd : Nat) (rt re k : LRegion) : LRegion :=
  .join (.case (.app .truthy (.var (.tmp sd))) .junk rt .junk re) (.blk d) .junk k

/-- The test of a `br_if` with `n` operands in slots `sd, …`: the last one is the condition. -/
def brIfTestL (ks : List TgtL) (res : Option IntType) (l sd : Nat) (k : LRegion) :
    Nat → LRegion
  | 0 => stuckRL
  | m + 1 =>
      .case (.app .truthy (.var (.tmp (sd + m))))
        .junk (jumpToL ks res l sd (decide (1 ≤ m))) .junk k

/-- The loop at label depth `d`: enter the body at once; `cont d` re-enters it; the body's
fallthrough leaves through `blk d` to `k`. -/
def loopJoin (d : Nat) (body k : LRegion) : LRegion :=
  .join (.loop (.br (.cont d) .unit) (.cont d) .junk body) (.blk d) .junk k

mutual

/-- Translate an expression at operand-stack depth `sd` under the labels `ks`, continuing with
`k`. -/
def trEL (nloc : Nat) (res : Option IntType) : List TgtL → Nat → Expr → LRegion → LRegion
  | ks, sd, .op o args, k =>
      trArgsL nloc res ks sd args (.let1 (.tmp sd) (.app (.op o) (pack sd args.length)) k)
  | _, sd, .localGet i, k => if i < nloc then mvL (.tmp sd) (.loc i) k else stuckRL
  | ks, sd, .localSet i e, k =>
      trEL nloc res ks sd e (needValL (hasVal e) (setLocalL nloc i sd k))
  | ks, sd, .localTee i e, k =>
      trEL nloc res ks sd e (needValL (hasVal e) (setLocalL nloc i sd k))
  | ks, sd, .drop e, k => trEL nloc res ks sd e k
  | _, _, .nop, k => k
  | _, _, .unreachable, k => .let1 .junk (.abort .unit) k
  | ks, sd, .block ty body, k =>
      .join (trSeqL nloc res (.blk ks.length sd ty :: ks) sd body
          (fallRL ks.length ty (seqVal false body)))
        (.blk ks.length) .junk k
  | ks, sd, .loop ty body, k =>
      loopJoin ks.length
        (trSeqL nloc res (.lp ks.length sd :: ks) sd body (fallRL ks.length ty (seqVal false body)))
        k
  | ks, sd, .if_ ty c t el, k =>
      trEL nloc res ks sd c (needValL (hasVal c) (ifJoinL ks.length sd
        (trSeqL nloc res (.blk ks.length sd ty :: ks) sd t (fallRL ks.length ty (seqVal false t)))
        (trSeqL nloc res (.blk ks.length sd ty :: ks) sd el (fallRL ks.length ty (seqVal false el)))
        k))
  | ks, sd, .br l args, _ => trArgsL nloc res ks sd args (jumpToL ks res l sd (!args.isEmpty))
  | ks, sd, .brIf l args, k =>
      trArgsL nloc res ks sd args (brIfTestL ks res l sd k args.length)
  | ks, sd, .return_ args, _ => trArgsL nloc res ks sd args (retRL res sd (!args.isEmpty))

/-- Translate operands into consecutive slots from `sd`; each must leave a value. -/
def trArgsL (nloc : Nat) (res : Option IntType) :
    List TgtL → Nat → List Expr → LRegion → LRegion
  | _, _, [], k => k
  | ks, sd, e :: es, k =>
      trEL nloc res ks sd e (needValL (hasVal e) (trArgsL nloc res ks (sd + 1) es k))

/-- Translate a body; every expression runs at depth `sd`, the last value stays in `tmp sd`. -/
def trSeqL (nloc : Nat) (res : Option IntType) :
    List TgtL → Nat → List Expr → LRegion → LRegion
  | _, _, [], k => k
  | ks, sd, e :: es, k => trEL nloc res ks sd e (trSeqL nloc res ks sd es k)

end

/-- The λRTL body of a fragment function (every function is translated). -/
def trBodyL (f : FragFunc) : LRegion :=
  trSeqL (nlocOf f) f.result [] 0 f.body (retRL f.result 0 (seqVal false f.body))

/-- The λRTL observation of a call outcome. -/
def obsOfL : FOut → Except WErr (LLab × RVal)
  | .ret r => .ok (.ret, encR r)
  | .trap => .error .trap

end Silmaril.Wasm.LambdaRTL
