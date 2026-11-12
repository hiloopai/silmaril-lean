module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Transfer.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: determination for `Round7.Task.envAgreeNE` (round 2, pass 3)

`Round7.Transfer.dderivesB_simEnv_of_E` moves a `utf8Env B` derivation of a reachable relation to
`simEnv B` when every quantifier of every rule instance is bound to an `ExpFree` value
(`Round7.Transfer.DDerivesBE`). This header names what is needed to show that every derivation of
SpecTec's `Step` from an `ExpFree` configuration is such a derivation.

* `AllEF ρ`: every term variable of `ρ` is bound to an `ExpFree` value.
* `BuiltinsEF B`: the primitives answer `ExpFree` values at `ExpFree` arguments.
* `GoodX e`, `GoodXs l`: `Round7.Script.GoodEv`, and an atom event is not `EXPORTS`. The
  evaluator, run on `GoodXs` syntax in an `AllEF` scope, answers `ExpFree` values
  (`Round7.Determ.evalEF`); matching an `ExpFree` value in an `AllEF` scope returns an `AllEF`
  scope (`Round7.Determ.matchEF`).
* `typMapNoExp S m`: no type of `m` named in `S` declares a record field `EXPORTS`. With
  `S := Round7.TypAgree.tyA`, a value typed at a type over `tyA` is `ExpFree`
  (`Round7.Determ.ef_of_hasTyp_A`).
* `InEF v`: if `v` is a non-empty tuple, its first component is `ExpFree`. This is the input of
  SpecTec's `Step`, `Step_read`, `Step_pure` and `Ref_ok`.

**The mode check.** Determination is a mode property of the rules, checked by the kernel on the
script (`Round7.Determ.detRelsOk_fixed`):

* `invVars e`: the variables whose values an `ExpFree` value of `e` determines to be `ExpFree`
  (variables, tuples, lists, cases, options, concatenations, subsumptions and single-domain
  iterations over a variable).
* `fvIn K e`: every free term variable of `e` (`IL.freeExp`) is in `K`.
* `premStep K pr`: what one premise adds to the known set `K`: an equation or membership whose
  known side is in `K` gives the `invVars` of the other side; a `let` gives the `invVars` of its
  pattern; a relation premise whose input is in `K` gives the `invVars` of its whole tuple.
* `ruleDetOk r`: starting from the quantifiers typed over `tyA` (`ExpFree` by typing) and the
  `invVars` of the conclusion's input, three rounds of `premStep` reach every quantifier and every
  free variable of the conclusion; every relation premise (also inside iterations) is a tuple
  whose input is in that set, and the domains of iterated premises are in it; the conclusion
  alternatives and premises are `GoodXs`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev)
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree)

/-- **Every term variable of `ρ` is bound to an `ExpFree` value.** -/
def AllEF (ρ : VarEnv) : Prop := ∀ p ∈ ρ.vals, ExpFree p.2

/-- **Every variable of `K` bound in `ρ` is bound to an `ExpFree` value.** -/
def EFOn (ρ : VarEnv) (K : List IL.Id) : Prop :=
  ∀ x ∈ K, ∀ w, ρ.findVal? x = some w → ExpFree w

/-- **The primitives preserve `ExpFree`.** -/
def BuiltinsEF (B : Builtins) : Prop :=
  ∀ x ws v, (∀ w, ArgV.val w ∈ ws → ExpFree w) → B.call x ws = some v → ExpFree v

/-- **The input of a relation instance is `ExpFree`**: the first component of a non-empty
tuple. -/
def InEF (v : Value) : Prop := ∀ a rest, v = .tuple (a :: rest) → ExpFree a

/-- No record type among the instances declares a field `EXPORTS`. -/
def instsNoExp (insts : List Inst) : Bool :=
  insts.all fun i => match i with
    | .instD _ _ (.structT fs) => fs.all fun f => match f with
      | .mk a _ _ _ => a != "EXPORTS"
    | _ => true

/-- **No type of `m` named in `S` declares a record field `EXPORTS`.** The kernel checks it for
the fixed wasm-3.0 script and `S := Round7.TypAgree.tyA` (`Round7.Determ.typMapNoExp_A`). -/
def typMapNoExp (S : List String) (m : Map TypDef) : Bool :=
  m.all fun p => !S.contains p.1 || instsNoExp p.2.2

/-! ## The mode check -/

/-- An iteration whose rounds are read off a single domain (`ListN` without a counter). -/
def invIter : Iter → Bool
  | .listN _ (some _) => false
  | _ => true

mutual
/-- **The variables an `ExpFree` value of `e` shows to be `ExpFree`.** -/
def invVars : Exp → List IL.Id
  | .varE x => [x]
  | .tupE es => invVarsL es
  | .listE es => invVarsL es
  | .caseE _ e => invVars e
  | .optE (some e) => invVars e
  | .catE e₁ e₂ => invVars e₁ ++ invVars e₂
  | .subE e _ _ => invVars e
  | .iterE e (.mk it [.mk x (.varE xs)]) =>
      if x != "_" && invIter it && (invVars e).contains x then [xs] else []
  | _ => []

/-- `invVars` on a list. -/
def invVarsL : List Exp → List IL.Id
  | [] => []
  | e :: es => invVars e ++ invVarsL es
end

/-- **Every free term variable of `e` is in `K`.** -/
def fvIn (K : List IL.Id) (e : Exp) : Bool := decide (∀ x ∈ (IL.freeExp e).varid, x ∈ K)

/-- **What one premise adds to the known variables `K`.** -/
def premStep (K : List IL.Id) : Prem → List IL.Id
  | .ifPr (.cmpE .eqOp _ a b) =>
      (if fvIn K a then invVars b else []) ++ (if fvIn K b then invVars a else [])
  | .ifPr (.memE a b) => if fvIn K b then invVars a else []
  | .letPr a b => if fvIn K b then invVars a else []
  | .rulePr _ _ _ (.tupE (a :: rest)) => if fvIn K a then invVarsL (a :: rest) else []
  | _ => []

/-- `n` rounds of `premStep` over all premises. -/
def modeK (prems : List Prem) : Nat → List IL.Id → List IL.Id
  | 0, K => K
  | n + 1, K => modeK prems n (K ++ prems.flatMap (premStep K))

/-- A premise is harmless for `ExpFree`: its relation premises (also inside iterations) are
tuples whose input is in `K`, and the domains of its iterations are in `K`. -/
def premDetOk (K : List IL.Id) : Prem → Bool
  | .rulePr _ _ _ (.tupE (a :: _)) => fvIn K a
  | .rulePr _ _ _ _ => false
  | .iterPr pr (.mk _ ds) => ds.all (fun d => fvIn K (domSrc d)) && premDetOk K pr
  | _ => true

/-- `Round7.TypAgree.goodEvsB`, and no atom event is `EXPORTS`. -/
def goodXsB (l : List Script.Ev) : Bool :=
  TypAgree.goodEvsB l && l.all fun e => match e with
    | .atom a => a != "EXPORTS"
    | _ => true

/-- The quantifiers of `qs` typed over `tyA`. -/
def quantsA (qs : List Param) : List IL.Id :=
  qs.filterMap fun q => match q with
    | .expP x t => if TypAgree.tyOk TypAgree.tyA TypAgree.tyA t then some x else none
    | _ => none

/-- All expression quantifiers of `qs`. -/
def quantNames (qs : List Param) : List IL.Id :=
  qs.filterMap fun q => match q with
    | .expP x _ => some x
    | _ => none

/-- The `invVars` of a conclusion's input, the first component of its tuple. -/
def conclIn : Exp → List IL.Id
  | .tupE (a :: _) => invVars a
  | _ => []

/-- The known variables of a rule instance with conclusion alternative `e'`. -/
def ruleK (qs : List Param) (e' : Exp) (prems : List Prem) : List IL.Id :=
  modeK prems 3 (quantsA qs ++ conclIn e')

/-- **One rule is determined.** -/
def ruleDetOk : Rule → Bool
  | .ruleD _ qs _ e prems =>
      goodXsB (Script.evPrems prems) &&
      (Round6.Reading.conclAlts e).all fun e' =>
        let K := ruleK qs e' prems
        goodXsB (Script.evExp e') && (quantNames qs).all K.contains && fvIn K e' &&
          prems.all (premDetOk K)

/-- **Every rule of every relation `Step` reaches is determined.** -/
def detRelsOk (m : Map RelDef) : Bool :=
  m.all fun p => !Script.stepReach.contains (0, p.1) || p.2.2.2.2.all ruleDetOk

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
