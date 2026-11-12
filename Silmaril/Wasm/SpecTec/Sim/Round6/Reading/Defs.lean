module

public import Silmaril.Wasm.SpecTec.Sim.Round5Fwd.Defs
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read.Defs

/-!
# SpecTec ↔ Core 3.0, round 6, track reading: a reading of `e?` in conclusions

`DDerives` (`Sim/Defs.lean`) evaluates a rule's conclusion with the evaluator (`EvalExp`). The IL
writes a bare optional atom such as `NULL?` in `REF NULL? heaptype` as an option iteration with no
domain variables, `iterE (NULL) (opt [])`, and the evaluator rejects every iteration with an empty
domain (`evalIterE`, after `eval.ml:377-379`). So the eight relations whose conclusions contain one
(`Reftype_ok`, `Fieldtype_ok`, `Subtype_ok2`, `Reftype_sub`, `Subtype_ok`, `Globaltype_ok`,
`Instr_ok`, `Global_ok`) lose those rules under `DDerives`, and `Ref_ok/sub` never fires
(`Round5.RefOk.not_reftypeOk`).

SpecTec's inductive backends read such an `e?` as a fresh variable ranging over `none` and
`some e`. This file adds that reading **without changing `DDerives`**:

* `optAlts e` replaces every empty-domain option iteration `iterE e₀ (opt [])` of `e` by either
  `optE none` or `optE (some e₀')` (with `e₀'` an alternative of `e₀`), in every combination.
  It descends through every expression constructor except into types, paths and the domains and
  bounds of iterations, none of which contains such an iteration in the pinned script's
  conclusions.
* `conclAlts e` is `e` itself followed, when `e` contains one (`hasOptNil`), by `optAlts e`.
  Keeping `e` makes the new reading an extension of `DDerives` by construction
  (`Round6.Reading.dderivesB_of_dderives`); when `e` contains no such iteration,
  `conclAlts e = [e]`.
* `DDerivesB` is `DDerives` with the conclusion read through `conclAlts`: rule `i` fires on `v`
  when **some** alternative of its conclusion evaluates to `v` under a well-typed assignment that
  satisfies the premises. Premises, functions (`EvalExp`) and the environment are unchanged, so
  the evaluator, `HasTyp` and every typing fact stay those of `simEnv B`.
* `otherwiseB`, `FiresB`, `SStepB`, `SReadB`, `SPureB`, `FwdPB` are `otherwise`, `Fires`,
  `SStep`, `SRead`, `SPure`, `FwdP` over `DDerivesB`.
* `RefOkAtB`, `RefOkBB` restate `Round5.Fwd.RefOkAt`/`RefOkB` over `DDerivesB`; `CastsFwdB`,
  `CastsBwdB` restate the cast-rule obligations.

See `docs/projects/spectec/README.md`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## 1. Empty-domain option iterations, and their alternatives -/

mutual
/-- `e` contains an option iteration with no domain variables, outside types, paths and the
domains and bounds of iterations. -/
def hasOptNil : Exp → Bool
  | .unE _ _ e => hasOptNil e
  | .binE _ _ e₁ e₂ => hasOptNil e₁ || hasOptNil e₂
  | .cmpE _ _ e₁ e₂ => hasOptNil e₁ || hasOptNil e₂
  | .tupE es => hasOptNilL es
  | .projE e _ => hasOptNil e
  | .caseE _ e => hasOptNil e
  | .uncaseE e _ => hasOptNil e
  | .optE eo => hasOptNilO eo
  | .theE e => hasOptNil e
  | .strE fs => hasOptNilF fs
  | .dotE e _ => hasOptNil e
  | .compE e₁ e₂ => hasOptNil e₁ || hasOptNil e₂
  | .listE es => hasOptNilL es
  | .liftE e => hasOptNil e
  | .memE e₁ e₂ => hasOptNil e₁ || hasOptNil e₂
  | .lenE e => hasOptNil e
  | .catE e₁ e₂ => hasOptNil e₁ || hasOptNil e₂
  | .idxE e₁ e₂ => hasOptNil e₁ || hasOptNil e₂
  | .sliceE e₁ e₂ e₃ => hasOptNil e₁ || hasOptNil e₂ || hasOptNil e₃
  | .updE e₁ _ e₂ => hasOptNil e₁ || hasOptNil e₂
  | .extE e₁ _ e₂ => hasOptNil e₁ || hasOptNil e₂
  | .callE _ args => hasOptNilA args
  | .iterE _ (.mk .opt []) => true
  | .iterE e _ => hasOptNil e
  | .cvtE e _ _ => hasOptNil e
  | .subE e _ _ => hasOptNil e
  | _ => false

/-- `hasOptNil` on a list. -/
def hasOptNilL : List Exp → Bool
  | [] => false
  | e :: es => hasOptNil e || hasOptNilL es

/-- `hasOptNil` on an option. -/
def hasOptNilO : Option Exp → Bool
  | none => false
  | some e => hasOptNil e

/-- `hasOptNil` on record fields. -/
def hasOptNilF : List ExpField → Bool
  | [] => false
  | .mk _ e :: fs => hasOptNil e || hasOptNilF fs

/-- `hasOptNil` on arguments (expression arguments only). -/
def hasOptNilA : List Arg → Bool
  | [] => false
  | .expA e :: rest => hasOptNil e || hasOptNilA rest
  | _ :: rest => hasOptNilA rest
end

/-- Every combination of one element of `xs` with one of `ys`. -/
def prod2 {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) : List γ :=
  xs.flatMap fun x => ys.map (f x)

mutual
/-- **The alternatives of an expression**: every empty-domain option iteration `iterE e₀ (opt [])`
is replaced by `optE none` or by `optE (some e₀')` for an alternative `e₀'` of `e₀`, in every
combination. An expression without one has itself as its only alternative (it is copied). -/
def optAlts : Exp → List Exp
  | .unE op t e => (optAlts e).map (.unE op t)
  | .binE op t e₁ e₂ => prod2 (.binE op t) (optAlts e₁) (optAlts e₂)
  | .cmpE op t e₁ e₂ => prod2 (.cmpE op t) (optAlts e₁) (optAlts e₂)
  | .tupE es => (optAltsL es).map .tupE
  | .projE e i => (optAlts e).map (.projE · i)
  | .caseE op e => (optAlts e).map (.caseE op)
  | .uncaseE e op => (optAlts e).map (.uncaseE · op)
  | .optE eo => (optAltsO eo).map .optE
  | .theE e => (optAlts e).map .theE
  | .strE fs => (optAltsF fs).map .strE
  | .dotE e a => (optAlts e).map (.dotE · a)
  | .compE e₁ e₂ => prod2 .compE (optAlts e₁) (optAlts e₂)
  | .listE es => (optAltsL es).map .listE
  | .liftE e => (optAlts e).map .liftE
  | .memE e₁ e₂ => prod2 .memE (optAlts e₁) (optAlts e₂)
  | .lenE e => (optAlts e).map .lenE
  | .catE e₁ e₂ => prod2 .catE (optAlts e₁) (optAlts e₂)
  | .idxE e₁ e₂ => prod2 .idxE (optAlts e₁) (optAlts e₂)
  | .sliceE e₁ e₂ e₃ => prod2 (fun (p : Exp × Exp) e => Exp.sliceE p.1 p.2 e)
      (prod2 Prod.mk (optAlts e₁) (optAlts e₂)) (optAlts e₃)
  | .updE e₁ p e₂ => prod2 (.updE · p ·) (optAlts e₁) (optAlts e₂)
  | .extE e₁ p e₂ => prod2 (.extE · p ·) (optAlts e₁) (optAlts e₂)
  | .callE x args => (optAltsA args).map (.callE x)
  | .iterE e (.mk .opt []) => .optE none :: (optAlts e).map fun e' => .optE (some e')
  | .iterE e it => (optAlts e).map (.iterE · it)
  | .cvtE e t₁ t₂ => (optAlts e).map (.cvtE · t₁ t₂)
  | .subE e t₁ t₂ => (optAlts e).map (.subE · t₁ t₂)
  | e => [e]

/-- `optAlts` on a list: every combination. -/
def optAltsL : List Exp → List (List Exp)
  | [] => [[]]
  | e :: es => prod2 List.cons (optAlts e) (optAltsL es)

/-- `optAlts` on an option. -/
def optAltsO : Option Exp → List (Option Exp)
  | none => [none]
  | some e => (optAlts e).map some

/-- `optAlts` on record fields. -/
def optAltsF : List ExpField → List (List ExpField)
  | [] => [[]]
  | .mk a e :: fs => prod2 (fun e' fs' => .mk a e' :: fs') (optAlts e) (optAltsF fs)

/-- `optAlts` on arguments (expression arguments only). -/
def optAltsA : List Arg → List (List Arg)
  | [] => [[]]
  | .expA e :: rest => prod2 (fun e' rest' => .expA e' :: rest') (optAlts e) (optAltsA rest)
  | a :: rest => (optAltsA rest).map (a :: ·)
end

/-- **The alternatives of a conclusion**: the conclusion itself, then, if it contains an
empty-domain option iteration, its `optAlts`. -/
def conclAlts (e : Exp) : List Exp :=
  e :: (if hasOptNil e then optAlts e else [])

/-! ## 2. The reading -/

mutual
/-- **The declarative reading with optional conclusions.** `DDerives`, except that the conclusion
is read through `conclAlts`: rule `i` of `x` derives `v` when an assignment `σ` is well typed,
some alternative of the conclusion evaluates to `v`, and every premise holds. -/
inductive DDerivesB (env : Env) (O : ElseI) : IL.Id → MixopS → List ArgV → Value → Prop where
  | rule {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value} {ps : List Param} {t : Typ}
      {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e e' : Exp}
      {prems : List Prem} {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
      (hrel : env.findRel? x = some (ps, op, t, rules))
      (hrule : rules[i]? = some (.ruleD nm qs op e prems))
      (halt : e' ∈ conclAlts e)
      (hps : bindParams VarEnv.empty ps args = some ρ₀)
      (hq : QuantsOk env (ρ₀.bindVals σ) qs)
      (he : EvalExp env (ρ₀.bindVals σ) e' v)
      (hp : ∀ pr ∈ prems, DPremB env O (O x args i v) (ρ₀.bindVals σ) pr) :
      DDerivesB env O x op args v

/-- `PremW` with relations read by `DDerivesB env O` itself. -/
inductive DPremB (env : Env) (O : ElseI) : Prop → VarEnv → Prem → Prop where
  | ifPr {els : Prop} {ρ : VarEnv} {e : Exp} :
      EvalExp env ρ e (.bool true) → DPremB env O els ρ (.ifPr e)
  | elsePr {els : Prop} {ρ : VarEnv} : els → DPremB env O els ρ .elsePr
  | letPr {els : Prop} {ρ : VarEnv} {e₁ e₂ : Exp} {w : Value} :
      EvalExp env ρ e₂ w → EvalExp env ρ e₁ w → DPremB env O els ρ (.letPr e₁ e₂)
  | rulePr {els : Prop} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
      {avs : List ArgV} {w : Value} :
      EvalArgs env ρ args avs → EvalExp env ρ e w → DDerivesB env O x op avs w →
      DPremB env O els ρ (.rulePr x args op e)
  | iterOptNone {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → (∀ p ∈ xvs, p.2 = .opt none) →
      DPremB env O els ρ (.iterPr pr (.mk .opt ds))
  | iterOptSome {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs row : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → domSomes xvs = some row →
      DPremB env O els (ρ.bindVals row) pr → DPremB env O els ρ (.iterPr pr (.mk .opt ds))
  | iterList {els : Prop} {ρ : VarEnv} {pr : Prem} {it : Iter} {ds : List Dom}
      {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)} {k : Nat} :
      (it = .list ∨ (it = .list1 ∧ 1 ≤ k)) →
      EvalDoms env ρ ds xvs → ds ≠ [] → domLists xvs = some dls →
      (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls none k, DPremB env O els (ρ.bindVals r) pr) →
      DPremB env O els ρ (.iterPr pr (.mk it ds))
  | iterListN {els : Prop} {ρ : VarEnv} {pr : Prem} {eₙ : Exp} {ido : Option IL.Id}
      {ds : List Dom} {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
      {kv : Value} {k : Nat} :
      EvalDoms env ρ ds xvs → EvalExp env ρ eₙ kv → kv.asNat? = some k →
      domLists xvs = some dls → (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls ido k, DPremB env O els (ρ.bindVals r) pr) →
      DPremB env O els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))
end

/-- The body of a rule under `DDerivesB`'s reading of its conclusion: `RuleBody` at some
alternative of the conclusion. -/
def RuleBodyB (env : Env) (D : Interp) (els : Prop) (ps : List Param) (args : List ArgV)
    (op : MixopS) (r : Rule) (v : Value) : Prop :=
  match r with
  | .ruleD nm qs op' e prems => ∃ e' ∈ conclAlts e,
      RuleBody env D els ps args op (.ruleD nm qs op' e' prems) v

/-- `otherwiseAt` over `DDerivesB`: rule `i` of `x` may use its `otherwise` premise at `v` when no
earlier rule fires on the same left-hand side under the new reading. -/
def otherwiseAtB (env : Env) (x : IL.Id) (args : List ArgV) : Nat → Value → Prop
  | i, v => ∀ j, j < i → ∀ ps op t rules r, env.findRel? x = some (ps, op, t, rules) →
      rules[j]? = some r → ∀ w, SameLhs v w →
      ¬ RuleBodyB env (DDerivesB env noElse) (otherwiseAtB env x args j w) ps args op r w
termination_by i => i

/-- `otherwiseAtB`, as an `ElseI`. -/
def otherwiseB (env : Env) : ElseI := fun x args i v => otherwiseAtB env x args i v

/-- SpecTec's whole-machine step, under the new reading. -/
def SStepB (env : Env) (c c' : Value) : Prop :=
  DDerivesB env (otherwiseB env) "Step" "%~>%" [] (.tuple [c, c'])

/-- `Step_pure`, under the new reading. -/
def SPureB (env : Env) (is js : List Value) : Prop :=
  DDerivesB env (otherwiseB env) "Step_pure" "%~>%" [] (.tuple [.list is, .list js])

/-- `Step_read`, under the new reading. -/
def SReadB (env : Env) (c : Value) (js : List Value) : Prop :=
  DDerivesB env (otherwiseB env) "Step_read" "%~>%" [] (.tuple [c, .list js])

/-- Rule `i` of `x` fires on `v`, under the new reading. -/
def FiresB (env : Env) (x : IL.Id) (i : Nat) (v : Value) : Prop :=
  ∃ t rules r, env.findRel? x = some ([], "%~>%", t, rules) ∧ rules[i]? = some r ∧
    RuleBodyB env (DDerivesB env (otherwiseB env)) (otherwiseB env x [] i v) [] [] "%~>%" r v

section Fwd

variable {H : Type}
open Silmaril.Wasm.Execution.Core

/-- A forward step under the new reading: `FwdP` with `SStepB`. -/
def FwdPB (env : Env) (hn : H → String) (c c' : Config H) : Prop :=
  Typed env hn c → Typed env hn c' → SStepB env (configV hn c) (configV hn c')

end Fwd

/-! ## 3. What the transfer lemmas consult -/

/-- The relations a premise consults. -/
def premRels : Prem → List IL.Id
  | .rulePr x _ _ _ => [x]
  | .iterPr pr _ => premRels pr
  | _ => []

/-- The relations a list of premises consults. -/
def premsRels : List Prem → List IL.Id
  | [] => []
  | pr :: prs => premRels pr ++ premsRels prs

/-- A rule is **plain** for the relations `S`: its conclusion has no empty-domain option
iteration, and every relation its premises consult is in `S`. -/
def PlainRule (S : IL.Id → Prop) : Rule → Prop
  | .ruleD _ _ _ e prems => hasOptNil e = false ∧ ∀ y ∈ premsRels prems, S y

/-- **A set of relations closed under plainness**: every rule of every relation in `S` is plain
for `S`. On such a set the two readings agree (`Round6.Reading.dderivesB_iff_of_closed`). -/
def Closed (env : Env) (S : IL.Id → Prop) : Prop :=
  ∀ x, S x → ∀ ps op t rules, env.findRel? x = some (ps, op, t, rules) →
    ∀ r ∈ rules, PlainRule S r

/-- `PlainRule`, as a check over a list of relation names. -/
def plainRuleB (S : List IL.Id) : Rule → Bool
  | .ruleD _ _ _ e prems => !hasOptNil e && (premsRels prems).all fun y => decide (y ∈ S)

/-- `Closed`, as a check over a list of relation names. -/
def closedB (env : Env) (S : List IL.Id) : Bool :=
  S.all fun x => match env.findRel? x with
    | some (_, _, _, rules) => rules.all (plainRuleB S)
    | none => true

/-- The conclusion of a rule. -/
def ruleConcl : Rule → Exp
  | .ruleD _ _ _ e _ => e

/-- Every rule of a list is plain for `S`, or has a conclusion without empty-domain option
iterations that names one of the constructors `K` (`RefsGC.ruleTags`). -/
def plainOrTagsB (S : List IL.Id) (K : List MixopS) (rules : List Rule) : Bool :=
  rules.all fun r => plainRuleB S r ||
    (!hasOptNil (ruleConcl r) && (RefsGC.ruleTags r).any fun op => decide (op ∈ K))

/-- A premise without an `otherwise`. -/
def noElsePr : Prem → Bool
  | .elsePr => false
  | .iterPr pr _ => noElsePr pr
  | _ => true

/-- A rule that is plain for `S` and has no `otherwise` premise. -/
def plainNoElseB (S : List IL.Id) : Rule → Bool
  | r@(.ruleD _ _ _ _ prems) => plainRuleB S r && prems.all noElsePr

/-- The constructors of the four instructions whose rules consult `Ref_ok`. -/
def castTags : List MixopS := ["BR_ON_CAST", "BR_ON_CAST_FAIL", "REF.TEST", "REF.CAST"]

/-! ## 4. `Ref_ok` and the cast rules under the new reading -/

section Casts

variable {H : Type}
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded)
open Round4Int (BI)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)

/-- `Round5.Fwd.RefOkAt` under the new reading: `Ref_ok` is Core's `RefOk` at one store and one
reference type, under every reading of `otherwise`. -/
def RefOkAtB (env : Env) (hn : H → String) (s : Store H) (rt : CRefType) : Prop :=
  ∀ (O : ElseI) (r : Ref), DDerivesB env O "Ref_ok" "%|-%:%" []
    (.tuple [storeV hn s, refToValue r, CT.elemType rt]) ↔ RefOk s r rt

/-- **`Round5.Fwd.RefOkB` under the new reading** (`RefOkB'`): on a typed store and a bounded
reference type, `Ref_ok` read by `DDerivesB` is Core's `RefOk`. Not proved here: the round-5
counterexample (`null` at `REF NULL ANY`) is no counterexample any more
(`Round6.Reading.dderivesB_refOk_nullAny`), and the `sub` rule now needs SpecTec's
`Reftype_ok`/`Reftype_sub` to agree with Core's `TyOk {}`/`Sub {}` on bounded types. -/
structure RefOkBB (env : Env) : Prop where
  /-- On a typed store and a bounded reference type. -/
  refOk : ∀ {H : Type} (hn : H → String) (s : Store H) (rt : CRefType),
    TypedV env storeT (storeV hn s) → Round4.tyBnd rt = true → RefOkAtB env hn s rt

/-- **The cast rules, forward, under the new reading** (`Round5.RefOk.CastsFwd` with `FwdPB`). -/
structure CastsFwdB (B : Builtins) (hn : H → String) : Prop where
  /-- `ref.test`. -/
  refTest : ∀ (s : Store H) (f : Frame) (r : Ref) (rt : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ →
    (RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 1]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 0]⟩)
  /-- `ref.cast`. -/
  refCast : ∀ (s : Store H) (f : Frame) (r : Ref) (rt : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ →
    (RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv B) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv B) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩)
  /-- `br_on_cast`. -/
  brOnCast : ∀ (s : Store H) (f : Frame) (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ →
    (RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩)
  /-- `br_on_cast_fail`. -/
  brOnCastFail : ∀ (s : Store H) (f : Frame) (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ →
    (RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩)

/-- **The cast rules, backward, under the new reading** (`Round5.RefOk.CastsBwd` with `FiresB`):
`Step_read` 2–5 and 65–68 (`Round5.Read.readDoneK`), under `ReadValidS`. -/
def CastsBwdB (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ i ∈ Round5.Read.readDoneK, ∀ (c : Config H) (w : Value), Round5.Read.ReadValidS c →
    Typed (simEnv (BI P hn host)) hn c →
    FiresB (simEnv (BI P hn host)) "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩

end Casts

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading
