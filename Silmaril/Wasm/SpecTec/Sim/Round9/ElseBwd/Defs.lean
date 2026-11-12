module

public import Silmaril.Wasm.SpecTec.Sim.Round8.NxStep.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.NxTyped.Thms

/-!
# Round 9, RE and RM: the `otherwise` rules of `Step_read` (definitions)

Rule `i` of `Step_read` with an `otherwise` premise may fire at `(a, b)` when no earlier rule
`j < i` fires at `(a, c)` for any `c` (SpecTec's reading, `Round6.Reading.otherwiseAtB`, and the
declarative one, `Sim.otherwiseAt`). To move such a firing along a map `ε` of values (export
erasure `Swap.eraseV` for RE, code erasure `CodeErase.Swap.eraseC` for RM), one has to show that
no earlier rule fires at `(ε a, c')`. This topic splits that into two parts, for both readings and
any `ε` that keeps instruction heads:

* **Heads.** The left-hand side of every `Step_read` rule is `z; instr*` (`%;%`). When the last
  instruction of both rules is a constructor (`lhsHead`), and the constructors differ, rule `j`
  cannot fire where rule `i` did, before or after `ε`. No backward reasoning is needed.
* **The pairs left** (`elsePairs`): the pairs `(i, j)` of `Step_read` with `i` an `otherwise` rule,
  `j < i`, and heads that are not known to differ. For those the obligation is a backward firing
  (`PairReflectB` for RE, `PairReflectD` for RM): if rule `j` fires at `(ε a, c')`, it fires at
  `(a, c)` for some `c`, where `a` is the left-hand side of a firing of rule `i`.

The definitions:

* `lastHead`, `cfgHead`, `lhsHead`: the head constructor of the last instruction of a left-hand
  side, as syntax. `vHead`: the same of a value `(z; instrs, rhs)`.
* `headsDiffer ri rj`: every conclusion alternative of both rules has a known head, and the heads
  differ. `hasElse r`: `r` has an `otherwise` premise (at top level).
* `elsePairsOf rules`: the pairs left. The kernel computes it on the fixed script
  (`Round9.ElseBwd.elsePairs_fixed`).
* `PairReflectB env ε x i j`, `PairReflectD env ε x i j`: the backward firing of rule `j` at the
  left-hand sides where rule `i` fires, under the two readings.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

/-! ## Heads of left-hand sides -/

/-- The head constructor of the last instruction of an instruction-list expression: a list whose
last element is a constructor, possibly after a concatenation. -/
def lastHead : Exp → Option MixopS
  | .listE es => match es.getLast? with
    | some (.caseE op _) => some op
    | _ => none
  | .catE _ e₂ => lastHead e₂
  | _ => none

/-- The head of a configuration expression `z; instr*`. -/
def cfgHead : Exp → Option MixopS
  | .caseE op (.tupE [_, is]) => if op = "%;%" then lastHead is else none
  | _ => none

/-- The head of a conclusion `(z; instr*, rhs)`. -/
def lhsHead : Exp → Option MixopS
  | .tupE [l, _] => cfgHead l
  | _ => none

/-- The head constructor of the last element of a list value. -/
def vHeadL : Value → Option MixopS
  | .list vs => match vs.getLast? with
    | some (.case op _) => some op
    | _ => none
  | _ => none

/-- The head of a configuration value `z; instrs`. -/
def vHeadC : Value → Option MixopS
  | .case op (.tuple [_, is]) => if op = "%;%" then vHeadL is else none
  | _ => none

/-- The head constructor of the last instruction of a value `(z; instrs, rhs)`. -/
def vHead : Value → Option MixopS
  | .tuple [l, _] => vHeadC l
  | _ => none

/-- The heads of two conclusion alternatives are known and differ. -/
def headNe (e₁ e₂ : Exp) : Bool :=
  match lhsHead e₁, lhsHead e₂ with
  | some o₁, some o₂ => o₁ != o₂
  | _, _ => false

/-- **Every conclusion alternative of `ri` and of `rj` has a known head, and they differ.** -/
def headsDiffer : Rule → Rule → Bool
  | .ruleD _ _ _ e₁ _, .ruleD _ _ _ e₂ _ =>
    (Round6.Reading.conclAlts e₁).all fun a => (Round6.Reading.conclAlts e₂).all fun b => headNe a b

/-- A rule has an `otherwise` premise at top level. -/
def hasElse : Rule → Bool
  | .ruleD _ _ _ _ prems => prems.any fun pr => match pr with
    | .elsePr => true
    | _ => false

/-- **The pairs left**: `(i, j)` with rule `i` an `otherwise` rule, `j < i`, and heads not known
to differ. -/
def elsePairsOf (rules : List Rule) : List (Nat × Nat) :=
  (List.range rules.length).flatMap fun i => match rules[i]? with
    | some ri => if hasElse ri then
        (List.range i).filterMap fun j => match rules[j]? with
          | some rj => if headsDiffer ri rj then none else some (i, j)
          | none => none
      else []
    | none => []

/-- The rule list of every `Step_read` entry of `m` gives `l` (`elsePairsOf`), and no `Step` rule
has an `otherwise` premise. -/
def elsePairsIs (m : Map RelDef) (l : List (Nat × Nat)) : Bool :=
  m.all fun p => (p.1 != "Step_read" || elsePairsOf p.2.2.2.2 == l) &&
    (p.1 != "Step" || !p.2.2.2.2.any hasElse)

/-- **The pairs left in the fixed script** (94): `(i, j)` with `i` an `otherwise` rule of
`Step_read`, `j < i`, and heads not known to differ. Rule 13 (`throw_ref-instrs`) has no
syntactic head (its instruction list ends in `instr'*`) and occurs with every `i` but 3, 5 (26 pairs);
the other 68 pairs share a head. The kernel checks the list (`Round9.ElseBwd.elsePairs_fixed`). -/
def elsePairs : List (Nat × Nat) :=
  [(3, 2), (5, 4), (21, 9), (21, 13), (21, 16), (21, 17), (21, 18), (21, 19), (21, 20),
    (29, 13), (29, 28), (30, 13), (30, 28), (30, 29), (32, 13), (32, 31),
    (33, 13), (33, 31), (33, 32), (34, 13), (34, 31), (34, 32), (34, 33), (36, 13), (36, 35),
    (37, 13), (37, 35), (37, 36), (54, 13), (54, 53), (55, 13), (55, 53), (55, 54),
    (57, 13), (57, 56), (58, 13), (58, 56), (58, 57), (59, 13), (59, 56), (59, 57), (59, 58),
    (61, 13), (61, 60), (62, 13), (62, 60), (62, 61), (66, 13), (66, 65), (68, 13), (68, 67),
    (84, 13), (84, 82), (84, 83), (85, 13), (85, 82), (85, 83), (85, 84),
    (90, 13), (90, 86), (90, 87), (90, 88), (90, 89),
    (91, 13), (91, 86), (91, 87), (91, 88), (91, 89), (91, 90),
    (92, 13), (92, 86), (92, 87), (92, 88), (92, 89), (92, 90), (92, 91),
    (96, 13), (96, 93), (96, 94), (96, 95), (97, 13), (97, 93), (97, 94), (97, 95), (97, 96),
    (101, 13), (101, 98), (101, 99), (101, 100),
    (102, 13), (102, 98), (102, 99), (102, 100), (102, 101)]

/-! ## The backward firings left -/

open Round6.Reading (DDerivesB RuleBodyB otherwiseAtB)

/-- **Rule `j` of `x` fires backward along `ε` at the left-hand sides where rule `i` fires**,
under SpecTec's reading (RE). `a` is the left-hand side of a firing of rule `i` in a typed
instance (`NxElse.Fired`); if rule `j` fires at `(ε a, c')` on the image side, it fires at
`(a, c)` for some `c`. -/
def PairReflectB (env : Env) (ε : Value → Value) (x : IL.Id) (args args' : List ArgV)
    (i j : Nat) : Prop :=
  ∀ ps op t rules r, env.findRel? x = some (ps, op, t, rules) → rules[j]? = some r →
    ∀ a b c', Round8.NxElse.Fired env x args i (.tuple [a, b]) →
      RuleBodyB env (DDerivesB env Sim.noElse) (otherwiseAtB env x args' j (.tuple [ε a, c']))
        ps args' op r (.tuple [ε a, c']) →
      ∃ c, RuleBodyB env (DDerivesB env Sim.noElse) (otherwiseAtB env x args j (.tuple [a, c]))
        ps args op r (.tuple [a, c])

/-- **Rule `i` of `x` fires in a typed instance, read declaratively**: its conclusion evaluates
to `v` in an instance whose quantifiers are typed (the data `Sim.Fires` carries besides its
premises). -/
def FiredD (env : Env) (x : IL.Id) (args : List ArgV) (i : Nat) (v : Value) : Prop :=
  ∃ (ps : List Param) (op : MixopS) (t : Typ) (rules : List Rule) (nm : IL.Id) (qs : List Param)
    (e : Exp) (prems : List Prem) (ρ₀ : VarEnv) (σ : List (IL.Id × Value)),
    env.findRel? x = some (ps, op, t, rules) ∧ rules[i]? = some (.ruleD nm qs op e prems) ∧
    bindParams VarEnv.empty ps args = some ρ₀ ∧ Sim.QuantsOk env (ρ₀.bindVals σ) qs ∧
    EvalExp env (ρ₀.bindVals σ) e v

/-- **`PairReflectB` under the declarative reading** (RM): `Sim.RuleBody` with premises read by
`DDerives env noElse` and `otherwise` by `Sim.otherwiseAt`. -/
def PairReflectD (env : Env) (ε : Value → Value) (x : IL.Id) (args args' : List ArgV)
    (i j : Nat) : Prop :=
  ∀ ps op t rules r, env.findRel? x = some (ps, op, t, rules) → rules[j]? = some r →
    ∀ a b c', FiredD env x args i (.tuple [a, b]) →
      Sim.RuleBody env (Sim.DDerives env Sim.noElse) (Sim.otherwiseAt env x args' j (.tuple [ε a, c']))
        ps args' op r (.tuple [ε a, c']) →
      ∃ c, Sim.RuleBody env (Sim.DDerives env Sim.noElse) (Sim.otherwiseAt env x args j (.tuple [a, c]))
        ps args op r (.tuple [a, c])

/-- **The obligation at the pairs left, for RE**: `PairReflectB` along export erasure at every
pair of `elsePairs`, in `env`. -/
def ElseBwdB (env : Env) : Prop :=
  ∀ p ∈ elsePairs, PairReflectB env Swap.eraseV "Step_read" [] [] p.1 p.2

/-- **The obligation at the pairs left, for RM**: `PairReflectD` along code erasure at every pair
of `elsePairs`, in `env`. -/
def ElseBwdD (env : Env) : Prop :=
  ∀ p ∈ elsePairs, PairReflectD env Round8.CodeErase.Swap.eraseC "Step_read" [] [] p.1 p.2

/-! ## RE: the rules of `BadFwd` that pass the check up to `otherwise` -/

/-- A relation premise of `Step` or `Step_read`. -/
def stepPremB : Prem → Bool
  | .rulePr y _ _ _ => Round8.NxStep.stepRel y
  | _ => false

/-- **A premise of a checked rule, `otherwise` allowed**: `otherwise` at top level, or a premise
that passes `NxStep.premS` and is not a relation premise of `Step`/`Step_read`. -/
def premSE : Prem → Bool
  | .elsePr => true
  | pr => Round8.NxStep.premS pr && !stepPremB pr

/-- **A rule passes the check up to `otherwise`.** -/
def goodRuleE : Rule → Bool
  | .ruleD _ _ _ e prems =>
    (Round6.Reading.conclAlts e).all (EraseAll.xExp EraseAll.grE EraseAll.gdE) && prems.all premSE

/-- The `Step`/`Step_read` rules of `m` that fail both `goodRule` and `goodRuleE`. -/
def stepBadE (m : Map RelDef) : List String :=
  m.flatMap fun p => if !Round8.NxStep.stepRel p.1 then [] else p.2.2.2.2.filterMap fun r =>
    match r with
    | .ruleD nm _ _ _ _ =>
      if Round8.NxStep.goodRule r || goodRuleE r then none else some (p.1 ++ "/" ++ nm)

/-- **`NxStep.RuleAt` at a rule that also fails `goodRuleE`.** -/
def RuleAtE (env : Env) (O : ElseI) (x : IL.Id) (op : MixopS) (args : List ArgV) (i : Nat)
    (v : Value) : Prop :=
  ∃ (ps : List Param) (t : Typ) (rules : List Rule) (nm : IL.Id) (qs : List Param) (e e' : Exp)
    (prems : List Prem) (ρ₀ : VarEnv) (σ : List (IL.Id × Value)),
    env.findRel? x = some (ps, op, t, rules) ∧ rules[i]? = some (.ruleD nm qs op e prems) ∧
    Round8.NxStep.goodRule (.ruleD nm qs op e prems) = false ∧
    goodRuleE (.ruleD nm qs op e prems) = false ∧ e' ∈ Round6.Reading.conclAlts e ∧
    bindParams VarEnv.empty ps args = some ρ₀ ∧ QuantsOk env (ρ₀.bindVals σ) qs ∧
    EvalExp env (ρ₀.bindVals σ) e' v ∧
    ∀ pr ∈ prems, Round6.Reading.DPremB env O (O x args i v) (ρ₀.bindVals σ) pr

/-- **`NxStep.BadFwd` at the rules that fail `goodRuleE` too** (eight in the fixed script,
`Round9.ElseBwd.stepBadE_fixed`). -/
def BadFwdE (env : Env) : Prop :=
  ∀ {x : IL.Id} {op : MixopS} {args : List ArgV} {i : Nat} {v : Value},
    Round8.NxStep.stepRel x = true →
    RuleAtE env (Round6.Reading.otherwiseB env) x op args i v →
    Round6.Reading.DDerivesB env (Round6.Reading.otherwiseB env) x op (args.map Swap.eraseA)
      (Swap.eraseV v)

/-! ## The simple pairs -/

/-- A conclusion `(z; L, R)` whose state is a variable: `(z, L)`. -/
def cfgVar : Exp → Option (IL.Id × Exp)
  | .tupE [.caseE op (.tupE [.varE z, l]), _] => if op = "%;%" then some (z, l) else none
  | _ => none

/-- The IL type `state`. -/
def isStateT : Typ → Bool
  | .varT x [] => x == "state"
  | _ => false

/-- `z` is an expression quantifier of `qs`, and every quantifier named `z` has type `state`. -/
def stateQ (qs : List Param) (z : IL.Id) : Bool :=
  (Determ.quantNames qs).contains z && qs.all fun q => match q with
    | .expP x t => x != z || isStateT t
    | _ => true

/-- **A left-hand side `z; L`** with `z` a state quantifier and `L` reading only quantifiers of
export-free type. -/
def lhsOk (qs : List Param) (e : Exp) : Bool :=
  match cfgVar e with
  | some (z, l) => stateQ qs z && EraseDer.varsIn (Round8.NxTyp.nxNames qs) (freeExp l) &&
      !(Round8.NxTyp.nxNames qs).contains z
  | none => false

/-- Every conclusion alternative of a rule has a left-hand side `z; L` (`lhsOk`) and passes round
3's check. -/
def lhsRule : Rule → Bool
  | .ruleD _ qs _ e _ => (Round6.Reading.conclAlts e).all fun e' =>
    lhsOk qs e' && EraseAll.xExp EraseAll.grE EraseAll.gdE e'

/-- Every quantifier is an expression quantifier, of export-free type unless it is `z`. -/
def quantsNx (qs : List Param) (z : IL.Id) : Bool :=
  qs.all fun q => match q with
    | .expP x t => x == z || Round8.NxTyp.nxT t
    | _ => false

/-- **A simple earlier rule**: every conclusion alternative is `(z; L, R)` with `lhsOk`, every
quantifier but `z` has export-free type, the conclusion passes round 3's check, and every premise is
an `if` that passes it and is not a binding site. -/
def simpleRule : Rule → Bool
  | .ruleD _ qs _ e prems =>
    (Round6.Reading.conclAlts e).all (fun e' => match cfgVar e' with
      | some (z, _) => lhsOk qs e' && quantsNx qs z && EraseAll.xExp EraseAll.grE EraseAll.gdE e'
      | none => false) &&
    prems.all fun pr => match pr with
      | .ifPr c => EraseAll.xExp EraseAll.grE EraseAll.gdE c &&
          !NxSites.bindSite NxTyped.sigX (NxSites.quantsΓ qs) pr
      | _ => false

/-- The pairs of `l` whose `otherwise` rule has `lhsRule` and whose earlier rule is simple. -/
def simplePairsOf (rules : List Rule) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.filter fun p => match rules[p.1]?, rules[p.2]? with
    | some ri, some rj => lhsRule ri && simpleRule rj
    | _, _ => false

/-- The rule list of every `Step_read` entry of `m` has `simplePairsOf … elsePairs = l`. -/
def simplePairsIs (m : Map RelDef) (l : List (Nat × Nat)) : Bool :=
  m.all fun p => p.1 != "Step_read" || simplePairsOf p.2.2.2.2 elsePairs == l

/-- **The simple pairs of the fixed script** (45 of `elsePairs`): the earlier rule is an
out-of-bounds, null or handler rule whose only premises are `if`s (`Round9.ElseBwd.simplePairs_fixed`). -/
def simplePairs : List (Nat × Nat) :=
  [(21, 16), (21, 17), (21, 18), (21, 19), (21, 20), (29, 28), (30, 28), (32, 31), (33, 31),
    (34, 31), (36, 35), (37, 35), (54, 53), (55, 53), (57, 56), (58, 56), (59, 56), (61, 60),
    (62, 60), (84, 82), (84, 83), (85, 82), (85, 83), (90, 86), (90, 87), (90, 88), (90, 89),
    (91, 86), (91, 87), (91, 88), (91, 89), (92, 86), (92, 87), (92, 88), (92, 89), (96, 93),
    (96, 94), (96, 95), (97, 93), (97, 94), (97, 95), (101, 98), (101, 99), (102, 98), (102, 99)]

/-! ## The pairs with `throw_ref-instrs` -/

/-- The head of an instruction expression, if it is a constructor. -/
def instrHead : Exp → Option MixopS
  | .caseE op _ => some op
  | _ => none

/-- The heads of a configuration `z; [e₁, …, eₙ]` whose instructions are a list literal. -/
def cfgHeads : Exp → Option (List (Option MixopS))
  | .tupE [.caseE op (.tupE [_, .listE es]), _] =>
    if op = "%;%" then some (es.map instrHead) else none
  | _ => none

/-- A configuration `z; e₁ (o₁ …) (o₂ …) e₄`: two adjacent constructors after a prefix. -/
def cfgAdj : Exp → Option (MixopS × MixopS)
  | .tupE [.caseE op (.tupE [_, .catE _ (.catE (.listE [.caseE o₁ _])
      (.catE (.listE [.caseE o₂ _]) _))]), _] => if op = "%;%" then some (o₁, o₂) else none
  | _ => none

/-- A head is compatible with a constructor: unknown, or equal. -/
def compat : Option MixopS → MixopS → Bool
  | none, _ => true
  | some o, o' => o == o'

/-- **No two adjacent positions of `hs` are compatible with `o₁` then `o₂`.** -/
def noAdj (o₁ o₂ : MixopS) : List (Option MixopS) → Bool
  | h₁ :: h₂ :: t => !(compat h₁ o₁ && compat h₂ o₂) && noAdj o₁ o₂ (h₂ :: t)
  | _ => true

/-- Every conclusion alternative of `ri` has list-literal instructions, every one of `rj` has two
adjacent constructors, and they cannot line up. -/
def adjDiffer : Rule → Rule → Bool
  | .ruleD _ _ _ e₁ _, .ruleD _ _ _ e₂ _ =>
    (Round6.Reading.conclAlts e₁).all fun a => (Round6.Reading.conclAlts e₂).all fun b =>
      match cfgHeads a, cfgAdj b with
      | some hs, some (o₁, o₂) => noAdj o₁ o₂ hs
      | _, _ => false

/-- The pairs of `l` whose rules satisfy `adjDiffer`. -/
def adjPairsOf (rules : List Rule) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.filter fun p => match rules[p.1]?, rules[p.2]? with
    | some ri, some rj => adjDiffer ri rj
    | _, _ => false

/-- The rule list of every `Step_read` entry of `m` has `adjPairsOf … elsePairs = l`. -/
def adjPairsIs (m : Map RelDef) (l : List (Nat × Nat)) : Bool :=
  m.all fun p => p.1 != "Step_read" || adjPairsOf p.2.2.2.2 elsePairs == l

/-- **The pairs with `throw_ref-instrs` (rule 13)** (26): its instructions contain
`REF.EXN_ADDR a` then `THROW_REF`, which cannot line up with the instructions of any of these
`otherwise` rules (`Round9.ElseBwd.adjPairs_fixed`). -/
def adjPairs : List (Nat × Nat) :=
  [(21, 13), (29, 13), (30, 13), (32, 13), (33, 13), (34, 13), (36, 13), (37, 13), (54, 13),
    (55, 13), (57, 13), (58, 13), (59, 13), (61, 13), (62, 13), (66, 13), (68, 13), (84, 13),
    (85, 13), (90, 13), (91, 13), (92, 13), (96, 13), (97, 13), (101, 13), (102, 13)]

/-- **`ElseBwdB` outside the simple pairs**: `PairReflectB` along export erasure at the 49 pairs of
`elsePairs` that are not in `simplePairs`. -/
def ElseBwdBRest (env : Env) : Prop :=
  ∀ p ∈ elsePairs, p ∉ simplePairs → PairReflectB env Swap.eraseV "Step_read" [] [] p.1 p.2

/-- **The pairs left after the simple pairs and the pairs with `throw_ref-instrs`** (23):
* four whose earlier rule has a `Ref_ok` premise: `br_on_cast(_fail)-succeed`, `ref.test-true`,
  `ref.cast-succeed` (3, 5, 66, 68);
* `throw_ref-handler-next` against `return_call_ref-handler` (21, 9), whose quantifiers include
  `instr*`;
* sixteen whose earlier rule is itself an `otherwise` rule (`…-zero`, `…-le`), so its own
  `otherwise` premise has to be read backward;
* `array.init_data-oob2` (100) against rules 101 and 102, which has an `Expand` premise. -/
def leftPairs : List (Nat × Nat) :=
  [(3, 2), (5, 4), (21, 9), (30, 29), (33, 32), (34, 32), (34, 33), (37, 36), (55, 54),
    (58, 57), (59, 57), (59, 58), (62, 61), (66, 65), (68, 67), (85, 84), (91, 90), (92, 90),
    (92, 91), (97, 96), (101, 100), (102, 100), (102, 101)]

/-- **`ElseBwdB` at the 23 pairs left** (RE). -/
def ElseBwdBLeft (env : Env) : Prop :=
  ∀ p ∈ leftPairs, PairReflectB env Swap.eraseV "Step_read" [] [] p.1 p.2

/-- **`ElseBwdD` outside the pairs with `throw_ref-instrs`** (RM, 68 pairs). -/
def ElseBwdDRest (env : Env) : Prop :=
  ∀ p ∈ elsePairs, p ∉ adjPairs →
    PairReflectD env Round8.CodeErase.Swap.eraseC "Step_read" [] [] p.1 p.2

/-! ## One level of `otherwise` chains -/

/-- **A simple earlier rule that may have an `otherwise` premise**: `simpleRule` with `otherwise`
allowed among the premises. -/
def simpleRuleE : Rule → Bool
  | .ruleD _ qs _ e prems =>
    (Round6.Reading.conclAlts e).all (fun e' => match cfgVar e' with
      | some (z, _) => lhsOk qs e' && quantsNx qs z && EraseAll.xExp EraseAll.grE EraseAll.gdE e'
      | none => false) &&
    prems.all fun pr => match pr with
      | .ifPr c => EraseAll.xExp EraseAll.grE EraseAll.gdE c &&
          !NxSites.bindSite NxTyped.sigX (NxSites.quantsΓ qs) pr
      | .elsePr => true
      | _ => false

/-- **The chain pairs** (12 of `leftPairs`): the earlier rule `j` is an `otherwise` rule
(`…-zero`) that passes `simpleRuleE`, and every rule `k < j` is, against `i`, outside `elsePairs`,
in `adjPairs` or in `simplePairs`. -/
def chainPairs : List (Nat × Nat) :=
  [(30, 29), (33, 32), (34, 32), (37, 36), (55, 54), (58, 57), (59, 57), (62, 61), (85, 84),
    (91, 90), (92, 90), (97, 96)]

/-- The rule list of every `Step_read` entry of `m` has `lhsRule` at `i` and `simpleRuleE` at `j`
for every chain pair. -/
def chainPairsIs (m : Map RelDef) : Bool :=
  m.all fun p => p.1 != "Step_read" || chainPairs.all fun q => match p.2.2.2.2[q.1]?, p.2.2.2.2[q.2]? with
    | some ri, some rj => lhsRule ri && simpleRuleE rj
    | _, _ => false

/-- **The pairs left after the chain pairs** (11): `leftPairs` without `chainPairs`. -/
def leftPairs' : List (Nat × Nat) :=
  [(3, 2), (5, 4), (21, 9), (34, 33), (59, 58), (66, 65), (68, 67), (92, 91), (101, 100),
    (102, 100), (102, 101)]

/-- **`ElseBwdB` at the 11 pairs of `leftPairs'`** (RE). -/
def ElseBwdBLeft' (env : Env) : Prop :=
  ∀ p ∈ leftPairs', PairReflectB env Swap.eraseV "Step_read" [] [] p.1 p.2

/-! ## Two levels of `otherwise` chains -/

/-- **The chain pairs of the second level** (2 of `leftPairs'`): `table.copy-gt` and
`memory.copy-gt` against `…-le`, whose own earlier `…-zero` rule is a chain rule of the first
level. (`array.copy-le` has an `Expand` premise, so `(92, 91)` is not one.) -/
def chain2Pairs : List (Nat × Nat) := [(34, 33), (59, 58)]

/-- The rule list of every `Step_read` entry of `m` has `lhsRule` at `i` and `simpleRuleE` at `j`
for every pair of `chain2Pairs`. -/
def chain2PairsIs (m : Map RelDef) : Bool :=
  m.all fun p => p.1 != "Step_read" || chain2Pairs.all fun q =>
    match p.2.2.2.2[q.1]?, p.2.2.2.2[q.2]? with
    | some ri, some rj => lhsRule ri && simpleRuleE rj
    | _, _ => false

/-- **The pairs left after both levels of chains** (9): `leftPairs'` without `chain2Pairs`. -/
def leftPairs'' : List (Nat × Nat) :=
  [(3, 2), (5, 4), (21, 9), (66, 65), (68, 67), (92, 91), (101, 100), (102, 100), (102, 101)]

/-- **`ElseBwdB` at the 9 pairs of `leftPairs''`** (RE). -/
def ElseBwdBLeft'' (env : Env) : Prop :=
  ∀ p ∈ leftPairs'', PairReflectB env Swap.eraseV "Step_read" [] [] p.1 p.2

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
