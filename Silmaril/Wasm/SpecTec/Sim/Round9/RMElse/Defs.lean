module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMRead.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round8.FiresC.Defs

/-!
# Round 9, rm (pass 2): the 28 `otherwise` rules of `Step_read` under code erasure (definitions)

Round 9's `RMRead.OpenRMRestDPJ` keeps round 8's `firesRead`: `RMCode.FiresEraseD` at the 28 rules
of `Step_read` with an `otherwise` premise (`FiresC.elseRead`). Round 8's `FiresC.ruleBody_erase`
moves a rule body across `eraseC` given that its relation premises and its `otherwise` premise move;
round 9's `ElseBwd.otherwise_eraseC_rest` moves the declarative `otherwise` of a fired `Step_read`
rule given `ElseBwd.ElseBwdDRest` (a backward firing at 68 pairs of rules).

* `elsePremC`, `elseRuleC`, `elseAt`: the check on the 28 rules: each passes round 8's evaluator
  check, has a top-level `otherwise` premise, and every other premise is a `FiresC.relPrem`
  (no `otherwise` inside, relations in `FiresC.relG`). The kernel checks it on the fixed script
  (`Round9.RMElse.elseAt_ok`).
* `OpenRMRestDPK`: `RMRead.OpenRMRestDPJ` with `firesRead` replaced by `ElseBwdDRest`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMElse

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (configVD BoundedSelM)

/-- **A premise of an `otherwise` rule that moves across code erasure**: `otherwise` at top level,
or a premise without `otherwise` whose relations are in `FiresC.relG`. -/
def elsePremC : Prem → Bool
  | .elsePr => true
  | pr => Round8.FiresC.relPrem pr

/-- **An `otherwise` rule whose other premises move**: it passes round 8's evaluator check, has a
top-level `otherwise` premise, and every premise is `elsePremC`. -/
def elseRuleC (r : Rule) : Bool :=
  Round8.CodeErase.EraseAll.xRule Round8.CodeErase.EraseAll.grC Round8.CodeErase.EraseAll.gdC r &&
    ElseBwd.hasElse r && match r with
    | .ruleD _ _ _ _ prems => prems.all elsePremC

/-- Every index of `l` names an `elseRuleC` rule of `x`. -/
noncomputable def elseAt (x : IL.Id) (l : List Nat) : Bool :=
  l.all fun i => match (Round8.FiresC.rulesOf x)[i]? with
    | some r => elseRuleC r
    | none => false


/-! ## `CODE`-free types -/

/-- **The type names whose values hold no `CODE` record**: round 7's export-free names
(`NxSites.sigFixed.good`) and `expr`, `frame`, `funccode`, `instr`, `moduleinst`, which may hold an
`EXPORTS` record but no function instance. Only `funcinst` and the types that hold one (`store`,
`state`, `config`, …) are left out. The kernel checks the list (`Round9.RMElse.goodTypsC_fixed`). -/
def goodC : List String :=
  ["Fnn", "Inn", "Jnn", "K", "Lnn", "M", "N", "Pnn", "Vnn", "X", "absheaptype", "addr",
    "addrtype", "arrayaddr", "arrayinst", "binop_", "bit", "blocktype", "bshape", "byte",
    "catch", "char", "comptype", "consttype", "context", "cvtop__", "dataaddr", "dataidx",
    "datainst", "datatype", "deftype", "dim", "elemaddr", "elemidx", "eleminst", "elemtype",
    "exnaddr", "exninst", "exp", "exportinst", "expr", "externaddr", "fN", "fNmag", "fieldidx",
    "fieldtype", "fieldval", "final", "frame", "funcaddr", "funccode", "funcidx", "globaladdr",
    "globalidx", "globalinst", "globaltype", "half", "heaptype", "hostaddr", "hostfunc", "iN",
    "idx", "init", "instr", "instrtype", "ishape", "labelidx", "lane_", "laneidx", "lanetype",
    "limits", "list", "lit_", "loadop_", "local", "localidx", "localtype", "m", "memaddr",
    "memarg", "memidx", "meminst", "memtype", "moduleinst", "mut", "n", "name", "null", "num_",
    "numtype", "oktypenat", "pack_", "packtype", "rectype", "ref", "reftype", "relaxed2",
    "relop_", "result", "resulttype", "shape", "storagetype", "storeop_", "structaddr",
    "structinst", "subtype", "sx", "sz", "tableaddr", "tableidx", "tableinst", "tabletype",
    "tagaddr", "tagidx", "taginst", "tagtype", "testop_", "typeidx", "typeuse", "typevar", "u31",
    "u32", "u64", "u8", "uN", "unop_", "vN", "val", "valtype", "vbinop_", "vcvtop__", "vec_",
    "vectype", "vextbinop__", "vextternop__", "vextunop__", "vloadop_", "vrelop_", "vshiftop_",
    "vswizzlop_", "vternop_", "vtestop_", "vunop_", "vvbinop", "vvternop", "vvtestop", "vvunop",
    "zero"]

/-- **A type body without `CODE` records**: no field is named `CODE`, and every type it mentions
is in `ok`. -/
def goodDTC (ok : List String) : DefTyp → Bool
  | .aliasT t => Round7.NxSites.goodTyp ok t
  | .structT fs => fs.all fun f => match f with
    | .mk a t _ _ => a != "CODE" && Round7.NxSites.goodTyp ok t
  | .variantT cs => cs.all fun c => match c with | .mk _ t _ _ => Round7.NxSites.goodTyp ok t

/-- **Every type `env` finds under a `good` name has `CODE`-free instance bodies.** -/
def EnvNC (good : List String) (env : Env) : Prop :=
  ∀ x td, env.findTyp? x = some td → good.contains x = true →
    ∀ i ∈ td.2, goodDTC good (Round7.NxSites.instDT i) = true

/-- The check behind `EnvNC goodC`: every type of `m` named in `goodC` has `goodDTC` instances. -/
def goodTypsC (m : Map TypDef) : Bool :=
  m.all fun p => !goodC.contains p.1 || p.2.2.all fun i => goodDTC goodC (Round7.NxSites.instDT i)

/-- A type whose values hold no `CODE` record. -/
def ncT (t : Typ) : Bool := Round7.NxSites.nxAT goodC (Round7.NxSites.toAT t)

/-- The expression quantifiers of `qs` of `CODE`-free type. -/
def ncNames (qs : List Param) : List String :=
  qs.filterMap fun q => match q with
    | .expP x t => if ncT t then some x else none
    | _ => none

/-- **A type that `hasTyp` reads alike in two scopes that differ only at `z`**: a type name whose
arguments do not mention `z`, or an `?`/`*`/`+` iteration of such a type. -/
def tyZ (z : IL.Id) : Typ → Bool
  | .varT _ args => decide (z ∉ (freeArgs args).varid)
  | .iterT t .opt => tyZ z t
  | .iterT t .list => tyZ z t
  | .iterT t .list1 => tyZ z t
  | .boolT => true
  | .numT _ => true
  | .textT => true
  | _ => false

/-- **A left-hand side `z; L`** with `z` a state quantifier and `L` reading only quantifiers of
`CODE`-free type. -/
def lhsOkC (qs : List Param) (e : Exp) : Bool :=
  match ElseBwd.cfgVar e with
  | some (z, l) => ElseBwd.stateQ qs z && Round7.EraseDer.varsIn (ncNames qs) (freeExp l) &&
      !(ncNames qs).contains z
  | none => false

/-- The conclusion of a rule has a left-hand side `lhsOkC`. -/
def lhsRuleC : Rule → Bool
  | .ruleD _ qs _ e _ => lhsOkC qs e

/-- Every quantifier is an expression quantifier, of `CODE`-free type read alike off `z` unless
it is `z`. -/
def quantsNC (qs : List Param) (z : IL.Id) : Bool :=
  qs.all fun q => match q with
    | .expP x t => x == z || (ncT t && tyZ z t)
    | _ => false

/-- **A simple earlier rule, `otherwise` allowed** (RM): its conclusion is `(z; L, R)` with
`lhsOkC`, `z` is not `_`, its quantifiers but `z` are `quantsNC`, its conclusion reads only
quantifiers, and every premise is `otherwise`, an `if` reading only quantifiers, or an `Expand`
premise without arguments reading only quantifiers (its derivations conclude `CODE`-free values,
`relNC`). -/
def simpleRuleCE : Rule → Bool
  | .ruleD _ qs _ e prems =>
    (match ElseBwd.cfgVar e with
      | some (z, _) => lhsOkC qs e && quantsNC qs z && z != "_"
      | none => false) &&
    Round7.EraseDer.varsIn (Round7.Determ.quantNames qs) (freeExp e) &&
    prems.all fun pr => match pr with
      | .ifPr c => Round7.EraseDer.varsIn (Round7.Determ.quantNames qs) (freeExp c)
      | .elsePr => true
      | .rulePr x args _ c => x == "Expand" && args.isEmpty &&
          Round7.EraseDer.varsIn (Round7.Determ.quantNames qs) (freeExp c)
      | _ => false

/-- `simpleRuleCE` without `otherwise`. -/
def simpleRuleC (r : Rule) : Bool :=
  simpleRuleCE r && !ElseBwd.hasElse r

/-- Every pair `(i, j)` of `l` has `lhsRuleC` at `i` and `f` at `j` in `rules`. -/
def pairsOk (f : Rule → Bool) (rules : List Rule) (l : List (Nat × Nat)) : Bool :=
  l.all fun p => match rules[p.1]?, rules[p.2]? with
    | some ri, some rj => lhsRuleC ri && f rj
    | _, _ => false

/-- **The simple pairs for RM** (48 of the 68 pairs of `ElseBwd.ElseBwdDRest`): round 9's 45
simple pairs, `throw_ref-handler-next` against `return_call_ref-handler` `(21, 9)`, whose
quantifier `instr*` is `CODE`-free, and `array.init_data-zero`/`-num` against `-oob2`
(`(101, 100)`, `(102, 100)`), whose `Expand` premise concludes `CODE`-free values. -/
def simplePairsC : List (Nat × Nat) :=
  (21, 9) :: (101, 100) :: (102, 100) :: ElseBwd.simplePairs

/-- **The chain pairs for RM** (13): the earlier rule is an `otherwise` rule that passes
`simpleRuleCE`, and every rule `k` before it is, against `i`, outside `elsePairs`, in `adjPairs`
or a `FiresC.relRead` rule (which goes forward along erasure). Round 9's 12 chain pairs and
`array.init_data-num` against `array.init_data-zero` `(102, 101)`. -/
def chainPairsC : List (Nat × Nat) :=
  (102, 101) :: ElseBwd.chainPairs

/-- **Three `otherwise` rules whose pairs are all simple or with `throw_ref-instrs`**
(`table.copy-zero`, `memory.copy-zero`, `array.copy-zero`): they go forward along erasure once the
simple pairs are proved. -/
def fwdElse : List Nat := [32, 57, 90]

/-- **The chain pairs of the second level for RM** (3): `table.copy-gt`, `memory.copy-gt` and
`array.copy-gt` against `…-le`, whose earlier rules are, against `i`, outside `elsePairs`, in
`adjPairs`, in `FiresC.relRead` or in `fwdElse`. -/
def chain2PairsC : List (Nat × Nat) := [(34, 33), (59, 58), (92, 91)]

/-- **The pairs left for RM** (4): `br_on_cast(_fail)-fail`, `ref.test-false` and `ref.cast-fail`
against the rule before, which has a `Ref_ok` premise reading the store; these rules read the state
as `(s; f)`. -/
def leftPairsC : List (Nat × Nat) :=
  [(3, 2), (5, 4), (66, 65), (68, 67)]

/-- A pair of variables `(x, y)`. -/
def pairVars : Exp → Option (IL.Id × IL.Id)
  | .tupE [.varE x, .varE y] => some (x, y)
  | _ => none

/-- A rule whose conclusion is a pair of quantifiers of `CODE`-free type. -/
def concl2C : Rule → Bool
  | .ruleD _ qs _ e _ => match pairVars e with
    | some (x, y) => (ncNames qs).contains x && (ncNames qs).contains y
    | none => false

/-- **Every derivation of `x` concludes a `CODE`-free value**: `x` has no parameters and every
rule concludes a pair of `CODE`-free quantifiers. -/
def relNC (m : Map RelDef) (x : IL.Id) : Bool :=
  match m.find? x with
  | some (ps, _, _, rules) => ps.isEmpty && rules.all concl2C
  | none => false

/-- **The backward firing at the 4 pairs left** (RM). -/
def ElseBwdDLeftC (env : Env) : Prop :=
  ∀ p ∈ leftPairsC, ElseBwd.PairReflectD env Round8.CodeErase.Swap.eraseC "Step_read" [] [] p.1 p.2

/-! ## The pairs with `Ref_ok` -/

/-- A conclusion `(x, e₂, e₃)` whose first component is a variable. -/
def concl3 : Exp → Option (IL.Id × Exp × Exp)
  | .tupE [.varE x, a, b] => some (x, a, b)
  | _ => none

/-- The IL type `store`. -/
def isStoreT : Typ → Bool
  | .varT x [] => x == "store"
  | _ => false

/-- `z` is an expression quantifier of `qs`, and every quantifier named `z` has type `store`. -/
def storeQ (qs : List Param) (z : IL.Id) : Bool :=
  (Round7.Determ.quantNames qs).contains z && qs.all fun q => match q with
    | .expP x t => x != z || isStoreT t
    | _ => true

/-- **A premise that goes back when the store quantifier `z` is rebound**: an `if` reading only
quantifiers; a `Ref_ok` premise without arguments whose conclusion is `(z, …)` and reads only
quantifiers; or any relation premise that does not mention `z`. -/
def refPremOk (qs : List Param) (z : IL.Id) : Prem → Bool
  | .ifPr c => Round7.EraseDer.varsIn (Round7.Determ.quantNames qs) (freeExp c)
  | .rulePr x args _ c =>
    if x == "Ref_ok" then
      args.isEmpty && (match concl3 c with
        | some (y, _, _) => y == z
        | none => false) && Round7.EraseDer.varsIn (Round7.Determ.quantNames qs) (freeExp c)
    else decide (z ∉ (freeArgs args).varid) && decide (z ∉ (freeExp c).varid)
  | _ => false

/-- **A rule of `Ref_ok` that goes back along code erasure**: it concludes `(s, e₂, e₃)` with `s`
a store quantifier, its other quantifiers are `quantsNC`, its conclusion reads only quantifiers,
and its premises are `refPremOk`. -/
def refOkRule : Rule → Bool
  | .ruleD _ qs _ e prems => match concl3 e with
    | some (z, _, _) => storeQ qs z && quantsNC qs z && z != "_" &&
        Round7.EraseDer.varsIn (Round7.Determ.quantNames qs) (freeExp e) &&
        prems.all (refPremOk qs z)
    | none => false

/-- **`Ref_ok` has no parameters and every rule is `refOkRule`.** -/
def refOkOk (m : Map RelDef) : Bool :=
  match m.find? "Ref_ok" with
  | some (ps, _, _, rules) => ps.isEmpty && rules.all refOkRule
  | none => false

/-- A conclusion `((s; f); L, R)` whose state is a pair of variables: `(s, f)`. -/
def cfgSF : Exp → Option (IL.Id × IL.Id)
  | .tupE [.caseE op (.tupE [.caseE op' (.tupE [.varE s, .varE f]), _]), _] =>
    if op = "%;%" ∧ op' = "%;%" then some (s, f) else none
  | _ => none

/-- An `otherwise` rule whose conclusion is `((s; f); L, R)` with `s` a store quantifier. -/
def lhsSF : Rule → Bool
  | .ruleD _ qs _ e _ => match cfgSF e with
    | some (s, _) => storeQ qs s
    | none => false

/-- **An earlier rule read at `((s; f); L, R)`**: `s` a store quantifier, the other quantifiers
`quantsNC`, the conclusion reading only quantifiers, the premises `refPremOk`, no `otherwise`. -/
def sfRule : Rule → Bool
  | .ruleD _ qs _ e prems => match cfgSF e with
    | some (z, _) => storeQ qs z && quantsNC qs z && z != "_" &&
        Round7.EraseDer.varsIn (Round7.Determ.quantNames qs) (freeExp e) &&
        prems.all (refPremOk qs z)
    | none => false

/-- Every pair `(i, j)` of `l` has `lhsSF` at `i` and `sfRule` at `j`. -/
def sfPairsOk (rules : List Rule) (l : List (Nat × Nat)) : Bool :=
  l.all fun p => match rules[p.1]?, rules[p.2]? with
    | some ri, some rj => lhsSF ri && sfRule rj
    | _, _ => false

variable {H : Type}

/-- **`RMRead.OpenRMRestDPJ` with `firesRead` replaced by the backward firing at the 68 pairs of
`ElseBwd.ElseBwdDRest`.** -/
structure OpenRMRestDPK (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMRead.OpenRMRestDPJ.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.HostD.BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The backward firing along code erasure at the 68 pairs outside `ElseBwd.adjPairs`. -/
  elseBwd : ElseBwd.ElseBwdDRest (simEnv (Prims.builtins P hn host))
  /-- As `RMRead.OpenRMRestDPJ.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `RMRead.OpenRMRestDPJ.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → Round6.Target.CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

/-- **`OpenRMRestDPK` with `elseBwd` replaced by the backward firing at the 4 pairs of
`leftPairsC`.** -/
structure OpenRMRestDPL (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `OpenRMRestDPK.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.HostD.BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The backward firing along code erasure at the 4 pairs left. -/
  elseLeft : ElseBwdDLeftC (simEnv (Prims.builtins P hn host))
  /-- As `OpenRMRestDPK.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `OpenRMRestDPK.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → Round6.Target.CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

/-- **The fields of round 8's `OpenRMRestDPF` left after round 9**: `forward`, `castsFwd` and
`castsBwd` outside `EasyP`. No per-rule obligation is left (`RMElse.restMSHCJ_sim`). -/
structure OpenRMRestDPM (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `OpenRMRestDPL.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.HostD.BD P hn host)) (configVD hn c) (configVD hn d')
  /-- As `OpenRMRestDPL.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `OpenRMRestDPL.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → Round6.Target.CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Silmaril.Wasm.SpecTec.Sim.Round9.RMElse
