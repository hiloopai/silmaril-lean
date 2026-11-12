module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.RuntimeBridge.Instances
public import Silmaril.Wasm.SpecTec.Scripts.Defs
public import Silmaril.Wasm.SpecTec.Sim.VecEncoding.Defs

/-!
# SpecTec ↔ Core 3.0: definitions for the whole-step simulation

This header fixes the three things a simulation between SpecTec's `Step` and silmaril-lean's Core
3.0 `Step P host` needs, and states the goal. The design and the per-family work plan are in
`docs/projects/spectec/README.md`.

1. **A reading of the IL relations that can simulate anything** (`DDerives`). The existing
   denotation `Sem.Derives` is the evaluator's: a rule fires when *its first matching split* of the
   conclusion satisfies the premises. Under that reading `Step/ctxt-instrs` always takes the empty
   split, so no step happens under a non-empty value prefix, and 25 rules whose variables are bound
   only by `if` premises never fire (`Broken`). Neither can simulate Core. `DDerives` is the
   *declarative* reading SpecTec's inductive backends use: a rule fires on `v` when **some** typed
   assignment of its quantified variables makes the conclusion evaluate to `v` and every premise
   hold. Concatenation patterns are then split in every way, and an `if x = e` premise is a test of
   an assignment that is already total. Function calls are still the evaluator's (`EvalExp`), with
   the `hint(builtin)` primitives supplied by `Env.builtins`.
2. **`otherwise` premises** (`otherwise`): rule `i` with an `otherwise` premise fires only if no
   earlier rule of the same relation fires on the same left-hand side, the reading of SpecTec's
   `middlend/else.ml`. The earlier rules' own premise relations are read without `otherwise`
   (`noElse`); this is exact when they never reach an `otherwise` rule, which holds in the pinned
   script (only `Step_pure` and `Step_read` contain `otherwise`, and no premise of theirs reaches
   either).
3. **A total encoding of Core configurations** (`configV`): instructions (`instrToV`),
   administrative instructions (`adminToV`), values with SpecTec's float representation (`valV`),
   frames and stores (`frameV`, `storeV`). Types and module instances reuse
   `Equiv.RuntimeBridge.closedTypes`. Clauses marked *provisional* follow the schema of
   `Silmaril.Wasm.SpecTec.encodeInstruction` and are not yet checked against the IL type `instr`.

The script is `Scripts.Wasm30.fixed` (`baseEnv`). It differs from `Scripts.Wasm30.original` only in
the binary and text grammars and in `$cont`/`$utf8`; no reduction rule or helper used by them
changes, so every statement here holds for the original script as well.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## 1. The declarative reading of IL relations -/

/-- An interpretation of the IL's relations: `I x op args v` says that `v` is derivable by the
relation `x` (with mixfix operator `op`) at the arguments `args`. -/
abbrev Interp : Type := IL.Id → MixopS → List ArgV → Value → Prop

/-- An interpretation of `otherwise` premises: `O x args i v` says that rule `i` of relation `x`
may use its `otherwise` premise when its conclusion is `v`. -/
abbrev ElseI : Type := IL.Id → List ArgV → Nat → Value → Prop

/-- The domains of an iteration denote `xvs` under `ρ`. -/
def EvalDoms (env : Env) (ρ : VarEnv) (ds : List Dom) (xvs : List (IL.Id × Value)) : Prop :=
  ∃ n, evalDoms n env ρ ds = .ok xvs

/-- The domain values of an iteration, each read as a list. -/
def domLists (xvs : List (IL.Id × Value)) : Option (List (IL.Id × List Value)) :=
  xvs.mapM fun p => p.2.asList?.map fun l => (p.1, l)

/-- The domain values of an option iteration that are all present, as one row. -/
def domSomes (xvs : List (IL.Id × Value)) : Option (List (IL.Id × Value)) :=
  xvs.mapM fun p => match p.2 with
    | .opt (some w) => some (p.1, w)
    | _ => none

/-- A premise holds under the total assignment `ρ`, with relations read through `D` and
`otherwise` through `els`. Iterated premises follow `Sem.premIter` round by round. -/
inductive PremW (env : Env) (D : Interp) : Prop → VarEnv → Prem → Prop where
  | ifPr {els : Prop} {ρ : VarEnv} {e : Exp} :
      EvalExp env ρ e (.bool true) → PremW env D els ρ (.ifPr e)
  | elsePr {els : Prop} {ρ : VarEnv} : els → PremW env D els ρ .elsePr
  | letPr {els : Prop} {ρ : VarEnv} {e₁ e₂ : Exp} {w : Value} :
      EvalExp env ρ e₂ w → EvalExp env ρ e₁ w → PremW env D els ρ (.letPr e₁ e₂)
  | rulePr {els : Prop} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
      {avs : List ArgV} {w : Value} :
      EvalArgs env ρ args avs → EvalExp env ρ e w → D x op avs w →
      PremW env D els ρ (.rulePr x args op e)
  | iterOptNone {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → (∀ p ∈ xvs, p.2 = .opt none) →
      PremW env D els ρ (.iterPr pr (.mk .opt ds))
  | iterOptSome {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs row : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → domSomes xvs = some row →
      PremW env D els (ρ.bindVals row) pr → PremW env D els ρ (.iterPr pr (.mk .opt ds))
  | iterList {els : Prop} {ρ : VarEnv} {pr : Prem} {it : Iter} {ds : List Dom}
      {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)} {k : Nat} :
      (it = .list ∨ (it = .list1 ∧ 1 ≤ k)) →
      EvalDoms env ρ ds xvs → ds ≠ [] → domLists xvs = some dls →
      (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls none k, PremW env D els (ρ.bindVals r) pr) →
      PremW env D els ρ (.iterPr pr (.mk it ds))
  | iterListN {els : Prop} {ρ : VarEnv} {pr : Prem} {eₙ : Exp} {ido : Option IL.Id}
      {ds : List Dom} {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
      {kv : Value} {k : Nat} :
      EvalDoms env ρ ds xvs → EvalExp env ρ eₙ kv → kv.asNat? = some k →
      domLists xvs = some dls → (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls ido k, PremW env D els (ρ.bindVals r) pr) →
      PremW env D els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))

/-- Every expression quantifier of a rule has, under `ρ`, a value of its declared type. This is
what the evaluator reading drops (`Equiv/Execution.lean`, "the dropped quantifiers"), and what
keeps, for example, `label-vals` from firing on a label whose body is not a value sequence. -/
def QuantsOk (env : Env) (ρ : VarEnv) (qs : List Param) : Prop :=
  ∀ x t, Param.expP x t ∈ qs → ∃ w, ρ.findVal? x = some w ∧ HasTyp env ρ t w

mutual
/-- The declarative reading of the IL's relations: rule `i` of `x` derives `v` when an assignment
`σ` of its variables (on top of the relation's parameters) is well typed, evaluates the conclusion
to `v`, and satisfies every premise, with `otherwise` read through `O`. -/
inductive DDerives (env : Env) (O : ElseI) : IL.Id → MixopS → List ArgV → Value → Prop where
  | rule {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value} {ps : List Param} {t : Typ}
      {rules : List Rule} {i : Nat} {nm : IL.Id} {qs : List Param} {e : Exp} {prems : List Prem}
      {ρ₀ : VarEnv} {σ : List (IL.Id × Value)}
      (hrel : env.findRel? x = some (ps, op, t, rules))
      (hrule : rules[i]? = some (.ruleD nm qs op e prems))
      (hps : bindParams VarEnv.empty ps args = some ρ₀)
      (hq : QuantsOk env (ρ₀.bindVals σ) qs)
      (he : EvalExp env (ρ₀.bindVals σ) e v)
      (hp : ∀ pr ∈ prems, DPrem env O (O x args i v) (ρ₀.bindVals σ) pr) :
      DDerives env O x op args v

/-- `PremW` with relations read by `DDerives env O` itself: the premises of `DDerives`. -/
inductive DPrem (env : Env) (O : ElseI) : Prop → VarEnv → Prem → Prop where
  | ifPr {els : Prop} {ρ : VarEnv} {e : Exp} :
      EvalExp env ρ e (.bool true) → DPrem env O els ρ (.ifPr e)
  | elsePr {els : Prop} {ρ : VarEnv} : els → DPrem env O els ρ .elsePr
  | letPr {els : Prop} {ρ : VarEnv} {e₁ e₂ : Exp} {w : Value} :
      EvalExp env ρ e₂ w → EvalExp env ρ e₁ w → DPrem env O els ρ (.letPr e₁ e₂)
  | rulePr {els : Prop} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
      {avs : List ArgV} {w : Value} :
      EvalArgs env ρ args avs → EvalExp env ρ e w → DDerives env O x op avs w →
      DPrem env O els ρ (.rulePr x args op e)
  | iterOptNone {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → (∀ p ∈ xvs, p.2 = .opt none) →
      DPrem env O els ρ (.iterPr pr (.mk .opt ds))
  | iterOptSome {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs row : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → domSomes xvs = some row →
      DPrem env O els (ρ.bindVals row) pr → DPrem env O els ρ (.iterPr pr (.mk .opt ds))
  | iterList {els : Prop} {ρ : VarEnv} {pr : Prem} {it : Iter} {ds : List Dom}
      {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)} {k : Nat} :
      (it = .list ∨ (it = .list1 ∧ 1 ≤ k)) →
      EvalDoms env ρ ds xvs → ds ≠ [] → domLists xvs = some dls →
      (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls none k, DPrem env O els (ρ.bindVals r) pr) →
      DPrem env O els ρ (.iterPr pr (.mk it ds))
  | iterListN {els : Prop} {ρ : VarEnv} {pr : Prem} {eₙ : Exp} {ido : Option IL.Id}
      {ds : List Dom} {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
      {kv : Value} {k : Nat} :
      EvalDoms env ρ ds xvs → EvalExp env ρ eₙ kv → kv.asNat? = some k →
      domLists xvs = some dls → (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls ido k, DPrem env O els (ρ.bindVals r) pr) →
      DPrem env O els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))

end

/-- The body of a rule under an interpretation `D` of relations and a reading `els` of its
`otherwise` premise: the right-hand side of `DDerives.rule`, for one rule. -/
def RuleBody (env : Env) (D : Interp) (els : Prop) (ps : List Param) (args : List ArgV)
    (op : MixopS) (r : Rule) (v : Value) : Prop :=
  match r with
  | .ruleD _ qs op' e prems =>
      op' = op ∧ ∃ ρ₀ σ, bindParams VarEnv.empty ps args = some ρ₀ ∧
        QuantsOk env (ρ₀.bindVals σ) qs ∧ EvalExp env (ρ₀.bindVals σ) e v ∧
        ∀ pr ∈ prems, PremW env D els (ρ₀.bindVals σ) pr

/-- `otherwise` read as false: rules with an `otherwise` premise never fire. -/
def noElse : ElseI := fun _ _ _ _ => False

/-- Two pairs `(a, b)` and `(a, c)` with the same left-hand side. -/
def SameLhs (v w : Value) : Prop := ∃ a b c, v = .tuple [a, b] ∧ w = .tuple [a, c]

/-- The intended reading of `otherwise` (SpecTec's `middlend/else.ml`): rule `i` of `x` may use its
`otherwise` premise at `v` when no earlier rule `j < i` of `x` fires on the same left-hand side.
The earlier rule's own `otherwise` is read the same way, by recursion on `j`; its premise relations
are read by `DDerives env noElse`. -/
def otherwiseAt (env : Env) (x : IL.Id) (args : List ArgV) : Nat → Value → Prop
  | i, v => ∀ j, j < i → ∀ ps op t rules r, env.findRel? x = some (ps, op, t, rules) →
      rules[j]? = some r → ∀ w, SameLhs v w →
      ¬ RuleBody env (DDerives env noElse) (otherwiseAt env x args j w) ps args op r w
termination_by i => i

/-- `otherwiseAt`, as an `ElseI`. -/
def otherwise (env : Env) : ElseI := fun x args i v => otherwiseAt env x args i v

/-! ### The environment and the three reduction relations -/

/-- The fixed wasm-3.0 script as an environment, with no primitives interpreted. -/
noncomputable def baseEnv : Env := envOfScript Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed

/-- `baseEnv` with the primitives `B` (numerics, `$ND`, `$R_*`, `$hostcall`) installed. -/
noncomputable def simEnv (B : Builtins) : Env := baseEnv.withBuiltins B

/-- SpecTec's whole-machine step `Step: config ~> config`, read declaratively. -/
def SStep (env : Env) (c c' : Value) : Prop :=
  DDerives env (otherwise env) "Step" "%~>%" [] (.tuple [c, c'])

/-- `Step_pure: instr* ~> instr*`, read declaratively. -/
def SPure (env : Env) (is js : List Value) : Prop :=
  DDerives env (otherwise env) "Step_pure" "%~>%" [] (.tuple [.list is, .list js])

/-- `Step_read: config ~> instr*`, read declaratively. -/
def SRead (env : Env) (c : Value) (js : List Value) : Prop :=
  DDerives env (otherwise env) "Step_read" "%~>%" [] (.tuple [c, .list js])

/-- Rule `i` of the relation `x` (no parameters, operator `%~>%`) fires on `v`, read declaratively:
the unit of work of the per-rule lemmas. -/
def Fires (env : Env) (x : IL.Id) (i : Nat) (v : Value) : Prop :=
  ∃ t rules r, env.findRel? x = some ([], "%~>%", t, rules) ∧ rules[i]? = some r ∧
    RuleBody env (DDerives env (otherwise env)) (otherwise env x [] i v) [] [] "%~>%" r v

/-! ### Typing of the values the structural rules quantify over -/

/-- A scope that binds term variables only, as every rule instance `VarEnv.empty.bindVals σ`
does: no type, definition or grammar variable can shadow a global name. -/
def ValsOnly (ρ : VarEnv) : Prop := ρ.typs = [] ∧ ρ.defs = [] ∧ ρ.grams = []

/-- `v` has the IL type `t` in every scope that binds term variables only. The types the
structural rules quantify over (`state`, `instr*`, `val*`, …) are closed, so this is what the
generic lemmas assume. -/
def TypedV (env : Env) (t : Typ) (v : Value) : Prop := ∀ ρ : VarEnv, ValsOnly ρ → HasTyp env ρ t v

/-- The IL type `state`. -/
abbrev stateT : Typ := .varT "state" []
/-- The IL type `store`. -/
abbrev storeT : Typ := .varT "store" []
/-- The IL type `frame`. -/
abbrev frameT : Typ := .varT "frame" []
/-- The IL type `n`. -/
abbrev nT : Typ := .varT "n" []
/-- The IL type `instr*`. -/
abbrev instrsT : Typ := .iterT (.varT "instr" []) .list
/-- The IL type `val*`. -/
abbrev valsT : Typ := .iterT (.varT "val" []) .list
/-- The IL type `catch*`. -/
abbrev catchesT : Typ := .iterT (.varT "catch" []) .list

/-- `z; instr*`, the `config` injection (`Equiv.ExecStep.configV`). -/
abbrev cfgV (z : Value) (is : List Value) : Value := .case "%;%" (.tuple [z, .list is])

/-- `s; f`, the `state` injection. -/
abbrev stV (s f : Value) : Value := .case "%;%" (.tuple [s, f])

/-! ## 2. The encoding of Core configurations -/

section Encoding

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv (instrV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.RuntimeBridge

/-- The closed types of the runtime, as `Equiv.RuntimeBridge` encodes them. -/
abbrev CT : ClosedTypes := Silmaril.SpecTec.Equiv.RuntimeBridge.closedTypes

/-- `sx`. -/
def sxV : Signedness → Value
  | .unsigned => caseNilV "U"
  | .signed => caseNilV "S"

/-- `sz`, the `%`-wrapped width. -/
def szV (p : PackSize) : Value := pctV p.width

/-- `memarg = {ALIGN u32, OFFSET u64}`. -/
def memargV (a : MemArg) : Value :=
  .struct [("ALIGN", pctV a.align.val), ("OFFSET", pctV a.offset.val)]

/-- `fN(N)`: `POS`/`NEG` of `NORM m exp`, `SUBNORM m`, `INF` or `NAN m` (`1.1-syntax.values`),
from the IEEE bit pattern, following `Silmaril.Wasm.SpecTec.floatBits`. Every case but `POS`/`NEG`
carries a tuple (`fNmag`'s cases are `tupT`s, and the script builds them with `CaseE op (TupE …)`),
so `SUBNORM m` is `.case "SUBNORM" (.tuple [m])`, not `.case "SUBNORM" m`. -/
def floatV (t : FloatType) (bits : BitVec t.width) : Value :=
  let ew := Silmaril.Wasm.SpecTec.floatExponentWidth t
  let m := Silmaril.Wasm.SpecTec.floatFraction t bits
  let e := Silmaril.Wasm.SpecTec.floatExponent t bits
  let mag : Value :=
    if e = 0 then .case "SUBNORM" (.tuple [.num (.natN m)])
    else if e = 2 ^ ew - 1 then
      (if m = 0 then caseNilV "INF" else .case "NAN" (.tuple [.num (.natN m)]))
    else .case "NORM" (.tuple [.num (.natN m),
      .num (.intN ((e : Int) - ((2 ^ (ew - 1) - 1 : Nat) : Int)))])
  .case (if Silmaril.Wasm.SpecTec.floatSign t bits = 0 then "POS" else "NEG") mag

/-- A numeral of `num_(nt)`: `%`-wrapped for integers, `fN` for floats. -/
def numV : NumVal → Value
  | ⟨.int _, b⟩ => pctV b.toNat
  | ⟨.float t, b⟩ => floatV t b

/-- `val`: `CONST nt c`, `VCONST V128 c` or a reference. Unlike
`RuntimeBridge.valToValue`, a float is encoded as SpecTec's `fN`, not as its bit pattern. -/
def valV : Val → Value
  | .num n => .case "CONST" (.tuple [Encode.toValue n.type, numV n])
  | .vec b => .case "VCONST" (.tuple [caseNilV "V128", pctV b.toNat])
  | .ref r => refToValue r

/-- A schema value of `Silmaril.Wasm.SpecTec`, read as an IL value: `$list`, `$none`, `$some` and
`$record` are the list, option and record injections, and every other tag is a `case` with a
tuple payload. Used only for the provisional SIMD clauses of `instrToV`. -/
def schemaV : Silmaril.Formats.TExpr String Int → Value
  | .atom i => if 0 ≤ i then .num (.natN i.toNat) else .num (.intN i)
  | .tag "$list" n ch => .list (List.ofFn fun k : Fin n => schemaV (ch k))
  | .tag "$none" _ _ => .opt none
  | .tag "$some" (_ + 1) ch => .opt (some (schemaV (ch 0)))
  | .tag t n ch => .case t (.tuple (List.ofFn fun k : Fin n => schemaV (ch k)))

/-- A schema constructor as an `instr` case: one payload is carried bare, as in the IL's
single-field cases; several (or none) as a tuple. *Provisional.* -/
def schemaInstrV (c : Silmaril.Wasm.SpecTec.Constructor) : Value :=
  match c.arguments with
  | [a] => .case c.tag (schemaV a.value)
  | xs => .case c.tag (.tuple (xs.map fun a => schemaV a.value))

mutual
/-- A source instruction as an IL `instr`. Scalar numerics and the index-only instructions are
`Equiv.instrV` (checked against the §5.3 grammar); blocks, memory, table and aggregate
instructions are written out against the IL type `instr`; the non-memory SIMD instructions are
`Vec.vecInstrV?` (`Sim/VecEncoding/Defs.lean`); the memory SIMD instructions are still `schemaInstrV`
(*provisional*). -/
def instrToV : Instr → Value
  | .select (some ts) => .case "SELECT" (.opt (some (.list (ts.map Encode.toValue))))
  | .block bt body => .case "BLOCK" (.tuple [Encode.toValue bt, .list (instrsToV body)])
  | .loop bt body => .case "LOOP" (.tuple [Encode.toValue bt, .list (instrsToV body)])
  | .if_ bt b₁ b₂ =>
      .case "IF%%ELSE%" (.tuple [Encode.toValue bt, .list (instrsToV b₁), .list (instrsToV b₂)])
  | .brTable ls l => .case "BR_TABLE" (.tuple [.list (ls.map Encode.toValue), Encode.toValue l])
  | .brOnCast l s t =>
      .case "BR_ON_CAST" (.tuple [Encode.toValue l, Encode.toValue s, Encode.toValue t])
  | .brOnCastFail l s t =>
      .case "BR_ON_CAST_FAIL" (.tuple [Encode.toValue l, Encode.toValue s, Encode.toValue t])
  | .callIndirect x y =>
      .case "CALL_INDIRECT" (.tuple [Encode.toValue x, .case "_IDX" (Encode.toValue y)])
  | .returnCallIndirect x y =>
      .case "RETURN_CALL_INDIRECT" (.tuple [Encode.toValue x, .case "_IDX" (Encode.toValue y)])
  | .tryTable bt cs body =>
      .case "TRY_TABLE" (.tuple [Encode.toValue bt,
        .case "%" (.tuple [.list (cs.map Encode.toValue)]),
        .list (instrsToV body)])
  | .tableSize x => .case "TABLE.SIZE" (Encode.toValue x)
  | .tableGrow x => .case "TABLE.GROW" (Encode.toValue x)
  | .tableFill x => .case "TABLE.FILL" (Encode.toValue x)
  | .tableCopy x y => .case "TABLE.COPY" (.tuple [Encode.toValue x, Encode.toValue y])
  | .tableInit x y => .case "TABLE.INIT" (.tuple [Encode.toValue x, Encode.toValue y])
  | .elemDrop x => .case "ELEM.DROP" (Encode.toValue x)
  | .intLoad t p m a => .case "LOAD" (.tuple [Encode.toValue (NumType.int t),
      .opt (p.map fun q => .case "%_%" (.tuple [szV q.1, sxV q.2])), Encode.toValue m, memargV a])
  | .floatLoad t m a =>
      .case "LOAD" (.tuple [Encode.toValue (NumType.float t), .opt none, Encode.toValue m,
        memargV a])
  | .intStore t p m a => .case "STORE" (.tuple [Encode.toValue (NumType.int t),
      .opt (p.map fun q => .case "%" (.tuple [szV q])), Encode.toValue m, memargV a])
  | .floatStore t m a =>
      .case "STORE" (.tuple [Encode.toValue (NumType.float t), .opt none, Encode.toValue m,
        memargV a])
  | .memoryFill x => .case "MEMORY.FILL" (Encode.toValue x)
  | .memoryCopy x y => .case "MEMORY.COPY" (.tuple [Encode.toValue x, Encode.toValue y])
  | .memoryInit x y => .case "MEMORY.INIT" (.tuple [Encode.toValue x, Encode.toValue y])
  | .dataDrop x => .case "DATA.DROP" (Encode.toValue x)
  | .refTest t => .case "REF.TEST" (Encode.toValue t)
  | .refCast t => .case "REF.CAST" (Encode.toValue t)
  | .refI31 => caseNilV "REF.I31"
  | .i31Get s => .case "I31.GET" (sxV s)
  | .structNew x => .case "STRUCT.NEW" (Encode.toValue x)
  | .structNewDefault x => .case "STRUCT.NEW_DEFAULT" (Encode.toValue x)
  | .structGet s x f =>
      .case "STRUCT.GET" (.tuple [.opt (s.map sxV), Encode.toValue x, Encode.toValue f])
  | .structSet x f => .case "STRUCT.SET" (.tuple [Encode.toValue x, Encode.toValue f])
  | .arrayNew x => .case "ARRAY.NEW" (Encode.toValue x)
  | .arrayNewDefault x => .case "ARRAY.NEW_DEFAULT" (Encode.toValue x)
  | .arrayNewFixed x n => .case "ARRAY.NEW_FIXED" (.tuple [Encode.toValue x, pctV n.val])
  | .arrayNewData x y => .case "ARRAY.NEW_DATA" (.tuple [Encode.toValue x, Encode.toValue y])
  | .arrayNewElem x y => .case "ARRAY.NEW_ELEM" (.tuple [Encode.toValue x, Encode.toValue y])
  | .arrayGet s x => .case "ARRAY.GET" (.tuple [.opt (s.map sxV), Encode.toValue x])
  | .arraySet x => .case "ARRAY.SET" (Encode.toValue x)
  | .arrayLen => caseNilV "ARRAY.LEN"
  | .arrayFill x => .case "ARRAY.FILL" (Encode.toValue x)
  | .arrayCopy x y => .case "ARRAY.COPY" (.tuple [Encode.toValue x, Encode.toValue y])
  | .arrayInitData x y => .case "ARRAY.INIT_DATA" (.tuple [Encode.toValue x, Encode.toValue y])
  | .arrayInitElem x y => .case "ARRAY.INIT_ELEM" (.tuple [Encode.toValue x, Encode.toValue y])
  | .externConvertAny => caseNilV "EXTERN.CONVERT_ANY"
  | .anyConvertExtern => caseNilV "ANY.CONVERT_EXTERN"
  | .intConst t b => valV (.num ⟨.int t, b⟩)
  | .floatConst t b => valV (.num ⟨.float t, b⟩)
  | .vecConst b => valV (.vec b)
  | i@(.vecLoad ..) | i@(.vecLoadLane ..) | i@(.vecStore ..) | i@(.vecStoreLane ..) =>
      schemaInstrV (Silmaril.Wasm.SpecTec.encodeInstruction i)
  | i@(.vecUnOp _) | i@(.vecBinOp _) | i@(.vecTernOp _) | i@(.vecTestOp _)
  | i@(.vecIntUnOp ..) | i@(.vecFloatUnOp ..) | i@(.vecIntBinOp ..) | i@(.vecFloatBinOp ..)
  | i@(.vecIntTernOp ..) | i@(.vecFloatTernOp ..) | i@(.vecAllTrue _) | i@(.vecIntRelOp ..)
  | i@(.vecFloatRelOp ..) | i@(.vecShiftOp ..) | i@(.vecBitmask _) | i@(.vecSwizzle _)
  | i@(.vecShuffle _) | i@(.vecExtUnOp ..) | i@(.vecExtBinOp ..) | i@(.vecExtTernOp ..)
  | i@(.vecNarrow ..) | i@(.vecConvert ..) | i@(.vecSplat _) | i@(.vecExtractLane ..)
  | i@(.vecReplaceLane ..) =>
      (Vec.vecInstrV? i).getD (schemaInstrV (Silmaril.Wasm.SpecTec.encodeInstruction i))
  | .convert op => Vec.convertInstrV op
  | i => instrV i

/-- `instrToV` on a sequence. -/
def instrsToV : List Instr → List Value
  | [] => []
  | i :: is => instrToV i :: instrsToV is
end

/-- A field value: a `val`, or `PACK pt c`. -/
def fieldValV : FieldVal → Value
  | .val v => valV v
  | .pack p b => .case "PACK" (.tuple [Encode.toValue p, pctV b.toNat])

/-- `frame = {LOCALS (val?)*, MODULE moduleinst}`. -/
def frameV (f : Frame) : Value :=
  .struct [("LOCALS", .list (f.locals.map fun o => .opt (o.map valV))),
    ("MODULE", moduleInstToValue CT f.module)]

mutual
/-- An administrative instruction as an IL `instr`. -/
def adminToV : Admin → Value
  | .plain i => instrToV i
  | .ref r => refToValue r
  | .callRefType d => .case "CALL_REF" (CT.defType d)
  | .returnCallRefType d => .case "RETURN_CALL_REF" (CT.defType d)
  | .label n cont body =>
      .case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont), .list (adminsToV body)])
  | .handler n cs body =>
      .case "HANDLER_%{%}%" (.tuple [.num (.natN n), .list (cs.map Encode.toValue),
        .list (adminsToV body)])
  | .frame n f body =>
      .case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV f, .list (adminsToV body)])
  | .trap => caseNilV "TRAP"

/-- `adminToV` on a sequence. -/
def adminsToV : List Admin → List Value
  | [] => []
  | a :: rest => adminToV a :: adminsToV rest
end

/-- `globalinst = {TYPE globaltype, VALUE val}`. -/
def globalInstV (g : GlobalInst) : Value :=
  .struct [("TYPE", CT.globalType g.type), ("VALUE", valV g.value)]

/-- `structinst = {TYPE deftype, FIELDS fieldval*}`. -/
def structInstV (s : StructInst) : Value :=
  .struct [("TYPE", CT.defType s.type), ("FIELDS", .list (s.fields.map fieldValV))]

/-- `arrayinst = {TYPE deftype, FIELDS fieldval*}`. -/
def arrayInstV (a : ArrayInst) : Value :=
  .struct [("TYPE", CT.defType a.type), ("FIELDS", .list (a.fields.map fieldValV))]

/-- `exninst = {TAG tagaddr, FIELDS val*}`. -/
def exnInstV (e : ExnInst) : Value :=
  .struct [("TAG", .num (.natN e.tag)), ("FIELDS", .list (e.fields.map valV))]

variable {H : Type}

/-- `funcinst = {TYPE deftype, MODULE moduleinst, CODE funccode}`, with the body encoded by
`instrsToV`; a host function is `_HOSTFUNC (hn h)`. A declared local is `LOCAL t`
(`funccode = FUNC typeidx local* expr`, `local = LOCAL valtype`): `call_ref-func` matches the
code against `FUNC x (LOCAL t)* instr*`. -/
def funcInstV (hn : H → String) (f : FuncInst H) : Value :=
  .struct [("TYPE", CT.defType f.type), ("MODULE", moduleInstToValue CT f.module),
    ("CODE", match f.code with
      | .wasm fn => .case "FUNC" (.tuple [pctV fn.type.toNat,
          .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
          .list (instrsToV fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h)))]

/-- `store`, ten fields in the order of `1.4-runtime.spectec`. -/
def storeV (hn : H → String) (s : Store H) : Value :=
  .struct
    [("TAGS", .list (s.tags.map (tagInstToValue CT))),
     ("GLOBALS", .list (s.globals.map globalInstV)),
     ("MEMS", .list (s.mems.map memInstToValue)),
     ("TABLES", .list (s.tables.map (tableInstToValue CT))),
     ("FUNCS", .list (s.funcs.map (funcInstV hn))),
     ("DATAS", .list (s.datas.map dataInstToValue)),
     ("ELEMS", .list (s.elems.map (elemInstToValue CT))),
     ("STRUCTS", .list (s.structs.map structInstV)),
     ("ARRAYS", .list (s.arrays.map arrayInstV)),
     ("EXNS", .list (s.exns.map exnInstV))]

/-- `state = store; frame`. -/
def stateV (hn : H → String) (s : Store H) (f : Frame) : Value :=
  .case "%;%" (.tuple [storeV hn s, frameV f])

/-- `config = state; instr*`. -/
def configV (hn : H → String) (c : Config H) : Value :=
  .case "%;%" (.tuple [stateV hn c.store c.frame, .list (adminsToV c.code)])

/-- The configuration relation: `v` is the SpecTec image of `c`. The encoding is a function, so
the relation is its graph. -/
def ConfigRel (hn : H → String) (c : Config H) (v : Value) : Prop := v = configV hn c

end Encoding

/-! ## 3. The goal -/

section Goal

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation

/-- A host whose every call has finitely many outcomes, listed: what `$hostcall`, a function into
a list of outcomes, can represent. -/
def HostFinite {H : Type} (host : HostSemantics H) : Prop :=
  ∀ h s vs, ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
    ∀ o, host h s vs o ↔ o ∈ os

/-- `c`'s image is a value of SpecTec's type `config`. The simulation is stated for such
configurations: the declarative reading types every quantified variable, so a configuration holding
an instruction outside the IL type `instr` (for example one with invalid immediates, which
`instrToV` sends to junk) cannot take a SpecTec step at all. -/
def Typed (env : Env) {H : Type} (hn : H → String) (c : Config H) : Prop :=
  HasTyp env VarEnv.empty (.varT "config" []) (configV hn c)

/-! ### The interface between the generic part and the per-rule families -/

variable {H : Type}

/-- The forward goal for one Core step: between typed configurations, the images are related by
SpecTec's `Step`. -/
def FwdP (env : Env) (hn : H → String) (c c' : Config H) : Prop :=
  Typed env hn c → Typed env hn c' → SStep env (configV hn c) (configV hn c')

/-- What the generic forward proof needs to know about the typing of encoded configurations.
Family E (encoding) proves it for `simEnv B`. -/
structure TypingFacts (env : Env) (hn : H → String) : Prop where
  /-- A typed configuration has a typed state and typed code. -/
  config : ∀ c : Config H, Typed env hn c ↔
    TypedV env stateT (stateV hn c.store c.frame) ∧ TypedV env instrsT (.list (adminsToV c.code))
  /-- A state is typed when its store and frame are. -/
  state : ∀ (s : Store H) (f : Frame), TypedV env stateT (stateV hn s f) ↔
    TypedV env storeT (storeV hn s) ∧ TypedV env frameT (frameV f)
  /-- `instr*` is typed elementwise. -/
  append : ∀ a b : List Value, TypedV env instrsT (.list (a ++ b)) ↔
    TypedV env instrsT (.list a) ∧ TypedV env instrsT (.list b)
  /-- A value sequence typed as `instr*` is typed as `val*`. -/
  vals : ∀ vs : List Val, TypedV env instrsT (.list (adminsToV (vals vs))) →
    TypedV env valsT (.list (adminsToV (vals vs)))
  /-- The components of a typed label. -/
  label : ∀ (n : Nat) (cont : List Instr) (body : List Admin),
    TypedV env instrsT (.list [adminToV (.label n cont body)]) →
    TypedV env nT (.num (.natN n)) ∧ TypedV env instrsT (.list (instrsToV cont)) ∧
      TypedV env instrsT (.list (adminsToV body))
  /-- The components of a typed handler. -/
  handler : ∀ (n : Nat) (cs : List Catch) (body : List Admin),
    TypedV env instrsT (.list [adminToV (.handler n cs body)]) →
    TypedV env nT (.num (.natN n)) ∧ TypedV env catchesT (.list (cs.map Encode.toValue)) ∧
      TypedV env instrsT (.list (adminsToV body))
  /-- The components of a typed frame. -/
  frame : ∀ (n : Nat) (f : Frame) (body : List Admin),
    TypedV env instrsT (.list [adminToV (.frame n f body)]) →
    TypedV env nT (.num (.natN n)) ∧ TypedV env frameT (frameV f) ∧
      TypedV env instrsT (.list (adminsToV body))

/-- **The families' forward obligations**, one field per constructor of Core's `Step` other than
the four context rules (which `forward` handles generically). Each field is the constructor's own
premises, concluding `FwdP` of its two configurations; the binders are copied verbatim from
`Silmaril/Wasm/Execution/Core/Step.lean`, so that `Step.rec` takes the fields as they are. The
assignment of fields to families is in `docs/projects/spectec/README.md`. -/
structure Forward (env : Env) (hname : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  /-- `Step.parametric`. -/
  parametric : ∀ {s : Store H} {f : Frame} {is is' : List Admin} (_ : ParametricStep is is'),
    FwdP env hname ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step.numeric`. -/
  numeric : ∀ {s : Store H} {f : Frame} {is is' : List Admin} (_ : NumericStep P is is'),
    FwdP env hname ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step.vector`. -/
  vector : ∀ {s : Store H} {f : Frame} {is is' : List Admin} (_ : VectorStep P is is'),
    FwdP env hname ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step.variable`. -/
  variable_ : ∀ {c c' : Config H} (_ : VariableStep c c'),
    FwdP env hname c c'
  /-- `Step.table`. -/
  table : ∀ {c c' : Config H} (_ : TableStep P c c'),
    FwdP env hname c c'
  /-- `Step.memory`. -/
  memory : ∀ {c c' : Config H} (_ : MemoryStep P c c'),
    FwdP env hname c c'
  /-- `Step.reference`. -/
  reference : ∀ {c c' : Config H} (_ : RefStep c c'),
    FwdP env hname c c'
  /-- `Step.aggregate`. -/
  aggregate : ∀ {c c' : Config H} (_ : AggregateStep c c'),
    FwdP env hname c c'
  /-- `Step.block`. -/
  block : ∀ {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List CValType} (_ : f.module.blockType? bt = some (t₁, t₂))
      (_ : vs.length = t₁.length),
    FwdP env hname ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩
  /-- `Step.loop`. -/
  loop : ∀ {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List CValType} (_ : f.module.blockType? bt = some (t₁, t₂))
      (_ : vs.length = t₁.length),
    FwdP env hname ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩
  /-- `Step.ifTrue`. -/
  ifTrue : ∀ {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr}
      (_ : c ≠ 0),
    FwdP env hname ⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩ ⟨s, f, [.plain (.block bt b₁)]⟩
  /-- `Step.ifFalse`. -/
  ifFalse : ∀ {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr},
    FwdP env hname ⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩ ⟨s, f, [.plain (.block bt b₂)]⟩
  /-- `Step.labelVals`. -/
  labelVals : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val},
    FwdP env hname ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩
  /-- `Step.brLabelZero`. -/
  brLabelZero : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs' vs : List Val}
      {l : LabelIdx} {rest : List Admin} (_ : l.toNat = 0) (_ : vs.length = n),
    FwdP env hname ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ expression cont⟩
  /-- `Step.brLabelSucc`. -/
  brLabelSucc : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
      {l : LabelIdx} {rest : List Admin} (_ : 0 < l.toNat),
    FwdP env hname ⟨s, f, [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩
  /-- `Step.brHandler`. -/
  brHandler : ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
      {l : LabelIdx} {rest : List Admin},
    FwdP env hname ⟨s, f, [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br l)]⟩
  /-- `Step.brIfTrue`. -/
  brIfTrue : ∀ {s : Store H} {f : Frame} {c : BitVec 32} {l : LabelIdx} (_ : c ≠ 0),
    FwdP env hname ⟨s, f, [constI32 c, .plain (.brIf l)]⟩ ⟨s, f, [.plain (.br l)]⟩
  /-- `Step.brIfFalse`. -/
  brIfFalse : ∀ {s : Store H} {f : Frame} {l : LabelIdx},
    FwdP env hname ⟨s, f, [constI32 0, .plain (.brIf l)]⟩ ⟨s, f, []⟩
  /-- `Step.brTableLt`. -/
  brTableLt : ∀ {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx}
      (_ : ls[i.toNat]? = some l),
    FwdP env hname ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩ ⟨s, f, [.plain (.br l)]⟩
  /-- `Step.brTableGe`. -/
  brTableGe : ∀ {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
      (_ : ls.length ≤ i.toNat),
    FwdP env hname ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩ ⟨s, f, [.plain (.br l')]⟩
  /-- `Step.brOnNullNull`. -/
  brOnNullNull : ∀ {s : Store H} {f : Frame} {l : LabelIdx},
    FwdP env hname ⟨s, f, [.ref .null, .plain (.brOnNull l)]⟩ ⟨s, f, [.plain (.br l)]⟩
  /-- `Step.brOnNullAddr`. -/
  brOnNullAddr : ∀ {s : Store H} {f : Frame} {v : Val} {l : LabelIdx} (_ : v ≠ .ref .null),
    FwdP env hname ⟨s, f, [v.toAdmin, .plain (.brOnNull l)]⟩ ⟨s, f, [v.toAdmin]⟩
  /-- `Step.brOnNonNullNull`. -/
  brOnNonNullNull : ∀ {s : Store H} {f : Frame} {l : LabelIdx},
    FwdP env hname ⟨s, f, [.ref .null, .plain (.brOnNonNull l)]⟩ ⟨s, f, []⟩
  /-- `Step.brOnNonNullAddr`. -/
  brOnNonNullAddr : ∀ {s : Store H} {f : Frame} {v : Val} {l : LabelIdx} (_ : v ≠ .ref .null),
    FwdP env hname ⟨s, f, [v.toAdmin, .plain (.brOnNonNull l)]⟩ ⟨s, f, [v.toAdmin, .plain (.br l)]⟩
  /-- `Step.brOnCastSucceed`. -/
  brOnCastSucceed : ∀ {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (_ : RefOk s r (f.module.instRef rt₂)),
    FwdP env hname ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r, .plain (.br l)]⟩
  /-- `Step.brOnCastFail`. -/
  brOnCastFail : ∀ {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (_ : ¬ RefOk s r (f.module.instRef rt₂)),
    FwdP env hname ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩
  /-- `Step.brOnCastFailSucceed`. -/
  brOnCastFailSucceed : ∀ {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (_ : RefOk s r (f.module.instRef rt₂)),
    FwdP env hname ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩
  /-- `Step.brOnCastFailFail`. -/
  brOnCastFailFail : ∀ {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (_ : ¬ RefOk s r (f.module.instRef rt₂)),
    FwdP env hname ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
      ⟨s, f, [.ref r, .plain (.br l)]⟩
  /-- `Step.call`. -/
  call : ∀ {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (_ : f.module.funcs[x.toNat]? = some a) (_ : s.funcs[a]? = some fi),
    FwdP env hname ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩
  /-- `Step.callRefNull`. -/
  callRefNull : ∀ {s : Store H} {f : Frame} {c : Admin} (_ : c.IsCallRef),
    FwdP env hname ⟨s, f, [.ref .null, c]⟩ ⟨s, f, [.trap]⟩
  /-- `Step.callRefFunc`. -/
  callRefFunc : ∀ {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
      {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func} (_ : c.IsCallRef)
      (_ : s.funcs[a]? = some fi) (_ : Expand fi.type (.func ps rs)) (_ : vs.length = ps.length)
      (_ : fi.code = .wasm code),
    FwdP env hname ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩
  /-- `Step.callRefHost`. -/
  callRefHost : ∀ {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
      {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {r : Result} (_ : c.IsCallRef)
      (_ : s.funcs[a]? = some fi) (_ : Expand fi.type (.func ps rs)) (_ : vs.length = ps.length)
      (_ : fi.code = .host h) (_ : host h s vs (.returned s' r)),
    FwdP env hname ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩
  /-- `Step.callRefHostDiv`. -/
  callRefHostDiv : ∀ {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
      {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} (_ : c.IsCallRef)
      (_ : s.funcs[a]? = some fi) (_ : Expand fi.type (.func ps rs)) (_ : vs.length = ps.length)
      (_ : fi.code = .host h) (_ : host h s vs .diverged),
    FwdP env hname ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
  /-- `Step.returnCall`. -/
  returnCall : ∀ {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (_ : f.module.funcs[x.toNat]? = some a) (_ : s.funcs[a]? = some fi),
    FwdP env hname ⟨s, f, [.plain (.returnCall x)]⟩
      ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩
  /-- `Step.returnCallRefLabel`. -/
  returnCallRefLabel : ∀ {s : Store H} {f : Frame} {k : Nat} {cont : List Instr} {vs : List Val}
      {c : Admin} {rest : List Admin} (_ : c.IsReturnCallRef),
    FwdP env hname ⟨s, f, [.label k cont (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩
  /-- `Step.returnCallRefHandler`. -/
  returnCallRefHandler : ∀ {s : Store H} {f : Frame} {k : Nat} {cs : List Catch} {vs : List Val}
      {c : Admin} {rest : List Admin} (_ : c.IsReturnCallRef),
    FwdP env hname ⟨s, f, [.handler k cs (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩
  /-- `Step.returnCallRefFrameNull`. -/
  returnCallRefFrameNull : ∀ {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val} {c : Admin}
      {rest : List Admin} (_ : c.IsReturnCallRef),
    FwdP env hname ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step.returnCallRefFrameAddr`. -/
  returnCallRefFrameAddr : ∀ {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
      {c : Admin} {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
      (_ : c.IsReturnCallRef) (_ : s.funcs[a]? = some fn) (_ : Expand fn.type (.func ps rs))
      (_ : vs.length = ps.length),
    FwdP env hname ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩
  /-- `Step.callIndirect`. -/
  callIndirect : ∀ {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx},
    FwdP env hname ⟨s, f, [.plain (.callIndirect x y)]⟩
      ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.callRef y)]⟩
  /-- `Step.returnCallIndirect`. -/
  returnCallIndirect : ∀ {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx},
    FwdP env hname ⟨s, f, [.plain (.returnCallIndirect x y)]⟩
      ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
        .plain (.returnCallRef y)]⟩
  /-- `Step.frameVals`. -/
  frameVals : ∀ {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val} (_ : vs.length = n),
    FwdP env hname ⟨s, f, [.frame n fi (vals vs)]⟩ ⟨s, f, vals vs⟩
  /-- `Step.returnFrame`. -/
  returnFrame : ∀ {s : Store H} {f fi : Frame} {n : Nat} {vs' vs : List Val} {rest : List Admin}
      (_ : vs.length = n),
    FwdP env hname ⟨s, f, [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs⟩
  /-- `Step.returnLabel`. -/
  returnLabel : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
      {rest : List Admin},
    FwdP env hname ⟨s, f, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩
  /-- `Step.returnHandler`. -/
  returnHandler : ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
      {rest : List Admin},
    FwdP env hname ⟨s, f, [.handler n cs (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩
  /-- `Step.throw`. -/
  throw : ∀ {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat} {ti : TagInst}
      {ts : Ty (.list .val)} (_ : s.tag? f x = some (ta, ti)) (_ : Expand ti.type (.func ts .nil))
      (_ : vs.length = ts.length),
    FwdP env hname ⟨s, f, vals vs ++ [.plain (.throw x)]⟩
      ⟨s.addExn ⟨ta, vs⟩, f, throwing s.exns.length⟩
  /-- `Step.throwRefNull`. -/
  throwRefNull : ∀ {s : Store H} {f : Frame},
    FwdP env hname ⟨s, f, [.ref .null, .plain .throwRef]⟩ ⟨s, f, [.trap]⟩
  /-- `Step.throwRefInstrs`. -/
  throwRefInstrs : ∀ {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {rest : List Admin}
      (_ : vs ≠ [] ∨ rest ≠ []),
    FwdP env hname ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩
  /-- `Step.throwRefLabel`. -/
  throwRefLabel : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat},
    FwdP env hname ⟨s, f, [.label n cont (throwing a)]⟩ ⟨s, f, throwing a⟩
  /-- `Step.throwRefFrame`. -/
  throwRefFrame : ∀ {s : Store H} {f fi : Frame} {n : Nat} {a : Nat},
    FwdP env hname ⟨s, f, [.frame n fi (throwing a)]⟩ ⟨s, f, throwing a⟩
  /-- `Step.throwRefHandlerEmpty`. -/
  throwRefHandlerEmpty : ∀ {s : Store H} {f : Frame} {n : Nat} {a : Nat},
    FwdP env hname ⟨s, f, [.handler n [] (throwing a)]⟩ ⟨s, f, throwing a⟩
  /-- `Step.throwRefHandlerCatch`. -/
  throwRefHandlerCatch : ∀ {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst} (_ : s.exns[a]? = some e)
      (_ : f.module.tags[x.toNat]? = some e.tag),
    FwdP env hname ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩
      ⟨s, f, vals e.fields ++ [.plain (.br l)]⟩
  /-- `Step.throwRefHandlerCatchRef`. -/
  throwRefHandlerCatchRef : ∀ {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst} (_ : s.exns[a]? = some e)
      (_ : f.module.tags[x.toNat]? = some e.tag),
    FwdP env hname ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
      ⟨s, f, vals e.fields ++ [.ref (.exn a), .plain (.br l)]⟩
  /-- `Step.throwRefHandlerCatchAll`. -/
  throwRefHandlerCatchAll : ∀ {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch}
      {a : Nat},
    FwdP env hname ⟨s, f, [.handler n (.catchAll l :: cs) (throwing a)]⟩ ⟨s, f, [.plain (.br l)]⟩
  /-- `Step.throwRefHandlerCatchAllRef`. -/
  throwRefHandlerCatchAllRef : ∀ {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx}
      {cs : List Catch} {a : Nat},
    FwdP env hname ⟨s, f, [.handler n (.catchAllRef l :: cs) (throwing a)]⟩
      ⟨s, f, [.ref (.exn a), .plain (.br l)]⟩
  /-- `Step.throwRefHandlerNext`. -/
  throwRefHandlerNext : ∀ {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch}
      {a : Nat} (_ : ¬ CatchMatches s f a c),
    FwdP env hname ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ ⟨s, f, [.handler n cs (throwing a)]⟩
  /-- `Step.tryTable`. -/
  tryTable : ∀ {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
      {vs : List Val} {t₁ t₂ : List CValType} (_ : f.module.blockType? bt = some (t₁, t₂))
      (_ : vs.length = t₁.length),
    FwdP env hname ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
      ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩
  /-- `Step.handlerVals`. -/
  handlerVals : ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val},
    FwdP env hname ⟨s, f, [.handler n cs (vals vs)]⟩ ⟨s, f, vals vs⟩
  /-- `Step.trapInstrs`. -/
  trapInstrs : ∀ {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
      (_ : vs ≠ [] ∨ rest ≠ []),
    FwdP env hname ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩
  /-- `Step.trapLabel`. -/
  trapLabel : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr},
    FwdP env hname ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩
  /-- `Step.trapHandler`. -/
  trapHandler : ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch},
    FwdP env hname ⟨s, f, [.handler n cs [.trap]]⟩ ⟨s, f, [.trap]⟩
  /-- `Step.trapFrame`. -/
  trapFrame : ∀ {s : Store H} {f fi : Frame} {n : Nat},
    FwdP env hname ⟨s, f, [.frame n fi [.trap]]⟩ ⟨s, f, [.trap]⟩

/-- The backward goal for one SpecTec step from the image of `c`: it lands on the image of a Core
successor of `c`. -/
def BwdP (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H)
    (w : Value) : Prop :=
  ∃ c', w = configV hn c' ∧ Step P host c c'

/-- **The families' backward obligations**, one per rule: whatever a `Step_pure`, `Step_read` or
store-changing `Step` rule (index `≥ 6`) derives from the image of a typed configuration is the
image of a Core step. Rules `0`–`5` of `Step` (`pure`, `read`, the four contexts) are the generic
part (`docs/projects/spectec/README.md`, track S). -/
structure Backward (env : Env) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  /-- `Step_pure`, rule by rule. -/
  pure : ∀ (i : Nat) (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Typed env hn ⟨s, f, is⟩ → Fires env "Step_pure" i (.tuple [.list (adminsToV is), w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `Step_read`, rule by rule. -/
  read : ∀ (i : Nat) (c : Config H) (w : Value),
    Typed env hn c → Fires env "Step_read" i (.tuple [configV hn c, w]) →
    ∃ is', w = .list (adminsToV is') ∧ Step P host c ⟨c.store, c.frame, is'⟩
  /-- The store-changing rules of `Step`, rule by rule. -/
  step : ∀ (i : Nat), 6 ≤ i → ∀ (c : Config H) (w : Value),
    Typed env hn c → Fires env "Step" i (.tuple [configV hn c, w]) → BwdP hn P host c w

/-- **The whole-step simulation, as a frozen goal.** For the spec profile with builtins `nd` and
`r`, and a finitely branching host named injectively by `hn`, there is an interpretation `B` of
SpecTec's primitives under which every Core step between typed configurations is a SpecTec step of
the images, and every SpecTec step from the image of a typed configuration is the image of a Core
step. The assembly (see `docs/projects/spectec/README.md`) exhibits `B` and proves separately that it
agrees with silmaril-lean's numerics and host. -/
def Task.wholeStep : Prop :=
  ∀ (H : Type) (hn : H → String), Function.Injective hn →
    ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
      ∃ B : Builtins,
        (∀ c c' : Config H, Typed (simEnv B) hn c → Typed (simEnv B) hn c' →
          Step (Profile.spec nd r) host c c' →
          SStep (simEnv B) (configV hn c) (configV hn c')) ∧
        (∀ (c : Config H) (w : Value), Typed (simEnv B) hn c →
          SStep (simEnv B) (configV hn c) w →
          ∃ c', w = configV hn c' ∧ Step (Profile.spec nd r) host c c')

end Goal

end Silmaril.Wasm.SpecTec.Sim
