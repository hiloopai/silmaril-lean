module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.ElseAgreeMove
public import Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.Thms

/-!
# Three ways an earlier rule reads back from `simEnv20T` to `simEnv20S`

`PairBack (simEnv20S B) (simEnv20T B) [] args ri rj` holds for a pair of rules (an `otherwise`
rule `ri` and an earlier rule `rj`) in any of three cases, each a Boolean check on the two rules
(`pairOkB`) with a soundness lemma:

* **different atoms** (`atomSepB`, `pairBack_atomSep`): both left-hand sides end in an
  instruction with a fixed constructor, and the constructors differ. Evaluation keeps the last
  constructor (`AtomSound`), so the two left-hand sides never meet. `VElse.ruleAtom` is sound for
  the configurations `(z; instr*)` of `Step_read` (`atomSound_ruleAtom`, 's
  `lhsAtom_of_eval`), and `pureAtom` for the code `instr*` of `Step_pure` (`atomSound_pureAtom`).
* **the same left-hand side** (`sameOkB`, `pairBack_same`): every premise of `rj` is relation-free,
  and every quantifier of `rj` either has a type off `tbad20` (typed alike in both environments,
  `hasTyp_off20T`) or is the state `z : state` of a left-hand side `(z; _)` that `ri` shares, which
  `ri` types in `simEnv20S` (the two values agree by evaluation, and a named type does not read
  the scope, `hasTyp_varT_scope`).
* **a trap against a code without one** (`trapLhsB`, `noTrapB`, `pairBack_trap`): the left-hand
  side of `rj` is `_ ++ [TRAP] ++ _` (`Step_pure`'s `trap-vals`), and that of `ri` is a list of
  constructors other than `TRAP` and of quantifiers of type `ref`, which `ri` types; a typed `ref`
  is not a `TRAP` (`not_hasTyp_variant`, `refCasesOk20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.ElseAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (QuantsOk SameLhs)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp mapM_ok_mem)
open Silmaril.Wasm.SpecTec.Sim.Round7 (VElse.ruleAtom VElse.lastAtom)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix (simEnv20T)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)
open Silmaril.Wasm.SpecTec.Sim20.StoreAgree (envSame20T typRepair20T hasElseB caseOp)

/-! ## Values and expressions -/

/-- The constructor of the last instruction of a left-hand side: a code list `instr*`, or a
configuration `(z; instr*)`. -/
def atomV : Value → Option MixopS
  | .list cs => match cs.getLast? with
    | some (.case a _) => some a
    | _ => none
  | .case _ (.tuple [_, .list cs]) => match cs.getLast? with
    | some (.case a _) => some a
    | _ => none
  | _ => none

/-- `atom` reads, off a rule, a constructor that every value of its conclusion's left-hand side
ends in. -/
def AtomSound (atom : Rule → Option MixopS) : Prop :=
  ∀ (env : Env) (ρ : VarEnv) nm qs op e prems a v, atom (.ruleD nm qs op e prems) = some a →
    EvalExp env ρ e v → ∃ l r, v = .tuple [l, r] ∧ atomV l = some a

/-- The last constructor of a `Step_pure` left-hand side `instr*`. -/
def pureAtom : Rule → Option MixopS
  | .ruleD _ _ _ (.tupE [code, _]) _ => VElse.lastAtom code
  | _ => none

theorem atomV_list {cs : List Value} {a : MixopS} (h : Sim.Round7.VDecl.LastCase a cs) :
    atomV (.list cs) = some a := by
  obtain ⟨w, hw⟩ := h
  simp [atomV, hw]

theorem pureAtom_some {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem}
    {a : MixopS} (h : pureAtom (.ruleD nm qs op e prems) = some a) :
    ∃ code rhs, e = .tupE [code, rhs] ∧ VElse.lastAtom code = some a := by
  unfold pureAtom at h
  split at h
  · rename_i code rhs _ heq
    injection heq with _ _ _ he _
    exact ⟨code, rhs, he, h⟩
  · cases h

theorem atomSound_pureAtom : AtomSound pureAtom := by
  intro env ρ nm qs op e prems a v ha he
  obtain ⟨code, rhs, rfl, hl⟩ := pureAtom_some ha
  obtain ⟨n, hn⟩ := he
  obtain ⟨m, v₁, v₂, h₁, -, rfl⟩ := Sim.Round7.VDecl.evalExp_tupE2 hn
  obtain ⟨cs, rfl, hc⟩ := Sim.Round7.VDecl.evalExp_lastAtom m hl h₁
  exact ⟨_, _, rfl, atomV_list hc⟩

theorem atomV_of_lhsAtom {v : Value} {a : MixopS} (h : Sim.Round7.VDecl.lhsAtom v = some a) :
    ∃ l r, v = .tuple [l, r] ∧ atomV l = some a := by
  unfold Sim.Round7.VDecl.lhsAtom at h
  split at h
  · rename_i l r
    refine ⟨l, r, rfl, ?_⟩
    unfold Sim.Round7.VDecl.codeAtom at h
    split at h
    · simp only [atomV]
      exact h
    · cases h
  · cases h

theorem atomSound_ruleAtom : AtomSound VElse.ruleAtom := fun _ _ _ _ _ _ _ _ _ ha he =>
  atomV_of_lhsAtom (Sim.Round7.VDecl.lhsAtom_of_eval ha he)

/-! ## The checks -/

/-- A rule with an `otherwise` premise, as a check. -/
def ruleElseB : Rule → Bool
  | .ruleD _ _ _ _ prems => prems.any hasElseB

/-- The quantifier `z : state`. -/
def isZState : Param → Bool
  | .expP "z" (.varT "state" []) => true
  | _ => false

/-- A quantifier whose type is off `tbad20`, or, when `zOk`, the state `z`. -/
def quantOffB (zOk : Bool) : Param → Bool
  | .expP y t => (evTyp t).all (tyEvB tbad20) || (zOk && isZState (.expP y t))
  | _ => true

/-- A conclusion `(z; _) ~> _`. -/
def zShapeB : Rule → Bool
  | .ruleD _ _ _ (.tupE [.caseE _ (.tupE [.varE "z", _]), _]) _ => true
  | _ => false

/-- A rule quantifying `z : state`. -/
def hasZB : Rule → Bool
  | .ruleD _ qs _ _ _ => qs.any isZState

/-- The same-left-hand-side check. -/
def sameOkB (ri rj : Rule) : Bool :=
  match rj with
  | .ruleD _ qsj _ _ premsj =>
    premsj.all relFreeB && qsj.all (quantOffB (zShapeB ri && zShapeB rj && hasZB ri))

/-- The different-atoms check. -/
def atomSepB (atom : Rule → Option MixopS) (ri rj : Rule) : Bool :=
  match atom ri, atom rj with
  | some a, some b => a != b
  | _, _ => false

/-- A conclusion `_ ++ [TRAP] ++ _ ~> _`. -/
def trapLhsB : Rule → Bool
  | .ruleD _ _ _ (.tupE [.catE _ (.catE (.listE [.caseE "TRAP" (.tupE [])]) _), _]) _ => true
  | _ => false

/-- The quantifier `y : ref`. -/
def isRefQ (y : IL.Id) : Param → Bool
  | .expP y' (.varT "ref" []) => y' == y
  | _ => false

/-- An element of a code list that is not a `TRAP`: a constructor other than `TRAP`, or a
quantifier of type `ref`. -/
def noTrapElB (qs : List Param) : Exp → Bool
  | .caseE op _ => op != "TRAP"
  | .subE (.varE y) (.varT "ref" []) _ => qs.any (isRefQ y)
  | _ => false

/-- A conclusion `es ~> _` with no `TRAP` among `es`. -/
def noTrapB : Rule → Bool
  | .ruleD _ qs _ (.tupE [.listE es, _]) _ => es.all (noTrapElB qs)
  | _ => false

/-- **The pair check.** -/
def pairOkB (atom : Rule → Option MixopS) (ri rj : Rule) : Bool :=
  atomSepB atom ri rj || sameOkB ri rj || (trapLhsB rj && noTrapB ri)

/-- Every `otherwise` rule passes `pairOkB` against every earlier rule. -/
def pairsOkB (atom : Rule → Option MixopS) (rules : List Rule) : Bool :=
  (List.range rules.length).all fun i => match rules[i]? with
    | some ri => !ruleElseB ri || (List.range i).all fun j => match rules[j]? with
      | some rj => pairOkB atom ri rj
      | none => true
    | none => true

/-! ## Evaluation shapes -/

theorem evalExps_mem {env : Env} {ρ : VarEnv} {es : List Exp} {vs : List Value}
    (h : EvalExps env ρ es vs) : ∀ u ∈ vs, ∃ e ∈ es, EvalExp env ρ e u := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · simp [evalExps] at hn
  · simp only [evalExps] at hn
    intro u hu
    obtain ⟨e, he, heu⟩ := mapM_ok_mem hn u hu
    exact ⟨e, he, n, heu⟩

theorem evalExps_singleton {env : Env} {ρ : VarEnv} {e : Exp} {vs : List Value}
    (h : EvalExps env ρ [e] vs) : ∃ u, vs = [u] ∧ EvalExp env ρ e u := by
  obtain ⟨n, hn⟩ := h
  rcases n with _ | n
  · simp [evalExps] at hn
  · simp only [evalExps] at hn
    obtain ⟨u, hu, vs', hvs', rfl⟩ := Sim.Round7.VDecl.mapM_cons_ok hn
    have hnil : vs' = [] :=
      (Except.ok.inj (by simpa only [List.mapM_nil, pure, Except.pure] using hvs')).symm
    exact ⟨u, by rw [hnil], n, hu⟩

/-- Concatenation keeps the elements of its left operand. -/
theorem mem_cat_left {v₁ v₂ v : Value} {l₁ : List Value} {x : Value} (h₁ : v₁ = .list l₁)
    (hx : x ∈ l₁) (hc : Value.cat? v₁ v₂ = some v) : ∃ l, v = .list l ∧ x ∈ l := by
  subst h₁
  cases v₂ <;> simp only [Value.cat?, Option.some.injEq, reduceCtorEq] at hc
  case list l₂ => exact ⟨l₁ ++ l₂, hc.symm, List.mem_append_left _ hx⟩

/-- Concatenation keeps the elements of its right operand. -/
theorem mem_cat_right {v₁ v₂ v : Value} {l₂ : List Value} {x : Value} (h₂ : v₂ = .list l₂)
    (hx : x ∈ l₂) (hc : Value.cat? v₁ v₂ = some v) : ∃ l, v = .list l ∧ x ∈ l := by
  subst h₂
  cases v₁ <;> simp only [Value.cat?, Option.some.injEq, reduceCtorEq] at hc
  case list l₁ => exact ⟨l₁ ++ l₂, hc.symm, List.mem_append_right _ hx⟩

/-- A scope `bindParams VarEnv.empty [] args` is the empty scope. -/
theorem bindParams_nil {args : List ArgV} {ρ₀ : VarEnv}
    (h : bindParams VarEnv.empty [] args = some ρ₀) : ρ₀ = VarEnv.empty := by
  cases args with
  | nil => exact (Option.some.inj h).symm
  | cons a rest => simp [bindParams] at h

/-! ## Different atoms -/

/-- **Rules whose left-hand sides end in different constructors never meet.** -/
theorem pairBack_atomSep {e₁ e₂ : Env} {atom : Rule → Option MixopS} (hA : AtomSound atom)
    {ps : List Param} {args : List ArgV} {ri rj : Rule} (h : atomSepB atom ri rj = true) :
    PairBack e₁ e₂ ps args ri rj := by
  rcases ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w _ _ hei hej hsame _
  exfalso
  unfold atomSepB at h
  split at h
  · rename_i a b ha hb
    obtain ⟨l, r, rfl, hl⟩ := hA _ _ _ _ _ _ _ _ _ ha hei
    obtain ⟨l', r', rfl, hl'⟩ := hA _ _ _ _ _ _ _ _ _ hb hej
    obtain ⟨x, y, z, h₁, h₂⟩ := hsame
    simp only [Value.tuple.injEq, List.cons.injEq] at h₁ h₂
    have hll : l = l' := h₁.1.trans h₂.1.symm
    subst hll
    rw [hl] at hl'
    exact absurd (Option.some.inj hl') (by simpa using h)
  · cases h

/-! ## The same left-hand side -/

theorem isZState_eq {y : IL.Id} {t : Typ} (h : isZState (.expP y t) = true) :
    y = "z" ∧ t = .varT "state" [] := by
  unfold isZState at h
  split at h
  · rename_i heq
    injection heq with h₁ h₂
    exact ⟨h₁, h₂⟩
  · cases h

theorem mem_of_hasZB {nm : IL.Id} {qs : List Param} {op : MixopS} {e : Exp} {prems : List Prem}
    (h : hasZB (.ruleD nm qs op e prems) = true) : Param.expP "z" (.varT "state" []) ∈ qs := by
  simp only [hasZB, List.any_eq_true] at h
  obtain ⟨q, hq, hz⟩ := h
  rcases q with ⟨y, t⟩ | _ | _ | _
  · obtain ⟨rfl, rfl⟩ := isZState_eq hz
    exact hq
  all_goals simp [isZState] at hz

/-- A conclusion `(z; _) ~> _` evaluates to a pair whose left-hand side carries the value of
`z`. -/
theorem zShape_eval {env : Env} {ρ : VarEnv} {nm : IL.Id} {qs : List Param} {op : MixopS}
    {e : Exp} {prems : List Prem} {v : Value} (h : zShapeB (.ruleD nm qs op e prems) = true)
    (he : EvalExp env ρ e v) :
    ∃ zv c cv r, ρ.findVal? "z" = some zv ∧ v = .tuple [.case c (.tuple [zv, cv]), r] := by
  unfold zShapeB at h
  split at h
  · rename_i c code rhs _ heq
    injection heq with _ _ _ hee _
    subst hee
    obtain ⟨n, hn⟩ := he
    obtain ⟨m, v₁, v₂, h₁, -, rfl⟩ := Sim.Round7.VDecl.evalExp_tupE2 hn
    obtain ⟨m', u, hu, rfl⟩ := Sim.Round7.VDecl.evalExp_caseE h₁
    obtain ⟨k, zv, cv, hz, -, rfl⟩ := Sim.Round7.VDecl.evalExp_tupE2 hu
    exact ⟨zv, c, cv, v₂, evalExp_varE_iff.1 ⟨k, hz⟩, rfl⟩
  · cases h

/-- The left-hand sides of two values with the same left-hand side agree. -/
theorem sameLhs_fst {l r l' r' : Value} (h : SameLhs (.tuple [l, r]) (.tuple [l', r'])) :
    l = l' := by
  obtain ⟨a, b, c, h₁, h₂⟩ := h
  have e₁ : l = a ∧ r = b := by simpa using h₁
  have e₂ : l' = a ∧ r' = c := by simpa using h₂
  exact e₁.1.trans e₂.1.symm

/-- **The shared state reads back**: rule `j`'s `z` is rule `i`'s, which `i` types. -/
theorem z_back {env : Env} {σ σ' : List (IL.Id × Value)} {qsi : List Param} {ri rj : Rule}
    {nmi opi ei premsi nmj qsj opj ej premsj} {v w u : Value}
    (hri : ri = .ruleD nmi qsi opi ei premsi) (hrj : rj = .ruleD nmj qsj opj ej premsj)
    (hzi : zShapeB ri = true) (hzj : zShapeB rj = true) (hhz : hasZB ri = true)
    (hq : QuantsOk env (VarEnv.empty.bindVals σ) qsi)
    (hei : EvalExp env (VarEnv.empty.bindVals σ) ei v)
    (hej : EvalExp env (VarEnv.empty.bindVals σ') ej w) (hsame : SameLhs v w)
    (hu : (VarEnv.empty.bindVals σ').findVal? "z" = some u) :
    HasTyp env (VarEnv.empty.bindVals σ') (.varT "state" []) u := by
  subst hri hrj
  obtain ⟨zv, hzv, htz⟩ := hq "z" (.varT "state" []) (mem_of_hasZB hhz)
  obtain ⟨zi, ci, cvi, ri, fzi, rfl⟩ := zShape_eval hzi hei
  obtain ⟨zj, cj, cvj, rj, fzj, rfl⟩ := zShape_eval hzj hej
  have hl : Value.case ci (.tuple [zi, cvi]) = .case cj (.tuple [zj, cvj]) := sameLhs_fst hsame
  have hz : zi = zj := by simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq] at hl; exact hl.2.1
  have hzi' : zi = zv := Option.some.inj (fzi.symm.trans hzv)
  have hzu : u = zv := (Option.some.inj (hu.symm.trans fzj)).trans (hz.symm.trans hzi')
  rw [hzu]
  exact hasTyp_varT_scope rfl rfl htz

/-- **Rules on the same left-hand side read back**, when their other quantifiers are off
`tbad20`. -/
theorem pairBack_same {B : Builtins} {args : List ArgV} {ri rj : Rule}
    (h : sameOkB ri rj = true) : PairBack (simEnv20S B) (simEnv20T B) [] args ri rj := by
  rcases hri : ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases hrj : rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w hps hq hei hej hsame hq'
  obtain rfl := bindParams_nil hps
  have h' : premsj.all relFreeB = true ∧
      qsj.all (quantOffB (zShapeB ri && zShapeB rj && hasZB ri)) = true := by
    simpa only [hrj, sameOkB, Bool.and_eq_true] using h
  refine ⟨fun y t hy => ?_, h'.1⟩
  obtain ⟨u, hu, ht⟩ := hq' y t hy
  have hqb : (evTyp t).all (tyEvB tbad20) = true ∨ ((zShapeB ri = true ∧ zShapeB rj = true) ∧
      hasZB ri = true) ∧ isZState (.expP y t) = true := by
    simpa only [quantOffB, Bool.or_eq_true, Bool.and_eq_true] using List.all_eq_true.1 h'.2 _ hy
  rcases hqb with hoff | ⟨⟨⟨hzi, hzj⟩, hhz⟩, hz⟩
  · exact ⟨u, hu, (hasTyp_off20T B rfl (goodT_of_all hoff)).1 ht⟩
  · obtain ⟨rfl, rfl⟩ := isZState_eq hz
    exact ⟨u, hu, z_back hri hrj hzi hzj hhz hq hei hej hsame hu⟩

/-! ## A trap against a code without one -/

/-- The cases of the wasm-2.0 `ref`. -/
def refCases20 : List TypCase :=
  [.mk "REF.NULL" (.varT "reftype" []) [] [], .mk "REF.FUNC_ADDR" (.varT "funcaddr" []) [] [],
    .mk "REF.HOST_ADDR" (.varT "hostaddr" []) [] []]

set_option maxRecDepth 100000 in
/-- The wasm-2.0 `ref`, as `simEnv20S B` finds it. -/
theorem findTyp_ref20S (B : Builtins) :
    (simEnv20S B).findTyp? "ref" = some ([], [.instD [] [] (.variantT refCases20)]) := rfl

/-- **A value of a one-instance variant type is a `case` of one of its constructors.** -/
theorem not_hasTyp_variant {env : Env} {ρ : VarEnv} (hρ : ρ.typs = []) {x : IL.Id}
    {cs : List TypCase} (hx : env.findTyp? x = some ([], [.instD [] [] (.variantT cs)]))
    {op : MixopS} (hop : ∀ c ∈ cs, caseOp c ≠ op) {w : Value} :
    ¬ HasTyp env ρ (.varT x []) (.case op w) := by
  intro h
  have hl : localTyp? ρ x [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [hx] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, -, hd⟩ | hrest
  · obtain ⟨op', w', he, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨rfl, rfl⟩ := Value.case.inj he
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem hc
    exact hop _ hm rfl
  · exact not_hasTypInsts_nil hrest

/-- **A typed wasm-2.0 `ref` is not a `TRAP`.** -/
theorem not_hasTyp_ref_trap (B : Builtins) {ρ : VarEnv} (hρ : ρ.typs = []) {w : Value} :
    ¬ HasTyp (simEnv20S B) ρ (.varT "ref" []) (.case "TRAP" w) :=
  not_hasTyp_variant hρ (findTyp_ref20S B) (by simp [refCases20, caseOp])

theorem isRefQ_eq {y : IL.Id} {q : Param} (h : isRefQ y q = true) :
    q = .expP y (.varT "ref" []) := by
  unfold isRefQ at h
  split at h
  · rename_i y'
    have hy : y' = y := by simpa using h
    rw [hy]
  · cases h

/-- A pair expression evaluates to a pair. -/
theorem evalExp_pair {env : Env} {ρ : VarEnv} {a b : Exp} {v : Value}
    (h : EvalExp env ρ (.tupE [a, b]) v) :
    ∃ va vb, EvalExp env ρ a va ∧ EvalExp env ρ b vb ∧ v = .tuple [va, vb] := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, va, vb, ha, hb, rfl⟩ := Sim.Round7.VDecl.evalExp_tupE2 hn
  exact ⟨va, vb, ⟨m, ha⟩, ⟨m, hb⟩, rfl⟩

/-- `_ ++ [TRAP] ++ _` evaluates to a list holding a `TRAP`. -/
theorem trapCat_eval {env : Env} {ρ : VarEnv} {e₁ e₃ : Exp} {l : Value}
    (h : EvalExp env ρ (.catE e₁ (.catE (.listE [.caseE "TRAP" (.tupE [])]) e₃)) l) :
    ∃ cs x, l = .list cs ∧ .case "TRAP" x ∈ cs := by
  obtain ⟨a₁, a₂, -, h₂, hc⟩ := evalExp_catE_iff.1 h
  obtain ⟨t₁, t₂, ht₁, -, hc₂⟩ := evalExp_catE_iff.1 h₂
  obtain ⟨ts, hts, rfl⟩ := evalExp_listE_iff.1 ht₁
  obtain ⟨u, rfl, hu⟩ := evalExps_singleton hts
  obtain ⟨x, -, rfl⟩ := evalExp_caseE_iff.1 hu
  obtain ⟨l₂, rfl, hm₂⟩ := mem_cat_left rfl (List.mem_singleton_self _) hc₂
  obtain ⟨l', rfl, hm⟩ := mem_cat_right rfl hm₂ hc
  exact ⟨l', x, rfl, hm⟩

/-- A left-hand side `_ ++ [TRAP] ++ _` holds a `TRAP`. -/
theorem trapLhs_eval {env : Env} {ρ : VarEnv} {nm : IL.Id} {qs : List Param} {op : MixopS}
    {e : Exp} {prems : List Prem} {v : Value} (h : trapLhsB (.ruleD nm qs op e prems) = true)
    (he : EvalExp env ρ e v) : ∃ cs r x, v = .tuple [.list cs, r] ∧ .case "TRAP" x ∈ cs := by
  unfold trapLhsB at h
  split at h
  · rename_i e₁ e₃ rhs _ heq
    injection heq with _ _ _ hee _
    subst hee
    obtain ⟨l, r, hl, -, rfl⟩ := evalExp_pair he
    obtain ⟨cs, x, rfl, hx⟩ := trapCat_eval hl
    exact ⟨cs, r, x, rfl, hx⟩
  · cases h

/-- An element without a `TRAP` evaluates to a value other than a `TRAP`. -/
theorem noTrapEl_eval {B : Builtins} {ρ : VarEnv} (hρ : ρ.typs = []) {qs : List Param} {e : Exp}
    {u : Value} (h : noTrapElB qs e = true) (hq : QuantsOk (simEnv20S B) ρ qs)
    (he : EvalExp (simEnv20S B) ρ e u) (x : Value) : u ≠ .case "TRAP" x := by
  rintro rfl
  unfold noTrapElB at h
  split at h
  · obtain ⟨_, -, hc⟩ := evalExp_caseE_iff.1 he
    obtain ⟨rfl, -⟩ := Value.case.inj hc
    simp at h
  · have hy := evalExp_varE_iff.1 (evalExp_subE_iff.1 he)
    obtain ⟨q, hq', hqy⟩ := List.any_eq_true.1 h
    obtain rfl := isRefQ_eq hqy
    obtain ⟨w, hw, ht⟩ := hq _ _ hq'
    have hwx : w = .case "TRAP" x := Option.some.inj (hw.symm.trans hy)
    exact not_hasTyp_ref_trap B hρ (hwx ▸ ht)
  · cases h

/-- A code without a `TRAP` evaluates to a list without one. -/
theorem noTrap_eval {B : Builtins} {ρ : VarEnv} (hρ : ρ.typs = []) {nm : IL.Id} {qs : List Param}
    {op : MixopS} {e : Exp} {prems : List Prem} {v : Value}
    (h : noTrapB (.ruleD nm qs op e prems) = true) (hq : QuantsOk (simEnv20S B) ρ qs)
    (he : EvalExp (simEnv20S B) ρ e v) :
    ∃ cs r, v = .tuple [.list cs, r] ∧ ∀ x, .case "TRAP" x ∉ cs := by
  unfold noTrapB at h
  split at h
  · rename_i qs' es rhs _ heq
    injection heq with _ hqs _ hee _
    subst hqs hee
    obtain ⟨n, hn⟩ := he
    obtain ⟨m, v₁, v₂, h₁, -, rfl⟩ := Sim.Round7.VDecl.evalExp_tupE2 hn
    obtain ⟨cs, hcs, rfl⟩ := evalExp_listE_iff.1 ⟨m, h₁⟩
    refine ⟨cs, v₂, rfl, fun x hx => ?_⟩
    obtain ⟨e, hm, heu⟩ := evalExps_mem hcs _ hx
    exact noTrapEl_eval hρ (List.all_eq_true.1 h e hm) hq heu x rfl
  · cases h

/-- **A `TRAP` pattern never meets a code without one.** -/
theorem pairBack_trap {B : Builtins} {args : List ArgV} {ri rj : Rule}
    (h : (trapLhsB rj && noTrapB ri) = true) :
    PairBack (simEnv20S B) (simEnv20T B) [] args ri rj := by
  rcases ri with ⟨nmi, qsi, opi, ei, premsi⟩
  rcases rj with ⟨nmj, qsj, opj, ej, premsj⟩
  intro ρ₀ σ σ' v w hps hq hei hej hsame _
  exfalso
  obtain rfl := bindParams_nil hps
  simp only [Bool.and_eq_true] at h
  obtain ⟨cs, r, rfl, hno⟩ := noTrap_eval rfl h.2 hq hei
  obtain ⟨cs', r', x, rfl, hx⟩ := trapLhs_eval h.1 hej
  obtain ⟨a, b, c, h₁, h₂⟩ := hsame
  simp only [Value.tuple.injEq, List.cons.injEq] at h₁ h₂
  have hl := h₁.1.trans h₂.1.symm
  simp only [Value.list.injEq] at hl
  exact hno x (hl ▸ hx)

/-! ## The pair check -/

/-- **`pairOkB` is sound.** -/
theorem pairBack_of_pairOkB {B : Builtins} {atom : Rule → Option MixopS} (hA : AtomSound atom)
    {args : List ArgV} {ri rj : Rule} (h : pairOkB atom ri rj = true) :
    PairBack (simEnv20S B) (simEnv20T B) [] args ri rj := by
  simp only [pairOkB, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact pairBack_atomSep hA h
  · exact pairBack_same h
  · exact pairBack_trap h

/-- `RuleHasElse`, as a check. -/
theorem ruleElseB_of {r : Rule} (h : RuleHasElse r) : ruleElseB r = true := by
  rcases r with ⟨nm, qs, op, e, prems⟩
  obtain ⟨pr, hm, hp⟩ := h
  simp only [ruleElseB, List.any_eq_true]
  exact ⟨pr, hm, hp⟩

/-- **`pairsOkB` gives the hypothesis of `otherwiseAt_move`.** -/
theorem pairBack_of_pairsOkB {B : Builtins} {atom : Rule → Option MixopS} (hA : AtomSound atom)
    {args : List ArgV} {rules : List Rule} (h : pairsOkB atom rules = true) :
    ∀ (i j : Nat) ri rj, j < i → rules[i]? = some ri → rules[j]? = some rj → RuleHasElse ri →
      PairBack (simEnv20S B) (simEnv20T B) [] args ri rj := by
  intro i j ri rj hj hri hrj hel
  have hi : i < rules.length := (List.getElem?_eq_some_iff.1 hri).1
  have h₁ := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [hri] at h₁
  simp only [ruleElseB_of hel, Bool.not_true, Bool.false_or] at h₁
  have h₂ := List.all_eq_true.1 h₁ j (List.mem_range.2 hj)
  rw [hrj] at h₂
  exact pairBack_of_pairOkB hA h₂

end Silmaril.Wasm.SpecTec.Sim20.ElseAgree
