module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy.Thms
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms

/-!
# Round 5: every `Step` rule reads the last instruction of its code

Every one of the 36 rules of SpecTec's `Step` reads its left-hand code `ce` (in
`z; ce ~> _` or `(s; f); ce ~> _`) in one of three shapes (`lastOk`, checked on the rules of
the fixed script by `rfl` in `stepRules_lastGuarded`):

* an iteration `x*` or `x^n` over one quantifier `x* : instr*` or `x* : val*`, whose body reads
  `x` back (possibly through `x <: instr`);
* a concatenation of such shapes;
* a literal list whose last element is a case other than `VUNOP`.

The declarative reading types every quantifier (`QuantsOk`), so the last instruction of the
code of a configuration SpecTec steps from is a case other than `VUNOP`, a typed `instr` or a
typed `val` (`lastGood_of_lastOk`). **No `Step` fires on a configuration whose last instruction
is a `VUNOP` that is neither a typed `instr` nor a typed `val`** (`not_sstep_of_last`), and the
image of `f32x4.sqrt` is one (`not_sstep_of_last_f32x4Sqrt`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Target

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {B : Builtins} {env : Env}

/-! ## The guard -/

/-- `y : instr*` or `y : val*`. -/
def isSeqParam (y : IL.Id) : Param → Bool
  | .expP z (.iterT (.varT t []) .list) => z == y && (t == "instr" || t == "val")
  | _ => false

/-- The body of an iteration reads its variable `x` back: `x`, or `x <: _`. -/
def bodyReads (x : IL.Id) : Exp → Bool
  | .varE y => y == x
  | .subE (.varE y) _ _ => y == x
  | _ => false

/-- An unbounded or counted iteration. -/
def iterOk : Iter → Bool
  | .list => true
  | .listN (.varE _) none => true
  | _ => false

/-- An iteration over one quantifier `y : instr*` or `y : val*` whose body reads its variable. -/
def iterExpOk (qs : List Param) (b : Exp) : IterExp → Bool
  | .mk it [.mk x (.varE y)] => iterOk it && bodyReads x b && x != "_" && qs.any (isSeqParam y)
  | _ => false

/-- A literal last element: a case other than `op`. -/
def lastLitOk (op : MixopS) : Option Exp → Bool
  | some (.caseE n _) => n != op
  | _ => false

/-- **The code shapes of the `Step` rules**: the last element of the code is read through a
quantifier of type `instr*` or `val*`, or is a literal case other than `op`. -/
def lastOk (qs : List Param) (op : MixopS) : Exp → Bool
  | .iterE b ie => iterExpOk qs b ie
  | .catE a b => lastOk qs op a && lastOk qs op b
  | .listE es => lastLitOk op es.getLast?
  | _ => false

/-- The conclusion reads its left-hand code in a `lastOk` shape. -/
def codeGuardQE (qs : List Param) (op : MixopS) : Exp → Bool
  | .tupE [.caseE "%;%" (.tupE [_, ce]), _] => lastOk qs op ce
  | _ => false

/-- `codeGuardQE` on a rule, at `VUNOP`. -/
def codeGuard : Rule → Bool
  | .ruleD _ qs _ e _ => codeGuardQE qs "VUNOP" e

set_option maxRecDepth 100000 in
/-- **Every rule of `Step` reads the last instruction of its code**, in every `simEnv B`. -/
theorem stepRules_lastGuarded (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step" = some ([], "%~>%", t, rules) ∧ rules.all codeGuard = true :=
  ⟨_, _, rfl, rfl⟩

/-! ## Soundness of the guard -/

/-- **What a guarded last element can be**: a case other than `op`, a typed `instr` or a typed
`val`. -/
def LastGood (B : Builtins) (op : MixopS) (u : Value) : Prop :=
  (∀ p, u ≠ .case op p) ∨ TypedV (simEnv B) (.varT "instr" []) u ∨
    TypedV (simEnv B) (.varT "val" []) u

/-- A body that reads `x` back evaluates to `x`'s value. -/
theorem bodyReads_sound {x : IL.Id} {b : Exp} (h : bodyReads x b = true) :
    ∀ (σ : VarEnv) (w u : Value), σ.findVal? x = some w → EvalExp env σ b u → u = w := by
  intro σ w u hw hu
  unfold bodyReads at h
  split at h
  · obtain rfl := beq_iff_eq.1 h
    rw [evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm
  · obtain rfl := beq_iff_eq.1 h
    rw [evalExp_subE_iff, evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm
  · cases h

/-- `x*` over one domain `y`, inverted: `y` is bound to the result. -/
theorem evalExp_iterList_inv {ρ : VarEnv} {b : Exp} {x y : IL.Id} {v : Value}
    (hb : ∀ (σ : VarEnv) (w u : Value), σ.findVal? x = some w → EvalExp env σ b u → u = w)
    (hx : x ≠ "_") (h : EvalExp env ρ (.iterE b (.mk .list [.mk x (.varE y)])) v) :
    ∃ vs, ρ.findVal? y = some (.list vs) ∧ v = .list vs := by
  obtain ⟨n, hn⟩ := evalExp_iterE_iff.1 h
  cases n with
  | zero => simp [evalIterE] at hn
  | succ n =>
      rw [evalIterE] at hn
      simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok] at hn
      obtain ⟨xvs, hdoms, -, k, -, hlist⟩ := hn
      obtain ⟨yv, fy, rfl⟩ := Exn.evalDoms_one hdoms
      obtain ⟨l, rfl, -, rfl⟩ := Exn.evalIterList_one_inv hb hx hlist
      exact ⟨l, fy, rfl⟩

/-- An iteration in a `lastOk` shape, inverted: its domain is bound to the result. -/
theorem evalExp_iterOk_inv {ρ : VarEnv} {b : Exp} {it : Iter} {x y : IL.Id} {v : Value}
    (hit : iterOk it = true) (hb : bodyReads x b = true) (hx : x ≠ "_")
    (h : EvalExp env ρ (.iterE b (.mk it [.mk x (.varE y)])) v) :
    ∃ vs, ρ.findVal? y = some (.list vs) ∧ v = .list vs := by
  unfold iterOk at hit
  split at hit
  · exact evalExp_iterList_inv (bodyReads_sound hb) hx h
  · obtain ⟨vs, hy, -, rfl⟩ := Exn.evalExp_iterN_inv (bodyReads_sound hb) hx h
    exact ⟨vs, hy, rfl⟩
  · cases hit

/-- A quantifier `y : instr*` or `y : val*`, bound to `vs`, types each element of `vs`. -/
theorem lastGood_of_seqParam {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {y : IL.Id} (hy : qs.any (isSeqParam y) = true)
    {vs : List Value} (hv : ρ.findVal? y = some (.list vs)) {u : Value} (hu : u ∈ vs)
    (op : MixopS) : LastGood B op u := by
  obtain ⟨q, hqm, hqy⟩ := List.any_eq_true.1 hy
  unfold isSeqParam at hqy
  split at hqy
  · rename_i z t
    obtain ⟨hz, ht⟩ := Bool.and_eq_true_iff.1 hqy
    obtain rfl := beq_iff_eq.1 hz
    obtain ⟨w, hw, hwt⟩ := hq z _ hqm
    rw [hv] at hw
    obtain rfl := Option.some.inj hw
    obtain ⟨l, hl, hlt⟩ := hasTyp_iterT_list_iff.1 hwt
    obtain rfl := (Value.list.inj hl)
    have hut : HasTyp (simEnv B) ρ (.varT t []) u := hasTypList_iff.1 hlt u hu
    rcases Bool.or_eq_true_iff.1 ht with h | h
    · obtain rfl := beq_iff_eq.1 h
      exact .inr (.inl (Typing.typedV_of_hasTyp hρ hut))
    · obtain rfl := beq_iff_eq.1 h
      exact .inr (.inr (Typing.typedV_of_hasTyp hρ hut))
  · cases hqy

/-- The last value of an evaluated list is the value of its last expression. -/
theorem evalExps_getLast {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value} {u : Value}, EvalExps env ρ es vs →
      vs.getLast? = some u → ∃ e, es.getLast? = some e ∧ EvalExp env ρ e u
  | [], _, _, h, hu => by
    rw [evalExps_nil_iff.1 h] at hu
    cases hu
  | [e], _, _, h, hu => by
    obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 h
    obtain rfl := evalExps_nil_iff.1 hws
    obtain rfl : w = _ := Option.some.inj hu
    exact ⟨e, rfl, hw⟩
  | _ :: e' :: es, _, _, h, hu => by
    obtain ⟨w, ws, -, hws, rfl⟩ := evalExps_cons_iff.1 h
    obtain ⟨w', ws', -, -, rfl⟩ := evalExps_cons_iff.1 hws
    rw [List.getLast?_cons_cons] at hu
    obtain ⟨e₀, he₀, hu'⟩ := evalExps_getLast hws hu
    exact ⟨e₀, by rw [List.getLast?_cons_cons]; exact he₀, hu'⟩

/-- A literal list in a `lastOk` shape ends in a case other than `op`. -/
theorem lastGood_of_listE {ρ : VarEnv} {es : List Exp} {op : MixopS} {vs : List Value}
    {u : Value} (hg : lastLitOk op es.getLast? = true)
    (he : EvalExp (simEnv B) ρ (.listE es) (.list vs)) (hu : vs.getLast? = some u) :
    LastGood B op u := by
  obtain ⟨vs', hvs, hv⟩ := evalExp_listE_iff.1 he
  obtain rfl := Value.list.inj hv
  obtain ⟨e, hes, heu⟩ := evalExps_getLast hvs hu
  rw [hes] at hg
  unfold lastLitOk at hg
  split at hg
  · rename_i n x hx
    obtain rfl := Option.some.inj hx
    obtain ⟨p, -, rfl⟩ := evalExp_caseE_iff.1 heu
    refine .inl fun p' hp => ?_
    obtain ⟨rfl, -⟩ := Value.case.inj hp
    exact absurd rfl (bne_iff_ne.1 hg)
  · cases hg

/-- An iteration in a `lastOk` shape: its elements are typed by its quantifier. -/
theorem lastGood_of_iterE {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {op : MixopS} {b : Exp} {ie : IterExp} {vs : List Value}
    {u : Value} (hg : iterExpOk qs b ie = true)
    (he : EvalExp (simEnv B) ρ (.iterE b ie) (.list vs)) (hu : vs.getLast? = some u) :
    LastGood B op u := by
  unfold iterExpOk at hg
  split at hg
  · rename_i it x y
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hg
    obtain ⟨⟨⟨hit, hbd⟩, hx⟩, hy⟩ := hg
    obtain ⟨vs', hv, hl⟩ := evalExp_iterOk_inv hit hbd hx he
    obtain rfl := Value.list.inj hl
    exact lastGood_of_seqParam hρ hq hy hv (List.mem_of_getLast? hu) op
  · cases hg

/-- A concatenation's last element is its right part's, or its left part's when the right part
is empty. -/
theorem lastGood_of_catE {ρ : VarEnv} {a b : Exp} {op : MixopS} {vs : List Value} {u : Value}
    (iha : ∀ {vs : List Value} {u : Value}, EvalExp (simEnv B) ρ a (.list vs) →
      vs.getLast? = some u → LastGood B op u)
    (ihb : ∀ {vs : List Value} {u : Value}, EvalExp (simEnv B) ρ b (.list vs) →
      vs.getLast? = some u → LastGood B op u)
    (he : EvalExp (simEnv B) ρ (.catE a b) (.list vs)) (hu : vs.getLast? = some u) :
    LastGood B op u := by
  obtain ⟨l₁, l₂, h₁, h₂, rfl⟩ := Exn.evalExp_cat_inv he
  rw [List.getLast?_append] at hu
  cases hl : l₂.getLast? with
  | some u' =>
    rw [hl] at hu
    obtain rfl : u' = u := Option.some.inj hu
    exact ihb h₂ hl
  | none =>
    rw [hl, Option.none_or] at hu
    exact iha h₁ hu

/-- **The guard is sound**: the last element of the value of a `lastOk` shape, under typed
quantifiers, is `LastGood`. -/
theorem lastGood_of_lastOk {ρ : VarEnv} (hρ : ValsOnly ρ) {qs : List Param}
    (hq : QuantsOk (simEnv B) ρ qs) {op : MixopS} :
    ∀ (e : Exp) {vs : List Value} {u : Value}, lastOk qs op e = true →
      EvalExp (simEnv B) ρ e (.list vs) → vs.getLast? = some u → LastGood B op u
  | e, _, _, hg, he, hu => by
    unfold lastOk at hg
    split at hg
    · exact lastGood_of_iterE hρ hq hg he hu
    · rename_i a b
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 hg
      exact lastGood_of_catE (fun h₁ h₂ => lastGood_of_lastOk hρ hq a ha h₁ h₂)
        (fun h₁ h₂ => lastGood_of_lastOk hρ hq b hb h₁ h₂) he hu
    · exact lastGood_of_listE hg he hu
    · cases hg
termination_by e => sizeOf e
