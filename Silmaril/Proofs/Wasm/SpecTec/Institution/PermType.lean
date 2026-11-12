module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.PermEval
public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# Renaming identifiers: equivariance of the type-membership test

`TypEqvAt π n`: the seven members of `Sem.hasTyp`'s mutual block, at fuel `n`, commute with
renaming every identifier by a permutation `π` fixing `"_"`. With the evaluator's equivariance
(`eqvAt`) this gives `typEqvAt π hπ n` at every fuel, and `hasTyp_rn` for the relation
`Sem.HasTyp`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

variable {π : Equiv.Perm IL.Id}

/-! ## Fuel-free auxiliaries -/

theorem typBinds_rn (hπ : π "_" = "_") :
    ∀ (ρ : VarEnv) (bs : List TypBind) (vs : List Value),
      typBinds (rnVarEnv π ρ) (rnTypBinds π bs) vs = rnVarEnv π (typBinds ρ bs vs)
  | ρ, .mk x t :: bs, v :: vs => by
    simp only [rnTypBinds, rnTypBind, typBinds, bindVal_rn hπ, typBinds_rn hπ _ bs vs]
  | ρ, [], _ => by simp only [rnTypBinds, typBinds]
  | ρ, .mk x t :: bs, [] => by simp only [rnTypBinds, rnTypBind, typBinds]

theorem caseScope_rn (hπ : π "_" = "_") (ρ : VarEnv) (t : Typ) (w : Value) :
    caseScope (rnVarEnv π ρ) (rnTyp π t) w = rnVarEnv π (caseScope ρ t w) := by
  cases t <;> cases w <;> simp only [rnTyp, caseScope, typBinds_rn hπ]

theorem localTyp?_rn (ρ : VarEnv) (x : IL.Id) (args : List Arg) :
    localTyp? (rnVarEnv π ρ) (π x) (rnArgs π args) = (localTyp? ρ x args).map (rnTyp π) := by
  cases args <;> simp only [rnArgs, localTyp?, findTyp?_rn, Option.map_none]

theorem premsOk_rn (hπ : π "_" = "_") (n : Nat) (env : Env) (ρ : VarEnv) (prems : List Prem) :
    premsOk n (rnEnv π env) (rnVarEnv π ρ) (rnPrems π prems) = premsOk n env ρ prems := by
  simp only [premsOk, (eqvAt hπ n).premsHold, elimUndef_map]
  rfl

theorem stripSubE_rn : ∀ e : Exp, stripSubE (rnExp π e) = rnExp π (stripSubE e)
  | .subE e _ _ => by simp only [rnExp, stripSubE, stripSubE_rn e]
  | .varE _ | .boolE _ | .numE _ | .textE _ | .unE .. | .binE .. | .cmpE .. | .tupE _
  | .projE .. | .caseE .. | .uncaseE .. | .optE _ | .theE _ | .strE _ | .dotE .. | .compE ..
  | .listE _ | .liftE _ | .memE .. | .lenE _ | .catE .. | .idxE .. | .sliceE .. | .updE ..
  | .extE .. | .callE .. | .iterE .. | .cvtE .. => rfl

/-- The renaming of a quantifier with its type. -/
def rnQ (π : Equiv.Perm IL.Id) (p : IL.Id × Typ) : IL.Id × Typ := (π p.1, rnTyp π p.2)

/-- The renaming of a defining conjunct. -/
def rnQE (π : Equiv.Perm IL.Id) (p : IL.Id × Typ × Exp) : IL.Id × Typ × Exp :=
  (π p.1, rnTyp π p.2.1, rnExp π p.2.2)

theorem quantOf_varE_rn (x : IL.Id) :
    ∀ qs : List Param, quantOf (rnParams π qs) (.varE (π x)) = (quantOf qs (.varE x)).map (rnQ π)
  | [] => rfl
  | p :: qs => by
    have ih := quantOf_varE_rn x qs
    simp only [quantOf] at ih ⊢
    cases p with
    | expP y t =>
      by_cases h : y = x
      · subst h
        simp only [rnParams, rnParam, List.findSome?_cons, ite_true, Option.map_some]
        rfl
      · have h' : ¬ π y = π x := fun e => h (π.injective e)
        simp only [rnParams, rnParam, List.findSome?_cons, h, h', ite_false, ih]
    | _ => simp only [rnParams, rnParam, List.findSome?_cons, ih]

theorem quantOf_rn (qs : List Param) (e : Exp) :
    quantOf (rnParams π qs) (rnExp π e) = (quantOf qs e).map (rnQ π) := by
  cases e with
  | varE x => exact quantOf_varE_rn x qs
  | _ => rfl

theorem quantEqs_rn (qs : List Param) :
    ∀ e : Exp, quantEqs (rnParams π qs) (rnExp π e) = (quantEqs qs e).map (rnQE π)
  | .binE op t a b => by
    cases op <;> simp only [rnExp, quantEqs, quantEqs_rn qs a, quantEqs_rn qs b, List.map_append,
      List.map_nil]
  | .cmpE op t a b => by
    cases op <;> simp only [rnExp, quantEqs, List.map_nil]
    rw [stripSubE_rn, quantOf_rn, stripSubE_rn, quantOf_rn]
    cases quantOf qs (stripSubE b) with
    | some p => rfl
    | none =>
      cases quantOf qs (stripSubE a) with
      | some p => rfl
      | none => rfl
  | .varE _ | .boolE _ | .numE _ | .textE _ | .unE .. | .tupE _
  | .projE .. | .caseE .. | .uncaseE .. | .optE _ | .theE _ | .strE _ | .dotE .. | .compE ..
  | .listE _ | .liftE _ | .memE .. | .lenE _ | .catE .. | .idxE .. | .sliceE .. | .updE ..
  | .extE .. | .callE .. | .iterE .. | .cvtE .. | .subE .. => rfl

theorem quantDefs_rn (qs : List Param) (prems : List Prem) :
    quantDefs (rnParams π qs) (rnPrems π prems) = (quantDefs qs prems).map (rnQE π) := by
  induction prems with
  | nil => rfl
  | cons p ps ih =>
    simp only [quantDefs, rnPrems, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]
    cases p <;> simp only [rnPrem, quantEqs_rn, List.map_nil]

theorem bindQuants_rn (hπ : π "_" = "_") {ev ev' : VarEnv → Exp → Res Value}
    {ty ty' : VarEnv → Typ → Value → Res Bool}
    (hev : ∀ ρ e, ev' (rnVarEnv π ρ) (rnExp π e) = ev ρ e)
    (hty : ∀ ρ t v, ty' (rnVarEnv π ρ) (rnTyp π t) v = ty ρ t v) :
    ∀ (ρ : VarEnv) (ds : List (IL.Id × Typ × Exp)),
      bindQuants ev' ty' (rnVarEnv π ρ) (ds.map (rnQE π)) =
        Option.map (rnVarEnv π) <$> bindQuants ev ty ρ ds
  | ρ, [] => rfl
  | ρ, (x, t, e) :: ds => by
    simp only [List.map_cons, rnQE, bindQuants, hev, hty, bindVal_rn hπ, bindQuants_rn hπ hev hty,
      map_bind, map_ite, map_ok, Option.map_none]

/-- Equivariance of the seven members of `hasTyp`'s mutual block at fuel `n`. -/
structure TypEqvAt (π : Equiv.Perm IL.Id) (n : Nat) : Prop where
  typ : ∀ env ρ t v, hasTyp n (rnEnv π env) (rnVarEnv π ρ) (rnTyp π t) v = hasTyp n env ρ t v
  tup : ∀ env ρ bs vs, hasTypTup n (rnEnv π env) (rnVarEnv π ρ) (rnTypBinds π bs) vs =
    hasTypTup n env ρ bs vs
  list : ∀ env ρ t vs, hasTypList n (rnEnv π env) (rnVarEnv π ρ) (rnTyp π t) vs =
    hasTypList n env ρ t vs
  deftyp : ∀ env ρ dt v, hasTypDef n (rnEnv π env) (rnVarEnv π ρ) (rnDefTyp π dt) v =
    hasTypDef n env ρ dt v
  fields : ∀ env ρ fs gs, hasTypFields n (rnEnv π env) (rnVarEnv π ρ) (rnTypFields π fs) gs =
    hasTypFields n env ρ fs gs
  case : ∀ env ρ cs op w, hasTypCase n (rnEnv π env) (rnVarEnv π ρ) (rnTypCases π cs) op w =
    hasTypCase n env ρ cs op w
  insts : ∀ env is ws v, hasTypInsts n (rnEnv π env) (rnInsts π is) (ws.map (rnArgV π)) v =
    hasTypInsts n env is ws v

theorem typEqvAt_zero : TypEqvAt π 0 := by
  constructor <;> intros <;>
    simp only [hasTyp, hasTypTup, hasTypList, hasTypDef, hasTypFields, hasTypCase, hasTypInsts]

section Succ

variable {n : Nat} (env : Env) (ρ : VarEnv)

theorem TypEqvAt.typ_succ (hπ : π "_" = "_") (ih : TypEqvAt π n) (t : Typ) (v : Value) :
    hasTyp (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnTyp π t) v = hasTyp (n + 1) env ρ t v := by
  cases t with
  | varT x args =>
    simp only [rnTyp, hasTyp, localTyp?_rn]
    cases localTyp? ρ x args with
    | some t => simp only [Option.map_some, ih.typ]
    | none =>
      simp only [Option.map_none, Env.findTyp?_rn, ofOption_map, bind_map_left,
        (eqvAt hπ n).args, rnTypDef, ih.insts]
  | iterT t it =>
    cases it with
    | listN e x => simp only [rnTyp, rnIter, hasTyp, (eqvAt hπ n).exp, ih.list]
    | _ => simp only [rnTyp, rnIter, hasTyp, ih.typ, ih.list]
  | _ => simp only [rnTyp, hasTyp, ih.tup]

theorem TypEqvAt.tup_succ (hπ : π "_" = "_") (ih : TypEqvAt π n) (bs : List TypBind)
    (vs : List Value) :
    hasTypTup (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnTypBinds π bs) vs =
      hasTypTup (n + 1) env ρ bs vs := by
  rcases bs with _ | ⟨⟨x, t⟩, bs⟩ <;> cases vs <;>
    simp only [rnTypBinds, rnTypBind, hasTypTup, ih.typ, bindVal_rn hπ, ih.tup]

theorem TypEqvAt.list_succ (ih : TypEqvAt π n) (t : Typ) (vs : List Value) :
    hasTypList (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnTyp π t) vs =
      hasTypList (n + 1) env ρ t vs := by
  cases vs <;> simp only [hasTypList, ih.typ, ih.list]

theorem TypEqvAt.deftyp_succ (ih : TypEqvAt π n) (dt : DefTyp) (v : Value) :
    hasTypDef (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnDefTyp π dt) v =
      hasTypDef (n + 1) env ρ dt v := by
  cases dt <;> simp only [rnDefTyp, hasTypDef, ih.typ, ih.fields, ih.case]

theorem TypEqvAt.fields_succ (hπ : π "_" = "_") (ih : TypEqvAt π n) (fs : List TypField)
    (gs : List (AtomS × Value)) :
    hasTypFields (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnTypFields π fs) gs =
      hasTypFields (n + 1) env ρ fs gs := by
  rcases fs with _ | ⟨⟨a, t, qs, prems⟩, fs⟩ <;> rcases gs with _ | ⟨⟨a', w⟩, gs⟩ <;>
    simp only [rnTypFields, rnTypField, hasTypFields, ih.typ, caseScope_rn hπ, premsOk_rn hπ,
      ih.fields]

theorem TypEqvAt.case_succ (hπ : π "_" = "_") (ih : TypEqvAt π n) (cs : List TypCase)
    (op : MixopS) (w : Value) :
    hasTypCase (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnTypCases π cs) op w =
      hasTypCase (n + 1) env ρ cs op w := by
  rcases cs with _ | ⟨⟨op', t, qs, prems⟩, cs⟩
  · simp only [rnTypCases, hasTypCase]
  · have hb := bindQuants_rn hπ (fun ρ e => (eqvAt hπ n).exp env ρ e) (fun ρ t v => ih.typ env ρ t v)
    simp only [rnTypCases, rnTypCase, hasTypCase, ih.typ, caseScope_rn hπ, quantDefs_rn, hb,
      elimUndef_map, ih.case]
    congr! 5
    funext q
    cases q <;> simp only [Function.comp_apply, Option.map_some, Option.map_none, premsOk_rn hπ]

theorem TypEqvAt.insts_succ (hπ : π "_" = "_") (ih : TypEqvAt π n) (is : List Inst)
    (ws : List ArgV) (v : Value) :
    hasTypInsts (n + 1) (rnEnv π env) (rnInsts π is) (ws.map (rnArgV π)) v =
      hasTypInsts (n + 1) env is ws v := by
  rcases is with _ | ⟨⟨qs, pats, dt⟩, is⟩
  · simp only [rnInsts, hasTypInsts]
  · simp only [rnInsts, rnInst, hasTypInsts, (eqvAt hπ n).matchArgs_empty, elimUndef_map,
      Function.comp_def, ih.deftyp, ih.insts]

end Succ

theorem typEqvAt_succ (hπ : π "_" = "_") {n : Nat} (ih : TypEqvAt π n) : TypEqvAt π (n + 1) where
  typ env ρ t v := TypEqvAt.typ_succ env ρ hπ ih t v
  tup env ρ bs vs := TypEqvAt.tup_succ env ρ hπ ih bs vs
  list env ρ t vs := TypEqvAt.list_succ env ρ ih t vs
  deftyp env ρ dt v := TypEqvAt.deftyp_succ env ρ ih dt v
  fields env ρ fs gs := TypEqvAt.fields_succ env ρ hπ ih fs gs
  case env ρ cs op w := TypEqvAt.case_succ env ρ hπ ih cs op w
  insts env is ws v := TypEqvAt.insts_succ env hπ ih is ws v

/-- **The type-membership test is equivariant** at every fuel. -/
theorem typEqvAt (hπ : π "_" = "_") : ∀ n, TypEqvAt π n
  | 0 => typEqvAt_zero
  | n + 1 => typEqvAt_succ hπ (typEqvAt hπ n)

/-- `HasTyp` is equivariant. -/
theorem hasTyp_rn (hπ : π "_" = "_") (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) :
    HasTyp (rnEnv π env) (rnVarEnv π ρ) (rnTyp π t) v ↔ HasTyp env ρ t v := by
  simp only [HasTyp, (typEqvAt hπ _).typ]

/-- `EvalExp` is equivariant. -/
theorem evalExp_rn (hπ : π "_" = "_") (env : Env) (ρ : VarEnv) (e : Exp) (v : Value) :
    EvalExp (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) v ↔ EvalExp env ρ e v := by
  simp only [EvalExp, (eqvAt hπ _).exp]

/-- `EvalArgs` is equivariant. -/
theorem evalArgs_rn (hπ : π "_" = "_") (env : Env) (ρ : VarEnv) (l : List Arg) (ws : List ArgV) :
    EvalArgs (rnEnv π env) (rnVarEnv π ρ) (rnArgs π l) (ws.map (rnArgV π)) ↔
      EvalArgs env ρ l ws := by
  have hinj : Function.Injective (List.map (rnArgV π)) :=
    List.map_injective_iff.mpr fun a b h => by rw [← rnArgV_symm π a, h, rnArgV_symm]
  simp only [EvalArgs, (eqvAt hπ _).args]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨ws', h₁, h₂⟩ := Res.map_eq_ok.mp hk
    exact ⟨k, h₁.trans (congrArg _ (hinj h₂))⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; rfl⟩

/-- `EvalDoms` is equivariant. -/
theorem evalDoms_rn (hπ : π "_" = "_") (env : Env) (ρ : VarEnv) (ds : List Dom)
    (xvs : List (IL.Id × Value)) :
    Silmaril.Wasm.SpecTec.Sim.EvalDoms (rnEnv π env) (rnVarEnv π ρ) (rnDoms π ds) (rnMap π id xvs) ↔
      Silmaril.Wasm.SpecTec.Sim.EvalDoms env ρ ds xvs := by
  have hinj : Function.Injective (rnMap (α := Value) π id) := by
    intro a b h
    have := congrArg (rnMap π.symm id) h
    rwa [rnMap_symm π (fun _ => id) (fun _ => rfl), rnMap_symm π (fun _ => id) (fun _ => rfl)]
      at this
  simp only [Silmaril.Wasm.SpecTec.Sim.EvalDoms, (eqvAt hπ _).doms]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨xs', h₁, h₂⟩ := Res.map_eq_ok.mp hk
    exact ⟨k, h₁.trans (congrArg _ (hinj h₂))⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; rfl⟩

end Silmaril.Wasm.SpecTec.Institution.Perm

