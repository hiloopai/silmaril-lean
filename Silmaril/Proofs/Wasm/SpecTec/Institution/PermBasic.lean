module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.PermLaws

/-!
# Renaming identifiers: the fuel-free parts of the evaluator

For a permutation `π` of identifiers that fixes the wildcard `"_"` (`Map.bind` ignores it), the
lookups and bindings of maps, scopes and environments commute with renaming, and so do the
fuel-free auxiliaries of the evaluator: `resolveTyp`, `matchTypV`, `bindParams`, `subCaseOk`,
`iterRows`. Syntactic equality (`typEq`, `symEq`) is preserved because renaming along a
permutation is injective.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Renaming as `List.map` -/

theorem rnExps_eq (f : IL.Id → IL.Id) (es : List Exp) : rnExps f es = es.map (rnExp f) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [rnExps, ih, List.map_cons]

theorem rnArgs_eq (f : IL.Id → IL.Id) (l : List Arg) : rnArgs f l = l.map (rnArg f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [rnArgs, ih, List.map_cons]

theorem rnDoms_eq (f : IL.Id → IL.Id) (ds : List Dom) : rnDoms f ds = ds.map (rnDom f) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [rnDoms, ih, List.map_cons]

theorem rnExpFields_eq (f : IL.Id → IL.Id) (fs : List ExpField) :
    rnExpFields f fs = fs.map (rnExpField f) := by
  induction fs with
  | nil => rfl
  | cons c fs ih => simp only [rnExpFields, ih, List.map_cons]

theorem rnPrems_eq (f : IL.Id → IL.Id) (ps : List Prem) : rnPrems f ps = ps.map (rnPrem f) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [rnPrems, ih, List.map_cons]

theorem rnParams_eq (f : IL.Id → IL.Id) (ps : List Param) :
    rnParams f ps = ps.map (rnParam f) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [rnParams, ih, List.map_cons]

theorem rnRules_eq (f : IL.Id → IL.Id) (rs : List Rule) : rnRules f rs = rs.map (rnRule f) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [rnRules, ih, List.map_cons]

theorem rnClauses_eq (f : IL.Id → IL.Id) (cs : List Clause) :
    rnClauses f cs = cs.map (rnClause f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [rnClauses, ih, List.map_cons]

theorem rnTypCases_eq (f : IL.Id → IL.Id) (cs : List TypCase) :
    rnTypCases f cs = cs.map (rnTypCase f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [rnTypCases, ih, List.map_cons]

theorem rnInsts_eq (f : IL.Id → IL.Id) (is : List Inst) : rnInsts f is = is.map (rnInst f) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [rnInsts, ih, List.map_cons]

theorem rnIdOpt_eq (f : IL.Id → IL.Id) (o : Option IL.Id) : rnIdOpt f o = o.map f := by
  cases o <;> rfl

theorem rnExpOpt_eq (f : IL.Id → IL.Id) (o : Option Exp) : rnExpOpt f o = o.map (rnExp f) := by
  cases o <;> rfl

theorem domVar_rn (f : IL.Id → IL.Id) (d : Dom) : domVar (rnDom f d) = f (domVar d) := by
  cases d; rfl

theorem domSrc_rn (f : IL.Id → IL.Id) (d : Dom) : domSrc (rnDom f d) = rnExp f (domSrc d) := by
  cases d; rfl

variable (π : Equiv.Perm IL.Id)

/-! ## Injectivity -/

theorem rnTyp_inj {a b : Typ} : rnTyp π a = rnTyp π b ↔ a = b :=
  ⟨fun h => by rw [← rnTyp_symm π a, h, rnTyp_symm], fun h => h ▸ rfl⟩

theorem rnSym_inj {a b : Sym} : rnSym π a = rnSym π b ↔ a = b :=
  ⟨fun h => by rw [← rnSym_symm π a, h, rnSym_symm], fun h => h ▸ rfl⟩

theorem typEq_rn (a b : Typ) : typEq (rnTyp π a) (rnTyp π b) = typEq a b := by
  rw [Bool.eq_iff_iff, typEq_iff, typEq_iff, rnTyp_inj]

theorem symEq_rn (a b : Sym) : symEq (rnSym π a) (rnSym π b) = symEq a b := by
  rw [Bool.eq_iff_iff, symEq_iff, symEq_iff, rnSym_inj]

/-! ## Maps -/

variable {α : Type}

theorem find?_rnMap (g : α → α) (m : Map α) (x : IL.Id) :
    (rnMap π g m).find? (π x) = (m.find? x).map g := by
  induction m with
  | nil => rfl
  | cons p m ih =>
    obtain ⟨y, v⟩ := p
    by_cases h : y = x
    · simp only [rnMap, List.map_cons, Map.find?_cons, h, ite_true, Option.map_some]
    · have h' : ¬ π y = π x := fun e => h (π.injective e)
      simp only [rnMap] at ih
      simp only [rnMap, List.map_cons, Map.find?_cons, h, h', ite_false, ih]

theorem mem_rnMap (g : α → α) (m : Map α) (x : IL.Id) : (rnMap π g m).mem (π x) = m.mem x := by
  simp only [Map.mem, find?_rnMap, Option.isSome_map]

variable {π}

theorem bind_rnMap (hπ : π "_" = "_") (g : α → α) (m : Map α) (x : IL.Id) (v : α) :
    (rnMap π g m).bind (π x) (g v) = rnMap π g (m.bind x v) := by
  by_cases h : x = "_"
  · subst h
    simp only [Map.bind, hπ, ite_true]
  · have h' : ¬ π x = "_" := fun e => h (π.injective (e.trans hπ.symm))
    simp only [Map.bind, h, h', ite_false, rnMap, List.map_cons]

theorem binds_rnMap (hπ : π "_" = "_") (g : α → α) (m : Map α) (xs : List (IL.Id × α)) :
    (rnMap π g m).binds (rnMap π g xs) = rnMap π g (m.binds xs) := by
  induction xs generalizing m with
  | nil => rfl
  | cons p xs ih =>
    obtain ⟨x, v⟩ := p
    have hb : (rnMap π g m).bind (π x) (g v) = rnMap π g (m.bind x v) := bind_rnMap hπ g m x v
    simp only [rnMap, List.map_cons, Map.binds_cons] at ih ⊢
    simp only [rnMap] at hb
    rw [hb, ih]

/-! ## Scopes -/

theorem findVal?_rn (ρ : VarEnv) (x : IL.Id) :
    (rnVarEnv π ρ).findVal? (π x) = ρ.findVal? x := by
  simp only [VarEnv.findVal?, rnVarEnv, find?_rnMap, Option.map_id_fun, id_eq]

theorem findTyp?_rn (ρ : VarEnv) (x : IL.Id) :
    (rnVarEnv π ρ).findTyp? (π x) = (ρ.findTyp? x).map (rnTyp π) := by
  simp only [VarEnv.findTyp?, rnVarEnv, find?_rnMap]

theorem findDef?_rn (ρ : VarEnv) (x : IL.Id) :
    (rnVarEnv π ρ).findDef? (π x) = (ρ.findDef? x).map π := by
  simp only [VarEnv.findDef?, rnVarEnv, find?_rnMap]

theorem findGram?_rn (ρ : VarEnv) (x : IL.Id) :
    (rnVarEnv π ρ).findGram? (π x) = (ρ.findGram? x).map (rnSym π) := by
  simp only [VarEnv.findGram?, rnVarEnv, find?_rnMap]

theorem bindVal_rn (hπ : π "_" = "_") (ρ : VarEnv) (x : IL.Id) (v : Value) :
    (rnVarEnv π ρ).bindVal (π x) v = rnVarEnv π (ρ.bindVal x v) := by
  simp only [VarEnv.bindVal, rnVarEnv]
  rw [← bind_rnMap hπ id ρ.vals x v]
  rfl

theorem bindTyp_rn (hπ : π "_" = "_") (ρ : VarEnv) (x : IL.Id) (t : Typ) :
    (rnVarEnv π ρ).bindTyp (π x) (rnTyp π t) = rnVarEnv π (ρ.bindTyp x t) := by
  simp only [VarEnv.bindTyp, rnVarEnv]
  rw [bind_rnMap hπ]

theorem bindDef_rn (hπ : π "_" = "_") (ρ : VarEnv) (x y : IL.Id) :
    (rnVarEnv π ρ).bindDef (π x) (π y) = rnVarEnv π (ρ.bindDef x y) := by
  simp only [VarEnv.bindDef, rnVarEnv]
  rw [bind_rnMap hπ]

theorem bindGram_rn (hπ : π "_" = "_") (ρ : VarEnv) (x : IL.Id) (g : Sym) :
    (rnVarEnv π ρ).bindGram (π x) (rnSym π g) = rnVarEnv π (ρ.bindGram x g) := by
  simp only [VarEnv.bindGram, rnVarEnv]
  rw [bind_rnMap hπ]

theorem bindVals_rn (hπ : π "_" = "_") (ρ : VarEnv) (xs : List (IL.Id × Value)) :
    (rnVarEnv π ρ).bindVals (rnMap π id xs) = rnVarEnv π (ρ.bindVals xs) := by
  simp only [VarEnv.bindVals, rnVarEnv]
  rw [binds_rnMap hπ]

theorem findVals?_rn (ρ : VarEnv) (xs : List IL.Id) :
    (rnVarEnv π ρ).findVals? (xs.map π) = ρ.findVals? xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [VarEnv.findVals?, List.map_cons, List.mapM_cons, findVal?_rn] at ih ⊢
    rw [ih]

theorem empty_rn : rnVarEnv π VarEnv.empty = VarEnv.empty := rfl

/-! ## Environments -/

theorem Env.findTyp?_rn (env : Env) (x : IL.Id) :
    (rnEnv π env).findTyp? (π x) = (env.findTyp? x).map (rnTypDef π) := by
  simp only [Env.findTyp?, rnEnv, find?_rnMap]

theorem Env.findDef?_rn (env : Env) (x : IL.Id) :
    (rnEnv π env).findDef? (π x) = (env.findDef? x).map (rnDefDef π) := by
  simp only [Env.findDef?, rnEnv, find?_rnMap]

theorem Env.findRel?_rn (env : Env) (x : IL.Id) :
    (rnEnv π env).findRel? (π x) = (env.findRel? x).map (rnRelDef π) := by
  simp only [Env.findRel?, rnEnv, find?_rnMap]

theorem Env.findGram?_rn (env : Env) (x : IL.Id) :
    (rnEnv π env).findGram? (π x) = (env.findGram? x).map (rnGramDef π) := by
  simp only [Env.findGram?, rnEnv, find?_rnMap]

theorem Env.memTyp_rn (env : Env) (x : IL.Id) : (rnEnv π env).memTyp (π x) = env.memTyp x := by
  simp only [Env.memTyp, rnEnv, mem_rnMap]

theorem Env.memGram_rn (env : Env) (x : IL.Id) :
    (rnEnv π env).memGram (π x) = env.memGram x := by
  simp only [Env.memGram, rnEnv, mem_rnMap]

theorem Env.builtins_rn (env : Env) (x : IL.Id) (ws : List ArgV) :
    (rnEnv π env).builtins.call (π x) (ws.map (rnArgV π)) = env.builtins.call x ws := by
  simp only [rnEnv, Equiv.symm_apply_apply, rnArgVs_symm]

/-! ## Fuel-free auxiliaries of the evaluator -/

theorem resolveTyp_rn (ρ : VarEnv) (t : Typ) :
    resolveTyp (rnVarEnv π ρ) (rnTyp π t) = rnTyp π (resolveTyp ρ t) := by
  cases t with
  | varT x args =>
    cases args with
    | nil =>
      simp only [rnTyp, rnArgs, resolveTyp, findTyp?_rn]
      cases ρ.findTyp? x <;> rfl
    | cons a args => rfl
  | _ => rfl

theorem resolveSym_rn (ρ : VarEnv) (g : Sym) :
    resolveSym (rnVarEnv π ρ) (rnSym π g) = rnSym π (resolveSym ρ g) := by
  cases g with
  | varG x args =>
    cases args with
    | nil =>
      simp only [rnSym, rnArgs, resolveSym, findGram?_rn]
      cases ρ.findGram? x <;> rfl
    | cons a args => rfl
  | _ => rfl

/-- `Res.ofOption` of a mapped option. -/
theorem ofOption_map {β γ : Type} (g : β → γ) (o : Option β) :
    Res.ofOption (o.map g) = g <$> Res.ofOption o := by
  cases o <;> rfl

theorem matchTypV_rn_other (env : Env) (ρ : VarEnv) (q t : Typ) (hq : ∀ x, q ≠ .varT x []) :
    matchTypV (rnEnv π env) (rnVarEnv π ρ) (rnTyp π q) (rnTyp π t) =
      rnVarEnv π <$> matchTypV env ρ q t := by
  have hq' : ∀ x, rnTyp π q ≠ .varT x [] := by
    intro x hx
    cases q with
    | varT y args =>
      cases args with
      | nil => exact hq y rfl
      | cons a args => simp [rnTyp, rnArgs] at hx
    | _ => simp [rnTyp] at hx
  have e₁ : matchTypV (rnEnv π env) (rnVarEnv π ρ) (rnTyp π q) (rnTyp π t) =
      if typEq (rnTyp π q) (rnTyp π t) then .ok (rnVarEnv π ρ) else .error .undef := by
    unfold matchTypV
    split
    · next _ x h => exact absurd h (hq' x)
    · rfl
  have e₂ : matchTypV env ρ q t = if typEq q t then .ok ρ else .error .undef := by
    unfold matchTypV
    split
    · next _ x => exact absurd rfl (hq x)
    · rfl
  rw [e₁, e₂, typEq_rn]
  split <;> rfl

theorem matchTypV_rn_var (hπ : π "_" = "_") (env : Env) (ρ : VarEnv) (x : IL.Id) (t : Typ) :
    matchTypV (rnEnv π env) (rnVarEnv π ρ) (.varT (π x) []) (rnTyp π t) =
      rnVarEnv π <$> matchTypV env ρ (.varT x []) t := by
  have hv : typEq (.varT (π x) []) (rnTyp π t) = typEq (.varT x []) t := typEq_rn π (.varT x []) t
  simp only [matchTypV, findTyp?_rn, Env.memTyp_rn]
  cases ρ.findTyp? x with
  | some t' =>
    simp only [Option.map_some, typEq_rn]
    split <;> rfl
  | none =>
    simp only [Option.map_none]
    split
    · rw [hv]
      split <;> rfl
    · rw [bindTyp_rn hπ]
      rfl

theorem matchTypV_rn (hπ : π "_" = "_") (env : Env) (ρ : VarEnv) (p t : Typ) :
    matchTypV (rnEnv π env) (rnVarEnv π ρ) (rnTyp π p) (rnTyp π t) =
      rnVarEnv π <$> matchTypV env ρ p t := by
  cases p with
  | varT x args =>
    cases args with
    | nil => exact matchTypV_rn_var hπ env ρ x t
    | cons a args => exact matchTypV_rn_other env ρ _ t fun _ h => by cases h
  | _ => exact matchTypV_rn_other env ρ _ t fun _ h => by cases h

theorem matchSymV_rn_other (env : Env) (ρ : VarEnv) (q t : Sym) (hq : ∀ x, q ≠ .varG x []) :
    matchSymV (rnEnv π env) (rnVarEnv π ρ) (rnSym π q) (rnSym π t) =
      rnVarEnv π <$> matchSymV env ρ q t := by
  have hq' : ∀ x, rnSym π q ≠ .varG x [] := by
    intro x hx
    cases q with
    | varG y args =>
      cases args with
      | nil => exact hq y rfl
      | cons a args => simp [rnSym, rnArgs] at hx
    | _ => simp [rnSym] at hx
  have e₁ : matchSymV (rnEnv π env) (rnVarEnv π ρ) (rnSym π q) (rnSym π t) =
      if symEq (rnSym π q) (rnSym π t) then .ok (rnVarEnv π ρ) else .error .undef := by
    unfold matchSymV
    split
    · next _ x h => exact absurd h (hq' x)
    · rfl
  have e₂ : matchSymV env ρ q t = if symEq q t then .ok ρ else .error .undef := by
    unfold matchSymV
    split
    · next _ x => exact absurd rfl (hq x)
    · rfl
  rw [e₁, e₂, symEq_rn]
  split <;> rfl

theorem matchSymV_rn_var (hπ : π "_" = "_") (env : Env) (ρ : VarEnv) (x : IL.Id) (t : Sym) :
    matchSymV (rnEnv π env) (rnVarEnv π ρ) (.varG (π x) []) (rnSym π t) =
      rnVarEnv π <$> matchSymV env ρ (.varG x []) t := by
  have hv : symEq (.varG (π x) []) (rnSym π t) = symEq (.varG x []) t := symEq_rn π (.varG x []) t
  simp only [matchSymV, findGram?_rn, Env.memGram_rn]
  cases ρ.findGram? x with
  | some t' =>
    simp only [Option.map_some, symEq_rn]
    split <;> rfl
  | none =>
    simp only [Option.map_none]
    split
    · rw [hv]
      split <;> rfl
    · rw [bindGram_rn hπ]
      rfl

theorem matchSymV_rn (hπ : π "_" = "_") (env : Env) (ρ : VarEnv) (p t : Sym) :
    matchSymV (rnEnv π env) (rnVarEnv π ρ) (rnSym π p) (rnSym π t) =
      rnVarEnv π <$> matchSymV env ρ p t := by
  cases p with
  | varG x args =>
    cases args with
    | nil => exact matchSymV_rn_var hπ env ρ x t
    | cons a args => exact matchSymV_rn_other env ρ _ t fun _ h => by cases h
  | _ => exact matchSymV_rn_other env ρ _ t fun _ h => by cases h

theorem bindParams_rn (hπ : π "_" = "_") :
    ∀ (ρ : VarEnv) (ps : List Param) (l : List ArgV),
      bindParams (rnVarEnv π ρ) (rnParams π ps) (l.map (rnArgV π)) =
        (bindParams ρ ps l).map (rnVarEnv π)
  | ρ, [], [] => rfl
  | ρ, .expP x t :: ps, .val v :: l => by
      simp only [rnParams, rnParam, List.map_cons, rnArgV, bindParams]
      rw [bindVal_rn hπ, bindParams_rn hπ]
  | ρ, .typP x :: ps, .typ t :: l => by
      simp only [rnParams, rnParam, List.map_cons, rnArgV, bindParams]
      rw [bindTyp_rn hπ, bindParams_rn hπ]
  | ρ, .defP x qs t :: ps, .defName y :: l => by
      simp only [rnParams, rnParam, List.map_cons, rnArgV, bindParams]
      rw [bindDef_rn hπ, bindParams_rn hπ]
  | ρ, .gramP x qs t :: ps, .gram g :: l => by
      simp only [rnParams, rnParam, List.map_cons, rnArgV, bindParams]
      rw [bindGram_rn hπ, bindParams_rn hπ]
  | ρ, [], _ :: _ => rfl
  | ρ, _ :: _, [] => by
      rename_i p _
      cases p <;> rfl
  | ρ, .expP _ _ :: _, .typ _ :: _ => rfl
  | ρ, .expP _ _ :: _, .defName _ :: _ => rfl
  | ρ, .expP _ _ :: _, .gram _ :: _ => rfl
  | ρ, .typP _ :: _, .val _ :: _ => rfl
  | ρ, .typP _ :: _, .defName _ :: _ => rfl
  | ρ, .typP _ :: _, .gram _ :: _ => rfl
  | ρ, .defP _ _ _ :: _, .val _ :: _ => rfl
  | ρ, .defP _ _ _ :: _, .typ _ :: _ => rfl
  | ρ, .defP _ _ _ :: _, .gram _ :: _ => rfl
  | ρ, .gramP _ _ _ :: _, .val _ :: _ => rfl
  | ρ, .gramP _ _ _ :: _, .typ _ :: _ => rfl
  | ρ, .gramP _ _ _ :: _, .defName _ :: _ => rfl

theorem iterRow_rn (ds : List (IL.Id × List Value)) (ido : Option IL.Id) (i : Nat) :
    iterRow (rnMap π id ds) (ido.map π) i = rnMap π id (iterRow ds ido i) := by
  simp only [iterRow, rnMap, List.map_append, List.filterMap_map]
  congr 1
  · rw [List.map_filterMap]
    congr 1
    funext d
    simp only [Function.comp_apply, id_eq]
    cases d.2[i]? <;> rfl
  · cases ido <;> rfl

theorem iterRows_rn (ds : List (IL.Id × List Value)) (ido : Option IL.Id) (k : Nat) :
    iterRows (rnMap π id ds) (ido.map π) k = (iterRows ds ido k).map (rnMap π id) := by
  simp only [iterRows, List.map_map]
  congr 1
  funext i
  exact iterRow_rn ds ido i

/-- The operator test of `subCaseOk`, on renamed cases. -/
theorem any_rnTypCases (cs : List TypCase) (op : MixopS) :
    ((rnTypCases π cs).any fun | .mk op' _ _ _ => decide (op' = op)) =
      cs.any fun | .mk op' _ _ _ => decide (op' = op) := by
  rw [rnTypCases_eq, List.any_map]
  congr 1
  funext c
  cases c
  rfl

theorem subCaseOk_rn_case (env : Env) (ρ : VarEnv) (x : IL.Id) (op : MixopS) (w : Value) :
    subCaseOk (rnEnv π env) (rnVarEnv π ρ) (.varT (π x) []) (.case op w) =
      subCaseOk env ρ (.varT x []) (.case op w) := by
  simp only [subCaseOk, findTyp?_rn, Env.findTyp?_rn]
  cases ρ.findTyp? x with
  | some _ => rfl
  | none =>
    cases env.findTyp? x with
    | none => rfl
    | some d =>
      obtain ⟨ps, insts⟩ := d
      rcases insts with _ | ⟨⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩, _ | _ | cs⟩, _ | ⟨_, _⟩⟩ <;>
        simp only [Option.map_none, Option.map_some, rnTypDef, rnInsts, rnInst, rnParams,
          rnArgs, rnDefTyp]
      rw [rnTypCases_eq, List.any_map]
      congr 1
      funext c
      cases c
      rfl

theorem subCaseOk_rn (env : Env) (ρ : VarEnv) (t : Typ) (v : Value) :
    subCaseOk (rnEnv π env) (rnVarEnv π ρ) (rnTyp π t) v = subCaseOk env ρ t v := by
  cases t with
  | varT x args =>
    cases args with
    | nil =>
      cases v with
      | case op w => exact subCaseOk_rn_case env ρ x op w
      | _ => rfl
    | cons a args => rfl
  | _ => rfl

theorem argSubOk_rn (env : Env) (ρ : VarEnv) (e : Exp) (v : Value) :
    argSubOk (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) v = argSubOk env ρ e v := by
  cases e with
  | subE e t₁ t₂ => exact subCaseOk_rn env ρ t₁ v
  | _ => rfl

/-! ## The result monad -/

theorem elimUndef_map {β γ δ : Type} (g : β → γ) (r : Res β) (k : γ → Res δ)
    (h : Unit → Res δ) : Res.elimUndef (g <$> r) k h = Res.elimUndef r (k ∘ g) h := by
  rcases r with (_ | _) | _ <;> rfl

theorem assert_map {β γ : Type} (c : Prop) [Decidable c] (g : β → γ) (r : Res β) :
    Res.assert c (g <$> r) = g <$> Res.assert c r := by
  by_cases h : c <;> simp [Res.assert, h]

theorem scan_map {β γ : Type} (g : β → γ) (F : Nat → Res β) :
    ∀ i k, Res.scan (fun j => g <$> F j) i k = g <$> Res.scan F i k
  | i, 0 => rfl
  | i, k + 1 => by
    simp only [Res.scan]
    rw [elimUndef_map, scan_map g F (i + 1) k]
    rcases F i with (_ | _) | _ <;> rfl

end Silmaril.Wasm.SpecTec.Institution.Perm
