module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.PermBasic

/-!
# Renaming identifiers: equivariance of the evaluator

`EqvAt π n` says that every member of the evaluator's mutual block (`Sem.evalExp` …
`Sem.anyRule`), at fuel `n`, commutes with renaming every identifier by the permutation `π`: on
the renamed environment, scope and syntax it computes the renamed result. Values carry no
identifiers, so value results are equal; scopes and evaluated arguments are renamed.
`eqvAt_zero` and `eqvAt_succ` prove it at every fuel, so `eqvAt π hπ n` holds for every `n` when
`π` fixes the wildcard `"_"`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Perm

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- Equivariance of every member of the evaluator's mutual block at fuel `n`. -/
structure EqvAt (π : Equiv.Perm IL.Id) (n : Nat) : Prop where
  exp : ∀ env ρ e, evalExp n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) = evalExp n env ρ e
  exps : ∀ env ρ es, evalExps n (rnEnv π env) (rnVarEnv π ρ) (rnExps π es) = evalExps n env ρ es
  expFields : ∀ env ρ fs, evalExpFields n (rnEnv π env) (rnVarEnv π ρ) (rnExpFields π fs) =
    evalExpFields n env ρ fs
  arg : ∀ env ρ a, evalArg n (rnEnv π env) (rnVarEnv π ρ) (rnArg π a) =
    rnArgV π <$> evalArg n env ρ a
  args : ∀ env ρ l, evalArgs n (rnEnv π env) (rnVarEnv π ρ) (rnArgs π l) =
    List.map (rnArgV π) <$> evalArgs n env ρ l
  doms : ∀ env ρ ds, evalDoms n (rnEnv π env) (rnVarEnv π ρ) (rnDoms π ds) =
    rnMap π id <$> evalDoms n env ρ ds
  iterE : ∀ env ρ e it ds, evalIterE n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (rnIter π it)
    (rnDoms π ds) = evalIterE n env ρ e it ds
  iterList : ∀ env ρ e xvs ido k, evalIterList n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e)
    (rnMap π id xvs) (ido.map π) k = evalIterList n env ρ e xvs ido k
  rounds : ∀ env ρ e rs, evalRounds n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e)
    (rs.map (rnMap π id)) = evalRounds n env ρ e rs
  pathGet : ∀ env ρ v p, pathGet n (rnEnv π env) (rnVarEnv π ρ) v (rnPath π p) =
    pathGet n env ρ v p
  pathSet : ∀ env ρ v p w, pathSet n (rnEnv π env) (rnVarEnv π ρ) v (rnPath π p) w =
    pathSet n env ρ v p w
  patLen : ∀ env ρ e, patLen n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) = patLen n env ρ e
  matchExp : ∀ env ρ e v, matchExp n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) v =
    rnVarEnv π <$> matchExp n env ρ e v
  matchDefault : ∀ env ρ e v, matchDefault n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) v =
    rnVarEnv π <$> matchDefault n env ρ e v
  matchExps : ∀ env ρ es vs, matchExps n (rnEnv π env) (rnVarEnv π ρ) (rnExps π es) vs =
    rnVarEnv π <$> matchExps n env ρ es vs
  matchExpFields : ∀ env ρ fs gs, matchExpFields n (rnEnv π env) (rnVarEnv π ρ)
    (rnExpFields π fs) gs = rnVarEnv π <$> matchExpFields n env ρ fs gs
  matchIterE : ∀ env ρ e it ds v, matchIterE n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e)
    (rnIter π it) (rnDoms π ds) v = rnVarEnv π <$> matchIterE n env ρ e it ds v
  matchIterList : ∀ env ρ e ds ido vs, matchIterList n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e)
    (rnDoms π ds) (ido.map π) vs = rnVarEnv π <$> matchIterList n env ρ e ds ido vs
  matchRounds : ∀ env ρ e xs ido i vs, matchRounds n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e)
    (xs.map π) (ido.map π) i vs = matchRounds n env ρ e xs ido i vs
  matchArg : ∀ env ρ a w, matchArg n (rnEnv π env) (rnVarEnv π ρ) (rnArg π a) (rnArgV π w) =
    rnVarEnv π <$> matchArg n env ρ a w
  matchArgs : ∀ env ρ l ws, matchArgs n (rnEnv π env) (rnVarEnv π ρ) (rnArgs π l)
    (ws.map (rnArgV π)) = rnVarEnv π <$> matchArgs n env ρ l ws
  callDef : ∀ env ρ x l, callDef n (rnEnv π env) (rnVarEnv π ρ) (π x) (rnArgs π l) =
    callDef n env ρ x l
  tryClauses : ∀ env cs ws, tryClauses n (rnEnv π env) (rnClauses π cs) (ws.map (rnArgV π)) =
    tryClauses n env cs ws
  premHolds : ∀ env ρ pr, premHolds n (rnEnv π env) (rnVarEnv π ρ) (rnPrem π pr) =
    rnVarEnv π <$> premHolds n env ρ pr
  premsHold : ∀ env ρ prs, premsHold n (rnEnv π env) (rnVarEnv π ρ) (rnPrems π prs) =
    rnVarEnv π <$> premsHold n env ρ prs
  premIter : ∀ env ρ pr it ds, premIter n (rnEnv π env) (rnVarEnv π ρ) (rnPrem π pr)
    (rnIter π it) (rnDoms π ds) = rnVarEnv π <$> premIter n env ρ pr it ds
  premRounds : ∀ env ρ pr xvs ido k, premRounds n (rnEnv π env) (rnVarEnv π ρ) (rnPrem π pr)
    (rnMap π id xvs) (ido.map π) k = rnVarEnv π <$> premRounds n env ρ pr xvs ido k
  derives : ∀ env x op ws v, derives n (rnEnv π env) (π x) op (ws.map (rnArgV π)) v =
    derives n env x op ws v
  anyRule : ∀ env op ps ws v rs, anyRule n (rnEnv π env) op (rnParams π ps)
    (ws.map (rnArgV π)) v (rnRules π rs) = anyRule n env op ps ws v rs

/-! ## Helpers for the result monad -/

section Helpers

variable {α β γ : Type}

theorem mapM_map_of {f : α → β} {g : β → Res γ} {h : α → Res γ} (hh : ∀ a, g (f a) = h a) :
    ∀ l : List α, (l.map f).mapM g = l.mapM h
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.mapM_cons, hh, mapM_map_of hh l]

theorem mapM_map_of' {f : α → β} {g : β → Res γ} {h : α → Res γ} {k : γ → γ}
    (hh : ∀ a, g (f a) = k <$> h a) :
    ∀ l : List α, (l.map f).mapM g = List.map k <$> l.mapM h
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.mapM_cons, hh, mapM_map_of' hh l, bind_map_left, map_bind,
      map_pure, List.map_cons]

theorem map_elimUndef (g : β → γ) (r : Res α) (k : α → Res β) (h : Unit → Res β) :
    g <$> Res.elimUndef r k h = Res.elimUndef r (fun a => g <$> k a) (fun u => g <$> h u) := by
  rcases r with (_ | _) | _ <;> rfl

theorem map_assert (c : Prop) [Decidable c] (g : β → γ) (r : Res β) :
    g <$> Res.assert c r = Res.assert c (g <$> r) := (assert_map c g r).symm

theorem map_scan (g : β → γ) (F : Nat → Res β) (i k : Nat) :
    g <$> Res.scan F i k = Res.scan (fun j => g <$> F j) i k := (scan_map g F i k).symm

theorem map_ite (c : Prop) [Decidable c] (g : β → γ) (a b : Res β) :
    g <$> (if c then a else b) = if c then g <$> a else g <$> b := by
  by_cases h : c <;> simp [h]

theorem map_error (g : β → γ) (e : Stuck) : g <$> (Except.error e : Res β) = .error e := rfl

theorem map_ok (g : β → γ) (b : β) : g <$> (Except.ok b : Res β) = .ok (g b) := rfl

theorem error_bind (e : Stuck) (k : β → Res γ) : (Except.error e : Res β) >>= k = .error e := rfl

theorem ok_bind (b : β) (k : β → Res γ) : (Except.ok b : Res β) >>= k = k b := rfl

theorem getD_map_perm (π : Equiv.Perm IL.Id) (o : Option IL.Id) (x : IL.Id) :
    (o.map π).getD (π x) = π (o.getD x) := by
  cases o <;> rfl

end Helpers

variable {π : Equiv.Perm IL.Id}

theorem eqvAt_zero : EqvAt π 0 := by
  constructor <;> intros <;>
    simp only [evalExp, evalExps, evalExpFields, evalArg, evalArgs, evalDoms, evalIterE,
      evalIterList, evalRounds, Sem.pathGet, Sem.pathSet, Sem.patLen, Sem.matchExp,
      Sem.matchDefault, Sem.matchExps, Sem.matchExpFields, Sem.matchIterE, Sem.matchIterList,
      Sem.matchRounds, Sem.matchArg, Sem.matchArgs, Sem.callDef, Sem.tryClauses, Sem.premHolds,
      Sem.premsHold, Sem.premIter, Sem.premRounds, Sem.derives, Sem.anyRule] <;> rfl


variable {n : Nat}

theorem EqvAt.exp_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (e : Exp) :
    evalExp (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) = evalExp (n + 1) env ρ e := by
  cases e with
  | optE eo => cases eo <;> simp only [rnExp, rnExpOpt, evalExp, ih.exp]
  | iterE e it =>
    cases it
    simp only [rnExp, rnIterExp, evalExp, ih.iterE]
  | _ =>
    simp only [rnExp, evalExp, ih.exp, ih.exps, ih.expFields, ih.pathGet, ih.pathSet,
      ih.callDef, findVal?_rn]


theorem EqvAt.exps_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (es : List Exp) :
    evalExps (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExps π es) = evalExps (n + 1) env ρ es := by
  simp only [evalExps, rnExps_eq]
  exact mapM_map_of (ih.exp env ρ) es

theorem EqvAt.expFields_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (fs : List ExpField) :
    evalExpFields (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExpFields π fs) =
      evalExpFields (n + 1) env ρ fs := by
  simp only [evalExpFields, rnExpFields_eq]
  refine mapM_map_of (fun c => ?_) fs
  cases c
  simp only [rnExpField, ih.exp]

theorem EqvAt.arg_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (a : Arg) :
    evalArg (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnArg π a) =
      rnArgV π <$> evalArg (n + 1) env ρ a := by
  cases a with
  | expA e =>
    simp only [rnArg, evalArg, ih.exp, Functor.map_map]
    rfl
  | typA t => simp only [rnArg, evalArg, resolveTyp_rn, map_ok, rnArgV]
  | defA x => simp only [rnArg, evalArg, findDef?_rn, getD_map_perm, map_ok, rnArgV]
  | gramA g => simp only [rnArg, evalArg, resolveSym_rn, map_ok, rnArgV]

theorem EqvAt.args_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (l : List Arg) :
    evalArgs (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnArgs π l) =
      List.map (rnArgV π) <$> evalArgs (n + 1) env ρ l := by
  simp only [evalArgs, rnArgs_eq]
  exact mapM_map_of' (ih.arg env ρ) l

theorem EqvAt.doms_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (ds : List Dom) :
    evalDoms (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnDoms π ds) =
      rnMap π id <$> evalDoms (n + 1) env ρ ds := by
  simp only [evalDoms, rnDoms_eq]
  refine mapM_map_of' (fun d => ?_) ds
  simp only [domVar_rn, domSrc_rn, ih.exp, Functor.map_map]
  rfl

theorem EqvAt.rounds_succ (hπ : π "_" = "_") (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (e : Exp)
    (rs : List (List (IL.Id × Value))) :
    evalRounds (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (rs.map (rnMap π id)) =
      evalRounds (n + 1) env ρ e rs := by
  simp only [evalRounds]
  exact mapM_map_of (fun r => by rw [bindVals_rn hπ, ih.exp]) rs

theorem EqvAt.pathGet_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (v : Value) (p : Path) :
    Sem.pathGet (n + 1) (rnEnv π env) (rnVarEnv π ρ) v (rnPath π p) =
      Sem.pathGet (n + 1) env ρ v p := by
  cases p <;> simp only [rnPath, Sem.pathGet, ih.pathGet, ih.exp]

theorem EqvAt.pathSet_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (v : Value) (p : Path)
    (w : Value) :
    Sem.pathSet (n + 1) (rnEnv π env) (rnVarEnv π ρ) v (rnPath π p) w =
      Sem.pathSet (n + 1) env ρ v p w := by
  cases p <;> simp only [rnPath, Sem.pathSet, ih.pathGet, ih.pathSet, ih.exp]


theorem rnExp_eq_listE {e : Exp} {es : List Exp} (h : rnExp π e = .listE es) :
    ∃ es', e = .listE es' := by
  cases e <;> simp [rnExp] at h ⊢

theorem rnExp_eq_catE {e a b : Exp} (h : rnExp π e = .catE a b) : ∃ a' b', e = .catE a' b' := by
  cases e <;> simp [rnExp] at h ⊢

theorem rnExp_eq_iterListN {e a eₙ : Exp} {x : Option IL.Id} {ds : List Dom}
    (h : rnExp π e = .iterE a (.mk (.listN eₙ x) ds)) :
    ∃ a' eₙ' x' ds', e = .iterE a' (.mk (.listN eₙ' x') ds') := by
  cases e with
  | iterE b it =>
    obtain ⟨i, ds'⟩ := it
    cases i <;> simp [rnExp, rnIterExp, rnIter] at h ⊢
  | _ => simp [rnExp] at h

/-- `patLen` away from its three special shapes: evaluate and take the length. -/
theorem patLen_default {env : Env} {ρ : VarEnv} {e : Exp} (h₁ : ∀ es, e ≠ .listE es)
    (h₂ : ∀ a b, e ≠ .catE a b) (h₃ : ∀ a eₙ x ds, e ≠ .iterE a (.mk (.listN eₙ x) ds)) :
    Sem.patLen (n + 1) env ρ e = evalExp n env ρ e >>= fun v => Res.ofOption v.len? := by
  cases e with
  | listE es => exact absurd rfl (h₁ es)
  | catE a b => exact absurd rfl (h₂ a b)
  | iterE a it =>
    obtain ⟨i, ds⟩ := it
    cases i with
    | listN eₙ x => exact absurd rfl (h₃ a eₙ x ds)
    | _ => simp only [Sem.patLen]
  | optE eo => cases eo <;> simp only [Sem.patLen]
  | _ => simp only [Sem.patLen]

theorem EqvAt.patLen_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (e : Exp) :
    Sem.patLen (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) = Sem.patLen (n + 1) env ρ e := by
  by_cases hs : (∃ es, e = .listE es) ∨ (∃ a b, e = .catE a b) ∨
      ∃ a eₙ x ds, e = .iterE a (.mk (.listN eₙ x) ds)
  · rcases hs with ⟨es, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, eₙ, x, ds, rfl⟩
    · simp only [rnExp, Sem.patLen, rnExps_eq, List.length_map]
    · simp only [rnExp, Sem.patLen, ih.patLen]
    · simp only [rnExp, rnIterExp, rnIter, Sem.patLen, ih.exp]
  · show Sem.patLen (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) = Sem.patLen (n + 1) env ρ e
    have h₁ : ∀ es, e ≠ .listE es := fun es h => hs (.inl ⟨es, h⟩)
    have h₂ : ∀ a b, e ≠ .catE a b := fun a b h => hs (.inr (.inl ⟨a, b, h⟩))
    have h₃ : ∀ a eₙ x ds, e ≠ .iterE a (.mk (.listN eₙ x) ds) :=
      fun a eₙ x ds h => hs (.inr (.inr ⟨a, eₙ, x, ds, h⟩))
    have r₁ : ∀ es, rnExp π e ≠ .listE es := fun es h => by
      obtain ⟨es', rfl⟩ := rnExp_eq_listE h
      exact h₁ es' rfl
    have r₂ : ∀ a b, rnExp π e ≠ .catE a b := fun a b h => by
      obtain ⟨a', b', rfl⟩ := rnExp_eq_catE h
      exact h₂ a' b' rfl
    have r₃ : ∀ a eₙ x ds, rnExp π e ≠ .iterE a (.mk (.listN eₙ x) ds) := fun a eₙ x ds h => by
      obtain ⟨a', eₙ', x', ds', rfl⟩ := rnExp_eq_iterListN h
      exact h₃ a' eₙ' x' ds' rfl
    rw [patLen_default r₁ r₂ r₃, patLen_default h₁ h₂ h₃, ih.exp]

/-- Renaming the keys of a list of bindings commutes with a key-preserving `mapM`. -/
theorem mapM_keys_rn {β : Type} (p : Value → Option β) (xvs : List (IL.Id × Value)) :
    (rnMap π id xvs).mapM (fun q => (p q.2).map fun o => (q.1, o)) =
      (xvs.mapM fun q => (p q.2).map fun o => (q.1, o)).map (rnMap π id) := by
  induction xvs with
  | nil => rfl
  | cons q xvs ih =>
    simp only [rnMap, List.map_cons, List.mapM_cons, id_eq] at ih ⊢
    rw [ih]
    cases p q.2 <;> cases xvs.mapM (fun q => (p q.2).map fun o => (q.1, o)) <;> rfl

theorem head?_rnMap (xvs : List (IL.Id × Value)) :
    (rnMap π id xvs).head? = xvs.head?.map (fun q => (π q.1, q.2)) := by
  cases xvs <;> rfl

theorem all_rnMap {β : Type} (q : IL.Id × β → Bool) (os : List (IL.Id × β)) :
    (rnMap π id os).all q = os.all (fun r => q (π r.1, r.2)) := by
  simp only [rnMap, List.all_map]
  rfl

theorem filterMap_rnMap (os : List (IL.Id × Option Value)) :
    (rnMap π id os).filterMap (fun r => r.2.map fun w => (r.1, w)) =
      rnMap π id (os.filterMap fun r => r.2.map fun w => (r.1, w)) := by
  simp only [rnMap, List.filterMap_map, List.map_filterMap]
  congr 1
  funext r
  simp only [Function.comp_apply, id_eq]
  cases r.2 <;> rfl

theorem isEmpty_rnDoms (ds : List Dom) : (rnDoms π ds).isEmpty = ds.isEmpty := by
  rw [rnDoms_eq, List.isEmpty_map]


theorem EqvAt.iterList_none (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (e : Exp)
    (xvs : List (IL.Id × Value)) (k : Nat) :
    evalIterList n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (rnMap π id xvs) none k =
      evalIterList n env ρ e xvs none k :=
  ih.iterList env ρ e xvs none k

theorem EqvAt.iterE_succ (hπ : π "_" = "_") (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (e : Exp)
    (it : Iter) (ds : List Dom) :
    evalIterE (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (rnIter π it) (rnDoms π ds) =
      evalIterE (n + 1) env ρ e it ds := by
  cases it with
  | opt =>
    simp only [rnIter, evalIterE, ih.doms, bind_map_left, isEmpty_rnDoms, mapM_keys_rn,
      ofOption_map, all_rnMap, filterMap_rnMap, bindVals_rn hπ, ih.exp]
  | listN eₙ x =>
    simp only [rnIter, evalIterE, ih.doms, bind_map_left, ih.exp, rnIdOpt_eq, ih.iterList]
  | _ =>
    simp only [rnIter, evalIterE, ih.doms, bind_map_left, isEmpty_rnDoms, head?_rnMap,
      Option.bind_map, Function.comp_def, ih.iterList_none]

/-- Renaming the keys commutes with reading every binding as a list. -/
theorem mapM_asList_rn (xvs : List (IL.Id × Value)) :
    (rnMap π id xvs).mapM (fun p : IL.Id × Value => p.2.asList?.map fun l => (p.1, l)) =
      (xvs.mapM fun p : IL.Id × Value => p.2.asList?.map fun l => (p.1, l)).map (rnMap π id) :=
  mapM_keys_rn Value.asList? xvs

theorem EqvAt.iterList_succ (ih : EqvAt π n) (env : Env) (ρ : VarEnv) (e : Exp)
    (xvs : List (IL.Id × Value)) (ido : Option IL.Id) (k : Nat) :
    evalIterList (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (rnMap π id xvs) (ido.map π) k =
      evalIterList (n + 1) env ρ e xvs ido k := by
  simp only [evalIterList, mapM_asList_rn, ofOption_map, bind_map_left, iterRows_rn, ih.rounds,
    all_rnMap]

section Match

variable (env : Env) (ρ : VarEnv)

theorem EqvAt.matchExp_succ_unE (ih : EqvAt π n) (op : UnOp) (t : OpTyp) (e : Exp) (v : Value) :
    Sem.matchExp (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π (.unE op t e)) v =
      rnVarEnv π <$> Sem.matchExp (n + 1) env ρ (.unE op t e) v := by
  have hd : Sem.matchDefault n (rnEnv π env) (rnVarEnv π ρ) (.unE op t (rnExp π e)) v =
      rnVarEnv π <$> Sem.matchDefault n env ρ (.unE op t e) v :=
    ih.matchDefault env ρ (.unE op t e) v
  cases op <;> cases v <;>
    simp only [rnExp, Sem.matchExp, ih.matchExp, map_assert, map_bind, hd]

theorem EqvAt.matchExp_succ_cvtE (ih : EqvAt π n) (e : Exp) (t₁ t₂ : NumTyp) (v : Value) :
    Sem.matchExp (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π (.cvtE e t₁ t₂)) v =
      rnVarEnv π <$> Sem.matchExp (n + 1) env ρ (.cvtE e t₁ t₂) v := by
  have hd : Sem.matchDefault n (rnEnv π env) (rnVarEnv π ρ) (.cvtE (rnExp π e) t₁ t₂) v =
      rnVarEnv π <$> Sem.matchDefault n env ρ (.cvtE e t₁ t₂) v :=
    ih.matchDefault env ρ (.cvtE e t₁ t₂) v
  cases v <;> simp only [rnExp, Sem.matchExp, ih.matchExp, map_bind, hd]

theorem EqvAt.matchExp_succ_projE (ih : EqvAt π n) (e : Exp) (i : Int) (v : Value) :
    Sem.matchExp (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π (.projE e i)) v =
      rnVarEnv π <$> Sem.matchExp (n + 1) env ρ (.projE e i) v := by
  have hd : Sem.matchDefault n (rnEnv π env) (rnVarEnv π ρ) (.projE (rnExp π e) i) v =
      rnVarEnv π <$> Sem.matchDefault n env ρ (.projE e i) v :=
    ih.matchDefault env ρ (.projE e i) v
  simp only [rnExp, Sem.matchExp, ih.matchExp, map_ite, hd]

theorem EqvAt.matchExp_succ_catE (ih : EqvAt π n) (e₁ e₂ : Exp) (v : Value) :
    Sem.matchExp (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π (.catE e₁ e₂)) v =
      rnVarEnv π <$> Sem.matchExp (n + 1) env ρ (.catE e₁ e₂) v := by
  simp only [rnExp, Sem.matchExp, ih.matchExp, ih.patLen, map_bind, map_elimUndef, map_assert,
    map_scan, bind_map_left]

theorem matchExp_succ_varE (hπ : π "_" = "_") (x : IL.Id) (v : Value) :
    Sem.matchExp (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π (.varE x)) v =
      rnVarEnv π <$> Sem.matchExp (n + 1) env ρ (.varE x) v := by
  simp only [rnExp, Sem.matchExp, findVal?_rn]
  cases ρ.findVal? x with
  | some w => simp only [map_ite, map_ok, map_error]
  | none => simp only [map_ok, bindVal_rn hπ]

theorem EqvAt.matchExp_succ (hπ : π "_" = "_") (ih : EqvAt π n) (e : Exp) (v : Value) :
    Sem.matchExp (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) v =
      rnVarEnv π <$> Sem.matchExp (n + 1) env ρ e v := by
  cases e with
  | varE x => exact matchExp_succ_varE env ρ hπ x v
  | unE op t e => exact ih.matchExp_succ_unE env ρ op t e v
  | projE e i => exact ih.matchExp_succ_projE env ρ e i v
  | catE e₁ e₂ => exact ih.matchExp_succ_catE env ρ e₁ e₂ v
  | cvtE e t₁ t₂ => exact ih.matchExp_succ_cvtE env ρ e t₁ t₂ v
  | iterE e it =>
    obtain ⟨i, ds⟩ := it
    simp only [rnExp, rnIterExp, Sem.matchExp, ih.matchIterE]
  | optE eo =>
    cases eo <;> simp only [rnExp, rnExpOpt, Sem.matchExp, ih.matchExp, map_assert, map_ok,
      map_bind]
  | binE op t e₁ e₂ =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.binE op t e₁ e₂) v
  | cmpE op t e₁ e₂ =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.cmpE op t e₁ e₂) v
  | theE e =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.theE e) v
  | dotE e a =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.dotE e a) v
  | compE e₁ e₂ =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.compE e₁ e₂) v
  | liftE e =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.liftE e) v
  | memE e₁ e₂ =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.memE e₁ e₂) v
  | lenE e =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.lenE e) v
  | idxE e₁ e₂ =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.idxE e₁ e₂) v
  | sliceE e₁ e₂ e₃ =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.sliceE e₁ e₂ e₃) v
  | updE e₁ p e₂ =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.updE e₁ p e₂) v
  | extE e₁ p e₂ =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.extE e₁ p e₂) v
  | callE x l =>
    simp only [rnExp, Sem.matchExp]
    exact ih.matchDefault env ρ (.callE x l) v
  | _ =>
    simp only [rnExp, Sem.matchExp, ih.matchExp, ih.matchExps, ih.matchExpFields, map_assert,
      map_ok, map_bind]

end Match

section Rest

variable (env : Env) (ρ : VarEnv)

theorem EqvAt.matchDefault_succ (ih : EqvAt π n) (e : Exp) (v : Value) :
    Sem.matchDefault (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) v =
      rnVarEnv π <$> Sem.matchDefault (n + 1) env ρ e v := by
  simp only [Sem.matchDefault, ih.exp, map_bind, map_assert, map_ok]

theorem EqvAt.matchExps_succ (ih : EqvAt π n) (es : List Exp) (vs : List Value) :
    Sem.matchExps (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExps π es) vs =
      rnVarEnv π <$> Sem.matchExps (n + 1) env ρ es vs := by
  cases es <;> cases vs <;>
    simp only [rnExps, Sem.matchExps, ih.matchExp, ih.matchExps, bind_map_left, map_bind,
      map_ok, map_error]

theorem EqvAt.matchExpFields_succ (ih : EqvAt π n) (fs : List ExpField)
    (gs : List (AtomS × Value)) :
    Sem.matchExpFields (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExpFields π fs) gs =
      rnVarEnv π <$> Sem.matchExpFields (n + 1) env ρ fs gs := by
  rcases fs with _ | ⟨⟨a, e⟩, fs⟩ <;> cases gs <;>
    simp only [rnExpFields, rnExpField, Sem.matchExpFields, ih.matchExp, ih.matchExpFields,
      bind_map_left, map_bind, map_assert, map_ok, map_error]

theorem domSrc_rnDoms (ds : List Dom) : (rnDoms π ds).map domSrc = rnExps π (ds.map domSrc) := by
  simp only [rnDoms_eq, rnExps_eq, List.map_map]
  congr 1
  funext d
  exact domSrc_rn π d

theorem domVar_rnDoms (ds : List Dom) : (rnDoms π ds).map domVar = (ds.map domVar).map π := by
  simp only [rnDoms_eq, List.map_map]
  congr 1
  funext d
  exact domVar_rn π d

theorem const_rnDoms {β : Type} (b : β) (ds : List Dom) :
    (rnDoms π ds).map (fun _ => b) = ds.map (fun _ => b) := by
  simp only [rnDoms_eq, List.map_map]
  rfl

theorem length_rnDoms (ds : List Dom) : (rnDoms π ds).length = ds.length := by
  rw [rnDoms_eq, List.length_map]

theorem EqvAt.matchRounds_none (ih : EqvAt π n) (e : Exp) (xs : List IL.Id) (i : Nat)
    (vs : List Value) :
    Sem.matchRounds n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (xs.map π) none i vs =
      Sem.matchRounds n env ρ e xs none i vs :=
  ih.matchRounds env ρ e xs none i vs

theorem EqvAt.matchRounds_some (ih : EqvAt π n) (e : Exp) (xs : List IL.Id) (y : IL.Id) (i : Nat)
    (vs : List Value) :
    Sem.matchRounds n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (xs.map π) (some (π y)) i vs =
      Sem.matchRounds n env ρ e xs (some y) i vs :=
  ih.matchRounds env ρ e xs (some y) i vs

theorem EqvAt.matchIterList_none (ih : EqvAt π n) (e : Exp) (ds : List Dom) (vs : List Value) :
    Sem.matchIterList n (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (rnDoms π ds) none vs =
      rnVarEnv π <$> Sem.matchIterList n env ρ e ds none vs :=
  ih.matchIterList env ρ e ds none vs

theorem EqvAt.matchRounds_succ (hπ : π "_" = "_") (ih : EqvAt π n) (e : Exp) (xs : List IL.Id)
    (ido : Option IL.Id) (i : Nat) (vs : List Value) :
    Sem.matchRounds (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (xs.map π) (ido.map π) i vs =
      Sem.matchRounds (n + 1) env ρ e xs ido i vs := by
  cases vs with
  | nil => simp only [Sem.matchRounds]
  | cons v vs =>
    cases ido <;>
      simp only [Sem.matchRounds, Option.map_some, Option.map_none, bindVal_rn hπ, ih.matchExp,
        bind_map_left, findVals?_rn, ih.matchRounds_none, ih.matchRounds_some]

theorem EqvAt.matchIterList_succ (ih : EqvAt π n) (e : Exp) (ds : List Dom) (ido : Option IL.Id)
    (vs : List Value) :
    Sem.matchIterList (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (rnDoms π ds) (ido.map π)
      vs = rnVarEnv π <$> Sem.matchIterList (n + 1) env ρ e ds ido vs := by
  simp only [Sem.matchIterList, domVar_rnDoms, ih.matchRounds, domSrc_rnDoms, length_rnDoms,
    ih.matchExps, map_bind]

theorem EqvAt.matchIterE_succ (ih : EqvAt π n) (e : Exp) (it : Iter) (ds : List Dom)
    (v : Value) :
    Sem.matchIterE (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnExp π e) (rnIter π it) (rnDoms π ds) v =
      rnVarEnv π <$> Sem.matchIterE (n + 1) env ρ e it ds v := by
  cases it with
  | opt =>
    simp only [rnIter, Sem.matchIterE]
    cases v.asOpt? with
    | none => simp only [Res.ofOption, error_bind, map_error]
    | some o =>
      cases o <;>
        simp only [Res.ofOption, ok_bind, domSrc_rnDoms, const_rnDoms, ih.matchExps,
          ih.matchExp, bind_map_left, domVar_rnDoms, findVals?_rn, map_bind]
  | listN eₙ x =>
    simp only [rnIter, Sem.matchIterE, ih.matchExp, bind_map_left, rnIdOpt_eq, ih.matchIterList,
      map_bind]
  | _ =>
    simp only [rnIter, Sem.matchIterE, ih.matchIterList_none, map_bind, map_assert]

theorem EqvAt.matchArg_succ (hπ : π "_" = "_") (ih : EqvAt π n) (a : Arg) (w : ArgV) :
    Sem.matchArg (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnArg π a) (rnArgV π w) =
      rnVarEnv π <$> Sem.matchArg (n + 1) env ρ a w := by
  cases a <;> cases w <;>
    simp only [rnArg, rnArgV, Sem.matchArg, argSubOk_rn, ih.matchExp, map_ite, map_error,
      matchTypV_rn hπ, matchSymV_rn hπ, bindDef_rn hπ, map_ok]

theorem EqvAt.matchArgs_succ (ih : EqvAt π n) (l : List Arg) (ws : List ArgV) :
    Sem.matchArgs (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnArgs π l) (ws.map (rnArgV π)) =
      rnVarEnv π <$> Sem.matchArgs (n + 1) env ρ l ws := by
  cases l <;> cases ws <;>
    simp only [rnArgs, List.map_nil, List.map_cons, Sem.matchArgs, ih.matchArg, ih.matchArgs,
      bind_map_left, map_bind, map_ok, map_error]

theorem rnDefDef_clauses (d : DefDef) : (rnDefDef π d).2.2 = rnClauses π d.2.2 := rfl

theorem EqvAt.callDef_succ (ih : EqvAt π n) (x : IL.Id) (l : List Arg) :
    Sem.callDef (n + 1) (rnEnv π env) (rnVarEnv π ρ) (π x) (rnArgs π l) =
      Sem.callDef (n + 1) env ρ x l := by
  simp only [Sem.callDef, ih.args, bind_map_left, findDef?_rn, getD_map_perm, Env.findDef?_rn,
    ofOption_map, rnDefDef_clauses, ih.tryClauses, Env.builtins_rn]

theorem EqvAt.matchArgs_empty (ih : EqvAt π n) (l : List Arg) (ws : List ArgV) :
    Sem.matchArgs n (rnEnv π env) VarEnv.empty (rnArgs π l) (ws.map (rnArgV π)) =
      rnVarEnv π <$> Sem.matchArgs n env VarEnv.empty l ws :=
  ih.matchArgs env VarEnv.empty l ws

theorem EqvAt.tryClauses_succ (ih : EqvAt π n) (cs : List Clause) (ws : List ArgV) :
    Sem.tryClauses (n + 1) (rnEnv π env) (rnClauses π cs) (ws.map (rnArgV π)) =
      Sem.tryClauses (n + 1) env cs ws := by
  rcases cs with _ | ⟨⟨qs, pats, e, prems⟩, cs⟩
  · simp only [rnClauses, Sem.tryClauses]
  · simp only [rnClauses, rnClause, Sem.tryClauses, ih.matchArgs_empty, bind_map_left,
      ih.premsHold, ← map_bind, elimUndef_map, Function.comp_def, ih.exp, ih.tryClauses]

theorem EqvAt.premHolds_succ (ih : EqvAt π n) (pr : Prem) :
    Sem.premHolds (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnPrem π pr) =
      rnVarEnv π <$> Sem.premHolds (n + 1) env ρ pr := by
  cases pr with
  | iterPr pr it =>
    obtain ⟨i, ds⟩ := it
    simp only [rnPrem, rnIterExp, Sem.premHolds, ih.premIter]
  | _ =>
    simp only [rnPrem, Sem.premHolds, ih.exp, ih.args, ih.matchExp, ih.derives, bind_map_left,
      map_bind, map_assert, map_ok, map_ite, map_error]

/-- `foldlM` of renamed premises. -/
theorem EqvAt.foldlM_premHolds (ih : EqvAt π n) :
    ∀ (prs : List Prem) (ρ : VarEnv),
      (rnPrems π prs).foldlM (fun ρ' pr => Sem.premHolds n (rnEnv π env) ρ' pr) (rnVarEnv π ρ) =
        rnVarEnv π <$> prs.foldlM (fun ρ' pr => Sem.premHolds n env ρ' pr) ρ
  | [], _ => rfl
  | pr :: prs, ρ => by
    simp only [rnPrems, List.foldlM_cons, ih.premHolds, bind_map_left, map_bind,
      ih.foldlM_premHolds prs]

theorem EqvAt.premsHold_succ (ih : EqvAt π n) (prs : List Prem) :
    Sem.premsHold (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnPrems π prs) =
      rnVarEnv π <$> Sem.premsHold (n + 1) env ρ prs := by
  simp only [Sem.premsHold]
  exact ih.foldlM_premHolds env prs ρ

theorem EqvAt.premRounds_none (ih : EqvAt π n) (pr : Prem) (xvs : List (IL.Id × Value))
    (k : Nat) :
    Sem.premRounds n (rnEnv π env) (rnVarEnv π ρ) (rnPrem π pr) (rnMap π id xvs) none k =
      rnVarEnv π <$> Sem.premRounds n env ρ pr xvs none k :=
  ih.premRounds env ρ pr xvs none k

theorem EqvAt.premIter_succ (hπ : π "_" = "_") (ih : EqvAt π n) (pr : Prem) (it : Iter)
    (ds : List Dom) :
    Sem.premIter (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnPrem π pr) (rnIter π it) (rnDoms π ds) =
      rnVarEnv π <$> Sem.premIter (n + 1) env ρ pr it ds := by
  cases it with
  | opt =>
    simp only [rnIter, Sem.premIter, ih.doms, bind_map_left, isEmpty_rnDoms, mapM_keys_rn,
      ofOption_map, all_rnMap, filterMap_rnMap, bindVals_rn hπ, ih.premHolds, map_bind,
      map_assert, map_ite, map_ok, map_error]
  | listN eₙ x =>
    simp only [rnIter, Sem.premIter, ih.doms, bind_map_left, ih.exp, rnIdOpt_eq, ih.premRounds,
      map_bind]
  | _ =>
    simp only [rnIter, Sem.premIter, ih.doms, bind_map_left, isEmpty_rnDoms, head?_rnMap,
      Option.bind_map, Function.comp_def, ih.premRounds_none, map_bind, map_assert]

theorem EqvAt.premRounds_succ (hπ : π "_" = "_") (ih : EqvAt π n) (pr : Prem)
    (xvs : List (IL.Id × Value)) (ido : Option IL.Id) (k : Nat) :
    Sem.premRounds (n + 1) (rnEnv π env) (rnVarEnv π ρ) (rnPrem π pr) (rnMap π id xvs) (ido.map π)
      k = rnVarEnv π <$> Sem.premRounds (n + 1) env ρ pr xvs ido k := by
  have hm : ∀ rows : List (List (IL.Id × Value)),
      (rows.map (rnMap π id)).mapM
          (fun r => Sem.premHolds n (rnEnv π env) ((rnVarEnv π ρ).bindVals r) (rnPrem π pr)) =
        List.map (rnVarEnv π) <$> rows.mapM (fun r => Sem.premHolds n env (ρ.bindVals r) pr) :=
    mapM_map_of' fun r => by rw [bindVals_rn hπ, ih.premHolds]
  simp only [Sem.premRounds, mapM_asList_rn, ofOption_map, bind_map_left, iterRows_rn, hm,
    all_rnMap, map_bind, map_assert, map_ok]

theorem EqvAt.derives_succ (ih : EqvAt π n) (x : IL.Id) (op : MixopS) (ws : List ArgV)
    (v : Value) :
    Sem.derives (n + 1) (rnEnv π env) (π x) op (ws.map (rnArgV π)) v =
      Sem.derives (n + 1) env x op ws v := by
  simp only [Sem.derives, Env.findRel?_rn]
  cases env.findRel? x with
  | none => rfl
  | some d =>
    obtain ⟨ps, op', t, rules⟩ := d
    simp only [Option.map_some, rnRelDef, ih.anyRule]

theorem bindParams_rn_empty (hπ : π "_" = "_") (ps : List Param) (ws : List ArgV) :
    bindParams VarEnv.empty (rnParams π ps) (ws.map (rnArgV π)) =
      (bindParams VarEnv.empty ps ws).map (rnVarEnv π) :=
  bindParams_rn hπ VarEnv.empty ps ws

theorem isOk_map {β γ : Type} (g : β → γ) (r : Res β) : (g <$> r).isOk = r.isOk := by
  rcases r with _ | _ <;> rfl

theorem bind_map_out {β γ δ : Type} (g : γ → δ) (r : Res β) (k : β → Res γ) :
    (r >>= fun a => g <$> k a) = g <$> (r >>= k) := (map_bind g r k).symm

theorem EqvAt.anyRule_succ (hπ : π "_" = "_") (ih : EqvAt π n) (op : MixopS) (ps : List Param)
    (ws : List ArgV) (v : Value) (rs : List Rule) :
    Sem.anyRule (n + 1) (rnEnv π env) op (rnParams π ps) (ws.map (rnArgV π)) v (rnRules π rs) =
      Sem.anyRule (n + 1) env op ps ws v rs := by
  rcases rs with _ | ⟨⟨nm, qs, op', e, prems⟩, rs⟩
  · simp only [rnRules, Sem.anyRule]
  · simp only [rnRules, rnRule, Sem.anyRule, bindParams_rn_empty hπ, ofOption_map,
      bind_map_left, ih.matchExp, ih.premsHold, bind_map_out, isOk_map, ih.anyRule]

end Rest

/-- **The induction step**: equivariance at fuel `n` gives equivariance at `n + 1`. -/
theorem eqvAt_succ (hπ : π "_" = "_") (ih : EqvAt π n) : EqvAt π (n + 1) where
  exp env ρ e := ih.exp_succ env ρ e
  exps env ρ es := ih.exps_succ env ρ es
  expFields env ρ fs := ih.expFields_succ env ρ fs
  arg env ρ a := ih.arg_succ env ρ a
  args env ρ l := ih.args_succ env ρ l
  doms env ρ ds := ih.doms_succ env ρ ds
  iterE env ρ e it ds := ih.iterE_succ hπ env ρ e it ds
  iterList env ρ e xvs ido k := ih.iterList_succ env ρ e xvs ido k
  rounds env ρ e rs := ih.rounds_succ hπ env ρ e rs
  pathGet env ρ v p := ih.pathGet_succ env ρ v p
  pathSet env ρ v p w := ih.pathSet_succ env ρ v p w
  patLen env ρ e := ih.patLen_succ env ρ e
  matchExp env ρ e v := EqvAt.matchExp_succ env ρ hπ ih e v
  matchDefault env ρ e v := EqvAt.matchDefault_succ env ρ ih e v
  matchExps env ρ es vs := EqvAt.matchExps_succ env ρ ih es vs
  matchExpFields env ρ fs gs := EqvAt.matchExpFields_succ env ρ ih fs gs
  matchIterE env ρ e it ds v := EqvAt.matchIterE_succ env ρ ih e it ds v
  matchIterList env ρ e ds ido vs := EqvAt.matchIterList_succ env ρ ih e ds ido vs
  matchRounds env ρ e xs ido i vs := EqvAt.matchRounds_succ env ρ hπ ih e xs ido i vs
  matchArg env ρ a w := EqvAt.matchArg_succ env ρ hπ ih a w
  matchArgs env ρ l ws := EqvAt.matchArgs_succ env ρ ih l ws
  callDef env ρ x l := EqvAt.callDef_succ env ρ ih x l
  tryClauses env cs ws := EqvAt.tryClauses_succ env ih cs ws
  premHolds env ρ pr := EqvAt.premHolds_succ env ρ ih pr
  premsHold env ρ prs := EqvAt.premsHold_succ env ρ ih prs
  premIter env ρ pr it ds := EqvAt.premIter_succ env ρ hπ ih pr it ds
  premRounds env ρ pr xvs ido k := EqvAt.premRounds_succ env ρ hπ ih pr xvs ido k
  derives env x op ws v := EqvAt.derives_succ env ih x op ws v
  anyRule env op ps ws v rs := EqvAt.anyRule_succ env hπ ih op ps ws v rs

/-- **The evaluator is equivariant** under every permutation of identifiers fixing `"_"`, at
every fuel. -/
theorem eqvAt (hπ : π "_" = "_") : ∀ n, EqvAt π n
  | 0 => eqvAt_zero
  | n + 1 => eqvAt_succ hπ (eqvAt hπ n)

end Silmaril.Wasm.SpecTec.Institution.Perm
