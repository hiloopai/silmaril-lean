module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Defs

/-!
# Round 7, memory SIMD: values without given atoms, through the left-hand-side fragment

`NoAtoms A v` says that no `case` of an atom of `A` occurs in `v`. On the fragment `LFrag A` the
context rules of `Step` write their left-hand sides in, evaluation moves `NoAtoms` in both
directions between the value and the variables it reads (`lvars`):

* `noAtoms_vars_of_eval`: if a fragment expression evaluates to a `NoAtoms` value, every variable
  it reads is bound to a `NoAtoms` value. An iteration `x*` over the domain `xs` evaluates to the
  list bound to `xs` itself (`evalExp_iterVar`), a concatenation to the two lists (or options)
  it joins.
* `noAtoms_of_eval`: if every variable a fragment expression reads is bound to a `NoAtoms` value,
  the expression evaluates only to `NoAtoms` values (its own `case`s have atoms outside `A`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

variable {A : List MixopS}

/-! ## `NoAtoms` on lists, concatenations and pairs -/

theorem noAtomsL_iff : ∀ {vs : List Value}, NoAtomsL A vs ↔ ∀ v ∈ vs, NoAtoms A v
  | [] => by simp [NoAtomsL]
  | v :: vs => by simp [NoAtomsL, noAtomsL_iff (vs := vs)]

theorem noAtoms_list_iff {vs : List Value} : NoAtoms A (.list vs) ↔ ∀ v ∈ vs, NoAtoms A v := by
  rw [NoAtoms]
  exact noAtomsL_iff

theorem noAtoms_tuple_iff {vs : List Value} : NoAtoms A (.tuple vs) ↔ ∀ v ∈ vs, NoAtoms A v := by
  rw [NoAtoms]
  exact noAtomsL_iff

theorem noAtoms_cat {v₁ v₂ v : Value} (h : Value.cat? v₁ v₂ = some v) :
    NoAtoms A v ↔ NoAtoms A v₁ ∧ NoAtoms A v₂ := by
  rcases v₁ with _ | _ | _ | _ | _ | _ | _ | _ | o₁ <;>
    rcases v₂ with _ | _ | _ | _ | _ | _ | _ | _ | o₂ <;>
    simp only [Value.cat?, reduceCtorEq, Option.some.injEq] at h
  case list.list l₁ l₂ =>
    subst h
    simp only [noAtoms_list_iff, List.mem_append]
    exact ⟨fun h => ⟨fun v hv => h v (.inl hv), fun v hv => h v (.inr hv)⟩,
      fun h v hv => hv.elim (h.1 v) (h.2 v)⟩
  all_goals (subst h; simp [NoAtoms])

/-! ## Evaluation inversions -/

theorem evalExp_varE_ok {n : Nat} {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value}
    (h : evalExp n env ρ (.varE x) = .ok v) : ρ.findVal? x = some v := by
  rcases n with _ | n
  · simp [evalExp] at h
  · simpa only [evalExp, Res.ofOption_eq_ok] using h

theorem findVal?_bind₁ (ρ : VarEnv) {x : IL.Id} (w : Value) (h : x ≠ "_") :
    (ρ.bindVals [(x, w)]).findVal? x = some w := by
  simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, h]

/-- The body `x`, at a binding of `x`, reads the bound value back. -/
theorem body_varE {x : IL.Id} (hne : x ≠ "_") (n : Nat) (env : Env) (ρ : VarEnv) (w u : Value)
    (h : evalExp n env (ρ.bindVals [(x, w)]) (.varE x) = .ok u) : u = w := by
  have hf : (ρ.bindVals [(x, w)]).findVal? x = some u := evalExp_varE_ok h
  rw [findVal?_bind₁ ρ w hne] at hf
  exact (Option.some.inj hf).symm

/-- The body `x` through a subtype injection, at a binding of `x`, reads the bound value back. -/
theorem body_subE {x : IL.Id} {t₁ t₂ : Typ} (hne : x ≠ "_") (n : Nat) (env : Env) (ρ : VarEnv)
    (w u : Value) (h : evalExp n env (ρ.bindVals [(x, w)]) (.subE (.varE x) t₁ t₂) = .ok u) :
    u = w := by
  rcases n with _ | n
  · simp [evalExp] at h
  · have h' : evalExp n env (ρ.bindVals [(x, w)]) (.varE x) = .ok u := by
      simpa only [evalExp] using h
    exact body_varE hne n env ρ w u h'

/-- **An `iterVar` iteration has the shape `x*` over `xs`**, and its body reads back the binding
of `x`. -/
theorem iterVar_shape {b : Exp} {it : IterExp} {xs : IL.Id} (hx : iterVar b it = some xs) :
    ∃ x, it = .mk .list [.mk x (.varE xs)] ∧ x ≠ "_" ∧
      ∀ (n : Nat) (env : Env) (ρ : VarEnv) (w u : Value),
        evalExp n env (ρ.bindVals [(x, w)]) b = .ok u → u = w := by
  unfold iterVar at hx
  split at hx
  · split_ifs at hx with hc
    obtain ⟨rfl, hne⟩ := hc
    obtain rfl := Option.some.inj hx
    exact ⟨_, rfl, hne, body_varE hne⟩
  · split_ifs at hx with hc
    obtain ⟨rfl, hne⟩ := hc
    obtain rfl := Option.some.inj hx
    exact ⟨_, rfl, hne, body_subE hne⟩
  · cases hx

/-- The rows of a one-domain iteration. -/
theorem iterRows_one (x : IL.Id) (ws : List Value) :
    iterRows [(x, ws)] none ws.length = ws.map fun w => [(x, w)] := by
  apply List.ext_getElem
  · simp [iterRows]
  · intro i h₁ h₂
    have hi : i < ws.length := by simpa [iterRows] using h₁
    simp [iterRows, iterRow, hi]

theorem mapM_rows {f : List (IL.Id × Value) → Res Value} {x : IL.Id}
    (hf : ∀ w u, f [(x, w)] = .ok u → u = w) :
    ∀ {ws vs : List Value}, (ws.map fun w => [(x, w)]).mapM f = .ok vs → vs = ws
  | [], vs, h => by
    simp only [List.map_nil, List.mapM_nil, pure, Except.pure] at h
    exact (Except.ok.inj h).symm
  | w :: ws, vs, h => by
    rw [List.map_cons, List.mapM_cons] at h
    simp only [Res.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨u, hu, us, hus, rfl⟩ := h
    rw [hf w u hu, mapM_rows hf hus]

/-- **An `iterVar` iteration evaluates to the list bound to its domain variable.** -/
theorem evalExp_iterVar {n : Nat} {env : Env} {ρ : VarEnv} {b : Exp} {it : IterExp} {xs : IL.Id}
    {v : Value} (hx : iterVar b it = some xs) (h : evalExp n env ρ (.iterE b it) = .ok v) :
    ∃ L, ρ.findVal? xs = some (.list L) ∧ v = .list L := by
  obtain ⟨x, rfl, -, hb⟩ := iterVar_shape hx
  rcases n with _ | _ | _ | _ | n
  all_goals simp only [evalExp, evalIterE, evalDoms, evalIterList, evalRounds, Res.bind_eq_ok,
    Res.ofOption_eq_ok, Res.assert_eq_ok] at h
  case' zero | succ.zero | succ.succ.zero | succ.succ.succ.zero => simp at h
  simp only [List.mapM_cons, List.mapM_nil, domSrc, domVar, evalExp, Res.map_eq_ok,
    Res.bind_eq_ok, Res.ofOption_eq_ok, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨_, ⟨_, ⟨u, hu, rfl⟩, _, rfl, rfl⟩, -, k, hk, ds, hds, hall, vs, hvs, rfl⟩ := h
  rcases u with _ | _ | _ | _ | _ | _ | L | _ <;>
    simp only [Value.asList?, List.head?_cons, Option.bind_some, Option.map_some, Option.map_none,
      reduceCtorEq, Option.some.injEq] at hk
  · simp only [List.mapM_cons, List.mapM_nil, Value.asList?, Option.map_some, Option.bind_some,
      Option.pure_def, Option.bind_eq_bind, Option.some.injEq] at hds
    subst hk hds
    rw [iterRows_one] at hvs
    exact ⟨L, hu, by rw [mapM_rows (fun w u h => hb n env ρ w u h) hvs]⟩

/-! ## Through the fragment -/

/-- The variables of `e` are bound to `NoAtoms` values. -/
def VarsOk (A : List MixopS) (ρ : VarEnv) (xs : List IL.Id) : Prop :=
  ∀ x ∈ xs, ∀ u, ρ.findVal? x = some u → NoAtoms A u

theorem varsOk_append {ρ : VarEnv} {xs ys : List IL.Id} :
    VarsOk A ρ (xs ++ ys) ↔ VarsOk A ρ xs ∧ VarsOk A ρ ys := by
  simp only [VarsOk, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem lfragL_cons {e : Exp} {es : List Exp} :
    LFragL A (e :: es) = true ↔ LFrag A e = true ∧ LFragL A es = true := by
  simp only [LFragL, Bool.and_eq_true]

/-- The list step of `vars_of_eval`. -/
theorem vars_of_mapM {ρ : VarEnv} {f : Exp → Res Value}
    (ih : ∀ e v, f e = .ok v → LFrag A e = true → NoAtoms A v → VarsOk A ρ (lvars e)) :
    ∀ {es : List Exp} {vs : List Value}, es.mapM f = .ok vs → LFragL A es = true →
      (∀ v ∈ vs, NoAtoms A v) → VarsOk A ρ (lvarsL es)
  | [], _, _, _, _ => by simp [lvarsL, VarsOk]
  | e :: es, vs, h, hl, hv => by
    obtain ⟨v, hv₁, vs', hvs', rfl⟩ := mapM_cons_ok' h
    rw [lfragL_cons] at hl
    simp only [lvarsL, varsOk_append]
    exact ⟨ih e v hv₁ hl.1 (hv v List.mem_cons_self),
      vars_of_mapM ih hvs' hl.2 fun w hw => hv w (List.mem_cons_of_mem _ hw)⟩
where
  mapM_cons_ok' {f : Exp → Res Value} {e₀ : Exp} {rest : List Exp} {vs : List Value}
      (hm : (e₀ :: rest).mapM f = .ok vs) :
      ∃ v, f e₀ = .ok v ∧ ∃ vs', rest.mapM f = .ok vs' ∧ v :: vs' = vs := by
    rw [List.mapM_cons] at hm
    simpa only [Res.bind_eq_ok, pure, Except.pure, Except.ok.injEq] using hm

/-- The list step of `noAtoms_of_eval`. -/
theorem noAtoms_of_mapM {ρ : VarEnv} {f : Exp → Res Value}
    (ih : ∀ e v, f e = .ok v → LFrag A e = true → VarsOk A ρ (lvars e) → NoAtoms A v) :
    ∀ {es : List Exp} {vs : List Value}, es.mapM f = .ok vs → LFragL A es = true →
      VarsOk A ρ (lvarsL es) → ∀ v ∈ vs, NoAtoms A v
  | [], vs, h, _, _ => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | e :: es, vs, h, hl, hx => by
    obtain ⟨v, hv₁, vs', hvs', rfl⟩ := vars_of_mapM.mapM_cons_ok' h
    rw [lfragL_cons] at hl
    simp only [lvarsL, varsOk_append] at hx
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ih e w hv₁ hl.1 hx.1
    · exact noAtoms_of_mapM ih hvs' hl.2 hx.2 w hw

/-! ### One evaluation step of each fragment constructor -/

section Steps

variable {env : Env} {ρ : VarEnv} {n : Nat}

theorem eval_tupE {es : List Exp} {v : Value} (h : evalExp (n + 1) env ρ (.tupE es) = .ok v) :
    ∃ m < n + 1, ∃ vs, es.mapM (evalExp m env ρ) = .ok vs ∧ v = .tuple vs := by
  rcases n with _ | n
  · simp [evalExp, evalExps] at h
  · have h' : ∃ vs, es.mapM (evalExp n env ρ) = .ok vs ∧ Value.tuple vs = v := by
      simpa only [evalExp, evalExps, Res.map_eq_ok] using h
    obtain ⟨vs, hvs, hv⟩ := h'
    exact ⟨n, by omega, vs, hvs, hv.symm⟩

theorem eval_listE {es : List Exp} {v : Value} (h : evalExp (n + 1) env ρ (.listE es) = .ok v) :
    ∃ m < n + 1, ∃ vs, es.mapM (evalExp m env ρ) = .ok vs ∧ v = .list vs := by
  rcases n with _ | n
  · simp [evalExp, evalExps] at h
  · have h' : ∃ vs, es.mapM (evalExp n env ρ) = .ok vs ∧ Value.list vs = v := by
      simpa only [evalExp, evalExps, Res.map_eq_ok] using h
    obtain ⟨vs, hvs, hv⟩ := h'
    exact ⟨n, by omega, vs, hvs, hv.symm⟩

theorem eval_caseE {a : MixopS} {e : Exp} {v : Value}
    (h : evalExp (n + 1) env ρ (.caseE a e) = .ok v) :
    ∃ w, evalExp n env ρ e = .ok w ∧ v = .case a w := by
  have h' : ∃ w, evalExp n env ρ e = .ok w ∧ Value.case a w = v := by
    simpa only [evalExp, Res.map_eq_ok] using h
  obtain ⟨w, hw, hv⟩ := h'
  exact ⟨w, hw, hv.symm⟩

theorem eval_catE {e₁ e₂ : Exp} {v : Value} (h : evalExp (n + 1) env ρ (.catE e₁ e₂) = .ok v) :
    ∃ v₁, evalExp n env ρ e₁ = .ok v₁ ∧ ∃ v₂, evalExp n env ρ e₂ = .ok v₂ ∧
      Value.cat? v₁ v₂ = some v := by
  simpa only [evalExp, Res.bind_eq_ok, Res.ofOption_eq_ok] using h

theorem eval_subE {e : Exp} {t₁ t₂ : Typ} {v : Value}
    (h : evalExp (n + 1) env ρ (.subE e t₁ t₂) = .ok v) : evalExp n env ρ e = .ok v := by
  simpa only [evalExp] using h

end Steps

/-- `vars_of_eval` below fuel `k`. -/
def OutBelow (A : List MixopS) (env : Env) (ρ : VarEnv) (k : Nat) : Prop :=
  ∀ m < k, ∀ {e : Exp} {v : Value}, evalExp m env ρ e = .ok v → LFrag A e = true →
    NoAtoms A v → VarsOk A ρ (lvars e)

/-- `noAtoms_of_eval` below fuel `k`. -/
def InBelow (A : List MixopS) (env : Env) (ρ : VarEnv) (k : Nat) : Prop :=
  ∀ m < k, ∀ {e : Exp} {v : Value}, evalExp m env ρ e = .ok v → LFrag A e = true →
    VarsOk A ρ (lvars e) → NoAtoms A v

section Cases

variable {env : Env} {ρ : VarEnv} {n : Nat}

theorem out_varE {x : IL.Id} {v : Value} (h : evalExp n env ρ (.varE x) = .ok v)
    (hv : NoAtoms A v) : VarsOk A ρ (lvars (.varE x)) := by
  have hx : ρ.findVal? x = some v := evalExp_varE_ok h
  intro y hy u hu
  have hyx : y = x := by simpa only [lvars, List.mem_singleton] using hy
  have huv : u = v := Option.some.inj (hu.symm.trans (hyx ▸ hx))
  exact huv ▸ hv

theorem out_seq {es : List Exp} {vs : List Value} {m : Nat} (ih : OutBelow A env ρ (n + 1))
    (hm : m < n + 1) (hvs : es.mapM (evalExp m env ρ) = .ok vs) (hl : LFragL A es = true)
    (hv : ∀ w ∈ vs, NoAtoms A w) : VarsOk A ρ (lvarsL es) :=
  vars_of_mapM (fun _ _ h hl hv => ih m hm h hl hv) hvs hl hv

theorem out_catE {e₁ e₂ : Exp} {v : Value} (ih : OutBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.catE e₁ e₂) = .ok v) (hl : LFrag A (.catE e₁ e₂) = true)
    (hv : NoAtoms A v) : VarsOk A ρ (lvars (.catE e₁ e₂)) := by
  obtain ⟨v₁, h₁, v₂, h₂, hc⟩ := eval_catE h
  have hl' : LFrag A e₁ = true ∧ LFrag A e₂ = true := by
    simpa only [LFrag, Bool.and_eq_true] using hl
  have hv' : NoAtoms A v₁ ∧ NoAtoms A v₂ := (noAtoms_cat hc).1 hv
  show VarsOk A ρ (lvars e₁ ++ lvars e₂)
  exact varsOk_append.2 ⟨ih n (by omega) h₁ hl'.1 hv'.1, ih n (by omega) h₂ hl'.2 hv'.2⟩

theorem out_iterE {b : Exp} {it : IterExp} {v : Value}
    (h : evalExp (n + 1) env ρ (.iterE b it) = .ok v) (hl : LFrag A (.iterE b it) = true)
    (hv : NoAtoms A v) : VarsOk A ρ (lvars (.iterE b it)) := by
  obtain ⟨xs, hx⟩ : ∃ xs, iterVar b it = some xs := by
    simpa only [LFrag, Option.isSome_iff_exists] using hl
  obtain ⟨L, hL, hvL⟩ := evalExp_iterVar hx h
  intro y hy u hu
  have hyx : y = xs := by simpa only [lvars, hx, Option.toList_some, List.mem_singleton] using hy
  have huv : u = v := by rw [hvL]; exact Option.some.inj (hu.symm.trans (hyx ▸ hL))
  exact huv ▸ hv

theorem in_catE {e₁ e₂ : Exp} {v : Value} (ih : InBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.catE e₁ e₂) = .ok v) (hl : LFrag A (.catE e₁ e₂) = true)
    (hx : VarsOk A ρ (lvars (.catE e₁ e₂))) : NoAtoms A v := by
  obtain ⟨v₁, h₁, v₂, h₂, hc⟩ := eval_catE h
  have hl' : LFrag A e₁ = true ∧ LFrag A e₂ = true := by
    simpa only [LFrag, Bool.and_eq_true] using hl
  have hx' : VarsOk A ρ (lvars e₁) ∧ VarsOk A ρ (lvars e₂) := varsOk_append.1 hx
  exact (noAtoms_cat hc).2 ⟨ih n (by omega) h₁ hl'.1 hx'.1, ih n (by omega) h₂ hl'.2 hx'.2⟩

theorem in_caseE {a : MixopS} {e : Exp} {v : Value} (ih : InBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.caseE a e) = .ok v) (hl : LFrag A (.caseE a e) = true)
    (hx : VarsOk A ρ (lvars (.caseE a e))) : NoAtoms A v := by
  obtain ⟨w, hw, rfl⟩ := eval_caseE h
  have hl' : (!A.contains a) = true ∧ LFrag A e = true := by
    simpa only [LFrag, Bool.and_eq_true] using hl
  have ha : a ∉ A := fun ha => by simp [ha] at hl'
  show a ∉ A ∧ NoAtoms A w
  exact ⟨ha, ih n (by omega) hw hl'.2 (by simpa only [lvars] using hx)⟩

theorem in_iterE {b : Exp} {it : IterExp} {v : Value}
    (h : evalExp (n + 1) env ρ (.iterE b it) = .ok v) (hl : LFrag A (.iterE b it) = true)
    (hx : VarsOk A ρ (lvars (.iterE b it))) : NoAtoms A v := by
  obtain ⟨xs, hxs⟩ : ∃ xs, iterVar b it = some xs := by
    simpa only [LFrag, Option.isSome_iff_exists] using hl
  obtain ⟨L, hL, rfl⟩ := evalExp_iterVar hxs h
  exact hx xs (by simp [lvars, hxs]) _ hL

theorem out_tupE {es : List Exp} {v : Value} (ih : OutBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.tupE es) = .ok v) (hl : LFrag A (.tupE es) = true)
    (hv : NoAtoms A v) : VarsOk A ρ (lvars (.tupE es)) := by
  obtain ⟨m, hm, vs, hvs, rfl⟩ := eval_tupE h
  exact out_seq ih hm hvs (by simpa [LFrag] using hl) (noAtoms_tuple_iff.1 hv)

theorem out_listE {es : List Exp} {v : Value} (ih : OutBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.listE es) = .ok v) (hl : LFrag A (.listE es) = true)
    (hv : NoAtoms A v) : VarsOk A ρ (lvars (.listE es)) := by
  obtain ⟨m, hm, vs, hvs, rfl⟩ := eval_listE h
  exact out_seq ih hm hvs (by simpa [LFrag] using hl) (noAtoms_list_iff.1 hv)

theorem out_caseE {a : MixopS} {e : Exp} {v : Value} (ih : OutBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.caseE a e) = .ok v) (hl : LFrag A (.caseE a e) = true)
    (hv : NoAtoms A v) : VarsOk A ρ (lvars (.caseE a e)) := by
  obtain ⟨w, hw, rfl⟩ := eval_caseE h
  exact ih n (by omega) (e := e) hw (by simp_all [LFrag]) (by simp_all [NoAtoms])

theorem out_subE {e : Exp} {t₁ t₂ : Typ} {v : Value} (ih : OutBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.subE e t₁ t₂) = .ok v) (hl : LFrag A (.subE e t₁ t₂) = true)
    (hv : NoAtoms A v) : VarsOk A ρ (lvars (.subE e t₁ t₂)) :=
  ih n (by omega) (e := e) (eval_subE h) (by simpa [LFrag] using hl) hv

theorem in_tupE {es : List Exp} {v : Value} (ih : InBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.tupE es) = .ok v) (hl : LFrag A (.tupE es) = true)
    (hx : VarsOk A ρ (lvars (.tupE es))) : NoAtoms A v := by
  obtain ⟨m, hm, vs, hvs, rfl⟩ := eval_tupE h
  exact noAtoms_tuple_iff.2 (noAtoms_of_mapM (fun _ _ h hl hx => ih m hm h hl hx) hvs
    (by simpa [LFrag] using hl) (by simpa [lvars] using hx))

theorem in_listE {es : List Exp} {v : Value} (ih : InBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.listE es) = .ok v) (hl : LFrag A (.listE es) = true)
    (hx : VarsOk A ρ (lvars (.listE es))) : NoAtoms A v := by
  obtain ⟨m, hm, vs, hvs, rfl⟩ := eval_listE h
  exact noAtoms_list_iff.2 (noAtoms_of_mapM (fun _ _ h hl hx => ih m hm h hl hx) hvs
    (by simpa [LFrag] using hl) (by simpa [lvars] using hx))

theorem in_subE {e : Exp} {t₁ t₂ : Typ} {v : Value} (ih : InBelow A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.subE e t₁ t₂) = .ok v) (hl : LFrag A (.subE e t₁ t₂) = true)
    (hx : VarsOk A ρ (lvars (.subE e t₁ t₂))) : NoAtoms A v :=
  ih n (by omega) (e := e) (eval_subE h) (by simpa [LFrag] using hl) (by simpa [lvars] using hx)

end Cases

/-- **A fragment expression evaluating to a `NoAtoms` value reads only `NoAtoms` bindings.** -/
theorem vars_of_eval {env : Env} {ρ : VarEnv} (n : Nat) :
    ∀ {e : Exp} {v : Value}, evalExp n env ρ e = .ok v → LFrag A e = true → NoAtoms A v →
      VarsOk A ρ (lvars e) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e v h hl hv
  rcases n with _ | n
  · simp [evalExp] at h
  have ih' : OutBelow A env ρ (n + 1) := fun m hm => ih m hm
  cases e
  case varE x => exact out_varE h hv
  case tupE es => exact out_tupE ih' h hl hv
  case listE es => exact out_listE ih' h hl hv
  case caseE a e => exact out_caseE ih' h hl hv
  case catE e₁ e₂ => exact out_catE ih' h hl hv
  case subE e t₁ t₂ => exact out_subE ih' h hl hv
  case iterE b it => exact out_iterE h hl hv
  all_goals simp [LFrag] at hl

/-- **A fragment expression reading only `NoAtoms` bindings evaluates to a `NoAtoms` value.** -/
theorem noAtoms_of_eval {env : Env} {ρ : VarEnv} (n : Nat) :
    ∀ {e : Exp} {v : Value}, evalExp n env ρ e = .ok v → LFrag A e = true →
      VarsOk A ρ (lvars e) → NoAtoms A v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e v h hl hx
  rcases n with _ | n
  · simp [evalExp] at h
  have ih' : InBelow A env ρ (n + 1) := fun m hm => ih m hm
  cases e
  case varE x => exact hx x (by simp [lvars]) v (evalExp_varE_ok h)
  case tupE es => exact in_tupE ih' h hl hx
  case listE es => exact in_listE ih' h hl hx
  case caseE a e => exact in_caseE ih' h hl hx
  case catE e₁ e₂ => exact in_catE ih' h hl hx
  case subE e t₁ t₂ => exact in_subE ih' h hl hx
  case iterE b it => exact in_iterE h hl hx
  all_goals simp [LFrag] at hl

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
