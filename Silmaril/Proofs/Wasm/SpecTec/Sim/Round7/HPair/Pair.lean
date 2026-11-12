module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HPair.Check

/-!
# Round 7, `BD`: `NoPair` through evaluation

* `noPair_cat`: a concatenation that is `NoPair` has `NoPair` parts (a contiguous part of a pair-free
  list is pair-free).
* `vars_of_evalP`: an `LFrag` expression evaluating to a `NoPair` value binds every variable it
  reads to a `NoPair` value (`VInv.vars_of_eval` with `NoPair` for `NoAtoms`).
* `noPair_of_evalP`: an `LFragP` expression whose variables are bound to `NoPair` values evaluates
  to a `NoPair` value. Concatenations and lists of two or more elements are left out of `LFragP`:
  they can put a `REF.FUNC_ADDR` next to a `CALL_REF`.
* `lastPair_eval`: a code expression ending in `a`, `b` evaluates to a list ending in a `case` of
  `a` followed by a `case` of `b`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HPair

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open VInv (LFrag LFragL lvars lvarsL iterVar)

/-! ## Values -/

theorem noPairL_iff : ∀ {vs : List Value}, NoPairL vs ↔ ∀ v ∈ vs, NoPair v
  | [] => by simp [NoPairL]
  | v :: vs => by simp [NoPairL, noPairL_iff (vs := vs)]

theorem pairFree_append : ∀ {l₁ l₂ : List Value}, PairFreeL (l₁ ++ l₂) →
    PairFreeL l₁ ∧ PairFreeL l₂
  | [], _, h => ⟨trivial, h⟩
  | [_], [], _ => ⟨trivial, trivial⟩
  | [_], _ :: _, h => ⟨trivial, h.2⟩
  | _ :: b :: l₁, l₂, h =>
      have ih := pairFree_append (l₁ := b :: l₁) (l₂ := l₂) h.2
      ⟨⟨h.1, ih.1⟩, ih.2⟩

theorem pairFree_nil : PairFreeL [] := trivial

theorem pairFree_single (a : Value) : PairFreeL [a] := trivial

theorem noPair_cat {v₁ v₂ v : Value} (h : Value.cat? v₁ v₂ = some v) (hv : NoPair v) :
    NoPair v₁ ∧ NoPair v₂ := by
  rcases v₁ with _ | _ | _ | _ | _ | _ | l₁ | o₁ <;>
    rcases v₂ with _ | _ | _ | _ | _ | _ | l₂ | o₂ <;>
    simp only [Value.cat?, reduceCtorEq, Option.some.injEq] at h
  case list.list =>
    subst h
    have hp : PairFreeL l₁ ∧ PairFreeL l₂ := pairFree_append hv.1
    have he : ∀ w ∈ l₁ ++ l₂, NoPair w := noPairL_iff.1 hv.2
    exact ⟨⟨hp.1, noPairL_iff.2 fun w hw => he w (List.mem_append_left _ hw)⟩,
      ⟨hp.2, noPairL_iff.2 fun w hw => he w (List.mem_append_right _ hw)⟩⟩
  case opt.opt =>
    rcases o₁ with _ | w₁ <;> rcases o₂ with _ | w₂ <;>
      simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      simp_all [NoPair]

/-- The last two elements of a pair-free list do not form `pairAt`. -/
theorem pairFree_last : ∀ {l : List Value} {x y : Value}, PairFreeL (l ++ [x, y]) →
    pairAt x y = false
  | [], _, _, h => h.1
  | [_], _, _, h => h.2.1
  | _ :: b :: l, _, _, h => pairFree_last (l := b :: l) h.2

/-! ## The out direction (on `LFrag`) -/

/-- The variables read are bound to `NoPair` values. -/
def VarsP (ρ : VarEnv) (xs : List IL.Id) : Prop :=
  ∀ x ∈ xs, ∀ u, ρ.findVal? x = some u → NoPair u

theorem varsP_append {ρ : VarEnv} {xs ys : List IL.Id} :
    VarsP ρ (xs ++ ys) ↔ VarsP ρ xs ∧ VarsP ρ ys := by
  simp only [VarsP, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem mapM_cons_ok {f : Exp → Res Value} {e₀ : Exp} {rest : List Exp} {vs : List Value}
    (hm : (e₀ :: rest).mapM f = .ok vs) :
    ∃ v, f e₀ = .ok v ∧ ∃ vs', rest.mapM f = .ok vs' ∧ v :: vs' = vs := by
  rw [List.mapM_cons] at hm
  simpa only [Res.bind_eq_ok, pure, Except.pure, Except.ok.injEq] using hm

section
variable {A : List MixopS}

theorem varsP_of_mapM {ρ : VarEnv} {f : Exp → Res Value}
    (ih : ∀ e v, f e = .ok v → LFrag A e = true → NoPair v → VarsP ρ (lvars e)) :
    ∀ {es : List Exp} {vs : List Value}, es.mapM f = .ok vs → LFragL A es = true →
      (∀ v ∈ vs, NoPair v) → VarsP ρ (lvarsL es)
  | [], _, _, _, _ => by simp [lvarsL, VarsP]
  | e :: es, vs, h, hl, hv => by
    obtain ⟨v, hv₁, vs', hvs', rfl⟩ := mapM_cons_ok h
    have hl' : LFrag A e = true ∧ LFragL A es = true := by
      simpa only [LFragL, Bool.and_eq_true] using hl
    simp only [lvarsL, varsP_append]
    exact ⟨ih e v hv₁ hl'.1 (hv v List.mem_cons_self),
      varsP_of_mapM ih hvs' hl'.2 fun w hw => hv w (List.mem_cons_of_mem _ hw)⟩

/-- `vars_of_evalP` below fuel `k`. -/
def OutBelowP (A : List MixopS) (env : Env) (ρ : VarEnv) (k : Nat) : Prop :=
  ∀ m < k, ∀ {e : Exp} {v : Value}, evalExp m env ρ e = .ok v → LFrag A e = true →
    NoPair v → VarsP ρ (lvars e)

variable {env : Env} {ρ : VarEnv} {n : Nat}

theorem outP_varE {x : IL.Id} {v : Value} (h : evalExp n env ρ (.varE x) = .ok v)
    (hv : NoPair v) : VarsP ρ (lvars (.varE x)) := by
  have hx : ρ.findVal? x = some v := VInv.evalExp_varE_ok h
  intro y hy u hu
  have hyx : y = x := by simpa only [lvars, List.mem_singleton] using hy
  have huv : u = v := Option.some.inj (hu.symm.trans (hyx ▸ hx))
  exact huv ▸ hv

theorem outP_catE {e₁ e₂ : Exp} {v : Value} (ih : OutBelowP A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.catE e₁ e₂) = .ok v) (hl : LFrag A (.catE e₁ e₂) = true)
    (hv : NoPair v) : VarsP ρ (lvars (.catE e₁ e₂)) := by
  obtain ⟨v₁, h₁, v₂, h₂, hc⟩ := VInv.eval_catE h
  have hl' : LFrag A e₁ = true ∧ LFrag A e₂ = true := by
    simpa only [LFrag, Bool.and_eq_true] using hl
  have hv' : NoPair v₁ ∧ NoPair v₂ := noPair_cat hc hv
  show VarsP ρ (lvars e₁ ++ lvars e₂)
  exact varsP_append.2 ⟨ih n (by omega) h₁ hl'.1 hv'.1, ih n (by omega) h₂ hl'.2 hv'.2⟩

theorem outP_iterE {b : Exp} {it : IterExp} {v : Value}
    (h : evalExp (n + 1) env ρ (.iterE b it) = .ok v) (hl : LFrag A (.iterE b it) = true)
    (hv : NoPair v) : VarsP ρ (lvars (.iterE b it)) := by
  obtain ⟨xs, hx⟩ : ∃ xs, iterVar b it = some xs := by
    simpa only [LFrag, Option.isSome_iff_exists] using hl
  obtain ⟨L, hL, hvL⟩ := VInv.evalExp_iterVar hx h
  intro y hy u hu
  have hyx : y = xs := by simpa only [lvars, hx, Option.toList_some, List.mem_singleton] using hy
  have huv : u = v := by rw [hvL]; exact Option.some.inj (hu.symm.trans (hyx ▸ hL))
  exact huv ▸ hv

theorem outP_tupE {es : List Exp} {v : Value} (ih : OutBelowP A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.tupE es) = .ok v) (hl : LFrag A (.tupE es) = true)
    (hv : NoPair v) : VarsP ρ (lvars (.tupE es)) := by
  obtain ⟨m, hm, vs, hvs, rfl⟩ := VInv.eval_tupE h
  have hvs' : ∀ w ∈ vs, NoPair w := noPairL_iff.1 hv
  exact varsP_of_mapM (fun _ _ h hl hv => ih m hm h hl hv) hvs (by simpa [LFrag] using hl) hvs'

theorem outP_listE {es : List Exp} {v : Value} (ih : OutBelowP A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.listE es) = .ok v) (hl : LFrag A (.listE es) = true)
    (hv : NoPair v) : VarsP ρ (lvars (.listE es)) := by
  obtain ⟨m, hm, vs, hvs, rfl⟩ := VInv.eval_listE h
  have hvs' : ∀ w ∈ vs, NoPair w := noPairL_iff.1 hv.2
  exact varsP_of_mapM (fun _ _ h hl hv => ih m hm h hl hv) hvs (by simpa [LFrag] using hl) hvs'

theorem outP_caseE {a : MixopS} {e : Exp} {v : Value} (ih : OutBelowP A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.caseE a e) = .ok v) (hl : LFrag A (.caseE a e) = true)
    (hv : NoPair v) : VarsP ρ (lvars (.caseE a e)) := by
  obtain ⟨w, hw, rfl⟩ := VInv.eval_caseE h
  have hl' : LFrag A e = true := by
    simp only [LFrag, Bool.and_eq_true] at hl
    exact hl.2
  exact ih n (by omega) (e := e) hw hl' hv

theorem outP_subE {e : Exp} {t₁ t₂ : Typ} {v : Value} (ih : OutBelowP A env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.subE e t₁ t₂) = .ok v) (hl : LFrag A (.subE e t₁ t₂) = true)
    (hv : NoPair v) : VarsP ρ (lvars (.subE e t₁ t₂)) :=
  ih n (by omega) (e := e) (VInv.eval_subE h) (by simpa [LFrag] using hl) hv

/-- **An `LFrag` expression evaluating to a `NoPair` value reads only `NoPair` bindings.** -/
theorem vars_of_evalP (n : Nat) :
    ∀ {e : Exp} {v : Value}, evalExp n env ρ e = .ok v → LFrag A e = true → NoPair v →
      VarsP ρ (lvars e) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e v h hl hv
  rcases n with _ | n
  · simp [evalExp] at h
  have ih' : OutBelowP A env ρ (n + 1) := fun m hm => ih m hm
  cases e
  case varE x => exact outP_varE h hv
  case tupE es => exact outP_tupE ih' h hl hv
  case listE es => exact outP_listE ih' h hl hv
  case caseE a e => exact outP_caseE ih' h hl hv
  case catE e₁ e₂ => exact outP_catE ih' h hl hv
  case subE e t₁ t₂ => exact outP_subE ih' h hl hv
  case iterE b it => exact outP_iterE h hl hv
  all_goals simp [LFrag] at hl

end

/-! ## The in direction (on `LFragP`) -/

section
variable {env : Env} {ρ : VarEnv} {n : Nat}

/-- `noPair_of_evalP` below fuel `k`. -/
def InBelowP (env : Env) (ρ : VarEnv) (k : Nat) : Prop :=
  ∀ m < k, ∀ {e : Exp} {v : Value}, evalExp m env ρ e = .ok v → LFragP e = true →
    VarsP ρ (lvars e) → NoPair v

theorem noPair_of_mapM {f : Exp → Res Value}
    (ih : ∀ e v, f e = .ok v → LFragP e = true → VarsP ρ (lvars e) → NoPair v) :
    ∀ {es : List Exp} {vs : List Value}, es.mapM f = .ok vs → LFragPL es = true →
      VarsP ρ (lvarsL es) → ∀ v ∈ vs, NoPair v
  | [], vs, h, _, _ => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | e :: es, vs, h, hl, hx => by
    obtain ⟨v, hv₁, vs', hvs', rfl⟩ := mapM_cons_ok h
    have hl' : LFragP e = true ∧ LFragPL es = true := by
      simpa only [LFragPL, Bool.and_eq_true] using hl
    simp only [lvarsL, varsP_append] at hx
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ih e w hv₁ hl'.1 hx.1
    · exact noPair_of_mapM ih hvs' hl'.2 hx.2 w hw

theorem inP_listE {es : List Exp} {v : Value} (ih : InBelowP env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.listE es) = .ok v) (hl : LFragP (.listE es) = true)
    (hx : VarsP ρ (lvars (.listE es))) : NoPair v := by
  obtain ⟨m, hm, vs, hvs, rfl⟩ := VInv.eval_listE h
  rcases es with _ | ⟨e, _ | ⟨e', es⟩⟩
  · have hnil : vs = [] := by
      simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq, eq_comm] using hvs
    rw [hnil]
    exact ⟨trivial, trivial⟩
  · obtain ⟨w, hw, vs', hvs', rfl⟩ := mapM_cons_ok hvs
    have hnil : vs' = [] := by
      simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq, eq_comm] using hvs'
    rw [hnil]
    have hw' : NoPair w := ih m hm hw (by simpa [LFragP] using hl) (by simpa [lvars, lvarsL] using hx)
    exact ⟨trivial, hw', trivial⟩
  · simp [LFragP] at hl

theorem inP_tupE {es : List Exp} {v : Value} (ih : InBelowP env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.tupE es) = .ok v) (hl : LFragP (.tupE es) = true)
    (hx : VarsP ρ (lvars (.tupE es))) : NoPair v := by
  obtain ⟨m, hm, vs, hvs, rfl⟩ := VInv.eval_tupE h
  exact noPairL_iff.2 (noPair_of_mapM (fun _ _ h hl hx => ih m hm h hl hx) hvs
    (by simpa [LFragP] using hl) (by simpa [lvars] using hx))

theorem inP_caseE {a : MixopS} {e : Exp} {v : Value} (ih : InBelowP env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.caseE a e) = .ok v) (hl : LFragP (.caseE a e) = true)
    (hx : VarsP ρ (lvars (.caseE a e))) : NoPair v := by
  obtain ⟨w, hw, rfl⟩ := VInv.eval_caseE h
  show NoPair w
  exact ih n (by omega) hw (by simpa [LFragP] using hl) (by simpa [lvars] using hx)

theorem inP_subE {e : Exp} {t₁ t₂ : Typ} {v : Value} (ih : InBelowP env ρ (n + 1))
    (h : evalExp (n + 1) env ρ (.subE e t₁ t₂) = .ok v) (hl : LFragP (.subE e t₁ t₂) = true)
    (hx : VarsP ρ (lvars (.subE e t₁ t₂))) : NoPair v :=
  ih n (by omega) (VInv.eval_subE h) (by simpa [LFragP] using hl) (by simpa [lvars] using hx)

theorem inP_iterE {b : Exp} {it : IterExp} {v : Value}
    (h : evalExp (n + 1) env ρ (.iterE b it) = .ok v) (hl : LFragP (.iterE b it) = true)
    (hx : VarsP ρ (lvars (.iterE b it))) : NoPair v := by
  obtain ⟨xs, hxs⟩ : ∃ xs, iterVar b it = some xs := by
    simpa only [LFragP, Option.isSome_iff_exists] using hl
  obtain ⟨L, hL, rfl⟩ := VInv.evalExp_iterVar hxs h
  exact hx xs (by simp [lvars, hxs]) _ hL

/-- **An `LFragP` expression reading only `NoPair` bindings evaluates to a `NoPair` value.** -/
theorem noPair_of_evalP (n : Nat) :
    ∀ {e : Exp} {v : Value}, evalExp n env ρ e = .ok v → LFragP e = true →
      VarsP ρ (lvars e) → NoPair v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e v h hl hx
  rcases n with _ | n
  · simp [evalExp] at h
  have ih' : InBelowP env ρ (n + 1) := fun m hm => ih m hm
  cases e
  case varE x => exact hx x (by simp [lvars]) v (VInv.evalExp_varE_ok h)
  case tupE es => exact inP_tupE ih' h hl hx
  case listE es => exact inP_listE ih' h hl hx
  case caseE a e => exact inP_caseE ih' h hl hx
  case subE e t₁ t₂ => exact inP_subE ih' h hl hx
  case iterE b it => exact inP_iterE h hl hx
  all_goals simp [LFragP] at hl

end

/-! ## The last two instructions -/

theorem lastPair_listE {es : List Exp} {a b : MixopS} (h : lastPair (.listE es) = some (a, b)) :
    ∃ pre ea eb, es = pre ++ [.caseE a ea, .caseE b eb] := by
  simp only [lastPair] at h
  split at h
  · rename_i b' eb a' ea rest hrev
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨rest.reverse, ea, eb, ?_⟩
    have := congrArg List.reverse hrev
    simpa using this
  · cases h

/-- A list ending in a `case` of `a` then a `case` of `b`. -/
def EndsIn (a b : MixopS) (cs : List Value) : Prop :=
  ∃ pre wa wb, cs = pre ++ [.case a wa, .case b wb]

theorem evalExp_listE_pair {n : Nat} {env : Env} {ρ : VarEnv} {es : List Exp} {a b : MixopS}
    {v : Value} (hp : lastPair (.listE es) = some (a, b))
    (h : evalExp (n + 2) env ρ (.listE es) = .ok v) : ∃ cs, v = .list cs ∧ EndsIn a b cs := by
  have h' : ∃ vs, es.mapM (evalExp n env ρ) = .ok vs ∧ Value.list vs = v := by
    simpa only [evalExp, evalExps, Res.map_eq_ok] using h
  obtain ⟨vs, hvs, hv⟩ := h'
  obtain ⟨pre, ea, eb, rfl⟩ := lastPair_listE hp
  rw [List.mapM_append] at hvs
  simp only [Res.bind_eq_ok, pure, Except.pure, Except.ok.injEq] at hvs
  obtain ⟨us, -, ws, hws, rfl⟩ := hvs
  obtain ⟨wa, hwa, ws', hws', rfl⟩ := mapM_cons_ok hws
  obtain ⟨wb, hwb, ws'', hws'', rfl⟩ := mapM_cons_ok hws'
  have hnil : ws'' = [] := by
    simpa only [List.mapM_nil, pure, Except.pure, Except.ok.injEq, eq_comm] using hws''
  obtain ⟨xa, rfl⟩ := VDecl.evalExp_caseE_shape hwa
  obtain ⟨xb, rfl⟩ := VDecl.evalExp_caseE_shape hwb
  exact ⟨_, hv.symm, us, xa, xb, by rw [hnil]⟩

/-- **A code expression ending in `a`, `b` evaluates to a list ending in them.** -/
theorem evalExp_lastPair {env : Env} {ρ : VarEnv} (n : Nat) :
    ∀ {e : Exp} {a b : MixopS} {v : Value}, lastPair e = some (a, b) →
      evalExp n env ρ e = .ok v → ∃ cs, v = .list cs ∧ EndsIn a b cs := by
  induction n with
  | zero => intro e a b v _ h; simp [evalExp] at h
  | succ n ih =>
    intro e a b v ha h
    cases e
    case listE es =>
      rcases n with _ | n
      · simp [evalExp, evalExps] at h
      · exact evalExp_listE_pair ha h
    case catE e₁ e₂ =>
      have ha₂ : lastPair e₂ = some (a, b) := by simpa only [lastPair] using ha
      obtain ⟨v₁, -, v₂, h₂, hc⟩ := VInv.eval_catE h
      obtain ⟨cs₂, rfl, pre, wa, wb, rfl⟩ := ih ha₂ h₂
      rcases v₁ with _ | _ | _ | _ | _ | _ | cs₁ | _ <;>
        simp only [Value.cat?, reduceCtorEq, Option.some.injEq] at hc
      exact ⟨cs₁ ++ (pre ++ [.case a wa, .case b wb]), hc.symm, cs₁ ++ pre, wa, wb, by simp⟩
    all_goals simp [lastPair] at ha

end Silmaril.Wasm.SpecTec.Sim.Round7.HPair
