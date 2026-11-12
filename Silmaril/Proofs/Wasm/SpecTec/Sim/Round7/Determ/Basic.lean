module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Determ.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc.Thms

/-!
# Round 7, determination: basic facts about `ExpFree` values and scopes

* `GoodX`, `GoodXs`: `Round7.Script.GoodEv`, and no atom event is `EXPORTS`.
* `ExpFree` of the parts of an `ExpFree` value, and of the values the value-level operations of
  the evaluator build from `ExpFree` values (`cat?`, `comp?`, `setField` away from `EXPORTS`, …).
* `AllEF` of the scopes built by binding `ExpFree` values.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script
open Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree (ExpFree valInv_expFree)

/-! ## Harmless syntax -/

/-- A harmless event for `ExpFree`: `GoodEv`, and an atom other than `EXPORTS`. -/
def GoodX (e : Ev) : Prop := GoodEv e ∧ ∀ a, e = .atom a → a ≠ "EXPORTS"

/-- Every event of `l` is `GoodX`. -/
def GoodXs (l : List Ev) : Prop := ∀ e ∈ l, GoodX e

@[simp] theorem goodXs_nil : GoodXs [] := by simp [GoodXs]

@[simp] theorem goodXs_cons {e : Ev} {l : List Ev} : GoodXs (e :: l) ↔ GoodX e ∧ GoodXs l := by
  simp [GoodXs]

@[simp] theorem goodXs_append {l₁ l₂ : List Ev} : GoodXs (l₁ ++ l₂) ↔ GoodXs l₁ ∧ GoodXs l₂ := by
  simp only [GoodXs, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

@[simp] theorem goodX_atom {a : String} : GoodX (.atom a) ↔ a ≠ "EXPORTS" := by
  simp [GoodX, GoodEv]

@[simp] theorem goodX_ref1 {x : String} : GoodX (.ref 1 x) ↔ GoodName x := by
  simp [GoodX, GoodEv]

@[simp] theorem goodX_ref0 {x : String} : GoodX (.ref 0 x) ↔ (0, x) ∈ stepReach := by
  simp [GoodX, GoodEv]

@[simp] theorem goodX_ref2 {x : String} : GoodX (.ref 2 x) := by simp [GoodX, GoodEv]

@[simp] theorem goodX_ref3 {x : String} : GoodX (.ref 3 x) := by simp [GoodX, GoodEv]

@[simp] theorem goodX_comp : GoodX .comp := by simp [GoodX, GoodEv]

@[simp] theorem goodX_upd {r : Exp} {ats : List String} : GoodX (.upd r ats) := by
  simp [GoodX, GoodEv]

theorem goodEvs_of_goodXs {l : List Ev} (h : GoodXs l) : GoodEvs l := fun e he => (h e he).1

theorem goodXs_flatMap {α : Type} {f : α → List Ev} {xs : List α} :
    GoodXs (xs.flatMap f) ↔ ∀ x ∈ xs, GoodXs (f x) := by
  simp only [GoodXs, List.mem_flatMap]
  exact ⟨fun h x hx e he => h e ⟨x, hx, he⟩, fun h e ⟨x, hx, he⟩ => h x hx e he⟩

/-- **The body of a reachable item other than `$utf8` and `name` is `GoodXs`.** -/
theorem goodXs_of_reach {n : Nat × String} (hn : n ∉ utf8Allowed) {l : List Ev}
    (hR : ∀ r ∈ evRefs l, r ∈ stepReach) (hok : ∀ e ∈ l, evOk n e = true) : GoodXs l := by
  intro e he
  refine ⟨goodEvs_of_reach hn hR hok e he, fun a ha => ?_⟩
  have ho := hok e he
  rw [ha] at ho
  simpa [evOk] using ho

theorem goodXs_exps : ∀ {es : List Exp}, GoodXs (evExps es) → ∀ e ∈ es, GoodXs (evExp e)
  | [], _ => by simp
  | e :: es, h => by
    simp only [evExps, goodXs_append] at h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact goodXs_exps h.2 e' he'

theorem goodXs_doms : ∀ {ds : List Dom}, GoodXs (evDoms ds) → ∀ e ∈ ds.map domSrc, GoodXs (evExp e)
  | [], _ => by simp
  | .mk x e :: ds, h => by
    simp only [evDoms, goodXs_append] at h
    intro e' he'
    simp only [List.map_cons, List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact h.1
    · exact goodXs_doms h.2 e' he'

theorem goodXs_doms' : ∀ {ds : List Dom}, GoodXs (evDoms ds) → ∀ d ∈ ds, GoodXs (evExp (domSrc d))
  | [], _ => by simp
  | .mk x e :: ds, h => by
    simp only [evDoms, goodXs_append] at h
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact goodXs_doms' h.2 d hd

theorem goodXs_args : ∀ {ags : List Arg}, GoodXs (evArgs ags) → ∀ a ∈ ags, GoodXs (evArg a)
  | [], _ => by simp
  | a :: ags, h => by
    simp only [evArgs, goodXs_append] at h
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact h.1
    · exact goodXs_args h.2 a' ha'

theorem goodXs_prems : ∀ {ps : List Prem}, GoodXs (evPrems ps) → ∀ p ∈ ps, GoodXs (evPrem p)
  | [], _ => by simp
  | p :: ps, h => by
    simp only [evPrems, goodXs_append] at h
    intro p' hp'
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact h.1
    · exact goodXs_prems h.2 p' hp'

theorem goodXs_fields : ∀ {fs : List ExpField}, GoodXs (evEFields fs) →
    ∀ a e, ExpField.mk a e ∈ fs → a ≠ "EXPORTS" ∧ GoodXs (evExp e)
  | [], _ => by simp
  | .mk a e :: fs, h => by
    simp only [evEFields, goodXs_cons, goodXs_append, goodX_atom] at h
    intro a' e' he'
    rcases List.mem_cons.1 he' with he' | he'
    · cases he'; exact ⟨h.1, h.2.1⟩
    · exact goodXs_fields h.2.2 a' e' he'

/-- **The clauses `utf8Env B` finds for a `GoodName` are `GoodXs`.** -/
theorem goodXClauses (B : Builtins) {x : IL.Id} (hx : GoodName x) {d : DefDef}
    (hd : (utf8Env B).findDef? x = some d) : ∀ c ∈ d.2.2, GoodXs (evClause c) := by
  rw [Round7.findDef?_utf8Env_of_ne B hx.2] at hd
  obtain ⟨hR, hok⟩ := findDef?_reach hx.1 hd
  have hn : (1, x) ∉ utf8Allowed := by simp [utf8Allowed, hx.2]
  have h := goodXs_of_reach hn hR hok
  simp only [defDefEv, goodXs_append, goodXs_flatMap] at h
  exact h.2

/-- **The rules `utf8Env B` finds for a reachable relation are `GoodXs`.** -/
theorem goodXRules (B : Builtins) {x : IL.Id} (hx : (0, x) ∈ stepReach) {d : RelDef}
    (hd : (utf8Env B).findRel? x = some d) : ∀ r ∈ d.2.2.2, GoodXs (evRule r) := by
  rw [Round7.findRel?_utf8Env] at hd
  obtain ⟨hR, hok⟩ := findRel?_reach hx hd
  have hn : (0, x) ∉ utf8Allowed := by simp [utf8Allowed]
  have h := goodXs_of_reach hn hR hok
  simp only [relDefEv, goodXs_append, goodXs_flatMap] at h
  exact h.2

/-! ## Parts of `ExpFree` values -/

theorem ef_tuple {vs : List Value} : ExpFree (.tuple vs) ↔ ∀ w ∈ vs, ExpFree w :=
  ⟨fun h => by cases h; assumption, .tuple⟩

theorem ef_list {vs : List Value} : ExpFree (.list vs) ↔ ∀ w ∈ vs, ExpFree w :=
  ⟨fun h => by cases h; assumption, .list⟩

theorem ef_case {op : MixopS} {w : Value} : ExpFree (.case op w) ↔ ExpFree w :=
  ⟨fun h => by cases h; assumption, .case op⟩

theorem ef_optSome {w : Value} : ExpFree (.opt (some w)) ↔ ExpFree w :=
  ⟨fun h => by cases h with | opt h => exact h w rfl,
    fun h => .opt fun w' hw' => by cases hw'; exact h⟩

theorem ef_optNone : ExpFree (.opt none) := .opt fun _ h => by cases h

theorem ef_opt {o : Option Value} : ExpFree (.opt o) ↔ ∀ w ∈ o, ExpFree w :=
  ⟨fun h => by cases h; assumption, .opt⟩

theorem ef_struct {gs : List (AtomS × Value)} : ExpFree (.struct gs) ↔
    (∀ p ∈ gs, ExpFree p.2) ∧ ∀ p ∈ gs, p.1 = "EXPORTS" → p.2 = .list [] :=
  ⟨fun h => by cases h; exact ⟨by assumption, by assumption⟩, fun h => .struct h.1 h.2⟩

theorem ef_bool (b : Bool) : ExpFree (.bool b) := .bool b

theorem ef_num (n : Num) : ExpFree (.num n) := .num n

theorem ef_listNil : ExpFree (.list []) := .list fun _ h => by cases h

theorem ef_of_asTuple {v : Value} {vs : List Value} (hv : ExpFree v) (h : v.asTuple? = some vs) :
    ∀ w ∈ vs, ExpFree w := valInv_expFree.tup v vs hv h

theorem ef_of_asList {v : Value} {vs : List Value} (hv : ExpFree v) (h : v.asList? = some vs) :
    ∀ w ∈ vs, ExpFree w := valInv_expFree.list v vs hv h

theorem ef_of_asOpt {v w : Value} (hv : ExpFree v) (h : v.asOpt? = some (some w)) : ExpFree w :=
  valInv_expFree.opt v w hv h

theorem ef_of_asCase {v w : Value} {op : MixopS} (hv : ExpFree v) (h : v.asCase? = some (op, w)) :
    ExpFree w := valInv_expFree.case v op w hv h

theorem ef_of_asStruct {v : Value} {gs : List (AtomS × Value)} (hv : ExpFree v)
    (h : v.asStruct? = some gs) : ∀ p ∈ gs, ExpFree p.2 := valInv_expFree.struct v gs hv h

/-! ## The value-level operations -/

theorem ef_field {v w : Value} {a : AtomS} (hv : ExpFree v) (h : v.field? a = some w) :
    ExpFree w := by
  cases v with
  | struct gs =>
    have hp := (ef_struct.1 hv).1
    simp only [Value.field?_struct, Option.map_eq_some_iff] at h
    obtain ⟨p, hp', rfl⟩ := h
    exact hp p (List.mem_of_find?_eq_some hp')
  | _ => simp [Value.field?] at h

theorem ef_idx {v w : Value} {i : Nat} (hv : ExpFree v) (h : v.idx? i = some w) : ExpFree w := by
  cases v with
  | list vs => exact ef_list.1 hv w (List.mem_of_getElem? h)
  | _ => simp [Value.idx?] at h

theorem ef_slice {v w : Value} {i k : Nat} (hv : ExpFree v) (h : v.slice? i k = some w) :
    ExpFree w := by
  cases v with
  | list vs =>
    simp only [Value.slice?] at h
    split at h
    · cases h
      exact ef_list.2 fun u hu => ef_list.1 hv u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
    · cases h
  | _ => simp [Value.slice?] at h

theorem ef_cat {v₁ v₂ w : Value} (h₁ : ExpFree v₁) (h₂ : ExpFree v₂) (h : Value.cat? v₁ v₂ = some w) :
    ExpFree w := by
  unfold Value.cat? at h
  split at h <;> cases h
  · exact ef_list.2 fun u hu => (List.mem_append.1 hu).elim (ef_list.1 h₁ u) (ef_list.1 h₂ u)
  · exact h₂
  · exact h₁

mutual
theorem ef_comp : ∀ {v₁ v₂ w : Value}, ExpFree v₁ → ExpFree v₂ → Value.comp? v₁ v₂ = some w →
    ExpFree w
  | .list a, .list b, w, h₁, h₂, h => by
    simp only [Value.comp?_list, Option.some.injEq] at h
    subst h
    exact ef_list.2 fun u hu => (List.mem_append.1 hu).elim (ef_list.1 h₁ u) (ef_list.1 h₂ u)
  | .opt none, .opt o, w, _, h₂, h => by
    simp only [Value.comp?, Option.some.injEq] at h
    subst h; exact h₂
  | .opt (some u), .opt none, w, h₁, _, h => by
    simp only [Value.comp?, Option.some.injEq] at h
    subst h; exact h₁
  | .opt (some _), .opt (some _), w, _, _, h => by simp [Value.comp?] at h
  | .struct f₁, .struct f₂, w, h₁, h₂, h => by
    simp only [Value.comp?, Option.map_eq_some_iff] at h
    obtain ⟨f, hf, rfl⟩ := h
    exact ef_compFields hf h₁ h₂
  | .bool _, _, _, _, _, h => by simp [Value.comp?] at h
  | .num _, _, _, _, _, h => by simp [Value.comp?] at h
  | .text _, _, _, _, _, h => by simp [Value.comp?] at h
  | .tuple _, _, _, _, _, h => by simp [Value.comp?] at h
  | .case _ _, _, _, _, _, h => by simp [Value.comp?] at h
  | .list _, .bool _, _, _, _, h => by simp [Value.comp?] at h
  | .list _, .num _, _, _, _, h => by simp [Value.comp?] at h
  | .list _, .text _, _, _, _, h => by simp [Value.comp?] at h
  | .list _, .tuple _, _, _, _, h => by simp [Value.comp?] at h
  | .list _, .case _ _, _, _, _, h => by simp [Value.comp?] at h
  | .list _, .struct _, _, _, _, h => by simp [Value.comp?] at h
  | .list _, .opt _, _, _, _, h => by simp [Value.comp?] at h
  | .opt (some _), .bool _, _, _, _, h => by simp [Value.comp?] at h
  | .opt (some _), .num _, _, _, _, h => by simp [Value.comp?] at h
  | .opt (some _), .text _, _, _, _, h => by simp [Value.comp?] at h
  | .opt (some _), .tuple _, _, _, _, h => by simp [Value.comp?] at h
  | .opt (some _), .case _ _, _, _, _, h => by simp [Value.comp?] at h
  | .opt (some _), .struct _, _, _, _, h => by simp [Value.comp?] at h
  | .opt (some _), .list _, _, _, _, h => by simp [Value.comp?] at h
  | .opt none, .bool _, _, _, _, h => by simp [Value.comp?] at h
  | .opt none, .num _, _, _, _, h => by simp [Value.comp?] at h
  | .opt none, .text _, _, _, _, h => by simp [Value.comp?] at h
  | .opt none, .tuple _, _, _, _, h => by simp [Value.comp?] at h
  | .opt none, .case _ _, _, _, _, h => by simp [Value.comp?] at h
  | .opt none, .struct _, _, _, _, h => by simp [Value.comp?] at h
  | .opt none, .list _, _, _, _, h => by simp [Value.comp?] at h
  | .struct _, .bool _, _, _, _, h => by simp [Value.comp?] at h
  | .struct _, .num _, _, _, _, h => by simp [Value.comp?] at h
  | .struct _, .text _, _, _, _, h => by simp [Value.comp?] at h
  | .struct _, .tuple _, _, _, _, h => by simp [Value.comp?] at h
  | .struct _, .case _ _, _, _, _, h => by simp [Value.comp?] at h
  | .struct _, .list _, _, _, _, h => by simp [Value.comp?] at h
  | .struct _, .opt _, _, _, _, h => by simp [Value.comp?] at h

theorem ef_compFields : ∀ {f₁ f₂ f : List (AtomS × Value)}, Value.compFields? f₁ f₂ = some f →
    ExpFree (.struct f₁) → ExpFree (.struct f₂) → ExpFree (.struct f)
  | [], [], f, h, _, _ => by
    simp only [Value.compFields?_nil, Option.some.injEq] at h
    subst h; exact .struct (fun _ h => by cases h) (fun _ h => by cases h)
  | [], _ :: _, f, h, _, _ => by simp [Value.compFields?] at h
  | _ :: _, [], f, h, _, _ => by simp [Value.compFields?] at h
  | (a₁, v₁) :: f₁, (a₂, v₂) :: f₂, f, h, h₁, h₂ => by
    have e₁ := ef_struct.1 h₁
    have e₂ := ef_struct.1 h₂
    simp only [Value.compFields?] at h
    split at h
    · rename_i ha
      subst ha
      split at h
      · rename_i v g hv hg
        simp only [Option.some.injEq] at h
        subst h
        have hv' : ExpFree v := ef_comp (e₁.1 _ List.mem_cons_self) (e₂.1 _ List.mem_cons_self) hv
        have hg' := ef_struct.1 (ef_compFields hg
          (.struct (fun p hp => e₁.1 p (List.mem_cons_of_mem _ hp))
            (fun p hp => e₁.2 p (List.mem_cons_of_mem _ hp)))
          (.struct (fun p hp => e₂.1 p (List.mem_cons_of_mem _ hp))
            (fun p hp => e₂.2 p (List.mem_cons_of_mem _ hp))))
        refine .struct (fun p hp => ?_) (fun p hp hpa => ?_)
        · rcases List.mem_cons.1 hp with rfl | hp
          · exact hv'
          · exact hg'.1 p hp
        · rcases List.mem_cons.1 hp with rfl | hp
          · have hl₁ := e₁.2 _ List.mem_cons_self hpa
            have hl₂ := e₂.2 _ List.mem_cons_self hpa
            simp only at hl₁ hl₂
            subst hl₁; subst hl₂
            simp only [Value.comp?_list, List.append_nil, Option.some.injEq] at hv
            exact hv.symm
          · exact hg'.2 p hp hpa
      · cases h
    · cases h
end

theorem ef_setField {v w u : Value} {a : AtomS} (ha : a ≠ "EXPORTS") (hv : ExpFree v)
    (hw : ExpFree w) (h : v.setField a w = some u) : ExpFree u := by
  cases v with
  | struct gs =>
    have e := ef_struct.1 hv
    simp only [Value.setField_struct, Option.some.injEq] at h
    subst h
    refine .struct (fun p hp => ?_) (fun p hp hpa => ?_)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      split
      · exact hw
      · exact e.1 q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      split at hpa
      · rename_i hqa
        exact absurd (hqa.symm.trans hpa) ha
      · rename_i hqa
        simp only [hqa, ↓reduceIte] at hpa ⊢
        exact e.2 q hq hpa
  | _ => simp [Value.setField] at h

theorem ef_setIdx {v w u : Value} {i : Nat} (hv : ExpFree v) (hw : ExpFree w)
    (h : v.setIdx i w = some u) : ExpFree u := by
  cases v with
  | list vs =>
    simp only [Value.setIdx] at h
    split at h
    · cases h
      exact ef_list.2 fun x hx => by
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact ef_list.1 hv x hx
        · exact hw
    · cases h
  | _ => simp [Value.setIdx] at h

theorem ef_setSlice {v w u : Value} {i k : Nat} (hv : ExpFree v) (hw : ExpFree w)
    (h : v.setSlice i k w = some u) : ExpFree u := by
  unfold Value.setSlice at h
  split at h
  · split at h
    · cases h
      rename_i vs ws _
      refine ef_list.2 fun x hx => ?_
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact ef_list.1 hv x (List.mem_of_mem_take hx)
      · exact ef_list.1 hw x hx
      · exact ef_list.1 hv x (List.mem_of_mem_drop hx)
    · cases h
  · cases h

theorem ef_unValue {op : UnOp} {v w : Value} (h : unValue op v = .ok w) : ExpFree w := by
  unfold unValue at h
  split at h
  · cases h; exact ef_bool _
  · obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 (Res.ofOption_eq_ok.1 h)
    exact ef_num _
  · cases h

theorem ef_binValues {op : BinOp} {v₁ v₂ w : Value} (h : binValues op v₁ v₂ = .ok w) :
    ExpFree w := by
  unfold binValues at h
  split at h
  · obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 (Res.ofOption_eq_ok.1 h)
    exact ef_bool _
  · obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 (Res.ofOption_eq_ok.1 h)
    exact ef_num _
  · cases h

theorem ef_cmpValues {op : CmpOp} {v₁ v₂ w : Value} (h : cmpValues op v₁ v₂ = .ok w) :
    ExpFree w := by
  unfold cmpValues at h
  split at h
  · cases h; exact ef_bool _
  · cases h; exact ef_bool _
  · obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 (Res.ofOption_eq_ok.1 h)
    exact ef_bool _
  · cases h

theorem ef_memValue {v₁ v₂ w : Value} (h : memValue v₁ v₂ = .ok w) : ExpFree w := by
  unfold memValue at h
  split at h <;> first | (cases h; exact ef_bool _) | cases h

theorem ef_boolShort {op : BinOp} {v w : Value} (h : boolShort op v = some w) : ExpFree w := by
  unfold boolShort at h
  split at h <;> first | (cases h; exact ef_bool _) | cases h

/-! ## Scopes -/

theorem allEF_empty : AllEF VarEnv.empty := by simp [AllEF, VarEnv.empty, Map.empty]

theorem allEF_bindVal {ρ : VarEnv} (h : AllEF ρ) (x : IL.Id) {v : Value} (hv : ExpFree v) :
    AllEF (ρ.bindVal x v) := by
  intro p hp
  simp only [VarEnv.bindVal, Map.bind] at hp
  split at hp
  · exact h p hp
  · rcases List.mem_cons.1 hp with rfl | hp
    · exact hv
    · exact h p hp

theorem allEF_bindVals {ρ : VarEnv} (h : AllEF ρ) :
    ∀ {xs : List (IL.Id × Value)}, (∀ p ∈ xs, ExpFree p.2) → AllEF (ρ.bindVals xs) := by
  intro xs hxs
  induction xs generalizing ρ with
  | nil => exact h
  | cons p xs ih =>
    have h₁ : AllEF (ρ.bindVal p.1 p.2) := allEF_bindVal h p.1 (hxs p List.mem_cons_self)
    exact ih h₁ fun q hq => hxs q (List.mem_cons_of_mem _ hq)

theorem allEF_of_vals {ρ ρ' : VarEnv} (h : AllEF ρ) (he : ρ'.vals = ρ.vals) : AllEF ρ' := by
  intro p hp; rw [he] at hp; exact h p hp

theorem ef_findVal {ρ : VarEnv} (h : AllEF ρ) {x : IL.Id} {w : Value}
    (hx : ρ.findVal? x = some w) : ExpFree w :=
  h (x, w) (mem_of_find? hx)

theorem mapM_option_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = some y
  | [], ys, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y₀, h₀, ys', h', rfl⟩ := h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, h₀⟩
    · obtain ⟨x', hx', hfx⟩ := mapM_option_mem h' y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', hfx⟩

theorem ef_findVals {ρ : VarEnv} (h : AllEF ρ) :
    ∀ {xs : List IL.Id} {ws : List Value}, ρ.findVals? xs = some ws → ∀ w ∈ ws, ExpFree w := by
  intro xs ws hx w hw
  simp only [VarEnv.findVals?] at hx
  obtain ⟨x, _, hfx⟩ := mapM_option_mem hx w hw
  exact ef_findVal h hfx

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
