module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.Path

/-!
# Round 8 (copy  for `EXPORTS` fields), the whole-evaluator erasure: scopes, related results and value facts (unrefined)

Round 9 copy 's `Round8.CodeErase` (itself a copy 's export erasure) for
`EXPORTS` fields with an arbitrary injective replacement `XTau.τ` (`swapX`); the prose below,
written for the earlier copies, speaks of erasure. Every value is in the swap set (`fun _ => True`).

The pieces `Round7/EraseAll/Step*.lean` use at every member of the evaluator:

* scopes: `eraseScope` commutes with every binding operation and leaves the type, definition and
  grammar namespaces alone; `SG` survives every binding the evaluator makes;
* related results (`ER`): `bind`, `map`, `ofOption`, `assert`, `elimUndef`, `mapM`, `foldlM`;
* value facts: literal tests and `asStruct?` read alike on erased values, iteration rows and
  columns commute with erasure, and the composition `nilLit ++ e` of `Deftype_ok` keeps the swap
  set and commutes with erasure (`comp?_nilLit`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase (eraseScope ScopeIn find?_eraseScope)

variable {Q : Value → Prop} {gd : String → Bool}

/-! ## Scopes -/

@[simp] theorem eraseScope_typs (ρ : VarEnv) : (eraseScope ρ).typs = ρ.typs := rfl
@[simp] theorem eraseScope_defs (ρ : VarEnv) : (eraseScope ρ).defs = ρ.defs := rfl
@[simp] theorem eraseScope_grams (ρ : VarEnv) : (eraseScope ρ).grams = ρ.grams := rfl

@[simp] theorem eraseScope_findDef (ρ : VarEnv) (x : IL.Id) :
    (eraseScope ρ).findDef? x = ρ.findDef? x := rfl
@[simp] theorem eraseScope_findTyp (ρ : VarEnv) (x : IL.Id) :
    (eraseScope ρ).findTyp? x = ρ.findTyp? x := rfl
@[simp] theorem eraseScope_findGram (ρ : VarEnv) (x : IL.Id) :
    (eraseScope ρ).findGram? x = ρ.findGram? x := rfl

theorem eraseScope_empty : eraseScope VarEnv.empty = VarEnv.empty := rfl

theorem map_bind (m : Map Value) (x : IL.Id) (v : Value) :
    (m.bind x v).map (fun p => (p.1, swapX p.2)) =
      Map.bind (m.map fun p => (p.1, swapX p.2)) x (swapX v) := by
  unfold Map.bind
  split <;> simp

theorem eraseScope_bindVal (ρ : VarEnv) (x : IL.Id) (v : Value) :
    eraseScope (ρ.bindVal x v) = (eraseScope ρ).bindVal x (swapX v) := by
  simp only [eraseScope, VarEnv.bindVal, map_bind]

theorem map_binds : ∀ (xs : List (IL.Id × Value)) (m : Map Value),
    (m.binds xs).map (fun p => (p.1, swapX p.2)) =
      Map.binds (m.map fun p => (p.1, swapX p.2)) (xs.map eraseP)
  | [], _ => rfl
  | (y, u) :: xs, m => by
    have := map_binds xs (m.bind y u)
    simp only [Map.binds, List.foldl_cons, List.map_cons] at this ⊢
    rw [this, map_bind]
    rfl

theorem eraseScope_bindVals (ρ : VarEnv) (xs : List (IL.Id × Value)) :
    eraseScope (ρ.bindVals xs) = (eraseScope ρ).bindVals (xs.map eraseP) := by
  simp only [eraseScope, VarEnv.bindVals, map_binds]

theorem eraseScope_bindTyp (ρ : VarEnv) (x : IL.Id) (t : Typ) :
    eraseScope (ρ.bindTyp x t) = (eraseScope ρ).bindTyp x t := rfl

theorem eraseScope_bindDef (ρ : VarEnv) (x y : IL.Id) :
    eraseScope (ρ.bindDef x y) = (eraseScope ρ).bindDef x y := rfl

theorem eraseScope_bindGram (ρ : VarEnv) (x : IL.Id) (g : Sym) :
    eraseScope (ρ.bindGram x g) = (eraseScope ρ).bindGram x g := rfl

theorem findVals?_eraseScope (ρ : VarEnv) : ∀ xs : List IL.Id,
    (eraseScope ρ).findVals? xs = (ρ.findVals? xs).map (List.map swapX)
  | [] => rfl
  | x :: xs => by
    have ih := findVals?_eraseScope ρ xs
    simp only [VarEnv.findVals?, List.mapM_cons] at ih ⊢
    rw [find?_eraseScope, ih]
    cases ρ.findVal? x <;> cases List.mapM ρ.findVal? xs <;> rfl

theorem sg_empty : SG Q gd VarEnv.empty := by
  refine ⟨fun p h => ?_, fun p h => ?_⟩ <;> simp [VarEnv.empty, Map.empty] at h

theorem mem_bind {α : Type} {m : Map α} {x : IL.Id} {v : α} {p : IL.Id × α}
    (h : p ∈ m.bind x v) : p = (x, v) ∨ p ∈ m := by
  unfold Map.bind at h
  split at h
  · exact Or.inr h
  · exact List.mem_cons.1 h

theorem mem_binds {α : Type} : ∀ {xs : List (IL.Id × α)} {m : Map α} {p : IL.Id × α},
    p ∈ m.binds xs → p ∈ xs ∨ p ∈ m
  | [], _, _, h => Or.inr h
  | (y, u) :: xs, m, p, h => by
    rcases mem_binds (xs := xs) (m := m.bind y u) h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases mem_bind h with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr h

theorem SG.bindVal {ρ : VarEnv} (h : SG Q gd ρ) {x : IL.Id} {v : Value} (hv : AllIn Q v) :
    SG Q gd (ρ.bindVal x v) := by
  refine ⟨fun p hp => ?_, h.2⟩
  rcases mem_bind hp with rfl | hp
  · exact hv
  · exact h.1 p hp

theorem SG.bindVals {ρ : VarEnv} (h : SG Q gd ρ) {xs : List (IL.Id × Value)}
    (hx : ∀ p ∈ xs, AllIn Q p.2) : SG Q gd (ρ.bindVals xs) := by
  refine ⟨fun p hp => ?_, h.2⟩
  rcases mem_binds hp with hp | hp
  · exact hx p hp
  · exact h.1 p hp

theorem SG.bindTyp {ρ : VarEnv} (h : SG Q gd ρ) (x : IL.Id) (t : Typ) :
    SG Q gd (ρ.bindTyp x t) := h

theorem SG.bindGram {ρ : VarEnv} (h : SG Q gd ρ) (x : IL.Id) (g : Sym) :
    SG Q gd (ρ.bindGram x g) := h

theorem SG.bindDef {ρ : VarEnv} (h : SG Q gd ρ) {x y : IL.Id} (hy : gd y = true) :
    SG Q gd (ρ.bindDef x y) := by
  refine ⟨h.1, fun p hp => ?_⟩
  rcases mem_bind hp with rfl | hp
  · exact hy
  · exact h.2 p hp

theorem SG.eraseScope {ρ : VarEnv} (h : SG Q gd ρ) : DefsG gd (eraseScope ρ) := h.2

theorem SG.find? {ρ : VarEnv} (h : SG Q gd ρ) {x : IL.Id} {v : Value}
    (hv : ρ.findVal? x = some v) : AllIn Q v :=
  Erase.ScopeIn.find? h.1 hv

theorem SG.findVals? {ρ : VarEnv} (h : SG Q gd ρ) : ∀ {xs : List IL.Id} {vs : List Value},
    ρ.findVals? xs = some vs → ∀ v ∈ vs, AllIn Q v
  | [], vs, hv => by
    simp only [VarEnv.findVals?_nil, Option.some.injEq] at hv
    subst hv; simp
  | x :: xs, vs, hv => by
    simp only [VarEnv.findVals?, List.mapM_cons] at hv
    cases hw : ρ.findVal? x with
    | none => simp [hw] at hv
    | some w =>
      cases hws : List.mapM ρ.findVal? xs with
      | none => simp [hw, hws] at hv
      | some ws =>
        simp [hw, hws] at hv
        subst hv
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact h.find? hw
        · exact SG.findVals? h (xs := xs) hws v hv

theorem map_find?_mem {α : Type} : ∀ {m : Map α} {x : IL.Id} {y : α}, m.find? x = some y →
    ∃ p ∈ m, p.2 = y
  | [], _, _, h => by simp [Map.find?] at h
  | (z, u) :: m, x, y, h => by
    simp only [Map.find?] at h
    split at h
    · cases h; exact ⟨(z, u), List.mem_cons_self .., rfl⟩
    · obtain ⟨p, hp, hpy⟩ := map_find?_mem h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpy⟩

theorem SG.defName {ρ : VarEnv} (h : SG Q gd ρ) {x : IL.Id} (hx : gd x = true) :
    gd ((ρ.findDef? x).getD x) = true := by
  cases hf : ρ.findDef? x with
  | none => exact hx
  | some y =>
    obtain ⟨p, hp, rfl⟩ := map_find?_mem (m := ρ.defs) hf
    exact h.2 p hp

/-! ## Related results -/

section ER
variable {α β : Type}

theorem ER.error {f : α → α} {P : α → Prop} (e : Stuck) : ER f P (.error e) (.error e) :=
  ⟨rfl, fun _ h => by cases h⟩

theorem ER.ok {f : α → α} {P : α → Prop} {a : α} (h : P a) : ER f P (.ok a) (.ok (f a)) :=
  ⟨rfl, fun _ h' => by cases h'; exact h⟩

theorem ER.bind {f : α → α} {P : α → Prop} {g : β → β} {P' : β → Prop} {r r' : Res α}
    {k k' : α → Res β} (hr : ER f P r r')
    (hk : ∀ a, r = .ok a → P a → ER g P' (k a) (k' (f a))) :
    ER g P' (r >>= k) (r' >>= k') := by
  obtain ⟨rfl, hA⟩ := hr
  cases r with
  | error e => exact ER.error e
  | ok a => exact hk a rfl (hA a rfl)

theorem ER.map {f : α → α} {P : α → Prop} {g : β → β} {P' : β → Prop} {r r' : Res α}
    (h : α → β) (hfg : ∀ a, P a → h (f a) = g (h a)) (hP : ∀ a, P a → P' (h a))
    (hr : ER f P r r') : ER g P' (h <$> r) (h <$> r') := by
  obtain ⟨rfl, hA⟩ := hr
  cases r with
  | error e => exact ER.error e
  | ok a =>
    refine ⟨?_, fun b hb => ?_⟩
    · simp [Functor.map, Except.map, hfg a (hA a rfl)]
    · simp only [Functor.map, Except.map, Except.ok.injEq] at hb
      exact hb ▸ hP a (hA a rfl)

theorem ER.ofOption {f : α → α} {P : α → Prop} {o o' : Option α} (he : o' = o.map f)
    (hA : ∀ a, o = some a → P a) : ER f P (Res.ofOption o) (Res.ofOption o') := by
  subst he
  cases o with
  | none => exact ER.error _
  | some a => exact ER.ok (hA a rfl)

theorem ER.assert {f : α → α} {P : α → Prop} {c c' : Prop} [Decidable c] [Decidable c']
    (hc : c ↔ c') {r r' : Res α} (h : c → ER f P r r') :
    ER f P (Res.assert c r) (Res.assert c' r') := by
  by_cases h₁ : c
  · rw [Res.assert_pos h₁, Res.assert_pos (hc.1 h₁)]; exact h h₁
  · rw [Res.assert_neg h₁, Res.assert_neg (fun h₂ => h₁ (hc.2 h₂))]; exact ER.error _

theorem ER.elimUndef {f : α → α} {P : α → Prop} {g : β → β} {P' : β → Prop} {r r' : Res α}
    {k k' : α → Res β} {u u' : Unit → Res β} (hr : ER f P r r')
    (hk : ∀ a, r = .ok a → P a → ER g P' (k a) (k' (f a)))
    (hu : r = .error .undef → ER g P' (u ()) (u' ())) :
    ER g P' (Res.elimUndef r k u) (Res.elimUndef r' k' u') := by
  obtain ⟨rfl, hA⟩ := hr
  rcases r with (_ | _) | a
  · exact hu rfl
  · exact ER.error _
  · exact hk a rfl (hA a rfl)

theorem ER.mapM {f : β → β} {P : β → Prop} {k k' : α → Res β} {h : α → α} :
    ∀ l : List α, (∀ x ∈ l, ER f P (k x) (k' (h x))) →
      ER (List.map f) (fun bs => ∀ b ∈ bs, P b) (l.mapM k) ((l.map h).mapM k')
  | [], _ => ⟨rfl, fun bs hb => by cases hb; simp⟩
  | x :: l, hx => by
    simp only [List.mapM_cons, List.map_cons]
    refine ER.bind (hx x (List.mem_cons_self ..)) fun b _ hb => ?_
    refine ER.bind (ER.mapM l fun y hy => hx y (List.mem_cons_of_mem _ hy)) fun bs _ hbs => ?_
    refine ⟨rfl, fun cs hcs => ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hcs
    subst hcs
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hb
    · exact hbs c hc

theorem ER.mapM' {f : β → β} {P : β → Prop} {k k' : α → Res β} :
    ∀ l : List α, (∀ x ∈ l, ER f P (k x) (k' x)) →
      ER (List.map f) (fun bs => ∀ b ∈ bs, P b) (l.mapM k) (l.mapM k') := by
  intro l hl
  have := ER.mapM (h := id) l hl
  simpa using this

end ER

theorem ER.foldlM {ρ : VarEnv} {step step' : VarEnv → Prem → Res VarEnv} :
    ∀ prs : List Prem, SG Q gd ρ →
      (∀ σ pr, pr ∈ prs → SG Q gd σ → ER eraseScope (SG Q gd) (step σ pr) (step' (eraseScope σ) pr)) →
      ER eraseScope (SG Q gd) (prs.foldlM step ρ) (prs.foldlM step' (eraseScope ρ))
  | [], hρ, _ => ER.ok hρ
  | pr :: prs, hρ, hs => by
    simp only [List.foldlM_cons]
    refine ER.bind (hs ρ pr (List.mem_cons_self ..) hρ) fun σ _ hσ => ?_
    exact ER.foldlM prs hσ fun σ' pr' hpr' hσ' => hs σ' pr' (List.mem_cons_of_mem _ hpr') hσ'

/-- `Res.scan` over related alternatives. -/
theorem ER.scan {f : VarEnv → VarEnv} {P : VarEnv → Prop} {k k' : Nat → Res VarEnv}
    (hk : ∀ j, ER f P (k j) (k' j)) : ∀ i m, ER f P (Res.scan k i m) (Res.scan k' i m)
  | i, 0 => by simp only [Res.scan_zero]; exact hk i
  | i, m + 1 => by
    simp only [Res.scan]
    exact ER.elimUndef (hk i) (fun a _ ha => ER.ok ha) fun _ => ER.scan hk (i + 1) m

/-! ## Values -/

theorem swapX_eq_bool {v : Value} {b : Bool} : swapX v = .bool b ↔ v = .bool b := by
  cases v with
  | opt o => cases o <;> simp
  | _ => simp

theorem swapX_eq_num {v : Value} {m : Num} : swapX v = .num m ↔ v = .num m := by
  cases v with
  | opt o => cases o <;> simp
  | _ => simp

theorem swapX_eq_text {v : Value} {t : Text} : swapX v = .text t ↔ v = .text t := by
  cases v with
  | opt o => cases o <;> simp
  | _ => simp

theorem swapX_eq_optNone {v : Value} : swapX v = .opt none ↔ v = .opt none := by
  cases v with
  | opt o => cases o <;> simp
  | _ => simp

theorem asStruct?_eraseC (v : Value) : (swapX v).asStruct? = v.asStruct?.map swapXf := by
  cases v with
  | opt o => cases o <;> rfl
  | _ => rfl

theorem swapX_num_cases (v : Value) :
    (∃ m, v = .num m ∧ swapX v = .num m) ∨ ((∀ m, v ≠ .num m) ∧ ∀ m, swapX v ≠ .num m) := by
  cases v with
  | num m => exact Or.inl ⟨m, rfl, rfl⟩
  | opt o => cases o <;> simp
  | _ => simp

theorem allIn_struct_fields {gs : List (IL.AtomS × Value)} (h : AllIn Q (.struct gs)) :
    ∀ p ∈ gs, AllIn Q p.2 := by
  have h2 := h.2
  clear h
  induction gs with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨a, v⟩ := g
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h2.1
    · exact ih h2.2 p hp

theorem allIn_list_mem {vs : List Value} (h : AllIn Q (.list vs)) : ∀ v ∈ vs, AllIn Q v :=
  (allIns_iff Q vs).1 h

theorem allIn_tuple_mem {vs : List Value} (h : AllIn Q (.tuple vs)) : ∀ v ∈ vs, AllIn Q v :=
  (allIns_iff Q vs).1 h

theorem allIn_list_of {vs : List Value} (h : ∀ v ∈ vs, AllIn Q v) : AllIn Q (.list vs) :=
  (allIns_iff Q vs).2 h

theorem allIn_tuple_of {vs : List Value} (h : ∀ v ∈ vs, AllIn Q v) : AllIn Q (.tuple vs) :=
  (allIns_iff Q vs).2 h

theorem swapXf_cons_ne {a : IL.AtomS} (ha : a ≠ "EXPORTS") (v : Value)
    (gs : List (IL.AtomS × Value)) : swapXf ((a, v) :: gs) = (a, swapX v) :: swapXf gs := by
  simp [ha]

/-! ## Domains, rows and columns -/

theorem mapM_asOpt_erase : ∀ xvs : List (IL.Id × Value),
    (xvs.map eraseP).mapM (fun (p : IL.Id × Value) => p.2.asOpt?.map fun o => (p.1, o)) =
      (xvs.mapM fun (p : IL.Id × Value) => p.2.asOpt?.map fun o => (p.1, o)).map
        (List.map fun (p : IL.Id × Option Value) => (p.1, p.2.map swapX))
  | [] => rfl
  | (x, v) :: xvs => by
    have ih := mapM_asOpt_erase xvs
    simp only [List.map_cons, List.mapM_cons, eraseP, asOpt?_eraseC] at ih ⊢
    rw [ih]
    cases v.asOpt? <;> cases (xvs.mapM fun (p : IL.Id × Value) => p.2.asOpt?.map fun o => (p.1, o)) <;> rfl

theorem mapM_asList_erase : ∀ xvs : List (IL.Id × Value),
    (xvs.map eraseP).mapM (fun (p : IL.Id × Value) => p.2.asList?.map fun l => (p.1, l)) =
      (xvs.mapM fun (p : IL.Id × Value) => p.2.asList?.map fun l => (p.1, l)).map
        (List.map fun (p : IL.Id × List Value) => (p.1, p.2.map swapX))
  | [] => rfl
  | (x, v) :: xvs => by
    have ih := mapM_asList_erase xvs
    simp only [List.map_cons, List.mapM_cons, eraseP, asList?_eraseC] at ih ⊢
    rw [ih]
    cases v.asList? <;> cases (xvs.mapM fun (p : IL.Id × Value) => p.2.asList?.map fun l => (p.1, l)) <;> rfl

theorem iterRow_erase (ds : List (IL.Id × List Value)) (ido : Option IL.Id) (i : Nat) :
    iterRow (ds.map fun p => (p.1, p.2.map swapX)) ido i = (iterRow ds ido i).map eraseP := by
  simp only [iterRow, List.map_append]
  congr 1
  · induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.map_cons, List.filterMap_cons, List.getElem?_map]
      cases d.2[i]? <;> simp [ih, eraseP]
  · cases ido <;> rfl

theorem iterRows_erase (ds : List (IL.Id × List Value)) (ido : Option IL.Id) (k : Nat) :
    iterRows (ds.map fun p => (p.1, p.2.map swapX)) ido k =
      (iterRows ds ido k).map (List.map eraseP) := by
  simp only [iterRows, List.map_map]
  congr 1
  funext i
  exact iterRow_erase ds ido i

theorem iterCol_erase (rows : List (List Value)) (j : Nat) :
    iterCol (rows.map (List.map swapX)) j = (iterCol rows j).map swapX := by
  simp only [iterCol]
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, List.filterMap_cons, List.getElem?_map]
    cases r[j]? <;> simp [ih]

theorem iterCols_erase (rows : List (List Value)) (k : Nat) :
    iterCols (rows.map (List.map swapX)) k = (iterCols rows k).map swapX := by
  simp only [iterCols, List.map_map]
  congr 1
  funext j
  simp [iterCol_erase, swapXs_eq_map]

theorem allIn_iterRows {ds : List (IL.Id × List Value)} (hd : ∀ d ∈ ds, ∀ v ∈ d.2, AllIn Q v)
    (ido : Option IL.Id) (k : Nat) : ∀ r ∈ iterRows ds ido k, ∀ p ∈ r, AllIn Q p.2 := by
  intro r hr p hp
  simp only [iterRows, List.mem_map, List.mem_range] at hr
  obtain ⟨i, -, rfl⟩ := hr
  simp only [iterRow, List.mem_append, List.mem_filterMap, Option.map_eq_some_iff,
    Option.mem_toList, Option.map_eq_some_iff] at hp
  rcases hp with ⟨d, hd', v, hv, rfl⟩ | ⟨y, -, rfl⟩
  · exact hd d hd' v (List.mem_of_getElem? hv)
  · trivial

theorem allIn_iterCols {rows : List (List Value)} (h : ∀ r ∈ rows, ∀ u ∈ r, AllIn Q u) (k : Nat) :
    ∀ v ∈ iterCols rows k, AllIn Q v := by
  intro v hv
  simp only [iterCols, List.mem_map, List.mem_range] at hv
  obtain ⟨j, -, rfl⟩ := hv
  refine allIn_list_of fun u hu => ?_
  simp only [iterCol, List.mem_filterMap] at hu
  obtain ⟨r, hr, hu⟩ := hu
  exact h r hr u (List.mem_of_getElem? hu)

theorem mapM_some_mem {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β},
    l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h, b, hb => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp at hb
  | a :: l, l', h, b, hb => by
    simp only [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some c =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some cs =>
        simp [ha, hl] at h
        subst h
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ⟨a, List.mem_cons_self .., ha⟩
        · obtain ⟨a', ha', hfa⟩ := mapM_some_mem hl b hb
          exact ⟨a', List.mem_cons_of_mem _ ha', hfa⟩

/-- The domain lists of an iteration, from `AllIn` domain values. -/
theorem allIn_asLists {xvs : List (IL.Id × Value)} (hx : ∀ p ∈ xvs, AllIn Q p.2)
    {ds : List (IL.Id × List Value)}
    (h : (xvs.mapM fun p => p.2.asList?.map fun l => (p.1, l)) = some ds) :
    ∀ d ∈ ds, ∀ v ∈ d.2, AllIn Q v := by
  intro d hd v hv
  obtain ⟨p, hp, hpd⟩ := mapM_some_mem h d hd
  obtain ⟨y, w⟩ := p
  cases w with
  | list l =>
    simp only [Value.asList?, Option.map_some, Option.some.injEq] at hpd
    subst hpd
    exact allIn_list_mem (hx _ hp) v hv
  | opt o => cases o <;> simp [Value.asList?] at hpd
  | _ => simp [Value.asList?] at hpd

theorem allIn_asOpts {xvs : List (IL.Id × Value)} (hx : ∀ p ∈ xvs, AllIn Q p.2)
    {os : List (IL.Id × Option Value)}
    (h : (xvs.mapM fun p => p.2.asOpt?.map fun o => (p.1, o)) = some os) :
    ∀ p ∈ os.filterMap (fun p => p.2.map fun w => (p.1, w)), AllIn Q p.2 := by
  intro q hq
  simp only [List.mem_filterMap, Option.map_eq_some_iff] at hq
  obtain ⟨d, hd, w, hw, rfl⟩ := hq
  obtain ⟨p, hp, hpd⟩ := mapM_some_mem h d hd
  obtain ⟨y, u⟩ := p
  cases u with
  | opt o =>
    simp only [Value.asOpt?, Option.map_some, Option.some.injEq] at hpd
    subst hpd
    simp only at hw
    subst hw
    exact (hx _ hp : AllIn Q (.opt (some w)))
  | _ => simp [Value.asOpt?] at hpd

theorem filterMap_opt_erase (os : List (IL.Id × Option Value)) :
    (os.map fun p => (p.1, p.2.map swapX)).filterMap (fun p => p.2.map fun w => (p.1, w)) =
      (os.filterMap fun p => p.2.map fun w => (p.1, w)).map eraseP := by
  induction os with
  | nil => rfl
  | cons p os ih =>
    obtain ⟨y, o⟩ := p
    cases o <;> simp [ih, eraseP]

/-! ## The composition of `Deftype_ok` -/

/-- A field value of a `nilLit` record: a list or `ε`. -/
def NilV : Value → Prop
  | .list _ => True
  | .opt none => True
  | _ => False

theorem comp?_nilV_erase {a b : Value} (ha : NilV a) (hA : AllIn Q a) (hb : AllIn Q b) :
    Value.comp? (swapX a) (swapX b) = (Value.comp? a b).map swapX ∧
      ∀ u, Value.comp? a b = some u → AllIn Q u := by
  cases a with
  | list l =>
    cases b with
    | list l' =>
      refine ⟨by simp [Value.comp?, swapXs_eq_map], fun u hu => ?_⟩
      simp only [Value.comp?, Option.some.injEq] at hu
      subst hu
      refine allIn_list_of fun x hx => ?_
      rcases List.mem_append.1 hx with hx | hx
      · exact allIn_list_mem hA x hx
      · exact allIn_list_mem hb x hx
    | opt o => cases o <;> simp [Value.comp?]
    | _ => simp [Value.comp?]
  | opt o =>
    cases o with
    | none =>
      cases b with
      | opt o' =>
        refine ⟨by cases o' <;> simp [Value.comp?], fun u hu => ?_⟩
        cases o' <;> simp only [Value.comp?, Option.some.injEq] at hu <;> subst hu
        · trivial
        · exact hb
      | _ => simp [Value.comp?]
    | some _ => exact ha.elim
  | _ => exact ha.elim

theorem compFields?_nil : ∀ (gs fs : List (IL.AtomS × Value)),
    (∀ p ∈ gs, p.1 ≠ "EXPORTS" ∧ NilV p.2 ∧ AllIn Q p.2) → (∀ p ∈ fs, AllIn Q p.2) →
    Value.compFields? (swapXf gs) (swapXf fs) = (Value.compFields? gs fs).map swapXf ∧
      ∀ f, Value.compFields? gs fs = some f → ∀ p ∈ f, p.1 ≠ "EXPORTS" ∧ AllIn Q p.2
  | [], [], _, _ => ⟨rfl, fun f hf => by
      simp only [Value.compFields?, Option.some.injEq] at hf; subst hf; simp⟩
  | [], (a, v) :: fs, _, _ => by simp [Value.compFields?]
  | (a, v) :: gs, [], hg, _ => by
    rw [swapXf_cons_ne (hg (a, v) (List.mem_cons_self ..)).1]
    simp [Value.compFields?]
  | (a, v) :: gs, (a₂, v₂) :: fs, hg, hf => by
    have ha : a ≠ "EXPORTS" := (hg (a, v) (List.mem_cons_self ..)).1
    have hv := hg (a, v) (List.mem_cons_self ..)
    have hv₂ : AllIn Q v₂ := hf (a₂, v₂) (List.mem_cons_self ..)
    obtain ⟨ih, ihA⟩ := compFields?_nil gs fs (fun p hp => hg p (List.mem_cons_of_mem _ hp))
      (fun p hp => hf p (List.mem_cons_of_mem _ hp))
    rw [swapXf_cons_ne ha]
    by_cases hx : a = a₂
    · subst hx
      rw [swapXf_cons_ne ha]
      obtain ⟨hc, hcA⟩ := comp?_nilV_erase hv.2.1 hv.2.2 hv₂
      cases hcv : Value.comp? v v₂ with
      | none => simp [Value.compFields?, hc, ih, hcv]
      | some w =>
        cases hcf : Value.compFields? gs fs with
        | none => simp [Value.compFields?, hc, ih, hcv, hcf]
        | some f =>
          refine ⟨by simp [Value.compFields?, hc, ih, hcv, hcf, ha], fun f' hf' => ?_⟩
          simp only [Value.compFields?, hcv, hcf, ite_true, Option.some.injEq] at hf'
          subst hf'
          intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨ha, hcA w hcv⟩
          · exact ihA f hcf p hp
    · have he : swapXf ((a₂, v₂) :: fs) = (a₂, if a₂ = "EXPORTS" then XTau.τ v₂ else swapX v₂) ::
          swapXf fs := by simp
      rw [he]
      simp [Value.compFields?, hx]

/-- **The composition `nilLit ++ e` commutes with erasure and keeps the swap set.** -/
theorem comp?_nilLit {gs : List (IL.AtomS × Value)} {b : Value}
    (hg : ∀ p ∈ gs, p.1 ≠ "EXPORTS" ∧ NilV p.2 ∧ AllIn Q p.2) (hb : AllIn Q b) :
    Value.comp? (swapX (.struct gs)) (swapX b) = (Value.comp? (.struct gs) b).map swapX ∧
      ∀ u, Value.comp? (.struct gs) b = some u → AllIn Q u := by
  cases b with
  | struct fs =>
    obtain ⟨h, hA⟩ := compFields?_nil gs fs hg (allIn_struct_fields hb)
    simp only [swapX_struct, Value.comp?, h]
    refine ⟨?_, fun u hu => ?_⟩
    · cases Value.compFields? gs fs <;> simp
    · simp only [Option.map_eq_some_iff] at hu
      obtain ⟨f, hf, rfl⟩ := hu
      have hn : NoExpF f := fun p hp => (hA f hf p hp).1
      exact allIn_struct_of_noCode hn fun p hp => (hA f hf p hp).2
  | opt o => cases o <;> simp [Value.comp?]
  | _ => simp [Value.comp?]

/-! ## The syntactic check, unfolded -/

section Syn
variable {gr : String → Bool}

theorem xExps_mem : ∀ {es : List Exp}, xExps gr gd es = true → ∀ e ∈ es, xExp gr gd e = true
  | [], _, _, h => by simp at h
  | e :: es, h, e', he' => by
    simp only [xExps, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact xExps_mem h.2 e' he'

theorem xFields_mem : ∀ {fs : List ExpField}, xFields gr gd fs = true →
    ∀ a e, ExpField.mk a e ∈ fs → a ≠ "EXPORTS" ∧ xExp gr gd e = true
  | [], _, _, _, h => by simp at h
  | .mk b e :: fs, h, a, e', he' => by
    simp only [xFields, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases List.mem_cons.1 he' with he' | he'
    · cases he'; exact ⟨h.1.1, h.1.2⟩
    · exact xFields_mem h.2 a e' he'

theorem xDoms_mem : ∀ {ds : List Dom}, xDoms gr gd ds = true → ∀ d ∈ ds, xExp gr gd (domSrc d) = true
  | [], _, _, h => by simp at h
  | .mk x e :: ds, h, d, hd => by
    simp only [xDoms, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h.1
    · exact xDoms_mem h.2 d hd

theorem xDoms_src : ∀ {ds : List Dom}, xDoms gr gd ds = true → xExps gr gd (ds.map domSrc) = true
  | [], _ => rfl
  | .mk x e :: ds, h => by
    simp only [xDoms, Bool.and_eq_true] at h
    simp only [List.map_cons, xExps, domSrc, h.1, xDoms_src h.2, Bool.and_self]

theorem xArgs_mem : ∀ {l : List Arg}, xArgs gr gd l = true → ∀ a ∈ l, xArg gr gd a = true
  | [], _, _, h => by simp at h
  | a :: l, h, a', ha' => by
    simp only [xArgs, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact h.1
    · exact xArgs_mem h.2 a' ha'

theorem xPrems_mem : ∀ {prs : List Prem}, xPrems gr gd prs = true → ∀ p ∈ prs, xPrem gr gd p = true
  | [], _, _, h => by simp at h
  | p :: prs, h, p', hp' => by
    simp only [xPrems, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hp' with rfl | hp'
    · exact h.1
    · exact xPrems_mem h.2 p' hp'

theorem xPath_dotsOk : ∀ {p : Path}, xPath gr gd p = true → dotsOk p = true
  | .rootP, _ => rfl
  | .idxP p _, h => by
    simp only [xPath, Bool.and_eq_true] at h
    simp only [dotsOk]
    exact xPath_dotsOk h.1
  | .sliceP p _ _, h => by
    simp only [xPath, Bool.and_eq_true] at h
    simp only [dotsOk]
    exact xPath_dotsOk h.1.1
  | .dotP p a, h => by
    simp only [xPath, Bool.and_eq_true] at h
    simp only [dotsOk, h.1, xPath_dotsOk h.2, Bool.and_self]

end Syn

/-! ## `Res.mapM` -/

theorem mapM_ok_mem' {α β : Type} {f : α → Res β} : ∀ {l : List α} {l' : List β},
    l.mapM f = .ok l' → ∀ b ∈ l', ∃ a ∈ l, f a = .ok b
  | [], l', h, b, hb => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp at hb
  | a :: l, l', h, b, hb => by
    simp only [List.mapM_cons, Res.bind_eq_ok] at h
    obtain ⟨c, hc, cs, hcs, hp⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self .., hc⟩
    · obtain ⟨a', ha', hfa⟩ := mapM_ok_mem' hcs b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hfa⟩

/-! ## The left operand of a composition -/

theorem nilV_of_eval {env : Env} {ρ : VarEnv} {e : Exp} (he : nilShape e = true) :
    ∀ {m : Nat} {v : Value}, evalExp m env ρ e = .ok v → NilV v := by
  intro m v h
  rcases m with _ | m
  · simp [evalExp] at h
  cases e with
  | listE es =>
    cases es with
    | nil =>
      rcases m with _ | m
      · simp [evalExp, evalExps] at h
      · simp only [evalExp, evalExps, List.mapM_nil, Res.map_eq_ok] at h
        obtain ⟨_, _, rfl⟩ := h
        trivial
    | cons _ _ => simp [nilShape] at he
  | optE eo =>
    cases eo with
    | none => simp only [evalExp, Except.ok.injEq] at h; subst h; trivial
    | some _ => simp [nilShape] at he
  | iterE e₀ it =>
    obtain ⟨it, ds⟩ := it
    simp only [evalExp] at h
    rcases m with _ | m
    · simp [evalIterE] at h
    cases it with
    | opt => simp [nilShape] at he
    | list =>
      simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, ⟨k, _, h⟩⟩ := h
      rcases m with _ | m
      · simp [evalIterList] at h
      simp only [evalIterList, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      simp only [Except.ok.injEq] at h; subst h; trivial
    | list1 =>
      simp only [evalIterE, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, ⟨k, _, _, h⟩⟩ := h
      rcases m with _ | m
      · simp [evalIterList] at h
      simp only [evalIterList, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      simp only [Except.ok.injEq] at h; subst h; trivial
    | listN eₙ ido =>
      simp only [evalIterE, Res.bind_eq_ok] at h
      obtain ⟨_, _, _, _, k, _, h⟩ := h
      rcases m with _ | m
      · simp [evalIterList] at h
      simp only [evalIterList, Res.bind_eq_ok, Res.assert_eq_ok] at h
      obtain ⟨_, _, _, _, _, h⟩ := h
      simp only [Except.ok.injEq] at h; subst h; trivial
  | _ => simp [nilShape] at he

/-- **The left operand of a composition evaluates to a record of lists and `ε`s.** -/
theorem nilLit_eval {gr : String → Bool} {env : Env} {ρ : VarEnv} {e : Exp}
    (hn : nilLit e = true) (hx : xExp gr gd e = true) {m : Nat} {v : Value}
    (h : evalExp m env ρ e = .ok v) :
    ∃ gs, v = .struct gs ∧ ∀ p ∈ gs, p.1 ≠ "EXPORTS" ∧ NilV p.2 := by
  cases e with
  | strE fs =>
    simp only [nilLit, List.all_eq_true] at hn
    simp only [xExp] at hx
    rcases m with _ | _ | m
    · simp [evalExp] at h
    · simp [evalExp, evalExpFields] at h
    simp only [evalExp, evalExpFields, Res.map_eq_ok] at h
    obtain ⟨gs, hgs, rfl⟩ := h
    refine ⟨gs, rfl, fun p hp => ?_⟩
    obtain ⟨f, hf, hfp⟩ := mapM_ok_mem' hgs p hp
    obtain ⟨a, e⟩ := f
    simp only [Res.map_eq_ok] at hfp
    obtain ⟨w, hw, rfl⟩ := hfp
    exact ⟨(xFields_mem hx a e hf).1, nilV_of_eval (hn _ hf) hw⟩
  | _ => simp [nilLit] at hn

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll
