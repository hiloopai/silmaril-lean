module

public import Silmaril.Raw.Wasm.Wit.Elab.Body

/-!
# Elaboration: elaborated worlds pass the binary checks

`elabWorldItems_good`: when wit-parser's `elaborate_world` (`elabWorldItems`)
succeeds on good items (`ItemGood`), in a good environment (`EnvGood`) whose
interface dependencies are ranked (`EnvRanked`, an acyclic `use` graph), its
imports and exports pass `WorldItem.validB` and `World.namesUniqueB`.

The keys stay distinct because every insertion checks them (`insertNew`,
`insertIfNew`); for exports, `addExport` appends an interface after its
dependencies, which have a smaller rank and therefore another key
(`addExport_inv`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

/-! ## Good items and environments -/

/-- A world item whose names pass the binary checks. -/
def ItemGood : Binary.WorldItem → Prop
  | .ifaceRef i _ _ => IfaceName.validB i = true
  | .ifaceInline n b => Plain n ∧ BodyGood b
  | .func f => FuncGood f
  | .type t => TypeGood t

/-- An environment of good interfaces. -/
def EnvGood (env : Binary.Env) : Prop := ∀ e ∈ env, IfaceName.validB e.1 = true ∧ BodyGood e.2

/-- The dependencies of an interface of the environment have a smaller rank. -/
def EnvRanked (env : Binary.Env) (R : String → Nat) : Prop :=
  ∀ e ∈ env, ∀ j ∈ Binary.directDeps e.2, R j.id < R e.1.id

/-- A list of good items with distinct keys. -/
def LInv (its : List Binary.WorldItem) : Prop :=
  (∀ x ∈ its, ItemGood x) ∧ (its.map Binary.WorldItem.key).Nodup

theorem ItemGood.validB {it : Binary.WorldItem} (h : ItemGood it) : WorldItem.validB it = true := by
  cases it with
  | ifaceRef i _ _ => exact h
  | ifaceInline n b =>
    simp only [WorldItem.validB, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨by simpa using not_mem_of_plain h.1 plainChar_colon, h.2.1⟩
  | func f => exact FuncGood.validB h
  | type _ => rfl

theorem lookup'_mem {i : Binary.IfaceName} {b : Binary.Interface} :
    ∀ {env : Binary.Env}, Binary.liveDeps.lookup' i env = some b → (i, b) ∈ env
  | [], h => by cases h
  | (j, b') :: xs, h => by
    unfold Binary.liveDeps.lookup' at h
    by_cases hj : j = i
    · simp only [hj, ite_true, Option.some.injEq] at h
      subst hj; subst h
      exact List.mem_cons_self
    · simp only [hj, ite_false] at h
      exact List.mem_cons_of_mem _ (lookup'_mem h)

theorem find?_mem {env : Binary.Env} {i : Binary.IfaceName} {b : Binary.Interface}
    (h : Binary.Env.find? env i = some b) : (i, b) ∈ env := lookup'_mem h

theorem itemDeps_good {env : Binary.Env} (hE : EnvGood env) {it : Binary.WorldItem} (h : ItemGood it) :
    ∀ j ∈ itemDeps env it, IfaceName.validB j = true := by
  intro j hj
  cases it with
  | ifaceRef i _ _ =>
    simp only [itemDeps] at hj
    cases hb : Binary.Env.find? env i with
    | none => rw [hb] at hj; exact absurd hj List.not_mem_nil
    | some b =>
      rw [hb] at hj
      exact (hE _ (find?_mem hb)).2.2.2 j hj
  | ifaceInline n b => exact h.2.2.2 j hj
  | func _ => exact absurd hj List.not_mem_nil
  | type _ => exact absurd hj List.not_mem_nil

theorem itemDeps_rank {env : Binary.Env} {R : String → Nat} (hR : EnvRanked env R)
    {i : Binary.IfaceName} {d : Option String} {st : Binary.Stability} :
    ∀ j ∈ itemDeps env (.ifaceRef i d st), R j.id < R i.id := by
  intro j hj
  simp only [itemDeps] at hj
  cases hb : Binary.Env.find? env i with
  | none => rw [hb] at hj; exact absurd hj List.not_mem_nil
  | some b =>
    rw [hb] at hj
    exact hR _ (find?_mem hb) j hj

/-! ## Folds -/

theorem foldl_inv {α β : Type} {P : β → Prop} {f : β → α → β} :
    ∀ {l : List α} {b : β}, (∀ b a, a ∈ l → P b → P (f b a)) → P b → P (l.foldl f b)
  | [], _, _, hb => hb
  | a :: l, b, h, hb =>
    foldl_inv (l := l) (fun b' a' ha' => h b' a' (List.mem_cons_of_mem _ ha')) (h b a List.mem_cons_self hb)

theorem foldlM_except_inv {ε α β : Type} {P : β → Prop} {f : β → α → Except ε β} :
    ∀ {l : List α} {b r : β}, (∀ b a b', a ∈ l → P b → f b a = .ok b' → P b') → P b →
      l.foldlM f b = .ok r → P r
  | [], b, r, _, hb, hr => by
    simp only [List.foldlM_nil] at hr
    cases hr; exact hb
  | a :: l, b, r, h, hb, hr => by
    rw [List.foldlM_cons] at hr
    obtain ⟨b', hb', hr⟩ := except_bind_ok hr
    exact foldlM_except_inv (fun x y z hy => h x y z (List.mem_cons_of_mem _ hy))
      (h b a b' List.mem_cons_self hb hb') hr

theorem foldlM_option_inv {α β : Type} {P : β → Prop} {f : β → α → Option β} :
    ∀ {l : List α} {b r : β}, (∀ b a b', a ∈ l → P b → f b a = some b' → P b') → P b →
      l.foldlM f b = some r → P r
  | [], b, r, _, hb, hr => by
    simp only [List.foldlM_nil] at hr
    cases hr; exact hb
  | a :: l, b, r, h, hb, hr => by
    rw [List.foldlM_cons] at hr
    cases hb' : f b a with
    | none => rw [hb'] at hr; cases hr
    | some b' =>
      rw [hb'] at hr
      exact foldlM_option_inv (fun x y z hy => h x y z (List.mem_cons_of_mem _ hy))
        (h b a b' List.mem_cons_self hb hb') hr

/-! ## Insertions -/

theorem not_mem_keys_of_hasKey {its : List Binary.WorldItem} {k : String} (h : hasKey its k = false) :
    k ∉ its.map Binary.WorldItem.key := by
  intro hm
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
  have : hasKey its x.key = true := List.any_eq_true.mpr ⟨x, hx, by simp⟩
  rw [this] at h; cases h

theorem LInv.append {its : List Binary.WorldItem} {it : Binary.WorldItem} (h : LInv its) (hg : ItemGood it)
    (hk : hasKey its it.key = false) : LInv (its ++ [it]) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact h.1 x hx
    · rw [List.mem_singleton.mp hx]; exact hg
  · rw [List.map_append, List.nodup_append]
    exact ⟨h.2, by simp, fun a ha b hb => by
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      rintro rfl
      exact not_mem_keys_of_hasKey hk (hb ▸ ha)⟩

theorem insertIfNew_inv {its : List Binary.WorldItem} {it : Binary.WorldItem} (h : LInv its)
    (hg : ItemGood it) : LInv (insertIfNew its it) := by
  unfold insertIfNew
  cases hk : hasKey its it.key with
  | true => exact h
  | false => exact h.append hg hk

theorem insertNew_inv {its its' : List Binary.WorldItem} {it : Binary.WorldItem} (h : LInv its)
    (hg : ItemGood it) (hi : insertNew its it = .ok its') : LInv its' := by
  unfold insertNew at hi
  cases hk : hasKey its it.key with
  | true => rw [hk] at hi; cases hi
  | false =>
    rw [hk] at hi
    cases hi
    exact h.append hg hk

theorem insertNew_mem {its its' : List Binary.WorldItem} {it : Binary.WorldItem}
    (hi : insertNew its it = .ok its') : ∀ x ∈ its', x ∈ its ∨ x = it := by
  unfold insertNew at hi
  cases hk : hasKey its it.key with
  | true => rw [hk] at hi; cases hi
  | false =>
    rw [hk] at hi
    cases hi
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact .inl hx
    · exact .inr (List.mem_singleton.mp hx)

/-! ## Imports -/

theorem importIface_inv {env : Binary.Env} (hE : EnvGood env) (st : Binary.Stability) :
    ∀ (f : Nat) (it : Binary.WorldItem) (acc : List Binary.WorldItem), ItemGood it → LInv acc →
      LInv (importIface env st f it acc)
  | 0, _, acc, _, h => h
  | f + 1, it, acc, hg, h => by
    unfold importIface
    split
    · exact h
    · refine insertIfNew_inv (foldl_inv (fun b j hj hb => ?_) h) hg
      exact importIface_inv hE st f _ b (itemDeps_good hE hg j hj) hb

theorem elabImport_inv {env : Binary.Env} (hE : EnvGood env) {fuel : Nat} {acc acc' : List Binary.WorldItem}
    {it : Binary.WorldItem} (h : LInv acc) (hg : ItemGood it) (he : elabImport env fuel acc it = .ok acc') :
    LInv acc' := by
  cases it with
  | ifaceRef i d s =>
    simp only [elabImport] at he
    cases he
    exact importIface_inv hE _ _ _ _ hg h
  | ifaceInline n b =>
    simp only [elabImport] at he
    cases he
    exact importIface_inv hE _ _ _ _ hg h
  | func f =>
    simp only [elabImport] at he
    exact insertNew_inv h hg he
  | type t =>
    simp only [elabImport] at he
    refine insertNew_inv ?_ hg he
    cases hd : typeDep t with
    | none => exact h
    | some j => exact importIface_inv hE _ _ _ _ (hg.2 j hd) h

/-! ## Exports -/

/-- The state of export elaboration: good items with distinct keys, no types
among the exports. -/
def XInv (s : XState) : Prop :=
  LInv s.imports ∧ LInv s.exports ∧ ∀ x ∈ s.exports, x.isType = false

/-- An imported or exported interface. -/
def IsIface : Binary.WorldItem → Prop
  | .ifaceRef .. | .ifaceInline .. => True
  | _ => False

/-- `x` is an interface reference below `it`: of smaller rank when `it` is one. -/
def Lower (R : String → Nat) (it x : Binary.WorldItem) : Prop :=
  ∃ j d st, x = .ifaceRef j d st ∧ ∀ i d' st', it = .ifaceRef i d' st' → R j.id < R i.id

theorem Lower.trans {R : String → Nat} {it : Binary.WorldItem} {j : Binary.IfaceName} {d : Option String}
    {st : Binary.Stability} (hj : ∀ i d' st', it = .ifaceRef i d' st' → R j.id < R i.id) {x : Binary.WorldItem}
    (h : x = .ifaceRef j d st ∨ Lower R (.ifaceRef j d st) x) : Lower R it x := by
  rcases h with rfl | ⟨j', d', st', rfl, hlt⟩
  · exact ⟨j, d, st, rfl, hj⟩
  · exact ⟨j', d', st', rfl, fun i d'' st'' hi => Nat.lt_trans (hlt j d st rfl) (hj i d'' st'' hi)⟩

theorem key_ne_of_lower {R : String → Nat} {it x : Binary.WorldItem} (hi : IsIface it) (hg : ItemGood it)
    (h : Lower R it x) : x.key ≠ it.key := by
  obtain ⟨j, d, st, rfl, hlt⟩ := h
  cases it with
  | ifaceRef i d' st' =>
    intro he
    have := hlt i d' st' rfl
    simp only [Binary.WorldItem.key] at he
    rw [he] at this
    exact Nat.lt_irrefl _ this
  | ifaceInline n b =>
    intro he
    simp only [Binary.WorldItem.key] at he
    have hc : ':' ∈ n.toList := by
      rw [← he]; simpa [Binary.IfaceName.id] using Binary.colon_mem_id j
    exact not_mem_of_plain hg.1 plainChar_colon hc
  | func _ => exact hi.elim
  | type _ => exact hi.elim

theorem itemDeps_lower {env : Binary.Env} {R : String → Nat} (hR : EnvRanked env R) {it : Binary.WorldItem}
    {j : Binary.IfaceName} (hj : j ∈ itemDeps env it) : ∀ i d' st', it = .ifaceRef i d' st' → R j.id < R i.id := by
  rintro i d' st' rfl
  exact itemDeps_rank hR j hj

theorem addExport_inv {env : Binary.Env} {R : String → Nat} (hE : EnvGood env) (hR : EnvRanked env R)
    (xs : List String) : ∀ (f : Nat) (it : Binary.WorldItem) (add : Bool) (s s' : XState),
      addExport env xs f it add s = some s' → ItemGood it → IsIface it → XInv s →
        XInv s' ∧ ∀ x ∈ s'.exports, x ∈ s.exports ∨ x = it ∨ Lower R it x
  | 0, _, _, s, s', h, _, _, hs => by
    simp only [addExport, Option.some.injEq] at h
    subst h
    exact ⟨hs, fun x hx => .inl hx⟩
  | f + 1, it, add, s, s', h, hg, hi, hs => by
    unfold addExport at h
    by_cases hk : hasKey s.exports it.key = true
    · simp only [hk, ite_true] at h
      cases add with
      | true =>
        simp only [ite_true, Option.some.injEq] at h
        subst h
        exact ⟨hs, fun x hx => .inl hx⟩
      | false => simp at h
    · have hk' : hasKey s.exports it.key = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ite_false] at h
      by_cases hr : (!add && reqHas s.req it) = true
      · simp only [hr, ite_true, Option.some.injEq] at h
        subst h
        exact ⟨hs, fun x hx => .inl hx⟩
      · simp only [hr, Bool.false_eq_true, ite_false] at h
        cases hfold : (itemDeps env it).foldlM (fun s j =>
            addExport env xs f (.ifaceRef j none (itemStab it)) (add && xs.contains j.id) s) s with
        | none => rw [hfold] at h; cases h
        | some s1 =>
          rw [hfold] at h
          have hinv : XInv s1 ∧ ∀ x ∈ s1.exports, x ∈ s.exports ∨ Lower R it x := by
            refine foldlM_option_inv (P := fun t => XInv t ∧ ∀ x ∈ t.exports, x ∈ s.exports ∨ Lower R it x)
              (fun b j b' hj hb hstep => ?_) ⟨hs, fun x hx => .inl hx⟩ hfold
            have hgj : ItemGood (.ifaceRef j none (itemStab it)) := itemDeps_good hE hg j hj
            obtain ⟨hb', hnew⟩ := addExport_inv hE hR xs f _ _ b b' hstep hgj trivial hb.1
            refine ⟨hb', fun x hx => ?_⟩
            rcases hnew x hx with hx | hx | hx
            · exact hb.2 x hx
            · exact .inr (Lower.trans (itemDeps_lower hR hj) (.inl hx))
            · exact .inr (Lower.trans (itemDeps_lower hR hj) (.inr hx))
          obtain ⟨hs1, hnew⟩ := hinv
          cases add with
          | true =>
            simp only [ite_true] at h
            by_cases hq : reqHas s1.req it = true
            · simp [hq] at h
            · simp only [hq, Bool.false_eq_true, ite_false, Option.some.injEq] at h
              subst h
              have hk1 : hasKey s1.exports it.key = false := by
                cases hh : hasKey s1.exports it.key with
                | false => rfl
                | true =>
                  exfalso
                  obtain ⟨x, hx, hxk⟩ := List.any_eq_true.mp hh
                  have hxk' : x.key = it.key := by simpa using hxk
                  rcases hnew x hx with hx | hx
                  · exact not_mem_keys_of_hasKey hk' (hxk' ▸ List.mem_map_of_mem hx)
                  · exact key_ne_of_lower hi hg hx hxk'
              refine ⟨⟨hs1.1, hs1.2.1.append hg hk1, fun x hx => ?_⟩, fun x hx => ?_⟩
              · rcases List.mem_append.mp hx with hx | hx
                · exact hs1.2.2 x hx
                · rw [List.mem_singleton.mp hx]
                  cases it with
                  | ifaceRef _ _ _ => rfl
                  | ifaceInline _ _ => rfl
                  | func _ => exact hi.elim
                  | type _ => exact hi.elim
              · rcases List.mem_append.mp hx with hx | hx
                · rcases hnew x hx with hx | hx
                  · exact .inl hx
                  · exact .inr (.inr hx)
                · exact .inr (.inl (List.mem_singleton.mp hx))
          | false =>
            simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at h
            subst h
            refine ⟨⟨insertIfNew_inv hs1.1 hg, hs1.2.1, hs1.2.2⟩, fun x hx => ?_⟩
            rcases hnew x hx with hx | hx
            · exact .inl hx
            · exact .inr (.inr hx)

/-! ## `elaborate_world` -/

theorem mem_sortImports {its : List Binary.WorldItem} {x : Binary.WorldItem} (h : x ∈ sortImports its) :
    x ∈ its := by
  obtain ⟨_, _, hx⟩ := List.mem_flatMap.mp h
  exact (List.mem_filter.mp hx).1

theorem sortImports_inv {its : List Binary.WorldItem} (h : LInv its) : LInv (sortImports its) := by
  refine ⟨fun x hx => h.1 x (mem_sortImports hx), ?_⟩
  unfold sortImports
  rw [List.map_flatMap]
  refine List.nodup_flatMap.mpr ⟨fun k _ => ?_, ?_⟩
  · exact List.Nodup.sublist ((List.filter_sublist).map _) h.2
  · refine List.Pairwise.imp_of_mem ?_ List.nodup_range
    intro a b _ _ hab x hxa hxb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxa
    obtain ⟨z, hz, hzy⟩ := List.mem_map.mp hxb
    have hy' := List.mem_filter.mp hy
    have hz' := List.mem_filter.mp hz
    have hyz : z = y := List.inj_on_of_nodup_map h.2 hz'.1 hy'.1 hzy
    have ha : importClass y = a := by simpa using hy'.2
    have hb : importClass z = b := by simpa using hz'.2
    exact hab (by rw [← ha, ← hb, hyz])

/-- **`elaborate_world` keeps items good and keys distinct.** -/
theorem elabWorldItems_good {env : Binary.Env} {R : String → Nat} (hE : EnvGood env) (hR : EnvRanked env R)
    {imports exports imps exps : List Binary.WorldItem} (hi : ∀ x ∈ imports, ItemGood x)
    (hx : ∀ x ∈ exports, ItemGood x) (h : elabWorldItems env imports exports = .ok (imps, exps)) :
    LInv imps ∧ LInv exps ∧ ∀ x ∈ exps, x.isType = false := by
  unfold elabWorldItems at h
  obtain ⟨imps0, himps, h⟩ := except_bind_ok h
  obtain ⟨funcs, hfuncs, h⟩ := except_bind_ok h
  have hI : LInv imps0 :=
    foldlM_except_inv (fun b a b' ha hb hstep => elabImport_inv hE hb (hi a (mem_sortImports ha)) hstep)
      ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩ himps
  have hF : LInv funcs ∧ ∀ x ∈ funcs, x.isType = false :=
    foldlM_except_inv (P := fun t => LInv t ∧ ∀ x ∈ t, x.isType = false)
      (fun b a b' ha hb hstep => by
        have hfa := List.mem_filter.mp ha
        refine ⟨insertNew_inv hb.1 (hx a hfa.1) hstep, fun y hy => ?_⟩
        rcases insertNew_mem hstep y hy with hy | rfl
        · exact hb.2 y hy
        · cases y with
          | func _ => rfl
          | _ => simp at hfa)
      ⟨⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil⟩, fun _ h => absurd h List.not_mem_nil⟩ hfuncs
  dsimp only at h
  split at h
  · rename_i s hs
    have hS : XInv s := by
      refine foldlM_option_inv (fun b a b' ha hb hstep => ?_) ⟨hI, hF.1, hF.2⟩ hs
      have hfa := List.mem_filter.mp ha
      have hia : IsIface a := by
        cases a with
        | ifaceRef _ _ _ => trivial
        | ifaceInline _ _ => trivial
        | _ => simp at hfa
      exact (addExport_inv hE hR _ _ a true b b' hstep (hx a hfa.1) hia hb).1
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨sortImports_inv hS.1, hS.2.1, hS.2.2⟩
    · cases h
  · cases h

/-- A world whose imports and exports come out of `elabWorldItems` passes the
binary checks. -/
theorem world_namesUniqueB {w : Binary.World} (hi : LInv w.imports) (he : LInv w.exports)
    (ht : ∀ x ∈ w.exports, x.isType = false) : World.namesUniqueB w = true := by
  simp only [World.namesUniqueB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨hi.2, he.2⟩, ht⟩, fun x hx => ?_⟩
  have hg : ItemGood x := (List.mem_append.mp hx).elim (hi.1 x) (he.1 x)
  cases x with
  | ifaceInline _ b => exact hg.2.2.1
  | type td => exact hg.1
  | ifaceRef _ _ _ => rfl
  | func _ => rfl

end Silmaril.Wasm.Wit.Elab
