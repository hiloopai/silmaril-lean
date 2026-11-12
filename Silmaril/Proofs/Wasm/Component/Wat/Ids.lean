module

public import Silmaril.Wasm.Component.Wat.Ids.Defs

/-!
# Component WAT: identifier resolution is conservative

`resolve` is the identity on S-expressions without identifiers (`resolve_noIds`), so
`readIds` agrees with `read` on text without `$` atoms (`readIds_of_noIds`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

theorem rAtom_of_not {sc : List Scope} {sp : Space} {a : String} (h : isId a = false) :
    rAtom sc sp a = some (.atom a) := by simp [rAtom, h]

theorem rRefs_noIds (sc : List Scope) (core : Bool) (sp : Space) (s : Sexp) :
    noIds s = true → rRefs sc core sp s = some s := by
  apply rRefs.induct sc (fun core sp s => noIds s = true → rRefs sc core sp s = some s)
    (fun core sp r => noIdsL r = true → rRefsL sc core sp r = some r)
  all_goals intros
  all_goals (try simp_all [rRefs, rRefsL, noIds, noIdsL, rAtom])

theorem stripId_noIds {r : List Sexp} (h : noIdsL r = true) : stripId r = (r, none) := by
  cases r with
  | nil => rfl
  | cons x r =>
    cases x with
    | atom a =>
      simp only [noIdsL, noIds, Bool.and_eq_true, Bool.not_eq_true'] at h
      simp [stripId, h.1]
    | _ => rfl

theorem stripSortId_noIds {s : Sexp} (h : noIds s = true) : stripSortId s = (s, none) := by
  unfold stripSortId
  split
  · simp only [noIds, noIdsL, Bool.and_eq_true] at h
    simp [stripId_noIds h.2.2]
  · simp only [noIds, noIdsL, Bool.and_eq_true] at h
    simp [stripId_noIds h.2]
  · rfl

theorem stripLast_noIds : ∀ {r : List Sexp}, noIdsL r = true → stripLast r = (r, none)
  | [], _ => rfl
  | [s], h => by
    simp only [noIdsL, Bool.and_eq_true] at h
    simp [stripLast, stripSortId_noIds h.1]
  | s :: t :: r, h => by
    simp only [noIdsL, Bool.and_eq_true] at h
    have := stripLast_noIds (r := t :: r) (by simp [noIdsL, h.2.1, h.2.2])
    simp only [stripLast, this]

theorem defOf_noIds (b : Bool) {xs : List Sexp} (h : noIdsL xs = true) :
    (defOf b xs).2.1 = xs := by
  unfold defOf
  split
  · simp only [noIdsL, Bool.and_eq_true] at h
    split <;> simp [stripLast_noIds h.2, stripId_noIds h.2]
  · rfl
  · simp only [noIdsL, Bool.and_eq_true] at h
    simp [stripId_noIds h.2.2]
  · simp only [noIdsL, Bool.and_eq_true] at h
    simp [stripLast_noIds h.2]
  · simp only [noIdsL, Bool.and_eq_true] at h
    simp [stripLast_noIds h.2]
  · simp only [noIdsL, Bool.and_eq_true] at h
    split <;> simp [stripId_noIds h.2]
  · rfl

/-- `rItemsAt` is the identity at fuel `n` (the induction hypothesis of `rItems_noIds`). -/
abbrev ItemsId (n : Nat) : Prop :=
  ∀ sc items, sc ≠ [] → noIdsL items = true → 2 * Sexp.nodesL items + 1 ≤ n →
    rItemsAt n sc items = some items

/-- `rItem` is the identity at fuel `n`. -/
abbrev ItemId (n : Nat) : Prop :=
  ∀ sc b xs, sc ≠ [] → noIdsL xs = true → 2 * Sexp.nodesL xs + 1 ≤ n →
    rItem n sc b xs = some (.list xs)

theorem rItem_noIds_succ (n : Nat) (ih2 : ItemsId n) : ItemId (n + 1) := by
  intro sc b xs hsc hx hn
  unfold rItem
  split
  all_goals (try (simp only [Nat.succ.injEq] at *))
  all_goals subst_vars
  · simp at *
  · simp only [noIdsL, Bool.and_eq_true] at hx
    simp only [stripId_noIds hx.2]
    rw [ih2 _ _ (by simp) hx.2 (by simp [Sexp.nodesL, Sexp.nodes] at hn; omega)]
    rfl
  · simp only [noIdsL, noIds, Bool.and_eq_true] at hx
    rw [ih2 _ _ (by simp) hx.2.1.2 (by simp [Sexp.nodesL, Sexp.nodes] at hn; omega)]
    rfl
  · simp only [noIdsL, noIds, Bool.and_eq_true] at hx
    rw [ih2 _ _ (by simp) hx.2.1.2 (by simp [Sexp.nodesL, Sexp.nodes] at hn; omega)]
    rfl
  · exact rRefs_noIds _ _ _ _ (by simpa [noIds] using hx)

theorem rItemsAt_noIds_cons (n : Nat) (ih1 : ItemId n) (ih2 : ItemsId n) (s : Scope)
    (outer : List Scope) (x : Sexp) (r : List Sexp) (hx : noIds x = true ∧ noIdsL r = true)
    (hn : 2 * Sexp.nodesL (x :: r) + 1 ≤ n + 1) :
    rItemsAt (n + 1) (s :: outer) (x :: r) = some (x :: r) := by
  have hpos : 0 < x.nodes := by cases x <;> simp [Sexp.nodes]; omega
  have hr : 2 * Sexp.nodesL r + 1 ≤ n := by simp [Sexp.nodesL] at hn; omega
  cases x with
  | list xs =>
    simp only [rItemsAt]
    have hxs : noIdsL xs = true := by simpa [noIds] using hx.1
    rw [defOf_noIds _ hxs, ih1 _ _ _ (by simp) hxs (by simp [Sexp.nodesL, Sexp.nodes] at hn; omega)]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [ih2 _ _ (by simp) hx.2 hr]
    rfl
  | atom a =>
    simp only [rItemsAt]
    rw [rRefs_noIds _ _ _ _ hx.1, ih2 _ _ (by simp) hx.2 hr]
    rfl
  | str b =>
    simp only [rItemsAt]
    rw [rRefs_noIds _ _ _ _ hx.1, ih2 _ _ (by simp) hx.2 hr]
    rfl

theorem rItemsAt_noIds_succ (n : Nat) (ih1 : ItemId n) (ih2 : ItemsId n) : ItemsId (n + 1) := by
  intro sc items hsc hx hn
  cases items with
  | nil => simp [rItemsAt]
  | cons x r =>
    obtain ⟨s, outer, rfl⟩ : ∃ s outer, sc = s :: outer := by
      cases sc with
      | nil => exact absurd rfl hsc
      | cons s outer => exact ⟨s, outer, rfl⟩
    exact rItemsAt_noIds_cons n ih1 ih2 s outer x r (by simpa [noIdsL] using hx) hn

theorem rItems_noIds : ∀ n, ItemId n ∧ ItemsId n := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => by omega, fun _ _ _ _ h => by omega⟩
  | succ n ih => exact ⟨rItem_noIds_succ n ih.2, rItemsAt_noIds_succ n ih.1 ih.2⟩

theorem resolve_noIds {s : Sexp} (h : noIds s = true) (hc : ∃ r, s = .list (.atom "component" :: r)) :
    resolve s = some s := by
  obtain ⟨r, rfl⟩ := hc
  simp only [noIds, noIdsL, Bool.and_eq_true] at h
  simp only [resolve, stripId_noIds h.2]
  rw [(rItems_noIds _).2 _ _ (by simp) h.2 (by omega)]
  rfl

/-- On text without identifiers, `readIds` is `read`. -/
theorem readIds_of_noIds {s : String} (h : ∀ x, Sexp.read s = some [x] → noIds x = true) :
    readIds s = read s := by
  unfold readIds read
  rcases hr : Sexp.read s with _ | l
  · rfl
  · rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
    · rfl
    · have hn := h x hr
      simp only
      by_cases hc : ∃ r, x = .list (.atom "component" :: r)
      · rw [resolve_noIds hn hc]; rfl
      · have h1 : resolve x = none := by
          unfold resolve; split
          · exact absurd ⟨_, rfl⟩ hc
          · rfl
        have h2 : ofSexp x = none := by
          unfold ofSexp; split
          · exact absurd ⟨_, rfl⟩ hc
          · rfl
        rw [h1, h2]; rfl
    · rfl

end Silmaril.Wasm.Component.Wat
