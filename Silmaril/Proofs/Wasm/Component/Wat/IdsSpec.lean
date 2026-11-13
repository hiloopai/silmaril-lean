module

public import Silmaril.Wasm.Component.Wat.IdsSpec.Defs
public import Silmaril.Wasm.Component.Wat.Thms

/-!
# Component WAT identifiers: proofs of the index specification

* `count_addAll`, `lookup_addAll_iff`: a scope built by allocations counts and names
  as `countIn` and `NamesIdx` say;
* `rItemsAt_list`: `rItemsAt` reads an item in the current scope and the rest in the
  scope extended by the item's allocations;
* `rItemsAt_scope`: item `k` of a scope is resolved in the scope of the allocations of
  the items before it;
* `rAtom_lookup_iff`: so an identifier reference `$x` of space `sp` there resolves to
  `i` exactly when `NamesIdx` (for a scope that starts without names).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

theorem count_add (s : Scope) (sp' : Space) (b : Option String) (sp : Space) :
    (s.add sp' b).count sp = if sp' = sp then s.count sp + 1 else s.count sp := by
  unfold Scope.count Scope.add
  by_cases h : sp' = sp
  · subst h
    simp [Scope.count]
  · have hf : (s.counts.filter fun e => e.1 ≠ sp').find? (fun e => e.1 = sp) =
        s.counts.find? (fun e => e.1 = sp) := by
      rw [List.find?_filter]
      congr 1
      funext e
      by_cases he : e.1 = sp <;> simp [he, Ne.symm h]
    rw [List.find?_cons_of_neg (by simpa using h), hf]
    simp [h]

theorem lookup_add (s : Scope) (sp' : Space) (b : Option String) (sp : Space) (x : String) :
    (s.add sp' b).lookup sp x =
      if sp' = sp ∧ b = some x then some (s.count sp') else s.lookup sp x := by
  unfold Scope.lookup Scope.add
  cases b with
  | none => simp
  | some y =>
    by_cases h : sp' = sp ∧ y = x
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp [h]

theorem addAll_append (s : Scope) (L M : List Alloc) :
    s.addAll (L ++ M) = (s.addAll L).addAll M := by
  simp [Scope.addAll, List.foldl_append]

theorem addAll_snoc (s : Scope) (L : List Alloc) (e : Alloc) :
    s.addAll (L ++ [e]) = (s.addAll L).add e.1 e.2 := by
  simp [Scope.addAll, List.foldl_append]

theorem isType_add (s : Scope) (sp : Space) (b : Option String) : (s.add sp b).isType = s.isType :=
  rfl

theorem isType_addAll (s : Scope) : ∀ L : List Alloc, (s.addAll L).isType = s.isType := by
  intro L
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L e ih => rw [addAll_snoc, isType_add, ih]

theorem countIn_snoc (L : List Alloc) (e : Alloc) (sp : Space) :
    countIn (L ++ [e]) sp = if e.1 = sp then countIn L sp + 1 else countIn L sp := by
  unfold countIn
  by_cases h : e.1 = sp <;> simp [h, List.filter_append]

/-- **Counting**: a scope counts the allocations of each space. -/
theorem count_addAll (s : Scope) (sp : Space) :
    ∀ L : List Alloc, (s.addAll L).count sp = s.count sp + countIn L sp := by
  intro L
  induction L using List.reverseRecOn with
  | nil => simp [Scope.addAll, countIn]
  | append_singleton L e ih =>
    rw [addAll_snoc, count_add, countIn_snoc, ih]
    by_cases h : e.1 = sp <;> simp [h, Nat.add_assoc]

/-- The decompositions of `L ++ [e]` around a binder `p` with no later `p`. -/
theorem split_snoc_iff {L L1 L2 : List Alloc} {e p : Alloc} (hp : p ∉ L2)
    (h : L ++ [e] = L1 ++ p :: L2) : (L2 = [] ∧ L = L1 ∧ e = p) ∨
      ∃ L2', L2 = L2' ++ [e] ∧ L = L1 ++ p :: L2' ∧ p ∉ L2' ∧ e ≠ p := by
  rcases List.eq_nil_or_concat' L2 with rfl | ⟨L2', z, rfl⟩
  · have h' : L = L1 ∧ [e] = [p] := List.append_inj' h rfl
    exact .inl ⟨rfl, h'.1, List.singleton_inj.mp h'.2⟩
  · have h2 : L ++ [e] = (L1 ++ p :: L2') ++ [z] := by simpa using h
    have h' : L = L1 ++ p :: L2' ∧ [e] = [z] := List.append_inj' h2 rfl
    have hz : e = z := List.singleton_inj.mp h'.2
    subst hz
    have hne : e ≠ p := fun he => hp (by simp [he])
    exact .inr ⟨L2', rfl, h'.1, fun hm => hp (by simp [hm]), hne⟩

theorem namesIdx_snoc_self (s : Scope) (L : List Alloc) (sp : Space) (x : String) (i : Nat) :
    (∃ L1 L2, L ++ [(sp, some x)] = L1 ++ (sp, some x) :: L2 ∧
        i = s.count sp + countIn L1 sp ∧ (sp, some x) ∉ L2) ↔
      i = s.count sp + countIn L sp := by
  constructor
  · rintro ⟨L1, L2, h, hi, hp⟩
    rcases split_snoc_iff hp h with ⟨-, hL, -⟩ | ⟨-, -, -, -, hne⟩
    · rw [hi, hL]
    · exact absurd rfl hne
  · intro hi
    exact ⟨L, [], rfl, hi, by simp⟩

theorem namesIdx_snoc_other (s : Scope) (L : List Alloc) (e : Alloc) (sp : Space) (x : String)
    (i : Nat) (he : e ≠ (sp, some x)) :
    (∃ L1 L2, L ++ [e] = L1 ++ (sp, some x) :: L2 ∧
        i = s.count sp + countIn L1 sp ∧ (sp, some x) ∉ L2) ↔
      (∃ L1 L2, L = L1 ++ (sp, some x) :: L2 ∧
        i = s.count sp + countIn L1 sp ∧ (sp, some x) ∉ L2) := by
  constructor
  · rintro ⟨L1, L2, h, hi, hp⟩
    rcases split_snoc_iff hp h with ⟨-, -, he'⟩ | ⟨L2', -, hL, hp', -⟩
    · exact absurd he' he
    · exact ⟨L1, L2', hL, hi, hp'⟩
  · rintro ⟨L1, L2, h, hi, hp⟩
    refine ⟨L1, L2 ++ [e], by simp [h], hi, ?_⟩
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hp, Ne.symm he⟩

/-- **Naming**: in a scope that starts without names, after the allocations `L`, `x`
names index `i` of `sp` exactly when the last binder of `x` in `sp` has `i`
allocations of `sp` before it (counting from the scope's own count). -/
theorem lookup_addAll_iff (s : Scope) (hs : s.names = []) (sp : Space) (x : String) (i : Nat) :
    ∀ L : List Alloc, (s.addAll L).lookup sp x = some i ↔
      ∃ L1 L2, L = L1 ++ (sp, some x) :: L2 ∧ i = s.count sp + countIn L1 sp ∧
        (sp, some x) ∉ L2 := by
  intro L
  induction L using List.reverseRecOn with
  | nil => simp [Scope.addAll, Scope.lookup, hs]
  | append_singleton L e ih =>
    rw [addAll_snoc, lookup_add]
    by_cases h : e.1 = sp ∧ e.2 = some x
    · have he : e = (sp, some x) := Prod.ext h.1 h.2
      subst he
      rw [namesIdx_snoc_self, count_addAll]
      simp [eq_comm]
    · have he : e ≠ (sp, some x) := fun he => h (by simp [he])
      rw [ite_eq_right h, ih, namesIdx_snoc_other s L e sp x i he]

/-- The fresh scope of `resolve`: `NamesIdx` exactly. -/
theorem lookup_fresh_iff (lbl : Option String) (ty : Bool) (L : List Alloc) (sp : Space)
    (x : String) (i : Nat) :
    (({ label := lbl, isType := ty } : Scope).addAll L).lookup sp x = some i ↔ NamesIdx L sp x i := by
  rw [lookup_addAll_iff _ rfl]
  simp [NamesIdx, Scope.count]

/-! ## `resolve` follows the allocations -/

theorem foldl_range_add (s : Scope) (k : Nat) :
    (List.range k).foldl (fun s _ => s.add .value none) s =
      s.addAll (List.replicate k (.value, none)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih, List.replicate_succ', addAll_snoc]
    rfl

theorem addAll_itemAllocs (s : Scope) (xs : List Sexp) :
    s.addAll (itemAllocs s.isType (.list xs)) =
      (List.range (startValues xs)).foldl (fun s _ => s.add .value none)
        (match (defOf s.isType xs).1 with
          | some sp => s.add sp (defOf s.isType xs).2.2
          | none => s) := by
  rw [foldl_range_add]
  unfold itemAllocs
  rw [addAll_append]
  cases (defOf s.isType xs).1 <;> rfl

/-- `rItemsAt` reads an item in the current scope, the rest in the scope extended by
the item's allocations. -/
theorem rItemsAt_list (n : Nat) (s : Scope) (outer : List Scope) (xs : List Sexp)
    (r : List Sexp) :
    rItemsAt (n + 1) (s :: outer) (.list xs :: r) =
      (rItem n (s :: outer) (defOf s.isType xs).2.2 (defOf s.isType xs).2.1).bind fun it' =>
        (rItemsAt n (s.addAll (itemAllocs s.isType (.list xs)) :: outer) r).map (it' :: ·) := by
  rw [addAll_itemAllocs]
  simp only [rItemsAt]
  cases rItem n (s :: outer) (defOf s.isType xs).2.2 (defOf s.isType xs).2.1 with
  | none => rfl
  | some it' =>
    simp only [Option.bind_some]
    cases rItemsAt n _ r <;> rfl

theorem rItemsAt_other (n : Nat) (s : Scope) (outer : List Scope) (y : Sexp) (r : List Sexp)
    (hy : ∀ xs, y ≠ .list xs) :
    rItemsAt (n + 1) (s :: outer) (y :: r) =
      (rRefs (s :: outer) false .type y).bind fun y' =>
        (rItemsAt n (s :: outer) r).map (y' :: ·) := by
  cases y with
  | list xs => exact absurd rfl (hy xs)
  | _ =>
    simp only [rItemsAt]
    cases rRefs (s :: outer) false .type _ with
    | none => rfl
    | some y' => simp only [Option.bind_some]; cases rItemsAt n (s :: outer) r <;> rfl

theorem rItemsAt_some_succ {n : Nat} {sc : List Scope} {items : List Sexp}
    {out : List Sexp} (h : rItemsAt n sc items = some out) : ∃ m, n = m + 1 := by
  cases n with
  | zero => simp [rItemsAt] at h
  | succ m => exact ⟨m, rfl⟩

/-- **The scope of item `k`**: when `rItemsAt` resolves the items of a scope `s`, item
`k` (a list `(xs)`) is resolved by `rItem` in the scope of the allocations of the
items before it, and its result is element `k` of the output. -/
theorem rItemsAt_scope : ∀ (items : List Sexp) (n : Nat) (s : Scope) (outer : List Scope)
    (out : List Sexp) (k : Nat) (xs : List Sexp),
    rItemsAt n (s :: outer) items = some out → items[k]? = some (.list xs) →
      ∃ m it, rItem m ((s.addAll (allocsOf s.isType (items.take k))) :: outer)
        (defOf s.isType xs).2.2 (defOf s.isType xs).2.1 = some it ∧ out[k]? = some it
  | [], _, _, _, _, _, _, _, hk => by simp at hk
  | y :: r, n, s, outer, out, k, xs, h, hk => by
    obtain ⟨n', rfl⟩ := rItemsAt_some_succ h
    rcases em (∃ ys, y = .list ys) with ⟨ys, rfl⟩ | hy
    · have h1 : ((rItem n' (s :: outer) (defOf s.isType ys).2.2 (defOf s.isType ys).2.1).bind
          fun it' => (rItemsAt n' (s.addAll (itemAllocs s.isType (.list ys)) :: outer) r).map
            (it' :: ·)) = some out := by rw [← rItemsAt_list]; exact h
      obtain ⟨it0, hit0, h2⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨out', hout', rfl⟩ := Option.map_eq_some_iff.mp h2
      cases k with
      | zero =>
        have hxs : ys = xs := by simpa using hk
        subst hxs
        exact ⟨n', it0, by simpa [allocsOf, Scope.addAll] using hit0, rfl⟩
      | succ k =>
        have hk' : r[k]? = some (.list xs) := by simpa using hk
        obtain ⟨m, it, hm, hit⟩ := rItemsAt_scope r n' _ outer out' k xs hout' hk'
        have hty : (s.addAll (itemAllocs s.isType (.list ys))).isType = s.isType :=
          isType_addAll s _
        rw [hty, ← addAll_append] at hm
        exact ⟨m, it, by simpa [allocsOf, List.take_succ_cons] using hm, by simpa using hit⟩
    · have hy' : ∀ ys, y ≠ .list ys := fun ys he => hy ⟨ys, he⟩
      have h1 : ((rRefs (s :: outer) false .type y).bind fun y' =>
          (rItemsAt n' (s :: outer) r).map (y' :: ·)) = some out := by
        rw [← rItemsAt_other n' s outer y r hy']; exact h
      obtain ⟨y', -, h2⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨out', hout', rfl⟩ := Option.map_eq_some_iff.mp h2
      cases k with
      | zero => simp at hk; exact absurd hk (hy' xs)
      | succ k =>
        have hk' : r[k]? = some (.list xs) := by simpa using hk
        obtain ⟨m, it, hm, hit⟩ := rItemsAt_scope r n' s outer out' k xs hout' hk'
        have hal : allocsOf s.isType ((y :: r).take (k + 1)) = allocsOf s.isType (r.take k) := by
          cases y with
          | list ys => exact absurd rfl (hy' ys)
          | _ => simp [allocsOf, itemAllocs]
        exact ⟨m, it, by rw [hal]; exact hm, by simpa using hit⟩

/-- An identifier reference is looked up in the innermost scope. -/
theorem rAtom_id (s : Scope) (outer : List Scope) (sp : Space) (a : String) (h : isId a = true) :
    rAtom (s :: outer) sp a = (s.lookup sp a).map num := by
  simp [rAtom, h]

/-- **The right index**: in the scope of item `k` of a component (or type) scope that
started without names, `$x` of space `sp` resolves to the numeral `i` exactly when
`NamesIdx` holds for the allocations of the items before `k`. -/
theorem rAtom_scope_iff (lbl : Option String) (ty : Bool) (before : List Sexp) (outer : List Scope)
    (sp : Space) (x : String) (hx : isId x = true) (i : Nat) :
    rAtom ((({ label := lbl, isType := ty } : Scope).addAll (allocsOf ty before)) :: outer) sp x =
        some (num i) ↔ NamesIdx (allocsOf ty before) sp x i := by
  rw [rAtom_id _ _ _ _ hx, ← lookup_fresh_iff lbl ty]
  constructor
  · intro h
    obtain ⟨j, hj, hji⟩ := Option.map_eq_some_iff.mp h
    have hnum : j = i := by
      have := congrArg num? hji
      simpa [num?_num] using this
    rw [← hnum]; exact hj
  · intro h
    rw [h]; rfl

end Silmaril.Wasm.Component.Wat
