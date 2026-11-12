module

public import Silmaril.Wasm.Wac.Implicit.Defs
public import Silmaril.Wasm.Wac.Types.Thms
public import Silmaril.Wasm.Wac.Names.Thms

/-!
# WAC implicit imports: every argument explicit, and well typed

* `resolve_complete`: after `Implicit.resolve`, every instantiation passes every
  import of its package as a named argument (the IR has fully explicit arguments).
* `aggregate_iff`: `aggregate` decides the relation `Aggregate` (sound, and complete
  from merged imports on distinct tracks, in particular from `[]`); `resolve_iff`:
  `resolve` decides `Resolve`.
* `aggregate_tracks`: the merged imports are pairwise semver-incompatible (one per
  track, so names are distinct), and none is compatible with an explicit import.
* `aggregate_lower`: the merged implicit import compatible with a name is a subtype of
  every import of that name, or of a semver-compatible name, that some instantiation
  left unsatisfied, provided the kinds are WIT-shaped (`Kind.wit`); `merge_not_lower`
  (`Silmaril.Wasm.Wac.Types.Thms`) shows the proviso is needed.
* `resolve_typed`: hence, when every explicit argument was checked (and refers to an
  existing node) and the imports are WIT-shaped, every argument of the resolved graph,
  explicit or implicit, is well typed.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

namespace Implicit

/-! ## Completeness -/

theorem extend_op_inst {base : Nat} {ms : Externs} {nd : CNode} {p : String} {imps : Externs}
    {args : List (String × Nat)} (h : (extend base ms nd).op = .inst p imps args) :
    ∃ args0, nd.op = .inst p imps args0 ∧
      args = args0 ++ (unsatisfied imps args0).map fun q => (q.1, nodeOf base ms q.1) := by
  unfold extend at h
  split at h
  · rename_i p0 imps0 args0 hop
    simp only [COp.inst.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨args0, hop, rfl⟩
  · rename_i hne; exact absurd h (hne p imps args)

theorem mem_unsatisfied {imps : Externs} {args : List (String × Nat)} {q : String × Kind}
    (hq : q ∈ imps) (hn : ¬ ∃ j, (q.1, j) ∈ args) : q ∈ unsatisfied imps args := by
  refine List.mem_filter.2 ⟨hq, ?_⟩
  simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
  exact fun a ha he => hn ⟨a.2, he ▸ ha⟩

/-- **After resolution every instantiation passes every import explicitly.** -/
theorem resolve_complete {g g' : CGraph} (h : resolve g = .ok g') : g'.Complete := by
  simp only [resolve, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i ms _
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro nd hnd p imps args hop q hq
    rcases List.mem_append.1 hnd with h1 | h1
    · obtain ⟨nd0, _, rfl⟩ := List.mem_map.1 h1
      obtain ⟨args0, _, rfl⟩ := extend_op_inst hop
      by_cases he : ∃ j, (q.1, j) ∈ args0
      · obtain ⟨j, hj⟩ := he
        exact ⟨j, List.mem_append_left _ hj⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨q, mem_unsatisfied hq he, rfl⟩)⟩
    · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h1
      cases hop

/-! ## Lookups -/

theorem ite_yes {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_no {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem lookup_cons (m x : String) (v : Kind) (es : Externs) :
    Externs.find ((x, v) :: es) m = if m = x then some v else Externs.find es m := by
  by_cases h : m = x
  · subst h; simp [Externs.find, List.lookup]
  · simp [Externs.find, List.lookup, beq_false_of_ne h, h]

theorem find_append_none {es : Externs} {n : String} {k : Kind} (h : es.find n = none) (m : String) :
    (es ++ [(n, k)]).find m = if m = n then some k else es.find m := by
  induction es with
  | nil => show Externs.find [(n, k)] m = _; rw [lookup_cons]
  | cons p es ih =>
    obtain ⟨x, v⟩ := p
    have hx : n ≠ x := fun e => by rw [lookup_cons, ite_yes e] at h; cases h
    have h' : Externs.find es n = none := by rw [lookup_cons, ite_no hx] at h; exact h
    have e1 : Externs.find ((x, v) :: es ++ [(n, k)]) m =
        if m = x then some v else Externs.find (es ++ [(n, k)]) m := lookup_cons m x v _
    rw [e1, ih h', lookup_cons]
    by_cases hm : m = x
    · subst hm; simp [Ne.symm hx]
    · simp [hm]

theorem find_replace_ne {es : Externs} {n m : String} {k : Kind} (hm : m ≠ n) :
    (es.replace n k).find m = es.find m := by
  induction es with
  | nil => rfl
  | cons p es ih =>
    obtain ⟨x, v⟩ := p
    have e : Externs.replace ((x, v) :: es) n k =
        (if x = n then (n, k) else (x, v)) :: Externs.replace es n k := rfl
    rw [e, lookup_cons m x v es]
    by_cases hx : x = n
    · subst hx; rw [ite_yes rfl, lookup_cons, ite_no hm, ite_no hm, ih]
    · rw [ite_no hx, lookup_cons, ih]

theorem find_replace_self {es : Externs} {n : String} {k : Kind} (h : (es.find n).isSome) :
    (es.replace n k).find n = some k := by
  induction es with
  | nil => simp [Externs.find] at h
  | cons p es ih =>
    obtain ⟨x, v⟩ := p
    have e : Externs.replace ((x, v) :: es) n k =
        (if x = n then (n, k) else (x, v)) :: Externs.replace es n k := rfl
    rw [e]
    by_cases hx : x = n
    · subst hx; rw [ite_yes rfl, lookup_cons, ite_yes rfl]
    · have hn : n ≠ x := Ne.symm hx
      rw [lookup_cons, ite_no hn] at h
      rw [ite_no hx, lookup_cons, ite_no hn, ih h]

/-! ## Semver tracks of the merged imports -/

/-- The merged imports are pairwise semver-incompatible: one per track, distinct names. -/
def Tracks (ms : Externs) : Prop := ms.Pairwise fun a b => compat a.1 b.1 = false

theorem tracks_eq {ms : Externs} (h : Tracks ms) {a b : String × Kind} (ha : a ∈ ms) (hb : b ∈ ms)
    (hab : compat a.1 b.1 = true) : a = b := by
  induction ms with
  | nil => cases ha
  | cons x t ih =>
    have h' := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with e1 | ha' <;> rcases List.mem_cons.1 hb with e2 | hb'
    · rw [e1, e2]
    · rw [e1, h'.1 b hb'] at hab; cases hab
    · rw [e2, compat_comm, h'.1 a ha'] at hab; cases hab
    · exact ih h'.2 ha' hb'

theorem findCompat_mem {ms : Externs} {n : String} {q : String × Kind} (h : findCompat ms n = some q) :
    q ∈ ms ∧ compat q.1 n = true := by
  unfold findCompat at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem findCompat_none {ms : Externs} {n : String} (h : findCompat ms n = none) :
    ∀ q ∈ ms, compat q.1 n = false := fun q hq => by
  simpa using List.find?_eq_none.1 h q hq

theorem findCompat_of_none {ms : Externs} {n : String} (h : ∀ q ∈ ms, compat q.1 n = false) :
    findCompat ms n = none :=
  List.find?_eq_none.2 fun q hq => by simp [h q hq]

theorem findCompat_of_mem {ms : Externs} (ht : Tracks ms) {q : String × Kind} {n : String} (hq : q ∈ ms)
    (hc : compat q.1 n = true) : findCompat ms n = some q := by
  cases hf : findCompat ms n with
  | none => rw [findCompat_none hf q hq] at hc; cases hc
  | some r =>
    obtain ⟨hr, hrc⟩ := findCompat_mem hf
    rw [tracks_eq ht hr hq (compat_trans hrc (by rw [compat_comm]; exact hc))]

theorem findCompat_append_old {ms : Externs} {x : String} {q : String × Kind} (h : findCompat ms x = some q)
    (es : Externs) : findCompat (ms ++ es) x = some q := by
  simp only [findCompat, List.find?_append] at *
  rw [h]; rfl

theorem findCompat_append_new {ms : Externs} {x : String} (h : findCompat ms x = none) (n : String) (k : Kind)
    (hc : compat n x = true) : findCompat (ms ++ [(n, k)]) x = some (n, k) := by
  simp only [findCompat, List.find?_append] at *
  rw [h]
  simp [hc]

theorem findCompat_replace (ms : Externs) (m x : String) (k : Kind) :
    findCompat (ms.replace m k) x = (findCompat ms x).map fun p => if p.1 = m then (m, k) else p := by
  unfold findCompat Externs.replace
  rw [List.find?_map]
  congr 2
  funext p
  by_cases h : p.1 = m
  · simp [h]
  · simp [h]

theorem find?_filter_of {p r : String × Kind → Bool} :
    ∀ {l : Externs}, (∀ a ∈ l, p a = true → r a = true) → (l.filter r).find? p = l.find? p
  | [], _ => rfl
  | a :: l, h => by
    have ih := find?_filter_of (p := p) (r := r) (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    cases hp : p a with
    | true =>
      have hr : r a = true := h a (List.mem_cons_self ..) hp
      simp [hr, hp]
    | false =>
      cases hr : r a <;> simp [hr, hp, ih]

theorem find?_filter_none {p r : String × Kind → Bool} :
    ∀ {l : Externs}, (∀ a ∈ l, p a = true → r a = false) → (l.filter r).find? p = none
  | [], _ => rfl
  | a :: l, h => by
    have ih := find?_filter_none (p := p) (r := r) (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    cases hp : p a with
    | true => simp [h a (List.mem_cons_self ..) hp, ih]
    | false => cases hr : r a <;> simp [hr, hp, ih]

theorem mem_remove {ms : Externs} {m : String} {a : String × Kind} (h : a ∈ ms.remove m) :
    a ∈ ms ∧ a.1 ≠ m := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  exact ⟨h1, by simpa using h2⟩

/-! ## Steps preserve `Tracks` -/

theorem tracks_fresh {ms : Externs} {n : String} {k : Kind} (ht : Tracks ms)
    (hf : ∀ q ∈ ms, compat q.1 n = false) : Tracks (ms ++ [(n, k)]) :=
  List.pairwise_append.2 ⟨ht, List.pairwise_singleton _ _, fun a ha b hb => by
    rw [List.mem_singleton.1 hb]; exact hf a ha⟩

theorem tracks_replace {ms : Externs} {m : String} {k : Kind} (ht : Tracks ms) : Tracks (ms.replace m k) := by
  unfold Tracks Externs.replace
  rw [List.pairwise_map]
  refine ht.imp fun {a b} h => ?_
  by_cases ha : a.1 = m <;> by_cases hb : b.1 = m <;> simp_all

theorem tracks_upgrade {ms : Externs} {n m : String} {k0 k : Kind} (ht : Tracks ms) (hm : (m, k0) ∈ ms)
    (hc : compat m n = true) : Tracks (ms.remove m ++ [(n, k)]) := by
  refine List.pairwise_append.2 ⟨ht.filter _, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
  rw [List.mem_singleton.1 hb]
  obtain ⟨ha1, ha2⟩ := mem_remove ha
  cases hab : compat a.1 n with
  | false => rfl
  | true =>
    have e := tracks_eq ht ha1 hm (compat_trans hab (by rw [compat_comm]; exact hc))
    exact absurd (congrArg Prod.fst e) ha2

/-! ## The relation -/

theorem explicit_ok {ex : List String} {n : String} (h : ex.any (fun e => compat e n) = false) :
    ∀ e ∈ ex, compat e n = false := fun e he => by simpa using List.any_eq_false.1 h e he

/-- **`aggregate` is sound for `Aggregate`.** -/
theorem aggregate_sound {ex : List String} {ws ms ms' : Externs} (h : aggregate ex ms ws = .ok ms') :
    Aggregate ex ms ws ms' := by
  induction ws generalizing ms with
  | nil =>
    have e : ms = ms' := by simpa [aggregate] using h
    exact e ▸ .nil ms
  | cons p rest ih =>
    show Aggregate ex ms (p :: rest) ms'
    obtain ⟨n, k⟩ := p
    have hx : ex.any (fun e => compat e n) = false := by
      cases hx : ex.any (fun e => compat e n)
      · rfl
      · simp [aggregate, hx] at h
    have hx' : ∀ e ∈ ex, compat e n = false := explicit_ok hx
    cases hf : findCompat ms n with
    | none =>
      have h1 : aggregate ex (ms ++ [(n, k)]) rest = .ok ms' := by simpa [aggregate, hx, hf] using h
      exact .fresh hx' (findCompat_none hf) (ih h1)
    | some q =>
      show Aggregate ex ms ((n, k) :: rest) ms'
      obtain ⟨m, k0⟩ := q
      have hmc : (m, k0) ∈ ms ∧ compat m n = true := findCompat_mem hf
      cases hk : merge k0 k with
      | none => simp [aggregate, hx, hf, hk] at h
      | some k' =>
        show Aggregate ex ms ((n, k) :: rest) ms'
        cases hv : verGt n m with
        | true =>
          have h1 : aggregate ex (ms.remove m ++ [(n, k')]) rest = .ok ms' := by
            simpa [aggregate, hx, hf, hk, hv] using h
          exact .upgrade hx' hmc.1 hmc.2 hk hv (ih h1)
        | false =>
          have h1 : aggregate ex (ms.replace m k') rest = .ok ms' := by
            simpa [aggregate, hx, hf, hk, hv] using h
          exact .keep hx' hmc.1 hmc.2 hk hv (ih h1)

theorem explicit_any {ex : List String} {n : String} (h : ∀ e ∈ ex, compat e n = false) :
    ex.any (fun e => compat e n) = false :=
  List.any_eq_false.2 fun e he => by simp [h e he]

/-- **`aggregate` is complete for `Aggregate`**, from merged imports on distinct tracks. -/
theorem aggregate_complete {ex : List String} {ms ws ms' : Externs} (h : Aggregate ex ms ws ms')
    (ht : Tracks ms) : aggregate ex ms ws = .ok ms' := by
  induction h with
  | nil => rfl
  | fresh hx hf _ ih =>
    rw [aggregate, explicit_any hx, findCompat_of_none hf]
    exact ih (tracks_fresh ht hf)
  | keep hx hm hc hk hv _ ih =>
    rw [aggregate, explicit_any hx]
    simp only [Bool.false_eq_true, ↓reduceIte, findCompat_of_mem ht hm hc, hk, hv]
    exact ih (tracks_replace ht)
  | upgrade hx hm hc hk hv _ ih =>
    rw [aggregate, explicit_any hx]
    simp only [Bool.false_eq_true, ↓reduceIte, findCompat_of_mem ht hm hc, hk, hv]
    exact ih (tracks_upgrade ht hm hc)

theorem aggregate_iff {ex : List String} {ms ws ms' : Externs} (ht : Tracks ms) :
    aggregate ex ms ws = .ok ms' ↔ Aggregate ex ms ws ms' :=
  ⟨aggregate_sound, fun h => aggregate_complete h ht⟩

/-- No merged import is compatible with an explicit import. -/
def Disjoint (ex : List String) (ms : Externs) : Prop := ∀ q ∈ ms, ∀ e ∈ ex, compat e q.1 = false

/-- **One merged import per semver track, none compatible with an explicit import.** -/
theorem aggregate_tracks {ex : List String} {ms ws ms' : Externs} (h : Aggregate ex ms ws ms')
    (ht : Tracks ms) (hd : Disjoint ex ms) : Tracks ms' ∧ Disjoint ex ms' := by
  induction h with
  | nil => exact ⟨ht, hd⟩
  | fresh hx hf _ ih =>
    refine ih (tracks_fresh ht hf) fun q hq e he => ?_
    rcases List.mem_append.1 hq with hq | hq
    · exact hd q hq e he
    · rw [List.mem_singleton.1 hq]; exact hx e he
  | @keep ms rest ms' n m k k0 k' hx hm hc hk hv _ ih =>
    refine ih (tracks_replace ht) fun q hq e he => ?_
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hq
    by_cases e1 : q0.1 = m
    · simp only [e1, ↓reduceIte]; exact hd _ hm e he
    · simp only [e1, ↓reduceIte]; exact hd q0 hq0 e he
  | upgrade hx hm hc hk hv _ ih =>
    refine ih (tracks_upgrade ht hm hc) fun q hq e he => ?_
    rcases List.mem_append.1 hq with hq | hq
    · exact hd q (mem_remove hq).1 e he
    · rw [List.mem_singleton.1 hq]; exact hx e he

/-! ## Aggregation is a lower bound -/

/-- Every name compatible with a merged import of `ms` stays compatible with one of `ms'`,
at a subtype. -/
def Mono (ms ms' : Externs) : Prop :=
  ∀ x q, findCompat ms x = some q → ∃ q', findCompat ms' x = some q' ∧ Sub q'.2 q.2

theorem Mono.trans {a b c : Externs} (h1 : Mono a b) (h2 : Mono b c) : Mono a c := fun x q h => by
  obtain ⟨q1, e1, s1⟩ := h1 x q h
  obtain ⟨q2, e2, s2⟩ := h2 x q1 e1
  exact ⟨q2, e2, s2.trans s1⟩

/-- Every item is WIT-shaped. -/
def WitEx (es : Externs) : Prop := ∀ p ∈ es, p.2.wit = true

theorem mono_fresh {ms : Externs} {n : String} {k : Kind} : Mono ms (ms ++ [(n, k)]) :=
  fun _ q h => ⟨q, findCompat_append_old h _, Sub.refl _⟩

theorem mono_keep {ms : Externs} (ht : Tracks ms) {m : String} {k0 k' : Kind} (hm : (m, k0) ∈ ms)
    (hs : Sub k' k0) : Mono ms (ms.replace m k') := fun x q h => by
  rw [findCompat_replace, h]
  by_cases e : q.1 = m
  · have hq := (findCompat_mem h).1
    have eq : q = (m, k0) := tracks_eq ht hq hm (by rw [e]; exact compat_refl m)
    subst eq
    exact ⟨(m, k'), by simp, hs⟩
  · exact ⟨q, by simp [e], Sub.refl _⟩

theorem mono_upgrade {ms : Externs} (ht : Tracks ms) {n m : String} {k0 k' : Kind} (hm : (m, k0) ∈ ms)
    (hc : compat m n = true) (hs : Sub k' k0) : Mono ms (ms.remove m ++ [(n, k')]) := fun x q h => by
  obtain ⟨hq, hqx⟩ := findCompat_mem h
  cases hmx : compat m x with
  | false =>
    refine ⟨q, ?_, Sub.refl _⟩
    have e : findCompat (ms.remove m) x = some q := by
      unfold findCompat Externs.remove
      rw [find?_filter_of fun a _ ha => ?_]
      · exact h
      · have hne : a.1 ≠ m := fun e => by rw [← e, ha] at hmx; cases hmx
        simpa using hne
    exact findCompat_append_old e _
  | true =>
    have eq : q = (m, k0) := tracks_eq ht hq hm (compat_trans hqx (by rw [compat_comm]; exact hmx))
    subst eq
    have e : findCompat (ms.remove m) x = none := by
      unfold findCompat Externs.remove
      refine find?_filter_none fun a ha hax => ?_
      have := tracks_eq ht ha hm (compat_trans hax (by rw [compat_comm]; exact hmx))
      simp [this]
    have hnx : compat n x = true := compat_trans (by rw [compat_comm]; exact hc) hmx
    exact ⟨(n, k'), findCompat_append_new e n k' hnx, hs⟩

theorem witEx_replace {ms : Externs} {n : String} {k : Kind} (hw : WitEx ms) (hk : k.wit = true) :
    WitEx (ms.replace n k) := fun p hp => by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  by_cases e : q.1 = n
  · simpa [e] using hk
  · simpa [e] using hw q hq

theorem witEx_append {ms : Externs} {n : String} {k : Kind} (hw : WitEx ms) (hk : k.wit = true) :
    WitEx (ms ++ [(n, k)]) := fun p hp => by
  rcases List.mem_append.1 hp with h | h
  · exact hw p h
  · rw [List.mem_singleton.1 h]; exact hk

theorem witEx_remove {ms : Externs} {m : String} (hw : WitEx ms) : WitEx (ms.remove m) :=
  fun p hp => hw p (mem_remove hp).1

/-- What aggregation establishes. -/
structure AggOk (ms ms' ws : Externs) : Prop where
  wit : WitEx ms'
  mono : Mono ms ms'
  covers : ∀ p ∈ ws, ∃ q, findCompat ms' p.1 = some q ∧ Sub q.2 p.2

/-- The new merged import covers the wanted import it came from. -/
theorem covers_step {ms1 ms' : Externs} {n : String} {k : Kind} {q1 : String × Kind}
    (h1 : findCompat ms1 n = some q1) (hs : Sub q1.2 k) (hm : Mono ms1 ms') :
    ∃ q, findCompat ms' n = some q ∧ Sub q.2 k := by
  obtain ⟨q, e, s⟩ := hm n q1 h1
  exact ⟨q, e, s.trans hs⟩

/-- **Aggregation is sound**: the merged imports are WIT-shaped, keep every earlier
import at a subtype, and cover every wanted import at a subtype. -/
theorem aggregate_lower {ex : List String} {ws ms ms' : Externs} (h : Aggregate ex ms ws ms')
    (ht : Tracks ms) (hw : WitEx ms) (hws : WitEx ws) : AggOk ms ms' ws := by
  induction h with
  | nil ms => exact ⟨hw, fun _ q h => ⟨q, h, Sub.refl _⟩, fun _ hp => nomatch hp⟩
  | @fresh ms rest ms' n k hx hf _ ih =>
    show AggOk ms ms' ((n, k) :: rest)
    have hk : k.wit = true := hws (n, k) (by simp)
    have r := ih (tracks_fresh ht hf) (witEx_append hw hk) fun p hp => hws p (by simp [hp])
    have c := covers_step (findCompat_append_new (findCompat_of_none hf) n k (compat_refl n))
      (Sub.refl k) r.mono
    exact ⟨r.wit, mono_fresh.trans r.mono, fun p hp => (List.mem_cons.1 hp).elim (· ▸ c) (r.covers p)⟩
  | @keep ms rest ms' n m k k0 k' hx hm hc hk hv _ ih =>
    show AggOk ms ms' ((n, k) :: rest)
    have hkw : k.wit = true := hws (n, k) (by simp)
    obtain ⟨w1, s0, s1⟩ : k'.wit = true ∧ Sub k' k0 ∧ Sub k' k := merge_wit (hw _ hm) hkw hk
    have r := ih (tracks_replace ht) (witEx_replace hw w1) fun p hp => hws p (by simp [hp])
    have h1 : findCompat (ms.replace m k') n = some (m, k') := by
      rw [findCompat_replace, findCompat_of_mem ht hm hc]; simp
    have c := covers_step h1 s1 r.mono
    exact ⟨r.wit, (mono_keep ht hm s0).trans r.mono,
      fun p hp => (List.mem_cons.1 hp).elim (· ▸ c) (r.covers p)⟩
  | @upgrade ms rest ms' n m k k0 k' hx hm hc hk hv _ ih =>
    show AggOk ms ms' ((n, k) :: rest)
    have hkw : k.wit = true := hws (n, k) (by simp)
    obtain ⟨w1, s0, s1⟩ : k'.wit = true ∧ Sub k' k0 ∧ Sub k' k := merge_wit (hw _ hm) hkw hk
    have r := ih (tracks_upgrade ht hm hc) (witEx_append (witEx_remove hw) w1)
      fun p hp => hws p (by simp [hp])
    have h0 : findCompat (ms.remove m) n = none := by
      unfold findCompat Externs.remove
      refine find?_filter_none fun a ha han => ?_
      have := tracks_eq ht ha hm (compat_trans han (by rw [compat_comm]; exact hc))
      simp [this]
    have c := covers_step (findCompat_append_new h0 n k' (compat_refl n)) s1 r.mono
    exact ⟨r.wit, (mono_upgrade ht hm hc s0).trans r.mono,
      fun p hp => (List.mem_cons.1 hp).elim (· ▸ c) (r.covers p)⟩

/-! ## Typing -/

theorem find_of_mem {es : Externs} {n : String} {k : Kind} (h : (n, k) ∈ es) :
    ∃ k0, es.find n = some k0 := by
  induction es with
  | nil => cases h
  | cons p es ih =>
    obtain ⟨x, v⟩ := p
    rw [lookup_cons]
    by_cases hx : n = x
    · exact ⟨v, ite_yes hx⟩
    · rw [ite_no hx]
      rcases List.mem_cons.1 h with e | h
      · exact absurd (congrArg Prod.fst e) hx
      · exact ih h

theorem getElem_findIdx_compat {ms : Externs} {n : String} {q : String × Kind}
    (h : findCompat ms n = some q) : ms[ms.findIdx fun p => compat p.1 n]? = some q := by
  induction ms with
  | nil => cases h
  | cons p ms ih =>
    unfold findCompat at h
    rw [List.find?_cons] at h
    cases hp : compat p.1 n with
    | true =>
      rw [hp] at h
      simp only [Option.some.injEq] at h
      subst h
      simp [List.findIdx_cons, hp]
    | false =>
      rw [hp] at h
      simp only [List.findIdx_cons, hp]
      exact ih h

theorem extend_kind (base : Nat) (ms : Externs) (nd : CNode) : (extend base ms nd).kind = nd.kind := by
  unfold extend; split <;> rfl

/-- The resolved graph. -/
def resolved (g : CGraph) (ms : Externs) : CGraph :=
  { g with nodes := (g.nodes.map (extend g.nodes.length ms)) ++ ms.map fun q => ⟨.implicit q.1, q.2⟩ }

theorem resolve_ok {g g' : CGraph} (h : resolve g = .ok g') :
    ∃ ms, aggregate g.importNames [] (wanted g) = .ok ms ∧ g' = resolved g ms := by
  simp only [resolve, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i ms hms
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨ms, hms, h.symm⟩

theorem kindOf_resolved_old {g : CGraph} {ms : Externs} {j : Nat} (hj : j < g.nodes.length) :
    (resolved g ms).kindOf j = g.kindOf j := by
  have hl : j < (g.nodes.map (extend g.nodes.length ms)).length := by simpa using hj
  simp only [resolved, CGraph.kindOf, List.getElem?_append_left hl, List.getElem?_map]
  cases g.nodes[j]? <;> simp [extend_kind]

theorem kindOf_resolved_new {g : CGraph} {ms : Externs} {n : String} {q : String × Kind}
    (h : findCompat ms n = some q) : (resolved g ms).kindOf (nodeOf g.nodes.length ms n) = q.2 := by
  have hl : (g.nodes.map (extend g.nodes.length ms)).length ≤ nodeOf g.nodes.length ms n := by
    simp [nodeOf]
  have e : ((resolved g ms).nodes)[nodeOf g.nodes.length ms n]? = some ⟨.implicit q.1, q.2⟩ := by
    unfold resolved
    rw [List.getElem?_append_right hl]
    simp only [List.length_map, nodeOf, Nat.add_sub_cancel_left, List.getElem?_map, getElem_findIdx_compat h,
      Option.map_some]
  simp only [CGraph.kindOf, e, Option.map_some, Option.getD_some]

/-- **`resolve` decides `Resolve`.** -/
theorem resolve_iff {g g' : CGraph} : resolve g = .ok g' ↔ Resolve g g' := by
  constructor
  · intro h
    obtain ⟨ms, hagg, rfl⟩ := resolve_ok h
    exact .mk (aggregate_sound hagg)
  · intro h
    cases h with
    | mk hagg =>
      have hok : aggregate g.importNames [] (wanted g) = .ok _ := aggregate_complete hagg List.Pairwise.nil
      simp only [resolve, bind, Except.bind, hok, pure, Except.pure]

/-- Every explicit argument refers to an existing node and type-checks. -/
def ExplicitTyped (g : CGraph) : Prop :=
  ∀ nd ∈ g.nodes, ∀ p imps args, nd.op = .inst p imps args →
    ∀ a ∈ args, a.2 < g.nodes.length ∧ ∃ k, imps.find a.1 = some k ∧ Sub (g.kindOf a.2) k

/-- Every import of every instantiated package is WIT-shaped. -/
def ImportsWit (g : CGraph) : Prop :=
  ∀ nd ∈ g.nodes, ∀ p imps args, nd.op = .inst p imps args → WitEx imps

theorem mem_wanted {g : CGraph} {nd : CNode} (hnd : nd ∈ g.nodes) {p : String} {imps : Externs}
    {args : List (String × Nat)} (hop : nd.op = .inst p imps args) {q : String × Kind}
    (hq : q ∈ unsatisfied imps args) : q ∈ wanted g :=
  List.mem_flatMap.2 ⟨nd, hnd, by rw [hop]; exact hq⟩

theorem wanted_wit {g : CGraph} (hW : ImportsWit g) : WitEx (wanted g) := fun q hq => by
  obtain ⟨nd, hnd, hq'⟩ := List.mem_flatMap.1 hq
  revert hq'
  cases hop : nd.op with
  | inst p imps args => exact fun hq' => hW nd hnd p imps args hop q (List.mem_filter.1 hq').1
  | _ => exact fun hq' => nomatch hq'

/-- An implicit argument is well typed. -/
theorem implicit_arg_typed {g : CGraph} {ms : Externs} (hA : AggOk [] ms (wanted g)) {nd : CNode}
    (hnd : nd ∈ g.nodes) {p : String} {imps : Externs} {args : List (String × Nat)}
    (hop : nd.op = .inst p imps args) {q : String × Kind} (hq : q ∈ unsatisfied imps args) :
    ∃ k, imps.find q.1 = some k ∧ Sub ((resolved g ms).kindOf (nodeOf g.nodes.length ms q.1)) k := by
  have hqi : q ∈ imps := (List.mem_filter.1 hq).1
  obtain ⟨k0, hk0⟩ := find_of_mem (n := q.1) (k := q.2) hqi
  have hm0 : (q.1, k0) ∈ unsatisfied imps args :=
    List.mem_filter.2 ⟨Externs.find_mem hk0, (List.mem_filter.1 hq).2⟩
  obtain ⟨q', hq', hs⟩ := hA.covers _ (mem_wanted hnd hop hm0)
  exact ⟨k0, hk0, by rw [kindOf_resolved_new hq']; exact hs⟩

/-- **After resolution every argument is well typed**, given checked explicit
arguments and WIT-shaped imports. -/
theorem resolve_typed {g g' : CGraph} (h : resolve g = .ok g') (hT : ExplicitTyped g)
    (hW : ImportsWit g) : g'.Typed := by
  obtain ⟨ms, hagg, rfl⟩ := resolve_ok h
  have hA : AggOk [] ms (wanted g) :=
    aggregate_lower (aggregate_sound hagg) List.Pairwise.nil (fun _ hp => nomatch hp) (wanted_wit hW)
  intro nd hnd p imps args hop a ha
  rcases List.mem_append.1 hnd with h1 | h1
  · obtain ⟨nd0, hnd0, rfl⟩ := List.mem_map.1 h1
    obtain ⟨args0, hop0, rfl⟩ := extend_op_inst hop
    rcases List.mem_append.1 ha with h2 | h2
    · obtain ⟨hlt, k, hk, hs⟩ := hT nd0 hnd0 p imps args0 hop0 a h2
      exact ⟨k, hk, by rw [kindOf_resolved_old hlt]; exact hs⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h2
      exact implicit_arg_typed hA hnd0 hop0 hq
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h1
    cases hop

end Implicit

end Silmaril.Wasm.Wac
