module

public import Silmaril.Proofs.Wasm.Wit.Elab.Topo
public import Silmaril.Wasm.Wit.Valid.Thms

/-!
# Elaboration: the types of a scope exist on acyclic scopes

`elabTypes_isSome`: the types of a scope are elaborated (the topological sort
succeeds) when the scope's names are distinct, every reference of a type
definition denotes a type (`Binds`), and the type reference graph is acyclic
(`Valid.typeAcyclic`).
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

/-- The names a scope item binds. -/
def ScopeItem.names : ScopeItem → List Name
  | .type d => [d.name]
  | .use u => u.names.map UseName.bound

theorem mem_scopeEntries_type {c : Ctx} {o : Owner} {d : TypeDef} :
    ∀ {items : List ScopeItem}, ScopeItem.type d ∈ items →
      (d.name, d.refs.map (·.2), some (elabTypeDef c o d)) ∈ scopeEntries c o items
  | [], h => absurd h List.not_mem_nil
  | it :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have ih := mem_scopeEntries_type (c := c) (o := o) h
      cases it with
      | type d' => exact List.mem_cons_of_mem _ ih
      | use u => exact List.mem_append_right _ ih

theorem mem_scopeEntries_use {c : Ctx} {o : Owner} {u : Use} {un : UseName} (hun : un ∈ u.names) :
    ∀ {items : List ScopeItem}, ScopeItem.use u ∈ items → (un.bound, [], none) ∈ scopeEntries c o items
  | [], h => absurd h List.not_mem_nil
  | it :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨un, hun, rfl⟩)
    · have ih := mem_scopeEntries_use (c := c) (o := o) hun h
      cases it with
      | type d' => exact List.mem_cons_of_mem _ ih
      | use u' => exact List.mem_append_right _ ih

/-- An entry is a type definition with its references, or a `use`d name. -/
theorem scopeEntries_cases {c : Ctx} {o : Owner} {e : Entry} :
    ∀ {items : List ScopeItem}, e ∈ scopeEntries c o items →
      (∃ d, ScopeItem.type d ∈ items ∧ e.1 = d.name ∧ e.2.1 = d.refs.map (·.2)) ∨ e.2.1 = []
  | [], h => absurd h List.not_mem_nil
  | .type d :: rest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl ⟨d, List.mem_cons_self, rfl, rfl⟩
    · rcases scopeEntries_cases h with ⟨d', hd', h1, h2⟩ | h0
      · exact .inl ⟨d', List.mem_cons_of_mem _ hd', h1, h2⟩
      · exact .inr h0
  | .use u :: rest, h => by
    rcases List.mem_append.mp h with h | h
    · obtain ⟨un, _, rfl⟩ := List.mem_map.mp h
      exact .inr rfl
    · rcases scopeEntries_cases h with ⟨d', hd', h1, h2⟩ | h0
      · exact .inl ⟨d', List.mem_cons_of_mem _ hd', h1, h2⟩
      · exact .inr h0

/-- With distinct names, the first binding of a defined name is its definition. -/
theorem findSome_src_type {d : TypeDef} : ∀ {items : List ScopeItem},
    (items.flatMap ScopeItem.names).Nodup → ScopeItem.type d ∈ items →
      items.findSome? (·.src? d.name) = some (.type d)
  | [], _, h => absurd h List.not_mem_nil
  | it :: rest, hn, h => by
    have hn' : (rest.flatMap ScopeItem.names).Nodup := (List.nodup_append.mp (by simpa using hn)).2.1
    rcases List.mem_cons.mp h with rfl | h
    · simp [ScopeItem.src?]
    · have hnot : d.name ∉ ScopeItem.names it := by
        intro hm
        have hdis := (List.nodup_append.mp (by simpa using hn)).2.2
        exact hdis d.name hm d.name (List.mem_flatMap.mpr ⟨_, h, by simp [ScopeItem.names]⟩) rfl
      have hnone : it.src? d.name = none := by
        cases it with
        | type d' =>
          have hne : d'.name ≠ d.name := fun he => hnot (by simp [ScopeItem.names, he])
          simp [ScopeItem.src?, hne]
        | use u =>
          simp only [ScopeItem.src?, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
          intro un hun hb
          exact hnot (List.mem_map.mpr ⟨un, hun, hb⟩)
      rw [List.findSome?_cons_of_isNone (by simp [hnone])]
      exact findSome_src_type hn' h

/-- What binds a name in a scope is an item of the scope binding that name. -/
theorem src_entry {c : Ctx} {o : Owner} {items : List ScopeItem} {x : Name} {src : Src}
    (h : items.findSome? (·.src? x) = some src) : ∃ e ∈ scopeEntries c o items, e.1 = x := by
  obtain ⟨it, hit, hsrc⟩ := List.exists_of_findSome?_eq_some h
  cases it with
  | type d =>
    have hx : d.name = x := by
      by_contra hne
      simp [ScopeItem.src?, hne] at hsrc
    exact ⟨_, mem_scopeEntries_type hit, hx⟩
  | use u =>
    obtain ⟨un, hun, hb⟩ : ∃ un ∈ u.names, un.bound = x := by
      simp only [ScopeItem.src?, Option.map_eq_some_iff] at hsrc
      obtain ⟨un, hf, _⟩ := hsrc
      exact ⟨un, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
    exact ⟨_, mem_scopeEntries_use hun hit, hb⟩

/-- The rank of a name of the scope of `o`: definitions above `use`d names. -/
def nameRank (U : Universe) (o : Owner) (s : TypeId → Nat) (x : Name) : Nat :=
  match o.src? U x with
  | some (.type _) => s ⟨o, x⟩ + 1
  | _ => 0

/-- A reference of a definition of an acyclic scope is a remaining entry of
smaller rank. -/
theorem ranked_ref {c : Ctx} {U : Universe} {o : Owner} {items : List ScopeItem} {s : TypeId → Nat}
    (hsc : o.scope U = some items) (hn : (items.flatMap ScopeItem.names).Nodup)
    (hacyc : ∀ t t', TypeEdge U t t' → s t' < s t) {d : TypeDef} (hd : ScopeItem.type d ∈ items)
    {r : Ref} (hr : r ∈ d.refs) {t : TypeId} (hb : Binds U o r.2 t) :
    ∃ e' ∈ scopeEntries c o items, e'.1 = r.2 ∧ nameRank U o s r.2 < nameRank U o s d.name := by
  have hsrcd : o.src? U d.name = some (.type d) := by
    simp only [Owner.src?, hsc, Option.bind_some]; exact findSome_src_type hn hd
  have hrd : nameRank U o s d.name = s ⟨o, d.name⟩ + 1 := by simp only [nameRank, hsrcd]
  have hdef : U.typeDef? ⟨o, d.name⟩ = some d := by simp only [Universe.typeDef?, hsrcd]
  cases hb with
  | @type d' hsrc =>
    have hsrc' : items.findSome? (·.src? r.2) = some (.type d') := by
      simpa only [Owner.src?, hsc, Option.bind_some] using hsrc
    obtain ⟨e', he', hname⟩ := src_entry (c := c) hsrc'
    have hedge : TypeEdge U ⟨o, d.name⟩ ⟨o, r.2⟩ := ⟨d, hdef, r, hr, .type hsrc⟩
    have hlt : s ⟨o, r.2⟩ < s ⟨o, d.name⟩ := hacyc _ _ hedge
    refine ⟨e', he', hname, ?_⟩
    simp only [nameRank, hsrc, hsrcd]; omega
  | @use path y j t' hsrc _ _ =>
    have hsrc' : items.findSome? (·.src? r.2) = some (.use path y) := by
      simpa only [Owner.src?, hsc, Option.bind_some] using hsrc
    obtain ⟨e', he', hname⟩ := src_entry (c := c) hsrc'
    refine ⟨e', he', hname, ?_⟩
    simp only [nameRank, hsrc, hsrcd]; omega

/-- **The types of an acyclic scope are elaborated.** -/
theorem elabTypes_isSome {c : Ctx} {U : Universe} {o : Owner} {items : List ScopeItem}
    (hsc : o.scope U = some items) (hn : (items.flatMap ScopeItem.names).Nodup)
    (hrefs : ∀ d, ScopeItem.type d ∈ items → ∀ r ∈ d.refs, ∃ t, Binds U o r.2 t)
    (hacyc : ∃ s : TypeId → Nat, ∀ t t', TypeEdge U t t' → s t' < s t) :
    (elabTypes c o items).isSome := by
  obtain ⟨s, hs⟩ := hacyc
  have hranked : Ranked (nameRank U o s) [] (scopeEntries c o items) := by
    intro e he x hx
    rcases scopeEntries_cases he with ⟨d, hd, h1, h2⟩ | h0
    · rw [h2] at hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      obtain ⟨t, hb⟩ := hrefs d hd r hr
      rw [h1]
      exact .inr (ranked_ref hsc hn hs hd hr hb)
    · rw [h0] at hx; exact absurd hx List.not_mem_nil
  obtain ⟨out, hout⟩ := toposort_complete _ [] _ (Nat.le_refl _) hranked
  simp [elabTypes, hout]

end Silmaril.Wasm.Wit.Elab
