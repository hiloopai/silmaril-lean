module

public import Silmaril.Wasm.Wit.Elab.Defs

/-!
# Elaboration: the topological sort

* `toposort_perm`: what `toposort` returns is a permutation of its input;
* `toposort_complete`: `toposort` succeeds when every reference of an entry is
  placed or names a remaining entry of smaller rank (an acyclic scope), with
  fuel at least the number of entries.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

theorem toposort_perm : ∀ (f : Nat) (placed : List Name) (rest out : List Entry),
    toposort f placed rest = some out → out.Perm rest
  | _, _, [], out, h => by
    have hout : out = [] := by simpa [toposort] using h.symm
    rw [hout]
  | 0, _, _ :: _, _, h => by cases h
  | f + 1, placed, x :: xs, out, h => by
    unfold toposort at h
    cases hf : (x :: xs).find? (fun e => e.2.1.all (· ∈ placed)) with
    | none => rw [hf] at h; cases h
    | some e =>
      have hmem : e ∈ x :: xs := List.mem_of_find?_eq_some hf
      have h' : ((toposort f (e.1 :: placed) ((x :: xs).erase e)).map (e :: ·)) = some out := by
        simpa only [hf] using h
      obtain ⟨out', hr, hout⟩ := Option.map_eq_some_iff.mp h'
      have ih : out'.Perm ((x :: xs).erase e) := toposort_perm f _ _ out' hr
      rw [← hout]
      exact (ih.cons e).trans (List.perm_cons_erase hmem).symm

/-- Every reference of an entry of `rest` is placed or names an entry of `rest`
of smaller rank. -/
def Ranked (r : Name → Nat) (placed : List Name) (rest : List Entry) : Prop :=
  ∀ e ∈ rest, ∀ x ∈ e.2.1, x ∈ placed ∨ ∃ e' ∈ rest, e'.1 = x ∧ r x < r e.1

/-- In a ranked nonempty scope some entry is ready. -/
theorem exists_ready {r : Name → Nat} {placed : List Name} {rest : List Entry}
    (hr : Ranked r placed rest) : ∀ (n : Nat) (e : Entry), e ∈ rest → r e.1 = n →
      ∃ e' ∈ rest, ∀ x ∈ e'.2.1, x ∈ placed := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e he hn
    by_cases hready : ∀ x ∈ e.2.1, x ∈ placed
    · exact ⟨e, he, hready⟩
    · obtain ⟨x, hx, hxp⟩ : ∃ x ∈ e.2.1, x ∉ placed := by
        simpa only [not_forall, exists_prop] using hready
      have hlt : ∃ e' ∈ rest, e'.1 = x ∧ r x < r e.1 := (hr e he x hx).resolve_left hxp
      obtain ⟨e', he', hname, hlt'⟩ := hlt
      exact ih (r e'.1) (by rw [hname, ← hn]; exact hlt') e' he' rfl

/-- Placing a ready entry keeps the scope ranked. -/
theorem Ranked.erase {r : Name → Nat} {placed : List Name} {rest : List Entry}
    (hr : Ranked r placed rest) (e : Entry) : Ranked r (e.1 :: placed) (rest.erase e) := by
  intro e₁ he₁ x hx
  have he₁' : e₁ ∈ rest := List.mem_of_mem_erase he₁
  rcases hr e₁ he₁' x hx with hp | ⟨e', he', hname, hlt⟩
  · exact .inl (List.mem_cons_of_mem _ hp)
  · by_cases heq : e' = e
    · exact .inl (by rw [← hname, heq]; exact List.mem_cons_self)
    · exact .inr ⟨e', (List.mem_erase_of_ne heq).mpr he', hname, hlt⟩

theorem find?_ready {placed : List Name} {rest : List Entry} {e : Entry} (he : e ∈ rest)
    (hready : ∀ x ∈ e.2.1, x ∈ placed) :
    ∃ e', rest.find? (fun e => e.2.1.all (· ∈ placed)) = some e' := by
  have hsome : (rest.find? (fun e => e.2.1.all (· ∈ placed))).isSome := by
    rw [List.find?_isSome]
    exact ⟨e, he, List.all_eq_true.mpr fun x hx => decide_eq_true (hready x hx)⟩
  exact Option.isSome_iff_exists.mp hsome

/-- **`toposort` succeeds on ranked scopes.** -/
theorem toposort_complete {r : Name → Nat} : ∀ (f : Nat) (placed : List Name) (rest : List Entry),
    rest.length ≤ f → Ranked r placed rest → ∃ out, toposort f placed rest = some out
  | _, _, [], _, _ => ⟨[], by simp [toposort]⟩
  | 0, _, _ :: _, hf, _ => absurd hf (by simp)
  | f + 1, placed, x :: xs, hf, hr => by
    obtain ⟨e₀, he₀, hready⟩ := exists_ready hr (r x.1) x List.mem_cons_self rfl
    obtain ⟨e, hfind⟩ := find?_ready he₀ hready
    have hmem : e ∈ x :: xs := List.mem_of_find?_eq_some hfind
    have hlen : ((x :: xs).erase e).length ≤ f := by
      rw [List.length_erase_of_mem hmem]
      simpa using hf
    obtain ⟨out, hout⟩ := toposort_complete f (e.1 :: placed) _ hlen (hr.erase e)
    refine ⟨e :: out, ?_⟩
    unfold toposort
    rw [hfind]
    simp [hout]

end Silmaril.Wasm.Wit.Elab
