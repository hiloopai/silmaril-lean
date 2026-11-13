module

public import Silmaril.Wasm.Tools.Component.Args.Defs

/-!
# Specification of the `wasm-tools component …` argument grammar

For every spec `s` and arguments `args`, when `parse s args = .ok is`:

* `parse_ok_declared`: every item names a declared option or positional of `s`;
* `parse_ok_no_conflict`: no pair of `s.conflicts` is present;
* `parse_ok_required`: every required positional and required option is present, and every
  requirement `(a, b)` of `s.requires` with `a` present has `b` present, or a present argument
  that conflicts with `b` (clap's rule);
* `parse_ok_scan`: `is` is exactly what `scan` read (`finish` only checks).

Conversely (`parse_of_scan`), a scan that succeeds and passes the checks is the parse. The
reading functions satisfy `optBool_absent` / `optBool_bare` / `optBool_eq`, the semantics of
clap's `Option<Option<bool>>` with a default (`optional_flag_with_default` in upstream's
`component.rs`).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Args

/-- An item names a declared option or positional. -/
def Declared (s : Spec) (i : Item) : Prop :=
  i.key ∈ s.opts.map Opt.key ∨ i.key ∈ s.pos.map Pos.key

/-- Every item of a successful outcome is declared. -/
def AllDecl (s : Spec) : Outcome → Prop
  | .ok is => ∀ i ∈ is, Declared s i
  | _ => True

theorem AllDecl.cons {s : Spec} {i : Item} {o : Outcome} (hi : Declared s i) (ho : AllDecl s o) :
    AllDecl s (o.cons i) := by
  cases o with
  | ok is =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact ho j hj
  | help _ => trivial
  | err _ => trivial

theorem AllDecl.prepend {s : Spec} {is : List Item} {o : Outcome} (hi : ∀ i ∈ is, Declared s i)
    (ho : AllDecl s o) : AllDecl s (o.prepend is) := by
  cases o with
  | ok js =>
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hi j hj
    · exact ho j hj
  | help _ => trivial
  | err _ => trivial

theorem declared_opt {s : Spec} {o : Opt} (ho : o ∈ s.opts) (v : Option String) :
    Declared s (.opt o.key v) :=
  Or.inl (List.mem_map_of_mem ho)

theorem use_declared {s : Spec} {st st' : St} {o : Opt} {v : Option String} {i : Item}
    (ho : o ∈ s.opts) (h : st.use o v = .ok (st', i)) : Declared s i := by
  unfold St.use at h
  split at h
  · cases h; exact declared_opt ho v
  · split at h
    · cases h
    · cases h; exact declared_opt ho v

theorem useValue_declared {s : Spec} {st st' : St} {o : Opt} {v : String} {i : Item}
    (ho : o ∈ s.opts) (h : st.useValue o v = .ok (st', i)) : Declared s i := by
  unfold St.useValue at h
  split at h
  · cases h
  · split at h
    · exact use_declared ho h
    · cases h

theorem positional_declared {s : Spec} {st st' : St} {a : String} {i : Item}
    (h : st.positional s a = .ok (st', i)) : Declared s i := by
  unfold St.positional at h
  split at h
  · rename_i p hp
    cases h
    exact Or.inr (List.mem_map_of_mem (List.mem_of_getElem? hp))
  · cases h

theorem map_ok_inv {ε α β : Type} {e : Except ε α} {f : α → β} {r : β}
    (h : e.map f = .ok r) : ∃ a, e = .ok a ∧ r = f a := by
  cases e with
  | error _ => cases h
  | ok a => cases h; exact ⟨a, rfl, rfl⟩

theorem shortStep_declared {s : Spec} {st st' : St} {o : Opt} {cs rest : List Char}
    {next : Option String} {i : Item} {u : Bool} (ho : o ∈ s.opts)
    (h : shortStep st o cs next = .ok (st', i, rest, u)) : Declared s i := by
  have hv : ∀ v st₀ i₀, st.useValue o v = .ok (st₀, i₀) → Declared s i₀ :=
    fun _ _ _ h => useValue_declared ho h
  have hu : ∀ v st₀ i₀, st.use o v = .ok (st₀, i₀) → Declared s i₀ :=
    fun _ _ _ h => use_declared ho h
  unfold shortStep at h
  split at h <;> (repeat' split at h) <;>
    first
    | cases h
    | (obtain ⟨⟨_, _⟩, he, hr⟩ := map_ok_inv h; cases hr; first | exact hv _ _ _ he | exact hu _ _ _ he)

theorem scanCluster_declared {s : Spec} :
    ∀ (f : Nat) (st : St) (cs : List Char) (next : Option String) {st' : St} {is : List Item}
      {u : Bool}, scanCluster s f st cs next = .ok (st', is, u) → ∀ i ∈ is, Declared s i
  | 0, _, _, _, _, _, _, h => by cases h; simp
  | _ + 1, _, [], _, _, _, _, h => by cases h; simp
  | f + 1, st, c :: cs, next, st', is, u, h => by
    unfold scanCluster at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i o hfo
        have ho : o ∈ s.opts := List.mem_of_find?_eq_some hfo
        split at h
        · cases h
        · rename_i st₁ i₁ rest₁ used₁ hstep
          have hi₁ : Declared s i₁ := shortStep_declared ho hstep
          split at h
          · cases h; simpa using hi₁
          · split at h
            · rename_i st₂ is₂ u₂ hrec
              cases h
              intro j hj
              rcases List.mem_cons.mp hj with rfl | hj
              · exact hi₁
              · exact scanCluster_declared f st₁ rest₁ next hrec j hj
            · cases h

theorem scanLong_declared {s : Spec} {st st' : St} {body : String} {next : Option String}
    {i : Item} {u : Bool} (h : scanLong s st body next = .ok (st', i, u)) : Declared s i := by
  unfold scanLong at h
  split at h
  · cases h
  · rename_i o hfo
    have ho : o ∈ s.opts := List.mem_of_find?_eq_some hfo
    have hv : ∀ v st₀ i₀, st.useValue o v = .ok (st₀, i₀) → Declared s i₀ :=
      fun _ _ _ h => useValue_declared ho h
    have hu : ∀ v st₀ i₀, st.use o v = .ok (st₀, i₀) → Declared s i₀ :=
      fun _ _ _ h => use_declared ho h
    split at h <;> (repeat' split at h) <;>
      first
      | cases h
      | (obtain ⟨⟨_, _⟩, he, hr⟩ := map_ok_inv h; cases hr; first | exact hv _ _ _ he | exact hu _ _ _ he)

/-- Everything `scan` reads is declared. -/
theorem scan_declared (s : Spec) (st : St) : (args : List String) → AllDecl s (scan s st args)
  | [] => by
    unfold scan
    intro i hi
    cases hi
  | a :: rest => by
    unfold scan
    split
    · split
      · rename_i st' i hp
        exact AllDecl.cons (positional_declared hp) (scan_declared s st' rest)
      · trivial
    · split
      · exact scan_declared s _ rest
      · split
        · trivial
        · split
          · split
            · trivial
            · rename_i st' i used hl
              exact AllDecl.cons (scanLong_declared hl) (scan_declared s st' (after used rest))
          · split
            · split
              · trivial
              · trivial
              · rename_i st' is used hc
                exact AllDecl.prepend (scanCluster_declared _ _ _ _ hc)
                  (scan_declared s st' (after used rest))
            · split
              · rename_i st' i hp
                exact AllDecl.cons (positional_declared hp) (scan_declared s st' rest)
              · trivial
termination_by args => args.length
decreasing_by
  all_goals simp_wf
  all_goals first | omega | exact Nat.lt_of_le_of_lt (after_length_le _ _) (by simp)

/-! ## `finish` and `parse` -/

theorem finish_ok {s : Spec} {is js : List Item} (h : finish s is = .ok js) :
    js = is ∧ firstConflict s is = none ∧ missingNames s is = [] := by
  unfold finish at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · rename_i hm
      cases h
      exact ⟨rfl, hc, hm⟩
    · cases h

theorem parse_ok_scan {s : Spec} {args : List String} {is : List Item}
    (h : parse s args = .ok is) :
    scan s {} args = .ok is ∧ firstConflict s is = none ∧ missingNames s is = [] := by
  unfold parse at h
  split at h
  · rename_i js hs
    obtain ⟨rfl, hc, hm⟩ := finish_ok h
    exact ⟨hs, hc, hm⟩
  · rename_i o hno
    exact (hno is h).elim

/-- Conversely: a successful scan that passes the checks is the parse. -/
theorem parse_of_scan {s : Spec} {args : List String} {is : List Item}
    (hs : scan s {} args = .ok is) (hc : firstConflict s is = none) (hm : missingNames s is = []) :
    parse s args = .ok is := by
  simp only [parse, hs, finish, hc, hm]

/-- **Declared**: a parse names only declared options and positionals. -/
theorem parse_ok_declared {s : Spec} {args : List String} {is : List Item}
    (h : parse s args = .ok is) : ∀ i ∈ is, Declared s i := by
  have hs : scan s {} args = .ok is := (parse_ok_scan h).1
  have ha : AllDecl s (scan s {} args) := scan_declared s {} args
  rw [hs] at ha
  exact ha

/-- **No conflict**: no conflicting pair is present. -/
theorem parse_ok_no_conflict {s : Spec} {args : List String} {is : List Item}
    (h : parse s args = .ok is) :
    ∀ p ∈ s.conflicts, ¬ (present is p.1 = true ∧ present is p.2 = true) := by
  intro p hp ⟨h1, h2⟩
  have hc : firstConflict s is = none := (parse_ok_scan h).2.1
  have hn := List.find?_eq_none.mp hc p hp
  simp [h1, h2] at hn

theorem filterMap_eq_nil_iff' {α β : Type} {f : α → Option β} {l : List α} :
    l.filterMap f = [] ↔ ∀ a ∈ l, f a = none := by
  simp [List.filterMap_eq_nil_iff]

/-- **Required**: required positionals and options are present, and requirements hold. -/
theorem parse_ok_required {s : Spec} {args : List String} {is : List Item}
    (h : parse s args = .ok is) :
    (∀ p ∈ s.pos, p.required = true → present is p.key = true) ∧
    (∀ k ∈ s.required, present is k = true) ∧
    (∀ r ∈ s.requires, present is r.1 = true →
      present is r.2 = true ∨ conflictsWithPresent s is r.2 = true) := by
  have hm : missingNames s is = [] := (parse_ok_scan h).2.2
  simp only [missingNames, List.append_eq_nil_iff, filterMap_eq_nil_iff'] at hm
  obtain ⟨⟨hr, hq⟩, hp⟩ := hm
  refine ⟨fun p hpm hreq => ?_, fun k hk => ?_, fun r hrm ha => ?_⟩
  · simpa [hreq] using hp p hpm
  · simpa using hq k hk
  · have hn := hr r hrm
    cases h2 : present is r.2 <;> cases h3 : conflictsWithPresent s is r.2 <;>
      simp_all

/-! ## Reading -/

theorem optBool_absent {is : List Item} {k : String} (h : present is k = false) (d : Bool) :
    optBool is k d = d := by
  have hf : is.find? (·.key == k) = none := by
    rw [List.find?_eq_none]
    intro x hx hk
    have : present is k = true := List.any_eq_true.mpr ⟨x, hx, hk⟩
    rw [h] at this
    cases this
  simp [optBool, hf]

theorem optBool_bare (rest : List Item) (k : String) (d : Bool) :
    optBool (.opt k none :: rest) k d = true := by
  simp [optBool, Item.key]

theorem optBool_eq (rest : List Item) (k v : String) (d : Bool) :
    optBool (.opt k (some v) :: rest) k d = (v == "true") := by
  simp [optBool, Item.key]

end Silmaril.Wasm.Tools.Component.Args
