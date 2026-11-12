module

public import Silmaril.Cli.Getopt.Defs

/-!
# Proofs: long-name resolution and permutation in the getopt dialect

* `resolveLong_exact`, `resolveLong_ok`, `resolveLong_unique`: an exact name wins; a resolved
  prefix is unique up to the target of the entries it is a prefix of, and a prefix all of whose
  entries mean one option resolves to it;
* `readTok_false`: an option token that does not take the next token reads the same whatever
  follows it;
* **`parse_permuted`**: the GNU reading (`permute`) of an argument vector is the POSIX reading
  (`requireOrder`) of its permuted vector `Parsed.permuted`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Cli.Getopt

open Silmaril.Cli Silmaril.Cli.Getopt

/-! ## Long names -/

theorem prefixOf_self (n : String) : prefixOf n n = true := by
  simp [prefixOf, List.isPrefixOf_iff_prefix]

theorem resolveLong_exact {ls : List Long} {n : String} {l : Long}
    (h : ls.find? (·.name == n) = some l) : resolveLong ls n = .ok l := by
  simp [resolveLong, h]

theorem resolveLong_ok {ls : List Long} {n : String} {l : Long} (h : resolveLong ls n = .ok l) :
    l ∈ ls ∧ (l.name = n ∨ (prefixOf n l.name = true ∧ (∀ l' ∈ ls, l'.name ≠ n) ∧
      ∀ l' ∈ ls, prefixOf n l'.name = true → l'.target = l.target)) := by
  cases hf : ls.find? (·.name == n) with
  | some l₀ =>
    rw [resolveLong_exact hf] at h
    cases h
    exact ⟨List.mem_of_find?_eq_some hf, .inl (by simpa using List.find?_some hf)⟩
  | none =>
    have hne : ∀ l' ∈ ls, l'.name ≠ n := by
      intro l' hl' he
      have := List.find?_eq_none.1 hf l' hl'
      simp [he] at this
    cases hfil : ls.filter (fun l => prefixOf n l.name) with
    | nil => simp [resolveLong, hf, hfil] at h
    | cons l₀ rest =>
      by_cases hall : rest.all (·.target == l₀.target) = true
      · simp only [resolveLong, hf, hfil, hall, ↓reduceIte, Except.ok.injEq] at h
        subst h
        have hm : l₀ ∈ ls.filter (fun l => prefixOf n l.name) := by rw [hfil]; simp
        have hm' := List.mem_filter.1 hm
        refine ⟨hm'.1, .inr ⟨hm'.2, hne, ?_⟩⟩
        intro l' hl' hp
        have : l' ∈ l₀ :: rest := by rw [← hfil]; exact List.mem_filter.2 ⟨hl', hp⟩
        rcases List.mem_cons.1 this with rfl | hr
        · rfl
        · have := List.all_eq_true.1 hall l' hr
          simpa using this
      · simp [resolveLong, hf, hfil, hall] at h

theorem resolveLong_unique {ls : List Long} {n : String} {l : Long} (hl : l ∈ ls)
    (hp : prefixOf n l.name = true)
    (hu : ∀ l' ∈ ls, prefixOf n l'.name = true → l'.target = l.target) :
    ∃ l', resolveLong ls n = .ok l' ∧ l'.target = l.target := by
  cases hf : ls.find? (·.name == n) with
  | some l₀ =>
    have he : l₀.name = n := by simpa using List.find?_some hf
    refine ⟨l₀, resolveLong_exact hf, hu l₀ (List.mem_of_find?_eq_some hf) ?_⟩
    rw [he]; exact prefixOf_self n
  | none =>
    cases hfil : ls.filter (fun l => prefixOf n l.name) with
    | nil =>
      have : l ∈ ls.filter (fun l => prefixOf n l.name) := List.mem_filter.2 ⟨hl, hp⟩
      rw [hfil] at this; cases this
    | cons l₀ rest =>
      have hsub : ∀ x ∈ l₀ :: rest, x.target = l.target := by
        intro x hx
        rw [← hfil] at hx
        have := List.mem_filter.1 hx
        exact hu x this.1 this.2
      have hall : rest.all (·.target == l₀.target) = true := by
        refine List.all_eq_true.2 fun x hx => ?_
        have h1 := hsub x (List.mem_cons_of_mem _ hx)
        have h2 := hsub l₀ List.mem_cons_self
        simp [h1, h2]
      refine ⟨l₀, ?_, hsub l₀ List.mem_cons_self⟩
      simp [resolveLong, hf, hfil, hall]

/-! ## Tokens that keep the next token -/

theorem readW_false {t : Table} {tok : String} {a : List Char} {c : Bool} {x : Option String}
    {ps : List (String × Given)}
    (h : readW t tok a c x = .ok (ps, false)) :
    c = false ∧ Getopt.readLong t tok (String.ofList (splitEq a).1)
      ((splitEq a).2.map String.ofList) x = .ok (ps, false) := by
  unfold readW at h
  cases hl : Getopt.readLong t tok (String.ofList (splitEq a).1) ((splitEq a).2.map String.ofList)
      x with
  | error e => simp [hl, Except.map] at h
  | ok q =>
    obtain ⟨q1, q2⟩ := q
    simp only [hl, Except.map, Except.ok.injEq, Prod.mk.injEq, Bool.or_eq_false_iff] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem readLong_false {t : Table} {tok n : String} {v x x' : Option String}
    {ps : List (String × Given)} (h : Getopt.readLong t tok n v x = .ok (ps, false)) :
    Getopt.readLong t tok n v x' = .ok (ps, false) := by
  unfold Getopt.readLong at h ⊢
  cases hr : resolveLong t.longs n with
  | error cs =>
    rw [hr] at h
    cases cs <;> simp at h
  | ok l =>
    rw [hr] at h
    simp only at h ⊢
    cases ha : l.arg <;> cases v <;> cases x <;> simp_all

theorem readW_keep {t : Table} {tok : String} {a : List Char} {x x' : Option String}
    {ps : List (String × Given)} (h : readW t tok a false x = .ok (ps, false)) :
    readW t tok a false x' = .ok (ps, false) := by
  have hl := readLong_false (x' := x') (readW_false h).2
  unfold readW
  simp [hl, Except.map]

theorem readCluster_false {t : Table} {tok : String} {x x' : Option String} :
    ∀ {cs : List Char} {ps : List (String × Given)},
      Getopt.readCluster t tok x cs = .ok (ps, false) →
      Getopt.readCluster t tok x' cs = .ok (ps, false)
  | [], _, h => by simpa [Getopt.readCluster] using h
  | ch :: r, ps, h => by
    unfold Getopt.readCluster at h ⊢
    by_cases hw : (t.wLong && ch == 'W') = true
    · simp only [hw, ↓reduceIte] at h ⊢
      cases r with
      | nil =>
        cases x with
        | none => simp at h
        | some y =>
          dsimp only at h
          exact absurd (readW_false h).1 (by decide)
      | cons a b =>
        dsimp only at h ⊢
        exact readW_keep h
    · simp only [Bool.not_eq_true] at hw
      simp only [hw, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hf : findChar t ch with
      | none => simp [hf] at h
      | some s =>
        simp only [hf] at h ⊢
        cases ha : s.arg with
        | none =>
          simp only [ha] at h ⊢
          cases hr : Getopt.readCluster t tok x r with
          | error e => simp [hr, Except.map] at h
          | ok q =>
            obtain ⟨q1, q2⟩ := q
            simp only [hr, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have ih : Getopt.readCluster t tok x' r = .ok (q1, false) := readCluster_false hr
            simp [ih, Except.map]
        | optional => cases r <;> simpa [ha] using h
        | required =>
          cases r with
          | nil => cases x <;> simp [ha] at h
          | cons a b => simpa [ha] using h

theorem readLongOnly_false {t : Table} {tok : String} {x x' : Option String} {cs : List Char}
    {ps : List (String × Given)} (h : readLongOnly t tok x cs = .ok (ps, false)) :
    readLongOnly t tok x' cs = .ok (ps, false) := by
  unfold readLongOnly at h ⊢
  cases ho : oneShort t cs
  · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases hr : resolveLong t.longs (String.ofList (splitEq cs).1) with
    | error es =>
      cases es with
      | nil => simp only [hr] at h ⊢; exact readCluster_false h
      | cons e es => simp only [hr] at h ⊢; exact readLong_false h
    | ok l => simp only [hr] at h ⊢; exact readLong_false h
  · simp only [ho, ↓reduceIte] at h ⊢
    exact readCluster_false h

theorem readTok_false {t : Table} {tok : String} {x x' : Option String}
    {ps : List (String × Given)} (h : readTok t tok x = .ok (ps, false)) :
    readTok t tok x' = .ok (ps, false) := by
  unfold readTok at h ⊢
  split at h
  · exact readLong_false h
  · cases hl : t.longOnly
    · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact readCluster_false h
    · simp only [hl, ↓reduceIte] at h ⊢
      exact readLongOnly_false h
  · cases h

/-! ## Permutation -/

/-- Option occurrences and tokens in front of a reading. -/
def prepend (os : List (String × Given)) (fr : List String) (q : Parsed) : Parsed :=
  { q with opts := os ++ q.opts, front := fr ++ q.front }

theorem prepend_nil (q : Parsed) : prepend [] [] q = q := by
  cases q; rfl

theorem prepend_prepend (os os' : List (String × Given)) (fr fr' : List String)
    (q : Parsed) : prepend os fr (prepend os' fr' q) = prepend (os ++ os') (fr ++ fr') q := by
  simp [prepend]

theorem map_prepend_nil {ε : Type} (e : Except ε Parsed) : e.map (prepend [] []) = e := by
  cases e <;> simp [Except.map, prepend_nil]

theorem map_map_prepend {ε : Type} (e : Except ε Parsed) (os os' : List (String × Given))
    (fr fr' : List String) :
    (e.map (prepend os' fr')).map (prepend os fr) =
      e.map (prepend (os ++ os') (fr ++ fr')) := by
  cases e <;> simp [Except.map, prepend_prepend]

theorem classify_dashdash_eq {s : String} (h : classify s = .dashdash) : s = "--" := by
  unfold classify at h
  split at h
  · rename_i hs; exact String.toList_inj.1 (by simpa using hs)
  · split at h; cases h
  all_goals cases h

theorem classify_word_eq {s w : String} (h : classify s = .word w) : w = s := by
  unfold classify at h
  split at h
  · cases h
  · split at h; cases h
  · cases h; rfl
  · cases h
  · cases h; rfl

/-- The option front of a GNU reading reads the same in POSIX order, before anything. -/
theorem parse_front {t : Table} :
    ∀ {argv : List String} {p : Parsed}, parse t .permute argv = .ok p → ∀ ys : List String,
      parse t .requireOrder (p.front ++ ys) =
        (parse t .requireOrder ys).map (prepend p.opts p.front)
  | [], p, h, ys => by
    simp only [parse, Except.ok.injEq] at h; subst h
    simpa using (map_prepend_nil _).symm
  | tok :: rest, p, h, ys => by
    unfold parse at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h
      simpa using (map_prepend_nil _).symm
    · rename_i w hw
      simp only at h
      cases hr : parse t .permute rest with
      | error e => simp [hr, Except.map] at h
      | ok q =>
        simp only [hr, Except.map, Except.ok.injEq] at h
        subst h
        exact parse_front hr ys
    · rename_i hnd hnw
      split at h
      · cases h
      · rename_i ps hrd
        cases hr : parse t .permute rest with
        | error e => simp [hr, Except.map] at h
        | ok q =>
          simp only [hr, Except.map, Except.ok.injEq] at h
          subst h
          have ih := parse_front hr ys
          have hrd' := readTok_false (x' := (q.front ++ ys).head?) hrd
          show parse t .requireOrder (tok :: (q.front ++ ys)) = _
          rw [parse]
          split
          · rename_i hc; exact absurd hc (hnd)
          · rename_i w hc; exact absurd hc (hnw w)
          · rw [hrd']
            simp only
            rw [ih]
            cases parse t .requireOrder ys <;> simp [Except.map, prepend]
      · rename_i ps hrd
        cases rest with
        | nil => cases h
        | cons x rest' =>
          simp only at h
          cases hr : parse t .permute rest' with
          | error e => simp [hr, Except.map] at h
          | ok q =>
            simp only [hr, Except.map, Except.ok.injEq] at h
            subst h
            have ih := parse_front hr ys
            show parse t .requireOrder (tok :: x :: (q.front ++ ys)) = _
            rw [parse]
            split
            · rename_i hc; exact absurd hc (hnd)
            · rename_i w hc; exact absurd hc (hnw w)
            · simp only [List.head?_cons] at hrd ⊢
              rw [hrd]
              simp only
              rw [ih]
              cases parse t .requireOrder ys <;> simp [Except.map, prepend]

/-- Without `--`, the operands of a GNU reading are words. -/
theorem parse_operands {t : Table} :
    ∀ {argv : List String} {p : Parsed}, parse t .permute argv = .ok p → p.dashdash = false →
      ∀ w ∈ p.operands, classify w = .word w
  | [], p, h, _ => by
    simp only [parse, Except.ok.injEq] at h; subst h; simp
  | tok :: rest, p, h, hd => by
    unfold parse at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; simp at hd
    · rename_i w hw
      simp only at h
      cases hr : parse t .permute rest with
      | error e => simp [hr, Except.map] at h
      | ok q =>
        simp only [hr, Except.map, Except.ok.injEq] at h
        subst h
        intro u hu
        rcases List.mem_cons.1 hu with h1 | hu
        · subst h1; have := classify_word_eq hw; subst this; exact hw
        · exact parse_operands (p := q) hr hd u hu
    · split at h
      · cases h
      · cases hr : parse t .permute rest with
        | error e => simp [hr, Except.map] at h
        | ok q =>
          simp only [hr, Except.map, Except.ok.injEq] at h
          subst h
          exact parse_operands (p := q) hr hd
      · cases rest with
        | nil => cases h
        | cons x rest' =>
          simp only at h
          cases hr : parse t .permute rest' with
          | error e => simp [hr, Except.map] at h
          | ok q =>
            simp only [hr, Except.map, Except.ok.injEq] at h
            subst h
            exact parse_operands (p := q) hr hd

/-- The operands after the front, in POSIX order. -/
theorem parse_tail {t : Table} {argv : List String} {p : Parsed}
    (h : parse t .permute argv = .ok p) :
    parse t .requireOrder (if p.dashdash then "--" :: p.operands else p.operands) =
      .ok { operands := p.operands, dashdash := p.dashdash } := by
  cases hd : p.dashdash
  · have hw := parse_operands h hd
    cases ho : p.operands with
    | nil => simp [parse]
    | cons w ws =>
      have : classify w = .word w := hw w (by simp [ho])
      simp [parse, this]
  · simp [parse, classify]

/-- **Permutation**: the GNU reading of an argument vector is the POSIX reading of the
permuted vector (the option tokens first). -/
theorem parse_permuted {t : Table} {argv : List String} {p : Parsed}
    (h : parse t .permute argv = .ok p) : parse t .requireOrder p.permuted = .ok p := by
  unfold Parsed.permuted
  rw [parse_front h, parse_tail h]
  cases p; simp [Except.map, prepend]

end Silmaril.Proofs.Cli.Getopt
