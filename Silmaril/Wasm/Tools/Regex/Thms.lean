module

public import Silmaril.Wasm.Tools.Regex.Defs

/-!
# Regular expressions: the derivative matcher decides the language

* inversion lemmas for `Re.Matches`;
* `nullable_iff`: `nullable` decides the empty word; `mkSeq_iff`, `mkAlt_iff`: the smart
  constructors keep the language;
* **`deriv_iff`**: `deriv c r` matches `w` iff `r` matches `c :: w` (Brzozowski);
* **`matchList_iff`**: `matchList r w = true ↔ Matches r w`;
* `anyStar_matches`: `anyStar` matches every word;
* **`search_iff`**: `Pattern.search p s` holds iff `p.re` matches a factor of `s`, which is a
  prefix when `p` starts with `^` and a suffix when it ends with `$` (`is_match`).

New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Regex

namespace Re

theorem zero_inv {w : List Char} (h : Matches .zero w) : False := nomatch h

theorem eps_inv {w : List Char} (h : Matches .eps w) : w = [] := by cases h; rfl

theorem chr_inv {s : CharSet} {w : List Char} (h : Matches (.chr s) w) :
    ∃ c, w = [c] ∧ s.mem c = true := by
  cases h with
  | chr hc => exact ⟨_, rfl, hc⟩

theorem seq_inv {a b : Re} {w : List Char} (h : Matches (.seq a b) w) :
    ∃ u v, w = u ++ v ∧ Matches a u ∧ Matches b v := by
  cases h with
  | seq ha hb => exact ⟨_, _, rfl, ha, hb⟩

theorem alt_inv {a b : Re} {w : List Char} (h : Matches (.alt a b) w) :
    Matches a w ∨ Matches b w := by
  cases h with
  | altL h => exact .inl h
  | altR h => exact .inr h

theorem seq_iff {a b : Re} {w : List Char} :
    Matches (.seq a b) w ↔ ∃ u v, w = u ++ v ∧ Matches a u ∧ Matches b v :=
  ⟨seq_inv, fun ⟨_, _, h, ha, hb⟩ => h ▸ .seq ha hb⟩

theorem alt_iff {a b : Re} {w : List Char} : Matches (.alt a b) w ↔ Matches a w ∨ Matches b w :=
  ⟨alt_inv, fun h => h.elim .altL .altR⟩

/-- A non-empty word in a star: a first non-empty piece and the rest. -/
theorem star_cons_inv {a : Re} {c : Char} {w : List Char} (h : Matches (.star a) (c :: w)) :
    ∃ u v, w = u ++ v ∧ Matches a (c :: u) ∧ Matches (.star a) v := by
  generalize hx : c :: w = x at h
  generalize hr : Re.star a = r at h
  induction h generalizing c w with
  | starNil => cases hx
  | @starCons a' u v ha hs _ ih =>
    cases hr
    cases u with
    | nil => exact ih hx rfl
    | cons d u =>
      simp only [List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨u, v, rfl, ha, hs⟩
  | _ => cases hr

theorem nullable_iff (r : Re) : r.nullable = true ↔ Matches r [] := by
  induction r with
  | zero => exact ⟨fun h => (by cases h), fun h => (zero_inv h).elim⟩
  | eps => exact ⟨fun _ => .eps, fun _ => rfl⟩
  | chr s =>
    refine ⟨fun h => (by cases h), fun h => ?_⟩
    obtain ⟨c, hc, -⟩ := chr_inv h
    cases hc
  | seq a b iha ihb =>
    show (a.nullable && b.nullable) = true ↔ _
    rw [Bool.and_eq_true, iha, ihb, seq_iff]
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨[], [], rfl, ha, hb⟩
    · rintro ⟨u, v, huv, ha, hb⟩
      have hnil : u = [] ∧ v = [] := List.append_eq_nil_iff.mp huv.symm
      exact ⟨hnil.1 ▸ ha, hnil.2 ▸ hb⟩
  | alt a b iha ihb =>
    show (a.nullable || b.nullable) = true ↔ _
    rw [Bool.or_eq_true, iha, ihb, alt_iff]
  | star a _ => exact ⟨fun _ => .starNil, fun _ => rfl⟩

theorem mkSeq_iff (a b : Re) (w : List Char) : Matches (mkSeq a b) w ↔ Matches (.seq a b) w := by
  unfold mkSeq
  split
  · exact ⟨fun h => (zero_inv h).elim, fun h => by
      obtain ⟨_, _, _, ha, _⟩ := seq_inv h
      exact (zero_inv ha).elim⟩
  · exact ⟨fun h => (zero_inv h).elim, fun h => by
      obtain ⟨_, _, _, _, hb⟩ := seq_inv h
      exact (zero_inv hb).elim⟩
  · rw [seq_iff]
    refine ⟨fun h => ⟨[], w, rfl, .eps, h⟩, fun ⟨u, v, huv, hu, hv⟩ => ?_⟩
    rw [eps_inv hu] at huv
    simpa [huv] using hv
  · rw [seq_iff]
    refine ⟨fun h => ⟨w, [], by simp, h, .eps⟩, fun ⟨u, v, huv, hu, hv⟩ => ?_⟩
    rw [eps_inv hv] at huv
    simpa [huv] using hu
  · exact Iff.rfl

theorem mkAlt_iff (a b : Re) (w : List Char) : Matches (mkAlt a b) w ↔ Matches (.alt a b) w := by
  unfold mkAlt
  split
  · rw [alt_iff]
    exact ⟨Or.inr, fun h => h.elim (fun h => (zero_inv h).elim) id⟩
  · rw [alt_iff]
    exact ⟨Or.inl, fun h => h.elim id (fun h => (zero_inv h).elim)⟩
  · split
    · rename_i hab
      subst hab
      rw [alt_iff]
      exact ⟨Or.inl, fun h => h.elim id id⟩
    · exact Iff.rfl

/-- The derivative of a concatenation. -/
theorem deriv_seq_iff {a b : Re} {c : Char} {w : List Char}
    (iha : ∀ w, Matches (a.deriv c) w ↔ Matches a (c :: w))
    (ihb : ∀ w, Matches (b.deriv c) w ↔ Matches b (c :: w)) :
    Matches ((Re.seq a b).deriv c) w ↔ Matches (.seq a b) (c :: w) := by
  have hstep : Matches (mkSeq (a.deriv c) b) w ↔ ∃ u v, w = u ++ v ∧ Matches a (c :: u) ∧
      Matches b v := by
    rw [mkSeq_iff, seq_iff]
    exact exists_congr fun u => exists_congr fun v => by rw [iha]
  have hsplit : Matches (.seq a b) (c :: w) ↔ (Matches a [] ∧ Matches b (c :: w)) ∨
      ∃ u v, w = u ++ v ∧ Matches a (c :: u) ∧ Matches b v := by
    rw [seq_iff]
    constructor
    · rintro ⟨u, v, huv, ha, hb⟩
      cases u with
      | nil => exact .inl ⟨ha, by simpa using huv ▸ hb⟩
      | cons d u =>
        simp only [List.cons_append, List.cons.injEq] at huv
        obtain ⟨rfl, rfl⟩ := huv
        exact .inr ⟨u, v, rfl, ha, hb⟩
    · rintro (⟨ha, hb⟩ | ⟨u, v, rfl, ha, hb⟩)
      · exact ⟨[], c :: w, rfl, ha, hb⟩
      · exact ⟨c :: u, v, rfl, ha, hb⟩
  show Matches (if a.nullable then mkAlt (mkSeq (a.deriv c) b) (b.deriv c)
    else mkSeq (a.deriv c) b) w ↔ _
  rw [hsplit]
  by_cases hn : a.nullable = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hn), mkAlt_iff, alt_iff, hstep, ihb]
    have ha : Matches a [] := (nullable_iff a).mp hn
    exact ⟨fun h => h.elim .inr (fun hb => .inl ⟨ha, hb⟩), fun h => h.elim (fun h => .inr h.2) .inl⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hn), hstep]
    have ha : ¬ Matches a [] := fun h => hn ((nullable_iff a).mpr h)
    exact ⟨.inr, fun h => h.elim (fun h => (ha h.1).elim) id⟩

/-- **Brzozowski**: the derivative by `c` matches `w` iff the expression matches `c :: w`. -/
theorem deriv_iff (c : Char) (r : Re) (w : List Char) :
    Matches (r.deriv c) w ↔ Matches r (c :: w) := by
  induction r generalizing w with
  | zero => exact ⟨fun h => (zero_inv h).elim, fun h => (zero_inv h).elim⟩
  | eps => exact ⟨fun h => (zero_inv h).elim, fun h => by cases eps_inv h⟩
  | chr s =>
    show Matches (if s.mem c then .eps else .zero) w ↔ _
    by_cases hc : s.mem c = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      refine ⟨fun h => by rw [eps_inv h]; exact .chr hc, fun h => ?_⟩
      obtain ⟨d, hd, -⟩ := chr_inv h
      have hw : w = [] := (List.cons.inj hd).2
      exact hw ▸ .eps
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      refine ⟨fun h => (zero_inv h).elim, fun h => ?_⟩
      obtain ⟨d, hd, hm⟩ := chr_inv h
      have hcd : c = d := (List.cons.inj hd).1
      exact (hc (hcd ▸ hm)).elim
  | seq a b iha ihb => exact deriv_seq_iff iha ihb
  | alt a b iha ihb =>
    show Matches (mkAlt (a.deriv c) (b.deriv c)) w ↔ _
    rw [mkAlt_iff, alt_iff, alt_iff, iha, ihb]
  | star a iha =>
    show Matches (mkSeq (a.deriv c) (.star a)) w ↔ _
    rw [mkSeq_iff, seq_iff]
    constructor
    · rintro ⟨u, v, hw, ha, hs⟩
      have hm : Matches (.star a) ((c :: u) ++ v) := .starCons ((iha u).mp ha) hs
      exact hw ▸ hm
    · intro h
      obtain ⟨u, v, hw, ha, hs⟩ := star_cons_inv h
      have hd : Matches (a.deriv c) u := (iha u).mpr ha
      exact ⟨u, v, hw, hd, hs⟩

/-- **The matcher decides the language.** -/
theorem matchList_iff (r : Re) (w : List Char) : r.matchList w = true ↔ Matches r w := by
  induction w generalizing r with
  | nil => exact nullable_iff r
  | cons c w ih =>
    show (r.deriv c).matchList w = true ↔ _
    rw [ih, deriv_iff]

end Re

theorem anyStar_matches (w : List Char) : Re.Matches anyStar w := by
  induction w with
  | nil => exact .starNil
  | cons c w ih => exact .starCons (u := [c]) (.chr rfl) ih

theorem anyL_iff {r : Re} {w : List Char} :
    Re.Matches (.seq anyStar r) w ↔ ∃ pre mid, w = pre ++ mid ∧ Re.Matches r mid := by
  rw [Re.seq_iff]
  exact ⟨fun ⟨pre, mid, hw, _, hm⟩ => ⟨pre, mid, hw, hm⟩,
    fun ⟨pre, mid, hw, hm⟩ => ⟨pre, mid, hw, anyStar_matches _, hm⟩⟩

theorem anyR_iff {r : Re} {w : List Char} :
    Re.Matches (.seq r anyStar) w ↔ ∃ mid suf, w = mid ++ suf ∧ Re.Matches r mid := by
  rw [Re.seq_iff]
  exact ⟨fun ⟨mid, suf, hw, hm, _⟩ => ⟨mid, suf, hw, hm⟩,
    fun ⟨mid, suf, hw, hm⟩ => ⟨mid, suf, hw, hm, anyStar_matches _⟩⟩

/-- **`is_match`**: the pattern matches a factor of the string, a prefix under `^` and a suffix
under `$`. -/
theorem search_iff (p : Pattern) (s : String) :
    p.search s = true ↔ ∃ pre mid suf, s.toList = pre ++ mid ++ suf ∧ Re.Matches p.re mid ∧
      (p.startAnchor = true → pre = []) ∧ (p.endAnchor = true → suf = []) := by
  unfold Pattern.search
  rw [Re.matchList_iff]
  cases hs : p.startAnchor <;> cases he : p.endAnchor
  · show Re.Matches (.seq (.seq anyStar p.re) anyStar) s.toList ↔ _
    rw [anyR_iff]
    constructor
    · rintro ⟨x, suf, hw, hx⟩
      obtain ⟨pre, mid, hx', hm⟩ := anyL_iff.mp hx
      have hw' : s.toList = pre ++ mid ++ suf := hx' ▸ hw
      exact ⟨pre, mid, suf, hw', hm, nofun, nofun⟩
    · rintro ⟨pre, mid, suf, hw, hm, -, -⟩
      exact ⟨pre ++ mid, suf, hw, anyL_iff.mpr ⟨pre, mid, rfl, hm⟩⟩
  · show Re.Matches (.seq anyStar p.re) s.toList ↔ _
    rw [anyL_iff]
    constructor
    · rintro ⟨pre, mid, hw, hm⟩
      exact ⟨pre, mid, [], by simpa using hw, hm, nofun, fun _ => rfl⟩
    · rintro ⟨pre, mid, suf, hw, hm, -, hsuf⟩
      have hw' : s.toList = pre ++ mid := by simpa [hsuf rfl] using hw
      exact ⟨pre, mid, hw', hm⟩
  · show Re.Matches (.seq p.re anyStar) s.toList ↔ _
    rw [anyR_iff]
    constructor
    · rintro ⟨mid, suf, hw, hm⟩
      exact ⟨[], mid, suf, by simpa using hw, hm, fun _ => rfl, nofun⟩
    · rintro ⟨pre, mid, suf, hw, hm, hpre, -⟩
      have hw' : s.toList = mid ++ suf := by simpa [hpre rfl] using hw
      exact ⟨mid, suf, hw', hm⟩
  · show Re.Matches p.re s.toList ↔ _
    constructor
    · intro hm
      exact ⟨[], s.toList, [], by simp, hm, fun _ => rfl, fun _ => rfl⟩
    · rintro ⟨pre, mid, suf, hw, hm, hpre, hsuf⟩
      have hw' : s.toList = mid := by simpa [hpre rfl, hsuf rfl] using hw
      exact hw' ▸ hm

end Silmaril.Wasm.Tools.Regex
