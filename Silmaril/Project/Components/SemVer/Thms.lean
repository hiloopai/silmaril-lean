module

public import Silmaril.Project.Components.SemVer.Defs
public import Silmaril.Wasm.Wit.Text.Thms
public import Silmaril.Wasm.Wit.Elab.Thms

/-!
# Registry references and SemVer precedence: theorems

PROVED:

* **Precedence is a strict order** (`prec_irrefl`, `prec_trans`, `prec_asymm`), total on
  keys (`prec_trichotomy`), and ignores build metadata (`key_build`). `precLe_iff_not_prec`:
  `PrecLe` is the complement of the converse.
* The precedence chain of SemVer 2.0.0 §11 (`semver_example_chain`, kernel evaluation):
  `1.0.0-alpha < 1.0.0-alpha.1 < 1.0.0-alpha.beta < 1.0.0-beta < 1.0.0-beta.2 < 1.0.0-beta.11
  < 1.0.0-rc.1 < 1.0.0`, and `1.0.0 < 2.0.0 < 2.1.0 < 2.1.1`.
* **Compatibility** is symmetric and transitive (`compatible_symm`, `compatible_trans`) and
  reflexive on release versions (`compatible_refl`); on `0.2` it is "major `0`, minor `2`, no
  pre-release" (`compatible_zero_two`). `Upgrade` is reflexive and transitive
  (`upgrade_refl`, `upgrade_trans`).
* **Parsing inverts printing**: `parseVersion?_str` (valid versions), `parseRef?_refOf` and
  `Release.ofRef?_ref` (valid package names); `parseRef?_valid`: what `parseRef?` returns is
  valid.
* The pilot's versions: `0.2.6` precedes `0.2.12` and they are compatible
  (`v0_2_6_upgrade`), while the strings compare the other way, character by character
  (`str_lt_but_prec`).

A Silmaril addition.
-/

@[expose] public section
namespace Silmaril.Project.Components.SemVer

open Silmaril.Wasm Silmaril.Project.Components

/-! ## Precedence -/

theorem prec_irrefl (a : Wit.Version) : ¬ Prec a a := lt_irrefl (key a)

theorem prec_trans {a b c : Wit.Version} (h₁ : Prec a b) (h₂ : Prec b c) : Prec a c :=
  lt_trans h₁ h₂

theorem prec_asymm {a b : Wit.Version} (h : Prec a b) : ¬ Prec b a := lt_asymm h

/-- Any two versions are ordered, or have the same precedence (the same key). -/
theorem prec_trichotomy (a b : Wit.Version) : Prec a b ∨ key a = key b ∨ Prec b a :=
  lt_trichotomy (key a) (key b)

theorem precLe_iff_not_prec (a b : Wit.Version) : PrecLe a b ↔ ¬ Prec b a := not_lt.symm

/-- Build metadata does not affect precedence. -/
theorem key_build (v : Wit.Version) (b : List String) : key { v with build := b } = key v := rfl

/-- `Prec` along the patch number, for release versions with one major and minor version. -/
theorem prec_of_patch {a b : Wit.Version} (hM : a.major = b.major) (hm : a.minor = b.minor)
    (ha : a.pre = []) (hb : b.pre = []) (hp : a.patch < b.patch) : Prec a b := by
  simp [Prec, key, preKeys, Prod.Lex.toLex_lt_toLex, hM, hm, ha, hb, hp]

/-- A version of a literal: `v a b c pre`. -/
abbrev ver (a b c : Nat) (pre : List String := []) : Wit.Version := ⟨a, b, c, pre, []⟩

/-- **The precedence example of SemVer 2.0.0 §11.** -/
theorem semver_example_chain :
    Prec (ver 1 0 0 ["alpha"]) (ver 1 0 0 ["alpha", "1"]) ∧
    Prec (ver 1 0 0 ["alpha", "1"]) (ver 1 0 0 ["alpha", "beta"]) ∧
    Prec (ver 1 0 0 ["alpha", "beta"]) (ver 1 0 0 ["beta"]) ∧
    Prec (ver 1 0 0 ["beta"]) (ver 1 0 0 ["beta", "2"]) ∧
    Prec (ver 1 0 0 ["beta", "2"]) (ver 1 0 0 ["beta", "11"]) ∧
    Prec (ver 1 0 0 ["beta", "11"]) (ver 1 0 0 ["rc", "1"]) ∧
    Prec (ver 1 0 0 ["rc", "1"]) (ver 1 0 0) ∧
    Prec (ver 1 0 0) (ver 2 0 0) ∧ Prec (ver 2 0 0) (ver 2 1 0) ∧ Prec (ver 2 1 0) (ver 2 1 1) := by
  decide

/-! ## Compatibility -/

theorem compatible_symm {a b : Wit.Version} (h : Compatible a b) : Compatible b a :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem compatible_trans {a b c : Wit.Version} (h₁ : Compatible a b) (h₂ : Compatible b c) :
    Compatible a c :=
  ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩

theorem compatible_refl {a : Wit.Version} (h : a.pre = []) : Compatible a a := ⟨h, h, rfl⟩

/-- On the `0.2` track: major `0`, minor `2`, no pre-release. -/
theorem compatible_zero_two {a : Wit.Version} (b : Wit.Version) (hM : a.major = 0)
    (hm : a.minor = 2) (ha : a.pre = []) :
    Compatible a b ↔ b.major = 0 ∧ b.minor = 2 ∧ b.pre = [] := by
  unfold Compatible track
  by_cases hb : b.major = 0
  · by_cases hb' : b.minor = 0
    · simp [hM, hm, ha, hb, hb']
    · simp [hM, hm, ha, hb, hb', eq_comm, and_comm]
  · simp [hM, hm, ha, hb]

theorem upgrade_refl {a : Wit.Version} (h : a.pre = []) : Upgrade a a :=
  ⟨compatible_refl h, le_refl (key a)⟩

theorem upgrade_trans {a b c : Wit.Version} (h₁ : Upgrade a b) (h₂ : Upgrade b c) : Upgrade a c :=
  ⟨compatible_trans h₁.1 h₂.1, le_trans h₁.2 h₂.2⟩

/-! ## Parsing -/

/-- **Parsing a printed valid version gives it back.** -/
theorem parseVersion?_str {v : Wit.Version} (hv : v.Valid) : parseVersion? v.str = some v := by
  unfold parseVersion?
  rw [Wit.Elab.Version.str_toList]
  exact Wit.Text.parseVer_verChars v (Wit.Text.verOk_of_valid hv)

/-- A character of a word is a letter or a digit. -/
theorem word_char {w : List Char} (hw : Wit.Word w) {c : Char} (hc : c ∈ w) :
    c.isLower ∨ c.isUpper ∨ c.isDigit := by
  cases w with
  | nil => exact hw.elim
  | cons d ds =>
    rcases List.mem_cons.1 hc with rfl | hc
    · rcases hw with h | h
      · exact .inl h.1
      · exact .inr (.inl h.1)
    · rcases hw with h | h
      · rcases h.2 c hc with h' | h'
        · exact .inl h'
        · exact .inr (.inr h')
      · rcases h.2 c hc with h' | h'
        · exact .inr (.inl h')
        · exact .inr (.inr h')

/-- A character not `-` lies in a word of `splitDash`. -/
theorem mem_splitDash {c : Char} : ∀ {l : List Char}, c ∈ l → c ≠ '-' →
    ∃ w ∈ Wit.splitDash l, c ∈ w
  | [], h, _ => absurd h List.not_mem_nil
  | d :: ds, h, hc => by
    unfold Wit.splitDash
    by_cases hd : d = '-'
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd hd hc
      · obtain ⟨w, hw, hcw⟩ := mem_splitDash h hc
        exact ⟨w, List.mem_cons_of_mem _ hw, hcw⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
      exact mem_splitDash_cons hd h hc
where
  mem_splitDash_cons {d : Char} {ds : List Char} (hd : ¬ d = '-') (h : c ∈ d :: ds) (hc : c ≠ '-') :
      ∃ w ∈ (match Wit.splitDash ds with
        | w :: ws => (d :: w) :: ws
        | [] => [[d]]), c ∈ w := by
    rcases hs : Wit.splitDash ds with _ | ⟨w, ws⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨[c], List.mem_singleton_self _, List.mem_singleton_self _⟩
      · obtain ⟨w', hw', _⟩ := mem_splitDash h hc
        rw [hs] at hw'
        exact absurd hw' List.not_mem_nil
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨c :: w, List.mem_cons_self, List.mem_cons_self⟩
      · obtain ⟨w', hw', hcw⟩ := mem_splitDash h hc
        rw [hs] at hw'
        rcases List.mem_cons.1 hw' with rfl | hw'
        · exact ⟨d :: w', List.mem_cons_self, List.mem_cons_of_mem _ hcw⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', hcw⟩

/-- A character of a valid identifier is a letter, a digit or `-`. -/
theorem validId_char {s : String} (hs : Wit.ValidId s) {c : Char} (hc : c ∈ s.toList) :
    c = '-' ∨ c.isLower ∨ c.isUpper ∨ c.isDigit := by
  by_cases hd : c = '-'
  · exact .inl hd
  · obtain ⟨w, hw, hcw⟩ := mem_splitDash hc hd
    exact .inr (word_char (hs w hw) hcw)

theorem colon_not_mem {s : String} (hs : Wit.ValidId s) : ':' ∉ s.toList := fun h => by
  rcases validId_char hs h with h | h | h | h <;> revert h <;> decide

theorem at_not_mem {s : String} (hs : Wit.ValidId s) : '@' ∉ s.toList := fun h => by
  rcases validId_char hs h with h | h | h | h <;> revert h <;> decide

theorem splitFirst_none {c : Char} : ∀ {xs : List Char}, c ∉ xs →
    Wit.Text.Parse.splitFirst c xs = (xs, none)
  | [], _ => rfl
  | d :: ds, h => by
    have hd : d ≠ c := fun e => h (e ▸ List.mem_cons_self)
    have ih := splitFirst_none (c := c) (xs := ds) (fun h' => h (List.mem_cons_of_mem _ h'))
    simp [Wit.Text.Parse.splitFirst, hd, ih]

theorem splitFirst_append {c : Char} (ys : List Char) : ∀ {xs : List Char}, c ∉ xs →
    Wit.Text.Parse.splitFirst c (xs ++ c :: ys) = (xs, some ys)
  | [], _ => by simp [Wit.Text.Parse.splitFirst]
  | d :: ds, h => by
    have hd : d ≠ c := fun e => h (e ▸ List.mem_cons_self)
    have ih := splitFirst_append (c := c) ys (xs := ds) (fun h' => h (List.mem_cons_of_mem _ h'))
    simp [Wit.Text.Parse.splitFirst, hd, ih]

/-- The characters of `refOf p` are split back into its parts. -/
theorem parseRefChars_refOf {p : Wit.PackageName} (hp : p.Valid) :
    parseRefChars (refOf p).toList = some p := by
  obtain ⟨ns, name, v⟩ := p
  have hns := colon_not_mem hp.1
  have hname := at_not_mem hp.2.1
  cases v with
  | none =>
    simp only [refOf, String.toList_append]
    simp [parseRefChars, splitFirst_append _ hns, splitFirst_none hname]
  | some v =>
    have hv : Wit.Text.Parse.parseVer v.str.toList = some v := parseVersion?_str (hp.2.2 v rfl)
    simp only [refOf, String.toList_append]
    simp [parseRefChars, splitFirst_append _ hns, splitFirst_append _ hname, hv]

/-- **The parser inverts the printer on valid package names.** -/
theorem parseRef?_refOf {p : Wit.PackageName} (hp : p.Valid) : parseRef? (refOf p) = some p := by
  simp [parseRef?, parseRefChars_refOf hp, hp]

/-- `Release.ref` is `refOf` of the package. -/
theorem release_ref_eq (r : Release) : r.ref = refOf r.pkg := rfl

/-- **A release is read back from its reference and digest.** -/
theorem Release.ofRef?_ref {r : Release} (hp : r.pkg.Valid) : releaseOfRef? r.ref r.digest = some r := by
  simp [releaseOfRef?, release_ref_eq, parseRef?_refOf hp]

/-- What `parseRef?` returns is a valid package name. -/
theorem parseRef?_valid {s : String} {p : Wit.PackageName} (h : parseRef? s = some p) : p.Valid := by
  unfold parseRef? at h
  cases hq : parseRefChars s.toList with
  | none => rw [hq] at h; cases h
  | some q =>
    rw [hq] at h
    by_cases hv : q.Valid
    · simp only [Option.bind_some, hv, ite_true, Option.some.injEq] at h
      exact h ▸ hv
    · simp [hv] at h

/-! ## The pilot's versions -/

/-- **`0.2.12` is a compatible upgrade of `0.2.6`**, and strictly newer. -/
theorem v0_2_6_upgrade : Upgrade (ver 0 2 6) (ver 0 2 12) ∧ Prec (ver 0 2 6) (ver 0 2 12) := by
  decide

/-- **String order is not precedence**: `"0.2.12" < "0.2.6"` character by character, but `0.2.6` precedes
`0.2.12`, and both strings parse to these versions. -/
theorem str_lt_but_prec : ("0.2.12" : String).toList < ("0.2.6" : String).toList ∧
    parseVersion? "0.2.6" = some (ver 0 2 6) ∧ parseVersion? "0.2.12" = some (ver 0 2 12) ∧
    Prec (ver 0 2 6) (ver 0 2 12) := by
  decide

/-- `wasi:io@0.2.12` read from its reference. -/
theorem parseRef?_wasi_io : parseRef? "wasi:io@0.2.12" = some ⟨"wasi", "io", some (ver 0 2 12)⟩ := by
  decide

end Silmaril.Project.Components.SemVer

end
