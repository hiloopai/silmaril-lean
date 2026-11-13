module

public import Silmaril.Wasm.Wac.Names.Defs

/-!
# WAC extern names: properties and wac's own test vectors

The test vectors of `alternate_lookup_key` in wac `5a7480c`
(`crates/wac-types/src/names.rs`, test `alternate_lookup_key`) and the
`find_matching_interface_name` examples of `LANGUAGE.md`, checked by `decide`.

* `compat_iff`, `compat_trans`: semver compatibility is an equivalence (equal names, or
  the same track), which the merging of implicit imports relies on.
* `readVersion_noLeadingZero`: an accepted version has numeric identifiers without
  leading zeros; `version_rejects` checks the rejections of the `semver` crate.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac

theorem compat_refl (a : String) : compat a a = true := by simp [compat]

theorem compat_comm (a b : String) : compat a b = compat b a := by
  unfold compat
  have e : ∀ x y : String, (x == y) = (y == x) := fun x y => by
    by_cases h : x = y
    · subst h; rfl
    · have h' : ¬ y = x := fun h'' => h h''.symm
      rw [beq_false_of_ne h, beq_false_of_ne h']
  cases ha : altKey a <;> cases hb : altKey b <;> simp only [e a b] <;> simp only [e]

theorem compat_iff (a b : String) :
    compat a b = true ↔ a = b ∨ ∃ x, altKey a = some x ∧ altKey b = some x := by
  unfold compat
  cases ha : altKey a <;> cases hb : altKey b <;> simp
  exact or_congr Iff.rfl eq_comm

theorem compat_trans {a b c : String} (h1 : compat a b = true) (h2 : compat b c = true) :
    compat a c = true := by
  rw [compat_iff] at *
  rcases h1 with rfl | ⟨x, hx, hb⟩
  · exact h2
  · rcases h2 with rfl | ⟨y, hy, hc⟩
    · exact .inr ⟨x, hx, hb⟩
    · rw [hb] at hy
      exact .inr ⟨x, hx, (Option.some.inj hy) ▸ hc⟩

theorem verGt_irrefl (a : String) : verGt a a = false := by
  unfold verGt
  cases verOf a with
  | none => rfl
  | some x =>
    obtain ⟨p, q, r⟩ := x
    simp [verLt]

/-- A numeric identifier of two or more digits does not start with `0`. -/
theorem numOk_noLeadingZero {c d : Char} {ds : List Char} (h : numOk (c :: d :: ds) = true) :
    c ≠ '0' := by
  rintro rfl
  simp [numOk] at h

/-- **Accepted versions have no leading zeros** (the `semver` crate's numeric
identifiers). -/
theorem readVersion_noLeadingZero {v ma mi pa : List Char}
    (h : readVersion v = some (ma, mi, pa)) : numOk ma = true ∧ numOk mi = true ∧ numOk pa = true := by
  unfold readVersion at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (obtain ⟨rfl, rfl, rfl⟩ := h; simp_all)

theorem tail_examples :
    tail "foo:bar/baz" = some "baz" ∧ tail "wasi:io/outgoing-stream@0.2.0" = some "outgoing-stream" ∧
    tail "a:b/c/d" = some "d" ∧ tail "baz" = none := by decide

theorem altKey_examples :
    altKey "x" = none ∧ altKey "x:y/z" = none ∧
    altKey "x:y/z@1.0.0" = some "x:y/z@1" ∧ altKey "x:y/z@1.1.0" = some "x:y/z@1" ∧
    altKey "x:y/z@1.1.2" = some "x:y/z@1" ∧ altKey "x:y/z@2.1.2" = some "x:y/z@2" ∧
    altKey "x:y/z@2.1.2+abc" = some "x:y/z@2" ∧ altKey "x:y/z@0.1.2" = some "x:y/z@0.1" ∧
    altKey "x:y/z@0.1.3" = some "x:y/z@0.1" ∧ altKey "x:y/z@0.2.3" = some "x:y/z@0.2" ∧
    altKey "x:y/z@0.2.3+abc" = some "x:y/z@0.2" ∧ altKey "x:y/z@0.0.1" = none ∧
    altKey "x:y/z@0.0.1-pre" = none ∧ altKey "x:y/z@0.1.0-pre" = none ∧
    altKey "x:y/z@1.0.0-pre" = none := by decide

theorem compat_examples :
    compat "a:b/c@0.2.0" "a:b/c@0.2.1" = true ∧ compat "a:b/c@0.2.0" "a:b/c@0.3.0" = false ∧
    compat "a:b/c@1.0.0" "a:b/c@1.4.0" = true ∧ compat "a:b/c" "a:b/c@1.0.0" = false := by decide

/-- Versions the `semver` crate rejects are on no track: leading zeros, an empty or
invalid build identifier, a missing component. -/
theorem version_rejects :
    altKey "x:y/z@01.0.0" = none ∧ altKey "x:y/z@1.01.0" = none ∧ altKey "x:y/z@0.1.00" = none ∧
    altKey "x:y/z@1.0.0+" = none ∧ altKey "x:y/z@1.0.0+a..b" = none ∧ altKey "x:y/z@1.0.0+a_b" = none ∧
    altKey "x:y/z@1.0" = none ∧ altKey "x:y/z@18446744073709551616.0.0" = none ∧
    altKey "x:y/z@18446744073709551615.0.0" = some "x:y/z@18446744073709551615" ∧
    altKey "x:y/z@10.0.0" = some "x:y/z@10" ∧ altKey "x:y/z@1.0.0+001.b-c" = some "x:y/z@1" ∧
    compat "a:b/c@01.0.0" "a:b/c@1.0.0" = false := by decide

theorem verGt_examples :
    verGt "a:b/c@0.2.1" "a:b/c@0.2.0" = true ∧ verGt "a:b/c@0.2.0" "a:b/c@0.2.1" = false ∧
    verGt "a:b/c@1.10.0" "a:b/c@1.9.3" = true ∧ verGt "a:b/c@1.0.0+b" "a:b/c@1.0.0" = false := by decide

end Silmaril.Wasm.Wac
