module

public import Silmaril.Net.Http.Qvalue.Defs

/-! Proofs for `Silmaril.Net.Http.Qvalue.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Net.Http.Qvalue

open Silmaril.Net.Http.Qvalue

theorem digit?_lt {b : UInt8} {x : Nat} (h : digit? b = some x) : x < 10 := by
  unfold digit? at h
  by_cases hd : Silmaril.Net.Http.Abnf.isDigit b = true
  · simp only [hd, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp only [Silmaril.Net.Http.Abnf.isDigit, Silmaril.Net.Http.Abnf.inRange,
      decide_eq_true_eq] at hd
    have h1 : b.toNat ≤ 0x39 := hd.2
    omega
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h

theorem thousandths_le {ds : List UInt8} {q : Nat} (h : thousandths ds = some q) : q ≤ 999 := by
  match ds, h with
  | [], h => simp only [thousandths, Option.some.injEq] at h; omega
  | [a], h =>
    simp only [thousandths, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    have := digit?_lt hx; omega
  | [a, b], h =>
    simp only [thousandths, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    have := digit?_lt hx; have := digit?_lt hy; omega
  | [a, b, c], h =>
    simp only [thousandths, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    have := digit?_lt hx; have := digit?_lt hy; have := digit?_lt hz; omega
  | _ :: _ :: _ :: _ :: _, h => simp only [thousandths, reduceCtorEq] at h

theorem parseQvalue_le {v : List UInt8} {q : Nat} (h : parseQvalue v = some q) : q ≤ 1000 := by
  unfold parseQvalue at h
  split at h
  · cases h; omega
  · cases h; omega
  · exact Nat.le_trans (thousandths_le h) (by omega)
  · split at h
    · cases h; omega
    · cases h
  · cases h

end Silmaril.Proofs.Net.Http.Qvalue
