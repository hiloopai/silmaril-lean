module

public import Silmaril.Net.WebTransport.ErrorCode.Defs

/-!
# WebTransport application error codes: proofs

For `Silmaril.Net.WebTransport.ErrorCode.Thms` (draft-ietf-webtrans-http3-17 §4.4). Every
proof is linear arithmetic with literal divisors (`omega`), using that `appFirst ≡ 0x21 + 1
(mod 0x1f)`: the grease code points of the range sit at offsets `≡ 30 (mod 31)`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.WebTransport.ErrorCode

open Silmaril.Net.Http3 Silmaril.Net.WebTransport

theorem isGrease_iff (h : Nat) : isGrease h = true ↔ 0x21 ≤ h ∧ (h - 0x21) % 0x1f = 0 := by
  simp [isGrease]

theorem toHttp_range {n : Nat} (hn : AppCode n) : appFirst ≤ toHttp n ∧ toHttp n ≤ appLast := by
  unfold AppCode at hn
  unfold toHttp appFirst appLast
  omega

theorem toHttp_not_grease (n : Nat) : isGrease (toHttp n) = false := by
  apply Bool.eq_false_iff.2
  intro h
  rw [isGrease_iff] at h
  unfold toHttp appFirst at h
  omega

theorem ofHttp_toHttp {n : Nat} (hn : AppCode n) : ofHttp (toHttp n) = some n := by
  have hr := toHttp_range hn
  have hg := toHttp_not_grease n
  simp only [ofHttp, hr.1, hr.2, hg, decide_true, Bool.not_false, Bool.and_self, ↓reduceIte,
    Option.some.injEq]
  unfold toHttp appFirst
  omega

theorem ofHttp_some {h n : Nat} (hs : ofHttp h = some n) :
    appFirst ≤ h ∧ h ≤ appLast ∧ isGrease h = false ∧ AppCode n ∧ toHttp n = h := by
  unfold ofHttp at hs
  split at hs
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    simp only [Option.some.injEq] at hs
    subst hs
    have h3' : ¬ (0x21 ≤ h ∧ (h - 0x21) % 0x1f = 0) := by
      rw [← isGrease_iff, h3]; simp
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · unfold AppCode; unfold appFirst appLast at *; omega
    · unfold toHttp; unfold appFirst appLast at *; omega
  · cases hs

theorem ofHttp_none_iff (h : Nat) : ofHttp h = none ↔ isAppRange h = false := by
  unfold ofHttp isAppRange
  split <;> simp_all

theorem isAppRange_iff (h : Nat) : isAppRange h = true ↔ ∃ n, AppCode n ∧ toHttp n = h := by
  constructor
  · intro hr
    cases hs : ofHttp h with
    | none => rw [ofHttp_none_iff] at hs; rw [hs] at hr; cases hr
    | some n => obtain ⟨-, -, -, hn, he⟩ := ofHttp_some hs; exact ⟨n, hn, he⟩
  · rintro ⟨n, hn, rfl⟩
    have hr := toHttp_range hn
    simp [isAppRange, hr.1, hr.2, toHttp_not_grease]

theorem toHttp_injective {m n : Nat} (h : toHttp m = toHttp n) : m = n := by
  unfold toHttp at h; omega

theorem toHttp_lt {m n : Nat} (h : m < n) : toHttp m < toHttp n := by
  unfold toHttp; omega

end Silmaril.Proofs.Net.WebTransport.ErrorCode
