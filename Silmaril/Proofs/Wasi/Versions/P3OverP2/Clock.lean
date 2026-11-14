module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Typed

/-!
# Proofs: WASI 0.3 over 0.2 satisfies the saturated clock theory

The component keeps the state of `clockTh3s` itself (`St.clk`) and clamps `now`
(`clampNow`): `clock_sat` holds for every theory of the 0.2 host. Invariant: the component's
clock state is the theory's, and the owed bound is at most `2^64 - 1`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3

variable {ST : Type}

/-- The clock invariant. -/
def ClockJ (s : St) (q : ClockSt) : Prop := s.clk = q ∧ q.lb ≤ u64Max

/-- Functions other than `now` and `wait-for` leave the clock theory. -/
theorem clockStep3s_other {f : FnName} (h1 : f ≠ now3) (h2 : f ≠ waitFor3) (q : ClockSt)
    (a : List Val) (r : Option (List Val)) : clockTh3s.step q (.imp f a r) = some q := by
  simp [clockTh3s, clockStep3s, h1, h2]

/-- A `u64` is at most `2^64 - 1`. -/
theorem toNat_le_u64Max (x : BitVec 64) : x.toNat ≤ u64Max := by
  have := x.isLt; simp only [u64Max]; omega

/-- **The clamped `now` is accepted.** -/
theorem clock_now {q : ClockSt} (hq : q.lb ≤ u64Max) (a : List Val) (x : Nat) :
    clockTh3s.step q (.imp now3 a (some [.u64 (finNow q x).2])) = some (finNow q x).1 := by
  have hv : (BitVec.ofNat 64 (clampNow q x)).toNat = clampNow q x := by
    have : clampNow q x ≤ u64Max := Nat.min_le_left _ _
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp only [u64Max] at this; omega)
  have hlast : q.last.elim 0 BitVec.toNat ≤ u64Max := by
    cases q.last with
    | none => simp [Option.elim, u64Max]
    | some l => simpa [Option.elim] using toNat_le_u64Max l
  have hlb : q.lb ≤ clampNow q x := by
    simp only [clampNow]; omega
  have hl : q.last.all (fun l => decide (l ≤ BitVec.ofNat 64 (clampNow q x))) = true := by
    cases hql : q.last with
    | none => rfl
    | some l =>
      have : l.toNat ≤ clampNow q x := by
        have h0 : q.last.elim 0 BitVec.toNat = l.toNat := by simp [hql]
        simp only [clampNow]; omega
      simp [BitVec.le_def, hv, this]
  simp only [clockTh3s, clockStep3s, ↓reduceIte]
  split
  · rfl
  · rename_i h; exact absurd ⟨hl, by simp only [finNow]; rw [hv]; exact hlb⟩ h

/-- The clock part of a call: the theory accepts the answer, the invariant is kept. -/
theorem wp_clock (T : Protocol ST WEv) (s : St) (q : (nsig p3World.imports).Op) (qT : ST)
    (qG : ClockSt) (hJ : ClockJ s qG) :
    Wp T (body s q) (fun a _ => ∃ qG', clockTh3s.step qG (.imp q.1.1 q.2 a.2) = some qG' ∧
      ClockJ a.1 qG') qT := by
  obtain ⟨rfl, hlb⟩ := hJ
  obtain ⟨⟨f, hf⟩, a⟩ := q
  obtain ⟨c, hc, hne, rfl⟩ := cls_cases hf
  cases c <;> simp only [body, hc, thenFin]
  case waitFor =>
    refine wp_fin' T _ _ (fun d _ => ⟨finWaitFor s.clk a, ?_, rfl, ?_⟩) qT
    · simp only [clockTh3s, clockStep3s, Fn3.name, finWaitFor,
        show (waitFor3 = now3) = False from eq_false (by decide), ite_false, ite_true]
      split <;> simp_all
    · simp only [finWaitFor]; split <;> simp_all [u64Max]
  all_goals
    first
    | exact absurd rfl hne
    | (simp only [Wp]; exact ⟨_, clockStep3s_other (by decide) (by decide) _ _ _, rfl, hlb⟩)
    | (refine wp_fin' T _ _ (fun d _ => ?_) qT
       first
       | exact ⟨_, clockStep3s_other (by decide) (by decide) _ _ _, rfl, hlb⟩
       | exact ⟨_, clock_now hlb _ _, rfl, Nat.zero_le _⟩)

/-- **The component satisfies the saturated clock theory**, for every theory of the 0.2 host. -/
theorem clock_sat (T : Protocol ST WEv) :
    (agP T (retG clockTh3s)).holds p3OverP2 :=
  ag_of_wpInv (J := fun s _ q => ClockJ s q)
    ⟨⟨rfl, Nat.zero_le _⟩, fun s qT qG q hJ => wp_clock T s q qT qG hJ⟩

end Silmaril.Wasi.Versions.P3OverP2
