module

public import Silmaril.Proofs.Wasi.Versions.P3OverP2.Refute

/-!
# Proofs: the corrected read theory is a weakening

`fsReadTh3w F` differs from `fsReadTh3 F` in two places: calls that are not well shaped
(`rdShaped`) are not constrained, and a read of `0` items may complete with `0`. Each step of
`rdStep` that accepts is a step of `rdStepZ` (`rdStepZ_of_rdStep`), and an accepting step of
`rdStep` on an ill-shaped call keeps the state (`rdStep_unshaped`), so every run accepted by
`fsReadTh3 F` is accepted by `fsReadTh3w F` (`fsReadTh3w_of`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P3OverP2

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3

variable (F : BitVec 32 → List (BitVec 8))

set_option linter.unusedTactic false in
/-- `stream.read`: an accepting step of `rdStep` is a step of `rdStepZ`. -/
theorem rdStepZ_of_read (q : RdSt) (a : List Val) (r : Option (List Val)) (q1 : RdSt)
    (h : rdStep F q (.imp cStreamRead a r) = some q1) :
    rdStepZ F q (.imp cStreamRead a r) = some q1 := by
  have hne : ¬ cStreamRead = readVia3 := by decide
  simp only [rdStep, rdStepZ, hne, ↓reduceIte] at h ⊢
  match a, r with
  | [rv, nv], some [pv, items] =>
    dsimp only at h ⊢
    rcases hb : (natOf rv >>= rest q) with _ | bs <;> rcases hn : natOf nv with _ | n <;>
      rcases hc : (natOf pv >>= copyOf) with _ | (_ | ⟨c, k⟩) <;> simp only [hb, hn, hc] at h ⊢
    all_goals first
      | exact h
      | (cases c <;> (try cases k) <;> (try dsimp only at h ⊢) <;> first
          | exact h
          | (split_ifs at h with hk
             simp only [hk.1, hk.2.1, hk.2.2, true_or, and_self, ↓reduceIte]
             exact h))
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => exact h
  | [_, _], none | [_, _], some [] | [_, _], some [_] | [_, _], some (_ :: _ :: _ :: _) => exact h

/-- **Every accepting step of `rdStep` is a step of `rdStepZ`.** -/
theorem rdStepZ_of_rdStep (q : RdSt) (e : WEv) (q1 : RdSt) (h : rdStep F q e = some q1) :
    rdStepZ F q e = some q1 := by
  cases e with
  | imp f a r =>
    by_cases h1 : f = readVia3
    · subst h1
      exact h
    · by_cases h2 : f = cStreamRead
      · subst h2
        exact rdStepZ_of_read F q a r q1 h
      · simp only [rdStep, rdStepZ, h1, h2, ↓reduceIte] at h ⊢
        exact h
  | _ => exact h

/-- `rdStep` rejects an ill-shaped `read-via-stream`. -/
theorem rdStep_readVia_unshaped (q : RdSt) (a : List Val) (r : Option (List Val)) (q1 : RdSt)
    (hsh : rdShaped (.imp readVia3 a r) = false) : rdStep F q (.imp readVia3 a r) ≠ some q1 := by
  intro h
  simp only [rdStep, ↓reduceIte] at h
  split at h
  · simp [rdShaped] at hsh
  · cases h

/-- An ill-shaped `stream.read` that `rdStep` accepts keeps the state. -/
theorem rdStep_read_unshaped (q : RdSt) (a : List Val) (r : Option (List Val)) (q1 : RdSt)
    (hsh : rdShaped (.imp cStreamRead a r) = false) (h : rdStep F q (.imp cStreamRead a r) = some q1) :
    q1 = q := by
  have hne : ¬ cStreamRead = readVia3 := by decide
  simp only [rdStep, hne, ↓reduceIte] at h
  split at h
  · rename_i rv nv pv items
    have hn : natOf nv = none := by simpa [rdShaped, hne] using hsh
    rw [hn] at h
    split at h <;> simp_all
  · exact (Option.some.inj h).symm

/-- **An accepting step of `rdStep` on an ill-shaped call keeps the state.** -/
theorem rdStep_unshaped (q : RdSt) (e : WEv) (q1 : RdSt) (hsh : rdShaped e = false)
    (h : rdStep F q e = some q1) : q1 = q := by
  cases e with
  | imp f a r =>
    by_cases h1 : f = readVia3
    · subst h1
      exact absurd h (rdStep_readVia_unshaped F q a r q1 hsh)
    · by_cases h2 : f = cStreamRead
      · subst h2
        exact rdStep_read_unshaped F q a r q1 hsh h
      · simp [rdShaped, h1, h2] at hsh
  | _ => simp [rdShaped] at hsh

/-- **The corrected read theory is a weakening**: every run accepted by `fsReadTh3 F` is
accepted by `fsReadTh3w F`. -/
theorem fsReadTh3w_of {t : List WEv} (h : (fsReadTh3 F).Accepts t) : (fsReadTh3w F).Accepts t := by
  refine accepts_sim (A := fsReadTh3 F) (B := fsReadTh3w F) (fun q q' => q = q') rfl
    (fun q q' e q1 hR hs => ⟨q1, ?_, rfl⟩) h
  subst hR
  change rdStep F q e = some q1 at hs
  show (if rdShaped e then rdStepZ F q e else some q) = some q1
  cases hsh : rdShaped e
  · rw [rdStep_unshaped F q e q1 hsh hs]
    rfl
  · exact rdStepZ_of_rdStep F q e q1 hs

end Silmaril.Wasi.Versions.P3OverP2
