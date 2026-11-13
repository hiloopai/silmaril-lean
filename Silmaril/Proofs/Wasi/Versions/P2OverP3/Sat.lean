module

public import Silmaril.Proofs.Wasi.Versions.P2OverP3.Main

/-!
# Proofs: the invariant method for WASI 0.2 over 0.3

`wp_call`: every export call preserves the invariant `J` and returns an answer the loose 0.2
theory accepts, under the WASI 0.3 clock theory `clockTh3`. `wpInv`, then `p2OverP3_sat`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3 (clockTh3 clockStep3 ClockSt now3)

/-- The step of the loose 0.2 theory on an answer of `now`. -/
theorem p2_step_now (io : IoSt) {g : Option (BitVec 64)} (a : List Val) {x : BitVec 64}
    (hg : g.all (fun l => decide (l ≤ x)) = true) :
    (p2Th .loose).step (io, g, (), ()) (.imp clockNow a (some [.u64 x])) =
      some (ioUpd io (ioOp clockNow) a (some [.u64 x]), some x, (), ()) := by
  have hop : ioOp clockNow = .other := by decide
  have hfs : fsOk (.imp clockNow a (some [.u64 x])) = true := by
    unfold fsOk
    dsimp only
    repeat rw [ite_eq_right (by decide)]
  simp [p2Th, Protocol.prod, ioTh, ioStep, hop, ansOk, clockTh, clockStep, nowStep, hg, pointwise,
    p2Ok, cliOk_now, fsTyped, hfs]

/-- The `now` call keeps the invariant. -/
theorem wp_now (cap : Nat) (s : St) (qT : ClockSt) (g : Option (BitVec 64)) (a : List Val)
    (hg : ClkLe g qT.last) :
    Wp clockTh3 ((prog cap s clockNow a).bind fun x =>
        .pure (⟨ioUpd s.io (ioOp clockNow) a x.2, x.1⟩, x.2))
      (fun x qT' => ∃ qG', (p2Th .loose).step (s.io, g, (), ()) (.imp clockNow a x.2) = some qG' ∧
        J x.1 qT' qG') qT := by
  rw [prog_now]
  intro n qT' hn
  obtain ⟨x, rfl, hle, hlast⟩ := now3_step (a := []) hn
  have hgx : g.all (fun l => decide (l ≤ x)) = true := by
    cases g with
    | none => rfl
    | some l =>
      obtain ⟨y, hy, hly⟩ := hg l rfl
      have hqy : qT.last = some y := hy
      rw [hqy] at hle
      simpa using BitVec.le_trans hly (by simpa using hle)
  refine ⟨_, p2_step_now s.io a hgx, rfl, fun z hz => ⟨x, hlast, ?_⟩⟩
  have hzx : z = x := (Option.some.inj hz).symm
  exact hzx ▸ BitVec.le_refl _

/-- The answers of the program, in the 0.2 theory (other than `now`). -/
theorem prog_good (cap : Nat) (s : St) (f : FnName) (a : List Val) :
    Leaves (prog cap s f a) fun x =>
      ansOk .loose s.io (ioOp f) a x.2 = true ∧ p2Ok (.imp f a x.2) = true := by
  by_cases hop : ioOp f = .other
  · refine (prog_other cap s f a hop).mono fun x hx => ⟨?_, ?_⟩
    · rw [hop]; rfl
    · simp [p2Ok, hop, hx]
  · exact (prog_io cap s f a hop).mono fun x hx => ⟨hx, by simp [p2Ok, hop]⟩

/-- **Every export call keeps the invariant**, under the WASI 0.3 clock theory. -/
theorem wp_call (cap : Nat) (s : St) (qT : ClockSt) (qG : P2St) (q : (nsig exp2).Op)
    (hJ : J s qT qG) :
    Wp clockTh3 (body cap s q) (fun x qT' => ∃ qG', (p2Th .loose).step qG
      (.imp q.1.1 q.2 x.2) = some qG' ∧ J x.1 qT' qG') qT := by
  obtain ⟨⟨f, hf⟩, a⟩ := q
  obtain ⟨io, g, ⟨⟩, ⟨⟩⟩ := qG
  obtain ⟨hio, hclk⟩ := hJ
  have hio' : io = s.io := hio
  subst hio'
  unfold body
  by_cases hnow : f = clockNow
  · subst hnow
    exact wp_now cap s qT g a hclk
  · rw [Wp.bind]
    refine Wp.of_leaves (R := fun q => ClkLe g q.last) (fun _ _ _ hq hs => clkLe_step hq hs)
      (fun x q hR hx => ⟨_, p2_step s.io g hx.1 hx.2 (fsOk_of_mem hf a x.2) hnow, rfl, hR⟩)
      _ (prog_good cap s f a) hclk

/-- **The invariant method applies.** -/
theorem wpInv (cap : Nat) : WpInv (body cap) St.init clockTh3 (p2Th .loose) J where
  init := ⟨rfl, fun _ h => nomatch h⟩
  call := fun s qT qG q hJ => wp_call cap s qT qG q hJ

/-- **WASI 0.2 over 0.3 satisfies the loose 0.2 theory under the 0.3 clock theory.** -/
theorem p2OverP3_sat (cap : Nat) :
    (agP clockTh3 (retG (p2Th .loose))).holds (p2OverP3 cap) :=
  ag_of_wpInv (wpInv cap)

end Silmaril.Wasi.Versions.P2OverP3
