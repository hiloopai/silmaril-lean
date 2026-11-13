module

public import Silmaril.Proofs.Wasm.JcoTool.KRead.Lift
public import Silmaril.Proofs.Wasm.JcoTool.KRead.Obs

/-!
# The observation of a generated module on Core is the model's

* `prel_init`: the start of the model pipe and the Core pipe from a store holding the
  instantiated module (`Inst0`) are related.
* `core_whole_iff`, `core_part_iff` (for injective `hb`, given `NoTrapAt k N`): the Core pipe and the model pipe have the same whole outputs and the same
  outputs so far. For outputs so far, both directions of the simulation are used: a point after
  which the Core sink never changes is one after which the model sink never changes, and back.
* `core_whole_correct`: every finished Core pipe holds `(trV k).run xs` (`KDrop.kdrop_pipe_correct`).
* `core_reads`, `core_game`: given that the model pipe reads as `trV k`, the Core observation reads as
  `trV k`, so its strategy reading is `StreamGame.den (trV k)`.
-/

public section

namespace Silmaril.Proofs.Wasm.JcoTool.KRead

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core (Store ModuleInst)
open Silmaril.Wasm.Numerics (Profile GrowKind)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.JcoTool.KRead
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (BI Prog MS Mode trV)
open Silmaril.Wasm.JcoTool.KDrop (DRStep genD)
open Silmaril.Wasm.Component.Streams.Kernel (KM)

variable {H : Type} {hb : BI → H} {ma : Nat}

theorem prel_init {xs : List Val} {k : KM} {N : Nat} {mi : ModuleInst} {a : Nat} {cs₀ : Store H}
    (h0 : Inst0 hb ma a k N mi cs₀) :
    PRel hb ma mi a (genD k N) (PSys.init xs k (m₀ k)) (PSys.init xs k (cs₀, none, .ready)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, h0.1, h0.2⟩

section
variable (hinj : Function.Injective hb) {k : KM} {N : Nat} (hn : NoTrapAt k N)
  (o : GrowKind → Nat → Nat → Nat → Bool) (hN : 0 < N ∧ N ≤ 256)
  {mi : ModuleInst} {a : Nat} {cs₀ : Store H} (h0 : Inst0 hb ma a k N mi cs₀)
include hinj hn hN h0

/-- **The whole outputs of the Core pipe are the model's.** -/
theorem core_whole_iff (xs ys : List Val) :
    (coreObs (Profile.deterministic o) hb ma a k cs₀).whole xs ys ↔ (dropObs k N).whole xs ys := by
  constructor
  · rintro ⟨d, hd, hb', hg⟩
    obtain ⟨c, hc, hr⟩ := bwd_steps hinj hn o hN .refl (prel_init h0) hd
    exact ⟨c, hc, hr.snk ▸ hb', hr.snk ▸ hg⟩
  · rintro ⟨c, hc, hb', hg⟩
    obtain ⟨d, hd, hr⟩ := fwd_steps (Profile.deterministic o) hN (ri_init xs k) hc (prel_init h0)
    exact ⟨d, hd, hr.snk ▸ hb', hr.snk ▸ hg⟩

/-- **The outputs so far of the Core pipe are the model's.** -/
theorem core_part_iff (xs ys : List Val) :
    (coreObs (Profile.deterministic o) hb ma a k cs₀).part xs ys ↔ (dropObs k N).part xs ys := by
  constructor
  · rintro ⟨d, hd, hq, hg⟩
    obtain ⟨c, hc, hr⟩ := bwd_steps hinj hn o hN .refl (prel_init h0) hd
    refine ⟨c, hc, fun c' hc' => ?_, hr.snk ▸ hg⟩
    obtain ⟨d', hd', hr'⟩ := fwd_steps (Profile.deterministic o) hN
      (ri_steps hN (ri_init xs k) hc) hc' hr
    rw [← hr'.snk, ← hr.snk]
    exact hq d' hd'
  · rintro ⟨c, hc, hq, hg⟩
    obtain ⟨d, hd, hr⟩ := fwd_steps (Profile.deterministic o) hN (ri_init xs k) hc (prel_init h0)
    refine ⟨d, hd, fun d' hd' => ?_, hr.snk ▸ hg⟩
    obtain ⟨c', hc', hr'⟩ := bwd_steps hinj hn o hN hc hr hd'
    rw [hr'.snk, hr.snk]
    exact hq c' hc'

/-- **Every finished Core pipe holds the kernel's whole output.** -/
theorem core_whole_correct {xs ys : List Val}
    (h : (coreObs (Profile.deterministic o) hb ma a k cs₀).whole xs ys) : ys = (trV k).run xs := by
  obtain ⟨c, hc, ⟨b, hb'⟩, hg⟩ := (core_whole_iff hinj hn o hN h0 xs ys).1 h
  rw [← hg]
  exact Silmaril.Wasm.JcoTool.KDrop.kdrop_pipe_correct (fun _ => hN) (psteps_kreach hc)
    ((kof_snk (k := k) c).symm ▸ hb')

/-- With liveness, **the Core observation reads as the kernel's transformer**. -/
theorem core_reads (hr : (dropObs k N).Reads (trV k)) :
    (coreObs (Profile.deterministic o) hb ma a k cs₀).Reads (trV k) := fun xs ys => by
  rw [core_whole_iff hinj hn o hN h0, core_part_iff hinj hn o hN h0]
  exact hr xs ys

/-- **The game reading of the Core runtime is the stream game of the kernel.** -/
theorem core_game (hr : (dropObs k N).Reads (trV k)) :
    (coreObs (Profile.deterministic o) hb ma a k cs₀).game =
      Silmaril.Wasm.Component.Algebra.StreamGame.den (trV k) :=
  game_eq_den (core_reads hinj hn o hN h0 hr)

end

end Silmaril.Proofs.Wasm.JcoTool.KRead
