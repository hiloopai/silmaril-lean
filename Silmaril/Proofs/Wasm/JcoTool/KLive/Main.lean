module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Net

/-!
# Liveness of networks with generated modules

* `mprogress`: no deadlock before every node has finished and every module has exited.
* `mexec_done`: every maximal execution reaches such a system and stays there (termination,
  `Term.no_infinite_mrun`, with progress).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (Network NSt RV OS Out rh wh NStep Node Reach Sys)
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Proofs.Wasm.JcoTool.KNet
open Silmaril.Proofs.Wasm.Component.Streams.Net (Inv)
open Silmaril.Proofs.Wasm.JcoTool.KDrop (relD_live)
open Silmaril.Proofs.Wasm.Component.Streams.Live (Setting)

/-- **The context of a reachable system.** -/
theorem mctx {M : MNet} (hL : M.Live) {m : MSys M.net} (h : MReach M m) :
    ∃ s, Reach M.net s ∧ Ctx M m s := by
  obtain ⟨s, hR, hA, hB⟩ := mreach_rb hL.ok h
  exact ⟨s, hR, ⟨hL.ok, hL.topo, hL.fits, hA,
    Silmaril.Proofs.Wasm.Component.Streams.Net.reach_inv hL.ok.wf hR,
    Silmaril.Proofs.Wasm.Component.Streams.Live.reach_pos hR, hB,
    Silmaril.Wasm.JcoTool.KGame.mreach_good hL.ok h⟩⟩

theorem not_finished_out {σ : Type} {x : NSt σ} {o : OS} {a : List Val} (ho : x.outs = [⟨o, a⟩])
    (hnc : ∀ d, o ≠ .closed d) : ¬ x.Finished := by
  intro hf
  obtain ⟨d, hd⟩ := hf.2 ⟨o, a⟩ (by rw [ho]; exact List.mem_singleton_self _)
  exact hnc d hd

/-- A running module's node has not finished. -/
theorem not_finished_live {r w ws : Nat} {ms : MS} {x : NSt KSt} (hR : RelD r w ws ms x)
    (hex : ms.mode ≠ .exited) : ¬ x.Finished := by
  obtain ⟨-, hL⟩ := relD_live hR hex
  have hc : ∀ (o : OS), outIs x o → (∀ d, o ≠ .closed d) → ¬ x.Finished := fun o ⟨a, ha⟩ hnc =>
    not_finished_out ha hnc
  rcases hL with ⟨-, -, -, -, -, -, hout⟩ | ⟨-, -, -, -, -, -, -, hout⟩ | ⟨-, -, -, -, hout⟩ |
    ⟨-, -, -, -, hout⟩ | ⟨-, -, hout, -⟩ | ⟨-, -, hout, -, -⟩ | ⟨-, -, -, hout | hout⟩ | ⟨-, -, -, hout⟩
  all_goals exact hc _ hout (by intro d h; cases h)

/-- If every node of the abstraction has finished, every node of the system has and every module
has exited. -/
theorem mdone_of {M : MNet} {m : MSys M.net} {s : Sys M.net} (hA : Abs M m s)
    (hf : ∀ i, (s.ns i).Finished) : MDone M m := by
  intro i
  refine ⟨fun hg => (hA.2 i).1 hg ▸ hf i, fun hg => ?_⟩
  obtain ⟨⟨k, N⟩, hkN⟩ := Option.ne_none_iff_exists'.1 hg
  obtain ⟨c, c', hn, hR⟩ := (hA.2 i).2 k N hkN
  obtain ⟨hy1, -, hy3, -⟩ := cast_fields hn (s.ns i)
  by_contra hex
  apply not_finished_live hR hex
  obtain ⟨⟨b, hb⟩, ho⟩ := hf i
  exact ⟨⟨b, hy1 ▸ hb⟩, fun o hmem => ho o (hy3 ▸ hmem)⟩

/-- **Progress**: a reachable system that is not done can step. -/
theorem mprogress {M : MNet} (hL : M.Live) {m : MSys M.net} (h : MReach M m) (hnd : ¬ MDone M m) :
    MEnabled M m := by
  obtain ⟨s, -, hC⟩ := mctx hL h
  have hex : ∃ i, ¬ (s.ns i).Finished := by
    by_contra hall
    exact hnd (mdone_of hC.abs (fun i => by by_contra hi; exact hall ⟨i, hi⟩))
  obtain ⟨i, hi⟩ := hex
  exact mprog_main hC _ i rfl hi

/-- The setting of a live network. -/
theorem live_setting {M : MNet} (hL : M.Live) : ∃ L, Setting M.net L := by
  obtain ⟨L, hc⟩ := hL.spec
  exact ⟨L, ⟨hL.ok.wf, hL.topo, hc⟩⟩

/-- **Liveness under every scheduler**: every maximal execution reaches a system where every node
has finished and every module has exited, and stays there. -/
theorem mexec_done {M : MNet} (hL : M.Live) {r : Nat → MSys M.net} (hr : MExec M r) :
    ∃ n, ∀ j, n ≤ j → r j = r n ∧ MDone M (r n) := by
  obtain ⟨L, S⟩ := live_setting hL
  have hreach : ∀ n, MReach M (r n) := by
    intro n
    induction n with
    | zero => rw [hr.1]; exact MSteps.refl _
    | succ n ih =>
      rcases hr.2 n with h | ⟨-, he⟩
      · exact MSteps.tail ih h
      · rw [he]; exact ih
  have hstop : ∃ n, ¬ MStep M (r n) (r (n + 1)) := by
    by_contra hall
    exact no_infinite_mrun hL.ok S r (hreach 0) (fun n => by
      by_contra hn
      exact hall ⟨n, hn⟩)
  obtain ⟨n, hn⟩ := hstop
  have hdis : ¬ MEnabled M (r n) ∧ r (n + 1) = r n := (hr.2 n).resolve_left hn
  have hstay : ∀ j, n ≤ j → r j = r n := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih =>
      rcases hr.2 j with h | ⟨-, he⟩
      · have h' : MStep M (r n) (r (j + 1)) := ih ▸ h
        exact absurd ⟨_, h'⟩ hdis.1
      · rw [he, ih]
  refine ⟨n, fun j hj => ⟨hstay j hj, ?_⟩⟩
  by_contra hnd
  exact hdis.1 (mprogress hL (hreach n) hnd)

end Silmaril.Proofs.Wasm.JcoTool.KLive
