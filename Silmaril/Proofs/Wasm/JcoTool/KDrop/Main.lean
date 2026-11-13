module

public import Silmaril.Proofs.Wasm.JcoTool.KDrop.Writes

/-!
# The generated module refines the `Net` node program

`step_sim`: every step of the callback runtime from a machine related to a node state is a step
of the node program (`NStep`) to a related state, or a step that changes neither the store nor
the node (`WR` resuming). `init_rel`: the machine after the lift is related to the node's
initial state.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KDrop

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (NSt OS RV Node NStep rh wh)
open Silmaril.Wasm.Component.Streams.Kernel (KExp KStmt KM KSt)

theorem no_step_exited {k : KM} {N : Nat} {st st' : DStore} {ms ms' : MS} (hm : ms.mode = .exited)
    (h : DRStep (genD k N) st ms st' ms') : False := by
  cases h with
  | ready hr _ => rw [hm] at hr; cases hr
  | event hw _ _ _ => rw [hm] at hw; cases hw

theorem relD_live {r w s : Nat} {ms : MS} {x : NSt KSt} (hR : RelD r w s ms x)
    (hex : ¬ ms.mode = .exited) : okD ms r w s ∧ RelL r s ms x := by
  unfold RelD at hR
  rwa [ite_eq_right hex] at hR

/-- **The simulation**: a step of the generated module is a step of the `Net` node, or changes
neither the store nor the node. -/
theorem step_sim {k : KM} {N c c' s : Nat} (hN : 0 < N ∧ N ≤ 256) (hs : s < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt KSt} (hR : RelD (rh c) (wh c') s ms x)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧ (NStep (node k c c') s st x st' x' ∨ (st' = st ∧ x' = x)) := by
  by_cases hex : ms.mode = .exited
  · exact (no_step_exited hex h).elim
  have hR' : okD ms (rh c) (wh c') s ∧ RelL (rh c) s ms x := relD_live hR hex
  obtain ⟨hok, hL⟩ := hR'
  rcases hL with ⟨hm, hpc, hk, h0, hoff, hrd, hout⟩ | ⟨hm, hpc, hk, h0, hoff, hrp, hrd, hout⟩ |
    ⟨hm, hpc, -, -, hout⟩ | ⟨hm, hpc, hk, hrd, hout⟩ | ⟨hm, hpc, hout, hnr⟩ |
    ⟨hm, hpc, hout, hnr, hne⟩ | ⟨hm, hpc, hrd, hout⟩ | ⟨hm, hpc, hrd, hout⟩
  · obtain ⟨x', h1, h2⟩ := sim_rd hN hs hok hm hpc hk h0 hoff hrd hout h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_wtr hs hok hm hpc hk h0 hoff hrp hrd hout h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_wtrd hok hm hpc hout h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_eoi hok hm hpc hk hrd hout h
    exact ⟨x', h1, .inl h2⟩
  · exact sim_wr hs hok hm hpc hout hnr h
  · obtain ⟨x', h1, h2⟩ := sim_wtw hs hok hm hpc hout hnr hne h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_cl hok hm hpc hrd hout h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_dead hok hm hpc hrd hout h
    exact ⟨x', h1, .inl h2⟩

/-- **The start**: the machine after the lift is related to the node's initial state. -/
theorem init_rel (k : KM) (c c' s : Nat) :
    RelD (rh c) (wh c') s (initMSD k (rh c) (wh c') s) (NSt.init (node k c c')) := by
  have hb : (initMSD k (rh c) (wh c') s).g BLEN = 0 := by
    simp [initMSD, initG, upd_apply, BLEN, GST, INSR, OUTSW, WS]
  have hkst : (initMSD k (rh c) (wh c') s).kst = (trV k).init := by
    simp only [MS.kst, hb, slice_zero]
    simp [initMSD, initG, upd_apply, GST, INSR, OUTSW, WS, trV, KM.tr, M32,
      Silmaril.Wasm.Component.Streams.Kernel.M32]
  refine relD_of (by simp [initMSD]) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (.inl ⟨rfl, ?_, hkst, ?_, ?_, rfl, [], rfl⟩)
  all_goals simp [initMSD, initG, upd_apply, INSR, OUTSW, WS, BLEN, OLEN, OOFF, PC, GST, CAP, pRD]

end Silmaril.Proofs.Wasm.JcoTool.KDrop
