module

public import Silmaril.Proofs.Wasm.JcoTool.KTee.Events
import Mathlib.Tactic.NormNum

/-!
# The generated tee refines the tee node

`step_sim`: every step of the callback runtime `DRStep (genT N)` from a machine related to a
state of `teeNode a b c` is a step `NStep` of the node to a related state, or changes neither
the store nor the node (`EXIT`, `WAIT`). `init_rel`: the machine after the lift is related to
the node's initial state.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KTee

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Event EventCode blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (NSt OS RV Node NStep rh wh status count)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KTee

theorem modeOf_one : modeOf 1 = some .ready := rfl

theorem modeOf_zero : modeOf 0 = some .exited := rfl

theorem waitCode_eval (t : St) {s : Nat} (hws : t.g WS = s) (hs : s < 2 ^ 28) :
    waitCode.eval t = 2 + 16 * s := by
  simp only [waitCode, E.eval, Bin.eval, hws]
  norm_num [M32]
  omega

theorem modeOf_wait (s : Nat) : modeOf (2 + 16 * s) = some (.waiting s) := by
  have h1 : (2 + 16 * s) % 16 = 2 := by omega
  have h2 : (2 + 16 * s) / 16 = s := by omega
  have h4 : ¬ 2 + 16 * s = 1 := by omega
  simp [modeOf, h1, h2, h4]

theorem ms_ready {ms' : MS} {s' : DSt} (h : modeOf 1 = some ms'.mode)
    (he : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩) : ms' = ⟨s'.g, s'.m, s'.rp, .ready⟩ := by
  rw [modeOf_one] at h
  rw [he, ← Option.some.inj h]

theorem no_step_exited {N : Nat} {st st' : DStore} {ms ms' : MS} (hm : ms.mode = .exited)
    (h : DRStep (genT N) st ms st' ms') : False := by
  cases h with
  | ready hr _ => rw [hm] at hr; cases hr
  | event hw _ _ _ => rw [hm] at hw; cases hw

/-- The conclusion of `step_sim`. -/
def SimOK (a b c s : Nat) (st st' : DStore) (ms' : MS) (x : NSt Unit) : Prop :=
  ∃ x', RelT (rh a) (wh b) (wh c) s ms' x' ∧
    (NStep (teeNode a b c) s st x st' x' ∨ (st' = st ∧ x' = x))

/-- An invocation that returned `YIELD` after one step of the node. -/
theorem simOK_yield {a b c s : Nat} {st : DStore} {ms' : MS} {x : NSt Unit} {s' : DSt} {v : Nat}
    (hmo : modeOf v = some ms'.mode) (hms : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩)
    (h : v = 1 ∧ ∃ x', RelT (rh a) (wh b) (wh c) s ⟨s'.g, s'.m, s'.rp, .ready⟩ x' ∧
      NStep (teeNode a b c) s st x s'.st x') : SimOK a b c s st s'.st ms' x := by
  obtain ⟨hv, x', hR', hn⟩ := h
  rw [hv] at hmo
  exact ⟨x', by rw [ms_ready hmo hms]; exact hR', .inl hn⟩

/-- The actions after `YIELD`. -/
theorem step_act {N a b c s : Nat} (hN : 0 < N ∧ N ≤ 256) {st : DStore} {ms ms' : MS}
    {x : NSt Unit} {s' : DSt} {v : Nat} (hR : RelT (rh a) (wh b) (wh c) s ms x)
    (hex : ms.mode ≠ .exited) (hmo : modeOf v = some ms'.mode) (hms : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩)
    (hx : dexec (readyT N) FUEL (inv ms [0, 0, 0] st) = some (.ret v, s'))
    (hstut : (ms.m aRS = 3 ∧ ms.m (aO 0) = 3 ∧ ms.m (aO 1) = 3 ∧ v = 0 ∧ s' = inv ms [0, 0, 0] st) ∨
      (v = waitCode.eval (inv ms [0, 0, 0] st).down ∧ s' = inv ms [0, 0, 0] st) →
      SimOK a b c s st s'.st ms' x) : SimOK a b c s st s'.st ms' x := by
  rcases readyT_ret hx with ⟨h1, h2, hx⟩ | ⟨h1, h2, hx⟩ | ⟨n0, n1, h1, h2, h3, -, hx⟩ |
    ⟨h1, hx⟩ | ⟨h1, h2, hx⟩ | ⟨h1, h2, hx⟩ | hs | hs
  · exact simOK_yield hmo hms (sim_actW (j := 0) (by omega) hR hex h1 h2 hx)
  · exact simOK_yield hmo hms (sim_actW (j := 1) (by omega) hR hex h1 h2 hx)
  · exact simOK_yield hmo hms (sim_actR hN hR hex n0 n1 h1 h2 h3 hx)
  · exact simOK_yield hmo hms (sim_actStop hR hex h1 hx)
  · exact simOK_yield hmo hms (sim_actClose (j := 0) (by omega) hR hex h1 h2 hx)
  · exact simOK_yield hmo hms (sim_actClose (j := 1) (by omega) hR hex h1 h2 hx)
  · exact hstut (.inl hs)
  · exact hstut (.inr hs)

/-- `EXIT` and `WAIT`: the node does not move. -/
theorem step_stutter {a b c s : Nat} (hs : s < 2 ^ 28) {st : DStore} {ms ms' : MS} {x : NSt Unit}
    {s' : DSt} {v : Nat} (hR : RelT (rh a) (wh b) (wh c) s ms x) (hex : ms.mode ≠ .exited)
    (hmo : modeOf v = some ms'.mode) (hms : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩)
    (h : (ms.m aRS = 3 ∧ ms.m (aO 0) = 3 ∧ ms.m (aO 1) = 3 ∧ v = 0 ∧ s' = inv ms [0, 0, 0] st) ∨
      (v = waitCode.eval (inv ms [0, 0, 0] st).down ∧ s' = inv ms [0, 0, 0] st)) :
    SimOK a b c s st s'.st ms' x := by
  have hok : okT ms (rh a) (wh b) (wh c) s := (relT_inv hR hex).2.2.1
  rcases h with ⟨h1, h2, h3, hv, hs'⟩ | ⟨hv, hs'⟩
  · have hmd : ms'.mode = .exited := by rw [hv, modeOf_zero] at hmo; exact (Option.some.inj hmo).symm
    refine ⟨x, ?_, .inr ⟨by rw [hs']; rfl, rfl⟩⟩
    rw [hms, hmd, hs']
    exact sim_exit hR hex h1 h2 h3
  · have hmd : ms'.mode = .waiting s := by
      rw [hv, waitCode_eval _ hok.2.2.2.1 hs, modeOf_wait] at hmo; exact (Option.some.inj hmo).symm
    refine ⟨x, ?_, .inr ⟨by rw [hs']; rfl, rfl⟩⟩
    rw [hms, hmd, hs']
    exact sim_wait hR hex

/-- An event is one of the input's or the outputs'. -/
theorem step_event {N a b c s : Nat} {st st₁ : DStore} {ms ms' : MS} {x : NSt Unit} {e : Event}
    {s' : DSt} {v : Nat} (hR : RelT (rh a) (wh b) (wh c) s ms x) (hex : ms.mode ≠ .exited)
    (hw : DWait st s e.index st₁ e) (hwf : wfD e = true)
    (hmo : modeOf v = some ms'.mode) (hms : ms' = ⟨s'.g, s'.m, s'.rp, ms'.mode⟩)
    (hx : dexec (cbT N) FUEL (inv (deliver e ms) [e.code.toNat, e.index, e.payload] st₁) = some (.ret v, s')) :
    SimOK a b c s st s'.st ms' x := by
  have hok : okT ms (rh a) (wh b) (wh c) s := (relT_inv hR hex).2.2.1
  have hdg : (deliver e ms).g = ms.g := by
    unfold deliver; split
    · split <;> rfl
    · rfl
  have hidx : ∀ k, (deliver e ms).g k = e.index → e.index = ms.g k := fun k h => by rw [← h, hdg]
  rcases cbT_ret hx with ⟨h0, h1, hx⟩ | ⟨h0, h1, hx⟩ | ⟨h0, h1, hx⟩ | ⟨h0, -⟩
  · have hi : e.index = rh a := (hidx INSR h1.symm).trans hok.1
    exact simOK_yield hmo hms (sim_evR hR hex (hi ▸ hw) hwf (code_two h0) hx)
  · have hi : e.index = wh (outC b c 0) := (hidx OUTSW h1.symm).trans hok.2.1
    exact simOK_yield hmo hms (sim_evW (j := 0) (by omega) hR hex (hi ▸ hw) hwf (code_three h0) hx)
  · have hi : e.index = wh (outC b c 1) := (hidx W1g h1.symm).trans hok.2.2.1
    exact simOK_yield hmo hms (sim_evW (j := 1) (by omega) hR hex (hi ▸ hw) hwf (code_three h0) hx)
  · have h0' : e.code.toNat = 0 := h0
    rcases dwait_code hw with hc | hc <;> rw [hc] at h0' <;> cases h0'

/-- A step after `YIELD`. -/
theorem step_ready {N a b c s : Nat} (hN : 0 < N ∧ N ≤ 256) (hs : s < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt Unit} (hR : RelT (rh a) (wh b) (wh c) s ms x)
    (hex : ms.mode ≠ .exited) (hi : dinvoke (cbT N) [0, 0, 0] st ms = some (st', ms')) :
    SimOK a b c s st st' ms' x := by
  obtain ⟨code, s', hx, hmo, hst, hms⟩ := dinvoke_inv hi
  have hx' : dexec (cbT N) FUEL (inv ms [0, 0, 0] st) = some (.ret code, s') := hx
  rw [hst]
  rcases cbT_ret hx' with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, hx''⟩
  · have h0' : (0 : Nat) = 2 := h0
    exact absurd h0' (by decide)
  · have h0' : (0 : Nat) = 3 := h0
    exact absurd h0' (by decide)
  · have h0' : (0 : Nat) = 3 := h0
    exact absurd h0' (by decide)
  · exact step_act hN hR hex hmo hms hx'' (step_stutter hs hR hex hmo hms)

/-- **The simulation**: a step of the generated tee is a step of the tee node, or changes neither
the store nor the node. -/
theorem step_sim {N a b c s : Nat} (hN : 0 < N ∧ N ≤ 256) (hs : s < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt Unit} (hR : RelT (rh a) (wh b) (wh c) s ms x)
    (h : DRStep (genT N) st ms st' ms') :
    ∃ x', RelT (rh a) (wh b) (wh c) s ms' x' ∧
      (NStep (teeNode a b c) s st x st' x' ∨ (st' = st ∧ x' = x)) := by
  by_cases hex : ms.mode = .exited
  · exact (no_step_exited hex h).elim
  have hmd : ms.mode = .ready ∨ ms.mode = .waiting s := (relT_inv hR hex).2.1
  cases h with
  | ready hm hi => exact step_ready hN hs hR hex hi
  | event hm hw hwf hi =>
    rename_i s₀ hd st₁ e
    have hs₀ : s₀ = s := by
      rcases hmd with h' | h' <;> rw [hm] at h' <;> cases h'
      rfl
    obtain ⟨code, s', hx, hmo, hst, hms⟩ := dinvoke_inv hi
    rw [hst]
    exact step_event hR hex (hs₀ ▸ dwait_index hw ▸ hw) hwf hmo hms hx

/-- **The start**: the machine after the lift is related to the node's initial state. -/
theorem init_rel (a b c s : Nat) :
    RelT (rh a) (wh b) (wh c) s (initMST (rh a) (wh b) (wh c) s) (NSt.init (teeNode a b c)) := by
  have hq : ∀ j, qOf (initMST (rh a) (wh b) (wh c) s) j = [] := fun j => by
    simp [qOf, initMST, upd_apply, slice, LENg, INSR, OUTSW, W1g, WS]
  refine relT_live (by simp [NSt.init, teeNode]) (.inl rfl) ?_ ?_ fun j hj => ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [initMST, upd_apply, LENg, OFF0, OFF1, INSR, OUTSW, W1g, WS]
  · exact .inl ⟨rfl, by simp [NSt.init, teeNode], rfl⟩
  · refine ⟨⟨.idle [], []⟩, ?_, .inl ⟨rfl, by rw [hq]⟩⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> simp [NSt.init, teeNode]

end Silmaril.Proofs.Wasm.JcoTool.KTee
