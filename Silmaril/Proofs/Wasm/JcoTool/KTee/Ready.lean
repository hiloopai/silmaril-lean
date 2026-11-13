module

public import Silmaril.Proofs.Wasm.JcoTool.KTee.Rel

/-!
# The generated tee: the actions after `YIELD` are steps of the tee node

`sim_actW` (a `stream.write`: `NStep.write`), `sim_actR` (a `stream.read`: `readBlk` or
`readNow`), `sim_actStop` (`dropIn`), `sim_actClose` (`dropOut`). Each takes the facts its guard
gives (`readyT_ret`) and returns the node's step and the relation after it.
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

/-- The invocation state of the callback. -/
def inv (ms : MS) (ps : List Nat) (st : DStore) : DSt := ⟨ms.g, ms.m, locals ps, st, ms.rp⟩

/-- The output stream of output `j` of `teeNode a b c`. -/
def outC (b c j : Nat) : Nat := if j = 0 then b else c

theorem teeNode_out (a b c j : Nat) (hj : j ≤ 1) : (teeNode a b c).outs[j]? = some (outC b c j) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> rfl

theorem okT_wh {ms : MS} {r b c s j : Nat} (hok : okT ms r (wh b) (wh c) s) (hj : j ≤ 1) :
    ms.g (WHg j) = wh (outC b c j) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · exact hok.2.1
  · exact hok.2.2.1

/-- What the guard of a write gives: output `j` is idle with the bytes `qOf ms j` to write. -/
theorem actW_pre {r w₀ w₁ s j : Nat} (hj : j ≤ 1) {ms : MS} {x : NSt Unit}
    (hR : RelT r w₀ w₁ s ms x) (hne : ms.mode ≠ .exited) (hO : ms.m (aO j) = 0) :
    ∃ o, x.outs[j]? = some o ∧ o.st = .idle (qOf ms j) := by
  obtain ⟨-, -, -, -, hOs⟩ := relT_inv hR hne
  obtain ⟨o, hoj, hrel⟩ := hOs j hj
  refine ⟨o, hoj, ?_⟩
  rcases hrel with ⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> first | exact h | omega

/-- The relation after a write of output `j` that is pending. -/
theorem actW_blocked {r w₀ w₁ s j : Nat} (hj : j ≤ 1) {ms : MS} {x : NSt Unit} {o : NOut}
    (hR : RelT r w₀ w₁ s ms x) (hne : ms.mode ≠ .exited) (hlt : ms.g (OFFg j) < ms.g LENg)
    (rp : Option (Nat × Nat)) (hrp : rp = ms.rp) :
    RelT r w₀ w₁ s ⟨ms.g, upd ms.m (aO j) 1, rp, .ready⟩
      { x with outs := x.outs.set j ⟨.busy (qOf ms j) [], o.ack⟩ } := by
  obtain ⟨hlen, -, hok, hI, hOs⟩ := relT_inv hR hne
  have hq : qOf ⟨ms.g, upd ms.m (aO j) 1, rp, .ready⟩ j = qOf ms j :=
    qOf_congr rfl rfl fun i _ => mem_upd_lo (aO_lt j hj) i
  have hqn : qOf ms j ≠ [] := by rw [← List.length_pos_iff, qOf_len]; omega
  exact relT_set hj hlen (okT_out hj hok (fun _ _ => rfl) (Nat.le_of_lt hlt)) hI hrp hOs
    (fun _ _ => rfl) (fun k hk => by simp [upd_apply, hk])
    (.inr (.inl ⟨by simp [upd_apply], by rw [hq], by rw [hq]; exact hqn⟩))

/-- The relation after a write of output `j` that returned at once. -/
theorem actW_done {r w₀ w₁ s j p : Nat} (hj : j ≤ 1) {ms : MS} {x : NSt Unit} {o : NOut}
    (hR : RelT r w₀ w₁ s ms x) (hne : ms.mode ≠ .exited) (hle : ms.g (OFFg j) ≤ ms.g LENg)
    (rp : Option (Nat × Nat)) (hrp : rp = ms.rp) :
    RelT r w₀ w₁ s ⟨(onWS j p ms.g ms.m).1, (onWS j p ms.g ms.m).2, rp, .ready⟩
      { x with outs := x.outs.set j (onWr ⟨.busy (qOf ms j) [], o.ack⟩ p) } := by
  obtain ⟨hlen, -, hok, hI, hOs⟩ := relT_inv hR hne
  exact relT_set hj hlen (okT_out hj hok (fun _ hk => onWS_g_other hk) (onWS_off_le hle)) hI hrp hOs
    (fun _ hk => onWS_g_other hk) (fun _ hk => onWS_m_other hk) (ORel_onWS hj rfl rp .ready)

/-- **Write the rest of the batch to output `j`** is `NStep.write`. -/
theorem sim_actW {a b c s j f v : Nat} (hj : j ≤ 1) {st : DStore} {ms : MS} {x : NSt Unit}
    {ps : List Nat} {s' : DSt} (hR : RelT (rh a) (wh b) (wh c) s ms x) (hne : ms.mode ≠ .exited)
    (hO : ms.m (aO j) = 0) (hlt : ms.g (OFFg j) < ms.g LENg)
    (hx : dexec (actW j) f (inv ms ps st) = some (.ret v, s')) :
    v = 1 ∧ ∃ x', RelT (rh a) (wh b) (wh c) s ⟨s'.g, s'.m, s'.rp, .ready⟩ x' ∧
      NStep (teeNode a b c) s st x s'.st x' := by
  obtain ⟨o, hoj, hq⟩ := actW_pre hj hR hne hO
  have hok : okT ms (rh a) (wh b) (wh c) s := (relT_inv hR hne).2.2.1
  obtain ⟨st₁, r, hd, -, hv, hst, hrp, hb, hnb⟩ := actW_ret hj hlt hok.2.2.2.2.1 hx
  have hd' : dstep st (.streamWrite (wh (outC b c j)) ((qOf ms j).take (qOf ms j).length)) =
      some (s'.st, .nat r) := by
    rw [List.take_length, qOf_slice, ← okT_wh hok hj, hst]; exact hd
  have hstep : NStep (teeNode a b c) s st x s'.st
      { x with outs := x.outs.set j (Silmaril.Wasm.Component.Streams.Net.Out.afterWrite
        ((qOf ms j).take (qOf ms j).length) ((qOf ms j).drop (qOf ms j).length) o.ack r) } :=
    .write (teeNode_out a b c j hj) (by rw [hoj, out_eta o, hq])
      (by rw [qOf_len]; omega) le_rfl hd'
  refine ⟨hv, _, ?_, hstep⟩
  rw [List.take_length, List.drop_length]
  by_cases hbl : r = blocked
  · have hgm : s'.g = ms.g ∧ s'.m = upd ms.m (aO j) 1 := hb hbl
    rw [hgm.1, hgm.2]
    have e : Silmaril.Wasm.Component.Streams.Net.Out.afterWrite (qOf ms j) [] o.ack r =
        ⟨.busy (qOf ms j) [], o.ack⟩ := by simp [Silmaril.Wasm.Component.Streams.Net.Out.afterWrite, hbl]
    rw [e]
    exact actW_blocked (o := o) hj hR hne hlt s'.rp hrp
  · have hgm : s'.g = (onWS j r ms.g ms.m).1 ∧ s'.m = (onWS j r ms.g ms.m).2 := hnb hbl
    rw [hgm.1, hgm.2]
    have e : Silmaril.Wasm.Component.Streams.Net.Out.afterWrite (qOf ms j) [] o.ack r =
        onWr ⟨.busy (qOf ms j) [], o.ack⟩ r := by
      simp [Silmaril.Wasm.Component.Streams.Net.Out.afterWrite, hbl]
    rw [e]
    exact actW_done (o := o) (p := r) hj hR hne (Nat.le_of_lt hlt) s'.rp hrp

end Silmaril.Proofs.Wasm.JcoTool.KTee
