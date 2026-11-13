module

public import Silmaril.Proofs.Wasm.JcoTool.KTee.Batch

/-!
# The generated tee: the drops, `EXIT` and `WAIT`

`sim_actStop` (`stream.drop-readable`: `NStep.dropIn`), `sim_actClose` (`stream.drop-writable`:
`NStep.dropOut`), `sim_exit` and `sim_wait` (no built-in: the node does not move).
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

theorem mem_two {l : List NOut} (hl : l.length = 2) {P : NOut → Prop}
    (h : ∀ j, j ≤ 1 → ∃ o, l[j]? = some o ∧ P o) : ∀ o ∈ l, P o := by
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  obtain ⟨o', ho', hp⟩ := h i (by omega)
  rw [List.getElem?_eq_getElem hi] at ho'
  cases ho'
  exact hp

/-- Output `j`'s offset is within the batch. -/
theorem okT_off {ms : MS} {r w₀ w₁ s j : Nat} (hok : okT ms r w₀ w₁ s) (hj : j ≤ 1) :
    ms.g (OFFg j) ≤ ms.g LENg := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · exact hok.2.2.2.2.2.1
  · exact hok.2.2.2.2.2.2

/-- What the guard of the input's drop gives: the node may stop, no read is pending. -/
theorem stop_pre {r w₀ w₁ s : Nat} {ms : MS} {x : NSt Unit} (hR : RelT r w₀ w₁ s ms x)
    (hne : ms.mode ≠ .exited) (hg : ms.m aRS = 2 ∨ (ms.m aRS = 0 ∧ ms.m (aO 0) = 2 ∧ ms.m (aO 1) = 2)) :
    x.mayStop trB ∧ ms.rp = none := by
  obtain ⟨hlen, -, -, hI, hOs⟩ := relT_inv hR hne
  have hdead : ms.m (aO 0) = 2 → ms.m (aO 1) = 2 → ∀ o ∈ x.outs, o.isDead := fun e0 e1 =>
    mem_two hlen fun j hj => by
      obtain ⟨o, ho, hr⟩ := hOs j hj
      have hd2 : ms.m (aO j) = 2 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
        · exact e0
        · exact e1
      refine ⟨o, ho, .inl ?_⟩
      rcases hr with ⟨e', -⟩ | ⟨e', -⟩ | ⟨-, h2⟩ | ⟨e', -⟩ <;> try (rw [hd2] at e'; cases e')
      exact h2
  rcases hg with e | ⟨e, e0, e1⟩
  · rcases hI with ⟨e', -⟩ | ⟨e', -⟩ | ⟨-, h, h'⟩ | ⟨e', -⟩ <;> try (rw [e] at e'; cases e')
    exact ⟨.inl h, h'⟩
  · rcases hI with ⟨-, h, h'⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ <;> try (rw [e] at e'; cases e')
    exact ⟨.inr ⟨h, .inr ⟨fun hn => by simp [hn] at hlen, hdead e0 e1⟩⟩, h'⟩

/-- The relation after the input's drop. -/
theorem relT_stop {r w₀ w₁ s : Nat} {ms : MS} {x : NSt Unit} (hR : RelT r w₀ w₁ s ms x)
    (hne : ms.mode ≠ .exited) (hrpn : ms.rp = none) :
    RelT r w₀ w₁ s ⟨ms.g, upd ms.m aRS 3, ms.rp, .ready⟩ (x.stop trB) := by
  obtain ⟨hlen, -, hok, -, hOs⟩ := relT_inv hR hne
  refine relT_live (by simp [Silmaril.Wasm.Component.Streams.Net.NSt.stop, hlen]) (.inl rfl) hok
    (.inr (.inr (.inr ⟨by simp [upd_apply], ⟨_, rfl⟩, hrpn⟩))) fun j hj => ?_
  obtain ⟨o, ho, hr⟩ := hOs j hj
  exact ⟨o, by simp [Silmaril.Wasm.Component.Streams.Net.NSt.stop, ho, trB_flush, push_nil],
    ORel_upd_RS hr _ _⟩

/-- **Drop the input** is `NStep.dropIn`. -/
theorem sim_actStop {a b c s f v : Nat} {st : DStore} {ms : MS} {x : NSt Unit} {ps : List Nat}
    {s' : DSt} (hR : RelT (rh a) (wh b) (wh c) s ms x) (hne : ms.mode ≠ .exited)
    (hg : ms.m aRS = 2 ∨ (ms.m aRS = 0 ∧ ms.m (aO 0) = 2 ∧ ms.m (aO 1) = 2))
    (hx : dexec actStop f (inv ms ps st) = some (.ret v, s')) :
    v = 1 ∧ ∃ x', RelT (rh a) (wh b) (wh c) s ⟨s'.g, s'.m, s'.rp, .ready⟩ x' ∧
      NStep (teeNode a b c) s st x s'.st x' := by
  have hok : okT ms (rh a) (wh b) (wh c) s := (relT_inv hR hne).2.2.1
  obtain ⟨hv, ⟨res, hd⟩, hrp, hgg, hm⟩ := actStop_ret hx
  have hI1 : ms.g INSR = rh a := hok.1
  have hd' : dstep st (.streamDropR (rh a)) = some (s'.st, res) := hI1 ▸ hd
  obtain ⟨hmay, hrpn⟩ := stop_pre hR hne hg
  refine ⟨hv, x.stop trB, ?_, .dropIn rfl hmay hd'⟩
  have e : (⟨s'.g, s'.m, s'.rp, .ready⟩ : MS) = ⟨ms.g, upd ms.m aRS 3, ms.rp, .ready⟩ := by
    rw [hgg, hm, hrp]; rfl
  rw [e]
  exact relT_stop hR hne hrpn

/-- What the guard of an output's drop gives: the input is dropped and the output written or
dead. -/
theorem close_pre {r w₀ w₁ s j : Nat} (hj : j ≤ 1) {ms : MS} {x : NSt Unit} (hR : RelT r w₀ w₁ s ms x)
    (hne : ms.mode ≠ .exited) (hRS : ms.m aRS = 3)
    (hg : (ms.m (aO j) = 0 ∧ ms.g LENg ≤ ms.g (OFFg j)) ∨ ms.m (aO j) = 2) :
    (∃ b', x.rd = .gone b') ∧ ∃ (o : NOut) (d : Bool), (x.outs[j]? = some ⟨.idle [], o.ack⟩ ∧ d = false ∨
      x.outs[j]? = some ⟨.dead, o.ack⟩ ∧ d = true) := by
  obtain ⟨-, -, -, hI, hOs⟩ := relT_inv hR hne
  have hgone : ∃ b', x.rd = .gone b' := by
    rcases hI with ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨-, h, -⟩ <;> try (rw [hRS] at e'; cases e')
    exact h
  obtain ⟨o, ho, hr⟩ := hOs j hj
  refine ⟨hgone, o, ?_⟩
  rcases hg with ⟨e, hle⟩ | e
  · rcases hr with ⟨-, h0⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ <;> try (rw [e] at e'; cases e')
    exact ⟨false, .inl ⟨by rw [ho, out_eta o, h0, qOf_nil hle], rfl⟩⟩
  · rcases hr with ⟨e', -⟩ | ⟨e', -⟩ | ⟨-, h2⟩ | ⟨e', -⟩ <;> try (rw [e] at e'; cases e')
    exact ⟨true, .inr ⟨by rw [ho, out_eta o, h2], rfl⟩⟩

/-- **Drop output `j`** is `NStep.dropOut`. -/
theorem sim_actClose {a b c s j f v : Nat} (hj : j ≤ 1) {st : DStore} {ms : MS} {x : NSt Unit}
    {ps : List Nat} {s' : DSt} (hR : RelT (rh a) (wh b) (wh c) s ms x) (hne : ms.mode ≠ .exited)
    (hRS : ms.m aRS = 3) (hg : (ms.m (aO j) = 0 ∧ ms.g LENg ≤ ms.g (OFFg j)) ∨ ms.m (aO j) = 2)
    (hx : dexec (actClose j) f (inv ms ps st) = some (.ret v, s')) :
    v = 1 ∧ ∃ x', RelT (rh a) (wh b) (wh c) s ⟨s'.g, s'.m, s'.rp, .ready⟩ x' ∧
      NStep (teeNode a b c) s st x s'.st x' := by
  obtain ⟨hlen, -, hok, hI, hOs⟩ := relT_inv hR hne
  obtain ⟨hv, ⟨res, hd⟩, hrp, hgg, hm⟩ := actClose_ret hj hx
  have hd' : dstep st (.streamDropW (wh (outC b c j))) = some (s'.st, res) := okT_wh hok hj ▸ hd
  obtain ⟨hgone, o, d, hdc⟩ := close_pre hj hR hne hRS hg
  refine ⟨hv, { x with outs := x.outs.set j ⟨.closed d, o.ack⟩ }, ?_,
    .dropOut (teeNode_out a b c j hj) hgone hdc hd'⟩
  have e : (⟨s'.g, s'.m, s'.rp, .ready⟩ : MS) = ⟨ms.g, upd ms.m (aO j) 3, ms.rp, .ready⟩ := by
    rw [hgg, hm, hrp]; rfl
  rw [e]
  exact relT_set hj hlen (okT_out hj hok (fun _ _ => rfl) (okT_off hok hj)) hI rfl hOs
    (fun _ _ => rfl) (fun k hk => by simp [upd_apply, hk])
    (.inr (.inr (.inr ⟨by simp [upd_apply], d, rfl⟩)))

/-- **`EXIT`**: everything is dropped; the node does not move. -/
theorem sim_exit {a b c s : Nat} {ms : MS} {x : NSt Unit} (hR : RelT (rh a) (wh b) (wh c) s ms x)
    (hne : ms.mode ≠ .exited) (hRS : ms.m aRS = 3) (h0 : ms.m (aO 0) = 3) (h1 : ms.m (aO 1) = 3) :
    RelT (rh a) (wh b) (wh c) s ⟨ms.g, ms.m, ms.rp, .exited⟩ x := by
  obtain ⟨hlen, -, -, hI, hOs⟩ := relT_inv hR hne
  refine ⟨hlen, ?_⟩
  simp only [↓reduceIte]
  refine ⟨?_, fun j hj => ?_⟩
  · rcases hI with ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨-, h, -⟩ <;> try (rw [hRS] at e'; cases e')
    exact h
  · obtain ⟨o, ho, hr⟩ := hOs j hj
    have h3 : ms.m (aO j) = 3 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
      · exact h0
      · exact h1
    rcases hr with ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨-, d, h⟩ <;> try (rw [h3] at e'; cases e')
    exact ⟨o, d, ho, h⟩

/-- **`WAIT`**: the node does not move. -/
theorem sim_wait {a b c s : Nat} {ms : MS} {x : NSt Unit} (hR : RelT (rh a) (wh b) (wh c) s ms x)
    (hne : ms.mode ≠ .exited) : RelT (rh a) (wh b) (wh c) s ⟨ms.g, ms.m, ms.rp, .waiting s⟩ x := by
  obtain ⟨hlen, -, hok, hI, hOs⟩ := relT_inv hR hne
  exact relT_live hlen (.inr rfl) hok hI hOs

end Silmaril.Proofs.Wasm.JcoTool.KTee
