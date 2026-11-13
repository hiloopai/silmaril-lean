module

public import Silmaril.Proofs.Wasm.JcoTool.KTee.Ready

/-!
# The generated tee: a batch read

`relT_batch`: the relation after a batch of bytes arrived (a `stream.read` that completed at
once, or the event of a pending one), when every output had written the previous batch or is
dead: the node's `NSt.onRead`. `relT_readBlk`: after a read that is pending (`readBlk`).
`sim_actR`: the read action is `NStep.readBlk` or `NStep.readNow`.
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

/-- An output that the guard of a read leaves: idle with nothing to write, dead or dropped. -/
theorem ORel_drained {ms : MS} {j : Nat} {o : NOut} (h : ORel ms j o) (h1 : ms.m (aO j) ≠ 1)
    (hw : ¬ (ms.m (aO j) = 0 ∧ ms.g (OFFg j) < ms.g LENg)) :
    (ms.m (aO j) = 0 ∧ o.st = .idle []) ∨ (ms.m (aO j) = 2 ∧ o.st = .dead) ∨
      (ms.m (aO j) = 3 ∧ ∃ d, o.st = .closed d) := by
  rcases h with ⟨h0, ho⟩ | ⟨h1', -⟩ | h2 | h3
  · exact .inl ⟨h0, by rw [ho, qOf_nil (by omega)]⟩
  · exact absurd h1' h1
  · exact .inr (.inl h2)
  · exact .inr (.inr h3)

theorem g0_LEN (g : Nat → Nat) : g0 g LENg = 0 := by simp [g0, upd_apply, LENg, OFF0, OFF1]

theorem g0_OFF (g : Nat → Nat) (j : Nat) (hj : j ≤ 1) : g0 g (OFFg j) = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> simp [g0, upd_apply, OFFg, OFF0, OFF1]

theorem g0_other (g : Nat → Nat) (k : Nat) (h0 : k ≠ LENg) (h1 : k ≠ OFF0) (h2 : k ≠ OFF1) :
    g0 g k = g k := by simp [g0, upd_apply, h0, h1, h2]

theorem okT_g0 {ms : MS} {r w₀ w₁ s : Nat} (hok : okT ms r w₀ w₁ s) (m : Nat → Nat)
    (rp : Option (Nat × Nat)) (md : Mode) : okT ⟨g0 ms.g, m, rp, md⟩ r w₀ w₁ s := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hok
  have e : ∀ k, k ≠ LENg → k ≠ OFF0 → k ≠ OFF1 → g0 ms.g k = ms.g k := fun k a b c => g0_other _ _ a b c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [e _ (by decide) (by decide) (by decide)]; exact h1
  · rw [e _ (by decide) (by decide) (by decide)]; exact h2
  · rw [e _ (by decide) (by decide) (by decide)]; exact h3
  · rw [e _ (by decide) (by decide) (by decide)]; exact h4
  · rw [g0_LEN]; omega
  · rw [show OFF0 = OFFg 0 from rfl, g0_OFF _ 0 (by omega)]; omega
  · rw [show OFF1 = OFFg 1 from rfl, g0_OFF _ 1 (by omega)]; omega

/-- An output that has written its batch, or is dead, or dropped. -/
def Drained (ms : MS) (j : Nat) (o : NOut) : Prop :=
  (ms.m (aO j) = 0 ∧ o.st = .idle []) ∨ (ms.m (aO j) = 2 ∧ o.st = .dead) ∨
    (ms.m (aO j) = 3 ∧ ∃ d, o.st = .closed d)

/-- The globals after a batch of `n` bytes. -/
theorem onRS_g (p : Nat) (g m : Nat → Nat) :
    (onRS p g m).1 LENg = p / 16 ∧ (∀ j, j ≤ 1 → (onRS p g m).1 (OFFg j) = 0) ∧
      ∀ k, k ≠ LENg → k ≠ OFF0 → k ≠ OFF1 → (onRS p g m).1 k = g k := by
  refine ⟨by simp [onRS, upd_apply, LENg, OFF0, OFF1], fun j hj => ?_,
    fun k a b c => by simp [onRS, upd_apply, a, b, c]⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl <;> simp [onRS, upd_apply, OFFg, OFF0, OFF1]

/-- The handles and bounds after a batch of at most `256` bytes. -/
theorem okT_batch {ms : MS} {r w₀ w₁ s p : Nat} (hok : okT ms r w₀ w₁ s) (hp : p / 16 ≤ 256)
    (m : Nat → Nat) (rp : Option (Nat × Nat)) (md : Mode) :
    okT ⟨(onRS p ms.g m).1, (onRS p ms.g m).2, rp, md⟩ r w₀ w₁ s := by
  obtain ⟨hL, hO, he⟩ := onRS_g p ms.g m
  obtain ⟨h1, h2, h3, h4, -⟩ := hok
  have hO0 : (onRS p ms.g m).1 OFF0 = 0 := hO 0 (by omega)
  have hO1 : (onRS p ms.g m).1 OFF1 = 0 := hO 1 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [he _ (by decide) (by decide) (by decide)]; exact h1
  · rw [he _ (by decide) (by decide) (by decide)]; exact h2
  · rw [he _ (by decide) (by decide) (by decide)]; exact h3
  · rw [he _ (by decide) (by decide) (by decide)]; exact h4
  · rw [hL]; exact hp
  · rw [hO0]; omega
  · rw [hO1]; omega

/-- The bytes every output has to write after a batch `xs`: all of them. -/
theorem qOf_batch {ms : MS} {code : Nat} {xs : List Val} (hcl : code / 16 = xs.length)
    (rp : Option (Nat × Nat)) (md : Mode) (j : Nat) (hj : j ≤ 1) :
    qOf ⟨(onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).1,
      (onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).2, rp, md⟩ j = xs.map nrm := by
  obtain ⟨hL, hO, -⟩ := onRS_g code ms.g (writeBytes ms.m IN (xs.map byteOf))
  have hs : slice (writeBytes ms.m IN (xs.map byteOf)) IN xs.length = xs.map byteOf := by
    simpa using slice_writeBytes ms.m IN (xs.map byteOf)
  have hm2 : (onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).2 =
      upd (writeBytes ms.m IN (xs.map byteOf)) aRS (if code % 16 = 0 then 0 else 2) := rfl
  unfold qOf
  dsimp only
  rw [hL, hO j hj, List.drop_zero, hcl, hm2, slice_congr (fun i _ => mem_upd_lo aRS_lt i), hs,
    List.map_map]
  rfl

/-- After a batch, an output keeps its state byte. -/
theorem onRS_aO {ms : MS} {code : Nat} {xs : List Val} (j : Nat) (hj : j ≤ 1) :
    (onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).2 (aO j) = ms.m (aO j) := by
  have := aO_lt j hj
  simp only [onRS, upd_apply, aO_ne_RS, ↓reduceIte, writeBytes]
  split <;> omega

/-- A drained output after the batch `ys` is pushed: idle with `ys`, or as it was. -/
theorem ORel_push {ms ms' : MS} {j : Nat} {o : NOut} {ys : List Val} (h : Drained ms j o)
    (hb : ms'.m (aO j) = ms.m (aO j)) (hq : qOf ms' j = ys) : ORel ms' j (o.push ys) := by
  unfold ORel
  rw [hb, hq]
  rcases h with ⟨e, ho⟩ | ⟨e, ho⟩ | ⟨e, d, ho⟩
  · exact .inl ⟨e, by rw [out_eta o, ho]; rfl⟩
  · exact .inr (.inr (.inl ⟨e, by rw [out_eta o, ho]; rfl⟩))
  · exact .inr (.inr (.inr ⟨e, d, by rw [out_eta o, ho]; rfl⟩))

/-- **After a batch**: `NSt.onRead`. -/
theorem relT_batch {r w₀ w₁ s code : Nat} {ms : MS} {x : NSt Unit} {xs : List Val}
    {rp : Option (Nat × Nat)} (hlen : x.outs.length = 2) (hok : okT ms r w₀ w₁ s)
    (hdr : ∀ j, j ≤ 1 → ∃ o, x.outs[j]? = some o ∧ Drained ms j o) (hcl : code / 16 = xs.length)
    (hxs : xs.length ≤ 256) (hrp : rp = none) :
    RelT r w₀ w₁ s ⟨(onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).1,
      (onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).2, rp, .ready⟩ (x.onRead trB code xs) := by
  have hR' : (onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).2 aRS =
      if code % 16 = 0 then 0 else 2 := by simp [onRS, upd_apply]
  have hI : IRel r ⟨(onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).1,
      (onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).2, rp, .ready⟩ (x.onRead trB code xs) := by
    by_cases hs : code % 16 = 0
    · exact .inl ⟨by show (onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).2 aRS = 0; rw [hR']; simp [hs],
        by simp [NSt.onRead, status, hs], hrp⟩
    · exact .inr (.inr (.inl ⟨by show (onRS code ms.g (writeBytes ms.m IN (xs.map byteOf))).2 aRS = 2; rw [hR']; simp [hs],
        by simp [NSt.onRead, status, hs], hrp⟩))
  refine relT_live (by simp [NSt.onRead, hlen]) (.inl rfl) (okT_batch hok (by omega) _ _ _) hI
    fun j hj => ?_
  obtain ⟨o, ho, hr⟩ := hdr j hj
  refine ⟨o.push ((trB.feed x.s xs).2), by simp [NSt.onRead, ho], ?_⟩
  rw [trB_feed]
  exact ORel_push hr (onRS_aO j hj) (qOf_batch hcl _ _ j hj)

/-- **After a read that is pending**: the input is busy and the batch empty. -/
theorem relT_readBlk {a b c s : Nat} {ms : MS} {x : NSt Unit} (hlen : x.outs.length = 2)
    (hok : okT ms (rh a) (wh b) (wh c) s)
    (hdr : ∀ j, j ≤ 1 → ∃ o, x.outs[j]? = some o ∧ Drained ms j o) :
    RelT (rh a) (wh b) (wh c) s ⟨g0 ms.g, upd ms.m aRS 1, some (rh a, IN), .ready⟩
      { x with rd := .busy } := by
  refine relT_live hlen (.inl rfl) (okT_g0 hok _ _ _) (.inr (.inl ⟨by simp [upd_apply], rfl, rfl,
    g0_LEN ms.g⟩)) fun j hj => ?_
  obtain ⟨o, ho, hr⟩ := hdr j hj
  refine ⟨o, ho, ?_⟩
  have hq : qOf ⟨g0 ms.g, upd ms.m aRS 1, some (rh a, IN), .ready⟩ j = [] :=
    qOf_nil (by show g0 ms.g LENg ≤ _; rw [g0_LEN]; omega)
  have hpush : o.push [] = o := push_nil o
  rw [← hpush]
  exact ORel_push hr (by simp [upd_apply, aO_ne_RS]) hq

/-- What the guard of a read gives: the input is idle and every output drained. -/
theorem actR_pre {r w₀ w₁ s : Nat} {ms : MS} {x : NSt Unit} (hR : RelT r w₀ w₁ s ms x)
    (hne : ms.mode ≠ .exited)
    (hw0 : ¬ (ms.m (aO 0) = 0 ∧ ms.g OFF0 < ms.g LENg)) (hw1 : ¬ (ms.m (aO 1) = 0 ∧ ms.g OFF1 < ms.g LENg))
    (hRS : ms.m aRS = 0) (h0 : ms.m (aO 0) ≠ 1) (h1 : ms.m (aO 1) ≠ 1) :
    x.rd = .idle ∧ ms.rp = none ∧ ∀ j, j ≤ 1 → ∃ o, x.outs[j]? = some o ∧ Drained ms j o := by
  obtain ⟨-, -, -, hI, hOs⟩ := relT_inv hR hne
  have hrd : x.rd = .idle ∧ ms.rp = none := by
    rcases hI with ⟨-, h, h'⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · exact ⟨h, h'⟩
    all_goals (rw [hRS] at e; cases e)
  refine ⟨hrd.1, hrd.2, fun j hj => ?_⟩
  obtain ⟨o, ho, hr⟩ := hOs j hj
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · exact ⟨o, ho, ORel_drained hr h0 hw0⟩
  · exact ⟨o, ho, ORel_drained hr h1 hw1⟩

/-- **Read the next batch** is `NStep.readBlk` or `NStep.readNow`. -/
theorem sim_actR {a b c s N f v : Nat} (hN : 0 < N ∧ N ≤ 256) {st : DStore} {ms : MS}
    {x : NSt Unit} {ps : List Nat} {s' : DSt} (hR : RelT (rh a) (wh b) (wh c) s ms x)
    (hne : ms.mode ≠ .exited)
    (hw0 : ¬ (ms.m (aO 0) = 0 ∧ ms.g OFF0 < ms.g LENg)) (hw1 : ¬ (ms.m (aO 1) = 0 ∧ ms.g OFF1 < ms.g LENg))
    (hRS : ms.m aRS = 0) (h0 : ms.m (aO 0) ≠ 1) (h1 : ms.m (aO 1) ≠ 1)
    (hx : dexec (actR N) f (inv ms ps st) = some (.ret v, s')) :
    v = 1 ∧ ∃ x', RelT (rh a) (wh b) (wh c) s ⟨s'.g, s'.m, s'.rp, .ready⟩ x' ∧
      NStep (teeNode a b c) s st x s'.st x' := by
  obtain ⟨hlen, -, hok, -, -⟩ := relT_inv hR hne
  obtain ⟨hrd, hrpn, hdr⟩ := actR_pre hR hne hw0 hw1 hRS h0 h1
  have hINSR : ms.g INSR = rh a := hok.1
  obtain ⟨hv, hrd'⟩ := actR_ret hN.2 hx
  refine ⟨hv, ?_⟩
  rcases hrd' with ⟨code, xs, hd, -, hcl, hxs, hrp, hg, hm⟩ | ⟨hd, hrp, hg, hm⟩
  · have hd' : dstep st (.streamRead (rh a) N) = some (s'.st, .read code xs) := hINSR ▸ hd
    refine ⟨x.onRead trB code xs, ?_, .readNow rfl hrd rfl hN.1 hd'⟩
    have hdr' : ∀ j, j ≤ 1 → ∃ o, x.outs[j]? = some o ∧ Drained ⟨g0 ms.g, ms.m, ms.rp, ms.mode⟩ j o :=
      hdr
    have hrp' : s'.rp = none := hrp.trans hrpn
    rw [hg, hm]
    exact relT_batch (ms := ⟨g0 ms.g, ms.m, ms.rp, ms.mode⟩) hlen (okT_g0 hok _ _ _) hdr' hcl
      (by omega) hrp'
  · have hd' : dstep st (.streamRead (rh a) N) = some (s'.st, .nat blocked) := hINSR ▸ hd
    refine ⟨{ x with rd := .busy }, ?_, .readBlk rfl hrd rfl hN.1 hd'⟩
    have hrp' : s'.rp = some (rh a, IN) := hrp.trans (by rw [← hINSR]; rfl)
    rw [hg, hm, hrp']
    exact relT_readBlk hlen hok hdr

end Silmaril.Proofs.Wasm.JcoTool.KTee
