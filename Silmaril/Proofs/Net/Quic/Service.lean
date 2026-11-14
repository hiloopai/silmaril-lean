module

public import Silmaril.Net.Quic.Service.Defs
import Silmaril.Net.Quic.Reassembly.Thms

/-!
# The QUIC stream service: proofs

For `Silmaril.Net.Quic.Service.Thms`: the service keeps its safety invariant, implementations
inherit it, and the reference implementation built from `RecvBuffer` provides the service.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Quic.Service

open Silmaril.Net.Quic Silmaril.Net.Quic.Service
open Silmaril.Net.Quic.RecvBuffer (insert_inv read_inv)

theorem take_of_prefix {c s : List UInt8} (hp : c <+: s) {n : Nat} (hn : n ≤ c.length) :
    c.take n = s.take n := by
  rw [List.prefix_iff_eq_take.1 hp, List.take_take, Nat.min_eq_left hn]

theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : upd f a b a = b := by
  simp [upd]

theorem upd2_eq {β : Type} (f : Nat → Role → β) (id : Nat) (r : Role) (b : β) (id' : Nat)
    (r' : Role) : upd f id (upd (f id) r b) id' r' = if id' = id ∧ r' = r then b else f id' r' := by
  by_cases h1 : id' = id
  · subst h1; by_cases h2 : r' = r
    · subst h2; simp [upd]
    · simp [upd, h2]
  · simp [upd, h1]

theorem upd_other {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by
  simp [upd, h]

/-! ## The specification keeps its invariant -/

theorem halfStep_ok {h h' : Half} {e : HalfEv} (hok : h.Ok) (hs : HalfStep h e h') : h'.Ok := by
  obtain ⟨hp, he, hr, hst, hx⟩ := hok
  cases hs with
  | write bs hf _ =>
    refine ⟨hp.trans (List.prefix_append _ _), fun h1 => ?_, hr, hst, hx⟩
    rw [(he h1).1] at hf; cases hf
  | finish hf _ =>
    refine ⟨hp, fun h1 => ?_, hr, hst, hx⟩
    rw [(he h1).1] at hf; cases hf
  | reset c hn =>
    refine ⟨hp, he, fun c' h1 => ?_, hst, hx⟩
    have := hr c' h1; rw [hn] at this; cases this
  | read bs hne hpre =>
    refine ⟨hpre, fun h1 => ?_, hr, hst, hx⟩
    have hw := (he h1).2
    have := hpre.length_le
    rw [List.length_append, hw] at this
    have : bs.length = 0 := by omega
    exact absurd (List.eq_nil_of_length_eq_zero this) hne
  | eof hf hrw _ hn =>
    refine ⟨hp, fun _ => ⟨hf, hrw⟩, hr, hst, ?_⟩
    simp [hn]
  | resetSeen c hc _ he' =>
    refine ⟨hp, fun h1 => by simp_all, fun c' h1 => ?_, hst, ?_⟩
    · simp only [Option.some.injEq] at h1; subst h1; exact hc
    · simp [he']
  | stopSending c hn =>
    refine ⟨hp, he, hr, fun c' h1 => ?_, hx⟩
    have := hst c' h1; rw [hn] at this; cases this
  | stopSeen c hc _ =>
    refine ⟨hp, he, hr, fun c' h1 => ?_, hx⟩
    simp only [Option.some.injEq] at h1; subst h1; exact hc

theorem empty_ok : ({} : Half).Ok := by
  refine ⟨List.nil_prefix, ?_, ?_, ?_, ?_⟩ <;> simp

theorem count_snoc_le {l m : List (List UInt8)} {d : List UInt8}
    (h : (l ++ [d]).count d ≤ m.count d) (hl : ∀ x, l.count x ≤ m.count x) (x : List UInt8) :
    (l ++ [d]).count x ≤ m.count x := by
  by_cases hx : x = d
  · subst hx; exact h
  · have : (d == x) = false := by simp [Ne.symm hx]
    simp only [List.count_append, List.count_singleton, this, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero]
    exact hl x

theorem connStep_ok {c c' : Conn} {e : ConnEv} (hok : c.Ok) (hs : ConnStep c e c') : c'.Ok := by
  obtain ⟨hh, hu, hl, hd⟩ := hok
  cases hs with
  | openStream t hlt =>
    refine ⟨hh, fun id r h => hu id r ?_, fun t' => ?_, hd⟩
    · rcases h with h | h
      · left; intro ho; apply h
        simp only [Conn.IsOpen, upd] at ho ⊢; split <;> simp_all <;> omega
      · exact .inr h
    · simp only [upd]; split
      · subst_vars; omega
      · exact hl t'
  | raiseLimit t m _ =>
    refine ⟨hh, hu, fun t' => ?_, hd⟩
    simp only [upd]; split
    · subst_vars; have := hl t'; omega
    · exact hl t'
  | half id r e ho hc hst =>
    refine ⟨fun id' r' => ?_, fun id' r' h => ?_, hl, hd⟩
    · by_cases h1 : id' = id
      · subst h1; by_cases h2 : r' = r
        · subst h2; simp only [upd_same]; exact halfStep_ok (hh _ _) hst
        · simp only [upd_same, upd_other _ _ h2]; exact hh _ _
      · simp only [upd_other _ _ h1]; exact hh _ _
    · by_cases h1 : id' = id
      · subst h1; by_cases h2 : r' = r
        · subst h2
          rcases h with h | h
          · exact absurd ho h
          · rw [hc] at h; cases h
        · simp only [upd_same, upd_other _ _ h2]; exact hu _ _ h
      · simp only [upd_other _ _ h1]; exact hu _ _ h
  | sendDatagram r d _ =>
    refine ⟨hh, hu, hl, fun r' x => ?_⟩
    have := hd r' x
    by_cases hr : r'.peer = r
    · simp only [upd, hr, ↓reduceIte, List.count_append]; rw [hr] at this; omega
    · simp only [upd, hr, ↓reduceIte]; exact this
  | recvDatagram r d hle =>
    refine ⟨hh, hu, hl, fun r' x => ?_⟩
    simp only [upd]; split
    · subst_vars; exact count_snoc_le hle (hd _) x
    · exact hd r' x

theorem connSteps_ok {c c' : Conn} {es : List ConnEv} (hok : c.Ok) (hs : ConnSteps c es c') :
    c'.Ok := by
  induction hs with
  | refl => exact hok
  | cons h _ ih => exact ih (connStep_ok hok h)

theorem initial_ok (limit : StreamType → Nat) (dg : Bool) : (Conn.initial limit dg).Ok :=
  ⟨fun _ _ => empty_ok, fun _ _ _ => rfl, fun _ => Nat.zero_le _, fun _ _ => by simp [Conn.initial]⟩

theorem connSteps_snoc {c c' c'' : Conn} {es : List ConnEv} {e : ConnEv}
    (h : ConnSteps c es c') (h' : ConnStep c' e c'') : ConnSteps c (es ++ [e]) c'' := by
  induction h with
  | refl => exact .cons h' (.refl _)
  | cons h _ ih => exact .cons h (ih h')

theorem reachable_spec (S : StreamService) {s : S.State} (h : S.Reachable s) :
    S.Inv s ∧ ∃ es, ConnSteps (S.view S.init) es (S.view s) := by
  induction h with
  | init => exact ⟨S.init_inv, [], .refl _⟩
  | @step s s' e _ hs ih =>
    obtain ⟨hi, es, hes⟩ := ih
    refine ⟨S.step_inv hi hs, es ++ [e], ?_⟩
    exact connSteps_snoc hes (S.step_sound hi hs)
  | internal _ hs ih =>
    obtain ⟨hi, es, hes⟩ := ih
    exact ⟨S.internal_inv hi hs, es, (S.internal_view hi hs) ▸ hes⟩

theorem reachable_ok (S : StreamService) {s : S.State} (h : S.Reachable s) : (S.view s).Ok := by
  obtain ⟨-, es, hes⟩ := reachable_spec S h
  exact connSteps_ok S.init_ok hes

/-! ## The reference half -/

theorem sliceOf_append {s t : List UInt8} {g : Segment} (hg : g.SliceOf s) :
    g.SliceOf (s ++ t) := by
  obtain ⟨h1, h2⟩ := hg
  simp only [Segment.stop] at h1
  refine ⟨by simp only [Segment.stop, List.length_append]; omega, ?_⟩
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  exact h2

theorem view_read_prefix {h : HalfImpl} (hi : h.Inv) : h.view.read <+: h.written := by
  simp only [HalfImpl.view]
  exact (List.take_prefix _ _).trans (contiguous_prefix hi.1)

theorem view_read_full {h : HalfImpl} (hi : h.Inv) (hd : h.buf.delivered = h.written.length) :
    h.view.read = h.written := by
  simp only [HalfImpl.view]
  rw [take_of_prefix (contiguous_prefix hi.1) hi.2.1, hd, List.take_length]

theorem halfImpl_step {h h' : HalfImpl} {e : HalfEv} (hi : h.Inv) (hs : h.step e = some h') :
    HalfStep h.view e h'.view ∧ h'.Inv := by
  obtain ⟨hsl, hd, hr, hst, he, hx⟩ := hi
  cases e with
  | write bs =>
    simp only [HalfImpl.step] at hs; split at hs
    · rename_i hc; obtain ⟨hf, hn⟩ := hc
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨HalfStep.write bs hf hn, fun g hg => sliceOf_append (hsl g hg), hd, hr, hst,
        fun h1 => ?_, hx⟩
      rw [(he h1).1] at hf; cases hf
    · cases hs
  | finish =>
    simp only [HalfImpl.step] at hs; split at hs
    · rename_i hc; obtain ⟨hf, hn⟩ := hc
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨HalfStep.finish hf hn, hsl, hd, hr, hst, fun h1 => ?_, hx⟩
      rw [(he h1).1] at hf; cases hf
    · cases hs
  | reset c =>
    simp only [HalfImpl.step] at hs; split at hs
    · rename_i hn
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨HalfStep.reset c hn, hsl, hd, fun c' h1 => ?_, hst, he, hx⟩
      have := hr c' h1; rw [hn] at this; cases this
    · cases hs
  | read bs =>
    simp only [HalfImpl.step] at hs; split at hs
    · rename_i hc; obtain ⟨hne, hb⟩ := hc
      simp only [Option.some.injEq] at hs; subst hs
      obtain ⟨⟨hsl', hd'⟩, hrd, hfull⟩ := read_inv (s := h.written) ⟨hsl, hd⟩
      have hv : h.view.read ++ bs = (contiguous h.buf.read.2.segs).take h.buf.read.2.delivered := by
        simp only [HalfImpl.view]; rw [← hb]; exact hrd
      refine ⟨?_, hsl', hd', hr, hst, fun h1 => ?_, hx⟩
      · have hstep := HalfStep.read (h := h.view) bs hne (by
          rw [hv]; exact (List.take_prefix _ _).trans (contiguous_prefix hsl'))
        simp only [HalfImpl.view] at hstep hv ⊢
        rw [hv] at hstep; exact hstep
      · exfalso
        obtain ⟨-, hdl⟩ := he h1
        have hlen := (contiguous_prefix hsl).length_le
        have h3 : bs.length + h.buf.delivered ≤ (contiguous h.buf.segs).length := by
          rw [← hb]; simp only [RecvBuffer.read, List.length_drop]; omega
        have : bs.length = 0 := by omega
        exact hne (List.eq_nil_of_length_eq_zero this)
    · cases hs
  | eof =>
    simp only [HalfImpl.step] at hs; split at hs
    · rename_i hc; obtain ⟨hf, hdl, he', hn⟩ := hc
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨HalfStep.eof hf (view_read_full ⟨hsl, hd, hr, hst, he, hx⟩ hdl) he' hn,
        hsl, hd, hr, hst, fun _ => ⟨hf, hdl⟩, by simp [hn]⟩
    · cases hs
  | resetSeen c =>
    simp only [HalfImpl.step] at hs; split at hs
    · rename_i hc; obtain ⟨hrc, hn, he'⟩ := hc
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨HalfStep.resetSeen c hrc hn he', hsl, hd, fun c' h1 => ?_, hst,
        fun h1 => by simp_all, by simp [he']⟩
      simp only [Option.some.injEq] at h1; subst h1; exact hrc
    · cases hs
  | stopSending c =>
    simp only [HalfImpl.step] at hs; split at hs
    · rename_i hn
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨HalfStep.stopSending c hn, hsl, hd, hr, fun c' h1 => ?_, he, hx⟩
      have := hst c' h1; rw [hn] at this; cases this
    · cases hs
  | stopSeen c =>
    simp only [HalfImpl.step] at hs; split at hs
    · rename_i hc; obtain ⟨hsc, hn⟩ := hc
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨HalfStep.stopSeen c hsc hn, hsl, hd, hr, fun c' h1 => ?_, he, hx⟩
      simp only [Option.some.injEq] at h1; subst h1; exact hsc
    · cases hs

theorem transmit_slice {h : HalfImpl} {off len : Nat} (ho : off ≤ h.written.length) :
    (Segment.mk off ((h.written.drop off).take len)).SliceOf h.written := by
  refine ⟨?_, ?_⟩
  · simp only [Segment.stop, List.length_take, List.length_drop]; omega
  · simp [List.take_eq_take_iff]

theorem halfImpl_transmit {h h' : HalfImpl} {off len : Nat} (hi : h.Inv)
    (hs : h.transmit off len = some h') : h'.view = h.view ∧ h'.Inv := by
  obtain ⟨hsl, hd, hr, hst, he, hx⟩ := hi
  simp only [HalfImpl.transmit] at hs
  split at hs
  · rename_i ho
    have hg := transmit_slice (h := h) (len := len) ho
    rw [RecvBuffer.insert_slices false hsl hg] at hs
    simp only [Option.some.injEq] at hs; subst hs
    obtain ⟨⟨hsl', hd'⟩, ht⟩ := insert_inv (s := h.written) ⟨hsl, hd⟩ hg
    refine ⟨?_, hsl', hd', hr, hst, he, hx⟩
    simp only [HalfImpl.view, ht]
  · cases hs

theorem halfImpl_view_empty : ({} : HalfImpl).view = {} := rfl

theorem halfImpl_empty_inv : ({} : HalfImpl).Inv :=
  ⟨fun _ hg => (by cases hg), Nat.le_refl _, fun _ h => (by cases h), fun _ h => (by cases h),
    fun h => (by cases h), by simp⟩

/-- Once all written bytes have been transmitted in one frame, everything is deliverable. -/
theorem halfImpl_transmit_all {h h' : HalfImpl} (hi : h.Inv)
    (hs : h.transmit 0 h.written.length = some h') : contiguous h'.buf.segs = h.written := by
  have hv := (halfImpl_transmit hi hs).2
  have hg : (Segment.mk 0 h.written).SliceOf h.written := by
    have := transmit_slice (h := h) (off := 0) (len := h.written.length) (Nat.zero_le _)
    simpa using this
  simp only [HalfImpl.transmit, Nat.zero_le, ↓reduceIte, List.drop_zero, List.take_length] at hs
  rw [RecvBuffer.insert_slices false hi.1 hg] at hs
  simp only [Option.some.injEq] at hs
  subst hs
  have hcov : ∀ j < h.written.length, Covered (h.buf.segs ++ [⟨0, h.written⟩]) j :=
    fun j hj => ⟨⟨0, h.written⟩, by simp, Nat.zero_le _, by simp [Segment.stop]; omega⟩
  obtain ⟨-, h2⟩ := contiguous_take hv.1 hcov
  have hp := contiguous_prefix hv.1
  rw [List.prefix_iff_eq_take.1 hp, Nat.le_antisymm hp.length_le h2, List.take_length]

/-! ## The reference connection -/

theorem connImpl_view_halves (c : ConnImpl) (id : Nat) (r : Role) (h' : HalfImpl) :
    (fun id' r' => (upd c.halves id (upd (c.halves id) r h') id' r').view) =
      upd (fun id' r' => (c.halves id' r').view) id
        (upd (fun r' => (c.halves id r').view) r h'.view) := by
  funext id' r'
  rw [upd2_eq, upd2_eq (fun id' r' => (c.halves id' r').view)]
  split <;> rfl

theorem connImpl_halves {c : ConnImpl} (hh : ∀ id r, (c.halves id r).Inv)
    (hu : ∀ id r, (¬ c.IsOpen id ∨ StreamId.canSend r id = false) → (c.halves id r).view = {})
    {id : Nat} {r : Role} {h' : HalfImpl} (hinv : h'.Inv)
    (hv : (¬ c.IsOpen id ∨ StreamId.canSend r id = false) → h'.view = {}) :
    (∀ id' r', (upd c.halves id (upd (c.halves id) r h') id' r').Inv) ∧
      (∀ id' r', (¬ c.IsOpen id' ∨ StreamId.canSend r' id' = false) →
        (upd c.halves id (upd (c.halves id) r h') id' r').view = {}) := by
  refine ⟨fun id' r' => ?_, fun id' r' hn => ?_⟩ <;> rw [upd2_eq] <;> split
  · exact hinv
  · exact hh _ _
  · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact hv hn
  · exact hu _ _ hn

theorem connImpl_step {c c' : ConnImpl} {e : ConnEv} (hi : c.Inv) (hs : c.step e = some c') :
    ConnStep c.view e c'.view ∧ c'.Inv := by
  obtain ⟨hh, hu, hl, hd⟩ := hi
  cases e with
  | openStream t =>
    simp only [ConnImpl.step] at hs; split at hs
    · rename_i hlt
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨ConnStep.openStream (c := c.view) t hlt, hh, fun id r h => hu id r ?_,
        fun t' => ?_, hd⟩
      · rcases h with h | h
        · left; intro ho; apply h
          simp only [ConnImpl.IsOpen, upd] at ho ⊢; split <;> simp_all <;> omega
        · exact .inr h
      · simp only [upd]; split
        · subst_vars; omega
        · exact hl t'
    · cases hs
  | raiseLimit t m =>
    simp only [ConnImpl.step] at hs; split at hs
    · rename_i hm
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨ConnStep.raiseLimit (c := c.view) t m hm, hh, hu, fun t' => ?_, hd⟩
      simp only [upd]; split
      · subst_vars; have := hl t'; omega
      · exact hl t'
    · cases hs
  | half id r e =>
    simp only [ConnImpl.step] at hs; split at hs
    · rename_i hc; obtain ⟨ho, hcs⟩ := hc
      cases hst : (c.halves id r).step e with
      | none => simp [hst] at hs
      | some h' =>
        simp only [hst, Option.map_some, Option.some.injEq] at hs; subst hs
        obtain ⟨hstep, hinv⟩ := halfImpl_step (hh id r) hst
        obtain ⟨h1, h2⟩ := connImpl_halves hh hu hinv (fun hn => by
          rcases hn with hn | hn
          · exact absurd ho hn
          · rw [hcs] at hn; cases hn)
        refine ⟨?_, h1, h2, hl, hd⟩
        have := ConnStep.half (c := c.view) id r e ho hcs hstep
        simp only [ConnImpl.view] at this ⊢
        rw [connImpl_view_halves]; exact this
    · cases hs
  | sendDatagram r d =>
    simp only [ConnImpl.step] at hs; split at hs
    · rename_i hdg
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨ConnStep.sendDatagram (c := c.view) r d hdg, hh, hu, hl, fun r' x => ?_⟩
      have := hd r' x
      by_cases hr : r'.peer = r
      · simp only [upd, hr, ↓reduceIte, List.count_append]; rw [hr] at this; omega
      · simp only [upd, hr, ↓reduceIte]; exact this
    · cases hs
  | recvDatagram r d =>
    simp only [ConnImpl.step] at hs; split at hs
    · rename_i hm
      simp only [Option.some.injEq] at hs; subst hs
      have hpos := List.count_pos_iff.2 hm
      have hle : (c.dgRecv r ++ [d]).count d ≤ (c.dgSent r.peer).count d := by
        have := hd r d; simp only [List.count_append, List.count_singleton, BEq.rfl,
          ↓reduceIte]; omega
      refine ⟨ConnStep.recvDatagram (c := c.view) r d hle, hh, hu, hl, fun r' x => ?_⟩
      have h1 := hd r' x
      have hpeer : ∀ r₁ r₂ : Role, r₁.peer = r₂.peer → r₁ = r₂ := by
        intro r₁ r₂; cases r₁ <;> cases r₂ <;> simp [Role.peer]
      by_cases hr : r' = r
      · subst hr
        simp only [upd, ↓reduceIte, List.count_append, List.count_singleton, List.count_erase]
        by_cases hx : d = x
        · subst hx; simp only [BEq.rfl, ↓reduceIte]; omega
        · have : (d == x) = false := by simp [hx]
          simp only [this, Bool.false_eq_true, ↓reduceIte]; omega
      · have : r'.peer ≠ r.peer := fun h => hr (hpeer _ _ h)
        simp only [upd, hr, ↓reduceIte, this]; exact h1
    · cases hs

theorem connImpl_internal {c c' : ConnImpl} (hi : c.Inv) (hs : ConnImpl.Internal c c') :
    c'.view = c.view ∧ c'.Inv := by
  obtain ⟨hh, hu, hl, hd⟩ := hi
  cases hs with
  | transmit id r off len ht =>
    obtain ⟨hv, hinv⟩ := halfImpl_transmit (hh id r) ht
    obtain ⟨h1, h2⟩ := connImpl_halves hh hu hinv (fun hn => hv ▸ hu id r hn)
    refine ⟨?_, h1, h2, hl, hd⟩
    simp only [ConnImpl.view]
    congr 1; funext id' r'; rw [upd2_eq]; split
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact hv
    · rfl
  | lose r d =>
    refine ⟨rfl, hh, hu, hl, fun r' x => ?_⟩
    have := hd r' x
    have hs := (List.erase_sublist (a := d) (l := c.inFlight r)).count_le x
    by_cases hr : r'.peer = r
    · simp only [upd, hr, ↓reduceIte]; rw [hr] at this; omega
    · simp only [upd, hr, ↓reduceIte]; exact this

theorem connImpl_initial_inv (limit : StreamType → Nat) (dg : Bool) :
    (ConnImpl.initial limit dg).Inv :=
  ⟨fun _ _ => halfImpl_empty_inv, fun _ _ _ => rfl, fun _ => Nat.zero_le _,
    fun _ _ => by simp [ConnImpl.initial]⟩

theorem connImpl_initial_view (limit : StreamType → Nat) (dg : Bool) :
    (ConnImpl.initial limit dg).view = Conn.initial limit dg := rfl

end Silmaril.Proofs.Net.Quic.Service
