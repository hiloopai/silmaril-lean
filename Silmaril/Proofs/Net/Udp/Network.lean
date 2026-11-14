module

public import Silmaril.Net.Udp.Network.Defs
public import Silmaril.Net.Udp.Service.Thms
public import Silmaril.Net.Channel.Thms

/-! Proofs for `Silmaril.Net.Udp.Network.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Udp.Proofs.Network

open Silmaril.Net.Ip Silmaril.Net.Channel Silmaril.Net.Udp Silmaril.Net.Udp.Network

/-! ## What a receiver accepts from the wire is well formed -/

theorem ofPacket_wf {p : Packet} {m : Msg} (h : Msg.ofPacket p = some m) : m.WF := by
  unfold Msg.ofPacket at h
  split at h
  · split at h
    · rename_i d hd
      split at h
      · rename_i hok
        cases h
        refine ⟨?_, (Datagram.decode_sound hd).1⟩
        unfold Datagram.checksumOk at hok
        split at hok
        · simp only [Bool.and_eq_true, beq_iff_eq] at hok
          show p.src.family = p.dst.family
          rw [hok.1, hok.2]
        · split at hok
          · rename_i l hl
            unfold Datagram.covered pseudo at hl
            show p.src.family = p.dst.family
            revert hl
            cases p.src <;> cases p.dst <;> simp [IpAddr.family]
          · cases hok
      · cases h
    · cases h
  · cases h

/-! ## Observations of runs -/

theorem obsOf_obs (o : Obs) (as : List Act) : obsOf (.obs o :: as) = o :: obsOf as := rfl
theorem obsOf_lose (m : Msg) (as : List Act) : obsOf (.lose m :: as) = obsOf as := rfl
theorem obsOf_dup (m : Msg) (as : List Act) : obsOf (.dup m :: as) = obsOf as := rfl
theorem obsOf_wire (p : Packet) (as : List Act) : obsOf (.wire p :: as) = obsOf as := rfl

theorem mem_erase_append {l : List Msg} {x : Msg} (m : Msg) (hx : x ∈ l) :
    x ∈ (l ++ [m]).erase m := by
  by_cases hm : m ∈ l
  · rw [List.erase_append_left _ hm]
    by_cases hxm : x = m
    · subst hxm; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ ((List.mem_erase_of_ne hxm).mpr hx)
  · rw [List.erase_append_right _ hm]
    exact List.mem_append_left _ hx

/-! ## Soundness: runs satisfy the specification -/

theorem local_sound {C : Config} {s s' : State} {as : List Act} (h : Steps C s as s')
    (hwf : ∀ x ∈ s.flight, x.WF) : ∀ o ∈ obsOf as, Local C o := by
  induction h with
  | refl => simp [obsOf]
  | @cons s s₁ s₂ a as hs _ ih =>
    cases hs with
    | send m hm hb =>
      rw [obsOf_obs]
      refine List.forall_mem_cons.mpr ⟨⟨hm, hb⟩, ih ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hwf x hx
      · rw [List.mem_singleton.mp hx]; exact hm
    | tooBig m hm => exact List.forall_mem_cons.mpr ⟨Or.inr ⟨rfl, hm⟩, ih hwf⟩
    | noBufs m => exact List.forall_mem_cons.mpr ⟨Or.inl rfl, ih hwf⟩
    | recv m hm hb =>
      rw [obsOf_obs]
      exact List.forall_mem_cons.mpr ⟨⟨rfl, hb, hwf m hm⟩,
        ih fun x hx => hwf x (List.erase_subset hx)⟩
    | refused a hb => exact List.forall_mem_cons.mpr ⟨⟨rfl, hb⟩, ih hwf⟩
    | lose m _ => exact ih fun x hx => hwf x (List.erase_subset hx)
    | dup m hm =>
      refine ih fun x hx => ?_
      rcases List.mem_append.mp hx with hx | hx
      · exact hwf x hx
      · rw [List.mem_singleton.mp hx]; exact hwf m hm
    | wire p _ =>
      refine ih fun x hx => ?_
      rcases List.mem_append.mp hx with hx | hx
      · exact hwf x hx
      · cases hp : Msg.ofPacket p with
        | none => simp [hp] at hx
        | some m =>
          simp only [hp, Option.toList_some, List.mem_singleton] at hx
          subst hx; exact ofPacket_wf hp

theorem chan_sound {C : Config} (hC : C.offPath = false) {s s' : State} {as : List Act}
    (h : Steps C s as s') : ∀ seen : List Msg, (∀ x ∈ s.flight, x ∈ seen) →
      okFrom seen (toChan (obsOf as)) := by
  induction h with
  | refl => intro _ _; simp [obsOf, toChan, okFrom]
  | @cons s s₁ s₂ a as hs _ ih =>
    intro seen hseen
    cases hs with
    | send m _ _ =>
      show okFrom (m :: seen) _
      refine ih (m :: seen) fun x hx => ?_
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_cons_of_mem _ (hseen x hx)
      · rw [List.mem_singleton.mp hx]; exact List.mem_cons_self
    | tooBig m _ => exact ih seen hseen
    | noBufs m => exact ih seen hseen
    | recv m hm _ =>
      exact ⟨hseen m hm, ih seen fun x hx => hseen x (List.erase_subset hx)⟩
    | refused a _ => exact ih seen hseen
    | lose m _ => exact ih seen fun x hx => hseen x (List.erase_subset hx)
    | dup m hm =>
      refine ih seen fun x hx => ?_
      rcases List.mem_append.mp hx with hx | hx
      · exact hseen x hx
      · rw [List.mem_singleton.mp hx]; exact hseen m hm
    | wire p hp =>
      have hnone : Msg.ofPacket p = none := by
        rcases hp with hp | hp
        · rw [hC] at hp; cases hp
        · exact hp
      refine ih seen fun x hx => ?_
      simp only [hnone, Option.toList_none, List.append_nil] at hx
      exact hseen x hx

/-! ## Completeness: the network can produce every specified trace -/

theorem complete {C : Config} :
    ∀ (t : List Obs) (s : State) (seen : List Msg), (∀ x ∈ seen, x ∈ s.flight) →
      (∀ o ∈ t, Local C o) → okFrom seen (toChan t) →
      ∃ as s', Steps C s as s' ∧ obsOf as = t := by
  intro t
  induction t with
  | nil => intro s _ _ _ _; exact ⟨[], s, .refl s, rfl⟩
  | cons o t ih =>
    intro s seen hseen hl hok
    have ho := hl o List.mem_cons_self
    have hl' : ∀ o ∈ t, Local C o := fun o' h => hl o' (List.mem_cons_of_mem _ h)
    cases o with
    | send m =>
      obtain ⟨as, s', hs, he⟩ := ih ⟨s.flight ++ [m]⟩ (m :: seen) (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ (List.mem_singleton_self _)
        · exact List.mem_append_left _ (hseen x hx)) hl' hok
      exact ⟨.obs (.send m) :: as, s', .cons (.send m ho.1 ho.2) hs, by rw [obsOf_obs, he]⟩
    | sendErr m e =>
      obtain ⟨as, s', hs, he⟩ := ih s seen hseen hl' hok
      rcases ho with rfl | ⟨rfl, hm⟩
      · exact ⟨_, s', .cons (.noBufs m) hs, by rw [obsOf_obs, he]⟩
      · exact ⟨_, s', .cons (.tooBig m hm) hs, by rw [obsOf_obs, he]⟩
    | recv a m =>
      obtain ⟨rfl, hb, _⟩ := ho
      obtain ⟨hm, hok'⟩ := hok
      have hin : m ∈ s.flight := hseen m hm
      obtain ⟨as, s', hs, he⟩ := ih ⟨(s.flight ++ [m]).erase m⟩ seen
        (fun x hx => mem_erase_append m (hseen x hx)) hl' hok'
      have hstep : Step C ⟨s.flight ++ [m]⟩ (.obs (.recv m.dst m)) ⟨(s.flight ++ [m]).erase m⟩ :=
        .recv m (List.mem_append_left _ hin) hb
      exact ⟨.dup m :: .obs (.recv m.dst m) :: as, s', .cons (.dup m hin) (.cons hstep hs),
        by rw [obsOf_dup, obsOf_obs, he]⟩
    | err a e =>
      obtain ⟨as, s', hs, he⟩ := ih s seen hseen hl' hok
      obtain ⟨rfl, hb⟩ := ho
      exact ⟨_, s', .cons (.refused a hb) hs, by rw [obsOf_obs, he]⟩

theorem complete_offPath {C : Config} (hC : C.offPath = true) :
    ∀ (t : List Obs) (s : State), (∀ o ∈ t, Local C o) →
      ∃ as s', Steps C s as s' ∧ obsOf as = t := by
  intro t
  induction t with
  | nil => intro s _; exact ⟨[], s, .refl s, rfl⟩
  | cons o t ih =>
    intro s hl
    have ho := hl o List.mem_cons_self
    have hl' : ∀ o ∈ t, Local C o := fun o' h => hl o' (List.mem_cons_of_mem _ h)
    cases o with
    | send m =>
      obtain ⟨as, s', hs, he⟩ := ih ⟨s.flight ++ [m]⟩ hl'
      exact ⟨_, s', .cons (.send m ho.1 ho.2) hs, by rw [obsOf_obs, he]⟩
    | sendErr m e =>
      obtain ⟨as, s', hs, he⟩ := ih s hl'
      rcases ho with rfl | ⟨rfl, hm⟩
      · exact ⟨_, s', .cons (.noBufs m) hs, by rw [obsOf_obs, he]⟩
      · exact ⟨_, s', .cons (.tooBig m hm) hs, by rw [obsOf_obs, he]⟩
    | recv a m =>
      obtain ⟨rfl, hb, hwf⟩ := ho
      have hp : Msg.ofPacket m.toPacket = some m := ofPacket_toPacket m hwf
      obtain ⟨as, s', hs, he⟩ := ih ⟨(s.flight ++ [m]).erase m⟩ hl'
      have hwire : Step C s (.wire m.toPacket) ⟨s.flight ++ [m]⟩ := by
        have h := Step.wire (C := C) (s := s) m.toPacket (Or.inl hC)
        rwa [hp, Option.toList_some] at h
      have hstep : Step C ⟨s.flight ++ [m]⟩ (.obs (.recv m.dst m)) ⟨(s.flight ++ [m]).erase m⟩ :=
        .recv m (List.mem_append_right _ (List.mem_singleton_self _)) hb
      exact ⟨.wire m.toPacket :: .obs (.recv m.dst m) :: as, s', .cons hwire (.cons hstep hs),
        by rw [obsOf_wire, obsOf_obs, he]⟩
    | err a e =>
      obtain ⟨as, s', hs, he⟩ := ih s hl'
      obtain ⟨rfl, hb⟩ := ho
      exact ⟨_, s', .cons (.refused a hb) hs, by rw [obsOf_obs, he]⟩

/-! ## The characterizations -/

theorem traces_iff {C : Config} (hC : C.offPath = false) (t : List Obs) :
    t ∈ traces C ↔ Spec C t := by
  constructor
  · rintro ⟨as, s', hs, rfl⟩
    exact ⟨local_sound hs (by simp), chan_sound hC hs [] (by simp)⟩
  · rintro ⟨hl, hok⟩
    exact complete t {} [] (by simp) hl hok

theorem traces_offPath_iff {C : Config} (hC : C.offPath = true) (t : List Obs) :
    t ∈ traces C ↔ ∀ o ∈ t, Local C o := by
  constructor
  · rintro ⟨as, s', hs, rfl⟩
    exact local_sound hs (by simp)
  · intro hl
    exact complete_offPath hC t {} hl

theorem traces_local {C : Config} {t : List Obs} (h : t ∈ traces C) : ∀ o ∈ t, Local C o := by
  obtain ⟨as, s', hs, rfl⟩ := h
  exact local_sound hs (by simp)

theorem mem_traces_of_spec {C : Config} {t : List Obs} (h : Spec C t) : t ∈ traces C := by
  cases hC : C.offPath
  · exact (traces_iff hC t).mpr h
  · exact (traces_offPath_iff hC t).mpr h.1

/-! ## Port isolation -/

/-- The message of a channel event. -/
def evMsg {α : Type} : Ev α → α
  | .send m => m
  | .recv m => m

theorem okFrom_filter {α : Type} (p : α → Bool) :
    ∀ (tr : List (Ev α)) (seen : List α), okFrom seen tr →
      okFrom (seen.filter p) (tr.filter fun e => p (evMsg e)) := by
  intro tr
  induction tr with
  | nil => intro _ _; trivial
  | cons e t ih =>
    intro seen h
    cases e with
    | send m =>
      have h' := ih (m :: seen) h
      by_cases hp : p m = true
      · simp only [List.filter_cons, evMsg, hp, ↓reduceIte] at h' ⊢
        exact h'
      · simp only [List.filter_cons, evMsg, hp, Bool.false_eq_true, ↓reduceIte] at h' ⊢
        exact h'
    | recv m =>
      obtain ⟨hm, h'⟩ := h
      by_cases hp : p m = true
      · simp only [List.filter_cons, evMsg, hp, ↓reduceIte]
        exact ⟨List.mem_filter.mpr ⟨hm, hp⟩, ih seen h'⟩
      · simp only [List.filter_cons, evMsg, hp, Bool.false_eq_true, ↓reduceIte]
        exact ih seen h'

theorem toChan_onlyTo (a : Endpoint) (t : List Obs) :
    toChan (onlyTo a t) = (toChan t).filter fun e => (evMsg e).dst == a := by
  induction t with
  | nil => rfl
  | cons o t ih =>
    cases o with
    | send m =>
      by_cases h : (m.dst == a) = true
      · simp only [onlyTo, toChan, List.filter_cons, Obs.about, h, ↓reduceIte,
          List.filterMap_cons, Obs.chan, evMsg] at ih ⊢
        rw [ih]
      · simp only [onlyTo, toChan, List.filter_cons, Obs.about, h, Bool.false_eq_true,
          ↓reduceIte, List.filterMap_cons, Obs.chan, evMsg] at ih ⊢
        exact ih
    | recv b m =>
      by_cases h : (m.dst == a) = true
      · simp only [onlyTo, toChan, List.filter_cons, Obs.about, h, ↓reduceIte,
          List.filterMap_cons, Obs.chan, evMsg] at ih ⊢
        rw [ih]
      · simp only [onlyTo, toChan, List.filter_cons, Obs.about, h, Bool.false_eq_true,
          ↓reduceIte, List.filterMap_cons, Obs.chan, evMsg] at ih ⊢
        exact ih
    | sendErr m e =>
      simp only [onlyTo, toChan, List.filter_cons, Obs.about, ↓reduceIte,
        List.filterMap_cons, Obs.chan] at ih ⊢
      exact ih
    | err b e =>
      simp only [onlyTo, toChan, List.filter_cons, Obs.about, ↓reduceIte,
        List.filterMap_cons, Obs.chan] at ih ⊢
      exact ih

theorem onlyTo_spec {C : Config} {t : List Obs} (a : Endpoint) (h : Spec C t) :
    Spec C (onlyTo a t) := by
  refine ⟨fun o ho => h.1 o (List.mem_filter.mp ho).1, ?_⟩
  show okFrom [] _
  rw [toChan_onlyTo]
  have := okFrom_filter (fun m : Msg => m.dst == a) (toChan t) [] h.2
  simpa using this

theorem isolation {C : Config} {t : List Obs} (a : Endpoint) (h : t ∈ traces C) :
    onlyTo a t ∈ traces C := by
  cases hC : C.offPath
  · exact (traces_iff hC _).mpr (onlyTo_spec a ((traces_iff hC t).mp h))
  · exact (traces_offPath_iff hC _).mpr fun o ho =>
      (traces_offPath_iff hC t).mp h o (List.mem_filter.mp ho).1

theorem recvAt_onlyTo {C : Config} (a : Endpoint) :
    ∀ t : List Obs, (∀ o ∈ t, Local C o) → recvAt a (onlyTo a t) = recvAt a t := by
  intro t
  induction t with
  | nil => intro _; rfl
  | cons o t ih =>
    intro hl
    have ih' := ih fun o' h => hl o' (List.mem_cons_of_mem _ h)
    cases o with
    | recv b m =>
      have hb : b = m.dst := (hl _ List.mem_cons_self).1
      by_cases hba : b = a
      · have h : (m.dst == a) = true := by rw [← hb, hba]; exact beq_self_eq_true a
        simp only [onlyTo, List.filter_cons, Obs.about, h, ↓reduceIte, recvAt, hba] at ih' ⊢
        rw [ih']
      · by_cases h : (m.dst == a) = true
        · simp only [onlyTo, List.filter_cons, Obs.about, h, ↓reduceIte, recvAt, hba] at ih' ⊢
          exact ih'
        · simp only [onlyTo, List.filter_cons, Obs.about, h, Bool.false_eq_true, ↓reduceIte,
            recvAt, hba] at ih' ⊢
          exact ih'
    | send m =>
      by_cases h : (m.dst == a) = true
      · simp only [onlyTo, List.filter_cons, Obs.about, h, ↓reduceIte, recvAt] at ih' ⊢
        exact ih'
      · simp only [onlyTo, List.filter_cons, Obs.about, h, Bool.false_eq_true, ↓reduceIte,
          recvAt] at ih' ⊢
        exact ih'
    | sendErr m e =>
      simp only [onlyTo, List.filter_cons, Obs.about, ↓reduceIte, recvAt] at ih' ⊢
      exact ih'
    | err b e =>
      simp only [onlyTo, List.filter_cons, Obs.about, ↓reduceIte, recvAt] at ih' ⊢
      exact ih'

/-! ## Malformed packets -/

theorem wire_malformed {C : Config} {s s' : State} {p : Packet} (h : Step C s (.wire p) s')
    (hp : Msg.ofPacket p = none) : s' = s := by
  cases h
  simp [hp]

end Silmaril.Net.Udp.Proofs.Network
