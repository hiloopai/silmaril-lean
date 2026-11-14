module

public import Silmaril.Net.Http3.Stream.Defs
import Silmaril.Net.Http3.Frame.Thms

/-!
# HTTP/3 streams: proofs

Control-stream invariants (RFC 9114 §6.2.1, §5.2, §7.2), critical unidirectional streams
(§6.2) and the request-stream grammar (§4.1), for `Silmaril.Net.Http3.Stream.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http3.Stream

open Silmaril.Net.Http3

/-! ## Folds in `Except` -/

theorem foldlM_cons_ok {α β ε : Type} {g : α → β → Except ε α} {s s' : α} {b : β} {bs : List β} :
    (b :: bs).foldlM g s = .ok s' ↔ ∃ s1, g s b = .ok s1 ∧ bs.foldlM g s1 = .ok s' := by
  simp only [List.foldlM_cons]
  cases h : g s b with
  | error e => simp [bind, Except.bind]
  | ok s1 => simp [bind, Except.bind]

theorem foldlM_nil_ok {α β ε : Type} {g : α → β → Except ε α} {s s' : α} :
    ([] : List β).foldlM g s = .ok s' ↔ s = s' := by
  simp [pure, Except.pure]

/-- A fold whose steps fix a predicate `P` and are the identity on `skip` elements is
unchanged by removing them. -/
theorem foldlM_filter {α β ε : Type} (g : α → β → Except ε α) (skip : β → Bool) (P : α → Prop)
    (hskip : ∀ s b, P s → skip b = true → g s b = .ok s)
    (hpres : ∀ s b s', P s → g s b = .ok s' → P s') :
    ∀ (bs : List β) (s : α), P s → bs.foldlM g s = (bs.filter (fun b => !skip b)).foldlM g s := by
  intro bs
  induction bs with
  | nil => intro s _; rfl
  | cons b bs ih =>
    intro s hs
    by_cases hb : skip b = true
    · simp only [List.filter_cons, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.foldlM_cons, hskip s b hs hb]
      exact ih s hs
    · simp only [List.filter_cons, hb, Bool.not_false, ↓reduceIte, List.foldlM_cons]
      cases h : g s b with
      | error e => rfl
      | ok s1 => exact ih s1 (hpres s b s1 hs h)

/-! ## Control stream -/

theorem controlStep_settings_some {peer : Role} {s s' : ControlState} {f : Frame}
    (hs : s.settings.isSome) (h : controlStep peer s f = .ok s') : s'.settings = s.settings := by
  unfold controlStep at h
  obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.1 hs
  rw [hps] at h
  simp only at h
  split at h <;> (try cases h) <;> (try rfl)
  all_goals (split at h <;> (try cases h) <;> (try (split at h <;> cases h)) <;> simp [hps])

theorem controlStep_first {peer : Role} {f : Frame} {s' : ControlState}
    (h : controlStep peer {} f = .ok s') : ∃ ps, f = .settings ps ∧ s' = { settings := some ps } := by
  unfold controlStep at h
  simp only at h
  split at h
  · rename_i ps; cases h; exact ⟨ps, rfl, rfl⟩
  · cases h

theorem controlStep_forbidden {peer : Role} {s s' : ControlState} {f : Frame}
    (hs : s.settings.isSome) (h : controlStep peer s f = .ok s') : forbiddenAfterSettings f = false := by
  unfold controlStep at h
  obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.1 hs
  rw [hps] at h
  simp only at h
  cases f <;> simp_all [forbiddenAfterSettings]

theorem controlRun_after {peer : Role} :
    ∀ (fs : List Frame) (s s' : ControlState), s.settings.isSome → controlRun peer s fs = .ok s' →
      (∀ f ∈ fs, forbiddenAfterSettings f = false) ∧ s'.settings = s.settings := by
  intro fs
  induction fs with
  | nil => intro s s' _ h; simp only [controlRun, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  | cons f fs ih =>
    intro s s' hs h
    obtain ⟨s1, h1, h2⟩ := foldlM_cons_ok.1 h
    have e1 := controlStep_settings_some hs h1
    have hs1 : s1.settings.isSome := by rw [e1]; exact hs
    obtain ⟨ih1, ih2⟩ := ih s1 s' hs1 h2
    refine ⟨?_, ih2.trans e1⟩
    intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact controlStep_forbidden hs h1
    · exact ih1 g hg

theorem controlRun_shape {peer : Role} {fs : List Frame} {s : ControlState}
    (h : controlRun peer {} fs = .ok s) (hne : fs ≠ []) :
    ∃ ps rest, fs = .settings ps :: rest ∧ s.settings = some ps ∧
      ∀ f ∈ rest, forbiddenAfterSettings f = false := by
  match fs, hne with
  | f :: rest, _ =>
    obtain ⟨s1, h1, h2⟩ := foldlM_cons_ok.1 h
    obtain ⟨ps, rfl, rfl⟩ := controlStep_first h1
    obtain ⟨hr, hset⟩ := controlRun_after rest _ s (by simp) h2
    exact ⟨ps, rest, rfl, hset, hr⟩

theorem noIncrease_refl (o : Option Nat) : NoIncrease o o := by
  cases o <;> simp [NoIncrease]

theorem noIncrease_trans {a b c : Option Nat} (h1 : NoIncrease a b) (h2 : NoIncrease b c) :
    NoIncrease a c := by
  cases a with
  | none => trivial
  | some x =>
    obtain ⟨y, rfl, hy⟩ := h1
    obtain ⟨z, rfl, hz⟩ := h2
    exact ⟨z, rfl, by omega⟩

theorem noDecrease_refl (o : Option Nat) : NoDecrease o o := by
  cases o <;> simp [NoDecrease]

theorem noDecrease_trans {a b c : Option Nat} (h1 : NoDecrease a b) (h2 : NoDecrease b c) :
    NoDecrease a c := by
  cases a with
  | none => trivial
  | some x =>
    obtain ⟨y, rfl, hy⟩ := h1
    obtain ⟨z, rfl, hz⟩ := h2
    exact ⟨z, rfl, by omega⟩

theorem controlStep_mono {peer : Role} {s s' : ControlState} {f : Frame}
    (h : controlStep peer s f = .ok s') :
    NoIncrease s.lastGoaway s'.lastGoaway ∧ NoDecrease s.maxPushId s'.maxPushId := by
  unfold controlStep at h
  split at h
  · split at h
    · cases h; exact ⟨noIncrease_refl _, noDecrease_refl _⟩
    · cases h
  · split at h
    all_goals (try (cases h; done))
    all_goals (try (cases h; exact ⟨noIncrease_refl _, noDecrease_refl _⟩))
    · -- goaway
      rename_i i
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hlt
          cases h
          refine ⟨?_, noDecrease_refl _⟩
          cases hg : s.lastGoaway with
          | none => trivial
          | some a =>
            rw [hg] at hlt
            simp only [Option.any_some, decide_eq_true_eq] at hlt
            exact ⟨i, rfl, by omega⟩
    · -- maxPushId
      rename_i p
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hlt
          cases h
          refine ⟨noIncrease_refl _, ?_⟩
          cases hm : s.maxPushId with
          | none => trivial
          | some a =>
            rw [hm] at hlt
            simp only [Option.any_some, decide_eq_true_eq] at hlt
            exact ⟨p, rfl, by omega⟩

theorem controlRun_mono {peer : Role} :
    ∀ (fs : List Frame) (s s' : ControlState), controlRun peer s fs = .ok s' →
      NoIncrease s.lastGoaway s'.lastGoaway ∧ NoDecrease s.maxPushId s'.maxPushId := by
  intro fs
  induction fs with
  | nil =>
    intro s s' h; simp only [controlRun, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨noIncrease_refl _, noDecrease_refl _⟩
  | cons f fs ih =>
    intro s s' h
    obtain ⟨s1, h1, h2⟩ := foldlM_cons_ok.1 h
    obtain ⟨a1, b1⟩ := controlStep_mono h1
    obtain ⟨a2, b2⟩ := ih s1 s' h2
    exact ⟨noIncrease_trans a1 a2, noDecrease_trans b1 b2⟩

theorem controlStep_goaway_server {s s' : ControlState} {i : Nat}
    (h : controlStep .server s (.goaway i) = .ok s') : isRequestStream i = true := by
  unfold controlStep at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
    · rename_i hn
      simp only [true_and, Classical.not_not] at hn
      exact hn

theorem controlRun_goaway_server :
    ∀ (fs : List Frame) (s s' : ControlState), controlRun .server s fs = .ok s' →
      ∀ i, Frame.goaway i ∈ fs → isRequestStream i = true := by
  intro fs
  induction fs with
  | nil => intro _ _ _ i hi; simp at hi
  | cons f fs ih =>
    intro s s' h i hi
    obtain ⟨s1, h1, h2⟩ := foldlM_cons_ok.1 h
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact controlStep_goaway_server h1
    · exact ih s1 s' h2 i hi

theorem controlStep_server_maxPushId {s s' : ControlState} {p : Nat}
    (hs : s.settings.isSome) : controlStep .server s (.maxPushId p) ≠ .ok s' := by
  unfold controlStep
  obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.1 hs
  simp [hps]

theorem controlRun_filter {peer : Role} (fs : List Frame) (s : ControlState) (hs : s.settings.isSome) :
    controlRun peer s fs = controlRun peer s (fs.filter fun f => !f.isUnknown) :=
  foldlM_filter (controlStep peer) Frame.isUnknown (fun s => s.settings.isSome)
    (fun s b hs hb => by
      obtain ⟨ps, hps⟩ := Option.isSome_iff_exists.1 hs
      cases b <;> simp_all [Frame.isUnknown, controlStep])
    (fun s b s' hs h => by rw [controlStep_settings_some hs h]; exact hs) fs s hs

/-! ## Critical unidirectional streams -/

/-- How many streams of each critical kind a list announces. -/
def countControl (ks : List UniKind) : Nat := ks.countP (· == .control)

theorem open_unknown (peer : Role) (u : UniStreams) (t : Nat) : u.open_ peer (.unknown t) = .ok u := rfl

theorem open_control_flag {peer : Role} {u u' : UniStreams} {k : UniKind}
    (h : u.open_ peer k = .ok u') : (u.control → u'.control) ∧
      (k = .control → ¬ u.control ∧ u'.control) := by
  cases k with
  | control => unfold UniStreams.open_ at h; by_cases hc : u.control <;> simp_all <;> subst h <;> simp_all
  | qpackEncoder => unfold UniStreams.open_ at h; by_cases hc : u.qpackEncoder <;> simp_all <;> subst h <;> simp_all
  | qpackDecoder => unfold UniStreams.open_ at h; by_cases hc : u.qpackDecoder <;> simp_all <;> subst h <;> simp_all
  | push p =>
    unfold UniStreams.open_ at h
    by_cases hp : peer = .client <;> by_cases hm : u.pushIds.contains p <;> simp_all <;> subst h <;> simp_all
  | unknown t => unfold UniStreams.open_ at h; simp_all <;> subst h <;> simp_all

theorem open_control_eq {peer : Role} {u u' : UniStreams} {k : UniKind} (hk : k ≠ .control)
    (h : u.open_ peer k = .ok u') : u'.control = u.control := by
  cases k with
  | control => exact absurd rfl hk
  | qpackEncoder => unfold UniStreams.open_ at h; by_cases hc : u.qpackEncoder <;> simp_all <;> subst h <;> simp_all
  | qpackDecoder => unfold UniStreams.open_ at h; by_cases hc : u.qpackDecoder <;> simp_all <;> subst h <;> simp_all
  | push p =>
    unfold UniStreams.open_ at h
    by_cases hp : peer = .client <;> by_cases hm : u.pushIds.contains p <;> simp_all <;> subst h <;> simp_all
  | unknown t => unfold UniStreams.open_ at h; simp_all <;> subst h <;> simp_all

theorem openAll_control_le_one {peer : Role} :
    ∀ (ks : List UniKind) (u u' : UniStreams), u.openAll peer ks = .ok u' →
      (if u.control then 1 else 0) + countControl ks ≤ 1 ∧
        (u'.control = (u.control || decide (0 < countControl ks))) := by
  intro ks
  induction ks with
  | nil =>
    intro u u' h
    simp only [UniStreams.openAll, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
    simp only [countControl, List.countP_nil, Nat.add_zero, Nat.lt_irrefl, decide_false,
      Bool.or_false, and_true]
    split <;> omega
  | cons k ks ih =>
    intro u u' h
    obtain ⟨u1, h1, h2⟩ := foldlM_cons_ok.1 h
    obtain ⟨ih1, ih2⟩ := ih u1 u' h2
    obtain ⟨m1, m2⟩ := open_control_flag h1
    by_cases hk : k = .control
    · subst hk
      obtain ⟨hn, hy⟩ := m2 rfl
      simp only [hy, ↓reduceIte] at ih1
      simp only [countControl, List.countP_cons, beq_self_eq_true, ↓reduceIte] at ih1 ⊢
      simp only [hn, Bool.false_eq_true, ↓reduceIte] at *
      refine ⟨by omega, ?_⟩
      rw [ih2, hy]; simp
    · have hk' : (k == UniKind.control) = false := by simp [hk]
      have hc : u1.control = u.control := open_control_eq hk h1
      simp only [countControl, List.countP_cons, hk', Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero] at ih1 ih2 ⊢
      rw [hc] at ih1 ih2
      exact ⟨ih1, ih2⟩

/-! ## Request streams -/

theorem reqRun_filter (k : StreamKind) (interim : List UInt8 → Bool) (fs : List Frame) (s : ReqState) :
    reqRun k interim s fs = reqRun k interim s (fs.filter fun f => !f.isUnknown) :=
  foldlM_filter (reqStep k interim) Frame.isUnknown (fun _ => True)
    (fun s b _ hb => by cases b <;> simp_all [Frame.isUnknown, reqStep]) (fun _ _ _ _ _ => trivial)
    fs s trivial

theorem reqRun_data (k : StreamKind) (interim : List UInt8 → Bool) :
    ∀ (chunks : List (List UInt8)) (p : Parts),
      reqRun k interim { phase := .body, parts := p } (chunks.map .data) =
        .ok { phase := .body, parts := { p with content := p.content ++ chunks.flatten } } := by
  intro chunks
  induction chunks with
  | nil => intro p; simp [reqRun, pure, Except.pure]
  | cons c cs ih =>
    intro p
    simp only [List.map_cons, reqRun, List.foldlM_cons, reqStep, bind, Except.bind]
    rw [← reqRun, ih]
    simp [List.append_assoc]

theorem reqRun_append {k : StreamKind} {interim : List UInt8 → Bool} {s s1 : ReqState}
    {xs ys : List Frame} (h : reqRun k interim s xs = .ok s1) :
    reqRun k interim s (xs ++ ys) = reqRun k interim s1 ys := by
  simp only [reqRun, List.foldlM_append] at h ⊢
  rw [h]; rfl

theorem reqRun_messageFrames (k : StreamKind) (interim : List UInt8 → Bool) (p : Parts)
    (hp : p.header = [] ∧ p.content = [] ∧ p.trailer = none)
    (h : List UInt8) (hh : k = .request ∨ interim h = false)
    (chunks : List (List UInt8)) (t : Option (List UInt8)) :
    reqRun k interim { phase := .awaitHeaders, parts := p } (messageFrames h chunks t) =
      .ok { phase := if t.isSome then .done else .body,
            parts := { p with header := h, content := chunks.flatten, trailer := t } } := by
  obtain ⟨_, hc, ht⟩ := hp
  have h1 : reqStep k interim { phase := .awaitHeaders, parts := p } (.headers h) =
      .ok { phase := .body, parts := { p with header := h } } := by
    simp only [reqStep]
    rcases hh with rfl | hh
    · simp
    · simp [hh]
  have h2 := reqRun_data k interim chunks { p with header := h }
  unfold messageFrames
  simp only [List.cons_append, reqRun, List.foldlM_cons, h1, bind, Except.bind]
  rw [← reqRun, reqRun_append h2]
  cases t with
  | none => simp [reqRun, pure, Except.pure, ht, hc]
  | some tr =>
    simp [reqRun, reqStep, bind, Except.bind, pure, Except.pure, hc]

theorem reqRun_interim (interim : List UInt8 → Bool) (k : StreamKind) (hk : k ≠ .request) :
    ∀ (is : List (List UInt8)) (p : Parts), (∀ i ∈ is, interim i = true) →
      reqRun k interim { phase := .awaitHeaders, parts := p } (is.map .headers) =
        .ok { phase := .awaitHeaders, parts := { p with interim := p.interim ++ is } } := by
  intro is
  induction is with
  | nil => intro p _; simp [reqRun, pure, Except.pure]
  | cons i is ih =>
    intro p hi
    simp only [List.map_cons, reqRun, List.foldlM_cons, reqStep, hk, ne_eq, not_false_eq_true,
      hi i (by simp), and_self, ↓reduceIte, bind, Except.bind]
    rw [← reqRun, ih _ (fun j hj => hi j (by simp [hj]))]
    simp [List.append_assoc]

/-- The request-stream invariant: the non-unknown frames read so far are a prefix of
`messageFrames` matching the state. -/
def Inv (s : ReqState) (ys : List Frame) : Prop :=
  s.parts.interim = [] ∧ s.parts.promises = [] ∧
  match s.phase with
  | .awaitHeaders => ys = [] ∧ s.parts.content = [] ∧ s.parts.trailer = none
  | .body => ∃ chunks, ys = messageFrames s.parts.header chunks none ∧
      chunks.flatten = s.parts.content ∧ s.parts.trailer = none
  | .done => ∃ chunks t, ys = messageFrames s.parts.header chunks (some t) ∧
      chunks.flatten = s.parts.content ∧ s.parts.trailer = some t

theorem inv_step {interim : List UInt8 → Bool} {s s' : ReqState} {ys : List Frame} {f : Frame}
    (hi : Inv s ys) (h : reqStep .request interim s f = .ok s') :
    Inv s' (ys ++ [f].filter fun f => !f.isUnknown) := by
  obtain ⟨hint, hprom, hph⟩ := hi
  obtain ⟨phase, parts⟩ := s
  cases f with
  | headers hd =>
    simp only [reqStep] at h
    cases phase with
    | awaitHeaders =>
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Except.ok.injEq] at h
      subst h
      obtain ⟨rfl, hc, ht⟩ := hph
      refine ⟨hint, hprom, [], ?_, ?_, ht⟩
      · simp [messageFrames, Frame.isUnknown]
      · exact hc.symm
    | body =>
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨chunks, rfl, hc, ht⟩ := hph
      refine ⟨hint, hprom, chunks, hd, ?_, hc, rfl⟩
      simp [messageFrames, Frame.isUnknown]
    | done => cases h
  | data d =>
    simp only [reqStep] at h
    cases phase with
    | body =>
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨chunks, rfl, hc, ht⟩ := hph
      refine ⟨hint, hprom, chunks ++ [d], ?_, ?_, ht⟩
      · simp [messageFrames, Frame.isUnknown]
      · simp [hc]
    | awaitHeaders => cases h
    | done => cases h
  | pushPromise p hd => simp [reqStep] at h
  | unknown t b =>
    simp only [reqStep, Except.ok.injEq] at h
    subst h
    simpa [Frame.isUnknown] using ⟨hint, hprom, hph⟩
  | settings _ | cancelPush _ | goaway _ | maxPushId _ | h2Reserved _ _ => cases h

theorem inv_run {interim : List UInt8 → Bool} :
    ∀ (fs : List Frame) (s s' : ReqState) (ys : List Frame), Inv s ys →
      reqRun .request interim s fs = .ok s' → Inv s' (ys ++ fs.filter fun f => !f.isUnknown) := by
  intro fs
  induction fs with
  | nil => intro s s' ys hi h; simp only [reqRun, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simpa using hi
  | cons f fs ih =>
    intro s s' ys hi h
    obtain ⟨s1, h1, h2⟩ := foldlM_cons_ok.1 h
    have := ih s1 s' _ (inv_step hi h1) h2
    rw [List.append_assoc, ← List.filter_append] at this
    simpa using this

theorem request_sound {interim : List UInt8 → Bool} {fs : List Frame} {s : ReqState} {p : Parts}
    (h : reqRun .request interim {} fs = .ok s) (hf : reqFinish .request s = .ok p) :
    ∃ chunks, fs.filter (fun f => !f.isUnknown) = messageFrames p.header chunks p.trailer ∧
      chunks.flatten = p.content ∧ p.interim = [] ∧ p.promises = [] := by
  have hi := inv_run fs {} s [] ⟨rfl, rfl, rfl, rfl, rfl⟩ h
  simp only [List.nil_append] at hi
  obtain ⟨hint, hprom, hph⟩ := hi
  unfold reqFinish at hf
  split at hf
  · cases hf
  · rename_i hphase
    simp only [Except.ok.injEq] at hf
    subst hf
    revert hph
    cases hs : s.phase with
    | awaitHeaders => exact absurd hs hphase
    | body =>
      intro hph; simp only at hph
      obtain ⟨chunks, h1, h2, h3⟩ := hph
      exact ⟨chunks, by rw [h1, h3], h2, hint, hprom⟩
    | done =>
      intro hph; simp only at hph
      obtain ⟨chunks, t, h1, h2, h3⟩ := hph
      exact ⟨chunks, by rw [h1, h3], h2, hint, hprom⟩

/-! ## Bytes to frames -/

theorem mapM_ofRaw_toRaw : ∀ (fs : List Frame), (∀ f ∈ fs, f.Valid) →
    (fs.map Frame.toRaw).mapM Frame.ofRaw = .ok fs := by
  intro fs
  induction fs with
  | nil => intro _; rfl
  | cons f fs ih =>
    intro hv
    simp only [List.map_cons, List.mapM_cons, ofRaw_toRaw (hv f (by simp)),
      ih (fun g hg => hv g (by simp [hg]))]
    rfl

theorem decodeFrames_encode {maxPayload : Nat} (fs : List Frame)
    (hv : ∀ f ∈ fs, f.Valid ∧ f.toRaw.payload.length ≤ maxPayload) :
    decodeFrames maxPayload (fs.flatMap Frame.encode) = .ok fs := by
  have e : fs.flatMap Frame.encode = (fs.map Frame.toRaw).flatMap encodeRaw := by
    simp only [List.flatMap_map]; rfl
  have hr := readRawAll_flatMap (maxPayload := maxPayload) (fs.map Frame.toRaw) (by
    intro r hr
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hr
    exact ⟨toRaw_valid (hv f hf).1, (hv f hf).2⟩)
  unfold decodeFrames
  rw [e, hr]
  simp only [mapM_ofRaw_toRaw fs (fun f hf => (hv f hf).1)]

end Silmaril.Proofs.Net.Http3.Stream
