module

public import Silmaril.Net.Qpack.State.Defs
public import Silmaril.Proofs.Net.Qpack.Section

/-!
# QPACK connection state: proofs

For `Silmaril.Net.Qpack.State.Thms` (RFC 9204 §2.1, §2.2).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Qpack

open Silmaril.Net.Qpack
open Silmaril.Net.Hpack (Entry)

/-! ## Distinct elements and a pigeonhole bound -/

theorem mem_distinct {x : Nat} {l : List Nat} : x ∈ distinct l ↔ x ∈ l := by
  induction l with
  | nil => simp [distinct]
  | cons y ys ih =>
    simp only [distinct]
    split
    · next hy =>
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact ih.mp hy
        · exact h
    · rw [List.mem_cons, ih, List.mem_cons]

theorem nodup_distinct (l : List Nat) : (distinct l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons y ys ih =>
    simp only [distinct]
    split
    · exact ih
    · next hy => exact List.nodup_cons.mpr ⟨hy, ih⟩

/-- A duplicate-free list contained in another is no longer. -/
theorem length_le_of_subset {l₁ l₂ : List Nat} (hn : l₁.Nodup) (hs : ∀ x ∈ l₁, x ∈ l₂) :
    l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hn
    have hmem : x ∈ l₂ := hs x (List.mem_cons_self ..)
    have := ih hxs (l₂ := l₂.erase x) fun y hy => by
      have hne : y ≠ x := fun h => hx (h ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hs y (List.mem_cons_of_mem _ hy))
    rw [List.length_erase_of_mem hmem] at this
    have : 0 < l₂.length := List.length_pos_of_mem hmem
    simp only [List.length_cons]; omega

theorem distinct_length_le {l₁ l₂ : List Nat} (hs : ∀ x ∈ l₁, x ∈ l₂) :
    (distinct l₁).length ≤ (distinct l₂).length :=
  length_le_of_subset (nodup_distinct l₁) fun x hx => mem_distinct.mpr (hs x (mem_distinct.mp hx))

theorem removeFirst_spec {p : Outstanding → Bool} {l l' : List Outstanding} {y : Outstanding}
    (h : removeFirst p l = some (y, l')) : y ∈ l ∧ ∀ z ∈ l', z ∈ l := by
  induction l generalizing l' with
  | nil => cases h
  | cons x xs ih =>
    simp only [removeFirst] at h
    split at h
    · cases h; exact ⟨List.mem_cons_self .., fun z hz => List.mem_cons_of_mem _ hz⟩
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨⟨y', ys⟩, hr, rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := ih hr
      refine ⟨List.mem_cons_of_mem _ h1, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (h2 z hz)

/-! ## Encoder -/

namespace Encoder

theorem init_valid (m b : Nat) : (Encoder.init m b).Valid := by
  refine ⟨DynTable.empty_valid m, Nat.le_refl _, ?_, ?_⟩
  · intro s hs; simp [Encoder.init] at hs
  · intro a ha
    rcases ha with ⟨-, h2⟩ | ha
    · exact absurd h2 (Nat.not_lt_zero _)
    · simp [Encoder.init, Encoder.refs] at ha

theorem mem_refs_of_subset {enc enc' : Encoder} (hp : ∀ o ∈ enc'.pending, o ∈ enc.pending)
    {a : Nat} (ha : a ∈ enc'.refs) : a ∈ enc.refs := by
  simp only [Encoder.refs, List.mem_flatMap] at ha ⊢
  obtain ⟨o, ho, ha⟩ := ha
  exact ⟨o, hp o ho, ha⟩

theorem blockingStreams_length_le {enc enc' : Encoder}
    (hp : ∀ o ∈ enc'.pending, o ∈ enc.pending) (hk : enc.krc ≤ enc'.krc) :
    (Encoder.blockingStreams enc').length ≤ (Encoder.blockingStreams enc).length := by
  apply distinct_length_le
  intro x hx
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hx ⊢
  obtain ⟨o, ⟨ho, hr⟩, rfl⟩ := hx
  exact ⟨o, ⟨hp o ho, by omega⟩, rfl⟩

theorem applyInstr_eq {enc enc' : Encoder} {i : EncoderInstr} (h : enc.applyInstr i = some enc') :
    ∃ t', enc.table.applyInstr i = .ok t' ∧ enc.evictionOk t' = true ∧
      enc' = { enc with table := t' } := by
  unfold Encoder.applyInstr at h
  split at h
  · next t' ht' =>
    split at h
    · next hg => cases h; exact ⟨t', ht', hg, rfl⟩
    · cases h
  · cases h

theorem applyInstr_valid {enc enc' : Encoder} (hv : enc.Valid) {i : EncoderInstr}
    (h : enc.applyInstr i = some enc') : enc'.Valid := by
  obtain ⟨t', ht', hg, rfl⟩ := applyInstr_eq h
  obtain ⟨htv, hkrc, hpend, hsafe⟩ := hv
  have hic := DynTable.applyInstr_insertCount ht'
  have hdr : enc.table.dropped ≤ t'.dropped ∧ t'.dropped ≤ enc.table.insertCount := by
    rcases DynTable.applyInstr_cases ht' with ⟨e, he⟩ | ⟨c, hc⟩
    · exact DynTable.insert_dropped he
    · exact DynTable.setCapacity_dropped hc
  have hguard : ∀ a, enc.table.dropped ≤ a → a < t'.dropped → a < enc.krc ∧ a ∉ enc.refs := by
    intro a h1 h2
    have := List.all_eq_true.mp hg a (List.mem_range'_1.mpr ⟨h1, by omega⟩)
    simpa using this
  refine ⟨DynTable.applyInstr_valid htv ht', Nat.le_trans hkrc hic,
    fun s hs => ⟨Nat.le_trans (hpend s hs).1 hic, (hpend s hs).2⟩, ?_⟩
  intro a ha
  dsimp only [Encoder.Pinned] at ha ⊢
  rw [DynTable.lookupAbs_isSome_iff]
  rcases ha with ⟨h1, h2⟩ | ha
  · show t'.dropped ≤ a ∧ a < t'.insertCount
    refine ⟨?_, h2⟩
    by_cases hlt : a < enc.table.insertCount
    · have hold := (DynTable.lookupAbs_isSome_iff _ _).mp (hsafe a (.inl ⟨h1, hlt⟩))
      by_cases hd : a < t'.dropped
      · have := (hguard a hold.1 hd).1; omega
      · omega
    · omega
  · have hold := (DynTable.lookupAbs_isSome_iff _ _).mp (hsafe a (.inr ha))
    refine ⟨?_, by omega⟩
    by_cases hd : a < t'.dropped
    · exact absurd ha (hguard a hold.1 hd).2
    · omega

theorem applyInstr_blockedOk {enc enc' : Encoder} (hb : enc.BlockedOk) {i : EncoderInstr}
    (h : enc.applyInstr i = some enc') : enc'.BlockedOk := by
  obtain ⟨t', -, -, rfl⟩ := applyInstr_eq h
  exact hb

theorem sendSection_eq {enc enc' : Encoder} {sid ric : Nat} {refs : List Nat}
    (h : enc.sendSection sid ric refs = some enc') :
    (ric = 0 ∧ refs = [] ∧ enc' = enc) ∨
    (ric ≠ 0 ∧ (∀ a ∈ refs, a < ric ∧ (enc.table.lookupAbs a).isSome) ∧
      ric ≤ enc.table.insertCount ∧
      (ric ≤ enc.krc ∨ sid ∈ enc.blockingStreams ∨
        enc.blockingStreams.length < enc.maxBlocked) ∧
      enc' = { enc with pending := enc.pending ++ [⟨sid, ric, refs⟩] }) := by
  unfold Encoder.sendSection at h
  by_cases h0 : ric = 0
  · simp only [h0, ↓reduceIte] at h
    split at h
    · next hr => cases h; exact .inl ⟨h0, hr, rfl⟩
    · cases h
  · simp only [h0, ↓reduceIte] at h
    split at h
    · next hg =>
      cases h
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hg
      obtain ⟨⟨hall, hric⟩, hblk⟩ := hg
      refine .inr ⟨h0, hall, hric, ?_, rfl⟩
      rcases hblk with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · cases h

theorem sendSection_valid {enc enc' : Encoder} (hv : enc.Valid) {sid ric : Nat}
    {refs : List Nat} (h : enc.sendSection sid ric refs = some enc') : enc'.Valid := by
  rcases sendSection_eq h with ⟨-, -, rfl⟩ | ⟨-, hall, hric, -, rfl⟩
  · exact hv
  obtain ⟨htv, hkrc, hpend, hsafe⟩ := hv
  refine ⟨htv, hkrc, ?_, ?_⟩
  · intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hpend s hs
    · rw [List.mem_singleton] at hs
      subst hs
      exact ⟨hric, fun a ha => (hall a ha).1⟩
  · intro a ha
    rcases ha with ha | ha
    · exact hsafe a (.inl ha)
    · simp only [Encoder.refs, List.flatMap_append, List.mem_append] at ha
      rcases ha with ha | ha
      · exact hsafe a (.inr ha)
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at ha
        exact (hall a ha).2

theorem sendSection_blockedOk {enc enc' : Encoder} (hb : enc.BlockedOk) {sid ric : Nat}
    {refs : List Nat} (h : enc.sendSection sid ric refs = some enc') : enc'.BlockedOk := by
  rcases sendSection_eq h with ⟨-, -, rfl⟩ | ⟨-, -, -, hblk, rfl⟩
  · exact hb
  unfold Encoder.BlockedOk at hb ⊢
  simp only [Encoder.blockingStreams] at hb hblk ⊢
  rw [List.filter_append, List.map_append]
  rcases hblk with hk | hs | hlt
  · -- the new section cannot block: same streams
    have : (List.filter (fun s : Outstanding => decide (enc.krc < s.ric))
        [(⟨sid, ric, refs⟩ : Outstanding)]) = [] := by
      simp only [List.filter_cons, List.filter_nil]
      simp only [show ¬ enc.krc < ric by omega, decide_false]; rfl
    rw [this, List.map_nil, List.append_nil]
    exact hb
  · -- the stream is already counted
    refine Nat.le_trans (distinct_length_le ?_) hb
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hx
    · simp only [List.filter_cons, List.filter_nil] at hx
      split at hx
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
        subst hx
        exact mem_distinct.mp hs
      · cases hx
  · -- one more stream, below the limit
    refine Nat.le_trans (length_le_of_subset (nodup_distinct _) (l₂ := sid :: distinct
      ((List.filter (fun s : Outstanding => decide (enc.krc < s.ric)) enc.pending).map
        Outstanding.streamId)) ?_) ?_
    · intro x hx
      have hx := mem_distinct.mp hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_cons_of_mem _ (mem_distinct.mpr hx)
      · simp only [List.filter_cons, List.filter_nil] at hx
        split at hx
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
          subst hx; exact List.mem_cons_self ..
        · cases hx
    · simp only [List.length_cons]; omega

theorem onDecoderInstr_cases {enc enc' : Encoder} {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') :
    (∃ o rest, o ∈ enc.pending ∧ (∀ z ∈ rest, z ∈ enc.pending) ∧
      enc' = { enc with pending := rest, krc := max enc.krc o.ric }) ∨
    (∃ s, enc' = { enc with pending := enc.pending.filter fun o => o.streamId != s }) ∨
    (∃ k, enc.krc + k ≤ enc.table.insertCount ∧ enc' = { enc with krc := enc.krc + k }) := by
  cases i with
  | sectionAck s =>
    simp only [Encoder.onDecoderInstr] at h
    split at h
    · cases h
    · next o rest hr =>
      cases h
      obtain ⟨h1, h2⟩ := removeFirst_spec hr
      exact .inl ⟨o, rest, h1, h2, rfl⟩
  | streamCancel s =>
    simp only [Encoder.onDecoderInstr, Except.ok.injEq] at h
    exact .inr (.inl ⟨s, h.symm⟩)
  | insertCountIncrement k =>
    simp only [Encoder.onDecoderInstr] at h
    split at h
    · cases h
    · next hk =>
      simp only [Except.ok.injEq] at h
      exact .inr (.inr ⟨k, by omega, h.symm⟩)

theorem onDecoderInstr_valid {enc enc' : Encoder} (hv : enc.Valid) {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') : enc'.Valid := by
  obtain ⟨htv, hkrc, hpend, hsafe⟩ := hv
  rcases onDecoderInstr_cases h with ⟨o, rest, ho, hrest, rfl⟩ | ⟨s, rfl⟩ | ⟨k, hk, rfl⟩
  · have hor := (hpend o ho).1
    refine ⟨htv, Nat.max_le.mpr ⟨hkrc, hor⟩, fun s hs => hpend s (hrest s hs), ?_⟩
    intro a ha
    rcases ha with ⟨h1, h2⟩ | ha
    · exact hsafe a (.inl ⟨Nat.le_trans (Nat.le_max_left _ _) h1, h2⟩)
    · exact hsafe a (.inr (mem_refs_of_subset (enc' := { enc with pending := rest }) hrest ha))
  · have hsub : ∀ o ∈ enc.pending.filter (fun o => o.streamId != s), o ∈ enc.pending :=
      fun o ho => (List.mem_filter.mp ho).1
    refine ⟨htv, hkrc, fun s hs => hpend s (hsub s hs), ?_⟩
    intro a ha
    rcases ha with ha | ha
    · exact hsafe a (.inl ha)
    · exact hsafe a (.inr (mem_refs_of_subset
        (enc' := { enc with pending := enc.pending.filter fun o => o.streamId != s }) hsub ha))
  · refine ⟨htv, hk, hpend, ?_⟩
    intro a ha
    rcases ha with ⟨h1, h2⟩ | ha
    · exact hsafe a (.inl ⟨by simp only at h1; omega, h2⟩)
    · exact hsafe a (.inr ha)

theorem onDecoderInstr_krc_mono {enc enc' : Encoder} {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') : enc.krc ≤ enc'.krc := by
  rcases onDecoderInstr_cases h with ⟨o, rest, -, -, rfl⟩ | ⟨s, rfl⟩ | ⟨k, -, rfl⟩
  · exact Nat.le_max_left _ _
  · exact Nat.le_refl _
  · exact Nat.le_add_right _ _

theorem onDecoderInstr_table {enc enc' : Encoder} {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') : enc'.table = enc.table := by
  rcases onDecoderInstr_cases h with ⟨o, rest, -, -, rfl⟩ | ⟨s, rfl⟩ | ⟨k, -, rfl⟩ <;> rfl

theorem onDecoderInstr_blockedOk {enc enc' : Encoder} (hb : enc.BlockedOk) {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') : enc'.BlockedOk := by
  have hk := onDecoderInstr_krc_mono h
  unfold Encoder.BlockedOk at hb ⊢
  rcases onDecoderInstr_cases h with ⟨o, rest, -, hrest, rfl⟩ | ⟨s, rfl⟩ | ⟨k, -, rfl⟩
  · exact Nat.le_trans (blockingStreams_length_le hrest hk) hb
  · exact Nat.le_trans (blockingStreams_length_le (fun o ho => (List.mem_filter.mp ho).1) hk) hb
  · exact Nat.le_trans (blockingStreams_length_le (enc := enc) (fun o ho => ho) hk) hb

theorem onDecoderInstr_error {enc : Encoder} {i : DecoderInstr} {err : QpackError}
    (h : enc.onDecoderInstr i = .error err) : err = .decoderStreamError := by
  cases i with
  | sectionAck s =>
    simp only [Encoder.onDecoderInstr] at h
    split at h
    · cases h; rfl
    · cases h
  | streamCancel s => cases h
  | insertCountIncrement k =>
    simp only [Encoder.onDecoderInstr] at h
    split at h
    · cases h; rfl
    · cases h

theorem onDecoderInstr_increment_error {enc : Encoder} {k : Nat}
    (hk : k = 0 ∨ enc.table.insertCount < enc.krc + k) :
    enc.onDecoderInstr (.insertCountIncrement k) = .error .decoderStreamError := by
  simp only [Encoder.onDecoderInstr, hk, ↓reduceIte]

end Encoder

/-! ## Decoder -/

theorem lookupDyn_error {t : DynTable} {ric a : Nat} {err : QpackError}
    (h : lookupDyn t ric a = .error err) : err = .decompressionFailed := by
  unfold lookupDyn at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h; rfl

theorem resolveRef_error {t : DynTable} {ric base : Nat} {r : Ref} {err : QpackError}
    (h : resolveRef t ric base r = .error err) : err = .decompressionFailed := by
  cases r with
  | static i =>
    simp only [resolveRef] at h
    split at h
    · cases h
    · cases h; rfl
  | dynamic i =>
    simp only [resolveRef] at h
    split at h
    · exact lookupDyn_error h
    · cases h; rfl
  | postBase p => exact lookupDyn_error h

theorem resolveLines_error {t : DynTable} {ric base : Nat} {ls : List FieldLine}
    {err : QpackError} (h : resolveLines t ric base ls = .error err) :
    err = .decompressionFailed := by
  induction ls with
  | nil => cases h
  | cons l ls ih =>
    simp only [resolveLines] at h
    split at h
    · next err' he =>
      cases h
      cases l with
      | indexed r => exact resolveRef_error he
      | literalRef n r v =>
        simp only [FieldLine.resolve] at he
        split at he
        · cases he
        · next e he' => cases he; exact resolveRef_error he'
      | literal n name v => cases he
    · split at h
      · next err' he => cases h; exact ih he
      · cases h

theorem decodeFieldSection_error {t : DynTable} {s : EncodedSection} {err : QpackError}
    (h : decodeFieldSection t s = .error err) : err = .decompressionFailed := by
  unfold decodeFieldSection at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · split at h
      · cases h; rfl
      · split at h
        · cases h
        · next err' he => cases h; exact resolveLines_error he

namespace Decoder

theorem onEncoderInstr_eq {d d' : Decoder} {i : EncoderInstr}
    (h : d.onEncoderInstr i = .ok d') : ∃ t', d.table.applyInstr i = .ok t' ∧
      d' = { d with table := t' } := by
  unfold Decoder.onEncoderInstr at h
  split at h
  · next t' ht' => cases h; exact ⟨t', ht', rfl⟩
  · cases h

theorem onEncoderInstr_valid {d d' : Decoder} (hv : d.Valid) {i : EncoderInstr}
    (h : d.onEncoderInstr i = .ok d') : d'.Valid := by
  obtain ⟨t', ht', rfl⟩ := onEncoderInstr_eq h
  exact ⟨DynTable.applyInstr_valid hv.1 ht', hv.2.1,
    Nat.le_trans hv.2.2 (DynTable.applyInstr_insertCount ht')⟩

theorem onEncoderInstr_error {d : Decoder} {i : EncoderInstr} {err : QpackError}
    (h : d.onEncoderInstr i = .error err) : err = .encoderStreamError := by
  unfold Decoder.onEncoderInstr at h
  split at h
  · cases h
  · next e he => cases h; exact DynTable.applyInstr_error he

theorem filter_length_le (l : List Nat) (p : Nat → Bool) : (l.filter p).length ≤ l.length :=
  List.length_filter_le p l

theorem onSection_cases {d d' : Decoder} {sid : Nat} {s : EncodedSection}
    {out : Option (List Entry)} {ins : Option DecoderInstr}
    (h : d.onSection sid s = .ok (d', out, ins)) :
    (∃ ric, decodeFieldSection d.table s = .ok (.blocked ric) ∧ out = none ∧ ins = none ∧
      (d' = d ∨ (sid ∉ d.blocked ∧ d.blocked.length < d.maxBlocked ∧
        d' = { d with blocked := sid :: d.blocked }))) ∨
    (∃ ric fs, decodeFieldSection d.table s = .ok (.decoded ric fs) ∧ out = some fs ∧
      ins = (if ric = 0 then none else some (.sectionAck sid)) ∧
      d' = { d with blocked := d.blocked.filter (· != sid), krc := max d.krc ric }) := by
  unfold Decoder.onSection at h
  split at h
  · cases h
  · next ric hd =>
    split at h
    · cases h; exact .inl ⟨ric, hd, rfl, rfl, .inl rfl⟩
    · next hm =>
      split at h
      · next hl => cases h; exact .inl ⟨ric, hd, rfl, rfl, .inr ⟨hm, hl, rfl⟩⟩
      · cases h
  · next ric fs hd =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .inr ⟨ric, fs, hd, rfl, rfl, rfl⟩

theorem onSection_valid {d d' : Decoder} (hv : d.Valid) {sid : Nat} {s : EncodedSection}
    {out : Option (List Entry)} {ins : Option DecoderInstr}
    (h : d.onSection sid s = .ok (d', out, ins)) : d'.Valid := by
  obtain ⟨htv, hb, hk⟩ := hv
  rcases onSection_cases h with ⟨ric, -, -, -, rfl | ⟨-, hl, rfl⟩⟩ | ⟨ric, fs, hd, -, -, rfl⟩
  · exact ⟨htv, hb, hk⟩
  · exact ⟨htv, by simp only [List.length_cons]; omega, hk⟩
  · have := decodeFieldSection_decoded hd
    exact ⟨htv, Nat.le_trans (filter_length_le _ _) hb, Nat.max_le.mpr ⟨hk, this.2.1⟩⟩

theorem onSection_krc_mono {d d' : Decoder} {sid : Nat} {s : EncodedSection}
    {out : Option (List Entry)} {ins : Option DecoderInstr}
    (h : d.onSection sid s = .ok (d', out, ins)) : d.krc ≤ d'.krc := by
  rcases onSection_cases h with ⟨ric, -, -, -, rfl | ⟨-, -, rfl⟩⟩ | ⟨ric, fs, -, -, -, rfl⟩
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

theorem onSection_error {d : Decoder} {sid : Nat} {s : EncodedSection} {err : QpackError}
    (h : d.onSection sid s = .error err) : err = .decompressionFailed := by
  unfold Decoder.onSection at h
  split at h
  · next e he => cases h; exact decodeFieldSection_error he
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl
  · cases h

theorem onSection_too_many_blocked {d : Decoder} {sid : Nat} {s : EncodedSection} {ric : Nat}
    (hd : decodeFieldSection d.table s = .ok (.blocked ric)) (hm : sid ∉ d.blocked)
    (hl : d.maxBlocked ≤ d.blocked.length) :
    d.onSection sid s = .error .decompressionFailed := by
  simp only [Decoder.onSection, hd, hm, ↓reduceIte, show ¬ d.blocked.length < d.maxBlocked by omega]

theorem onSection_ack {d d' : Decoder} {sid : Nat} {s : EncodedSection}
    {out : Option (List Entry)} {ins : Option DecoderInstr}
    (h : d.onSection sid s = .ok (d', out, ins)) :
    ins.isSome ↔ ∃ ric fs, decodeFieldSection d.table s = .ok (.decoded ric fs) ∧ ric ≠ 0 := by
  rcases onSection_cases h with ⟨ric, hd, -, rfl, -⟩ | ⟨ric, fs, hd, -, rfl, -⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro r fs h'; rw [hd] at h'; cases h'
  · constructor
    · intro hs
      refine ⟨ric, fs, hd, fun h0 => ?_⟩
      simp [h0] at hs
    · rintro ⟨r, fs', h', h0⟩
      rw [hd] at h'
      simp only [Except.ok.injEq, SectionResult.decoded.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      simp [h0]

theorem cancelStream_valid {d : Decoder} (hv : d.Valid) (sid : Nat) :
    (d.cancelStream sid).1.Valid :=
  ⟨hv.1, Nat.le_trans (filter_length_le _ _) hv.2.1, hv.2.2⟩

theorem insertCountIncrement_valid {d : Decoder} (hv : d.Valid) :
    d.insertCountIncrement.1.Valid := by
  unfold Decoder.insertCountIncrement
  split
  · exact ⟨hv.1, hv.2.1, Nat.le_refl _⟩
  · exact hv

theorem insertCountIncrement_spec (d : Decoder) {k : Nat}
    (h : d.insertCountIncrement.2 = some (.insertCountIncrement k)) :
    k ≠ 0 ∧ d.krc + k = d.table.insertCount ∧ d.insertCountIncrement.1.krc = d.krc + k := by
  unfold Decoder.insertCountIncrement at h ⊢
  split at h
  · next hlt =>
    simp only [Option.some.injEq, DecoderInstr.insertCountIncrement.injEq] at h
    subst h
    simp only [hlt, ↓reduceIte]
    omega
  · cases h

theorem insertCountIncrement_krc_mono (d : Decoder) : d.krc ≤ d.insertCountIncrement.1.krc := by
  unfold Decoder.insertCountIncrement
  split
  · next h => exact Nat.le_of_lt h
  · exact Nat.le_refl _

end Decoder

/-- An Insert Count Increment emitted by a decoder is accepted by an encoder that agrees on
the Known Received Count and has sent at least the decoder's insertions. -/
theorem increment_accepted {d : Decoder} {enc : Encoder} {k : Nat}
    (h : d.insertCountIncrement.2 = some (.insertCountIncrement k)) (hk : enc.krc = d.krc)
    (hic : d.table.insertCount ≤ enc.table.insertCount) :
    enc.onDecoderInstr (.insertCountIncrement k) = .ok { enc with krc := enc.krc + k } := by
  obtain ⟨hk0, hsum, -⟩ := Decoder.insertCountIncrement_spec d h
  simp only [Encoder.onDecoderInstr,
    show ¬ (k = 0 ∨ enc.table.insertCount < enc.krc + k) by omega, ↓reduceIte]

end Silmaril.Proofs.Net.Qpack
