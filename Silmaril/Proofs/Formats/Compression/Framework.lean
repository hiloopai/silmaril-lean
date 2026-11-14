module

public import Silmaril.Formats.Compression.Defs

/-!
# Proofs of the compression framework laws

Stated in `Silmaril.Formats.Compression.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Formats.Compression

open Silmaril.Formats.Compression

theorem whole_eq_some_iff (d : Decoder) (bytes out : List UInt8) :
    d.whole bytes = some out ↔ d bytes = some (out, []) := by
  unfold Decoder.whole
  split <;> simp_all

theorem roundTrip_whole {d : Decoder} {e : Encoder} (h : RoundTrip d e) (data : List UInt8) :
    d.whole (e data) = some data := by
  rw [whole_eq_some_iff]
  simpa using h data []

theorem roundTrip_injective {d : Decoder} {e : Encoder} (h : RoundTrip d e) :
    Function.Injective e := by
  intro a b hab
  have ha := roundTrip_whole h a
  rw [hab, roundTrip_whole h b] at ha
  exact (Option.some.inj ha).symm

theorem roundTrip_membersFuel {d : Decoder} {e : Encoder} (h : RoundTrip d e)
    (nonempty : ∀ x, e x ≠ []) :
    ∀ (xs : List (List UInt8)), xs ≠ [] → ∀ fuel, xs.length ≤ fuel → ∀ acc,
      d.membersFuel fuel (xs.flatMap e) acc = some (acc ++ xs.flatten)
  | [], hxs, _, _, _ => absurd rfl hxs
  | x :: xs, _, fuel, hfuel, acc => by
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    rw [List.flatMap_cons, Decoder.membersFuel, h x]
    cases xs with
    | nil => simp
    | cons y ys =>
      have hrest : (y :: ys).flatMap e ≠ [] := by
        rw [List.flatMap_cons]; exact fun hn => nonempty y (List.append_eq_nil_iff.mp hn).1
      have ih := roundTrip_membersFuel h nonempty (y :: ys) (by simp) fuel
        (by simp at hfuel ⊢; omega) (acc ++ x)
      revert hrest ih
      generalize (y :: ys).flatMap e = r
      intro hrest ih
      cases r with
      | nil => exact absurd rfl hrest
      | cons b bs => simpa [Decoder.membersFuel] using ih

theorem roundTrip_members {d : Decoder} {e : Encoder} (h : RoundTrip d e)
    (nonempty : ∀ x, e x ≠ []) {xs : List (List UInt8)} (hxs : xs ≠ []) :
    d.members (xs.flatMap e) = some xs.flatten := by
  unfold Decoder.members
  rw [roundTrip_membersFuel h nonempty xs hxs]
  · simp
  · have : xs.length ≤ (xs.flatMap e).length := by
      induction xs with
      | nil => simp
      | cons x xs ih =>
        rw [List.flatMap_cons, List.length_append, List.length_cons]
        have hx : 0 < (e x).length := List.length_pos_iff.mpr (nonempty x)
        cases xs with
        | nil => simp; omega
        | cons y ys => have := ih (by simp); omega
    omega

namespace Framing

variable {H : Type}

theorem wrap_spec {f : Framing H} {body : Decoder} {bytes out rest : List UInt8}
    (hw : f.wrap body bytes = some (out, rest)) :
    ∃ h afterHeader afterBody, f.header bytes = some (h, afterHeader) ∧
      body afterHeader = some (out, afterBody) ∧ f.trailer h out afterBody = some rest := by
  unfold Framing.wrap at hw
  split at hw
  · simp at hw
  · rename_i h afterHeader hh
    split at hw
    · simp at hw
    · rename_i out' afterBody hb
      split at hw
      · simp at hw
      · rename_i rest' ht
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact ⟨h, afterHeader, afterBody, hh, hb, ht⟩

theorem wrap_eq {f : Framing H} {body : Decoder} {bytes afterHeader afterBody out rest : List UInt8}
    {h : H} (hh : f.header bytes = some (h, afterHeader))
    (hb : body afterHeader = some (out, afterBody)) (ht : f.trailer h out afterBody = some rest) :
    f.wrap body bytes = some (out, rest) := by
  simp [Framing.wrap, hh, hb, ht]

theorem wrap_consumes {f : Framing H} {body : Decoder} (hf : f.Consumes)
    (hb : body.Consumes) : (f.wrap body).Consumes := by
  intro bytes out rest hw
  obtain ⟨h, a, b, hh, hbody, ht⟩ := wrap_spec hw
  exact (hf.2 ht).trans ((hb hbody).trans (hf.1 hh))

theorem wrap_local {f : Framing H} {body : Decoder} (hf : f.Local) (hb : body.Local) :
    (f.wrap body).Local := by
  intro bytes out rest tail hw
  obtain ⟨h, a, b, hh, hbody, ht⟩ := wrap_spec hw
  exact wrap_eq (hf.1 tail hh) (hb tail hbody) (hf.2 tail ht)

theorem wrap_trailer {f : Framing H} {body : Decoder} {spec : List UInt8 → List UInt8}
    (hf : f.Consumes) (hb : body.Consumes) (hs : f.TrailerIs spec)
    {bytes out rest : List UInt8} (hw : f.wrap body bytes = some (out, rest)) :
    ∃ pre, bytes = pre ++ (spec out ++ rest) := by
  obtain ⟨h, a, b, hh, hbody, ht⟩ := wrap_spec hw
  obtain ⟨p, rfl⟩ := hf.1 hh
  obtain ⟨q, rfl⟩ := hb hbody
  refine ⟨p ++ q, ?_⟩
  rw [hs ht, List.append_assoc]

theorem wrap_roundTrip {f : Framing H} {body : Decoder} {e : Encoder} {hdr : List UInt8}
    {trl : List UInt8 → List UInt8} (hf : f.Writes hdr trl) (hb : RoundTrip body e) :
    RoundTrip (f.wrap body) (Framing.encode hdr e trl) := by
  intro data rest
  obtain ⟨h, hh, ht⟩ := hf (e data ++ (trl data ++ rest))
  have hbytes : Framing.encode hdr e trl data ++ rest = hdr ++ (e data ++ (trl data ++ rest)) := by
    simp [Framing.encode]
  rw [hbytes]
  exact wrap_eq hh (hb data (trl data ++ rest)) (ht data rest)

theorem wrap_eq_wrapDep (f : Framing H) (body : Decoder) : f.wrap body = f.wrapDep fun _ => body :=
  rfl

theorem wrapDep_spec {f : Framing H} {body : H → Decoder} {bytes out rest : List UInt8}
    (hw : f.wrapDep body bytes = some (out, rest)) :
    ∃ h afterHeader afterBody, f.header bytes = some (h, afterHeader) ∧
      body h afterHeader = some (out, afterBody) ∧ f.trailer h out afterBody = some rest := by
  unfold Framing.wrapDep at hw
  split at hw
  · simp at hw
  · rename_i h afterHeader hh
    split at hw
    · simp at hw
    · rename_i out' afterBody hb
      split at hw
      · simp at hw
      · rename_i rest' ht
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact ⟨h, afterHeader, afterBody, hh, hb, ht⟩

theorem wrapDep_eq {f : Framing H} {body : H → Decoder}
    {bytes afterHeader afterBody out rest : List UInt8} {h : H}
    (hh : f.header bytes = some (h, afterHeader)) (hb : body h afterHeader = some (out, afterBody))
    (ht : f.trailer h out afterBody = some rest) : f.wrapDep body bytes = some (out, rest) := by
  simp [Framing.wrapDep, hh, hb, ht]

theorem wrapDep_consumes {f : Framing H} {body : H → Decoder} (hf : f.Consumes)
    (hb : ∀ h, (body h).Consumes) : (f.wrapDep body).Consumes := by
  intro bytes out rest hw
  obtain ⟨h, a, b, hh, hbody, ht⟩ := wrapDep_spec hw
  exact (hf.2 ht).trans ((hb h hbody).trans (hf.1 hh))

theorem wrapDep_local {f : Framing H} {body : H → Decoder} (hf : f.Local)
    (hb : ∀ h, (body h).Local) : (f.wrapDep body).Local := by
  intro bytes out rest tail hw
  obtain ⟨h, a, b, hh, hbody, ht⟩ := wrapDep_spec hw
  exact wrapDep_eq (hf.1 tail hh) (hb h tail hbody) (hf.2 tail ht)

theorem wrapDep_trailer {f : Framing H} {body : H → Decoder} {spec : List UInt8 → List UInt8}
    (hf : f.Consumes) (hb : ∀ h, (body h).Consumes) (hs : f.TrailerIs spec)
    {bytes out rest : List UInt8} (hw : f.wrapDep body bytes = some (out, rest)) :
    ∃ pre, bytes = pre ++ (spec out ++ rest) := by
  obtain ⟨h, a, b, hh, hbody, ht⟩ := wrapDep_spec hw
  obtain ⟨p, rfl⟩ := hf.1 hh
  obtain ⟨q, rfl⟩ := hb h hbody
  refine ⟨p ++ q, ?_⟩
  rw [hs ht, List.append_assoc]

theorem wrapDep_roundTrip {f : Framing H} {body : H → Decoder} {e : Encoder} {hdr : List UInt8}
    {h : H} {trl : List UInt8 → List UInt8} (hf : f.WritesAt hdr h trl)
    (hb : RoundTrip (body h) e) : RoundTrip (f.wrapDep body) (Framing.encode hdr e trl) := by
  intro data rest
  have hbytes : Framing.encode hdr e trl data ++ rest = hdr ++ (e data ++ (trl data ++ rest)) := by
    simp [Framing.encode]
  rw [hbytes]
  exact wrapDep_eq (hf.1 _) (hb data (trl data ++ rest)) (hf.2 data rest)

theorem wrapDep_outputLinear {f : Framing H} {body : H → Decoder} {k : Nat} (hf : f.Consumes)
    (hc : ∀ h, (body h).Consumes) (hb : ∀ h, (body h).OutputLinear k) :
    (f.wrapDep body).OutputLinear k := by
  intro bytes out rest hw
  obtain ⟨h, a, b, hh, hbody, ht⟩ := wrapDep_spec hw
  have h₁ := (hf.1 hh).length_le
  have h₂ := (hc h hbody).length_le
  have h₃ := (hf.2 ht).length_le
  exact Nat.le_trans (hb h hbody) (Nat.mul_le_mul_left k (by omega))

end Framing

namespace Decoder

/-- Whole-buffer decoding inherits a linear output bound. -/
theorem whole_outputLinear {d : Decoder} {k : Nat} (hd : d.OutputLinear k) {bytes out : List UInt8}
    (h : d.whole bytes = some out) : out.length ≤ k * bytes.length := by
  have := hd ((whole_eq_some_iff d bytes out).mp h)
  simpa using this

theorem membersFuel_outputLinear {d : Decoder} {k : Nat} (hc : d.Consumes) (hd : d.OutputLinear k) :
    ∀ (fuel : Nat) (bytes acc out : List UInt8), d.membersFuel fuel bytes acc = some out →
      out.length ≤ acc.length + k * bytes.length
  | 0, _, _, _, h => by simp [Decoder.membersFuel] at h
  | fuel + 1, bytes, acc, out, h => by
    unfold Decoder.membersFuel at h
    split at h
    · simp at h
    · rename_i o hdo
      simp only [Option.some.injEq] at h
      subst h
      have := hd hdo
      simp only [List.length_append, List.length_nil, Nat.sub_zero] at this ⊢
      omega
    · rename_i o r hne hdo
      have ih := membersFuel_outputLinear hc hd fuel r (acc ++ o) out h
      have hb := hd hdo
      have hle := (hc hdo).length_le
      have hsplit : k * (bytes.length - r.length) + k * r.length = k * bytes.length := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hle]
      simp only [List.length_append] at ih
      omega

/-- A multi-member file inherits a linear output bound from its members. -/
theorem members_outputLinear {d : Decoder} {k : Nat} (hc : d.Consumes) (hd : d.OutputLinear k)
    {bytes out : List UInt8} (h : d.members bytes = some out) : out.length ≤ k * bytes.length := by
  have := membersFuel_outputLinear hc hd _ bytes [] out h
  simpa using this

/-- A whole buffer encoded by a round-tripping encoder is a one-member file. -/
theorem roundTrip_members_single {d : Decoder} {e : Encoder} (h : RoundTrip d e)
    (data : List UInt8) : d.members (e data) = some data := by
  have := h data []
  simp only [List.append_nil] at this
  simp [Decoder.members, Decoder.membersFuel, this]

end Decoder

namespace Incremental

theorem sound_decode {i : Incremental} {d : Decoder} (hs : i.Sound d) {initial : List UInt8}
    {calls : List i.Call} {out : List UInt8}
    (hdone : i.status (i.run (i.start initial) calls) = .done out) :
    ∃ rest, d (initial ++ i.delivered calls) = some (out, rest) := by
  obtain ⟨rest, h⟩ := hs initial calls out hdone
  exact ⟨rest, by simpa using h []⟩

theorem sound_agree {i : Incremental} {d : Decoder} (hs : i.Sound d)
    {i₁ i₂ : List UInt8} {c₁ c₂ : List i.Call} {o₁ o₂ : List UInt8}
    (h₁ : i.status (i.run (i.start i₁) c₁) = .done o₁)
    (h₂ : i.status (i.run (i.start i₂) c₂) = .done o₂)
    (same : i₁ ++ i.delivered c₁ = i₂ ++ i.delivered c₂) : o₁ = o₂ := by
  obtain ⟨r₁, e₁⟩ := sound_decode hs h₁
  obtain ⟨r₂, e₂⟩ := sound_decode hs h₂
  rw [same, e₂] at e₁
  exact (Prod.mk.inj (Option.some.inj e₁)).1.symm

theorem local_of_sound_complete {i : Incremental} {d : Decoder} (hs : i.Sound d)
    (hc : i.Complete d) : d.Local := by
  intro bytes out rest tail hd
  obtain ⟨calls, hnil, hdone⟩ := hc hd
  obtain ⟨rest', h⟩ := hs bytes calls out hdone
  have h₀ := h []
  have h₁ := h tail
  simp only [hnil, List.append_nil] at h₀ h₁
  rw [hd] at h₀
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h₀)
  exact h₁

end Incremental

end Silmaril.Proofs.Formats.Compression
