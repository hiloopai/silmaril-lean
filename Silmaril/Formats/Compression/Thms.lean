module

public import Silmaril.Formats.Compression.Defs
import Silmaril.Proofs.Formats.Compression.Framework

/-!
# Lossless compression: framework laws

All proved (standard axioms), for every decoder, encoder, container and
streaming decoder:

* `Decoder.decodes_functional`: a compressed stream has at most one meaning;
* `RoundTrip.whole`, `RoundTrip.surjective`, `RoundTrip.injective`: a
  round-tripping encoder makes the format total on data, and is itself lossless;
* `RoundTrip.members`: concatenated encodings decode to the concatenated data
  (multi-member files);
* `Framing.wrap_consumes`, `Framing.wrap_local`, `Framing.wrap_trailer`,
  `Framing.wrap_roundTrip`: a container inherits the member laws of its header,
  body and trailer, and its encoder round-trips;
* `Framing.wrap_eq_wrapDep`, `Framing.wrapDep_consumes`, `wrapDep_local`,
  `wrapDep_trailer`, `wrapDep_roundTrip`, `wrapDep_outputLinear`: the same laws
  when the body decoder depends on the header metadata (`wrap` is the constant
  case);
* `Decoder.whole_outputLinear`, `Decoder.members_outputLinear`,
  `RoundTrip.members_single`: linear output bounds and round trips carry over
  to whole buffers and multi-member files;
* `Checksum.digest_append`: check values are computed incrementally;
* `Incremental.sound_decode`, `Incremental.sound_agree`: a finished streaming
  run decodes the offered input, so finished runs agree however the input was
  split into calls; `Incremental.local_of_sound_complete`: a sound and complete
  streaming decoder makes its member decoder `Local`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

namespace Decoder

theorem whole_eq_some_iff (d : Decoder) (bytes out : List UInt8) :
    d.whole bytes = some out ↔ d bytes = some (out, []) :=
  Proofs.Formats.Compression.whole_eq_some_iff d bytes out

theorem decodes_functional {d : Decoder} {c a b : List UInt8} (ha : d.Decodes c a)
    (hb : d.Decodes c b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

theorem whole_outputLinear {d : Decoder} {k : Nat} (hd : d.OutputLinear k) {bytes out : List UInt8}
    (h : d.whole bytes = some out) : out.length ≤ k * bytes.length :=
  Proofs.Formats.Compression.Decoder.whole_outputLinear hd h

/-- A multi-member file of members that consume prefixes inherits their linear
output bound. -/
theorem members_outputLinear {d : Decoder} {k : Nat} (hc : d.Consumes) (hd : d.OutputLinear k)
    {bytes out : List UInt8} (h : d.members bytes = some out) : out.length ≤ k * bytes.length :=
  Proofs.Formats.Compression.Decoder.members_outputLinear hc hd h

end Decoder

namespace RoundTrip

variable {d : Decoder} {e : Encoder}

theorem whole (h : RoundTrip d e) (data : List UInt8) : d.whole (e data) = some data :=
  Proofs.Formats.Compression.roundTrip_whole h data

theorem surjective (h : RoundTrip d e) (data : List UInt8) : ∃ c, d.Decodes c data :=
  ⟨e data, h.whole data⟩

theorem injective (h : RoundTrip d e) : Function.Injective e :=
  Proofs.Formats.Compression.roundTrip_injective h

/-- Concatenated encodings are a multi-member file of the concatenated data. -/
theorem members (h : RoundTrip d e) (nonempty : ∀ x, e x ≠ []) {xs : List (List UInt8)}
    (hxs : xs ≠ []) : d.members (xs.flatMap e) = some xs.flatten :=
  Proofs.Formats.Compression.roundTrip_members h nonempty hxs

/-- One encoded buffer is a one-member file. -/
theorem members_single (h : RoundTrip d e) (data : List UInt8) : d.members (e data) = some data :=
  Proofs.Formats.Compression.Decoder.roundTrip_members_single h data

end RoundTrip

namespace Framing

variable {H : Type} {f : Framing H} {body : Decoder}

theorem wrap_consumes (hf : f.Consumes) (hb : body.Consumes) : (f.wrap body).Consumes :=
  Proofs.Formats.Compression.Framing.wrap_consumes hf hb

theorem wrap_local (hf : f.Local) (hb : body.Local) : (f.wrap body).Local :=
  Proofs.Formats.Compression.Framing.wrap_local hf hb

/-- A decoded container member ends with the trailer of its output, followed by
the untouched rest. -/
theorem wrap_trailer {spec : List UInt8 → List UInt8} (hf : f.Consumes) (hb : body.Consumes)
    (hs : f.TrailerIs spec) {bytes out rest : List UInt8}
    (hw : f.wrap body bytes = some (out, rest)) : ∃ pre, bytes = pre ++ (spec out ++ rest) :=
  Proofs.Formats.Compression.Framing.wrap_trailer hf hb hs hw

theorem wrap_roundTrip {e : Encoder} {hdr : List UInt8} {trl : List UInt8 → List UInt8}
    (hf : f.Writes hdr trl) (hb : RoundTrip body e) :
    RoundTrip (f.wrap body) (Framing.encode hdr e trl) :=
  Proofs.Formats.Compression.Framing.wrap_roundTrip hf hb

/-- A fixed body is the constant case of a header-dependent one. -/
theorem wrap_eq_wrapDep (f : Framing H) (body : Decoder) : f.wrap body = f.wrapDep fun _ => body :=
  rfl

section Dep

variable {body : H → Decoder}

theorem wrapDep_consumes (hf : f.Consumes) (hb : ∀ h, (body h).Consumes) :
    (f.wrapDep body).Consumes :=
  Proofs.Formats.Compression.Framing.wrapDep_consumes hf hb

theorem wrapDep_local (hf : f.Local) (hb : ∀ h, (body h).Local) : (f.wrapDep body).Local :=
  Proofs.Formats.Compression.Framing.wrapDep_local hf hb

theorem wrapDep_trailer {spec : List UInt8 → List UInt8} (hf : f.Consumes)
    (hb : ∀ h, (body h).Consumes) (hs : f.TrailerIs spec) {bytes out rest : List UInt8}
    (hw : f.wrapDep body bytes = some (out, rest)) : ∃ pre, bytes = pre ++ (spec out ++ rest) :=
  Proofs.Formats.Compression.Framing.wrapDep_trailer hf hb hs hw

/-- An encoder that writes a header with metadata `h` and a body for `body h`
round-trips. -/
theorem wrapDep_roundTrip {e : Encoder} {hdr : List UInt8} {h : H} {trl : List UInt8 → List UInt8}
    (hf : f.WritesAt hdr h trl) (hb : RoundTrip (body h) e) :
    RoundTrip (f.wrapDep body) (Framing.encode hdr e trl) :=
  Proofs.Formats.Compression.Framing.wrapDep_roundTrip hf hb

/-- A container adds no output: its members obey the bodies' linear bound. -/
theorem wrapDep_outputLinear {k : Nat} (hf : f.Consumes) (hc : ∀ h, (body h).Consumes)
    (hb : ∀ h, (body h).OutputLinear k) : (f.wrapDep body).OutputLinear k :=
  Proofs.Formats.Compression.Framing.wrapDep_outputLinear hf hc hb

end Dep

end Framing

theorem Checksum.digest_append (c : Checksum) (a b : List UInt8) :
    c.digest (a ++ b) = c.finish (b.foldl c.update (a.foldl c.update c.init)) := by
  simp [Checksum.digest, List.foldl_append]

namespace Incremental

variable {i : Incremental} {d : Decoder}

theorem sound_decode (hs : i.Sound d) {initial : List UInt8} {calls : List i.Call}
    {out : List UInt8} (hdone : i.status (i.run (i.start initial) calls) = .done out) :
    ∃ rest, d (initial ++ i.delivered calls) = some (out, rest) :=
  Proofs.Formats.Compression.Incremental.sound_decode hs hdone

/-- Finished runs on the same logical input agree, however it was split into calls. -/
theorem sound_agree (hs : i.Sound d) {i₁ i₂ : List UInt8} {c₁ c₂ : List i.Call}
    {o₁ o₂ : List UInt8} (h₁ : i.status (i.run (i.start i₁) c₁) = .done o₁)
    (h₂ : i.status (i.run (i.start i₂) c₂) = .done o₂)
    (same : i₁ ++ i.delivered c₁ = i₂ ++ i.delivered c₂) : o₁ = o₂ :=
  Proofs.Formats.Compression.Incremental.sound_agree hs h₁ h₂ same

theorem local_of_sound_complete (hs : i.Sound d) (hc : i.Complete d) : d.Local :=
  Proofs.Formats.Compression.Incremental.local_of_sound_complete hs hc

end Incremental

end Silmaril.Formats.Compression
