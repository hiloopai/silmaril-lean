module

public import Silmaril.Net.Tcp.Header.Defs
public import Silmaril.Net.Tcp.Seq.Thms
public import Silmaril.Net.Ip.Addr.Thms
public import Silmaril.Net.Ip.Checksum.Thms

/-!
# TCP segment header format: theorems

PROVED (standard axioms):

* Options: `decodeOpts_zeros` (padding alone is an empty option list), `decodeOpts_encode`
  (a well-formed option is read back, followed by the rest), **`decodeOpts_optArea`** (the
  option area of well-formed options decodes to them), `optArea_length_mod` (it is a whole
  number of 32-bit words).
* `Ctl.ofByte_toByte`: the control bits survive their octet (all 256 cases).
* **`Header.decode_encode`**: a well-formed header (`Header.WF`) is read back from its octets,
  whatever follows; `Segment.decode_encode`: the same for a segment, whose data is the rest.
* **`Segment.seal_checksumOk`**: a segment sealed for a pair of addresses of one family passes
  the receiver's checksum test; `Segment.seal_some`: sealing succeeds exactly then;
  `Segment.length_withChecksum`: the checksum field does not change the length.

NOT PROVED (by design): `Header.encode (decode l)` need not be `l`. Decoding normalizes: an
explicit End of Option List followed by zeros and the zero padding are the same option area,
and `Opt.nop` placement is kept but `decodeOpts` rejects non-zero octets after End of Option
List. The decoder is sound in the weaker sense that it only accepts what MUST-69 allows.
-/

@[expose] public section

namespace Silmaril.Net.Tcp

open Silmaril.Net.Wire Silmaril.Net.Ip Silmaril.Net.Ip.Checksum

theorem decodeOpts_zeros (n : Nat) : decodeOpts (zeros n) = some [] := by
  cases n with
  | zero => simp [zeros, decodeOpts]
  | succ n =>
    rw [zeros, List.replicate_succ, decodeOpts.eq_def]
    simp

theorem decodeOpts_encode (o : Opt) (ho : o.WF) (rest : List UInt8) :
    decodeOpts (o.encode ++ rest) = (decodeOpts rest).map (o :: ·) := by
  cases o with
  | nop => rw [Opt.encode, List.cons_append, List.nil_append, decodeOpts.eq_def]; simp
  | mss v => rw [Opt.encode, List.cons_append, List.cons_append, decodeOpts.eq_def]; simp [be16]
  | other k d =>
    have hk : 3 ≤ k.toNat := ho.1
    have hd : d.length + 2 < 256 := ho.2
    have hk0 : k ≠ 0 := by intro h; subst h; simp at hk
    have hk1 : k ≠ 1 := by intro h; subst h; simp at hk
    have hk2 : k ≠ 2 := by intro h; subst h; simp at hk
    have hm : (d.length + 2) % 256 = d.length + 2 := Nat.mod_eq_of_lt hd
    rw [Opt.encode, List.cons_append, List.cons_append, decodeOpts.eq_def]
    simp [hk0, hk1, hk2, hm]

theorem Ctl.ofByte_toByte (c : Ctl) : Ctl.ofByte c.toByte = c := by
  cases c with
  | mk a b c d e f g h =>
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;> decide

theorem decodeOpts_pad (os : List Opt) (h : ∀ o ∈ os, o.WF) (n : Nat) :
    decodeOpts (encodeOpts os ++ zeros n) = some os := by
  induction os with
  | nil => simpa [encodeOpts] using decodeOpts_zeros n
  | cons o os ih =>
    have ho : o.WF := h o List.mem_cons_self
    have ht : decodeOpts (encodeOpts os ++ zeros n) = some os :=
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [encodeOpts, List.append_assoc, decodeOpts_encode o ho, ht]
    rfl

theorem decodeOpts_optArea (os : List Opt) (h : ∀ o ∈ os, o.WF) :
    decodeOpts (optArea os) = some os := decodeOpts_pad os h _

theorem optArea_length_mod (os : List Opt) : (optArea os).length % 4 = 0 := by
  simp only [optArea, List.length_append, zeros_length, padLen]
  omega

theorem Header.offByte_div (h : Header) (hw : h.WF) :
    h.offByte.toNat / 16 = h.dataOffset ∧ h.offByte.toNat % 16 = h.rsvd.toNat := by
  have h1 : h.rsvd.toNat < 16 := hw.1
  have h2 : (optArea h.options).length ≤ 40 := hw.2.2
  have hv : h.offByte.toNat = h.dataOffset * 16 + h.rsvd.toNat := by
    rw [Header.offByte, u8_toNat_ofNat, Header.dataOffset]
    omega
  rw [hv]
  omega

theorem Header.area_eq (h : Header) :
    (h.dataOffset - 5) * 4 = (optArea h.options).length := by
  have := optArea_length_mod h.options
  rw [Header.dataOffset]
  omega

/-- **Round trip** of a well-formed header. -/
theorem Header.decode_encode (h : Header) (hw : h.WF) (r : List UInt8) :
    Header.decode (h.encode ++ r) = some (h, r) := by
  obtain ⟨hdiv, hmod⟩ := Header.offByte_div h hw
  have hd5 : 5 ≤ h.dataOffset := by rw [Header.dataOffset]; omega
  have harea : (h.dataOffset - 5) * 4 = (optArea h.options).length := Header.area_eq h
  have hopts : decodeOpts (optArea h.options) = some h.options := decodeOpts_optArea _ hw.2.1
  have hc : 5 ≤ h.offByte.toNat / 16 ∧
      (h.offByte.toNat / 16 - 5) * 4 ≤ (optArea h.options ++ r).length := by
    rw [hdiv, harea, List.length_append]; omega
  have htake : (optArea h.options ++ r).take ((h.offByte.toNat / 16 - 5) * 4) = optArea h.options := by
    rw [hdiv, harea]; simp
  have hdrop : (optArea h.options ++ r).drop ((h.offByte.toNat / 16 - 5) * 4) = r := by
    rw [hdiv, harea]; simp
  have hr : UInt8.ofNat (h.offByte.toNat % 16) = h.rsvd := by rw [hmod]; simp
  simp only [Header.encode, be16, be32, List.cons_append, List.nil_append]
  rw [Header.decode]
  simp only [hc, and_self, ↓reduceIte, htake, hdrop, hopts, Option.map_some, hr, rd16_be16,
    rd32_be32, Ctl.ofByte_toByte]

theorem Header.encode_split (h : Header) : h.encode = h.pre ++ be16 h.checksum ++ h.post := by
  simp [Header.encode, Header.pre, Header.post]

theorem Header.pre_length (h : Header) : h.pre.length = 16 := by
  simp [Header.pre]

theorem Segment.encode_withChecksum (s : Segment) (c : UInt16) :
    (s.withChecksum c).encode = s.header.pre ++ be16 c ++ s.header.post ++ s.payload := by
  simp only [Segment.encode, Segment.withChecksum, Header.encode_split]
  rfl

theorem Segment.length_withChecksum (s : Segment) (c : UInt16) :
    (s.withChecksum c).encode.length = s.encode.length := by
  have h1 := Segment.encode_withChecksum s c
  have h2 := Segment.encode_withChecksum s s.header.checksum
  have h3 : s.withChecksum s.header.checksum = s := rfl
  rw [h3] at h2
  rw [h1, h2]
  simp

theorem Segment.withChecksum_withChecksum (s : Segment) (c d : UInt16) :
    (s.withChecksum c).withChecksum d = s.withChecksum d := rfl

/-- **A sealed segment passes the receiver's checksum test.** -/
theorem Segment.seal_checksumOk {src dst : IpAddr} {s s' : Segment}
    (h : Segment.seal src dst s = some s') : Segment.checksumOk src dst s' = true := by
  simp only [Segment.seal, Segment.covered, Option.map_map, Option.map_eq_some_iff,
    Function.comp_apply] at h
  obtain ⟨ph, hph, rfl⟩ := h
  have hev : ph.length % 2 = 0 := pseudo_length_even hph
  let pre := ph ++ s.header.pre
  have hpre : pre.length % 2 = 0 := by
    simp only [pre, List.length_append, Header.pre_length]; omega
  have hz : ph ++ (s.withChecksum 0).encode = pre ++ [0, 0] ++ (s.header.post ++ s.payload) := by
    rw [Segment.encode_withChecksum]
    simp only [pre, List.append_assoc]
    rfl
  have hv := verify_fill pre (s.header.post ++ s.payload) hpre
  rw [← hz] at hv
  generalize checksum (ph ++ (s.withChecksum 0).encode) = c at hv ⊢
  have hlen : (s.withChecksum c).encode.length = (s.withChecksum 0).encode.length := by
    rw [Segment.length_withChecksum, Segment.length_withChecksum]
  have hcov : Segment.covered src dst (s.withChecksum c) =
      some (ph ++ (s.withChecksum c).encode) := by
    simp only [Segment.covered, hlen, hph, Option.map_some]
  simp only [Segment.checksumOk, hcov, Segment.encode_withChecksum]
  simpa only [pre, List.append_assoc] using hv

/-- **Round trip** of a segment with a well-formed header. -/
theorem Segment.decode_encode (s : Segment) (hw : s.header.WF) :
    Segment.decode s.encode = some s := by
  rw [Segment.decode, Segment.encode, Header.decode_encode s.header hw]
  rfl

/-- Sealing succeeds exactly for addresses of one family. -/
theorem Segment.seal_some (src dst : IpAddr) (s : Segment) :
    (Segment.seal src dst s).isSome = (src.family == dst.family) := by
  cases src <;> cases dst <;> rfl

end Silmaril.Net.Tcp
