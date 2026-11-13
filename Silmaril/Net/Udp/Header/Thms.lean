module

public import Silmaril.Net.Udp.Header.Defs
public import Silmaril.Net.Ip.Addr.Thms
public import Silmaril.Net.Ip.Checksum.Thms

/-!
# UDP header and datagram format: theorems

PROVED (standard axioms):

* `Header.decode_encode`, `Header.decode_sound`: header round trip, both directions (the 8
  octets and the four fields determine each other).
* **`Datagram.decode_encode`**: a datagram whose length fits in 16 bits is read back from its
  octets, whatever follows them; **`Datagram.decode_sound`**: a decoded datagram fits, and the
  input is its octets followed by ignored octets.
* **`Datagram.seal_checksumOk`**: a datagram sealed for a pair of addresses (IPv4 or IPv6)
  passes the receiver's checksum test for them; `Datagram.seal_some`: sealing succeeds exactly
  for addresses of one family; `Datagram.seal_checksum_ne_zero`: a sealed checksum is never
  zero (so it is never mistaken for "no checksum").
-/

@[expose] public section

namespace Silmaril.Net.Udp

open Silmaril.Net.Wire Silmaril.Net.Ip Silmaril.Net.Ip.Checksum

@[simp] theorem Header.encode_length (h : Header) : h.encode.length = 8 := rfl

theorem Header.decode_encode (h : Header) (r : List UInt8) :
    Header.decode (h.encode ++ r) = some (h, r) := by
  simp [Header.encode, be16, Header.decode]

theorem Header.decode_sound {l r : List UInt8} {h : Header}
    (hd : Header.decode l = some (h, r)) : l = h.encode ++ r := by
  match l, hd with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, hd =>
    simp only [Header.decode, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp [Header.encode, be16_rd16]

theorem Datagram.len_toNat {d : Datagram} (h : d.WF) : (UInt16.ofNat d.len).toNat = d.len := by
  rw [u16_toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- **Round trip**: a datagram is read back from its octets, whatever follows them. -/
theorem Datagram.decode_encode (d : Datagram) (hw : d.WF) (junk : List UInt8) :
    Datagram.decode (d.encode ++ junk) = some d := by
  have hl : (UInt16.ofNat d.len).toNat = d.len := Datagram.len_toNat hw
  have hlen : d.len = 8 + d.payload.length := rfl
  have hdec : Header.decode (d.encode ++ junk) = some (d.header, d.payload ++ junk) := by
    rw [Datagram.encode, List.append_assoc, Header.decode_encode]
  have hc : 8 ≤ d.header.length.toNat ∧ d.header.length.toNat - 8 ≤ (d.payload ++ junk).length := by
    simp only [Datagram.header, hl, List.length_append]
    omega
  have hn : d.header.length.toNat - 8 = d.payload.length := by
    show (UInt16.ofNat d.len).toNat - 8 = d.payload.length
    rw [hl]; omega
  have ht : (d.payload ++ junk).take (d.header.length.toNat - 8) = d.payload := by
    rw [hn]; simp
  rw [Datagram.decode, hdec]
  simp only [hc, and_self, ↓reduceIte, ht]
  rfl

/-- Inversion of `Datagram.decode`: the header read, the length checks and the result. -/
theorem Datagram.decode_inv {l : List UInt8} {d : Datagram} (h : Datagram.decode l = some d) :
    ∃ hd r, Header.decode l = some (hd, r) ∧ 8 ≤ hd.length.toNat ∧
      hd.length.toNat - 8 ≤ r.length ∧
      d = ⟨hd.srcPort, hd.dstPort, hd.checksum, r.take (hd.length.toNat - 8)⟩ := by
  unfold Datagram.decode at h
  split at h
  · rename_i hd r hdec
    split at h
    · rename_i hc
      exact ⟨hd, r, hdec, hc.1, hc.2, (Option.some.inj h).symm⟩
    · cases h
  · cases h

/-- **Soundness of `decode`**: a decoded datagram fits in 16 bits, and the input is its octets
followed by ignored octets. -/
theorem Datagram.decode_sound {l : List UInt8} {d : Datagram} (h : Datagram.decode l = some d) :
    d.WF ∧ ∃ junk, l = d.encode ++ junk := by
  obtain ⟨hd, r, hdec, h8, hr, rfl⟩ := Datagram.decode_inv h
  have hl : l = hd.encode ++ r := Header.decode_sound hdec
  have hlt : hd.length.toNat < 65536 := hd.length.toNat_lt
  have htl : (r.take (hd.length.toNat - 8)).length = hd.length.toNat - 8 := by
    simp only [List.length_take]; omega
  have hlen : 8 + (r.take (hd.length.toNat - 8)).length = hd.length.toNat := by omega
  have hwf : 8 + (r.take (hd.length.toNat - 8)).length < 65536 := by omega
  have hh : (Datagram.header ⟨hd.srcPort, hd.dstPort, hd.checksum,
      r.take (hd.length.toNat - 8)⟩) = hd := by
    simp only [Datagram.header, Datagram.len, hlen, UInt16.ofNat_toNat]
  refine ⟨hwf, r.drop (hd.length.toNat - 8), ?_⟩
  rw [hl, Datagram.encode, hh, List.append_assoc, List.take_append_drop]

/-- Sealing succeeds exactly for addresses of one family. -/
theorem Datagram.seal_some (src dst : IpAddr) (d : Datagram) :
    (Datagram.seal src dst d).isSome = (src.family == dst.family) := by
  cases src <;> cases dst <;> rfl

/-- A sealed checksum is never zero. -/
theorem Datagram.seal_checksum_ne_zero {src dst : IpAddr} {d d' : Datagram}
    (h : Datagram.seal src dst d = some d') : d'.checksum ≠ 0 := by
  simp only [Datagram.seal, Option.map_eq_some_iff] at h
  obtain ⟨l, -, rfl⟩ := h
  simp only [txUdp]
  split
  · decide
  · assumption

/-- Sealing changes only the checksum field. -/
theorem Datagram.seal_fields {src dst : IpAddr} {d d' : Datagram}
    (h : Datagram.seal src dst d = some d') :
    d'.srcPort = d.srcPort ∧ d'.dstPort = d.dstPort ∧ d'.payload = d.payload := by
  simp only [Datagram.seal, Option.map_eq_some_iff] at h
  obtain ⟨l, -, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- The octets of a datagram, with the checksum field split out. -/
theorem Datagram.encode_split (d : Datagram) :
    d.encode = (be16 d.srcPort ++ be16 d.dstPort ++ be16 (UInt16.ofNat d.len)) ++
      be16 d.checksum ++ d.payload := by
  simp [Datagram.encode, Datagram.header, Header.encode]

/-- **A sealed datagram passes the receiver's checksum test.** -/
theorem Datagram.seal_checksumOk {src dst : IpAddr} {d d' : Datagram}
    (h : Datagram.seal src dst d = some d') : Datagram.checksumOk src dst d' = true := by
  have hne : d'.checksum ≠ 0 := Datagram.seal_checksum_ne_zero h
  simp only [Datagram.seal, Datagram.covered, Option.map_map, Option.map_eq_some_iff,
    Function.comp_apply] at h
  obtain ⟨ph, hph, rfl⟩ := h
  simp only at hne
  have hev : ph.length % 2 = 0 := pseudo_length_even hph
  have hlen : ({ d with checksum := 0 } : Datagram).len = d.len := rfl
  let pre := ph ++ (be16 d.srcPort ++ be16 d.dstPort ++ be16 (UInt16.ofNat d.len))
  have hpre : pre.length % 2 = 0 := by
    simp only [pre, List.length_append, be16_length]; omega
  have hz : ph ++ ({ d with checksum := 0 } : Datagram).encode = pre ++ [0, 0] ++ d.payload := by
    rw [Datagram.encode_split]
    simp only [pre, hlen, List.append_assoc]
    rfl
  have hv := verify_fill_tx pre d.payload hpre
  rw [← hz] at hv
  generalize hc : txUdp (Checksum.checksum (ph ++ ({ d with checksum := 0 } : Datagram).encode)) = c
    at hv hne ⊢
  have hcov : Datagram.covered src dst { d with checksum := c } =
      some (ph ++ ({ d with checksum := c } : Datagram).encode) := by
    have hl' : ({ d with checksum := c } : Datagram).len = d.len := rfl
    have hph' : pseudo src dst protoUdp d.len = some ph := hph
    simp only [Datagram.covered, hl', hph', Option.map_some]
  have henc : ({ d with checksum := c } : Datagram).encode =
      (be16 d.srcPort ++ be16 d.dstPort ++ be16 (UInt16.ofNat d.len)) ++ be16 c ++ d.payload :=
    Datagram.encode_split _
  have hne' : ¬ c = 0 := hne
  simp only [Datagram.checksumOk, hne', ↓reduceIte, hcov, henc]
  simpa only [pre, List.append_assoc] using hv

end Silmaril.Net.Udp
