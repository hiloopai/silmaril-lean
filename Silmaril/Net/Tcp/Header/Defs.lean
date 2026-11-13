module

public import Silmaril.Net.Tcp.Seq.Defs
public import Silmaril.Net.Ip.Addr.Defs
public import Silmaril.Net.Ip.Checksum.Defs

/-!
# TCP: segment header format with options (RFC 9293 §3.1, §3.2)

RFC 9293 §3.1, Figure 1: Source Port (16 bits), Destination Port (16), Sequence Number (32),
Acknowledgment Number (32), Data Offset (4: the header length in 32-bit words), Reserved (4),
eight control bits CWR ECE URG ACK PSH RST SYN FIN, Window (16), Checksum (16), Urgent Pointer
(16), then options and padding up to `4 · DOffset` octets, then the data.

* `Ctl`: the eight control bits; `Ctl.toByte`/`Ctl.ofByte` their octet (CWR most significant).
* `Opt`: an option. §3.1: "Case 1: A single octet of option-kind. Case 2: An octet of
  option-kind (Kind), an octet of option-length, and the actual option-data octets", the length
  counting kind and length octets. Table 1, the mandatory set: End of Option List (kind 0),
  No-Operation (kind 1), Maximum Segment Size (kind 2, length 4, §3.2). Other kinds
  (`Opt.other`) are kept as kind and data, so options this formalization does not know yet
  (SACK, timestamps, window scale: §3.2.1) survive a round trip ("MUST ignore without error any
  TCP Option it does not implement", MUST-6). End of Option List is not an `Opt`: it is
  implied by the end of the list, and encoded, when needed, as the first octet of the padding.
* `optArea os`: the options followed by zero padding to a multiple of 4 octets ("The content of
  the header beyond the End of Option List Option MUST be header padding of zeros", MUST-69;
  a zero padding octet is itself an End of Option List).
* `decodeOpts`: the receiver's option parser. It accepts options "even if they do not begin on
  a word boundary" (MUST-64) and in any order; an End of Option List must be followed only by
  zeros; an illegal length (below 2, beyond the option area, or an MSS length other than 4) is
  an error (MUST-7 leaves the reaction to the implementation).
* `Header`, `Header.encode`, `Header.decode`; `Header.WF`: reserved bits fit in 4 bits, options
  are well formed (`Opt.WF`) and the option area is at most 40 octets (Data Offset ≤ 15).
* `Segment`: a header and data; the checksum over the pseudo-header (protocol 6, the TCP length,
  RFC 9293 §3.1 Figure 2 and RFC 8200 §8.1), the header with a zero checksum field and the data
  (`Segment.seal`, `Segment.checksumOk`). "The TCP checksum is never optional" (MUST-2/3): no
  zero-means-absent rule, unlike UDP.

A Silmaril addition (region `Net`, see `docs/projects/wasm-wasi.md`).
-/

@[expose] public section

namespace Silmaril.Net.Tcp

open Silmaril.Net.Wire Silmaril.Net.Ip Silmaril.Net.Ip.Checksum

/-- **The control bits** (RFC 9293 §3.1). -/
structure Ctl where
  cwr : Bool := false
  ece : Bool := false
  urg : Bool := false
  ack : Bool := false
  psh : Bool := false
  rst : Bool := false
  syn : Bool := false
  fin : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The octet of the control bits, CWR most significant (RFC 9293 §3.1, Figure 1). -/
def Ctl.toByte (c : Ctl) : UInt8 :=
  UInt8.ofNat (c.cwr.toNat * 128 + c.ece.toNat * 64 + c.urg.toNat * 32 + c.ack.toNat * 16 +
    c.psh.toNat * 8 + c.rst.toNat * 4 + c.syn.toNat * 2 + c.fin.toNat)

/-- The control bits of an octet. -/
def Ctl.ofByte (b : UInt8) : Ctl :=
  ⟨b.toNat / 128 % 2 == 1, b.toNat / 64 % 2 == 1, b.toNat / 32 % 2 == 1, b.toNat / 16 % 2 == 1,
   b.toNat / 8 % 2 == 1, b.toNat / 4 % 2 == 1, b.toNat / 2 % 2 == 1, b.toNat % 2 == 1⟩

/-- **A TCP option** other than End of Option List (RFC 9293 §3.1, §3.2). -/
inductive Opt where
  /-- No-Operation, kind 1. -/
  | nop
  /-- Maximum Segment Size, kind 2, length 4 (§3.2, §3.7.1). -/
  | mss (v : UInt16)
  /-- Any other option: kind and option data (the length octet is computed). -/
  | other (kind : UInt8) (data : List UInt8)
  deriving DecidableEq, Repr

/-- The octets of an option. -/
def Opt.encode : Opt → List UInt8
  | .nop => [1]
  | .mss v => [2, 4] ++ be16 v
  | .other k d => k :: UInt8.ofNat (d.length + 2) :: d

/-- A well-formed option: an `other` option has a kind outside the mandatory set and a length
that fits in its octet. -/
def Opt.WF : Opt → Prop
  | .nop => True
  | .mss _ => True
  | .other k d => 3 ≤ k.toNat ∧ d.length + 2 < 256

/-- The octets of a list of options. -/
def encodeOpts : List Opt → List UInt8
  | [] => []
  | o :: os => o.encode ++ encodeOpts os

/-- Padding octets needed to reach a multiple of 4. -/
def padLen (n : Nat) : Nat := (4 - n % 4) % 4

/-- **The option area**: options, then zero padding to a 32-bit boundary (MUST-69). -/
def optArea (os : List Opt) : List UInt8 :=
  encodeOpts os ++ zeros (padLen (encodeOpts os).length)

/-- **The receiver's option parser** over the option area. -/
def decodeOpts : List UInt8 → Option (List Opt)
  | [] => some []
  | k :: rest =>
    if k = 0 then
      if rest.all (· == 0) then some [] else none
    else if k = 1 then
      (decodeOpts rest).map (Opt.nop :: ·)
    else
      match rest with
      | [] => none
      | len :: rest' =>
        if k = 2 then
          if len = 4 then
            match rest' with
            | a :: b :: r => (decodeOpts r).map (Opt.mss (rd16 a b) :: ·)
            | _ => none
          else none
        else if 2 ≤ len.toNat ∧ len.toNat - 2 ≤ rest'.length then
          (decodeOpts (rest'.drop (len.toNat - 2))).map
            (Opt.other k (rest'.take (len.toNat - 2)) :: ·)
        else none
termination_by l => l.length
decreasing_by
  all_goals simp_wf
  all_goals (try simp only [List.length_drop])
  all_goals omega

/-- **A TCP header** (RFC 9293 §3.1). Data Offset is computed from the options. -/
structure Header where
  srcPort : Port
  dstPort : Port
  seq : SeqNum
  ack : SeqNum
  /-- The four reserved bits ("Must be zero in generated segments", kept as received). -/
  rsvd : UInt8
  ctl : Ctl
  window : UInt16
  checksum : UInt16
  urgent : UInt16
  options : List Opt
  deriving DecidableEq, Repr

/-- Data Offset: the header length in 32-bit words. -/
def Header.dataOffset (h : Header) : Nat := 5 + (optArea h.options).length / 4

/-- A header that can be encoded: reserved bits in 4 bits, well-formed options, at most 40
octets of options (Data Offset at most 15). -/
def Header.WF (h : Header) : Prop :=
  h.rsvd.toNat < 16 ∧ (∀ o ∈ h.options, o.WF) ∧ (optArea h.options).length ≤ 40

/-- The octet holding Data Offset and the reserved bits. -/
def Header.offByte (h : Header) : UInt8 := UInt8.ofNat (h.dataOffset * 16 + h.rsvd.toNat)

/-- The octets of a header, in network byte order (RFC 9293 §3.1, Figure 1). -/
def Header.encode (h : Header) : List UInt8 :=
  be16 h.srcPort ++ be16 h.dstPort ++ be32 h.seq ++ be32 h.ack ++ [h.offByte, h.ctl.toByte] ++
    be16 h.window ++ be16 h.checksum ++ be16 h.urgent ++ optArea h.options

/-- The 16 octets of a header before the checksum field. -/
def Header.pre (h : Header) : List UInt8 :=
  be16 h.srcPort ++ be16 h.dstPort ++ be32 h.seq ++ be32 h.ack ++ [h.offByte, h.ctl.toByte] ++
    be16 h.window

/-- The octets of a header after the checksum field. -/
def Header.post (h : Header) : List UInt8 := be16 h.urgent ++ optArea h.options

/-- **Read a header** from the front of a list of octets: the fixed 20 octets, then
`4 · DOffset - 20` octets of option area. -/
def Header.decode : List UInt8 → Option (Header × List UInt8)
  | s0 :: s1 :: d0 :: d1 :: q0 :: q1 :: q2 :: q3 :: a0 :: a1 :: a2 :: a3 ::
    ob :: cb :: w0 :: w1 :: c0 :: c1 :: u0 :: u1 :: rest =>
      if 5 ≤ ob.toNat / 16 ∧ (ob.toNat / 16 - 5) * 4 ≤ rest.length then
        (decodeOpts (rest.take ((ob.toNat / 16 - 5) * 4))).map fun os =>
          (⟨rd16 s0 s1, rd16 d0 d1, rd32 q0 q1 q2 q3, rd32 a0 a1 a2 a3,
            UInt8.ofNat (ob.toNat % 16), Ctl.ofByte cb, rd16 w0 w1, rd16 c0 c1, rd16 u0 u1, os⟩,
           rest.drop ((ob.toNat / 16 - 5) * 4))
      else none
  | _ => none

/-- **A TCP segment**: a header and its data. -/
structure Segment where
  header : Header
  payload : List UInt8
  deriving DecidableEq, Repr

/-- The octets of a segment. -/
def Segment.encode (s : Segment) : List UInt8 := s.header.encode ++ s.payload

/-- Read a segment from the octets of an IP payload: a header, and the rest as data. -/
def Segment.decode (l : List UInt8) : Option Segment :=
  (Header.decode l).map fun p => ⟨p.1, p.2⟩

/-- The segment with the checksum field replaced. -/
def Segment.withChecksum (s : Segment) (c : UInt16) : Segment :=
  ⟨{ s.header with checksum := c }, s.payload⟩

/-- The octets the checksum covers: the pseudo-header (protocol 6, the TCP length), then the
segment (RFC 9293 §3.1). `none` for addresses of different families. -/
def Segment.covered (src dst : IpAddr) (s : Segment) : Option (List UInt8) :=
  (pseudo src dst protoTcp s.encode.length).map (· ++ s.encode)

/-- **Fill in the checksum** (RFC 9293 §3.1, MUST-2), computed with the field zeroed. -/
def Segment.seal (src dst : IpAddr) (s : Segment) : Option Segment :=
  (Segment.covered src dst (s.withChecksum 0)).map fun l => s.withChecksum (checksum l)

/-- **The receiver's checksum test** (MUST-3). -/
def Segment.checksumOk (src dst : IpAddr) (s : Segment) : Bool :=
  match Segment.covered src dst s with
  | some l => verify l
  | none => false

end Silmaril.Net.Tcp
