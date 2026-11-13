module

public import Silmaril.Net.Tls.Record.Defs
public import Silmaril.Net.WebSocket.Frame.Thms

@[expose] public section

/-!
# The TLS record header: theorems

PROVED (standard axioms):

* `decodeHeader_encodeHeader`: a valid header is read back from any stream it starts;
* `tls_not_token`: no TLS content type is a `tchar`, so a stream that starts a TLS record never
  starts an HTTP/1.1 request line, and conversely (`token_not_tls`);
* `preface_not_tls`: the HTTP/2 connection preface (RFC 9113 §3.4) does not start a TLS record.

CHECKED: a ClientHello record header (`16 03 01 …`).
-/

namespace Silmaril.Net.Tls

open Silmaril.Net.Http2 (beBytes beValue)

theorem decodeHeader_encodeHeader (limit : Nat) (h : RecordHeader) (hv : h.Valid limit)
    (rest : List UInt8) : decodeHeader limit (encodeHeader h ++ rest) = some (h, rest) := by
  obtain ⟨ht, hver, hl, hlim⟩ := hv
  have ht' : h.type < 256 := by simp [contentTypes] at ht; omega
  have e1 : beBytes 2 h.version = [(h.version / 256 % 256).toUInt8, (h.version % 256).toUInt8] := by
    simp [beBytes]
  have e2 : beBytes 2 h.length = [(h.length / 256 % 256).toUInt8, (h.length % 256).toUInt8] := by
    simp [beBytes]
  have v1 : beValue [(h.version / 256 % 256).toUInt8, (h.version % 256).toUInt8] = h.version := by
    rw [← e1]; exact Silmaril.Net.WebSocket.beValue_beBytes 2 _ (by simpa using hver)
  have v2 : beValue [(h.length / 256 % 256).toUInt8, (h.length % 256).toUInt8] = h.length := by
    rw [← e2]; exact Silmaril.Net.WebSocket.beValue_beBytes 2 _ (by simp; omega)
  have tt : h.type.toUInt8.toNat = h.type := by
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']; omega
  simp only [encodeHeader, e1, e2, List.cons_append, List.nil_append, decodeHeader, v1, v2, tt]
  have : contentTypes.contains h.type = true := by simpa using ht
  simp [hl, ht]

theorem tls_not_token (t : Nat) (ht : t ∈ contentTypes) :
    Silmaril.Net.Http.Field.isTchar t.toUInt8 = false := by
  simp only [contentTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide

theorem token_not_tls {xs : List UInt8} {h : RecordHeader} {rest : List UInt8} {limit : Nat}
    (hd : decodeHeader limit xs = some (h, rest)) : startsWithToken xs = false := by
  match xs, hd with
  | t :: v0 :: v1 :: l0 :: l1 :: r, hd =>
    simp only [decodeHeader] at hd
    split at hd
    · next hc =>
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      have := tls_not_token _ hc.1
      simp only [Nat.toUInt8_eq, UInt8.ofNat_toNat] at this
      simpa [startsWithToken] using this
    · cases hd

theorem preface_not_tls (limit : Nat) :
    decodeHeader limit Silmaril.Net.Http2.clientPreface = none := by
  cases hd : decodeHeader limit Silmaril.Net.Http2.clientPreface with
  | none => rfl
  | some p =>
    obtain ⟨hh, r⟩ := p
    have h1 := token_not_tls hd
    have h2 : startsWithToken Silmaril.Net.Http2.clientPreface = true := by decide +kernel
    rw [h1] at h2
    cases h2

/-- A ClientHello record header: handshake, legacy version 0x0301, 512 octets. -/
example : decodeHeader maxPlaintext [0x16, 0x03, 0x01, 0x02, 0x00] =
    some (⟨handshakeType, 0x0301, 512⟩, []) := by
  decide +kernel

/-- An HTTP/1.1 request line is not a TLS record. -/
example : decodeHeader maxPlaintext ("GET / HTTP/1.1\r\n".toList.map (·.toNat.toUInt8)) = none := by
  decide +kernel

end Silmaril.Net.Tls
