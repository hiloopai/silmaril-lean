module

public import Silmaril.Net.Ip.Addr.Defs
public import Silmaril.Net.Wire.Thms

/-!
# IP addresses: theorems

PROVED (standard axioms):

* `Ipv4Addr.decode_bytes`, `Ipv6Addr.decode_bytes`: decoding the octets of an address gives it
  back, and the rest of the input untouched (round trip); `Ipv4Addr.decode_sound`,
  `Ipv6Addr.decode_sound`: a successful decode consumed exactly the octets of its result.
  So `bytes` is injective (`Ipv4Addr.bytes_inj`, `Ipv6Addr.bytes_inj`).
* `toMapped?_toMapped`: an IPv4-mapped IPv6 address gives back its IPv4 address
  (RFC 4291 §2.5.5.2); `toMapped_inj`; `toMapped_not_loopback`: no mapped address is `::1`.
* `pseudo4_length` (12), `pseudo6_length` (40), `pseudo_length_even`: the pseudo-headers have
  even length, as the checksum lemmas of `Ip.Checksum` need.
-/

@[expose] public section

namespace Silmaril.Net.Ip

open Silmaril.Net.Wire

@[simp] theorem Ipv4Addr.bytes_length (x : Ipv4Addr) : x.bytes.length = 4 := rfl

@[simp] theorem Ipv6Addr.bytes_length (x : Ipv6Addr) : x.bytes.length = 16 := rfl

theorem Ipv4Addr.decode_bytes (x : Ipv4Addr) (r : List UInt8) :
    Ipv4Addr.decode (x.bytes ++ r) = some (x, r) := rfl

theorem Ipv4Addr.decode_sound {l r : List UInt8} {x : Ipv4Addr}
    (h : Ipv4Addr.decode l = some (x, r)) : l = x.bytes ++ r := by
  match l, h with
  | _ :: _ :: _ :: _ :: _, h =>
    simp only [Ipv4Addr.decode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem Ipv6Addr.decode_bytes (x : Ipv6Addr) (r : List UInt8) :
    Ipv6Addr.decode (x.bytes ++ r) = some (x, r) := by
  simp [Ipv6Addr.bytes, be16, Ipv6Addr.decode]

theorem Ipv6Addr.decode_sound {l r : List UInt8} {x : Ipv6Addr}
    (h : Ipv6Addr.decode l = some (x, r)) : l = x.bytes ++ r := by
  match l, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h =>
    simp only [Ipv6Addr.decode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Ipv6Addr.bytes, be16_rd16]

theorem Ipv4Addr.bytes_inj {x y : Ipv4Addr} (h : x.bytes = y.bytes) : x = y := by
  have hx := Ipv4Addr.decode_bytes x []
  rw [h, Ipv4Addr.decode_bytes] at hx
  simpa using hx.symm

theorem Ipv6Addr.bytes_inj {x y : Ipv6Addr} (h : x.bytes = y.bytes) : x = y := by
  have hx := Ipv6Addr.decode_bytes x []
  rw [h, Ipv6Addr.decode_bytes] at hx
  simpa using hx.symm

/-- **An IPv4-mapped address gives back its IPv4 address** (RFC 4291 §2.5.5.2). -/
theorem toMapped?_toMapped (x : Ipv4Addr) : x.toMapped.toMapped? = some x := by
  have h1 := be16_rd16 x.a x.b
  have h2 := be16_rd16 x.c x.d
  simp only [be16, List.cons.injEq, and_true] at h1 h2
  simp [Ipv6Addr.toMapped?, Ipv4Addr.toMapped, h1.1, h1.2, h2.1, h2.2]

theorem toMapped_inj {x y : Ipv4Addr} (h : x.toMapped = y.toMapped) : x = y := by
  have hx := toMapped?_toMapped x
  rw [h, toMapped?_toMapped] at hx
  simpa using hx.symm

/-- No IPv4-mapped address is the IPv6 loopback address. -/
theorem toMapped_not_loopback (x : Ipv4Addr) : x.toMapped.isLoopback = false := by
  simp [Ipv6Addr.isLoopback, Ipv4Addr.toMapped, Ipv6Addr.loopback]

@[simp] theorem pseudo4_length (s d : Ipv4Addr) (p : UInt8) (n : UInt16) :
    (pseudo4 s d p n).length = 12 := rfl

@[simp] theorem pseudo6_length (s d : Ipv6Addr) (p : UInt8) (n : UInt32) :
    (pseudo6 s d p n).length = 40 := by
  simp [pseudo6]

/-- Every pseudo-header has even length. -/
theorem pseudo_length_even {s d : IpAddr} {p : UInt8} {n : Nat} {ph : List UInt8}
    (h : pseudo s d p n = some ph) : ph.length % 2 = 0 := by
  match s, d, h with
  | .v4 _, .v4 _, h =>
    simp only [pseudo, Option.some.injEq] at h
    rw [← h, pseudo4_length]
  | .v6 _, .v6 _, h =>
    simp only [pseudo, Option.some.injEq] at h
    rw [← h, pseudo6_length]

end Silmaril.Net.Ip
