module

public import Silmaril.Wasi.Versions.NetAddr.Defs

@[expose] public section

/-!
# IP addresses and socket addresses: theorems

PROVED (standard axioms):

* **`sockAddrOf_sockAddrV`**: decoding an encoded well-formed socket address gives it back;
  **`sockAddrV_of`**: a value that decodes is the encoding of what it decodes to, and
  `sockAddrOf_wf`: what decodes is well formed. So `sockAddrOf` is a bijection between the
  WASI `ip-socket-address` values and the well-formed `SockAddr`s.
* **`akey_of`**: the numbers `Udp3Conn.akey` reads from a decodable value are those of the
  decoded address (`SockAddr.key`), and `key_inj`: on well-formed addresses `key` is
  injective, so `akey` comparisons are comparisons of decoded addresses (`akey_eq_iff`).
-/

namespace Silmaril.Wasi.Versions.NetAddr

open Silmaril.Wasm.Component (Val)

theorem sockAddrOf_sockAddrV {s : SockAddr} (h : s.WF) : sockAddrOf (sockAddrV s) = some s := by
  rcases s with ⟨_, ip⟩ | ⟨_, _, ip, _⟩ <;> rcases ip with ⟨⟩ | ⟨⟩ <;>
    simp_all [SockAddr.WF, sockAddrV, sockAddrOf, ipV, ipv4Of, ipv6Of]

theorem ipv4Of_eq {v : Val} {ip : IpAddr} (h : ipv4Of v = some ip) : ipV ip = v ∧ ∃ a b c d, ip = .v4 a b c d := by
  unfold ipv4Of at h
  split at h
  · cases h; exact ⟨rfl, _, _, _, _, rfl⟩
  · cases h

theorem ipv6Of_eq {v : Val} {ip : IpAddr} (h : ipv6Of v = some ip) :
    ipV ip = v ∧ ∃ a b c d e f g i, ip = .v6 a b c d e f g i := by
  unfold ipv6Of at h
  split at h
  · cases h; exact ⟨rfl, _, _, _, _, _, _, _, _, rfl⟩
  · cases h

/-- **A value that decodes is the encoding of its decoding**, which is well formed. -/
theorem sockAddrV_of {v : Val} {s : SockAddr} (h : sockAddrOf v = some s) :
    sockAddrV s = v ∧ s.WF := by
  unfold sockAddrOf at h
  split at h
  · obtain ⟨ip, hip, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨he, a, b, c, d, rfl⟩ := ipv4Of_eq hip
    exact ⟨by simp [sockAddrV, he], trivial⟩
  · obtain ⟨ip, hip, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨he, a, b, c, d, e, f, g, i, rfl⟩ := ipv6Of_eq hip
    exact ⟨by simp [sockAddrV, he], trivial⟩
  · cases h

theorem sockAddrOf_wf {v : Val} {s : SockAddr} (h : sockAddrOf v = some s) : s.WF :=
  (sockAddrV_of h).2

/-- `akey` of an encoded well-formed address. -/
theorem akey_sockAddrV {s : SockAddr} (h : s.WF) : Udp3Conn.akey (sockAddrV s) = some s.key := by
  rcases s with ⟨_, ip⟩ | ⟨_, _, ip, _⟩ <;> rcases ip with ⟨⟩ | ⟨⟩ <;>
    simp_all [SockAddr.WF, sockAddrV, ipV, Udp3Conn.akey, Udp3Conn.u8Of, Udp3Conn.u16Of,
      SockAddr.key, IpAddr.nums]

/-- **`akey` reads the numbers of the decoded address.** -/
theorem akey_of {v : Val} {s : SockAddr} (h : sockAddrOf v = some s) :
    Udp3Conn.akey v = some s.key := by
  obtain ⟨hv, hw⟩ := sockAddrV_of h
  rw [← hv]; exact akey_sockAddrV hw

theorem key_inj {s t : SockAddr} (hs : s.WF) (ht : t.WF) (h : s.key = t.key) : s = t := by
  rcases s with ⟨_, ip⟩ | ⟨_, _, ip, _⟩ <;> rcases ip with ⟨⟩ | ⟨⟩ <;>
    rcases t with ⟨_, ip'⟩ | ⟨_, _, ip', _⟩ <;> rcases ip' with ⟨⟩ | ⟨⟩ <;>
    simp_all [SockAddr.WF, SockAddr.key, IpAddr.nums, BitVec.toNat_inj]

/-- **Comparing `akey`s of decodable values is comparing their decodings.** -/
theorem akey_eq_iff {v w : Val} {s t : SockAddr} (hv : sockAddrOf v = some s)
    (hw : sockAddrOf w = some t) : Udp3Conn.akey v = Udp3Conn.akey w ↔ s = t := by
  rw [akey_of hv, akey_of hw]
  exact ⟨fun h => key_inj (sockAddrOf_wf hv) (sockAddrOf_wf hw) (Option.some.inj h),
    fun h => h ▸ rfl⟩

end Silmaril.Wasi.Versions.NetAddr
