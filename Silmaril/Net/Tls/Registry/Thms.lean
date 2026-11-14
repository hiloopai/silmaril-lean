module

public import Silmaril.Net.Tls.Registry.Defs
public import Silmaril.Crypto.Catalog.Thms

@[expose] public section

/-!
# TLS registries: theorems

PROVED (standard axioms, by case analysis or `decide`):

* `CipherSuite.ofCode_code`: the cipher-suite map is injective on code points;
* `tls13_aead`: every TLS 1.3 suite protects records with an AEAD and derives keys with HKDF
  (RFC 8446 §5.2, §7.1);
* `h2_tls13_ok`: every TLS 1.3 suite is acceptable for HTTP/2; `h2_rsa_blocked`: static-RSA
  suites are not, under TLS 1.2 (RFC 9113 §9.2, Appendix A);
* `selectAlpn_sound`: the selected protocol is offered by both sides and is never `h2c`
  (RFC 7301 §3.2, RFC 9113 §3.1);
* `sha1_not_tls13`: no SHA-1 signature scheme is allowed for TLS 1.3 handshake signatures
  (RFC 8446 §4.2.3);
* `assumptions_dh_free_iff_rsa`: a suite's assumption list omits the DH assumption exactly when
  it uses static-RSA key transport (no forward secrecy);
* `implemented_hashes`: of the hashes the recognized suites use for HKDF/HMAC, only SHA-256
  has an executable specification here (SHA-384 is planned).
-/

namespace Silmaril.Net.Tls

open Silmaril.Crypto.Catalog

theorem CipherSuite.ofCode_code (s : CipherSuite) : CipherSuite.ofCode s.code = some s := by
  cases s <;> rfl

theorem tls13_aead (s : CipherSuite) (h : s.tls13 = true) :
    (∃ a, s.components.record = .aead a) ∧ ∃ hh, s.components.kdf = .hkdf hh := by
  cases s <;> simp_all [CipherSuite.tls13, CipherSuite.components]

theorem h2_tls13_ok (s : CipherSuite) (h : s.tls13 = true) : h2Acceptable .tls13 s = true := by
  simp [h2Acceptable, h]

theorem h2_rsa_blocked (s : CipherSuite) (h : s.components.keyExchange = .rsa) :
    h2Acceptable .tls12 s = false := by
  cases s <;> simp_all [h2Acceptable, CipherSuite.h2Blocked, CipherSuite.components,
    CipherSuite.tls13]

theorem selectAlpn_sound {server client : List AlpnId} {p : AlpnId}
    (h : selectAlpn server client = some p) : p ∈ server ∧ p ∈ client ∧ p ≠ .h2c := by
  unfold selectAlpn at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at hp
  exact ⟨hm, hp.2, hp.1⟩

theorem sha1_not_tls13 (c : Nat) (s : SigAlg) (h : SignatureScheme.ofCode c = some s)
    (hs : sigHash? s = some .sha1) : allowedInTls13Handshake s = false := by
  cases s <;> simp_all [allowedInTls13Handshake]

theorem assumptions_dh_free_iff_rsa (s : CipherSuite) (g : Group) (sig : SigAlg) :
    Assumption.dhHard g ∉ s.assumptions g sig ↔ s.components.keyExchange = .rsa := by
  cases s <;> simp [CipherSuite.assumptions, CipherSuite.components]

theorem implemented_hashes :
    (CipherSuite.all.map fun s => match s.components.kdf with
      | .hkdf h | .hmac h => ((hashImpl h).isSome, h)
      | _ => (false, .md5)).all (fun p => p.1 == (p.2 == .sha256)) = true := by
  decide

/-! ## Examples -/

/-- A browser-like offer against a server preferring `h2`. -/
example : selectAlpn [.h2, .http11] [.http11, .h2] = some .h2 := by decide
/-- `h2c` is never negotiated in TLS. -/
example : selectAlpn [.h2c, .http11] [.h2c, .http11] = some .http11 := by decide
/-- No overlap: `no_application_protocol`. -/
example : selectAlpn [.h3] [.http11] = none := by decide

example : CipherSuite.ofCode 0x1301 = some .tls13_aes_128_gcm_sha256 := by decide
example : CipherSuite.ofCode 0x1306 = none := by decide
example : NamedGroup.ofCode 0x001D = some .x25519 := rfl

end Silmaril.Net.Tls
