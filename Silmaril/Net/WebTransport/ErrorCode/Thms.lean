module

public import Silmaril.Net.WebTransport.ErrorCode.Defs
import Silmaril.Proofs.Net.WebTransport.ErrorCode

@[expose] public section

/-!
# WebTransport over HTTP/3 error codes: theorems (draft-ietf-webtrans-http3-17)

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/WebTransport/ErrorCode.lean`), §4.4:

* `toHttp_range`: every 32-bit application error code maps into
  `0x52e4a40fa8db..0x52e5ac983162`;
* `toHttp_not_grease`: the image never is a reserved `0x1f * N + 0x21` code point
  (`Http3.isGrease`);
* `ofHttp_toHttp`: the inverse recovers the application code;
* `ofHttp_some`: whatever the inverse accepts is in range, not grease, decodes to a 32-bit code,
  and maps back to itself; `ofHttp_none_iff`: it rejects exactly the codes outside the
  `WT_APPLICATION_ERROR` range and the grease code points;
* `isAppRange_iff`: the `WT_APPLICATION_ERROR` range of §9.5 is exactly the image of the 32-bit
  codes, so `toHttp` is a bijection onto it; `toHttp_injective`, `toHttp_lt`: it is strictly
  increasing ("the two HTTP/3 error codepoints adjacent to a reserved codepoint would map to two
  adjacent WebTransport application error codepoints").

CHECKED: the endpoints of §4.4 (`0 ↦ 0x52e4a40fa8db`, `0xffffffff ↦ 0x52e5ac983162`), the
first skipped grease code point, and that the protocol error codes of §9.5 are neither grease
nor application codes nor RFC 9114 codes.
-/

namespace Silmaril.Net.WebTransport

open Silmaril.Net.Http3

theorem toHttp_range {n : Nat} (hn : AppCode n) : appFirst ≤ toHttp n ∧ toHttp n ≤ appLast :=
  Silmaril.Proofs.Net.WebTransport.ErrorCode.toHttp_range hn

theorem toHttp_not_grease (n : Nat) : isGrease (toHttp n) = false :=
  Silmaril.Proofs.Net.WebTransport.ErrorCode.toHttp_not_grease n

theorem ofHttp_toHttp {n : Nat} (hn : AppCode n) : ofHttp (toHttp n) = some n :=
  Silmaril.Proofs.Net.WebTransport.ErrorCode.ofHttp_toHttp hn

theorem ofHttp_some {h n : Nat} (hs : ofHttp h = some n) :
    appFirst ≤ h ∧ h ≤ appLast ∧ isGrease h = false ∧ AppCode n ∧ toHttp n = h :=
  Silmaril.Proofs.Net.WebTransport.ErrorCode.ofHttp_some hs

theorem ofHttp_none_iff (h : Nat) : ofHttp h = none ↔ isAppRange h = false :=
  Silmaril.Proofs.Net.WebTransport.ErrorCode.ofHttp_none_iff h

/-- Grease code points are rejected by the inverse. -/
theorem ofHttp_grease {h : Nat} (hg : isGrease h = true) : ofHttp h = none := by
  simp [ofHttp, hg]

theorem isAppRange_iff (h : Nat) : isAppRange h = true ↔ ∃ n, AppCode n ∧ toHttp n = h :=
  Silmaril.Proofs.Net.WebTransport.ErrorCode.isAppRange_iff h

theorem toHttp_injective {m n : Nat} (h : toHttp m = toHttp n) : m = n :=
  Silmaril.Proofs.Net.WebTransport.ErrorCode.toHttp_injective h

theorem toHttp_lt {m n : Nat} (h : m < n) : toHttp m < toHttp n :=
  Silmaril.Proofs.Net.WebTransport.ErrorCode.toHttp_lt h

/-! ## Known answers -/

/-- "0x00000000 corresponds to 0x52e4a40fa8db, and 0xffffffff corresponds to 0x52e5ac983162"
(§4.4). -/
theorem toHttp_endpoints : toHttp 0 = 0x52e4a40fa8db ∧ toHttp 0xffffffff = 0x52e5ac983162 :=
  ⟨rfl, rfl⟩

theorem ofHttp_endpoints : ofHttp 0x52e4a40fa8db = some 0 ∧ ofHttp 0x52e5ac983162 = some 0xffffffff :=
  by decide

/-- The first grease code point of the range is `appFirst + 30`; codes 29 and 30 straddle it. -/
theorem first_grease_skipped : isGrease (appFirst + 30) = true ∧ toHttp 29 = appFirst + 29 ∧
    toHttp 30 = appFirst + 31 ∧ ofHttp (appFirst + 30) = none := by decide

/-- Just outside the range. -/
theorem ofHttp_outside : ofHttp (appFirst - 1) = none ∧ ofHttp (appLast + 1) = none := by decide

/-- The protocol error codes (§9.5) are not grease, not application codes, and distinct from
RFC 9114 / RFC 9297 codes. -/
theorem protocol_codes_disjoint :
    ErrorCode.all.all (fun e => !isGrease e.code && !isAppRange e.code &&
      Http3.ErrorCode.all.all (fun e' => e'.code != e.code)) = true := by decide

theorem ofCode_code (e : ErrorCode) : ErrorCode.ofCode e.code = some e := by
  cases e <;> rfl

end Silmaril.Net.WebTransport
