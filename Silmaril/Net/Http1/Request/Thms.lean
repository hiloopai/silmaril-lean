module

public import Silmaril.Net.Http1.Request.Defs
public import Silmaril.Net.Http1.Framing.Defs
import Silmaril.Proofs.Net.Http1.Request
import Silmaril.Net.Http1.Profile.Thms

/-!
# HTTP/1.1 request context: laws

Proofs in `Silmaril/Proofs/Net/Http1/Request.lean`.

* `checkRequest_ok`: an accepted request has major version 1, a target of a form its
  method allows, exactly one valid `Host` (or, below HTTP/1.1, none), framing as the
  profile reads it and not invalid, codings the server implements, and the persistence of
  RFC 9112 §9.3 (`Accepted` lists the facts).
* `checkRequest_host11`: an accepted HTTP/1.1 request has exactly one `Host` field line, with a valid value (RFC 9112 §3.2).
* `checkRequest_connect`: a request is CONNECT iff its target is in authority form.
* `checkRequest_framing`: with a compliant profile, the framing is the reference framing.
* `checkRequest_clte`: a request with both `Transfer-Encoding` and `Content-Length` is never
  followed by another request on the connection (§6.3 rule 3).
* `RequestError.status_mem`: errors are answered `400`, `501` or `505`.
* **The two field vocabularies agree**: `FieldLine.toLine_isValid` identifies the HTTP/1.1
  field-line validity (`Silmaril.Net.Http1.Syntax`) with the RFC 9110 one
  (`Silmaril.Net.Http.Field`), byte class by byte class; so `toRequest_isValid`: a
  valid head with valid trailers gives a valid RFC 9110 request (`Http.Request.isValid`).
* **Trailers** `fieldValues_mergeTrailers`: merging trailers never changes the values of a
  field forbidden in trailers, so `requestBodyLength_mergeTrailers`: the framing of the
  merged section is that of the header section.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

theorem checkRequest_ok {cfg : ServerConfig} {h : RequestHead} {c : Context}
    (hc : checkRequest cfg h = .ok c) : Accepted cfg h c :=
  Proofs.Request.checkRequest_ok hc

theorem checkRequest_host11 {cfg : ServerConfig} {h : RequestHead} {c : Context}
    (hc : checkRequest cfg h = .ok c) (hv : h.line.version.atLeast11 = true) :
    ∃ host, fieldValues h.fields hostName = [host] ∧ Http.Uri.isHttpAuthority host = true := by
  obtain ⟨host, hh | ⟨-, hn⟩⟩ := (checkRequest_ok hc).host
  · exact ⟨host, hh⟩
  · rw [hv] at hn; cases hn

theorem checkRequest_connect {cfg : ServerConfig} {h : RequestHead} {c : Context}
    (hc : checkRequest cfg h = .ok c) : h.line.method = methodCONNECT ↔ c.form = .authority :=
  Proofs.Request.checkRequest_connect hc

theorem checkRequest_framing {cfg : ServerConfig} {h : RequestHead} {c : Context}
    (hc : checkRequest cfg h = .ok c) (hp : cfg.profile.Compliant) :
    c.framing = rfcRequestFraming h.line.version h.fields := by
  have a := checkRequest_ok hc
  rcases frame_compliant hp h.line.version h.fields with he | he
  · rw [a.framing, he]
  · exact absurd (a.framing.trans he) a.framing_ne

theorem checkRequest_clte {cfg : ServerConfig} {h : RequestHead} {c : Context}
    (hc : checkRequest cfg h = .ok c) (hte : transferCodings h.fields ≠ [])
    (hcl : fieldElements h.fields contentLengthName ≠ []) : c.persistent = false := by
  rw [(checkRequest_ok hc).persistent]
  simp [framingForcesClose, hte, hcl]

theorem RequestError.status_mem (e : RequestError) : e.status ∈ [400, 501, 505] := by
  cases e <;> simp [RequestError.status]

theorem FieldLine.toLine_isValid (f : FieldLine) : f.toLine.isValid = true ↔ f.Valid :=
  Proofs.Request.toLine_isValid f

theorem toRequest_isValid {h : RequestHead} {b : Body} {c : Context} (hv : h.Valid)
    (ht : ∀ f ∈ b.trailers, f.Valid) (hm : c.method = Http.Method.ofToken h.line.method) :
    (toRequest h b c).isValid = true := Proofs.Request.toRequest_isValid hv ht hm

theorem fieldValues_mergeTrailers {hs ts : List FieldLine} {n : Bytes}
    (hn : lower n ∈ trailerForbidden) : fieldValues (mergeTrailers hs ts) n = fieldValues hs n :=
  Proofs.Request.fieldValues_mergeTrailers hn

theorem requestBodyLength_mergeTrailers (hs ts : List FieldLine) :
    requestBodyLength (mergeTrailers hs ts) = requestBodyLength hs := by
  have h₁ := fieldValues_mergeTrailers (hs := hs) (ts := ts)
    (n := transferEncodingName) (by decide)
  have h₂ := fieldValues_mergeTrailers (hs := hs) (ts := ts) (n := contentLengthName) (by decide)
  simp only [requestBodyLength, bodyLengthOfFields, transferCodings, contentLength?,
    fieldElements, h₁, h₂]

end Silmaril.Net.Http1
