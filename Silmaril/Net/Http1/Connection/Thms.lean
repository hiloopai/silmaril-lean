module

public import Silmaril.Net.Http1.Connection.Defs
import Silmaril.Proofs.Net.Http1.Connection

/-!
# HTTP/1.1 connection management: laws

* **Persistence** (RFC 9112 §9.3): `persists_close` (`close` always closes),
  `persists_http11` (HTTP/1.1 without `close` persists), `persists_http10` (HTTP/1.0 persists
  only with `keep-alive`).
* **Forced closure** (§6.1, §6.3 rule 3): `keepOpen_framingForcesClose`,
  `framingForcesClose_clte` (a request with both `Transfer-Encoding` and `Content-Length`),
  `framingForcesClose_http10` (an HTTP/1.0 message with `Transfer-Encoding`), `keepOpen_close`
  (a `close` in the request or the response), `keepOpen_closeDelimited` (a close-delimited
  response, §6.3 rule 8).
* **Hop-by-hop fields** (RFC 9110 §7.6.1): `stripHopByHop_mem` (a forwarded field is neither a
  fixed hop-by-hop field nor named by `Connection`), `fieldValues_stripHopByHop`, hence
  `stripHopByHop_transferCodings` (a forwarded message carries no `Transfer-Encoding`: the
  next hop's framing comes from the forwarder) and `stripHopByHop_connectionOptions`.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse (Bytes)

theorem persists_close {ka : KeepAlive} {v : Version} {fs : List FieldLine}
    (h : hasClose fs = true) : persists ka v fs = false := by
  simp [persists, h]

theorem persists_http11 {ka : KeepAlive} {v : Version} {fs : List FieldLine}
    (hc : hasClose fs = false) (hv : v.atLeast11 = true) : persists ka v fs = true := by
  simp [persists, hc, hv]

theorem persists_http10 {ka : KeepAlive} {v : Version} {fs : List FieldLine}
    (hv : v = ⟨1, 0⟩) (hk : keepAliveOption ∉ connectionOptions fs) :
    persists ka v fs = false := by
  subst hv; simp [persists, hk, Version.atLeast11]

theorem framingForcesClose_clte {v : Version} {fs : List FieldLine}
    (hte : transferCodings fs ≠ []) (hcl : fieldElements fs contentLengthName ≠ []) :
    framingForcesClose v fs = true := by
  simp [framingForcesClose, hte, hcl]

theorem framingForcesClose_http10 {fs : List FieldLine} (hte : transferCodings fs ≠ []) :
    framingForcesClose ⟨1, 0⟩ fs = true := by
  simp [framingForcesClose, hte, Version.is10]

theorem keepOpen_framingForcesClose {ka : KeepAlive} {req : RequestHead} {resp : ResponseHead}
    (h : framingForcesClose req.line.version req.fields = true) : keepOpen ka req resp = false := by
  simp [keepOpen, h]

theorem keepOpen_close {ka : KeepAlive} {req : RequestHead} {resp : ResponseHead}
    (h : hasClose req.fields = true ∨ hasClose resp.fields = true) :
    keepOpen ka req resp = false := by
  rcases h with h | h <;> simp [keepOpen, persists_close h, h]

theorem keepOpen_closeDelimited {ka : KeepAlive} {req : RequestHead} {resp : ResponseHead}
    (h : responseBodyLength req.line.method resp.line.code resp.fields = .close) :
    keepOpen ka req resp = false := by
  simp [keepOpen, h]

theorem stripHopByHop_mem {fs : List FieldLine} {f : FieldLine} (hf : f ∈ stripHopByHop fs) :
    f ∈ fs ∧ lower f.name ∉ hopByHopNames ∧ lower f.name ∉ connectionOptions fs :=
  Proofs.Connection.stripHopByHop_mem hf

theorem fieldValues_stripHopByHop {fs : List FieldLine} {n : Bytes}
    (hn : lower n ∈ hopByHopNames) : fieldValues (stripHopByHop fs) n = [] :=
  Proofs.Connection.fieldValues_stripHopByHop hn

theorem stripHopByHop_transferCodings (fs : List FieldLine) :
    transferCodings (stripHopByHop fs) = [] := by
  simp [transferCodings, fieldElements, fieldValues_stripHopByHop (by decide : lower transferEncodingName ∈ hopByHopNames)]

theorem stripHopByHop_connectionOptions (fs : List FieldLine) :
    connectionOptions (stripHopByHop fs) = [] := by
  simp [connectionOptions, fieldElements, fieldValues_stripHopByHop (by decide : lower connectionName ∈ hopByHopNames)]

end Silmaril.Net.Http1
