module

public import Silmaril.Net.Http1.Pipeline.Defs
import Silmaril.Proofs.Net.Http1.Pipeline
import Silmaril.Net.Http1.Request.Thms

/-!
# Persistent connections and pipelining: laws

Proofs in `Silmaril/Proofs/Net/Http1/Pipeline.lean`.

* `serve_pipeline` (RFC 9112 §9.3.2): on the octets of a pipeline of valid requests, each
  accepted and kept open, the server reads exactly those requests, in order, and stops at the
  end of the input. Each exchange holds the handler's response to its request
  (`serve` builds it so), so responses go out in request order.
* `serve_closes` (§9.3, §9.6): after a request that closes the connection, the server reads
  nothing more, **whatever octets follow**: a request smuggled behind it is never processed.
* `serve_clte_closes` (§6.3 rule 3): in particular after an accepted request with both
  `Transfer-Encoding` and `Content-Length`.
* `readResponse_encode`, `readResponses_encode` (RFC 9110 §15.2, RFC 9112 §9.3.2): the
  interim and final responses to a pipeline of requests are read back in order, each framed by
  its request's method.
* `mayAutoRetry_POST` (§9.3.1): a non-idempotent request is not retried automatically.
-/

@[expose] public section

namespace Silmaril.Net.Http1

open Silmaril.Parse.ByteParse

theorem serve_pipeline (cfg : ServerConfig) (H : Handler) (xs : List (RequestHead × Body))
    (pre : Bytes) (n : Nat)
    (hv : ∀ x ∈ xs, x.1.Valid ∧ x.2.Fits (cfg.profile.frame x.1.line.version x.1.fields))
    (hk : ∀ x ∈ xs, KeptOpen cfg H x.1 x.2) (hn : xs.length < n) :
    (serve cfg H n ⟨(pre ++ (xs.map fun x => encRequest x.1 x.2).flatten).toArray⟩
        pre.length).1.map (fun e => (e.request, e.body)) = xs ∧
      (serve cfg H n ⟨(pre ++ (xs.map fun x => encRequest x.1 x.2).flatten).toArray⟩
        pre.length).2 = .eof :=
  Proofs.Pipeline.serve_pipeline cfg H xs pre n hv hk hn

theorem serve_closes (cfg : ServerConfig) (H : Handler) {h : RequestHead} {b : Body}
    (hv : h.Valid) (hb : b.Fits (cfg.profile.frame h.line.version h.fields)) {c : Context}
    (hc : checkRequest cfg h = .ok c)
    (hk : (c.persistent && keepOpen cfg.keepAlive h (H h b c).1) = false)
    (pre rest : Bytes) (n : Nat) :
    serve cfg H (n + 1) ⟨(pre ++ encRequest h b ++ rest).toArray⟩ pre.length =
      ([⟨h, b, c, (H h b c).1, (H h b c).2⟩], .closed) :=
  Proofs.Pipeline.serve_closes cfg H hv hb hc hk pre rest n

theorem serve_clte_closes (cfg : ServerConfig) (H : Handler) {h : RequestHead} {b : Body}
    (hv : h.Valid) (hb : b.Fits (cfg.profile.frame h.line.version h.fields)) {c : Context}
    (hc : checkRequest cfg h = .ok c) (hte : transferCodings h.fields ≠ [])
    (hcl : fieldElements h.fields contentLengthName ≠ []) (pre rest : Bytes) (n : Nat) :
    serve cfg H (n + 1) ⟨(pre ++ encRequest h b ++ rest).toArray⟩ pre.length =
      ([⟨h, b, c, (H h b c).1, (H h b c).2⟩], .closed) :=
  serve_closes cfg H hv hb hc (by simp [checkRequest_clte hc hte hcl]) pre rest n

theorem readResponse_encode (method : Bytes) (is : List ResponseHead) {f : ResponseHead}
    {fb : Body} (pre rest : Bytes) (n : Nat) (hr : ResponsesFit method is f fb)
    (hn : is.length < n) :
    readResponse method ⟨(pre ++ encResponses is f fb ++ rest).toArray⟩ n pre.length =
      .ok (is, f, fb) (pre.length + (encResponses is f fb).length) :=
  Proofs.Pipeline.readResponse_encode method is pre rest n hr hn

theorem readResponses_encode (n : Nat) (rs : List (Bytes × List ResponseHead × ResponseHead × Body))
    (pre rest : Bytes) (hr : ∀ r ∈ rs, ResponsesFit r.1 r.2.1 r.2.2.1 r.2.2.2 ∧ r.2.1.length ≤ n) :
    readResponses
        ⟨(pre ++ (rs.map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten ++ rest).toArray⟩ n
        (rs.map (·.1)) pre.length =
      .ok (rs.map (·.2))
        (pre.length + (rs.map fun r => encResponses r.2.1 r.2.2.1 r.2.2.2).flatten.length) :=
  Proofs.Pipeline.readResponses_encode n rs pre rest hr

theorem mayAutoRetry_POST : mayAutoRetry (ascii "POST") = false := by decide
theorem mayAutoRetry_PUT : mayAutoRetry (ascii "PUT") = true := by decide

end Silmaril.Net.Http1
