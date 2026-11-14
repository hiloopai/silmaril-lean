module

public import Silmaril.Servers.Core.Defs
public import Silmaril.Net.Http1.Institution.Defs

/-!
# HTTP/1.1 implementations as servers: the exchange reading of the HTTP/1.1 institution

`Silmaril.Net.Http1.Inst` is an institution whose models are HTTP/1.1 implementations
(`Impl`: request framing, keep-alive decision, implemented codings, response relation) and
whose sentences are protocol obligations. This module reads an implementation as a server of
the core (`Silmaril.Servers.Core`): over the interface `wireSig` of framed HTTP/1.1 messages
(heads and bodies, as octets), `implServer I` is the atomic-handler server of its response
relation, with overlapping requests answered independently.

**Which obligations survive the reading.** `respRel M φ` translates the obligations about
responses (`status`, `notStatus`, `respField`, `noRespField`, `unknownMethods`,
`headNoContent`, `wellFramed`, and conjunctions of these) into relations between a request and
its response. For those, satisfaction in the HTTP/1.1 institution is satisfaction of the atomic
trace sentence by the server (`Thms.sat_iff_server_sat`): a proved observation map, in the
direction institution → traces, at the level of sentences.

The other obligations (`framesSafely`, `closesOnClTe`, `implements`, negations) concern request
framing, connection management or capabilities, which the exchange reading forgets: `respRel`
is `none` for them, and `Thms.closesOnClTe_not_observable` shows two implementations with the
same server, one satisfying `closesOnClTe` and one violating it. So the exchange reading is a
projection: equal servers do not give equal wire-level obligations.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Servers.Http1Bridge

open Silmaril.Servers
open Silmaril.Net.Http1 Silmaril.Net.Http1.Inst

/-- **Framed HTTP/1.1 messages**: a request head and body, a response head and body. -/
abbrev wireSig : Silmaril.Servers.Sig := ⟨RequestHead × Body, ResponseHead × Body⟩

/-- The exchanges an implementation allows. -/
def exch (I : Impl) (q : RequestHead × Body) (p : ResponseHead × Body) : Prop :=
  I.responds q.1 q.2 p.1 p.2

/-- **The server of an implementation**: the atomic-handler server of its response relation. -/
def implServer (I : Impl) : Silmaril.Servers.Model wireSig :=
  (Machine.ofRel (A := wireSig) (exch I)).server ()

/-- **The exchange relation of a response obligation** (`none` for the obligations about
framing, connections and capabilities, and for negations). -/
def respRel {A : Inst.Sig} (M : Inst.Model A) :
    Inst.Sen A → Option (RequestHead × Body → ResponseHead × Body → Prop)
  | .status m r cs => some fun q p =>
      q.1.Valid → q.1.line.method = M.meth m → r q.1.line.target = true → p.1.line.code ∈ cs
  | .notStatus m r cs => some fun q p =>
      q.1.Valid → q.1.line.method = M.meth m → r q.1.line.target = true → p.1.line.code ∉ cs
  | .respField m r f => some fun q p =>
      q.1.Valid → q.1.line.method = M.meth m → r q.1.line.target = true →
        fieldValues p.1.fields (M.fld f) ≠ []
  | .noRespField f => some fun _ p => fieldValues p.1.fields (M.fld f) = []
  | .unknownMethods ks cs => some fun q p =>
      q.1.Valid → q.1.line.method ∉ ks.map M.meth → p.1.line.code ∈ cs
  | .headNoContent => some fun q p => q.1.line.method = methodHEAD → encBody p.2 = []
  | .wellFramed => some fun q p =>
      p.1.Valid ∧ p.2.Fits (responseBodyLength q.1.line.method p.1.line.code p.1.fields)
  | .conj φ ψ => match respRel M φ, respRel M ψ with
      | some R, some S => some fun q p => R q p ∧ S q p
      | _, _ => none
  | _ => none

end Silmaril.Servers.Http1Bridge
