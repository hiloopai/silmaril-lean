module

public import Silmaril.Net.Http1.Pipeline.Defs
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# An institution of HTTP/1.1 implementations

An institution (`Silmaril.Logic.Institution`: a functor `Sig ⥤ Room`) whose models are
HTTP/1.1 implementations and whose sentences are protocol obligations, both RFC requirements
and the behaviour of a particular service:

| institution | here |
| --- | --- |
| signatures | `Sig`: a vocabulary of method symbols, field-name symbols and transfer-coding symbols |
| signature morphisms | `Sig.Hom`: maps of the three kinds of symbols (extension, renaming, identification) |
| sentences | `Sen Σ`: obligations about responses to methods on routes, response fields, implemented codings, request framing, connection closure and `HEAD`; negation and conjunction |
| models | `Model Σ`: an implementation (`Impl`: its request framing, its keep-alive decision, the codings it implements and its response relation), with an interpretation of each symbol as octets |
| model reduct | `Model.reduct σ`: the same implementation, symbols interpreted through `σ` |
| satisfaction | `Sat M φ` |

**Why these sentences.** A sentence quantifies over requests and responses only through the
octets that its symbols denote in the model, or not at all. An obligation such as "an
unrecognised method is answered `501`" cannot be a sentence when *recognised* means "denoted by
some symbol": it would not be invariant under reducts. The sentence `unknownMethods known codes`
names the recognised methods explicitly, and so it is invariant. As in the machine institution
(`Silmaril.Automata.Inst`), the satisfaction condition (`sat_map_iff`) holds because of this
choice.

**Three classes of models.** The standard vocabulary `Std` names the methods of RFC 9110 §9.3,
the framing and connection fields and the registered codings. Its standard interpretation is
`Model.Standard`, and `rfcCore` lists the protocol obligations that every compliant HTTP/1.1
server has:

* a **vanilla** implementation is a standard model of `Std` that satisfies `rfcCore`;
* an **extension-compliant** implementation is a model of an extended vocabulary
  `Std.extend M F C` (extension methods, fields, codings), whose reduct along the inclusion
  `Sig.incl` is vanilla, and which satisfies its extension's own sentences;
* a **noncompliant** implementation violates a sentence of `rfcCore`, and `Violates M φ`
  records which one.

The satisfaction condition then says that an extension is **conservative**: an extended
implementation satisfies the translation of a vanilla obligation iff its vanilla reduct
satisfies the obligation (`ExtensionCompliant.reduct_vanilla`). `Institution.Thms` gives
`refModel`, the reference server of `Silmaril.Net.Http1.Pipeline` read as a model, and proves
that it is vanilla for every compliant profile and every well-behaved handler. It also proves
that the `Content-Length`-first and keep-alive-always variants violate `rfcCore`.
-/

@[expose] public section

namespace Silmaril.Net.Http1.Inst

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Parse.ByteParse (Bytes)

/-- A vocabulary: method, field-name and transfer-coding symbols. -/
structure Sig where
  Meth : Type
  Fld : Type
  Cod : Type

/-- A signature morphism: maps of the three kinds of symbols. -/
@[ext] structure Sig.Hom (A B : Sig) where
  meth : A.Meth → B.Meth
  fld : A.Fld → B.Fld
  cod : A.Cod → B.Cod

instance : Category Sig where
  Hom := Sig.Hom
  id _ := ⟨id, id, id⟩
  comp σ τ := ⟨τ.meth ∘ σ.meth, τ.fld ∘ σ.fld, τ.cod ∘ σ.cod⟩

/-- A route: which request targets an obligation is about (vocabulary-free). -/
abbrev Route := Bytes → Bool

/-- Sentences: obligations of an HTTP/1.1 implementation. -/
inductive Sen (A : Sig) : Type where
  /-- Every response to a valid request with method `m` on `route` has a status in `codes`. -/
  | status (m : A.Meth) (route : Route) (codes : List Nat)
  /-- No response to a valid request with method `m` on `route` has a status in `codes`. -/
  | notStatus (m : A.Meth) (route : Route) (codes : List Nat)
  /-- Every response to a valid request with method `m` on `route` carries the field `f`. -/
  | respField (m : A.Meth) (route : Route) (f : A.Fld)
  /-- No response carries the field `f`. -/
  | noRespField (f : A.Fld)
  /-- The implementation implements the transfer coding `c` (RFC 9112 §7). -/
  | implements (c : A.Cod)
  /-- A valid request whose method is none of `known` is answered with a status in `codes`
  (RFC 9110 §9.1: `501` for an unrecognised method). -/
  | unknownMethods (known : List A.Meth) (codes : List Nat)
  /-- Request framing is the reference framing or a rejection (RFC 9112 §6.1, §6.3). -/
  | framesSafely
  /-- After a request with both `Transfer-Encoding` and `Content-Length` the connection
  closes (RFC 9112 §6.3 rule 3). -/
  | closesOnClTe
  /-- A response to `HEAD` has no content (RFC 9110 §9.3.2). -/
  | headNoContent
  /-- Every response has a valid head and a body that fits its framing (RFC 9112 §4–§6). -/
  | wellFramed
  | neg (φ : Sen A)
  | conj (φ ψ : Sen A)

/-- Sentence translation. -/
def Sen.map {A B : Sig} (σ : Sig.Hom A B) : Sen A → Sen B
  | .status m r cs => .status (σ.meth m) r cs
  | .notStatus m r cs => .notStatus (σ.meth m) r cs
  | .respField m r f => .respField (σ.meth m) r (σ.fld f)
  | .noRespField f => .noRespField (σ.fld f)
  | .implements c => .implements (σ.cod c)
  | .unknownMethods ks cs => .unknownMethods (ks.map σ.meth) cs
  | .framesSafely => .framesSafely
  | .closesOnClTe => .closesOnClTe
  | .headNoContent => .headNoContent
  | .wellFramed => .wellFramed
  | .neg φ => .neg (φ.map σ)
  | .conj φ ψ => .conj (φ.map σ) (ψ.map σ)

/-- An HTTP/1.1 implementation, independent of any vocabulary. -/
structure Impl where
  /-- The framing it gives a request (RFC 9112 §6.3). -/
  frame : Version → List FieldLine → BodyLength
  /-- Whether it keeps the connection open after answering a request (RFC 9112 §9.3). -/
  keep : RequestHead → ResponseHead → Bool
  /-- The transfer codings it implements, by name. -/
  implements : Bytes → Bool
  /-- Its responses: `responds h b rh rb` when it may answer the request `(h, b)` with
  `(rh, rb)` (nondeterministic). -/
  responds : RequestHead → Body → ResponseHead → Body → Prop

/-- A model: an implementation with an interpretation of the symbols as octets. -/
structure Model (A : Sig) : Type where
  meth : A.Meth → Bytes
  fld : A.Fld → Bytes
  cod : A.Cod → Bytes
  impl : Impl

/-- The responses to valid requests with method `m` on `route` satisfy `P`. -/
def Model.onRoute {A : Sig} (M : Model A) (m : Bytes) (route : Route)
    (P : ResponseHead → Body → Prop) : Prop :=
  ∀ h b rh rb, h.Valid → h.line.method = m → route h.line.target = true →
    M.impl.responds h b rh rb → P rh rb

/-- Satisfaction. -/
def Sat {A : Sig} (M : Model A) : Sen A → Prop
  | .status m r cs => M.onRoute (M.meth m) r fun rh _ => rh.line.code ∈ cs
  | .notStatus m r cs => M.onRoute (M.meth m) r fun rh _ => rh.line.code ∉ cs
  | .respField m r f => M.onRoute (M.meth m) r fun rh _ => fieldValues rh.fields (M.fld f) ≠ []
  | .noRespField f => ∀ h b rh rb, M.impl.responds h b rh rb → fieldValues rh.fields (M.fld f) = []
  | .implements c => M.impl.implements (M.cod c) = true
  | .unknownMethods ks cs => ∀ h b rh rb, h.Valid → h.line.method ∉ ks.map M.meth →
      M.impl.responds h b rh rb → rh.line.code ∈ cs
  | .framesSafely => ∀ v fs, M.impl.frame v fs = rfcRequestFraming v fs ∨ M.impl.frame v fs = .invalid
  | .closesOnClTe => ∀ h rh, transferCodings h.fields ≠ [] →
      fieldElements h.fields contentLengthName ≠ [] → M.impl.keep h rh = false
  | .headNoContent => ∀ h b rh rb, h.line.method = methodHEAD → M.impl.responds h b rh rb →
      encBody rb = []
  | .wellFramed => ∀ h b rh rb, M.impl.responds h b rh rb →
      rh.Valid ∧ rb.Fits (responseBodyLength h.line.method rh.line.code rh.fields)
  | .neg φ => ¬ Sat M φ
  | .conj φ ψ => Sat M φ ∧ Sat M ψ

/-- The reduct of a model along a signature morphism: the same implementation, the symbols
interpreted through `σ`. -/
def Model.reduct {A B : Sig} (σ : Sig.Hom A B) (M : Model B) : Model A :=
  ⟨M.meth ∘ σ.meth, M.fld ∘ σ.fld, M.cod ∘ σ.cod, M.impl⟩

/-- `M` satisfies every sentence of `T`. -/
def SatAll {A : Sig} (M : Model A) (T : List (Sen A)) : Prop := ∀ φ ∈ T, Sat M φ

/-- `M` violates `φ`. -/
def Violates {A : Sig} (M : Model A) (φ : Sen A) : Prop := ¬ Sat M φ

/-! ## The standard vocabulary -/

/-- The methods of RFC 9110 §9.3. -/
inductive StdMethod where
  | get | head | post | put | delete | connect | options | trace
  deriving DecidableEq, Repr

/-- The fields whose meaning RFC 9110 and RFC 9112 fix for framing and connections. -/
inductive StdField where
  | contentLength | transferEncoding | host | connection | te | upgrade | trailer
  | contentType | allow | location
  deriving DecidableEq, Repr

/-- The registered transfer codings (RFC 9112 §7). -/
inductive StdCoding where
  | chunked | compress | deflate | gzip
  deriving DecidableEq, Repr

/-- The standard vocabulary. -/
def Std : Sig := ⟨StdMethod, StdField, StdCoding⟩

def StdMethod.token : StdMethod → Bytes
  | .get => ascii "GET" | .head => ascii "HEAD" | .post => ascii "POST" | .put => ascii "PUT"
  | .delete => ascii "DELETE" | .connect => ascii "CONNECT" | .options => ascii "OPTIONS"
  | .trace => ascii "TRACE"

def StdField.name : StdField → Bytes
  | .contentLength => contentLengthName | .transferEncoding => transferEncodingName
  | .host => hostName | .connection => connectionName | .te => teName | .upgrade => upgradeName
  | .trailer => ascii "trailer" | .contentType => ascii "content-type" | .allow => ascii "allow"
  | .location => ascii "location"

def StdCoding.name : StdCoding → Bytes
  | .chunked => chunkedName | .compress => compressName | .deflate => deflateName
  | .gzip => gzipName

/-- The standard interpretation of the standard vocabulary. -/
def Model.Standard (M : Model Std) : Prop :=
  M.meth = StdMethod.token ∧ M.fld = StdField.name ∧ M.cod = StdCoding.name

/-- The protocol obligations of every compliant HTTP/1.1 server, as sentences of `Std`:
safe request framing (RFC 9112 §6.1, §6.3, §11.2), closure after `Transfer-Encoding` with
`Content-Length` (§6.3 rule 3), no content in responses to `HEAD` (RFC 9110 §9.3.2),
well-framed responses (RFC 9112 §4–§6) and the chunked coding (§6.1: "A recipient MUST be able
to parse the chunked transfer coding"). -/
def rfcCore : List (Sen Std) :=
  [.framesSafely, .closesOnClTe, .headNoContent, .wellFramed, .implements StdCoding.chunked]

/-- A vanilla HTTP/1.1 implementation. -/
def Vanilla (M : Model Std) : Prop := M.Standard ∧ SatAll M rfcCore

/-- A vocabulary with extension methods `M`, fields `F` and codings `C`. -/
def Sig.extend (A : Sig) (M F C : Type) : Sig := ⟨A.Meth ⊕ M, A.Fld ⊕ F, A.Cod ⊕ C⟩

/-- The inclusion into an extended vocabulary. -/
def Sig.incl (A : Sig) (M F C : Type) : Sig.Hom A (A.extend M F C) := ⟨Sum.inl, Sum.inl, Sum.inl⟩

/-- An extension-compliant implementation of the extension theory `T`: its vanilla reduct is
standard, it satisfies the vanilla obligations translated into the extension, and it
satisfies `T`. -/
def ExtensionCompliant {M F C : Type} (T : List (Sen (Std.extend M F C)))
    (X : Model (Std.extend M F C)) : Prop :=
  (X.reduct (Std.incl M F C)).Standard ∧ SatAll X (rfcCore.map (Sen.map (Std.incl M F C))) ∧
    SatAll X T

/-! ## The reference server as a model -/

/-- `HEAD` responses are sent without content (RFC 9110 §9.3.2). -/
def stripHead (h : RequestHead) (r : ResponseHead × Body) : ResponseHead × Body :=
  if h.line.method = methodHEAD then (r.1, .none) else r

/-- The reference server of `Silmaril.Net.Http1.Pipeline` with configuration `cfg` and handler
`H`, as an implementation. -/
def refImpl (cfg : ServerConfig) (H : Handler) : Impl where
  frame := cfg.profile.frame
  keep h rh := match checkRequest cfg h with
    | .ok c => c.persistent && keepOpen cfg.keepAlive h rh
    | .error _ => false
  implements n := n = chunkedName || cfg.implements n
  responds h b rh rb := match checkRequest cfg h with
    | .ok c => (rh, rb) = stripHead h (H h b c)
    | .error e => (rh, rb) = stripHead h (errorResponse e.status)

/-- The reference server as a standard model. -/
def refModel (cfg : ServerConfig) (H : Handler) : Model Std :=
  ⟨StdMethod.token, StdField.name, StdCoding.name, refImpl cfg H⟩

/-- A handler is well behaved: its responses have valid heads, and bodies that fit their framing
(responses to `HEAD` are stripped by the server, so their bodies do not matter). -/
def Handler.WellFramed (H : Handler) : Prop :=
  ∀ h b c, (H h b c).1.Valid ∧ (h.line.method ≠ methodHEAD →
    (H h b c).2.Fits (responseBodyLength h.line.method (H h b c).1.line.code (H h b c).1.fields))

/-- A noncompliant variant: the connection is always kept open. -/
def keepAlwaysImpl (cfg : ServerConfig) (H : Handler) : Impl :=
  { refImpl cfg H with keep := fun _ _ => true }

/-! ## An extension: `PATCH` (RFC 5789) -/

/-- The vocabulary with the extension method `PATCH`. -/
abbrev PatchSig : Sig := Std.extend Unit Empty Empty

/-- `PATCH`. -/
def methodPATCH : Bytes := ascii "PATCH"

/-- A handler that applies `PATCH` (answering `204`) and allows no other method (`405`, with
`Allow`, RFC 9110 §15.5.6). -/
def patchHandler : Handler := fun h _ _ =>
  if h.line.method = methodPATCH then (⟨⟨Version.http11, 204, ascii "No Content"⟩, []⟩, .none)
  else (⟨⟨Version.http11, 405, ascii "Method Not Allowed"⟩,
    [⟨ascii "Allow", methodPATCH⟩, ⟨ascii "Content-Length", ascii "0"⟩]⟩, .content [])

/-- The reference server with `patchHandler`, as a model of the extended vocabulary. -/
def patchModel : Model PatchSig :=
  ⟨Sum.elim StdMethod.token fun _ => methodPATCH, Sum.elim StdField.name Empty.elim,
    Sum.elim StdCoding.name Empty.elim, refImpl {} patchHandler⟩

/-- The extension's obligation: a valid `PATCH` request is answered `204`, or rejected as a
request (`400`, `501`, `505`). -/
def patchTheory : List (Sen PatchSig) := [.status (Sum.inr ()) (fun _ => true) [204, 400, 501, 505]]

end Silmaril.Net.Http1.Inst
