module

public import Silmaril.Net.Udp.Network.Defs
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# An institution of UDP socket semantics

An institution (`Silmaril.Logic.Institution`: a functor `Sig ⥤ Room`) whose models are
socket-level UDP semantics (sets of observation traces, `Udp.Network.Obs`) and whose sentences
are properties of datagram delivery:

| institution | here |
| --- | --- |
| signatures | `Sig`: endpoint symbols (`Ep`: the sockets an obligation names) and payload-kind symbols (`Kind`: the classes of datagrams an upper protocol recognizes) |
| signature morphisms | `Sig.Hom`: maps of both kinds of symbols (extension, renaming, identification) |
| sentences | `Sen A`: well-formed sends, port isolation, authenticity, no duplication, reliable FIFO delivery and payload filtering at named endpoints; negation and conjunction |
| models | `Model A`: a trace set over the socket API, with each endpoint symbol interpreted as an endpoint and each kind symbol as a recognizer of payloads |
| model reduct | `Model.reduct σ`: the same traces, symbols interpreted through `σ` |
| satisfaction | `Sat M φ`: every trace of `M` has the property (`Holds`) |

**Why these sentences.** A sentence names endpoints and payload kinds only through symbols, and
says nothing about the endpoints its symbols do not denote. This is what makes satisfaction
invariant under reducts (`Inst.Thms.sat_map_iff`), as in the HTTP/1.1 institution
(`Silmaril.Net.Http1.Inst`), whose design this follows.

**Reliability is a sentence, not an assumption.** `noDup e` and `fifo s d` are the properties
a reliable transport would have. `Inst.Thms` proves that the network model of
`Udp.Network` (`Model.net`), at any bound endpoint, *violates* both (duplication, reordering),
and violates `onlyKind e k` for any kind that rejects some payload (plain UDP delivers whatever
anyone sends). It satisfies `sendsWF` and `addressed e` (port isolation) always, and
`authentic e` exactly when no off-path packets arrive. An upper protocol that needs more (QUIC
needs no duplication and no forgery) must establish it itself (`Udp.QuicCarrier`).

**Socket API, not packets.** Models are trace sets over socket observations; the packet network
of `Udp.Network` is one way to produce them (`Model.net`), and a host that implements UDP
differently is another model of the same signature.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Net.Udp.Inst

open CategoryTheory Silmaril.Logic.Institution Silmaril.Net.Channel Silmaril.Net.Udp.Network

/-- A vocabulary: endpoint symbols and payload-kind symbols. -/
structure Sig where
  Ep : Type
  Kind : Type

/-- A signature morphism: maps of both kinds of symbols. -/
@[ext] structure Sig.Hom (A B : Sig) where
  ep : A.Ep → B.Ep
  kind : A.Kind → B.Kind

instance : Category Sig where
  Hom := Sig.Hom
  id _ := ⟨id, id⟩
  comp σ τ := ⟨τ.ep ∘ σ.ep, τ.kind ∘ σ.kind⟩

/-- **Sentences**: obligations of a UDP socket semantics. -/
inductive Sen (A : Sig) : Type where
  /-- Every send the host accepts is of a well-formed message. -/
  | sendsWF
  /-- Every datagram received at `e` is addressed to `e` (port isolation). -/
  | addressed (e : A.Ep)
  /-- Every datagram received at `e` was sent before (no forgery). -/
  | authentic (e : A.Ep)
  /-- At every point, no datagram has been received at `e` more often than it was sent. -/
  | noDup (e : A.Ep)
  /-- The datagrams from `s` to `d` form a reliable FIFO channel: each receive at `d` is the
  oldest datagram from `s` not yet received (as a TCP byte stream would be). -/
  | fifo (s d : A.Ep)
  /-- Every datagram received at `e` has a payload of kind `k`. -/
  | onlyKind (e : A.Ep) (k : A.Kind)
  | neg (φ : Sen A)
  | conj (φ ψ : Sen A)

/-- Sentence translation. -/
def Sen.map {A B : Sig} (σ : Sig.Hom A B) : Sen A → Sen B
  | .sendsWF => .sendsWF
  | .addressed e => .addressed (σ.ep e)
  | .authentic e => .authentic (σ.ep e)
  | .noDup e => .noDup (σ.ep e)
  | .fifo s d => .fifo (σ.ep s) (σ.ep d)
  | .onlyKind e k => .onlyKind (σ.ep e) (σ.kind k)
  | .neg φ => .neg (φ.map σ)
  | .conj φ ψ => .conj (φ.map σ) (ψ.map σ)

/-- **A model**: a socket semantics (its observation traces) with an interpretation of the
symbols. -/
structure Model (A : Sig) : Type where
  ep : A.Ep → Endpoint
  kind : A.Kind → List UInt8 → Bool
  traces : Set (List Obs)

/-! ## Trace properties (vocabulary-free) -/

/-- The messages of accepted sends. -/
def sentMsgs : List Obs → List Msg
  | [] => []
  | .send m :: t => m :: sentMsgs t
  | _ :: t => sentMsgs t

/-- The channel from `s` to `d`: sends from `s` to `d`, and receives at `d` of datagrams from
`s`. -/
def Obs.link (s d : Endpoint) : Obs → Option (Ev Msg)
  | .send m => if m.src = s ∧ m.dst = d then some (.send m) else none
  | .recv a m => if a = d ∧ m.src = s then some (.recv m) else none
  | _ => none

/-- The vocabulary-free trace properties. -/
def SendsWF (t : List Obs) : Prop := ∀ m, Obs.send m ∈ t → m.WF

def Addressed (a : Endpoint) (t : List Obs) : Prop := ∀ m, Obs.recv a m ∈ t → m.dst = a

def Authentic (a : Endpoint) (t : List Obs) : Prop :=
  ∀ pre m post, t = pre ++ Obs.recv a m :: post → m ∈ sentMsgs pre

def NoDup (a : Endpoint) (t : List Obs) : Prop :=
  ∀ pre, pre <+: t → ∀ m, (recvAt a pre).count m ≤ (sentMsgs pre).count m

def FifoLink (s d : Endpoint) (t : List Obs) : Prop := Fifo (t.filterMap (Obs.link s d))

def OnlyKind (a : Endpoint) (k : List UInt8 → Bool) (t : List Obs) : Prop :=
  ∀ m, Obs.recv a m ∈ t → k m.data = true

/-- **Satisfaction.** -/
def Sat {A : Sig} (M : Model A) : Sen A → Prop
  | .sendsWF => ∀ t ∈ M.traces, SendsWF t
  | .addressed e => ∀ t ∈ M.traces, Addressed (M.ep e) t
  | .authentic e => ∀ t ∈ M.traces, Authentic (M.ep e) t
  | .noDup e => ∀ t ∈ M.traces, NoDup (M.ep e) t
  | .fifo s d => ∀ t ∈ M.traces, FifoLink (M.ep s) (M.ep d) t
  | .onlyKind e k => ∀ t ∈ M.traces, OnlyKind (M.ep e) (M.kind k) t
  | .neg φ => ¬ Sat M φ
  | .conj φ ψ => Sat M φ ∧ Sat M ψ

/-- The reduct of a model along a signature morphism: the same traces, the symbols interpreted
through `σ`. -/
def Model.reduct {A B : Sig} (σ : Sig.Hom A B) (M : Model B) : Model A :=
  ⟨M.ep ∘ σ.ep, M.kind ∘ σ.kind, M.traces⟩

/-- `M` satisfies every sentence of `T`. -/
def SatAll {A : Sig} (M : Model A) (T : List (Sen A)) : Prop := ∀ φ ∈ T, Sat M φ

/-! ## The network model -/

/-- **The network model**: the observable traces of `Udp.Network` under the host
configuration `C`, with an interpretation of the symbols. -/
def Model.net {A : Sig} (C : Config) (ep : A.Ep → Endpoint) (kind : A.Kind → List UInt8 → Bool) :
    Model A := ⟨ep, kind, Network.traces C⟩

/-- The obligations every host meets at the endpoint `e`: well-formed sends and port
isolation. -/
def hostCore {A : Sig} (e : A.Ep) : List (Sen A) := [.sendsWF, .addressed e]

/-! ## A vocabulary for a QUIC server -/

/-- Endpoint symbols of a QUIC deployment: the server's socket and a client's socket. -/
inductive QuicEp where
  | server
  | client
  deriving DecidableEq, Repr

/-- Payload kinds: datagrams whose first octet has the QUIC fixed bit set (RFC 9000 §17.2,
§17.3: "Fixed Bit: The next bit (0x40) of byte 0 is set to 1"; RFC 9443 uses this to
demultiplex QUIC from other protocols on one port). -/
inductive QuicKind where
  | fixedBit
  deriving DecidableEq, Repr

/-- The QUIC vocabulary. -/
abbrev QuicSig : Sig := ⟨QuicEp, QuicKind⟩

/-- The fixed-bit recognizer: a nonempty payload whose first octet has bit `0x40` set. -/
def fixedBitSet : List UInt8 → Bool
  | b :: _ => b &&& 0x40 != 0
  | [] => false

/-- The QUIC vocabulary extended with the symbols of a co-located protocol (endpoints `E`,
kinds `K`), and its inclusion. -/
abbrev QuicSig.extend (E K : Type) : Sig := ⟨QuicEp ⊕ E, QuicKind ⊕ K⟩

def QuicSig.incl (E K : Type) : Sig.Hom QuicSig (QuicSig.extend E K) := ⟨Sum.inl, Sum.inl⟩

end Silmaril.Net.Udp.Inst
