module

public import Silmaril.Net.Udp.Institution.Defs
public import Silmaril.Net.Udp.Network.Thms
import Silmaril.Proofs.Net.Udp.Institution

/-!
# The UDP institution: theorems and the institution

Proofs in `Silmaril/Proofs/Net/Udp/Institution.lean`, using only the standard axioms:

* `sat_map_iff`: **the satisfaction condition** `M ⊨ σ(φ) ↔ M|σ ⊨ φ`; `Sen.map_id`,
  `Sen.map_comp`: translation is functorial. So `inst : Sig ⥤ Room` is an institution and
  `classic` is its Goguen–Burstall form.
* `net_hostCore`, `net_authentic`: the network model meets the host obligations at every
  endpoint, and is authentic when no off-path packets arrive.
* `net_not_authentic`, `net_not_noDup`, `net_not_fifo`, `net_not_onlyKind`: at every bound
  endpoint the network model violates authenticity (with off-path packets), no-duplication,
  reliable FIFO delivery and payload filtering. UDP's unreliability is proved, not assumed
  away.
* `quic_conservative`: a deployment that adds a co-located protocol's symbols to the QUIC
  vocabulary satisfies a translated QUIC obligation iff its QUIC reduct does.
-/

@[expose] public section

namespace Silmaril.Net.Udp.Inst

open Silmaril.Net.Ip
open CategoryTheory Silmaril.Logic.Institution Silmaril.Net.Udp.Network

theorem sat_map_iff {A B : Sig} (σ : A ⟶ B) (M : Model B) (φ : Sen A) :
    Sat M (φ.map σ) ↔ Sat (M.reduct σ) φ :=
  Proofs.Institution.sat_map_iff σ M φ

theorem Sen.map_id {A : Sig} (φ : Sen A) : φ.map (𝟙 A) = φ := Proofs.Institution.map_id φ

theorem Sen.map_comp {A B C : Sig} (σ : A ⟶ B) (τ : B ⟶ C) (φ : Sen A) :
    φ.map (σ ≫ τ) = (φ.map σ).map τ := Proofs.Institution.map_comp σ τ φ

/-- The room of a vocabulary: obligations, socket semantics (discrete), satisfaction. -/
def room (A : Sig) : Room.{0, 0, 0} :=
  ⟨Sen A, Cat.of (Discrete (Model A)), fun M φ => Sat (Discrete.as M) φ⟩

/-- The corridor of a signature morphism. -/
def corridor {A B : Sig} (σ : A ⟶ B) : room A ⟶ room B :=
  ⟨Sen.map σ, Discrete.functor fun (M : Model B) => Discrete.mk (M.reduct σ),
    fun M φ => sat_map_iff σ (Discrete.as M) φ⟩

/-- **The UDP institution**, as a functor into rooms. -/
def inst : Sig ⥤ Room.{0, 0, 0} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext fun φ => Sen.map_id φ)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))
  map_comp σ τ := Room.hom_ext (funext fun φ => Sen.map_comp σ τ φ)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))

/-- The UDP institution in the direct form. -/
def classic : ClassicInstitution.{1, 0, 0, 0, 0} Sig := ClassicInstitution.ofRoomFunctor inst

/-! ## The network model -/

/-- The reduct of a network model is the network model with the composed interpretation. -/
theorem net_reduct {A B : Sig} (σ : A ⟶ B) (C : Config) (ep : B.Ep → Endpoint)
    (kind : B.Kind → List UInt8 → Bool) :
    (Model.net C ep kind).reduct σ = Model.net C (ep ∘ σ.ep) (kind ∘ σ.kind) := rfl

/-- Every host meets the host obligations, at every endpoint. -/
theorem net_hostCore {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) : SatAll (Model.net C ep kind) (hostCore e) :=
  Proofs.Institution.net_hostCore C ep kind e

/-- Without off-path packets, every datagram received was sent. -/
theorem net_authentic {A : Sig} {C : Config} (hC : C.offPath = false) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) : Sat (Model.net C ep kind) (.authentic e) :=
  Proofs.Institution.net_authentic hC ep kind e

/-- With off-path packets, a bound endpoint can receive a datagram nobody sent. -/
theorem net_not_authentic {A : Sig} {C : Config} (hC : C.offPath = true) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) (hb : C.bound (ep e) = true) :
    Sat (Model.net C ep kind) (.neg (.authentic e)) :=
  Proofs.Institution.net_not_authentic hC ep kind e hb

/-- UDP duplicates: at a bound endpoint, `noDup` fails. -/
theorem net_not_noDup {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) (hb : C.bound (ep e) = true) :
    Sat (Model.net C ep kind) (.neg (.noDup e)) :=
  Proofs.Institution.net_not_noDup C ep kind e hb

/-- UDP reorders: at a bound endpoint, reliable FIFO delivery fails. -/
theorem net_not_fifo {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) (hb : C.bound (ep e) = true) :
    Sat (Model.net C ep kind) (.neg (.fifo e e)) :=
  Proofs.Institution.net_not_fifo C ep kind e hb

/-- UDP does not filter payloads: a kind that rejects some payload is not guaranteed. -/
theorem net_not_onlyKind {A : Sig} (C : Config) (ep : A.Ep → Endpoint)
    (kind : A.Kind → List UInt8 → Bool) (e : A.Ep) (k : A.Kind) (hb : C.bound (ep e) = true)
    (bs : List UInt8) (hbs : 8 + bs.length < 65536) (hk : kind k bs = false) :
    Sat (Model.net C ep kind) (.neg (.onlyKind e k)) :=
  Proofs.Institution.net_not_onlyKind C ep kind e k hb bs hbs hk

/-- A QUIC server socket on plain UDP receives datagrams without the QUIC fixed bit (a QUIC
stack must discard them itself, RFC 9000 §5.2). -/
theorem quic_server_unfiltered (C : Config) (ep : QuicEp → Endpoint)
    (hb : C.bound (ep .server) = true) :
    Sat (A := QuicSig) (Model.net C ep fun _ => fixedBitSet) (.neg (.onlyKind .server .fixedBit)) :=
  net_not_onlyKind (A := QuicSig) C ep (fun _ => fixedBitSet) QuicEp.server QuicKind.fixedBit hb [0]
    (by decide) (by decide)

/-- **Conservativity** for co-located protocols: an extended deployment satisfies a translated
QUIC obligation iff its QUIC reduct does. -/
theorem quic_conservative {E K : Type} (X : Model (QuicSig.extend E K)) (φ : Sen QuicSig) :
    Sat X (φ.map (QuicSig.incl E K)) ↔ Sat (X.reduct (QuicSig.incl E K)) φ :=
  sat_map_iff (A := QuicSig) (B := QuicSig.extend E K) (QuicSig.incl E K) X φ

end Silmaril.Net.Udp.Inst
