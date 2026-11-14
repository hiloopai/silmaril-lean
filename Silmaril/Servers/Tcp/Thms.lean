module

public import Silmaril.Servers.Tcp.Defs
public import Silmaril.Servers.Transport.Thms
public import Silmaril.Servers.WasiBinaries.Thms
import Silmaril.Proofs.Servers.Tcp.Basic

/-!
# HTTP over a TCP byte stream: theorems

* **Reading with leftovers**:
  - `h1Read_msgs`: the messages are `Wire1`'s;
  - `h1Read_encode`: encoded valid requests are read back with nothing left over and no error;
  - `h1Read_rest_suffix`: the leftover is a suffix of the input.
* **Protocol selection**:
  - `select_mono`: a decision does not change as octets arrive;
  - `select_http1_ne_h2`: selecting HTTP/1.1 never serves HTTP/2;
  - `select_sniff_preface`, `select_prior_preface`: with sniffing or prior knowledge, the
    preface selects HTTP/2;
  - `select_sniff_get`, `select_prior_get`: on an HTTP/1.1 request line, sniffing gives
    HTTP/1.1 and prior knowledge refuses (no universal compatibility).
* **Implementing**:
  - `AtMost.mono` and `AtLeast.mono`: `AtMost` is monotone, and `AtLeast` antitone, in the
    obvious arguments;
  - `AtMost.sat`: a sentence of the HTTP model holds of every TCP-level trace through the
    reading;
  - `exactly_iff`: `Exactly` is equality of the image and the model.
* **Hello over TCP**:
  - `hello_atMost`: on port `p`, under HTTP/1.1 selection and without TLS, `helloTcp p`
    implements at most the per-request server of the `wasi:http` hello module (the denotation
    of `tests/servers/wasi-http/hello.wat`'s core module over typed hosts);
  - `hello_atMost_spec`: hence at most the function server of `200 hello`;
  - `hello_realizes`: it realizes every single exchange of a served request.

  `Exactly` is not claimed. The reading names requests `⟨c, k⟩` in connection order and
  lists connections one after another, while the HTTP model allows any identities and any
  interleaving.
-/

@[expose] public section

namespace Silmaril.Servers.Tcp

open Silmaril.Servers.Transport Silmaril.Servers.Wire1
open Silmaril.Net.Http1
open Silmaril.Net.Http (Request Response)

/-! ## Reading -/

theorem h1Read_msgs (bs : List UInt8) : (h1Read bs).msgs.map toRequest = requests bs := by
  simp only [h1Read, requests, Proofs.Servers.Tcp.readReqs_fst]

theorem h1Read_encode (ms : List WireReq) (hv : ∀ m ∈ ms, ReqOk m) :
    h1Read (encRequests ms) = ⟨ms, [], false⟩ :=
  Proofs.Servers.Tcp.h1Read_encode ms hv

theorem h1Read_rest_suffix (bs : List UInt8) : (h1Read bs).rest <:+ bs := List.drop_suffix _ _

/-! ## Protocol selection -/

theorem select_mono {s : Select} {a : Option (List UInt8)} {bs : List UInt8} {p : Proto}
    (h : select s a bs = some p) (more : List UInt8) : select s a (bs ++ more) = some p :=
  Proofs.Servers.Tcp.select_mono h more

theorem select_http1_ne_h2 (a : Option (List UInt8)) (bs : List UInt8) :
    select .http1 a bs ≠ some .h2 := by simp [select]

theorem select_sniff_preface (more : List UInt8) :
    select .sniffPreface none (h2Preface ++ more) = some .h2 :=
  select_mono (bs := h2Preface) (by decide) more

theorem select_prior_preface (more : List UInt8) :
    select .h2PriorKnowledge none (h2Preface ++ more) = some .h2 :=
  select_mono (bs := h2Preface) (by decide) more

/-- `GET ` (an HTTP/1.1 request line starts so). -/
def getPrefix : List UInt8 := [0x47, 0x45, 0x54, 0x20]

theorem select_sniff_get (more : List UInt8) :
    select .sniffPreface none (getPrefix ++ more) = some .h1 :=
  select_mono (bs := getPrefix) (by decide) more

theorem select_prior_get (more : List UInt8) :
    select .h2PriorKnowledge none (getPrefix ++ more) = some .refused :=
  select_mono (bs := getPrefix) (by decide) more

/-! ## Implementing an HTTP server -/

variable {Addr : Type} {A : Servers.Sig}

theorem AtMost.mono {ρ : PMap (TTrace Addr) (Servers.Trace A)} {T T' : TModel Addr}
    {M M' : Servers.Model A} (h : AtMost ρ T M) (hT : T' ⊆ T) (hM : M ≤ M') : AtMost ρ T' M' :=
  fun t ht => hM t (h t (PMap.image_mono ρ hT ht))

theorem AtLeast.mono {ρ : PMap (TTrace Addr) (Servers.Trace A)} {T T' : TModel Addr}
    {M M' : Servers.Model A} (h : AtLeast ρ T M) (hT : T ⊆ T') (hM : M' ≤ M) : AtLeast ρ T' M' :=
  fun t ht => PMap.image_mono ρ hT (h t (hM t ht))

/-- A sentence of the HTTP model holds of every TCP-level trace, read through `ρ`. -/
theorem AtMost.sat {ρ : PMap (TTrace Addr) (Servers.Trace A)} {T : TModel Addr}
    {M : Servers.Model A} (h : AtMost ρ T M) {φ : Servers.Sen A} (hM : M.Sat φ) :
    ∀ t ∈ T, ρ.pull φ t :=
  (PMap.sat_pull_iff ρ T φ).2 fun t ht => hM t (h t ht)

theorem exactly_iff {ρ : PMap (TTrace Addr) (Servers.Trace A)} {T : TModel Addr}
    {M : Servers.Model A} : Exactly ρ T M ↔ ρ.image T = {t | M.Tr t} :=
  ⟨fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2, fun h => ⟨fun t ht => (h ▸ ht : t ∈ {t | M.Tr t}),
    fun t ht => h ▸ (ht : t ∈ {t | M.Tr t})⟩⟩

/-! ## Hello over TCP -/

theorem helloWire_toResponse : toResponse helloWire = WasiExamples.helloResp :=
  Proofs.Servers.Tcp.helloWire_toResponse

/-- **Hello over TCP implements at most the `wasi:http` hello module's per-request server.** -/
theorem hello_atMost (p : Port) :
    AtMost (h1Reading (Addr := Addr) .http1 none p) (helloTcp p)
      (Exchange.fresh (WasiCore.wasiServerTy (WasiBinaries.den WasiBinaries.helloCore))) :=
  Proofs.Servers.Tcp.hello_atMost p

theorem hello_atMost_spec (p : Port) :
    AtMost (h1Reading (Addr := Addr) .http1 none p) (helloTcp p)
      (Servers.Model.ofFun fun _ => WasiExamples.helloResp) :=
  (hello_atMost p).mono subset_rfl WasiBinaries.helloBin_fresh

/-- **Hello over TCP realizes every single exchange of a served request.** -/
theorem hello_realizes (p : Port) (a : Addr) (m : WireReq) (hm : Served m) :
    [Servers.Event.recv ⟨0, 0⟩ (toRequest m), Servers.Event.send ⟨0, 0⟩ WasiExamples.helloResp] ∈
      (h1Reading (Addr := Addr) .http1 none p).image (helloTcp p) :=
  Proofs.Servers.Tcp.hello_realizes p a m hm

end Silmaril.Servers.Tcp
