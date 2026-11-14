module

public import Silmaril.Wasi.Versions.HttpOs.Defs
public import Silmaril.Wasi.Versions.SockOs.Thms
public import Silmaril.Wasi.Versions.HttpBody2Over.Thms

@[expose] public section

/-!
# The OS image of WASI HTTP: theorems

PROVED (standard axioms): the HTTP theories are observations of the network of their web.

* Per event (`evHttp2_ok`, `evHttp3_ok`, `evBody2_ok`, `evBody3_ok`): the image of a checked
  answer is admitted by `httpNet`.
* **Theories** (`httpTh_netOk`, `httpTh3_netOk`, `bodyTh_netOk`, `body3Th_netOk`): the image of
  every accepted trace is admitted.
* **Hosts** (`httpImpl_netOk`, `httpImpl3_netOk`, `bodyImpl_netOk`, `body3Impl_netOk`): every
  run of the concrete hosts has an admitted image.
* **Adapters** (`http3Over2_netOk`, `http2Over3_netOk`, `httpB3Over2_netOk`,
  `httpB2Over3_netOk`): over every host of the imported theory, the exported events of the
  composite have an admitted image (the same web on both sides).
* **The extended image** (`xHttp2_netOk`, `xHttp3_netOk`): a run accepted by the theory with
  bodies has an extended image admitted by the network, whose LPS part is the stdout image.

As for sockets (`Silmaril.Wasi.Versions.SockOs`), these are statements about the WASI layer in the
extended vocabulary; no x86 socket or HTTP syscall arm is involved.
-/

namespace Silmaril.Wasi.Versions.HttpOs

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.SockOs
open Silmaril.Wasm.Component (Val)
open Silmaril.Machine.Process.IoSpecNet

/-! ## Admitted events -/

/-- The outcome of an inner result that the web accepts is the connection outcome. -/
theorem innerOutcome_conn {W : Web} {k : Val × Val} {x : Val} {o : Option Nat}
    (h : innerOutcome x = some o) (hok : outcomeOk (W k.1 k.2) x = true) :
    connOf W (keyV k) = o := by
  have hc : connOf W (keyV k) = match W k.1 k.2 with | .status _ => none | .error c => some c := rfl
  rw [hc]
  unfold innerOutcome at h
  split at h
  · cases hW : W k.1 k.2 <;> simp_all [outcomeOk]
  · cases hW : W k.1 k.2 <;> simp_all [outcomeOk]
  · cases h

/-- A status the web accepts is in the inbox. -/
theorem statusIn_of_ok {W : Web} {body : Val × Val → List (BitVec 8)} {k : Val × Val}
    {s : BitVec 16} (h : statusOk W k (some [.u16 s]) = true) :
    (SockEv.recv (keyV k) (.u16 s) : SockEv Val).Admits (httpNet W body) := by
  show inboxOf W body (.record [k.1, k.2]) (.u16 s) = true
  cases hW : W k.1 k.2 <;> simp_all [inboxOf, statusIn, statusOk]

/-- A checked 0.2 `get` answer with an outcome: its connect event is admitted. -/
theorem get2_admits {W : Web} {body : Val × Val → List (BitVec 8)} {q : HttpSt} {h : BitVec 32}
    {rest : List Val} {x : Val} {k : Val × Val} {o : Option Nat} (hl : lookup h q.futs = some k)
    (ho : innerOutcome x = some o)
    (hc : httpOk W q (.imp futGet (.u32 h :: rest) (some [.variant 1 (some (.variant 0 (some x)))])) = true) :
    (SockEv.connect (hw h) (keyV k) o : SockEv Val).Admits (httpNet W body) := by
  have hok : outcomeOk (W k.1 k.2) x = true := by simpa [httpOk, hl, getOk] using hc
  exact innerOutcome_conn ho hok

/-- A checked 0.2 `status` answer of a tied response: its recv event is admitted. -/
theorem status2_admits {W : Web} {body : Val × Val → List (BitVec 8)} {q : HttpSt} {h : BitVec 32}
    {rest : List Val} {s : BitVec 16} {k : Val × Val} (hl : lookup h q.resps = some k)
    (hc : httpOk W q (.imp respStatus (.u32 h :: rest) (some [.u16 s])) = true) :
    (SockEv.recv (keyV k) (.u16 s) : SockEv Val).Admits (httpNet W body) := by
  have hok : statusOk W k (some [.u16 s]) = true := by
    simpa [httpOk, hl, show respStatus ≠ futGet by decide] using hc
  exact statusIn_of_ok hok

/-- **The image of a checked 0.2 outgoing answer is admitted.** -/
theorem evHttp2_ok (W : Web) (body : Val × Val → List (BitVec 8)) (q : HttpSt) (e : WEv)
    (h : httpOk W q e = true) : SockOk (httpNet W body) (evHttp2 q e) := by
  unfold evHttp2
  split
  · split
    · next hf =>
      subst hf
      split
      · next hl ho => exact sockOk_single (get2_admits hl ho h)
      · exact sockOk_nil
    · exact sockOk_nil
  · split
    · next hf =>
      subst hf
      split
      · next hl => exact sockOk_single (status2_admits hl h)
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- A checked 0.3 `send` answer with an outcome: its connect event is admitted. -/
theorem send3_admits {W : Web} {body : Val × Val → List (BitVec 8)} {q : Http3St} {r : BitVec 32}
    {rest : List Val} {x : Val} {o : Option Nat} (ho : innerOutcome x = some o)
    (hc : http3Ok W q (.imp send3 (.u32 r :: rest) (some [x])) = true) :
    (SockEv.connect (hw r) (keyV (q.key r)) o : SockEv Val).Admits (httpNet W body) := by
  have hok : sendOk (W (q.key r).1 (q.key r).2) (some [x]) = true := by simpa [http3Ok] using hc
  have hok' : outcomeOk (W (q.key r).1 (q.key r).2) x = true := by
    revert hok; unfold sendOk outcomeOk; split <;> simp_all
  exact innerOutcome_conn ho hok'

/-- A checked 0.3 `get-status-code` answer of a tied response: its recv event is admitted. -/
theorem status3_admits {W : Web} {body : Val × Val → List (BitVec 8)} {q : Http3St} {h : BitVec 32}
    {rest : List Val} {s : BitVec 16} {k : Val × Val} (hl : lookup h q.resps = some k)
    (hc : http3Ok W q (.imp getStatus3 (.u32 h :: rest) (some [.u16 s])) = true) :
    (SockEv.recv (keyV k) (.u16 s) : SockEv Val).Admits (httpNet W body) := by
  have hok : statusOk W k (some [.u16 s]) = true := by
    simpa [http3Ok, hl, show getStatus3 ≠ send3 by decide] using hc
  exact statusIn_of_ok hok

/-- **The image of a checked 0.3 outgoing answer is admitted.** -/
theorem evHttp3_ok (W : Web) (body : Val × Val → List (BitVec 8)) (q : Http3St) (e : WEv)
    (h : http3Ok W q e = true) : SockOk (httpNet W body) (evHttp3 q e) := by
  unfold evHttp3
  split
  · split
    · next hf =>
      subst hf
      split
      · next ho => exact sockOk_single (send3_admits ho h)
      · exact sockOk_nil
    · split
      · next hf' =>
        subst hf'
        split
        · next hl => exact sockOk_single (status3_admits hl h)
        · exact sockOk_nil
      · exact sockOk_nil
  · exact sockOk_nil

/-- A chunk of the rest of a body is a chunk of the body. -/
theorem chunk_infix {body bs : List (BitVec 8)} {n m : Nat} (h : bs = (body.drop n).take m) :
    bs <:+: body := by
  rw [h]
  exact (List.take_prefix m _).isInfix.trans (List.drop_suffix n _).isInfix

/-- A chunk of the body is in the inbox. -/
theorem chunkIn_of {W : Web} {body : Val × Val → List (BitVec 8)} {k : Val × Val}
    {vs : List Val} {bs : List (BitVec 8)} (hbs : u8sOf vs = some bs) (hi : bs <:+: body k) :
    (SockEv.recv (keyV k) (.record vs) : SockEv Val).Admits (httpNet W body) := by
  show inboxOf W body (.record [k.1, k.2]) (.record vs) = true
  simp [inboxOf, chunkIn, hbs, hi]

/-- A checked 0.2 read answer `ok(vs)` on a tracked stream: its chunk is admitted. -/
theorem read2_admits {B : BWeb} {k : Val × Val} {n len : Nat} {vs : List Val}
    (hok : readOk ((B.body k).drop n) len (some [.variant 0 (some (.record vs))]) = true) :
    (SockEv.recv (keyV k) (.record vs) : SockEv Val).Admits (httpNet B.web B.body) := by
  cases hbs : u8sOf vs with
  | none => simp [readOk, hbs] at hok
  | some bs =>
    have hbs' : bs = ((B.body k).drop n).take bs.length := by
      simp only [readOk, hbs, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.2
    exact chunkIn_of hbs (chunk_infix hbs')

/-- **The image of a checked 0.2 read answer is admitted.** -/
theorem chunkEv2_ok (B : BWeb) (q : BodySt) (e : WEv) (h : bodyCheck B q e = true) :
    SockOk (httpNet B.web B.body) (chunkEv2 q e) := by
  unfold chunkEv2
  split
  · next f hd rest vs =>
    split
    · next hf =>
      split
      · next k n hl => exact sockOk_single (read2_admits (by simpa [bodyCheck, hf, hl] using h))
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- A checked 0.3 `stream.read` answer `COMPLETED` on a tracked stream: its chunk is admitted. -/
theorem read3_admits {B : BWeb} {k : Val × Val} {n m c : Nat} {pv : BitVec 32} {vs : List Val}
    (hc : copy3 pv = some (some (.completed, c)))
    (hok : read3Ok ((B.body k).drop n) m (some [.u32 pv, .record vs]) = true) :
    (SockEv.recv (keyV k) (.record vs) : SockEv Val).Admits (httpNet B.web B.body) := by
  cases hbs : u8sOf vs with
  | none => simp [read3Ok, hc, hbs] at hok
  | some bs =>
    have hbs' : bs = ((B.body k).drop n).take c := by
      simp only [read3Ok, hc, hbs, Bool.and_eq_true, decide_eq_true_eq] at hok
      exact hok.2.1
    exact chunkIn_of hbs (chunk_infix hbs')

/-- **The image of a checked 0.3 `stream.read` answer is admitted.** -/
theorem chunkEv3_ok (B : BWeb) (q : Body3St) (e : WEv) (h : body3Check B q e = true) :
    SockOk (httpNet B.web B.body) (chunkEv3 q e) := by
  unfold chunkEv3
  split
  · next f hd rest pv vs =>
    split
    · next hf =>
      split
      · next k n c hl hc =>
        exact sockOk_single (read3_admits hc (by simpa [body3Check, hf, hl] using h))
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- **The image of a checked 0.2 answer with bodies is admitted.** -/
theorem evBody2_ok (B : BWeb) (q : BodySt) (e : WEv) (h : bodyOk B q e = true) :
    SockOk (httpNet B.web B.body) (evBody2 q e) := by
  have h' : httpOk B.web q.base e = true ∧ bodyCheck B q e = true := by
    simpa only [bodyOk, Bool.and_eq_true] using h
  exact sockOk_append (evHttp2_ok B.web B.body q.base e h'.1) (chunkEv2_ok B q e h'.2)

/-- **The image of a checked 0.3 answer with bodies is admitted.** -/
theorem evBody3_ok (B : BWeb) (q : Body3St) (e : WEv) (h : body3Ok B q e = true) :
    SockOk (httpNet B.web B.body) (evBody3 q e) := by
  have h' : http3Ok B.web q.base e = true ∧ body3Check B q e = true := by
    simpa only [body3Ok, Bool.and_eq_true] using h
  exact sockOk_append (evHttp3_ok B.web B.body q.base e h'.1) (chunkEv3_ok B q e h'.2)

/-! ## Theories are observations of the web -/

/-- **0.2 outgoing HTTP**: the image of an accepted trace is admitted by the web. -/
theorem httpTh_netOk (W : Web) (body : Val × Val → List (BitVec 8)) {t : List WEv}
    (h : (httpTh W).Accepts t) : SockOk (httpNet W body) (imgRun httpNext evHttp2 HttpSt.init t) :=
  imgRun_sockOk (evHttp2_ok W body) h

/-- **0.3 outgoing HTTP**: the image of an accepted trace is admitted by the web. -/
theorem httpTh3_netOk (W : Web) (body : Val × Val → List (BitVec 8)) {t : List WEv}
    (h : (httpTh3 W).Accepts t) : SockOk (httpNet W body) (imgRun http3Next evHttp3 {} t) :=
  imgRun_sockOk (evHttp3_ok W body) h

/-- **0.2 HTTP with bodies**: the image of an accepted trace is admitted by the body web. -/
theorem bodyTh_netOk (B : BWeb) {t : List WEv} (h : (bodyTh B).Accepts t) :
    SockOk (httpNet B.web B.body) (imgRun bodyNext evBody2 {} t) :=
  imgRun_sockOk (evBody2_ok B) h

/-- **0.3 HTTP with bodies**: the image of an accepted trace is admitted by the body web. -/
theorem body3Th_netOk (B : BWeb) {t : List WEv} (h : (body3Th B).Accepts t) :
    SockOk (httpNet B.web B.body) (imgRun body3Next evBody3 {} t) :=
  imgRun_sockOk (evBody3_ok B) h

/-! ## Hosts -/

/-- **Every run of the concrete 0.2 outgoing HTTP host has an admitted image.** -/
theorem httpImpl_netOk (W : Web) (body : Val × Val → List (BitVec 8)) {t : List WEv}
    (ht : Follows (httpImpl W) t) :
    SockOk (httpNet W body) (imgRun httpNext evHttp2 HttpSt.init t) :=
  httpTh_netOk W body (gated_follows (httpImpl_ok W)
    (other_ok fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩) ht)

/-- **Every run of the concrete 0.3 outgoing HTTP host has an admitted image.** -/
theorem httpImpl3_netOk (W : Web) (body : Val × Val → List (BitVec 8)) {t : List WEv}
    (ht : Follows (httpImpl3 W) t) : SockOk (httpNet W body) (imgRun http3Next evHttp3 {} t) :=
  httpTh3_netOk W body (gated_follows (httpImpl3_ok W)
    (other_ok fun _ _ _ => ⟨rfl, rfl, fun _ => rfl⟩) ht)

/-- **Every run of the concrete 0.2 HTTP host with bodies has an admitted image.** -/
theorem bodyImpl_netOk (B : BWeb) {t : List WEv} (ht : Follows (bodyImpl B) t) :
    SockOk (httpNet B.web B.body) (imgRun bodyNext evBody2 {} t) :=
  bodyTh_netOk B (gated_follows (bodyImpl_ok B)
    (other_ok fun _ _ _ => ⟨by simp [bodyOk, httpOk, bodyCheck],
      by simp [bodyOk, httpOk, bodyCheck], fun _ => by simp [bodyOk, httpOk, bodyCheck]⟩) ht)

/-- **Every run of the concrete 0.3 HTTP host with bodies has an admitted image.** -/
theorem body3Impl_netOk (B : BWeb) {t : List WEv} (ht : Follows (body3Impl B) t) :
    SockOk (httpNet B.web B.body) (imgRun body3Next evBody3 {} t) :=
  body3Th_netOk B (gated_follows (body3Impl_ok B)
    (other_ok fun _ _ _ => ⟨by simp [body3Ok, http3Ok, body3Check],
      by simp [body3Ok, http3Ok, body3Check], fun _ => by simp [body3Ok, http3Ok, body3Check]⟩) ht)

/-! ## Adapters -/

/-- **Outgoing HTTP 0.3 over 0.2**: over every host of `httpTh W`, the 0.3 events of the
composite have an image admitted by the web. -/
theorem http3Over2_netOk (W : Web) (body : Val × Val → List (BitVec 8)) (rounds : Nat)
    {Y : Sig.{0}} {η : Host Y httpImports} (hη : (hostSat (httpTh W).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody (http3Over2 rounds) ()),
      SockOk (httpNet W body) (imgRun http3Next evHttp3 {} (htrace p)) :=
  fun p hp => httpTh3_netOk W body (http3Over2_model W rounds hη p hp)

/-- **Outgoing HTTP 0.2 over 0.3**: the 0.2 events of the composite have an admitted image. -/
theorem http2Over3_netOk (W : Web) (body : Val × Val → List (BitVec 8)) {Y : Sig.{0}}
    {η : Host Y http3Fns} (hη : (hostSat (httpTh3 W).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody http2Over3 {}),
      SockOk (httpNet W body) (imgRun httpNext evHttp2 HttpSt.init (htrace p)) :=
  fun p hp => httpTh_netOk W body (http2Over3_model W hη p hp)

/-- **HTTP with bodies, 0.3 over 0.2**: the 0.3 events and body chunks of the composite have
an image admitted by the body web. -/
theorem httpB3Over2_netOk (B : BWeb) (rounds : Nat) {Y : Sig.{0}} {η : Host Y httpBodyImports}
    (hη : (hostSat (bodyTh B).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody (httpB3Over2 rounds) {}),
      SockOk (httpNet B.web B.body) (imgRun body3Next evBody3 {} (htrace p)) :=
  fun p hp => body3Th_netOk B (httpB3Over2_model B rounds hη p hp)

/-- **HTTP with bodies, 0.2 over 0.3**: the 0.2 events and body chunks of the composite have
an image admitted by the body web. -/
theorem httpB2Over3_netOk (B : BWeb) (rounds : Nat) {Y : Sig.{0}} {η : Host Y httpBody3Fns}
    (hη : (hostSat (body3Th B).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody (httpB2Over3 rounds) {}),
      SockOk (httpNet B.web B.body) (imgRun bodyNext evBody2 {} (htrace p)) :=
  fun p hp => bodyTh_netOk B (httpB2Over3_model B rounds hη p hp)

/-! ## The extended image -/

/-- **The extended image of a 0.2 HTTP run** accepted by the theory with bodies is admitted by
the network of the body web, and its LPS part is the stdout image. -/
theorem xHttp2_netOk (ch : Silmaril.Process.LPS.Word) (B : BWeb) {t : List WEv}
    (h : (bodyTh B).Accepts t) :
    NetOk (httpNet B.web B.body) (xHttp2 ch t) ∧ lpsPart (xHttp2 ch t) = Silmaril.Wasi.Os.osTrace ch t := by
  refine ⟨fun ev hev => ?_, (lpsPart_xRun _ _ t).trans (runA_osEv ch t)⟩
  have hev' : ev ∈ imgRun bodyNext evBody2 {} t := by
    have hs : sockPart (xHttp2 ch t) = imgRun bodyNext evBody2 {} t := sockPart_xRun _ _ t
    rwa [hs] at hev
  exact bodyTh_netOk B h ev hev'

/-- **The extended image of a 0.3 HTTP run** accepted by the theory with bodies is admitted by
the network of the body web, and its LPS part is the stdout image. -/
theorem xHttp3_netOk (ch : Silmaril.Process.LPS.Word) (B : BWeb) {t : List WEv}
    (h : (body3Th B).Accepts t) :
    NetOk (httpNet B.web B.body) (xHttp3 ch t) ∧ lpsPart (xHttp3 ch t) = P3.osTrace3 ch t := by
  refine ⟨fun ev hev => ?_, (lpsPart_xRun _ _ t).trans (runA_osStep3 ch _ t)⟩
  have hev' : ev ∈ imgRun body3Next evBody3 {} t := by
    have hs : sockPart (xHttp3 ch t) = imgRun body3Next evBody3 {} t := sockPart_xRun _ _ t
    rwa [hs] at hev
  exact body3Th_netOk B h ev hev'

end Silmaril.Wasi.Versions.HttpOs
