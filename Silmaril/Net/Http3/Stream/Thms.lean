module

public import Silmaril.Net.Http3.Stream.Defs
public import Silmaril.Net.Http3.Frame.Thms
import Silmaril.Proofs.Net.Http3.Stream

@[expose] public section

/-!
# HTTP/3 streams: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Http3/Stream.lean`):

Control stream (RFC 9114 §6.2.1, §5.2, §7.2):

* `controlRun_shape`: every control stream the reader accepts starts with SETTINGS, its
  parameters are what the reader keeps, and no later frame is SETTINGS, DATA, HEADERS,
  PUSH_PROMISE or an HTTP/2-reserved type;
* `controlRun_first_not_settings`: a control stream whose first frame is anything else (even an
  unknown or grease frame) fails with `H3_MISSING_SETTINGS`;
* `controlRun_mono`: GOAWAY identifiers never increase and MAX_PUSH_ID never decreases along an
  accepted control stream;
* `controlRun_goaway_server`: every GOAWAY accepted from a server names a request stream;
* `controlRun_filter`: after SETTINGS, unknown (extension, grease) frames do not affect the
  reader (§9).

Critical unidirectional streams (§6.2, RFC 9204 §4.2):

* `openAll_control_le_one`: a peer whose unidirectional streams are all accepted opened at most
  one control stream; `open_unknown`: an unknown stream type is never a connection error.

Request streams (§4.1):

* `reqRun_messageFrames`: the frames of a message (header section, content in any chunking,
  optional trailer section) are accepted and give back that header section, the concatenated
  content and the trailer section; `reqRun_interim` adds interim responses before them;
* `request_sound`: conversely, every request stream the server accepts and that ends cleanly
  is, after removing unknown frames, exactly `messageFrames header chunks trailer` for the
  received parts, with no interim responses and no PUSH_PROMISE;
* `reqRun_filter`: unknown frames anywhere on a request stream are ignored;
* `decodeFrames_encode`, `request_bytes`: from bytes, through `readRawAll`/`Frame.ofRaw`, to
  the received message parts.

CHECKED (`rfl`): control-stream examples (missing SETTINGS, duplicate SETTINGS, DATA on the
control stream, increasing GOAWAY, a server GOAWAY naming a non-request stream, MAX_PUSH_ID
from a server), request streams with DATA first, HEADERS after trailers, PUSH_PROMISE sent by
a client, and an empty request stream (`H3_REQUEST_INCOMPLETE`).
-/

namespace Silmaril.Net.Http3

theorem controlRun_shape {peer : Role} {fs : List Frame} {s : ControlState}
    (h : controlRun peer {} fs = .ok s) (hne : fs ≠ []) :
    ∃ ps rest, fs = .settings ps :: rest ∧ s.settings = some ps ∧
      ∀ f ∈ rest, forbiddenAfterSettings f = false :=
  Silmaril.Proofs.Net.Http3.Stream.controlRun_shape h hne

theorem controlRun_first_not_settings {peer : Role} {f : Frame} (fs : List Frame)
    (hf : ∀ ps, f ≠ .settings ps) : controlRun peer {} (f :: fs) = .error .missingSettings := by
  cases f <;> first | exact absurd rfl (hf _) | rfl

theorem controlRun_mono {peer : Role} {fs : List Frame} {s s' : ControlState}
    (h : controlRun peer s fs = .ok s') :
    NoIncrease s.lastGoaway s'.lastGoaway ∧ NoDecrease s.maxPushId s'.maxPushId :=
  Silmaril.Proofs.Net.Http3.Stream.controlRun_mono fs s s' h

theorem controlRun_goaway_server {fs : List Frame} {s s' : ControlState}
    (h : controlRun .server s fs = .ok s') {i : Nat} (hi : Frame.goaway i ∈ fs) :
    isRequestStream i = true :=
  Silmaril.Proofs.Net.Http3.Stream.controlRun_goaway_server fs s s' h i hi

theorem controlRun_filter {peer : Role} (fs : List Frame) (s : ControlState)
    (hs : s.settings.isSome) :
    controlRun peer s fs = controlRun peer s (fs.filter fun f => !f.isUnknown) :=
  Silmaril.Proofs.Net.Http3.Stream.controlRun_filter fs s hs

theorem open_unknown (peer : Role) (u : UniStreams) (t : Nat) :
    u.open_ peer (.unknown t) = .ok u := rfl

theorem openAll_control_le_one {peer : Role} {ks : List UniKind} {u : UniStreams}
    (h : ({} : UniStreams).openAll peer ks = .ok u) : ks.countP (· == .control) ≤ 1 := by
  have := (Silmaril.Proofs.Net.Http3.Stream.openAll_control_le_one ks {} u h).1
  simpa [Silmaril.Proofs.Net.Http3.Stream.countControl] using this

theorem reqRun_filter (k : StreamKind) (interim : List UInt8 → Bool) (fs : List Frame)
    (s : ReqState) :
    reqRun k interim s fs = reqRun k interim s (fs.filter fun f => !f.isUnknown) :=
  Silmaril.Proofs.Net.Http3.Stream.reqRun_filter k interim fs s

theorem reqRun_messageFrames (k : StreamKind) (interim : List UInt8 → Bool) (p : Parts)
    (hp : p.header = [] ∧ p.content = [] ∧ p.trailer = none)
    (h : List UInt8) (hh : k = .request ∨ interim h = false)
    (chunks : List (List UInt8)) (t : Option (List UInt8)) :
    reqRun k interim { phase := .awaitHeaders, parts := p } (messageFrames h chunks t) =
      .ok { phase := if t.isSome then .done else .body,
            parts := { p with header := h, content := chunks.flatten, trailer := t } } :=
  Silmaril.Proofs.Net.Http3.Stream.reqRun_messageFrames k interim p hp h hh chunks t

theorem reqRun_interim (interim : List UInt8 → Bool) (k : StreamKind) (hk : k ≠ .request)
    (is : List (List UInt8)) (p : Parts) (hi : ∀ i ∈ is, interim i = true) :
    reqRun k interim { phase := .awaitHeaders, parts := p } (is.map .headers) =
      .ok { phase := .awaitHeaders, parts := { p with interim := p.interim ++ is } } :=
  Silmaril.Proofs.Net.Http3.Stream.reqRun_interim interim k hk is p hi

theorem request_sound {interim : List UInt8 → Bool} {fs : List Frame} {s : ReqState} {p : Parts}
    (h : reqRun .request interim {} fs = .ok s) (hf : reqFinish .request s = .ok p) :
    ∃ chunks, fs.filter (fun f => !f.isUnknown) = messageFrames p.header chunks p.trailer ∧
      chunks.flatten = p.content ∧ p.interim = [] ∧ p.promises = [] :=
  Silmaril.Proofs.Net.Http3.Stream.request_sound h hf

theorem decodeFrames_encode {maxPayload : Nat} (fs : List Frame)
    (hv : ∀ f ∈ fs, f.Valid ∧ f.toRaw.payload.length ≤ maxPayload) :
    decodeFrames maxPayload (fs.flatMap Frame.encode) = .ok fs :=
  Silmaril.Proofs.Net.Http3.Stream.decodeFrames_encode fs hv

/-- From the bytes of a request stream to the received message: header section, content (in
any chunking) and trailer section. -/
theorem request_bytes {maxPayload : Nat} (interim : List UInt8 → Bool) (h : List UInt8)
    (chunks : List (List UInt8)) (t : Option (List UInt8))
    (hv : ∀ f ∈ messageFrames h chunks t, f.Valid ∧ f.toRaw.payload.length ≤ maxPayload) :
    ∃ fs, decodeFrames maxPayload ((messageFrames h chunks t).flatMap Frame.encode) = .ok fs ∧
      reqRun .request interim {} fs =
        .ok { phase := if t.isSome then .done else .body,
              parts := { header := h, content := chunks.flatten, trailer := t } } :=
  ⟨_, decodeFrames_encode _ hv,
    reqRun_messageFrames .request interim {} ⟨rfl, rfl, rfl⟩ h (.inl rfl) chunks t⟩

/-! ## Known answers -/

theorem control_missing_settings :
    controlRun .client {} [.goaway 0] = .error .missingSettings := by rfl

theorem control_grease_first :
    controlRun .client {} [.unknown 0x21 [], .settings []] = .error .missingSettings := by rfl

theorem control_second_settings :
    controlRun .client {} [.settings [], .unknown 0x21 [], .settings []] =
      .error .frameUnexpected := by rfl

theorem control_data : controlRun .client {} [.settings [], .data []] = .error .frameUnexpected := by
  rfl

theorem control_goaway_increase :
    controlRun .server {} [.settings [], .goaway 8, .goaway 12] = .error .idError := by rfl

theorem control_goaway_decrease :
    controlRun .server {} [.settings [], .goaway 12, .goaway 8] =
      .ok { settings := some [], lastGoaway := some 8 } := by rfl

theorem control_goaway_not_request :
    controlRun .server {} [.settings [], .goaway 2] = .error .idError := by rfl

theorem control_maxPushId_from_server :
    controlRun .server {} [.settings [], .maxPushId 3] = .error .frameUnexpected := by rfl

theorem control_maxPushId_decrease :
    controlRun .client {} [.settings [], .maxPushId 3, .maxPushId 2] = .error .idError := by rfl

theorem uni_second_control :
    ({} : UniStreams).openAll .client [.control, .qpackEncoder, .control] =
      .error .streamCreationError := by rfl

theorem uni_push_from_client :
    ({} : UniStreams).openAll .client [.push 0] = .error .streamCreationError := by rfl

theorem uni_push_reused :
    ({} : UniStreams).openAll .server [.push 0, .push 0] = .error .idError := by rfl

theorem uni_header_push : readUniHeader [0x01, 0x05, 0xaa] = some (.push 5, [0xaa]) := by rfl

theorem uni_header_webtransport : readUniHeader [0x40, 0x54, 0x00] = some (.unknown 0x54, [0x00]) := by
  rfl

theorem request_data_first :
    reqRun .request (fun _ => false) {} [.data [1]] = .error .frameUnexpected := by rfl

theorem request_headers_after_trailers :
    reqRun .request (fun _ => false) {} [.headers [], .headers [], .headers []] =
      .error .frameUnexpected := by rfl

theorem request_push_promise :
    reqRun .request (fun _ => false) {} [.headers [], .pushPromise 0 []] =
      .error .frameUnexpected := by rfl

theorem request_empty : reqFinish .request {} = .error .requestIncomplete := by rfl

theorem bidi_from_server : acceptBidi .client 1 = .error .streamCreationError := by rfl

end Silmaril.Net.Http3
