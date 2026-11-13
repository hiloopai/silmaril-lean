module

public import Silmaril.Wasi.Versions.HttpOsTr.Defs
public import Silmaril.Wasi.Versions.HttpOs.Thms

@[expose] public section

/-!
# The OS image of WASI HTTP with trailers: theorems

PROVED (standard axioms):

* `sockOk_T`: what `httpNet B.web B.body` admits, `httpNetT B` admits.
* `trEv2_ok`, `trEv3_ok`: the trailer event of a checked answer is admitted.
* **`bodyTh_netOkT`**, **`body3Th_netOkT`**: the image with trailers of a trace accepted by the
  theory with bodies is admitted by `httpNetT B`.
* **Hosts and adapters** (`bodyImpl_netOkT`, `body3Impl_netOkT`, `httpB3Over2_netOkT`,
  `httpB2Over3_netOkT`): the same for every run of the concrete hosts and for the exported
  events of the two body adapters over every host of the imported theory.
-/

namespace Silmaril.Wasi.Versions.HttpOs

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasi.Versions.Net
open Silmaril.Wasi.Versions.SockOs
open Silmaril.Wasm.Component (Val)
open Silmaril.Machine.Process.IoSpecNet

/-- An event the network without trailers admits is admitted with trailers. -/
theorem admits_T {B : BWeb} {e : SockEv Val} (h : e.Admits (httpNet B.web B.body)) :
    e.Admits (httpNetT B) := by
  cases e with
  | recv loc d =>
    have h' : inboxOf B.web B.body loc d = true := h
    show inboxT B loc d = true
    unfold inboxT
    split
    · simp [h']
    · next hn =>
      unfold inboxOf at h'
      split at h'
      · next a p => exact absurd rfl (hn a p)
      · exact absurd h' (by simp)
  | _ => exact h

/-- **What the network without trailers admits, the network with trailers admits.** -/
theorem sockOk_T {B : BWeb} {l : List (SockEv Val)} (h : SockOk (httpNet B.web B.body) l) :
    SockOk (httpNetT B) l := fun e he => admits_T (h e he)

/-- A checked trailers answer is admitted. -/
theorem trail_admits {B : BWeb} {k : Val × Val} {x : Val} (h : entriesOk (B.trailers k) (some [x]) = true) :
    (SockEv.recv (keyV k) x : SockEv Val).Admits (httpNetT B) := by
  have ht : trailIn B k x = true := by
    unfold trailIn
    cases hk : B.trailers k with
    | none => rfl
    | some l => simpa [entriesOk, hk] using h
  show inboxT B (.record [k.1, k.2]) x = true
  simp [inboxT, ht]

/-- `entries` is not a read. -/
theorem isReadFn_entries2 : isReadFn entries2 = false := by decide

/-- **The trailer event of a checked 0.2 answer is admitted.** -/
theorem trEv2_ok (B : BWeb) (q : BodySt) (e : WEv) (h : bodyCheck B q e = true) :
    SockOk (httpNetT B) (trEv2 q e) := by
  unfold trEv2
  split
  · next f hd rest x =>
    split
    · next hf =>
      split
      · next k hl =>
        have hne : entries2 ≠ trGet2 := by decide
        have hc : entriesOk (B.trailers k) (some [x]) = true := by
          simpa [bodyCheck, hf, hl, isReadFn_entries2, hne] using h
        exact sockOk_single (trail_admits hc)
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- `copy-all` is not a 0.3 read. -/
theorem copyAll3_ne_read : copyAll3 ≠ P3.cStreamRead := by decide

/-- `copy-all` is not a 0.3 future read. -/
theorem copyAll3_ne_fread : copyAll3 ≠ P3.cFutureRead := by decide

/-- **The trailer event of a checked 0.3 answer is admitted.** -/
theorem trEv3_ok (B : BWeb) (q : Body3St) (e : WEv) (h : body3Check B q e = true) :
    SockOk (httpNetT B) (trEv3 q e) := by
  unfold trEv3
  split
  · next f hd rest x =>
    split
    · next hf =>
      split
      · next k hl =>
        have hc : entriesOk (B.trailers k) (some [x]) = true := by
          subst hf
          unfold body3Check at h
          simpa [hl, copyAll3_ne_read, copyAll3_ne_fread] using h
        exact sockOk_single (trail_admits hc)
      · exact sockOk_nil
    · exact sockOk_nil
  · exact sockOk_nil

/-- **The image with trailers of a checked 0.2 answer is admitted.** -/
theorem evBodyT2_ok (B : BWeb) (q : BodySt) (e : WEv) (h : bodyOk B q e = true) :
    SockOk (httpNetT B) (evBodyT2 q e) := by
  have h' : httpOk B.web q.base e = true ∧ bodyCheck B q e = true := by
    simpa only [bodyOk, Bool.and_eq_true] using h
  exact sockOk_append (sockOk_T (evBody2_ok B q e h)) (trEv2_ok B q e h'.2)

/-- **The image with trailers of a checked 0.3 answer is admitted.** -/
theorem evBodyT3_ok (B : BWeb) (q : Body3St) (e : WEv) (h : body3Ok B q e = true) :
    SockOk (httpNetT B) (evBodyT3 q e) := by
  have h' : http3Ok B.web q.base e = true ∧ body3Check B q e = true := by
    simpa only [body3Ok, Bool.and_eq_true] using h
  exact sockOk_append (sockOk_T (evBody3_ok B q e h)) (trEv3_ok B q e h'.2)

/-- **0.2 HTTP with bodies and trailers**: the image of an accepted trace is admitted. -/
theorem bodyTh_netOkT (B : BWeb) {t : List WEv} (h : (bodyTh B).Accepts t) :
    SockOk (httpNetT B) (imgRun bodyNext evBodyT2 {} t) :=
  imgRun_sockOk (evBodyT2_ok B) h

/-- **0.3 HTTP with bodies and trailers**: the image of an accepted trace is admitted. -/
theorem body3Th_netOkT (B : BWeb) {t : List WEv} (h : (body3Th B).Accepts t) :
    SockOk (httpNetT B) (imgRun body3Next evBodyT3 {} t) :=
  imgRun_sockOk (evBodyT3_ok B) h

/-- **Every run of the concrete 0.2 host with bodies has an admitted image with trailers.** -/
theorem bodyImpl_netOkT (B : BWeb) {t : List WEv} (ht : Follows (bodyImpl B) t) :
    SockOk (httpNetT B) (imgRun bodyNext evBodyT2 {} t) :=
  bodyTh_netOkT B (gated_follows (bodyImpl_ok B)
    (other_ok fun _ _ _ => ⟨by simp [bodyOk, httpOk, bodyCheck],
      by simp [bodyOk, httpOk, bodyCheck], fun _ => by simp [bodyOk, httpOk, bodyCheck]⟩) ht)

/-- **Every run of the concrete 0.3 host with bodies has an admitted image with trailers.** -/
theorem body3Impl_netOkT (B : BWeb) {t : List WEv} (ht : Follows (body3Impl B) t) :
    SockOk (httpNetT B) (imgRun body3Next evBodyT3 {} t) :=
  body3Th_netOkT B (gated_follows (body3Impl_ok B)
    (other_ok fun _ _ _ => ⟨by simp [body3Ok, http3Ok, body3Check],
      by simp [body3Ok, http3Ok, body3Check], fun _ => by simp [body3Ok, http3Ok, body3Check]⟩) ht)

/-- **HTTP with bodies, 0.3 over 0.2**: the 0.3 events, body chunks and trailers of the
composite have an image admitted by the body web. -/
theorem httpB3Over2_netOkT (B : BWeb) (rounds : Nat) {Y : Sig.{0}} {η : Host Y httpBodyImports}
    (hη : (hostSat (bodyTh B).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody (httpB3Over2 rounds) {}),
      SockOk (httpNetT B) (imgRun body3Next evBodyT3 {} (htrace p)) :=
  fun p hp => body3Th_netOkT B (httpB3Over2_model B rounds hη p hp)

/-- **HTTP with bodies, 0.2 over 0.3**: the 0.2 events, body chunks and trailers of the
composite have an image admitted by the body web. -/
theorem httpB2Over3_netOkT (B : BWeb) (rounds : Nat) {Y : Sig.{0}} {η : Host Y httpBody3Fns}
    (hη : (hostSat (body3Th B).Accepts).holds η) :
    ∀ p ∈ link η (ofSBody (httpB2Over3 rounds) {}),
      SockOk (httpNetT B) (imgRun bodyNext evBodyT2 {} (htrace p)) :=
  fun p hp => bodyTh_netOkT B (httpB2Over3_model B rounds hη p hp)

end Silmaril.Wasi.Versions.HttpOs
