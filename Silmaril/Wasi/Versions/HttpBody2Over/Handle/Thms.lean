module

public import Silmaril.Wasi.Versions.HttpBody2Over.Steps.Thms

@[expose] public section

/-!
# HTTP with bodies, 0.2 over 0.3: the program of `handle`

PROVED (standard axioms): **`wp_handleB`**: under every answer sequence the 0.3 theory with
bodies `body3Th B` accepts, the program of `handle` (`send`, `get-status-code`,
`consume-body`, `stream.read` to the end, `future.read` and `copy-all`) returns an answer that
the 0.2 theory with bodies `bodyTh B` accepts for `handle`, and keeps `JB2`. The body read to
`DROPPED` is the body of the web (`wp_readAll3`); the polled trailer outcome matches the web
(`wp_pollFut3`).
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)

/-- A trap of `handle` keeps `JB2`. -/
theorem handleB_trap (B : BWeb) {st : B2St} {q3 q3' : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (ha : q3'.base.auth = q3.base.auth) (hp : q3'.base.path = q3.base.path) (a : List Val) :
    PostH B q2 a (st, none) q3' :=
  ⟨q2, bodyTh_of_httpTh (q := q2) (by decide)
    (step2_quiet (httpOk_ne B.web q2.base (by decide) (by decide) a none) (httpNext_none _ _ _)),
    jb2_keys hJ ha hp⟩

/-- **Storing a result** that matches the body web keeps `JB2`. -/
theorem handleB_store (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (r : BitVec 32) (rest : List Val) (x : Val × RInfo) (hx : PendB B (q3.base.key r) x) :
    PostH B q2 (.u32 r :: rest) (storeFutB st x) q3 := by
  obtain ⟨ha, hp, hpend, hresp, hbod, hstr, hftr, htrs⟩ := hJ
  have hk : q2.base.key r = q3.base.key r := key_eq ha hp r
  have hs : (httpTh B.web).step q2.base
      (.imp httpHandle (.u32 r :: rest) (some [okV (some (.u32 st.fresh))])) =
      some { q2.base with futs := (st.fresh, q2.base.key r) :: q2.base.futs } := by
    rw [← httpNext_handleOk]
    exact gated_step_of (httpOk_ne B.web q2.base (by decide) (by decide) _ _)
  refine ⟨_, bodyTh_of_httpTh (by decide) hs, ha, hp, fun fu y hy => ?_, hresp, hbod, hstr, hftr, htrs⟩
  by_cases hf : fu = st.fresh
  · subst hf
    simp only [storeFutB, lookup_cons_self, Option.some.injEq] at hy
    exact ⟨q2.base.key r, lookup_cons_self _ _ _, hk ▸ hy ▸ hx⟩
  · simp only [storeFutB] at hy ⊢
    rw [lookup_cons_ne hf] at hy ⊢
    exact hpend fu y hy

/-- **Polling the trailer future** gives the continuation an outcome that matches the web. -/
theorem wp_pollFut3 (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) (fu : BitVec 32) (k : Val × Val) (hk : ∃ x, B k.1 k.2 = .resp x) (b0 : Http3St)
    (hb0a : b0.auth = q3.base.auth) (hb0p : b0.path = q3.base.path) (kont : TrInfo → BProg2)
    (hkont : ∀ i qx, qx.base = b0 → InfoOk B k i → Wp (body3Th B) (kont i) (PostH B q2 a) qx) :
    ∀ n qa, qa.base = b0 → lookup fu qa.futs = some (some k) →
      Wp (body3Th B) (pollFut3 st fu kont n) (PostH B q2 a) qa
  | 0, qa, hb, _ => handleB_trap B hJ (by rw [hb, hb0a]) (by rw [hb, hb0p]) a
  | n + 1, qa, hb, hl => fun r qb hs => by
    obtain ⟨hc, hq⟩ := body3Th_body_inv (f := P3.cFutureRead) (by decide) hs
    change body3Check B qa (.imp P3.cFutureRead [.u32 fu] r) = true at hc
    change qb = body3Step qa (.imp P3.cFutureRead [.u32 fu] r) at hq
    obtain ⟨x, hx⟩ := hk
    have hf : fut3Ok (B.trailers k) r = true := by
      simpa [body3Check, hl, hx, show P3.cFutureRead ≠ P3.cStreamRead by decide] using hc
    have hbb : qb.base = b0 := by rw [hq, body3Step_base, hb]
    have htrap : Wp (body3Th B) (trapB st) (PostH B q2 a) qb :=
      handleB_trap B hJ (by rw [hbb, hb0a]) (by rw [hbb, hb0p]) a
    rw [body3Step_fut] at hq
    beta_reduce
    split
    · have hq' : qb = qa := by rw [hq]; rfl
      exact wp_pollFut3 B hJ a fu k ⟨x, hx⟩ b0 hb0a hb0p kont hkont n qb hbb (hq' ▸ hl)
    · exact hkont .noTr qb hbb (Option.isNone_iff_eq_none.1 (by simpa [fut3Ok] using hf))
    · next t =>
      have hqb : qb = { qa with trs := (t, some k) :: qa.trs } := by
        rw [hq]; simp [trHandle3, hl]
      intro r₂ qc hs₂
      obtain ⟨hc₂, hq₂⟩ := body3Th_body_inv (f := copyAll3) (by decide) hs₂
      change body3Check B qb (.imp copyAll3 [.u32 t] r₂) = true at hc₂
      change qc = body3Step qb (.imp copyAll3 [.u32 t] r₂) at hq₂
      have hent : entriesOk (B.trailers k) r₂ = true := by
        rw [hqb] at hc₂
        simpa [body3Check, lookup_cons_self, show copyAll3 ≠ P3.cStreamRead by decide,
          show copyAll3 ≠ P3.cFutureRead by decide] using hc₂
      have hqc : qc = qb := by rw [hq₂, body3Step_copy]
      exact hkont (.tr r₂) qc (by rw [hqc]; exact hbb)
        ⟨by simpa [fut3Ok] using hf, hent⟩
    · next c p => exact hkont (.err _) qb hbb ⟨c, p, rfl⟩
    · exact htrap

/-- A `stream.read` answer that completes nothing. -/
theorem completed3_none {pv : BitVec 32} {vs : List Val}
    (h : ∀ c, copy3 pv ≠ some (some (.completed, c))) : completed3 (some [.u32 pv, .record vs]) = none := by
  rcases hc : copy3 pv with _ | _ | ⟨cr, c⟩
  · simp [completed3, hc]
  · simp [completed3, hc]
  · cases cr
    · exact absurd hc (h c)
    all_goals simp [completed3, hc]

/-- **Reading the body to `DROPPED`** gives the continuation the body bytes. -/
theorem wp_readAll3 (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) (rd fu : BitVec 32) (k : Val × Val) (b0 : Http3St)
    (hb0a : b0.auth = q3.base.auth) (hb0p : b0.path = q3.base.path)
    (kont : List (BitVec 8) → BProg2)
    (hkont : ∀ bytes qx, qx.base = b0 → lookup fu qx.futs = some (some k) → bytes = B.body k →
      Wp (body3Th B) (kont bytes) (PostH B q2 a) qx) :
    ∀ n acc qa, qa.base = b0 → lookup fu qa.futs = some (some k) →
      (∃ m, lookup rd qa.streams = some (some (k, m)) ∧ acc = (B.body k).take m) →
      Wp (body3Th B) (readAll3 st rd kont n acc) (PostH B q2 a) qa
  | 0, _, qa, hb, _, _ => handleB_trap B hJ (by rw [hb, hb0a]) (by rw [hb, hb0p]) a
  | n + 1, acc, qa, hb, hf, ⟨m, hl, hacc⟩ => fun r qb hs => by
    obtain ⟨hc, hq⟩ := body3Th_body_inv (f := P3.cStreamRead) (by decide) hs
    change body3Check B qa (.imp P3.cStreamRead [.u32 rd, P3.natV readLen3] r) = true at hc
    change qb = body3Step qa (.imp P3.cStreamRead [.u32 rd, P3.natV readLen3] r) at hq
    have hrd : read3Ok ((B.body k).drop m) (count3 [.u32 rd, P3.natV readLen3]) r = true := by
      simpa [body3Check, hl] using hc
    have hbb : qb.base = b0 := by rw [hq, body3Step_base, hb]
    have hfb : lookup fu qb.futs = some (some k) := by rw [hq, body3Step_streams_futs]; exact hf
    have htrap : Wp (body3Th B) (trapB st) (PostH B q2 a) qb :=
      handleB_trap B hJ (by rw [hbb, hb0a]) (by rw [hbb, hb0p]) a
    rw [body3Step_read_tracked qa rd [P3.natV readLen3] hl r] at hq
    beta_reduce
    split
    · next pv vs =>
      split
      · next hcp =>
        have hq' : qb = qa := by
          rw [hq, completed3_none (fun c h => by rw [hcp] at h; cases h)]
        exact wp_readAll3 B hJ a rd fu k b0 hb0a hb0p kont hkont n acc qb hbb hfb
          ⟨m, hq' ▸ hl, hacc⟩
      · next c hcp =>
        split
        · next bs hbs =>
          have h1 : c ≤ count3 [.u32 rd, P3.natV readLen3] ∧ bs = ((B.body k).drop m).take c ∧
              bs.length = c := by
            simpa [read3Ok, hcp, hbs] using hrd
          have hcomp : completed3 (some [.u32 pv, .record vs]) = some c := by
            simp [completed3, hcp]
          rw [hcomp] at hq
          refine wp_readAll3 B hJ a rd fu k b0 hb0a hb0p kont hkont n (acc ++ bs) qb hbb hfb
            ⟨m + c, by rw [hq]; exact lookup_cons_self _ _ _, ?_⟩
          rw [hacc, h1.2.1, List.take_add]
        · exact htrap
      · next hcp =>
        have he : ((B.body k).drop m).isEmpty = true := by simpa [read3Ok, hcp] using hrd
        have hq' : qb = qa := by
          rw [hq, completed3_none (fun c h => by rw [hcp] at h; cases h)]
        refine hkont acc qb hbb hfb ?_
        rw [hacc, List.take_of_length_le (List.drop_eq_nil_iff.1 (List.isEmpty_iff.1 he))]
      · exact htrap
    · exact htrap

/-- After `consume-body` handed out the stream `rd` and the future `fu` of the response of
key `q3.base.key r`: the body, the trailers and the stored answer. -/
theorem wp_bodyKont (B : BWeb) (rounds : Nat) {st : B2St} {q3 : Body3St} {q2 : BodySt}
    (hJ : JB2 B st q3 q2) (r : BitVec 32) (rest : List Val) (rs : BitVec 32) (s : BitVec 16)
    (hW : B.web (q3.base.key r).1 (q3.base.key r).2 = .status s) (b0 : Http3St)
    (hba : b0.auth = q3.base.auth) (hbp : b0.path = q3.base.path) (rd fu : BitVec 32) (qb : Body3St)
    (hbb : qb.base = b0) (hrd : lookup rd qb.streams = some (some (q3.base.key r, 0)))
    (hfu : lookup fu qb.futs = some (some (q3.base.key r))) :
    Wp (body3Th B) (readAll3 st rd (fun bytes => pollFut3 st fu
        (fun i => .pure (storeFutB st (okV (some (.u32 rs)), s, bytes, i))) rounds) rounds [])
      (PostH B q2 (.u32 r :: rest)) qb := by
  refine wp_readAll3 B hJ _ rd fu (q3.base.key r) b0 hba hbp _ ?_ rounds [] qb hbb hfu ⟨0, hrd, by simp⟩
  intro bytes qx hbx hfx hby
  refine wp_pollFut3 B hJ _ fu (q3.base.key r) (bweb_resp hW) b0 hba hbp _ ?_ rounds qx hbx hfx
  intro i qy hby' hi
  have hJy : JB2 B st qy q2 := jb2_keys hJ (by rw [hby', hba]) (by rw [hby', hbp])
  have hkey : qy.base.key r = q3.base.key r := by simp [Http3St.key, hby', hba, hbp]
  refine handleB_store B hJy r rest _ ?_
  rw [hkey]
  exact ⟨by simp [outcomeOk, hW, okV], fun _ _ => ⟨hW, hby, hi⟩⟩

/-- **After `get-status-code(rs)` answered `s`**: `consume-body`, the body, the trailers and
the stored answer. -/
theorem wp_bodyOfProg (B : BWeb) (rounds : Nat) {st : B2St} {q3 : Body3St} {q2 : BodySt}
    (hJ : JB2 B st q3 q2) (r : BitVec 32) (rest : List Val) (rs : BitVec 32) (s : BitVec 16)
    (hW : B.web (q3.base.key r).1 (q3.base.key r).2 = .status s) (qa : Body3St)
    (hba : qa.base.auth = q3.base.auth) (hbp : qa.base.path = q3.base.path)
    (hlr : lookup rs qa.base.resps = some (q3.base.key r)) :
    Wp (body3Th B) (bodyOfProg rounds st rs s) (PostH B q2 (.u32 r :: rest)) qa := by
  intro r₃ qb hs
  have hq : qb = body3Step qa (.imp consumeBody3 [.u32 rs, .u32 0] r₃) :=
    (body3Th_body_inv (f := consumeBody3) (by decide) hs).2
  have hbb : qb.base = qa.base := by rw [hq, body3Step_base]
  beta_reduce
  split
  · next rd fu =>
    have hrd : lookup rd qb.streams = some (some (q3.base.key r, 0)) := by
      rw [hq]; simp [body3Step, hlr, lookup_cons_self]
    have hfu : lookup fu qb.futs = some (some (q3.base.key r)) := by
      rw [hq]; simp [body3Step, hlr, lookup_cons_self]
    exact wp_bodyKont B rounds hJ r rest rs s hW qa.base hba hbp rd fu qb hbb hrd hfu
  · exact handleB_trap B hJ (by rw [hbb, hba]) (by rw [hbb, hbp]) _

/-- **After `send` answered `ok(rs)`**: the status, then the body. -/
theorem wp_afterSendB (B : BWeb) (rounds : Nat) {st : B2St} {q3 : Body3St} {q2 : BodySt}
    (hJ : JB2 B st q3 q2) (r : BitVec 32) (rest : List Val) (rs : BitVec 32) {s₀ : BitVec 16}
    (hW : B.web (q3.base.key r).1 (q3.base.key r).2 = .status s₀) (qa : Body3St)
    (hba : qa.base.auth = q3.base.auth) (hbp : qa.base.path = q3.base.path)
    (hlr : lookup rs qa.base.resps = some (q3.base.key r)) :
    Wp (body3Th B) (afterSendB rounds st rs) (PostH B q2 (.u32 r :: rest)) qa := by
  intro r₂ qb hs
  obtain ⟨hok, hq⟩ := body3Th_http_inv (f := getStatus3) (by decide) hs
  change http3Ok B.web qa.base (.imp getStatus3 [.u32 rs] r₂) = true at hok
  change qb = { qa with base := http3Next qa.base (.imp getStatus3 [.u32 rs] r₂) } at hq
  rw [http3Next_status] at hq
  have hbb : qb.base = qa.base := by rw [hq]
  beta_reduce
  split
  · next s =>
    have hs : s = s₀ := by
      simpa [http3Ok, hlr, statusOk, hW, getStatus3, send3] using hok
    subst hs
    exact wp_bodyOfProg B rounds hJ r rest rs s hW qb (by rw [hbb, hba]) (by rw [hbb, hbp])
      (by rw [hbb, hlr])
  · exact handleB_trap B hJ (by rw [hbb, hba]) (by rw [hbb, hbp]) _

/-- **The program of `handle(r, _)`** answers as the 0.2 theory with bodies allows, keeping
`JB2`. -/
theorem wp_sendProgB (B : BWeb) (rounds : Nat) {st : B2St} {q3 : Body3St} {q2 : BodySt}
    (hJ : JB2 B st q3 q2) (r : BitVec 32) (rest : List Val) :
    Wp (body3Th B) (sendProgB rounds st r) (PostH B q2 (.u32 r :: rest)) q3 := by
  intro r₁ q3₁ hs
  have hok : http3Ok B.web q3.base (.imp send3 [.u32 r] r₁) = true :=
    (body3Th_http_inv (f := send3) (by decide) hs).1
  have hq : q3₁ = { q3 with base := http3Next q3.base (.imp send3 [.u32 r] r₁) } :=
    (body3Th_http_inv (f := send3) (by decide) hs).2
  have hkeys := http3Next_keys q3.base (f := send3) (by decide) (by decide) [.u32 r] r₁
  have ha : q3₁.base.auth = q3.base.auth := by rw [hq]; exact hkeys.1
  have hp : q3₁.base.path = q3.base.path := by rw [hq]; exact hkeys.2
  beta_reduce
  split
  · next rs =>
    have hs' : sendOk (B.web (q3.base.key r).1 (q3.base.key r).2)
        (some [.variant 0 (some (.u32 rs))]) = true := by simpa [http3Ok] using hok
    have hlr : lookup rs q3₁.base.resps = some (q3.base.key r) := by
      rw [hq]; simp [http3Next, lookup_cons_self]
    exact wp_afterSendB B rounds hJ r rest rs (sendOk_okStatus hs').choose_spec q3₁ ha hp hlr
  · next c p =>
    have hs' : sendOk (B.web (q3.base.key r).1 (q3.base.key r).2)
        (some [.variant 1 (some (.variant c p))]) = true := by simpa [http3Ok] using hok
    have hW : B.web (q3.base.key r).1 (q3.base.key r).2 = .error c := sendOk_err hs'
    have hkey : q3₁.base.key r = q3.base.key r := by simp [Http3St.key, ha, hp]
    refine handleB_store B (jb2_keys hJ ha hp) r rest _ ?_
    rw [hkey]
    exact ⟨by simp [outcomeOk, hW, errV], fun _ h => by simp [errV] at h⟩
  · exact handleB_trap B hJ ha hp _

/-- **The program of `handle`** answers as the 0.2 theory with bodies allows, keeping `JB2`. -/
theorem wp_handleB (B : BWeb) (rounds : Nat) {st : B2St} {q3 : Body3St} {q2 : BodySt}
    (hJ : JB2 B st q3 q2) (a : List Val) :
    Wp (body3Th B) (handleProgB rounds st a) (PostH B q2 a) q3 := by
  unfold handleProgB
  split
  · next r rest => exact wp_sendProgB B rounds hJ r rest
  · exact handleB_trap B hJ rfl rfl a

end Silmaril.Wasi.Versions.Net
