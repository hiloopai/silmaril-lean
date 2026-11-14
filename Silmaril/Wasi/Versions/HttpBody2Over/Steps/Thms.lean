module

public import Silmaril.Wasi.Versions.HttpBody2Over.Defs
public import Silmaril.Wasi.Versions.HttpBodyOver.Thms

@[expose] public section

/-!
# HTTP with bodies, 0.2 over 0.3: the steps without import calls

PROVED (standard axioms): the steps of the theories that `httpB2Over3` relies on, and that
every export call of `httpB2Over3` that makes no import call (`get`, `status` and the 0.2 body
functions, answered from the buffers) keeps the invariant `JB2` and answers as the 0.2 theory
with bodies `bodyTh B` allows (`getResB_step`, `statusResB_step`, `bodyRes2_step`).
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)

/-! ## Theory steps -/

/-- A step of the outgoing 0.2 theory on an outgoing function is a step of the 0.2 theory with
bodies, framing the body part. -/
theorem bodyTh_of_httpTh {B : BWeb} {q : BodySt} {b : HttpSt} {f : FnName}
    (hb : isBodyFn f = false) {a : List Val} {r : Option (List Val)}
    (h : (httpTh B.web).step q.base (.imp f a r) = some b) :
    (bodyTh B).step q (.imp f a r) = some { q with base := b } := by
  obtain ⟨hok, hq⟩ := gated_step_iff.1 h
  subst hq
  refine gated_step_iff.2 ⟨?_, ?_⟩
  · simp [bodyOk, hok, bodyCheck_other B q hb]
  · simp [bodyNext, bodyStep_other q hb]

/-- A checked step of the 0.2 theory with bodies on a body function. -/
theorem bodyTh_step_of {B : BWeb} {q : BodySt} {f : FnName} (hb : isBodyFn f = true)
    {a : List Val} {r : Option (List Val)} (hc : bodyCheck B q (.imp f a r) = true) :
    (bodyTh B).step q (.imp f a r) = some (bodyStep q (.imp f a r)) := by
  obtain ⟨h₁, h₂⟩ := bodyFn_ne hb
  refine gated_step_iff.2 ⟨by simp [bodyOk, httpOk_other B.web _ h₁ h₂, hc], ?_⟩
  rw [bodyNext, httpNext_body _ hb, ← bodyStep_base q]

/-- A step of the 0.3 theory with bodies on an outgoing function. -/
theorem body3Th_http_inv {B : BWeb} {q q' : Body3St} {f : FnName} (hb : isBodyFn3 f = false)
    {a : List Val} {r : Option (List Val)} (h : (body3Th B).step q (.imp f a r) = some q') :
    http3Ok B.web q.base (.imp f a r) = true ∧ q' = { q with base := http3Next q.base (.imp f a r) } := by
  obtain ⟨hok, hq⟩ := gated_step_iff.1 h
  refine ⟨by simp only [body3Ok, Bool.and_eq_true] at hok; exact hok.1, ?_⟩
  rw [hq, body3Next, body3Step_other q hb]

/-- A step of the 0.3 theory with bodies on a body function. -/
theorem body3Th_body_inv {B : BWeb} {q q' : Body3St} {f : FnName} (hb : isBodyFn3 f = true)
    {a : List Val} {r : Option (List Val)} (h : (body3Th B).step q (.imp f a r) = some q') :
    body3Check B q (.imp f a r) = true ∧ q' = body3Step q (.imp f a r) := by
  obtain ⟨hok, hq⟩ := gated_step_iff.1 h
  refine ⟨by simp only [body3Ok, Bool.and_eq_true] at hok; exact hok.2, ?_⟩
  rw [hq, body3Next, http3Next_body _ hb, ← body3Step_base q]

/-- A status of the status web comes from a response of the body web. -/
theorem bweb_resp {B : BWeb} {k : Val × Val} {s : BitVec 16} (h : B.web k.1 k.2 = .status s) :
    ∃ x, B k.1 k.2 = .resp x := by
  unfold BWeb.web at h
  cases hB : B k.1 k.2 with
  | resp x => exact ⟨x, rfl⟩
  | error c => rw [hB] at h; cases h

/-- `JB2` reads only the requests of the 0.3 state. -/
theorem jb2_keys {B : BWeb} {st : B2St} {q3 q3' : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (ha : q3'.base.auth = q3.base.auth) (hp : q3'.base.path = q3.base.path) : JB2 B st q3' q2 :=
  ⟨hJ.1.trans ha.symm, hJ.2.1.trans hp.symm, hJ.2.2⟩

/-- The request keys of the two versions agree on states with the same requests. -/
theorem key_eq {q2 : HttpSt} {q3 : Http3St} (ha : q2.auth = q3.auth) (hp : q2.path = q3.path)
    (r : BitVec 32) : q2.key r = q3.key r := by
  simp [HttpSt.key, Http3St.key, ha, hp]

/-! ## `get` and `status` -/

/-- `some(err)` is a step of the 0.2 theory with bodies that keeps its state. -/
theorem gotB_step (B : BWeb) (q : BodySt) (a : List Val) :
    (bodyTh B).step q (.imp futGet a (some [gotV])) = some q :=
  bodyTh_of_httpTh (by decide) (got_step B.web q.base a)

/-- **Retrieving a stored result** keeps `JB2`. -/
theorem getStoredB_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (fu : BitVec 32) (rest : List Val) {x : Val} {i : RInfo}
    (hx : lookup fu st.pend = some (some (x, i))) :
    ∃ q2', (bodyTh B).step q2
        (.imp futGet (.u32 fu :: rest) (some [.variant 1 (some (.variant 0 (some x)))])) = some q2' ∧
      JB2 B { st with pend := (fu, none) :: st.pend, resp := recResp x i st.resp } q3 q2' := by
  obtain ⟨ha, hp, hpend, hresp, hbod⟩ := hJ
  obtain ⟨k, hk, hok, hri⟩ := hpend fu (x, i) hx
  have hchk : httpOk B.web q2.base
      (.imp futGet (.u32 fu :: rest) (some [.variant 1 (some (.variant 0 (some x)))])) = true := by
    simpa [httpOk, hk, getOk] using hok
  have hpend' : ∀ fu' y, lookup fu' ((fu, none) :: st.pend) = some (some y) →
      ∃ k, lookup fu' q2.base.futs = some k ∧ PendB B k y := by
    intro fu' y hy
    by_cases hf : fu' = fu
    · subst hf; simp [lookup_cons_self] at hy
    · rw [lookup_cons_ne hf] at hy; exact hpend fu' y hy
  rcases outcomeOk_cases hok with ⟨rs, rfl⟩ | ⟨c, p, rfl⟩
  · have hs : (httpTh B.web).step q2.base (.imp futGet (.u32 fu :: rest)
        (some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.u32 rs))))))])) =
        some { q2.base with resps := (rs, k) :: q2.base.resps } :=
      gated_step_iff.2 ⟨hchk, by simp [httpNext, hk]⟩
    refine ⟨_, bodyTh_of_httpTh (by decide) hs, ha, hp, hpend', fun rs' k' hl => ?_, hbod⟩
    by_cases hr : rs' = rs
    · subst hr
      simp only [lookup_cons_self, Option.some.injEq] at hl
      subst hl
      exact ⟨i, by simp [recResp, lookup_cons_self], hri rs' rfl⟩
    · rw [lookup_cons_ne hr] at hl
      obtain ⟨v, hv, hok'⟩ := hresp rs' k' hl
      exact ⟨v, by simp only [recResp]; rw [lookup_cons_ne hr]; exact hv, hok'⟩
  · have hs : (httpTh B.web).step q2.base (.imp futGet (.u32 fu :: rest)
        (some [.variant 1 (some (.variant 0 (some (.variant 1 (some (.variant c p))))))])) =
        some q2.base := step2_quiet hchk (by simp [httpNext])
    refine ⟨_, bodyTh_of_httpTh (by decide) hs, ha, hp, hpend', ?_, hbod⟩
    simpa [recResp] using hresp

/-- **`get`** keeps `JB2`. -/
theorem getResB_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp futGet a (getResB st a).2) = some q2' ∧
      JB2 B (getResB st a).1 q3 q2' := by
  unfold getResB
  split
  · next fu rest =>
    split
    · next x i hx =>
      have h := getStoredB_step B hJ fu rest hx
      simp only [] at h ⊢
      exact h
    · exact ⟨q2, gotB_step B q2 _, hJ⟩
  · exact ⟨q2, gotB_step B q2 _, hJ⟩

/-- **`status`** keeps `JB2`. -/
theorem statusResB_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp respStatus a (statusResB st a).2) = some q2' ∧
      JB2 B (statusResB st a).1 q3 q2' := by
  refine ⟨q2, bodyTh_of_httpTh (b := q2.base) (by decide) (step2_quiet ?_ (httpNext_status _ _ _)), hJ⟩
  unfold httpOk
  split
  · next h rest r heq =>
    simp only [WEv.imp.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp only [show respStatus ≠ futGet by decide, ↓reduceIte]
    split
    · next k hl =>
      obtain ⟨v, hv, hok, -⟩ := hJ.2.2.2.1 h k hl
      simp [statusResB, selfH, hv, statusOk, hok]
    · rfl
  · rfl

/-! ## The 0.2 body functions -/

/-- A trap of a body function keeps the 0.2 body state. -/
theorem bodyStep_none (q : BodySt) (f : FnName) (a : List Val) : bodyStep q (.imp f a none) = q := by
  rcases a with _ | ⟨v, a⟩
  · rfl
  cases v
  case u32 h =>
    simp only [bodyStep]
    split_ifs
    all_goals first
      | rfl
      | (split <;> simp_all [readCount, isFailed])
  all_goals rfl

/-- A trap of a body function passes the body check. -/
theorem bodyCheck_none (B : BWeb) (q : BodySt) (f : FnName) (a : List Val) :
    bodyCheck B q (.imp f a none) = true := by
  rcases a with _ | ⟨v, a⟩
  · rfl
  cases v
  case u32 h =>
    simp only [bodyCheck]
    split_ifs
    all_goals first
      | rfl
      | (repeat' split) <;> simp [readOk, trailerOk, entriesOk]
  all_goals rfl

/-- A trap of a body function keeps `JB2`. -/
theorem bodyTrap_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    {f : FnName} (hb : isBodyFn f = true) (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp f a none) = some q2' ∧ JB2 B st q3 q2' :=
  ⟨q2, by rw [bodyTh_step_of hb (bodyCheck_none B q2 f a), bodyStep_none], hJ⟩

/-- A checked step of a body function that keeps the outgoing state. -/
theorem bodyStep_base_eq (q : BodySt) (e : WEv) : (bodyStep q e).base.auth = q.base.auth ∧
    (bodyStep q e).base.path = q.base.path ∧ (bodyStep q e).base.futs = q.base.futs ∧
    (bodyStep q e).base.resps = q.base.resps := by
  rw [bodyStep_base]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- `consume(rs, …)` answered `ok(b)`. -/
theorem bodyStep_consumeB (q : BodySt) (rs : BitVec 32) (rest : List Val) (b : BitVec 32) :
    bodyStep q (.imp consume2 (.u32 rs :: rest) (some [okV (some (.u32 b))])) =
      { q with bodies := (b, lookup rs q.base.resps) :: q.bodies } := by
  simp [bodyStep, okHandle, okV]

/-- Pushing a matching entry on both sides keeps a tracking clause. -/
theorem track_push {α β : Type} {l : List (BitVec 32 × Option α)} {m : List (BitVec 32 × β)}
    {R : α → β → Prop} (hold : ∀ h k, lookup h l = some (some k) → ∃ v, lookup h m = some v ∧ R k v)
    (h0 : BitVec 32) (o : Option α) (v0 : β) (hnew : ∀ k, o = some k → R k v0) :
    ∀ h k, lookup h ((h0, o) :: l) = some (some k) →
      ∃ v, lookup h ((h0, v0) :: m) = some v ∧ R k v := by
  intro h k hl
  by_cases hh : h = h0
  · have ho : o = some k := by
      have h' : lookup h0 ((h0, o) :: l) = some (some k) := hh ▸ hl
      rw [lookup_cons_self] at h'
      exact Option.some.inj h'
    exact ⟨v0, by rw [hh, lookup_cons_self], hnew k ho⟩
  · have hl' : lookup h l = some (some k) := by rwa [lookup_cons_ne hh] at hl
    have hm : lookup h ((h0, v0) :: m) = lookup h m := lookup_cons_ne hh _ _
    rw [hm]
    exact hold h k hl'

/-- The info recorded for a tracked response gives a matching body. -/
theorem resp_body {B : BWeb} {st : B2St} {q2 : BodySt}
    (hresp : ∀ rs k, lookup rs q2.base.resps = some k → ∃ v, lookup rs st.resp = some v ∧ RespOk B k v)
    {rs : BitVec 32} {s : BitVec 16} {bytes : List (BitVec 8)} {i : TrInfo}
    (hv : lookup rs st.resp = some (s, bytes, i)) :
    ∀ k, lookup rs q2.base.resps = some k → BodyOk B k (bytes, i) := by
  intro k hk
  obtain ⟨v, hv', hok⟩ := hresp rs k hk
  have hvv : v = (s, bytes, i) := Option.some.inj (hv'.symm.trans hv)
  rw [hvv] at hok
  exact hok.2

/-- **`consume`** keeps `JB2`. -/
theorem consumeRes_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp consume2 a (consumeResB st a).2) = some q2' ∧
      JB2 B (consumeResB st a).1 q3 q2' := by
  have hb : isBodyFn consume2 = true := by decide
  unfold consumeResB
  split
  · next rs rest =>
    split
    · next s bytes i hv =>
      have hc : bodyCheck B q2 (.imp consume2 (.u32 rs :: rest) (some [okV (some (.u32 st.fresh))])) =
          true := by
        simp [bodyCheck, isReadFn, consume2, trGet2, entries2, P2.isRead, P2.isBread]
      obtain ⟨ha, hp, hpend, hresp, hbod, hstr, hftr, htrs⟩ := hJ
      refine ⟨_, bodyTh_step_of hb hc, ?_⟩
      rw [bodyStep_consumeB]
      exact ⟨ha, hp, hpend, hresp, track_push hbod _ _ _ (resp_body hresp hv), hstr, hftr, htrs⟩
    · exact bodyTrap_step B hJ hb _
  · exact bodyTrap_step B hJ hb _

/-- `stream(b, …)` answered `ok(s)`. -/
theorem bodyStep_streamB (q : BodySt) (b : BitVec 32) (rest : List Val) (s : BitVec 32) :
    bodyStep q (.imp bodyStream2 (.u32 b :: rest) (some [okV (some (.u32 s))])) =
      { q with streams := (s, (lookup b q.bodies).join.map (·, 0)) :: q.streams } := by
  simp [bodyStep, okHandle, okV, show bodyStream2 ≠ consume2 by decide]

/-- The streams clause of `JB2` after `stream(b)` handed out `s0` with the buffer `bytes`. -/
theorem streams_push {B : BWeb} {st : B2St} {q2 : BodySt}
    (hbod : ∀ b k, lookup b q2.bodies = some (some k) → ∃ v, lookup b st.bodies = some v ∧ BodyOk B k v)
    (hstr : ∀ s k n, lookup s q2.streams = some (some (k, n)) →
      lookup s st.bufs = some ((B.body k).drop n))
    {b s0 : BitVec 32} {bytes : List (BitVec 8)} {i : TrInfo} (hv : lookup b st.bodies = some (bytes, i)) :
    ∀ s k n, lookup s ((s0, (lookup b q2.bodies).join.map (·, 0)) :: q2.streams) = some (some (k, n)) →
      lookup s ((s0, bytes) :: st.bufs) = some ((B.body k).drop n) := by
  intro s k n hl
  by_cases hs : s = s0
  · have hj : (lookup b q2.bodies).join.map (·, 0) = some (k, n) := by
      rw [hs, lookup_cons_self] at hl; exact Option.some.inj hl
    obtain ⟨k', hk', hkn⟩ := Option.map_eq_some_iff.1 hj
    have hb' : lookup b q2.bodies = some (some k') := Option.join_eq_some_iff.1 hk'
    obtain ⟨v, hv', hok⟩ := hbod b k' hb'
    have hvv : v = (bytes, i) := Option.some.inj (hv'.symm.trans hv)
    have hkk : k' = k ∧ 0 = n := Prod.mk.inj hkn
    rw [hs, lookup_cons_self, ← hkk.1, ← hkk.2, List.drop_zero, ← hok.1, hvv]
  · rw [lookup_cons_ne hs] at hl ⊢
    exact hstr s k n hl

/-- **`stream`** keeps `JB2`. -/
theorem streamRes_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp bodyStream2 a (streamResB st a).2) = some q2' ∧
      JB2 B (streamResB st a).1 q3 q2' := by
  have hb : isBodyFn bodyStream2 = true := by decide
  unfold streamResB
  split
  · next b rest =>
    split
    · next bytes i hv =>
      have hc : bodyCheck B q2 (.imp bodyStream2 (.u32 b :: rest) (some [okV (some (.u32 st.fresh))])) =
          true := by
        simp [bodyCheck, isReadFn, bodyStream2, trGet2, entries2, P2.isRead, P2.isBread]
      obtain ⟨ha, hp, hpend, hresp, hbod, hstr, hftr, htrs⟩ := hJ
      refine ⟨_, bodyTh_step_of hb hc, ?_⟩
      rw [bodyStep_streamB]
      exact ⟨ha, hp, hpend, hresp, hbod, streams_push hbod hstr hv, hftr, htrs⟩
    · exact bodyTrap_step B hJ hb _
  · exact bodyTrap_step B hJ hb _

/-- A read function is neither `consume` nor `stream`. -/
theorem readFn_ne {f : FnName} (hf : isReadFn f = true) : f ≠ consume2 ∧ f ≠ bodyStream2 := by
  simp only [isReadFn, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with rfl | rfl <;> decide

/-- A read of a tracked stream `s` answered from the buffer `rest`. -/
theorem bodyStep_readB_tracked (q : BodySt) {f : FnName} (hf : isReadFn f = true) (s : BitVec 32)
    (rest' : List Val) (rest : List (BitVec 8)) {k : Val × Val} {n : Nat}
    (hl : lookup s q.streams = some (some (k, n))) :
    bodyStep q (.imp f (.u32 s :: rest') (readAns rest (readLen (.u32 s :: rest')))) =
      if rest.isEmpty then q
      else { q with streams := (s, some (k, n + (rest.take (readLen (.u32 s :: rest'))).length)) ::
        q.streams } := by
  obtain ⟨h₁, h₂⟩ := readFn_ne hf
  unfold readAns
  by_cases he : rest.isEmpty = true
  · simp [he, bodyStep, h₁, h₂, hf, hl, readCount, isFailed, P2.errClosed, errV]
  · simp only [he, Bool.false_eq_true, ↓reduceIte, bodyStep, h₁, h₂, hf, hl, readCount, okV,
      bytesV, u8sOf_map, Option.map_some]

/-- A read of an untracked stream keeps the 0.2 body state. -/
theorem bodyStep_read_untracked (q : BodySt) {f : FnName} (hf : isReadFn f = true) (s : BitVec 32)
    (rest' : List Val) (r : Option (List Val))
    (hl : ∀ k n, lookup s q.streams ≠ some (some (k, n))) :
    bodyStep q (.imp f (.u32 s :: rest') r) = q := by
  obtain ⟨h₁, h₂⟩ := readFn_ne hf
  simp only [bodyStep, h₁, h₂, hf, ↓reduceIte]
  split
  · next k n c hl' _ => exact absurd hl' (hl k n)
  · next v hl' _ => exact absurd hl' (hl v.1 v.2)
  · rfl

/-- The streams clause of `JB2` after a buffered read of a tracked stream `s`. -/
theorem streams_after_read_tracked (B : BWeb) {st : B2St} {q2 : BodySt}
    (hS : ∀ s k n, lookup s q2.streams = some (some (k, n)) →
      lookup s st.bufs = some ((B.body k).drop n))
    {f : FnName} (hf : isReadFn f = true) (s : BitVec 32) (rest' : List Val)
    (rest : List (BitVec 8)) {k0 : Val × Val} {n0 : Nat} (hl0 : lookup s q2.streams = some (some (k0, n0)))
    (hrest : rest = (B.body k0).drop n0) :
    ∀ s' k n, lookup s' (bodyStep q2 (.imp f (.u32 s :: rest')
        (readAns rest (readLen (.u32 s :: rest'))))).streams = some (some (k, n)) →
      lookup s' ((s, rest.drop (rest.take (readLen (.u32 s :: rest'))).length) :: st.bufs) =
        some ((B.body k).drop n) := by
  intro s' k n hl
  rw [bodyStep_readB_tracked q2 hf s rest' rest hl0] at hl
  by_cases hs : s' = s
  · show lookup s' ((s, _) :: st.bufs) = _
    by_cases he : rest.isEmpty = true
    · have hl' : lookup s q2.streams = some (some (k, n)) := by simpa [he, hs] using hl
      have hkn : k0 = k ∧ n0 = n :=
        Prod.mk.inj (Option.some.inj (Option.some.inj (hl0.symm.trans hl')))
      rw [hs, lookup_cons_self, ← hkn.1, ← hkn.2, ← hrest, List.isEmpty_iff.1 he]; simp
    · have hl' : some (k0, n0 + (rest.take (readLen (.u32 s :: rest'))).length) = some (k, n) := by
        simpa [he, hs, lookup_cons_self] using hl
      have hkn := Prod.mk.inj (Option.some.inj hl')
      rw [hs, lookup_cons_self, ← hkn.1, ← hkn.2, hrest, List.drop_drop]
  · have hl' : lookup s' q2.streams = some (some (k, n)) := by
      by_cases he : rest.isEmpty = true
      · simpa [he] using hl
      · simpa [he, lookup_cons_ne hs] using hl
    rw [lookup_cons_ne hs]
    exact hS s' k n hl'

/-- The streams clause of `JB2` after a buffered read of `s`. -/
theorem streams_after_readB (B : BWeb) {st : B2St} {q2 : BodySt}
    (hS : ∀ s k n, lookup s q2.streams = some (some (k, n)) →
      lookup s st.bufs = some ((B.body k).drop n))
    {f : FnName} (hf : isReadFn f = true) (s : BitVec 32) (rest' : List Val)
    (rest : List (BitVec 8)) (hb : lookup s st.bufs = some rest) :
    ∀ s' k n, lookup s' (bodyStep q2 (.imp f (.u32 s :: rest')
        (readAns rest (readLen (.u32 s :: rest'))))).streams = some (some (k, n)) →
      lookup s' ((s, rest.drop (rest.take (readLen (.u32 s :: rest'))).length) :: st.bufs) =
        some ((B.body k).drop n) := by
  by_cases ht : ∃ k0 n0, lookup s q2.streams = some (some (k0, n0))
  · obtain ⟨k0, n0, hl0⟩ := ht
    exact streams_after_read_tracked B hS hf s rest' rest hl0
      (Option.some.inj (hb.symm.trans (hS s k0 n0 hl0)))
  · intro s' k n hl
    have hu : ∀ k n, lookup s q2.streams ≠ some (some (k, n)) := fun k n h => ht ⟨k, n, h⟩
    have hl' : lookup s' q2.streams = some (some (k, n)) := by
      rwa [bodyStep_read_untracked q2 hf s rest' _ hu] at hl
    have hs : s' ≠ s := fun h => hu k n (h ▸ hl')
    rw [lookup_cons_ne hs]
    exact hS s' k n hl'

/-- A read changes only the streams of the 0.2 body state. -/
theorem bodyStep_read_frame (q : BodySt) {f : FnName} (hf : isReadFn f = true) (a : List Val)
    (r : Option (List Val)) :
    (bodyStep q (.imp f a r)).base = q.base ∧ (bodyStep q (.imp f a r)).bodies = q.bodies ∧
      (bodyStep q (.imp f a r)).ftr = q.ftr ∧ (bodyStep q (.imp f a r)).trs = q.trs := by
  obtain ⟨h₁, h₂⟩ := readFn_ne hf
  rcases a with _ | ⟨v, a⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  cases v
  case u32 h =>
    simp only [bodyStep, h₁, h₂, hf, ↓reduceIte]
    repeat' split
    all_goals exact ⟨rfl, rfl, rfl, rfl⟩
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- The read check of a buffered answer. -/
theorem readRes_check (B : BWeb) {st : B2St} {q2 : BodySt}
    (hS : ∀ s k n, lookup s q2.streams = some (some (k, n)) →
      lookup s st.bufs = some ((B.body k).drop n))
    {f : FnName} (hf : isReadFn f = true) (s : BitVec 32) (rest' : List Val)
    {rest : List (BitVec 8)} (hbuf : lookup s st.bufs = some rest) :
    bodyCheck B q2 (.imp f (.u32 s :: rest') (readAns rest (readLen (.u32 s :: rest')))) = true := by
  simp only [bodyCheck, hf, ↓reduceIte]
  split
  · next k n hl =>
    have h' : rest = (B.body k).drop n := Option.some.inj (hbuf.symm.trans (hS s k n hl))
    rw [← h']
    exact readOk_ans rest _
  · rfl

/-- **`read` / `blocking-read`** keeps `JB2`. -/
theorem readRes_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    {f : FnName} (hf : isReadFn f = true) (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp f a (readResB st a).2) = some q2' ∧
      JB2 B (readResB st a).1 q3 q2' := by
  have hb : isBodyFn f = true := by
    simp only [isReadFn, Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with rfl | rfl <;> decide
  unfold readResB
  split
  · next s rest' =>
    split
    · next rest hbuf =>
      obtain ⟨ha, hp, hpend, hresp, hbod, hstr, hftr, htrs⟩ := hJ
      refine ⟨_, bodyTh_step_of hb (readRes_check B hstr hf s rest' hbuf), ?_⟩
      obtain ⟨hb1, hb2, hb3, hb4⟩ := bodyStep_read_frame q2 hf (.u32 s :: rest')
        (readAns rest (readLen (.u32 s :: rest')))
      exact ⟨by rw [hb1]; exact ha, by rw [hb1]; exact hp, by rw [hb1]; exact hpend,
        by rw [hb1]; exact hresp, by rw [hb2]; exact hbod,
        streams_after_readB B hstr hf s rest' rest hbuf, by rw [hb3]; exact hftr,
        by rw [hb4]; exact htrs⟩
    · exact bodyTrap_step B hJ hb _
  · exact bodyTrap_step B hJ hb _

/-- `finish(b, …)` answered `ft`. -/
theorem bodyStep_finishB (q : BodySt) (b : BitVec 32) (rest : List Val) (ft : BitVec 32) :
    bodyStep q (.imp bodyFinish2 (.u32 b :: rest) (some [.u32 ft])) =
      { q with ftr := (ft, (lookup b q.bodies).join) :: q.ftr } := by
  simp [bodyStep, show bodyFinish2 ≠ consume2 by decide, show bodyFinish2 ≠ bodyStream2 by decide,
    show isReadFn bodyFinish2 = false by decide]

/-- The trailer outcome of a tracked body. -/
theorem body_info {B : BWeb} {st : B2St} {q2 : BodySt}
    (hbod : ∀ b k, lookup b q2.bodies = some (some k) → ∃ v, lookup b st.bodies = some v ∧ BodyOk B k v)
    {b : BitVec 32} {v : List (BitVec 8) × TrInfo} (hv : lookup b st.bodies = some v) :
    ∀ k, (lookup b q2.bodies).join = some k → InfoOk B k v.2 := by
  intro k hk
  obtain ⟨v', hv', hok⟩ := hbod b k (Option.join_eq_some_iff.1 hk)
  have hvv : v' = v := Option.some.inj (hv'.symm.trans hv)
  rw [← hvv]
  exact hok.2

/-- **`finish`** keeps `JB2`. -/
theorem finishRes_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp bodyFinish2 a (finishResB st a).2) = some q2' ∧
      JB2 B (finishResB st a).1 q3 q2' := by
  have hb : isBodyFn bodyFinish2 = true := by decide
  unfold finishResB
  split
  · next b rest =>
    split
    · next bytes i hv =>
      have hc : bodyCheck B q2 (.imp bodyFinish2 (.u32 b :: rest) (some [.u32 st.fresh])) = true := by
        simp [bodyCheck, isReadFn, bodyFinish2, trGet2, entries2, P2.isRead, P2.isBread]
      obtain ⟨ha, hp, hpend, hresp, hbod, hstr, hftr, htrs⟩ := hJ
      refine ⟨_, bodyTh_step_of hb hc, ?_⟩
      rw [bodyStep_finishB]
      exact ⟨ha, hp, hpend, hresp, hbod, hstr, track_push hftr _ _ _ (body_info hbod hv), htrs⟩
    · exact bodyTrap_step B hJ hb _
  · exact bodyTrap_step B hJ hb _

/-- `future-trailers.get(ft, …)` with no trailer handle in the answer. -/
theorem bodyStep_trGetB_none (q : BodySt) (ft : BitVec 32) (rest : List Val) {r : Option (List Val)}
    (h : trHandle r = none) : bodyStep q (.imp trGet2 (.u32 ft :: rest) r) = q := by
  simp [bodyStep, h, show trGet2 ≠ consume2 by decide, show trGet2 ≠ bodyStream2 by decide,
    show isReadFn trGet2 = false by decide, show trGet2 ≠ bodyFinish2 by decide]

/-- `future-trailers.get(ft, …)` handing out the trailer handle `t`. -/
theorem bodyStep_trGetB_some (q : BodySt) (ft : BitVec 32) (rest : List Val) {r : Option (List Val)}
    {t : BitVec 32} (h : trHandle r = some t) :
    bodyStep q (.imp trGet2 (.u32 ft :: rest) r) = { q with trs := (t, (lookup ft q.ftr).join) :: q.trs } := by
  simp [bodyStep, h, show trGet2 ≠ consume2 by decide, show trGet2 ≠ bodyStream2 by decide,
    show isReadFn trGet2 = false by decide, show trGet2 ≠ bodyFinish2 by decide]

/-- The trailer check of a buffered outcome. -/
theorem trGet_checkB (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (ft : BitVec 32) (rest : List Val) {i : TrInfo} (hi : lookup ft st.ftr = some i)
    {r : Option (List Val)} (hr : ∀ k, InfoOk B k i → trailerOk (B.trailers k) r = true) :
    bodyCheck B q2 (.imp trGet2 (.u32 ft :: rest) r) = true := by
  simp only [bodyCheck, show isReadFn trGet2 = false by decide, Bool.false_eq_true, ↓reduceIte]
  split
  · next k hl =>
    obtain ⟨i', hi', hok⟩ := hJ.2.2.2.2.2.2.1 ft k hl
    rw [hi] at hi'
    cases hi'
    split
    · exact hr k hok
    · rfl
  · rfl

/-- The outcome of a tracked trailer future. -/
theorem ftr_info {B : BWeb} {st : B2St} {q2 : BodySt}
    (hftr : ∀ ft k, lookup ft q2.ftr = some (some k) → ∃ i, lookup ft st.ftr = some i ∧ InfoOk B k i)
    {ft : BitVec 32} {i : TrInfo} (hi : lookup ft st.ftr = some i) :
    ∀ k, (lookup ft q2.ftr).join = some k → InfoOk B k i := by
  intro k hk
  obtain ⟨i', hi', hok⟩ := hftr ft k (Option.join_eq_some_iff.1 hk)
  have hii : i' = i := Option.some.inj (hi'.symm.trans hi)
  rw [← hii]
  exact hok

/-- `future-trailers.get` of a future with buffered trailers keeps `JB2`. -/
theorem trGet_tr_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (ft : BitVec 32) (rest : List Val) {ans : Option (List Val)} (hi : lookup ft st.ftr = some (.tr ans)) :
    ∃ q2', (bodyTh B).step q2 (.imp trGet2 (.u32 ft :: rest)
        (some [.variant 1 (some (okV (some (okV (some (.variant 1 (some (.u32 st.fresh))))))))])) =
        some q2' ∧ JB2 B { st with trv := (st.fresh, ans) :: st.trv, next := st.next + 1 } q3 q2' := by
  have hc : bodyCheck B q2 (.imp trGet2 (.u32 ft :: rest)
      (some [.variant 1 (some (okV (some (okV (some (.variant 1 (some (.u32 st.fresh))))))))])) = true :=
    trGet_checkB B hJ ft rest hi fun k hk => by simp [trailerOk, okV, hk.1]
  obtain ⟨ha, hp, hpend, hresp, hbod, hstr, hftr, htrs⟩ := hJ
  refine ⟨_, bodyTh_step_of (by decide) hc, ?_⟩
  rw [bodyStep_trGetB_some _ _ _ rfl]
  exact ⟨ha, hp, hpend, hresp, hbod, hstr, hftr,
    track_push htrs _ _ _ fun k hk => (ftr_info hftr hi k hk).2⟩

/-- **`future-trailers.get`** keeps `JB2`. -/
theorem trGetRes_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp trGet2 a (trGetResB st a).2) = some q2' ∧
      JB2 B (trGetResB st a).1 q3 q2' := by
  have hb : isBodyFn trGet2 = true := by decide
  unfold trGetResB
  split
  · next ft rest =>
    split
    · next hi =>
      refine ⟨q2, ?_, hJ⟩
      rw [bodyTh_step_of hb (trGet_checkB B hJ ft rest hi fun k hk => ?_),
        bodyStep_trGetB_none _ _ _ rfl]
      simp [trailerOk, okV, noneV, show B.trailers k = none from hk]
    · next ans hi => exact trGet_tr_step B hJ ft rest hi
    · next v hi =>
      refine ⟨q2, ?_, hJ⟩
      rw [bodyTh_step_of hb (trGet_checkB B hJ ft rest hi fun k hk => ?_),
        bodyStep_trGetB_none _ _ _ (by simp [trHandle, okV, errV])]
      obtain ⟨c, p, rfl⟩ := hk
      simp [trailerOk, okV, errV]
    · exact bodyTrap_step B hJ hb _
  · exact bodyTrap_step B hJ hb _

/-- **`entries`** keeps `JB2`. -/
theorem entriesRes_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp entries2 a (entriesResB st a).2) = some q2' ∧
      JB2 B (entriesResB st a).1 q3 q2' := by
  have hb : isBodyFn entries2 = true := by decide
  unfold entriesResB
  split
  · next t rest =>
    split
    · next ans hans =>
      have hc : bodyCheck B q2 (.imp entries2 (.u32 t :: rest) ans) = true := by
        simp only [bodyCheck, show isReadFn entries2 = false by decide,
          show entries2 ≠ trGet2 by decide, Bool.false_eq_true, ↓reduceIte]
        split
        · next k hl =>
          obtain ⟨ans', hans', hok⟩ := hJ.2.2.2.2.2.2.2 t k hl
          rw [hans] at hans'
          cases hans'
          exact hok
        · rfl
      exact ⟨q2, by rw [bodyTh_step_of hb hc, bodyStep_entries], hJ⟩
    · exact bodyTrap_step B hJ hb _
  · exact bodyTrap_step B hJ hb _

/-- The 0.2 body functions. -/
theorem bodyFn_cases {f : FnName} (hb : isBodyFn f = true) :
    f = consume2 ∨ f = bodyStream2 ∨ f = bodyFinish2 ∨ f = trGet2 ∨ f = entries2 ∨
      isReadFn f = true := by
  simp only [isBodyFn, Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with (((((h | h) | h) | h) | h) | h) | h <;> subst h <;> decide

/-- **A 0.2 body function answered from the buffers** keeps `JB2`. -/
theorem bodyRes2_step (B : BWeb) {st : B2St} {q3 : Body3St} {q2 : BodySt} (hJ : JB2 B st q3 q2)
    {f : FnName} (hb : isBodyFn f = true) (a : List Val) :
    ∃ q2', (bodyTh B).step q2 (.imp f a (bodyRes2 st f a).2) = some q2' ∧
      JB2 B (bodyRes2 st f a).1 q3 q2' := by
  rcases bodyFn_cases hb with rfl | rfl | rfl | rfl | rfl | h
  · simp (config := {decide := true}) only [bodyRes2, ↓reduceIte]; exact consumeRes_step B hJ a
  · simp (config := {decide := true}) only [bodyRes2, ↓reduceIte]; exact streamRes_step B hJ a
  · simp (config := {decide := true}) only [bodyRes2, ↓reduceIte]; exact finishRes_step B hJ a
  · simp (config := {decide := true}) only [bodyRes2, ↓reduceIte]; exact trGetRes_step B hJ a
  · simp (config := {decide := true}) only [bodyRes2, ↓reduceIte]; exact entriesRes_step B hJ a
  · obtain ⟨h₁, h₂⟩ := readFn_ne h
    simp only [bodyRes2, h₁, h₂, h, ↓reduceIte]
    exact readRes_step B hJ h a

end Silmaril.Wasi.Versions.Net
