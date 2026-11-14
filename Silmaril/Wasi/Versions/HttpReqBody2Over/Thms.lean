module

public import Silmaril.Wasi.Versions.HttpReqBody2Over.Defs
public import Silmaril.Wasi.Versions.HttpReqBodyOver.Thms

@[expose] public section

/-!
# Outgoing request bodies, 0.2 over 0.3: theorems

PROVED (standard axioms):

* `wp_bodyWLoop`: the write loop leaves the whole body in the 0.3 theory's record of the
  stream when it reports success.
* `wp_getProg`: the program of `get(f)` answers as the 0.2 check of `get` requires, and the
  0.3 theory records exactly the response the 0.2 theory records.
* **`req2Over3_model`**: over every host of the 0.3 theory with outgoing bodies `req3Th Q`, the
  composite is a model of the 0.2 one `req2Th Q` (same request-body web). Invariant `JR2`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## The 0.3 steps -/

/-- A step of the 0.3 theory with bodies. -/
theorem req3_step {Q : QWeb} {q q' : Req3St} {e : WEv} (h : (req3Th Q).step q e = some q') :
    req3Ok Q q e = true ∧ q' = req3Next q e := by
  have h' : (if req3Ok Q q e = true then some (req3Next q e) else none) = some q' := h
  by_cases hok : req3Ok Q q e = true
  · simp only [hok, ↓reduceIte, Option.some.injEq] at h'
    exact ⟨hok, h'.symm⟩
  · simp [hok] at h'

/-- A call of a program over the 0.3 slice. -/
theorem wp_call3 {A : Type} {Q : QWeb} {f : FnName} {hf : f ∈ req3Fns} {args : List Val}
    {k : Option (List Val) → Prog (nsig req3Fns) A} {P : A → Req3St → Prop} {q : Req3St}
    (h : ∀ r, req3Ok Q q (.imp f args r) = true →
      Wp (req3Th Q) (k r) P (req3Next q (.imp f args r))) :
    Wp (req3Th Q) (.call (⟨f, hf⟩, args) k) P q := by
  intro r q' hs
  obtain ⟨hok, hq⟩ := req3_step hs
  exact hq ▸ h r hok

theorem ne_w_new : P3.cStreamWrite ≠ P3.cStreamNew := by decide
theorem ne_d_new : P3.cStreamDropW ≠ P3.cStreamNew := by decide
theorem ne_d_w : P3.cStreamDropW ≠ P3.cStreamWrite := by decide
theorem ne_r_new : reqNew3 ≠ P3.cStreamNew := by decide
theorem ne_r_w : reqNew3 ≠ P3.cStreamWrite := by decide
theorem ne_r_d : reqNew3 ≠ P3.cStreamDropW := by decide
theorem ne_a_new : setAuth3 ≠ P3.cStreamNew := by decide
theorem ne_a_w : setAuth3 ≠ P3.cStreamWrite := by decide
theorem ne_a_d : setAuth3 ≠ P3.cStreamDropW := by decide
theorem ne_a_r : setAuth3 ≠ reqNew3 := by decide
theorem ne_p_new : setPath3 ≠ P3.cStreamNew := by decide
theorem ne_p_w : setPath3 ≠ P3.cStreamWrite := by decide
theorem ne_p_d : setPath3 ≠ P3.cStreamDropW := by decide
theorem ne_p_r : setPath3 ≠ reqNew3 := by decide
theorem ne_p_a : setPath3 ≠ setAuth3 := by decide
theorem ne_new_send : P3.cStreamNew ≠ send3 := by decide
theorem ne_w_send : P3.cStreamWrite ≠ send3 := by decide
theorem ne_d_send : P3.cStreamDropW ≠ send3 := by decide
theorem ne_r_send : reqNew3 ≠ send3 := by decide
theorem ne_a_send : setAuth3 ≠ send3 := by decide
theorem ne_p_send : setPath3 ≠ send3 := by decide

/-- `stream.new`. -/
theorem n3_new (q : Req3St) (rd wr : BitVec 32) :
    req3Next q (.imp P3.cStreamNew [] (some [.u32 rd, .u32 wr])) =
      { q with pairs := (wr, rd) :: q.pairs, written := (rd, ([], false)) :: q.written } := by
  unfold req3Next
  simp only [↓reduceIte]

/-- `stream.write` on an open stream. -/
theorem n3_write (q : Req3St) {wr rd : BitVec 32} {pre : List (BitVec 8)} (rest : List (BitVec 8))
    (hp : lookup wr q.pairs = some rd) (hw : lookup rd q.written = some (pre, false))
    {r : Option (List Val)} {c : Nat} (hc : countOf3 r = some c) :
    req3Next q (.imp P3.cStreamWrite [.u32 wr, bytesV rest] r) =
      { q with written := (rd, (pre ++ rest.take c, false)) :: q.written } := by
  have hv : valOf (bytesV rest) = some rest := by simp only [valOf, bytesV, u8sOf_map]
  unfold req3Next
  simp only [ne_w_new, ↓reduceIte, hc, hp, hw, hv]

/-- `stream.drop-writable`. -/
theorem n3_drop (q : Req3St) {wr rd : BitVec 32} {bs : List (BitVec 8)} {x : Bool}
    (hp : lookup wr q.pairs = some rd) (hw : lookup rd q.written = some (bs, x)) (r : Option (List Val)) :
    req3Next q (.imp P3.cStreamDropW [.u32 wr] r) =
      { q with written := (rd, (bs, true)) :: q.written } := by
  unfold req3Next
  simp only [ne_d_new, ne_d_w, ↓reduceIte, hp, hw]

/-- `request.new` with a body stream. -/
theorem n3_req (q : Req3St) (rd rq : BitVec 32) (v : Val) :
    req3Next q (.imp reqNew3 [.u32 0, .variant 1 (some (.u32 rd)), .u32 0, noneV]
      (some [.record [.u32 rq, v]])) = { q with reqs := (rq, some rd) :: q.reqs } := by
  unfold req3Next
  simp only [ne_r_new, ne_r_w, ne_r_d, ↓reduceIte, contentsOf]

/-- A successful 0.3 `set-authority`. -/
theorem n3_auth (q : Req3St) (rq : BitVec 32) (v : Val) {r : Option (List Val)} (hr : isOkU r = true) :
    req3Next q (.imp setAuth3 [.u32 rq, v] r) = { q with auth := (rq, v) :: q.auth } := by
  unfold req3Next
  simp only [ne_a_new, ne_a_w, ne_a_d, ne_a_r, ↓reduceIte, hr]

/-- A successful 0.3 `set-path-with-query`. -/
theorem n3_path (q : Req3St) (rq : BitVec 32) (v : Val) {r : Option (List Val)} (hr : isOkU r = true) :
    req3Next q (.imp setPath3 [.u32 rq, v] r) = { q with path := (rq, v) :: q.path } := by
  unfold req3Next
  simp only [ne_p_new, ne_p_w, ne_p_d, ne_p_r, ne_p_a, ↓reduceIte, hr]

/-! ## The write loop -/

/-- **The write loop**: on success the stream's record holds the whole body. -/
theorem wp_bodyWLoop {Q : QWeb} {wr rd : BitVec 32} {R} :
    ∀ (n : Nat) (rest pre : List (BitVec 8)) {q : Req3St}, lookup wr q.pairs = some rd →
      lookup rd q.written = some (pre, false) → q.resps = R →
      Wp (req3Th Q) (bodyWLoop n wr rest)
        (fun ok q' => (ok = true → lookup wr q'.pairs = some rd ∧
          lookup rd q'.written = some (pre ++ rest, false)) ∧ q'.resps = R) q
  | n, [], pre, _, hp, hw, hR => by
    cases n <;> exact ⟨fun _ => ⟨hp, by rw [List.append_nil]; exact hw⟩, hR⟩
  | 0, _ :: _, _, _, _, _, hR => ⟨fun h => absurd h (by decide), hR⟩
  | n + 1, b :: bs, pre, q, hp, hw, hR => wp_call3 (f := P3.cStreamWrite) fun r _ => by
    cases hc : countOf3 r with
    | none => exact ⟨fun h => absurd h (by decide), (req3Next_resps _ ne_w_send _ _).trans hR⟩
    | some c =>
      rw [n3_write q (b :: bs) hp hw hc]
      have h := wp_bodyWLoop (Q := Q) n ((b :: bs).drop c) (pre ++ (b :: bs).take c) (q := { q with
        written := (rd, (pre ++ (b :: bs).take c, false)) :: q.written }) hp
        (lookup_cons_self _ _ _) hR
      rwa [List.append_assoc, List.take_append_drop] at h

/-! ## The exchange -/

/-- The answer of `send` passes the 0.2 check, and records the same response. -/
theorem wrapGet_ok {o : HttpOutcome} {x : Option (List Val)} (h : x = none ∨ sendOk o x = true) :
    (∀ v, wrapGet x = some [.variant 1 (some (.variant 0 (some v)))] → outcomeOk o v = true) ∧
      ∀ k ob R, respUpd (sendOf2 (wrapGet x)) k ob R = respUpd x k ob R := by
  rcases h with rfl | h
  · exact ⟨fun v hv => by simp [wrapGet] at hv, fun _ _ _ => rfl⟩
  · unfold sendOk at h
    split at h
    · next rs =>
      refine ⟨fun v hv => ?_, fun _ _ _ => rfl⟩
      simp only [wrapGet, Option.some.injEq, List.cons.injEq, Val.variant.injEq, and_true,
        true_and] at hv
      subst hv
      rfl
    · next c c' p =>
      refine ⟨fun v hv => ?_, fun _ _ _ => rfl⟩
      simp only [wrapGet, Option.some.injEq, List.cons.injEq, Val.variant.injEq, and_true,
        true_and] at hv
      subst hv
      simpa [outcomeOk] using h
    · cases h

/-- The postcondition of the exchange for the key `k` and the body `bs`, over the responses
`R`. -/
def XPost (Q : QWeb) (k : Val × Val) (bs : List (BitVec 8))
    (R : List (BitVec 32 × ((Val × Val) × Option (List (BitVec 8))))) (y : Option (List Val))
    (q : Req3St) : Prop :=
  (∀ v, y = some [.variant 1 (some (.variant 0 (some v)))] → outcomeOk (Q k.1 k.2 bs) v = true) ∧
    q.resps = respUpd (sendOf2 y) k (some bs) R

/-- A trap. -/
theorem xpost_none {Q : QWeb} {k : Val × Val} {bs : List (BitVec 8)} {R} {q : Req3St}
    (h : q.resps = R) : XPost Q k bs R none q := ⟨fun _ hv => (by cases hv), h⟩

/-- `send` of a request with the key `k` and the finished body `bs`. -/
theorem wp_sendX3 {Q : QWeb} {q : Req3St} {rq : BitVec 32} {k : Val × Val} {bs : List (BitVec 8)}
    {R} (hk : q.key rq = k) (hd : q.done rq = some bs) (hR : q.resps = R) :
    Wp (req3Th Q) (.call (mSend3, [.u32 rq]) fun x => .pure (wrapGet x)) (XPost Q k bs R) q :=
  wp_call3 (f := send3) fun x hok => by
    have hs : x = none ∨ sendOk (Q k.1 k.2 bs) x = true := by
      cases x with
      | none => exact Or.inl rfl
      | some l => exact Or.inr (by simpa [req3Ok, hd, hk] using hok)
    obtain ⟨h₁, h₂⟩ := wrapGet_ok hs
    exact ⟨h₁, by rw [req3Next_send_resps, hk, hd, hR, h₂]⟩

/-- The request, its key, `send`. -/
theorem wp_reqXchg2 {Q : QWeb} {q : Req3St} {rd : BitVec 32} {k : Val × Val}
    {bs : List (BitVec 8)} {R} (hw : lookup rd q.written = some (bs, true)) (hR : q.resps = R) :
    Wp (req3Th Q) (reqXchg2 rd k) (XPost Q k bs R) q := wp_call3 (f := reqNew3) fun r _ => by
  split
  · rw [n3_req]
    refine wp_call3 (f := setAuth3) fun r₁ _ => ?_
    by_cases h₁ : isOkU r₁ = true
    · simp only [h₁, ↓reduceIte]
      rw [n3_auth _ _ _ h₁]
      refine wp_call3 (f := setPath3) fun r₂ _ => ?_
      by_cases h₂ : isOkU r₂ = true
      · simp only [h₂, ↓reduceIte]
        rw [n3_path _ _ _ h₂]
        exact wp_sendX3 (by simp [Req3St.key, lookup_cons_self])
          (by simp [Req3St.done, lookup_cons_self, hw]) hR
      · simp only [h₂, Bool.false_eq_true, ↓reduceIte]
        exact xpost_none ((req3Next_resps _ ne_p_send _ _).trans hR)
    · simp only [h₁, Bool.false_eq_true, ↓reduceIte]
      exact xpost_none ((req3Next_resps _ ne_a_send _ _).trans hR)
  · exact xpost_none ((req3Next_resps _ ne_r_send _ _).trans hR)

/-- After `stream.new`. -/
theorem wp_reqXchg1 {Q : QWeb} (rounds : Nat) {q : Req3St} {rd wr : BitVec 32} {k : Val × Val}
    {bs : List (BitVec 8)} {R} (hp : lookup wr q.pairs = some rd)
    (hw : lookup rd q.written = some ([], false)) (hR : q.resps = R) :
    Wp (req3Th Q) (reqXchg1 rounds rd wr k bs) (XPost Q k bs R) q := by
  unfold reqXchg1
  rw [Wp.bind]
  refine Wp.mono (fun ok q' h => ?_) (wp_bodyWLoop rounds bs [] hp hw hR)
  by_cases ho : ok = true
  · simp only [ho, ↓reduceIte]
    obtain ⟨hp', hw'⟩ := h.1 ho
    refine wp_call3 (f := P3.cStreamDropW) fun r _ => ?_
    rw [n3_drop q' hp' hw' r]
    exact wp_reqXchg2 (by rw [lookup_cons_self, List.nil_append]) h.2
  · simp only [ho, Bool.false_eq_true, ↓reduceIte]
    exact xpost_none h.2

/-- **The exchange.** -/
theorem wp_reqXchg {Q : QWeb} (rounds : Nat) {q : Req3St} {k : Val × Val} {bs : List (BitVec 8)}
    {R} (hR : q.resps = R) : Wp (req3Th Q) (reqXchg rounds k bs) (XPost Q k bs R) q :=
  wp_call3 (f := P3.cStreamNew) fun r _ => by
    split
    · rw [n3_new]
      exact wp_reqXchg1 rounds (lookup_cons_self _ _ _) (lookup_cons_self _ _ _) hR
    · exact xpost_none ((req3Next_resps _ ne_new_send _ _).trans hR)

/-! ## The invariant -/

/-- The postcondition of the program of an export call `f a`: the 0.2 check passes, and the
0.3 theory records the responses the 0.2 theory records. -/
def ProgPost2 (Q : QWeb) (q2 : Req2St) (f : FnName) (a : List Val) (x : Option (List Val))
    (q3 : Req3St) : Prop :=
  req2Ok Q q2 (.imp f a x) = true ∧ q3.resps = (req2Next q2 (.imp f a x)).resps

/-- A `get` that traps. -/
theorem progPost2_trap (Q : QWeb) (q2 : Req2St) (a : List Val) {q3 : Req3St}
    (hR : q3.resps = q2.resps) : ProgPost2 Q q2 futGet a none q3 := by
  refine ⟨?_, ?_⟩
  · rcases a with _ | ⟨v, a'⟩
    · rfl
    cases v <;> simp [req2Ok]
  · rcases a with _ | ⟨v, a'⟩
    · exact hR
    cases v
    case u32 h => simp [req2Next, ne_get_auth, ne_get_path, ne_get_body, ne_get_write,
      isWrite_get, ne_get_fin, ne_get_hdl, hR]
    all_goals exact hR

/-- `get`, from the postcondition of the exchange. -/
theorem progPost2_get {Q : QWeb} {q2 : Req2St} {fu : BitVec 32} {rest : List Val}
    {k : Val × Val} {ob : Option (BitVec 32)} {bs : List (BitVec 8)}
    (hf : lookup fu q2.futs = some (k, ob)) (hd : q2.done ob = some bs) {y : Option (List Val)}
    {q3 : Req3St} (h : XPost Q k bs q2.resps y q3) : ProgPost2 Q q2 futGet (.u32 fu :: rest) y q3 := by
  refine ⟨?_, by rw [h.2, n_get_resps q2 hf rest y, hd]⟩
  have hc : ∀ v, y = some [.variant 1 (some (.variant 0 (some v)))] →
      outcomeOk (Q k.1 k.2 bs) v = true := h.1
  simp only [req2Ok, ↓reduceIte]
  split
  · simp_all
  · rfl

/-- The program of `get`. -/
theorem wp_getProg (Q : QWeb) (rounds : Nat) {s q2 : Req2St} (hs : s = q2) (a : List Val)
    {q3 : Req3St} (hR : q3.resps = q2.resps) :
    Wp (req3Th Q) (getProg rounds s a) (ProgPost2 Q q2 futGet a) q3 := by
  subst hs
  rcases a with _ | ⟨v, rest⟩
  · exact progPost2_trap Q s [] hR
  cases v
  case u32 fu =>
    cases hf : lookup fu s.futs with
    | none =>
      simp only [getProg, hf]
      exact progPost2_trap Q s _ hR
    | some kob =>
      obtain ⟨k, ob⟩ := kob
      cases hd : s.done ob with
      | none =>
        simp only [getProg, hf, hd]
        exact progPost2_trap Q s _ hR
      | some bs =>
        simp only [getProg, hf, hd]
        exact Wp.mono (fun y q h => progPost2_get hf hd h) (wp_reqXchg rounds hR)
  all_goals exact progPost2_trap Q s _ hR

/-- The checks of `status` agree on equal responses (0.2 side). -/
theorem req2Ok_status (Q : QWeb) {q2 : Req2St} {q3 : Req3St} (hR : q3.resps = q2.resps)
    (a : List Val) (r : Option (List Val)) :
    req2Ok Q q2 (.imp respStatus a r) = req3Ok Q q3 (.imp getStatus3 a r) :=
  (req3Ok_status Q hR.symm a r).symm

/-- The check of an export served without the host. -/
theorem req2Ok_other (Q : QWeb) (q : Req2St) {f : FnName} (h₁ : f ≠ futGet) (h₂ : f ≠ respStatus)
    (a : List Val) (r : Option (List Val)) : req2Ok Q q (.imp f a r) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h => simp [req2Ok, h₁, h₂]
  all_goals rfl

/-- **The program of an export call.** -/
theorem wp_prog2 (Q : QWeb) (rounds : Nat) {s : Req2St × Nat} {q2 : Req2St} (hs : s.1 = q2)
    (f : FnName) (a : List Val) {q3 : Req3St} (hR : q3.resps = q2.resps) :
    Wp (req3Th Q) (req2Prog rounds s f a) (ProgPost2 Q q2 f a) q3 := by
  unfold req2Prog
  by_cases h₁ : f = futGet
  · subst h₁
    simpa using wp_getProg Q rounds hs a hR
  · by_cases h₂ : f = respStatus
    · subst h₂
      simp only [ne_st_get, ↓reduceIte]
      refine wp_call3 (f := getStatus3) fun r hok => ?_
      exact ⟨(req2Ok_status Q hR a r).trans hok,
        by rw [req2Next_status, req3Next_resps _ ne_status3_send, hR]⟩
    · simp only [h₁, h₂, ↓reduceIte]
      exact ⟨req2Ok_other Q q2 h₁ h₂ a _, by rw [req2Next_resps _ h₁, hR]⟩

/-- **The invariant of `req2Over3`.** -/
theorem req2Over3_inv (Q : QWeb) (rounds : Nat) :
    WpInv (req2Over3 rounds) ({}, 0) (req3Th Q) (req2Th Q) JR2 where
  init := ⟨rfl, rfl⟩
  call := by
    intro s q3 q2 c hJ
    show Wp (req3Th Q) ((req2Prog rounds s c.1.1 c.2).bind _) _ q3
    rw [Wp.bind]
    refine Wp.mono (fun x q3' h => ?_) (wp_prog2 Q rounds hJ.1 c.1.1 c.2 hJ.2)
    refine ⟨req2Next q2 (.imp c.1.1 c.2 x), ?_, by rw [hJ.1], h.2⟩
    show (if req2Ok Q q2 (.imp c.1.1 c.2 x) = true then some _ else none) = _
    simp only [h.1, ↓reduceIte]

/-- **Outgoing request bodies, 0.2 over 0.3**: over every host of the 0.3 theory with outgoing
bodies, the composite is a model of the 0.2 one, for the same request-body web. -/
theorem req2Over3_model (Q : QWeb) (rounds : Nat) {Y : Sig.{0}} {η : Host Y req3Fns}
    (hη : (hostSat (req3Th Q).Accepts).holds η) :
    (hostSat (req2Th Q).Accepts).holds (link η (ofSBody (req2Over3 rounds) ({}, 0))) :=
  link_model (ag_of_wpInv (req2Over3_inv Q rounds)) hη

end Silmaril.Wasi.Versions.Net
