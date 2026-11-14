module

public import Silmaril.Wasi.Versions.HttpReqBodyOver.Defs
public import Silmaril.Wasi.Versions.HttpReqBody.Thms
public import Silmaril.Wasi.Versions.HttpOver.Thms
public import Silmaril.Wasi.Versions.HttpBody.Thms

@[expose] public section

/-!
# Outgoing request bodies, 0.3 over 0.2: theorems

PROVED (standard axioms):

* `wp_sendB`: the program of `send(r)` answers as `sendOk` allows for the web's outcome at the
  key and the finished body of the adapter's copy of the 0.3 state, and the 0.2 theory records
  exactly the response the 0.3 theory records.
* **`req3Over2_model`**: over every host of the 0.2 theory with outgoing bodies `req2Th Q`, the
  composite is a model of the 0.3 one `req3Th Q` (same request-body web). Invariant `JR3`.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## The 0.2 steps -/

/-- A step of the 0.2 theory with bodies. -/
theorem req2_step {Q : QWeb} {q q' : Req2St} {e : WEv} (h : (req2Th Q).step q e = some q') :
    req2Ok Q q e = true ∧ q' = req2Next q e := by
  have h' : (if req2Ok Q q e = true then some (req2Next q e) else none) = some q' := h
  by_cases hok : req2Ok Q q e = true
  · simp only [hok, ↓reduceIte, Option.some.injEq] at h'
    exact ⟨hok, h'.symm⟩
  · simp [hok] at h'

/-- A call of the program: its answer passes the check, and the state is the next one. -/
theorem wp_call2 {A : Type} {Q : QWeb} {f : FnName} {hf : f ∈ req2Fns} {args : List Val}
    {k : Option (List Val) → Prog (nsig req2Fns) A} {P : A → Req2St → Prop} {q : Req2St}
    (h : ∀ r, req2Ok Q q (.imp f args r) = true →
      Wp (req2Th Q) (k r) P (req2Next q (.imp f args r))) :
    Wp (req2Th Q) (.call (⟨f, hf⟩, args) k) P q := by
  intro r q' hs
  obtain ⟨hok, hq⟩ := req2_step hs
  exact hq ▸ h r hok

theorem ne_path_auth : setPath ≠ setAuthority := by decide
theorem ne_body_auth : outReqBody2 ≠ setAuthority := by decide
theorem ne_body_path : outReqBody2 ≠ setPath := by decide
theorem ne_write_auth : outBodyWrite2 ≠ setAuthority := by decide
theorem ne_write_path : outBodyWrite2 ≠ setPath := by decide
theorem ne_write_body : outBodyWrite2 ≠ outReqBody2 := by decide
theorem ne_bwf_auth : P2.osBwf ≠ setAuthority := by decide
theorem ne_bwf_path : P2.osBwf ≠ setPath := by decide
theorem ne_bwf_body : P2.osBwf ≠ outReqBody2 := by decide
theorem ne_bwf_write : P2.osBwf ≠ outBodyWrite2 := by decide
theorem isWrite_bwf : isWriteFn P2.osBwf = true := by decide
theorem ne_fin_auth : outBodyFinish2 ≠ setAuthority := by decide
theorem ne_fin_path : outBodyFinish2 ≠ setPath := by decide
theorem ne_fin_body : outBodyFinish2 ≠ outReqBody2 := by decide
theorem ne_fin_write : outBodyFinish2 ≠ outBodyWrite2 := by decide
theorem isWrite_fin : isWriteFn outBodyFinish2 = false := by decide
theorem ne_hdl_auth : httpHandle ≠ setAuthority := by decide
theorem ne_hdl_path : httpHandle ≠ setPath := by decide
theorem ne_hdl_body : httpHandle ≠ outReqBody2 := by decide
theorem ne_hdl_write : httpHandle ≠ outBodyWrite2 := by decide
theorem isWrite_hdl : isWriteFn httpHandle = false := by decide
theorem ne_hdl_fin : httpHandle ≠ outBodyFinish2 := by decide
theorem ne_get_auth : futGet ≠ setAuthority := by decide
theorem ne_get_path : futGet ≠ setPath := by decide
theorem ne_get_body : futGet ≠ outReqBody2 := by decide
theorem ne_get_write : futGet ≠ outBodyWrite2 := by decide
theorem isWrite_get : isWriteFn futGet = false := by decide
theorem ne_get_fin : futGet ≠ outBodyFinish2 := by decide
theorem ne_get_hdl : futGet ≠ httpHandle := by decide
theorem ne_st_auth : respStatus ≠ setAuthority := by decide
theorem ne_st_path : respStatus ≠ setPath := by decide
theorem ne_st_body : respStatus ≠ outReqBody2 := by decide
theorem ne_st_write : respStatus ≠ outBodyWrite2 := by decide
theorem isWrite_st : isWriteFn respStatus = false := by decide
theorem ne_st_fin : respStatus ≠ outBodyFinish2 := by decide
theorem ne_st_hdl : respStatus ≠ httpHandle := by decide
theorem ne_st_get : respStatus ≠ futGet := by decide
theorem ne_auth_get : setAuthority ≠ futGet := by decide
theorem ne_path_get : setPath ≠ futGet := by decide
theorem ne_body_get : outReqBody2 ≠ futGet := by decide
theorem ne_write_get : outBodyWrite2 ≠ futGet := by decide
theorem ne_bwf_get : P2.osBwf ≠ futGet := by decide
theorem ne_fin_get : outBodyFinish2 ≠ futGet := by decide
theorem ne_hdl_get : httpHandle ≠ futGet := by decide

/-- A write keeps the responses. -/
theorem writeNext_resps (q : Req2St) (s : BitVec 32) (c : Val) : (writeNext q s c).resps = q.resps := by
  unfold writeNext; split <;> (try split) <;> rfl

/-- **Only `get` records responses.** -/
theorem req2Next_resps (q : Req2St) {f : FnName} (hf : f ≠ futGet) (a : List Val)
    (r : Option (List Val)) : (req2Next q (.imp f a r)).resps = q.resps := by
  rcases a with _ | ⟨v, rest⟩
  · rfl
  cases v
  case u32 h =>
    simp only [req2Next]
    split_ifs <;> first
      | rfl
      | (split <;> first | rfl | exact writeNext_resps _ _ _)
  all_goals rfl

/-- `status` keeps the state. -/
theorem req2Next_status (q : Req2St) (a : List Val) (r : Option (List Val)) :
    req2Next q (.imp respStatus a r) = q := by
  rcases a with _ | ⟨v, rest⟩
  · rfl
  cases v
  case u32 h =>
    simp [req2Next, ne_st_auth, ne_st_path, ne_st_body, ne_st_write, isWrite_st, ne_st_fin,
      ne_st_hdl, ne_st_get]
  all_goals rfl

/-- A successful `set-authority`. -/
theorem n_setAuth (q : Req2St) (h : BitVec 32) (v : Val) {r : Option (List Val)} (hr : isOkU r = true) :
    req2Next q (.imp setAuthority [.u32 h, v] r) = { q with auth := (h, v) :: q.auth } := by
  simp [req2Next, hr]

/-- A successful `set-path-with-query`. -/
theorem n_setPath (q : Req2St) (h : BitVec 32) (v : Val) {r : Option (List Val)} (hr : isOkU r = true) :
    req2Next q (.imp setPath [.u32 h, v] r) = { q with path := (h, v) :: q.path } := by
  simp [req2Next, hr, ne_path_auth]

/-- A successful `outgoing-request.body`. -/
theorem n_body (q : Req2St) (h b : BitVec 32) {r : Option (List Val)} (hr : okHandle r = some b) :
    req2Next q (.imp outReqBody2 [.u32 h] r) =
      { q with rbody := (h, b) :: q.rbody, written := (b, ([], false)) :: q.written } := by
  simp [req2Next, hr, ne_body_auth, ne_body_path]

/-- A successful `outgoing-body.write`. -/
theorem n_write (q : Req2St) (b s : BitVec 32) {r : Option (List Val)} (hr : okHandle r = some s) :
    req2Next q (.imp outBodyWrite2 [.u32 b] r) = { q with sbody := (s, b) :: q.sbody } := by
  simp [req2Next, hr, ne_write_auth, ne_write_path, ne_write_body]

/-- A successful `blocking-write-and-flush` of the bytes `bs` on a stream of an open body. -/
theorem n_bwf (q : Req2St) {s b : BitVec 32} {bs₀ : List (BitVec 8)} (bs : List (BitVec 8))
    (hs : lookup s q.sbody = some b) (hb : lookup b q.written = some (bs₀, false))
    {r : Option (List Val)} (hr : isOkU r = true) :
    req2Next q (.imp P2.osBwf [.u32 s, bytesV bs] r) =
      { q with written := (b, (bs₀ ++ bs, false)) :: q.written } := by
  have hv : valOf (bytesV bs) = some bs := by simp only [valOf, bytesV, u8sOf_map]
  simp [req2Next, hr, ne_bwf_auth, ne_bwf_path, ne_bwf_body, ne_bwf_write, isWrite_bwf,
    writeNext, hs, hb, hv]

/-- A successful `outgoing-body.finish`. -/
theorem n_finish (q : Req2St) {b : BitVec 32} {bs : List (BitVec 8)} {x : Bool} (t : Val)
    (hb : lookup b q.written = some (bs, x)) {r : Option (List Val)} (hr : isOkU r = true) :
    req2Next q (.imp outBodyFinish2 [.u32 b, t] r) =
      { q with written := (b, (bs, true)) :: q.written } := by
  simp [req2Next, hr, hb, ne_fin_auth, ne_fin_path, ne_fin_body, ne_fin_write, isWrite_fin]

/-- A successful `handle`. -/
theorem n_handle (q : Req2St) (rq fu : BitVec 32) (t : Val) {r : Option (List Val)}
    (hr : okHandle r = some fu) :
    req2Next q (.imp httpHandle [.u32 rq, t] r) =
      { q with futs := (fu, (q.key rq, lookup rq q.rbody)) :: q.futs } := by
  simp [req2Next, hr, ne_hdl_auth, ne_hdl_path, ne_hdl_body, ne_hdl_write, isWrite_hdl, ne_hdl_fin]

/-- A pending `get` keeps the state. -/
theorem n_pending (q : Req2St) (fu : BitVec 32) {r : Option (List Val)} (hr : isPending r = true) :
    req2Next q (.imp futGet [.u32 fu] r) = q := by
  have hr' : r = some [.variant 0 none] := by
    unfold isPending at hr; split at hr <;> first | rfl | cases hr
  subst hr'
  simp [req2Next, ne_get_auth, ne_get_path, ne_get_body, ne_get_write, isWrite_get, ne_get_fin,
    ne_get_hdl]

/-! ## Responses -/

/-- The responses after an answer `x` of `send` for the key `k` and the body `ob`. -/
def respUpd (x : Option (List Val)) (k : Val × Val) (ob : Option (List (BitVec 8)))
    (R : List (BitVec 32 × ((Val × Val) × Option (List (BitVec 8))))) :
    List (BitVec 32 × ((Val × Val) × Option (List (BitVec 8)))) :=
  match x with
  | some [.variant 0 (some (.u32 rs))] => (rs, (k, ob)) :: R
  | _ => R

/-- An answer of `get` without a response records none. -/
theorem respUpd_sendOf2 {r : Option (List Val)}
    (h : ∀ rs, ¬r = some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.u32 rs))))))])
    (k : Val × Val) (ob : Option (List (BitVec 8))) (R) : respUpd (sendOf2 r) k ob R = R := by
  unfold sendOf2
  split
  · next rs => exact absurd rfl (h rs)
  · rfl
  · rfl

/-- The responses after a `get` answer: those of the inner result. -/
theorem n_get_resps (q : Req2St) {fu : BitVec 32} {k : Val × Val} {ob : Option (BitVec 32)}
    (hf : lookup fu q.futs = some (k, ob)) (rest : List Val) (r : Option (List Val)) :
    (req2Next q (.imp futGet (.u32 fu :: rest) r)).resps = respUpd (sendOf2 r) k (q.done ob) q.resps := by
  simp only [req2Next, ne_get_auth, ne_get_path, ne_get_body, ne_get_write, isWrite_get,
    ne_get_fin, ne_get_hdl, Bool.false_eq_true, ↓reduceIte, hf]
  split
  · next rs k' ob' hl =>
    have he : (k', ob') = (k, ob) := (Option.some.inj hl).symm
    simp only [Prod.mk.injEq] at he
    rw [he.1, he.2]
    rfl
  · next hn => exact (respUpd_sendOf2 (fun rs h => hn rs k ob h rfl) k _ _).symm

/-- The postcondition of the program of `send` for the key `k` and the body `bs`, over the
responses `R`. -/
def SendPost (Q : QWeb) (k : Val × Val) (bs : List (BitVec 8))
    (R : List (BitVec 32 × ((Val × Val) × Option (List (BitVec 8))))) (x : Option (List Val))
    (q : Req2St) : Prop :=
  (x = none ∨ sendOk (Q k.1 k.2 bs) x = true) ∧ q.resps = respUpd x k (some bs) R

/-- A trap. -/
theorem post_none {Q : QWeb} {k : Val × Val} {bs : List (BitVec 8)} {R} {q : Req2St}
    (h : q.resps = R) : SendPost Q k bs R none q := ⟨Or.inl rfl, h⟩

/-- The answer of the final `get` passes the 0.3 check. -/
theorem sendOf2_ok {o : HttpOutcome} {r : Option (List Val)}
    (h : ∀ x, r = some [.variant 1 (some (.variant 0 (some x)))] → outcomeOk o x = true) :
    sendOf2 r = none ∨ sendOk o (sendOf2 r) = true := by
  unfold sendOf2
  split
  · next rs => exact Or.inr (by have := h _ rfl; cases o <;> simp_all [outcomeOk, sendOk, okV])
  · next c p => exact Or.inr (by have := h _ rfl; cases o <;> simp_all [outcomeOk, sendOk, errV])
  · exact Or.inl rfl

/-- **The final `get`.** -/
theorem get_final {Q : QWeb} {q : Req2St} {fu b : BitVec 32} {k : Val × Val}
    {bs : List (BitVec 8)} {R} (hf : lookup fu q.futs = some (k, some b))
    (hw : lookup b q.written = some (bs, true)) (hR : q.resps = R) {r : Option (List Val)}
    (hok : req2Ok Q q (.imp futGet [.u32 fu] r) = true) :
    SendPost Q k bs R (sendOf2 r) (req2Next q (.imp futGet [.u32 fu] r)) := by
  have hd : q.done (some b) = some bs := by simp [Req2St.done, hw]
  refine ⟨sendOf2_ok fun x hx => ?_, by rw [n_get_resps q hf [] r, hd, hR]⟩
  subst hx
  simpa [req2Ok, hf, hd] using hok

/-- **Polling.** -/
theorem wp_pollGetB {Q : QWeb} {fu b : BitVec 32} {k : Val × Val} {bs : List (BitVec 8)} {R} :
    ∀ (n : Nat) {q : Req2St}, lookup fu q.futs = some (k, some b) →
      lookup b q.written = some (bs, true) → q.resps = R →
      Wp (req2Th Q) (pollGetB n fu) (SendPost Q k bs R) q
  | 0, _, _, _, hR => post_none hR
  | n + 1, q, hf, hw, hR => wp_call2 (f := futGet) fun r hok => by
    show Wp (req2Th Q) (if isPending r then pollGetB n fu else .pure (sendOf2 r)) _ _
    by_cases hp : isPending r = true
    · simp only [hp, ↓reduceIte, n_pending q fu hp]
      exact wp_pollGetB n hf hw hR
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact get_final hf hw hR hok

/-! ## The stages of `send` -/

/-- `handle`, then poll. -/
theorem wp_sendB4 {Q : QWeb} (rounds : Nat) {q : Req2St} {rq b : BitVec 32} {k : Val × Val}
    {bs : List (BitVec 8)} {R} (hk : q.key rq = k) (hb : lookup rq q.rbody = some b)
    (hw : lookup b q.written = some (bs, true)) (hR : q.resps = R) :
    Wp (req2Th Q) (sendB4 rounds rq) (SendPost Q k bs R) q := wp_call2 (f := httpHandle) fun r _ => by
  show Wp (req2Th Q) (match okHandle r with | some fu => pollGetB rounds fu | none => .pure none) _ _
  cases hr : okHandle r with
  | none => exact post_none ((req2Next_resps q ne_hdl_get _ r).trans hR)
  | some fu =>
    rw [n_handle q rq fu noneV hr]
    exact wp_pollGetB rounds (by rw [lookup_cons_self, hk, hb]) hw hR

/-- Write the body, finish it, then `handle`. -/
theorem wp_sendB3 {Q : QWeb} (rounds : Nat) {q : Req2St} {rq b st : BitVec 32} {k : Val × Val}
    {bs : List (BitVec 8)} {R} (hs : lookup st q.sbody = some b)
    (hw : lookup b q.written = some ([], false)) (hk : q.key rq = k)
    (hb : lookup rq q.rbody = some b) (hR : q.resps = R) :
    Wp (req2Th Q) (sendB3 rounds rq b st bs) (SendPost Q k bs R) q :=
  wp_call2 (f := P2.osBwf) fun r _ => by
    by_cases hr : isOkU r = true
    · simp only [hr, ↓reduceIte]
      rw [n_bwf q bs hs hw hr]
      refine wp_call2 (f := outBodyFinish2) fun r' _ => ?_
      by_cases hr' : isOkU r' = true
      · simp only [hr', ↓reduceIte]
        rw [n_finish _ noneV (lookup_cons_self _ _ _) hr']
        exact wp_sendB4 rounds hk hb (by rw [lookup_cons_self, List.nil_append]) hR
      · simp only [hr', Bool.false_eq_true, ↓reduceIte]
        exact post_none ((req2Next_resps _ ne_fin_get _ _).trans hR)
    · simp only [hr, Bool.false_eq_true, ↓reduceIte]
      exact post_none ((req2Next_resps _ ne_bwf_get _ _).trans hR)

/-- Take the body and its stream, then write. -/
theorem wp_sendB2 {Q : QWeb} (rounds : Nat) {q : Req2St} {rq : BitVec 32} {k : Val × Val}
    {bs : List (BitVec 8)} {R} (hk : q.key rq = k) (hR : q.resps = R) :
    Wp (req2Th Q) (sendB2 rounds rq bs) (SendPost Q k bs R) q :=
  wp_call2 (f := outReqBody2) fun r _ => by
    cases hr : okHandle r with
    | none =>
      simp only
      exact post_none ((req2Next_resps _ ne_body_get _ _).trans hR)
    | some b =>
      simp only
      rw [n_body q rq b hr]
      refine wp_call2 (f := outBodyWrite2) fun r' _ => ?_
      cases hr' : okHandle r' with
      | none =>
        simp only
        exact post_none ((req2Next_resps _ ne_write_get _ _).trans hR)
      | some st =>
        simp only
        rw [n_write _ b st hr']
        exact wp_sendB3 rounds (lookup_cons_self _ _ _) (lookup_cons_self _ _ _) hk
          (lookup_cons_self _ _ _) hR

/-- **The program of `send(r)`** for a finished body `bs` of the adapter's copy `s`. -/
theorem wp_sendB {Q : QWeb} (rounds : Nat) (s : Req3St) {rq : BitVec 32} {rest : List Val}
    {bs : List (BitVec 8)} (hd : s.done rq = some bs) (q : Req2St) :
    Wp (req2Th Q) (sendB rounds s (.u32 rq :: rest)) (SendPost Q (s.key rq) bs q.resps) q := by
  simp only [sendB, hd]
  refine wp_call2 (f := setAuthority) fun r _ => ?_
  by_cases hr : isOkU r = true
  · simp only [hr, ↓reduceIte]
    rw [n_setAuth q rq _ hr]
    refine wp_call2 (f := setPath) fun r' _ => ?_
    by_cases hr' : isOkU r' = true
    · simp only [hr', ↓reduceIte]
      rw [n_setPath _ rq _ hr']
      exact wp_sendB2 rounds (by simp [Req2St.key, lookup_cons_self]) rfl
    · simp only [hr', Bool.false_eq_true, ↓reduceIte]
      exact post_none (req2Next_resps _ ne_path_get _ _)
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]
    exact post_none (req2Next_resps _ ne_auth_get _ _)

/-! ## The 0.3 steps -/

theorem ne_send_new : send3 ≠ P3.cStreamNew := by decide
theorem ne_send_write : send3 ≠ P3.cStreamWrite := by decide
theorem ne_send_drop : send3 ≠ P3.cStreamDropW := by decide
theorem ne_send_req : send3 ≠ reqNew3 := by decide
theorem ne_send_auth : send3 ≠ setAuth3 := by decide
theorem ne_send_path : send3 ≠ setPath3 := by decide
theorem ne_status3_send : getStatus3 ≠ send3 := by decide

/-- Only `send` records responses. -/
theorem req3Next_resps (q : Req3St) {f : FnName} (hf : f ≠ send3) (a : List Val)
    (r : Option (List Val)) : (req3Next q (.imp f a r)).resps = q.resps := by
  unfold req3Next
  dsimp only
  split_ifs <;> (repeat' split) <;> rfl

/-- A `send` that trapped keeps the state. -/
theorem req3Next_send_none (q : Req3St) (a : List Val) : req3Next q (.imp send3 a none) = q := by
  unfold req3Next
  simp only [ne_send_new, ne_send_write, ne_send_drop, ne_send_req, ne_send_auth,
    ne_send_path, ↓reduceIte]

/-- The responses after `send`. -/
theorem req3Next_send_resps (q : Req3St) (rq : BitVec 32) (rest : List Val) (x : Option (List Val)) :
    (req3Next q (.imp send3 (.u32 rq :: rest) x)).resps = respUpd x (q.key rq) (q.done rq) q.resps := by
  unfold req3Next
  simp only [ne_send_new, ne_send_write, ne_send_drop, ne_send_req, ne_send_auth,
    ne_send_path, ↓reduceIte]
  split
  · next h t rs he =>
    have hh : rq = h := Val.u32.inj (List.cons.inj he).1
    rw [hh]
    rfl
  · next hn =>
    unfold respUpd
    split
    · next rs => exact absurd rfl (hn rq rest rs rfl)
    · rfl

/-- The check of an export served without the host. -/
theorem req3Ok_other (Q : QWeb) (q : Req3St) {f : FnName} (h₁ : f ≠ send3) (h₂ : f ≠ getStatus3)
    (a : List Val) (r : Option (List Val)) : req3Ok Q q (.imp f a r) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h => simp [req3Ok, h₁, h₂]
  all_goals rfl

/-- The checks of `status` agree on equal responses. -/
theorem req3Ok_status (Q : QWeb) {q2 : Req2St} {q3 : Req3St} (hR : q2.resps = q3.resps)
    (a : List Val) (r : Option (List Val)) :
    req3Ok Q q3 (.imp getStatus3 a r) = req2Ok Q q2 (.imp respStatus a r) := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h => simp [req3Ok, req2Ok, ne_status3_send, ne_st_get, hR]
  all_goals rfl

/-! ## The invariant -/

/-- The postcondition of the program of an export call `f a`: the 0.3 check passes, and the
0.2 theory records the responses the 0.3 theory records. -/
def ProgPost (Q : QWeb) (q3 : Req3St) (f : FnName) (a : List Val) (x : Option (List Val))
    (q2 : Req2St) : Prop :=
  req3Ok Q q3 (.imp f a x) = true ∧ q2.resps = (req3Next q3 (.imp f a x)).resps

/-- `send`, from its postcondition. -/
theorem progPost_send {Q : QWeb} {q3 : Req3St} {rq : BitVec 32} {rest : List Val}
    {bs : List (BitVec 8)} (hd : q3.done rq = some bs) {x : Option (List Val)} {q2 : Req2St}
    (h : SendPost Q (q3.key rq) bs q3.resps x q2) : ProgPost Q q3 send3 (.u32 rq :: rest) x q2 := by
  refine ⟨?_, by rw [h.2, req3Next_send_resps, hd]⟩
  rcases h.1 with hx | hx
  · rw [hx]; simp [req3Ok]
  · cases x with
    | none => simp [req3Ok]
    | some l => simpa [req3Ok, hd] using hx

/-- A `send` that traps at once. -/
theorem progPost_trap (Q : QWeb) (q3 : Req3St) (a : List Val) {q2 : Req2St}
    (hR : q2.resps = q3.resps) : ProgPost Q q3 send3 a none q2 := by
  refine ⟨?_, by rw [req3Next_send_none, hR]⟩
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v <;> simp [req3Ok]

/-- The program of `send`. -/
theorem wp_send (Q : QWeb) (rounds : Nat) {s : Req3St} {q3 : Req3St} (hs : s = q3) (a : List Val)
    {q2 : Req2St} (hR : q2.resps = q3.resps) :
    Wp (req2Th Q) (sendB rounds s a) (ProgPost Q q3 send3 a) q2 := by
  subst hs
  rcases a with _ | ⟨v, rest⟩
  · exact progPost_trap Q s [] hR
  cases v
  case u32 rq =>
    cases hd : s.done rq with
    | none =>
      simp only [sendB, hd]
      exact progPost_trap Q s _ hR
    | some bs =>
      exact Wp.mono (fun x q h => progPost_send hd (hR ▸ h)) (wp_sendB rounds s hd q2)
  all_goals exact progPost_trap Q s _ hR

/-- **The program of an export call.** -/
theorem wp_prog (Q : QWeb) (rounds : Nat) {s : Req3St × Nat} {q3 : Req3St} (hs : s.1 = q3)
    (f : FnName) (a : List Val) {q2 : Req2St} (hR : q2.resps = q3.resps) :
    Wp (req2Th Q) (req3Prog rounds s f a) (ProgPost Q q3 f a) q2 := by
  unfold req3Prog
  by_cases h₁ : f = send3
  · subst h₁
    simpa using wp_send Q rounds hs a hR
  · by_cases h₂ : f = getStatus3
    · subst h₂
      simp only [ne_status3_send, ↓reduceIte]
      refine wp_call2 (f := respStatus) fun r hok => ?_
      exact ⟨(req3Ok_status Q hR a r).trans hok,
        by rw [req2Next_status, req3Next_resps _ ne_status3_send, hR]⟩
    · simp only [h₁, h₂, ↓reduceIte]
      exact ⟨req3Ok_other Q q3 h₁ h₂ a _, by rw [req3Next_resps _ h₁, hR]⟩

/-- **The invariant of `req3Over2`.** -/
theorem req3Over2_inv (Q : QWeb) (rounds : Nat) :
    WpInv (req3Over2 rounds) ({}, 0) (req2Th Q) (req3Th Q) JR3 where
  init := ⟨rfl, rfl⟩
  call := by
    intro s q2 q3 c hJ
    show Wp (req2Th Q) ((req3Prog rounds s c.1.1 c.2).bind _) _ q2
    rw [Wp.bind]
    refine Wp.mono (fun x q2' h => ?_) (wp_prog Q rounds hJ.1 c.1.1 c.2 hJ.2)
    refine ⟨req3Next q3 (.imp c.1.1 c.2 x), ?_, by rw [hJ.1], h.2⟩
    show (if req3Ok Q q3 (.imp c.1.1 c.2 x) = true then some _ else none) = _
    simp only [h.1, ↓reduceIte]

/-- **Outgoing request bodies, 0.3 over 0.2**: over every host of the 0.2 theory with outgoing
bodies, the composite is a model of the 0.3 one, for the same request-body web. -/
theorem req3Over2_model (Q : QWeb) (rounds : Nat) {Y : Sig.{0}} {η : Host Y req2Fns}
    (hη : (hostSat (req2Th Q).Accepts).holds η) :
    (hostSat (req3Th Q).Accepts).holds (link η (ofSBody (req3Over2 rounds) ({}, 0))) :=
  link_model (ag_of_wpInv (req3Over2_inv Q rounds)) hη

end Silmaril.Wasi.Versions.Net
