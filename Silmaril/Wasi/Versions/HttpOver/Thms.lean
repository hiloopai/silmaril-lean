module

public import Silmaril.Wasi.Versions.HttpOver.Defs
public import Silmaril.Wasi.Versions.Http3.Thms
public import Silmaril.Wasi.Versions.Net3.Over.Thms

@[expose] public section

/-!
# Outgoing HTTP across versions: theorems

PROVED (standard axioms):

* **(b) 0.3 over 0.2**: `http3Over2_sat`, **`http3Over2_model`**: for every web `W`, every
  number of rounds and every host of the 0.2 theory `httpTh W`, the composite is a model of the
  0.3 theory `httpTh3 W`. Invariant `JH3`: the two theory states agree on requests and responses.
* **(c) 0.2 over 0.3**: `http2Over3_sat`, **`http2Over3_model`**: for every web `W` and every
  host of `httpTh3 W`, the composite is a model of `httpTh W`. Invariant `JH2`.

Both are safety results over **every** host of the respective theory: `http3Over2` may trap
after `rounds` answers `none`, and both theories admit traps.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Next states -/

/-- A 0.2 setter call updates the list of authorities. -/
theorem httpNext_setAuth (q : HttpSt) (a : List Val) (r : Option (List Val)) :
    httpNext q (.imp setAuthority a r) = { q with auth := setUpd a r q.auth } := by
  unfold setUpd
  split
  · simp [httpNext, setAuthority]
  · unfold httpNext
    split <;> first
      | (rename_i h; obtain ⟨rfl, -⟩ := h; simp_all (config := {decide := true}))
      | rfl

/-- A 0.2 setter call updates the list of paths. -/
theorem httpNext_setPath (q : HttpSt) (a : List Val) (r : Option (List Val)) :
    httpNext q (.imp setPath a r) = { q with path := setUpd a r q.path } := by
  unfold setUpd
  split
  · simp [httpNext, setAuthority, setPath]
  · unfold httpNext
    split <;> first
      | (rename_i h; obtain ⟨rfl, -⟩ := h; simp_all (config := {decide := true}))
      | rfl

/-- A 0.3 setter call updates the list of authorities. -/
theorem http3Next_setAuth (q : Http3St) (a : List Val) (r : Option (List Val)) :
    http3Next q (.imp setAuth3 a r) = { q with auth := setUpd a r q.auth } := by
  unfold setUpd
  split
  · simp [http3Next, setAuth3]
  · unfold http3Next
    split <;> first
      | (rename_i h; obtain ⟨rfl, -⟩ := h; simp_all (config := {decide := true}))
      | rfl

/-- A 0.3 setter call updates the list of paths. -/
theorem http3Next_setPath (q : Http3St) (a : List Val) (r : Option (List Val)) :
    http3Next q (.imp setPath3 a r) = { q with path := setUpd a r q.path } := by
  unfold setUpd
  split
  · simp [http3Next, setAuth3, setPath3]
  · unfold http3Next
    split <;> first
      | (rename_i h; obtain ⟨rfl, -⟩ := h; simp_all (config := {decide := true}))
      | rfl

/-- `status` keeps the 0.2 state. -/
theorem httpNext_status (q : HttpSt) (a : List Val) (r : Option (List Val)) :
    httpNext q (.imp respStatus a r) = q := by
  unfold httpNext
  split <;> first
    | (rename_i h; obtain ⟨rfl, -⟩ := h; simp_all (config := {decide := true}))
    | simp_all

/-- `get-status-code` keeps the 0.3 state. -/
theorem http3Next_status (q : Http3St) (a : List Val) (r : Option (List Val)) :
    http3Next q (.imp getStatus3 a r) = q := by
  unfold http3Next
  split <;> first
    | (rename_i h; obtain ⟨rfl, -⟩ := h; simp_all (config := {decide := true}))
    | simp_all

/-! ## Checks -/

/-- Functions other than `get` and `status` pass the 0.2 check. -/
theorem httpOk_ne (W : Web) (q : HttpSt) {f : FnName} (h₁ : f ≠ futGet) (h₂ : f ≠ respStatus)
    (a : List Val) (r : Option (List Val)) : httpOk W q (.imp f a r) = true := by
  unfold httpOk
  split <;> simp_all

/-- Functions other than `send` and `get-status-code` pass the 0.3 check. -/
theorem http3Ok_ne (W : Web) (q : Http3St) {f : FnName} (h₁ : f ≠ send3) (h₂ : f ≠ getStatus3)
    (a : List Val) (r : Option (List Val)) : http3Ok W q (.imp f a r) = true := by
  unfold http3Ok
  split <;> simp_all

/-- The two `status` checks agree on states with the same responses. -/
theorem httpOk_status_eq (W : Web) {q2 : HttpSt} {q3 : Http3St} (h : q2.resps = q3.resps)
    (a : List Val) (r : Option (List Val)) :
    httpOk W q2 (.imp respStatus a r) = http3Ok W q3 (.imp getStatus3 a r) := by
  rcases a with _ | ⟨v, a⟩
  · rfl
  · cases v <;> simp [httpOk, http3Ok, h, respStatus, futGet, getStatus3, send3]; rfl

/-- A trap of `send` passes the 0.3 check. -/
theorem http3Ok_send_trap (W : Web) (q : Http3St) (a : List Val) :
    http3Ok W q (.imp send3 a none) = true := by
  rcases a with _ | ⟨v, a⟩
  · rfl
  · cases v <;> simp [http3Ok]

/-- A trap of `send` keeps the 0.3 state. -/
theorem http3Next_send_trap (q : Http3St) (a : List Val) : http3Next q (.imp send3 a none) = q := by
  unfold http3Next
  split <;> simp_all

/-- A trap keeps the 0.2 state. -/
theorem httpNext_none (q : HttpSt) (f : FnName) (a : List Val) : httpNext q (.imp f a none) = q := by
  unfold httpNext
  split <;> simp_all

/-- Functions other than the setters keep the requests of the 0.3 state. -/
theorem http3Next_keys (q : Http3St) {f : FnName} (h₁ : f ≠ setAuth3) (h₂ : f ≠ setPath3)
    (a : List Val) (r : Option (List Val)) :
    (http3Next q (.imp f a r)).auth = q.auth ∧ (http3Next q (.imp f a r)).path = q.path := by
  unfold http3Next
  split <;> simp_all; split <;> simp_all

/-- A trap of `send` is a step of the 0.3 theory. -/
theorem step3_send_trap (W : Web) (q : Http3St) (a : List Val) :
    (httpTh3 W).step q (.imp send3 a none) = some q := by
  have h := gated_step_of (i := {}) (n := http3Next) (q := q) (http3Ok_send_trap W q a)
  rwa [http3Next_send_trap] at h

/-! ## (b) 0.3 over 0.2 -/

/-- The answers `get` of a tied future may give, by the 0.2 check. -/
theorem getOk_cases {W : Web} {k : Val × Val} {r : Option (List Val)} (h : getOk W k r = true) :
    r = some [.variant 0 none] ∨ r = some [gotV] ∨
    (∃ rs s, W k.1 k.2 = .status s ∧
      r = some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.u32 rs))))))]) ∨
    (∃ c p, W k.1 k.2 = .error c ∧
      r = some [.variant 1 (some (.variant 0 (some (.variant 1 (some (.variant c p))))))]) := by
  unfold getOk at h
  split at h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · next x =>
    unfold outcomeOk at h
    split at h
    · next s rs heq => exact Or.inr (Or.inr (Or.inl ⟨rs, s, heq, rfl⟩))
    · next c c' p heq =>
      have hc : c' = c := by simpa using h
      exact Or.inr (Or.inr (Or.inr ⟨c, p, heq, by rw [hc]⟩))
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The 0.2 check of `get` on a tied future. -/
theorem httpOk_get {W : Web} {q : HttpSt} {fu : BitVec 32} {k : Val × Val}
    (hl : lookup fu q.futs = some k) (r : Option (List Val)) :
    httpOk W q (.imp futGet [.u32 fu] r) = getOk W k r := by
  simp [httpOk, hl]

/-- A pending answer keeps the 0.2 state. -/
theorem httpNext_pending (q : HttpSt) (fu : BitVec 32) :
    httpNext q (.imp futGet [.u32 fu] (some [.variant 0 none])) = q := by
  simp [httpNext]

/-- **A decided `get`** gives a `send` answer accepted by the 0.3 theory, and keeps `JH3`. -/
theorem sendOf2_step (W : Web) {q2 : HttpSt} {q3 : Http3St} (hJ : JH3 () q2 q3) (r : BitVec 32)
    (rest : List Val) {fu : BitVec 32} (hl : lookup fu q2.futs = some (q3.key r))
    {r₂ : Option (List Val)} (hok : getOk W (q3.key r) r₂ = true) (hp : isPending r₂ = false) :
    ∃ q3', (httpTh3 W).step q3 (.imp send3 (.u32 r :: rest) (sendOf2 r₂)) = some q3' ∧
      JH3 () (httpNext q2 (.imp futGet [.u32 fu] r₂)) q3' := by
  obtain ⟨ha, hpa, hr⟩ := hJ
  rcases getOk_cases hok with rfl | rfl | ⟨rs, s, hW, rfl⟩ | ⟨c, p, hW, rfl⟩
  · simp [isPending] at hp
  · have hn : httpNext q2 (.imp futGet [.u32 fu] (some [gotV])) = q2 := by simp [httpNext, gotV]
    exact ⟨q3, step3_send_trap W q3 _, hn ▸ ⟨ha, hpa, hr⟩⟩
  · refine ⟨{ q3 with resps := (rs, q3.key r) :: q3.resps }, gated_step_iff.2 ⟨?_, ?_⟩, ?_⟩
    · simp [http3Ok, sendOf2, sendOk, hW, okV]
    · simp [http3Next, sendOf2, okV]
    · simp [JH3, httpNext, hl, ha, hpa, hr]
  · refine ⟨q3, gated_step_iff.2 ⟨?_, ?_⟩, ?_⟩
    · simp [http3Ok, sendOf2, sendOk, hW, errV]
    · simp [http3Next, sendOf2, errV]
    · have hn : httpNext q2 (.imp futGet [.u32 fu]
          (some [.variant 1 (some (.variant 0 (some (.variant 1 (some (.variant c p))))))])) = q2 := by
        simp [httpNext]
      exact hn ▸ ⟨ha, hpa, hr⟩

/-- **Polling a tied future** returns a `send` answer accepted by the 0.3 theory, or traps. -/
theorem wp_pollGet (W : Web) (r : BitVec 32) (rest : List Val) (q3 : Http3St) (fu : BitVec 32) :
    ∀ (k : Nat) (q2 : HttpSt), JH3 () q2 q3 → lookup fu q2.futs = some (q3.key r) →
      Wp (httpTh W) (pollGet k fu)
        (fun x q2' => ∃ q3', (httpTh3 W).step q3 (.imp send3 (.u32 r :: rest) x.2) = some q3' ∧
          JH3 x.1 q2' q3') q2
  | 0, _, hJ, _ => ⟨q3, step3_send_trap W q3 _, hJ⟩
  | k + 1, q2, hJ, hl => fun r₂ q2' hstep => by
    obtain ⟨hok, hq⟩ := gated_step_iff.1 hstep
    change httpOk W q2 (.imp futGet [.u32 fu] r₂) = true at hok
    change q2' = httpNext q2 (.imp futGet [.u32 fu] r₂) at hq
    rw [httpOk_get hl] at hok
    show Wp (httpTh W) (if isPending r₂ = true then pollGet k fu else .pure ((), sendOf2 r₂)) _ q2'
    by_cases hp : isPending r₂ = true
    · have hr₂ : r₂ = some [.variant 0 none] := by
        unfold isPending at hp; split at hp <;> simp_all
      have hq' : q2' = q2 := by rw [hq, hr₂, httpNext_pending]
      simp only [hp, ↓reduceIte]
      exact hq' ▸ wp_pollGet W r rest q3 fu k q2 hJ hl
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact hq ▸ sendOf2_step W hJ r rest hl hok (by simpa using hp)

/-- The 0.2 state after `handle(r, none)` answered `ok(f)`. -/
theorem httpNext_handle (q : HttpSt) (r fu : BitVec 32) :
    httpNext q (.imp httpHandle [.u32 r, noneV] (some [.variant 0 (some (.u32 fu))])) =
      { q with futs := (fu, q.key r) :: q.futs } := by
  simp [httpNext, HttpSt.key]

/-- **The program of `send`** returns an answer accepted by the 0.3 theory, keeping `JH3`. -/
theorem wp_send3 (W : Web) (rounds : Nat) (a : List Val) (q2 : HttpSt) (q3 : Http3St)
    (hJ : JH3 () q2 q3) :
    Wp (httpTh W) (send3Prog rounds a)
      (fun x q2' => ∃ q3', (httpTh3 W).step q3 (.imp send3 a x.2) = some q3' ∧ JH3 x.1 q2' q3')
      q2 := by
  unfold send3Prog
  split
  · next r rest =>
    intro r₁ q2' h₁
    have hq : q2' = httpNext q2 (.imp httpHandle [.u32 r, noneV] r₁) := (gated_step_iff.1 h₁).2
    beta_reduce
    split
    · next fu =>
      rw [hq, httpNext_handle]
      have hk : q2.key r = q3.key r := by simp [HttpSt.key, Http3St.key, hJ.1, hJ.2.1]
      exact wp_pollGet W r rest q3 fu rounds _ hJ (by simp [hk, lookup])
    · next hne =>
      have hq' : q2' = q2 := by
        rw [hq]; unfold httpNext
        split <;> first
          | (rename_i h; obtain ⟨rfl, -⟩ := h; simp_all (config := {decide := true}))
          | simp_all
      exact ⟨q3, step3_send_trap W q3 _, hq' ▸ hJ⟩
  · exact ⟨q3, step3_send_trap W q3 _, hJ⟩

/-- A forwarded setter keeps `JH3`. -/
theorem setter3_step (W : Web) {q2 : HttpSt} {q3 : Http3St} (hJ : JH3 () q2 q3) (a : List Val)
    (r : Option (List Val)) :
    (∃ q3', (httpTh3 W).step q3 (.imp setAuth3 a r) = some q3' ∧
      JH3 () (httpNext q2 (.imp setAuthority a r)) q3') ∧
    (∃ q3', (httpTh3 W).step q3 (.imp setPath3 a r) = some q3' ∧
      JH3 () (httpNext q2 (.imp setPath a r)) q3') := by
  obtain ⟨ha, hp, hr⟩ := hJ
  refine ⟨⟨_, gated_step_of (http3Ok_ne W q3 (by decide) (by decide) a r), ?_⟩,
    ⟨_, gated_step_of (http3Ok_ne W q3 (by decide) (by decide) a r), ?_⟩⟩
  · rw [httpNext_setAuth, http3Next_setAuth]; exact ⟨by simp [ha], hp, hr⟩
  · rw [httpNext_setPath, http3Next_setPath]; exact ⟨ha, by simp [hp], hr⟩

/-- A forwarded `status` keeps `JH3`. -/
theorem status3_step (W : Web) {q2 : HttpSt} {q3 : Http3St} (hJ : JH3 () q2 q3) (a : List Val)
    {r : Option (List Val)} (hok : httpOk W q2 (.imp respStatus a r) = true) :
    ∃ q3', (httpTh3 W).step q3 (.imp getStatus3 a r) = some q3' ∧
      JH3 () (httpNext q2 (.imp respStatus a r)) q3' := by
  refine ⟨q3, ?_, by rw [httpNext_status]; exact hJ⟩
  have h := gated_step_of (i := {}) (n := http3Next) (q := q3)
    (show http3Ok W q3 (.imp getStatus3 a r) = true by rwa [← httpOk_status_eq W hJ.2.2])
  rwa [http3Next_status] at h

/-- The invariant of `http3Over2`. -/
theorem http3Over2_inv (W : Web) (rounds : Nat) :
    WpInv (http3Over2 rounds) () (httpTh W) (httpTh3 W) JH3 where
  init := ⟨rfl, rfl, rfl⟩
  call := by
    intro _ q2 q3 q hJ
    by_cases h₁ : q.1.1 = setAuth3
    · simp only [http3Over2, h₁, ↓reduceIte]
      intro r q2' hs
      rw [(gated_step_iff.1 hs).2]
      exact (setter3_step W hJ q.2 r).1
    by_cases h₂ : q.1.1 = setPath3
    · simp only [http3Over2, h₂, ↓reduceIte]
      intro r q2' hs
      rw [(gated_step_iff.1 hs).2]
      exact (setter3_step W hJ q.2 r).2
    by_cases h₃ : q.1.1 = send3
    · simp only [http3Over2, h₃, ↓reduceIte]
      exact wp_send3 W rounds q.2 q2 q3 hJ
    have h₄ : q.1.1 = getStatus3 := by
      have hm := q.1.2
      simp only [http3Fns_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      exact ((hm.resolve_left h₃).resolve_left h₁).resolve_left h₂
    simp only [http3Over2, h₄]
    intro r q2' hs
    obtain ⟨hok, hq⟩ := gated_step_iff.1 hs
    rw [hq]
    exact status3_step W hJ q.2 hok

/-- **The component guarantee of outgoing HTTP 0.3 over 0.2.** -/
theorem http3Over2_sat (W : Web) (rounds : Nat) :
    (agP (httpTh W) (retG (httpTh3 W))).holds (ofSBody (http3Over2 rounds) ()) :=
  ag_of_wpInv (http3Over2_inv W rounds)

/-- **Outgoing HTTP 0.3 over 0.2**: over every host of the 0.2 theory of the web `W`, the
composite is a model of the 0.3 theory of the same web. -/
theorem http3Over2_model (W : Web) (rounds : Nat) {Y : Sig.{0}} {η : Host Y httpImports}
    (hη : (hostSat (httpTh W).Accepts).holds η) :
    (hostSat (httpTh3 W).Accepts).holds (link η (ofSBody (http3Over2 rounds) ())) :=
  link_model (http3Over2_sat W rounds) hη

/-! ## (c) 0.2 over 0.3 -/

/-- Functions other than the setters keep the requests of the 0.2 state. -/
theorem httpNext_keys (q : HttpSt) {f : FnName} (h₁ : f ≠ setAuthority) (h₂ : f ≠ setPath)
    (a : List Val) (r : Option (List Val)) :
    (httpNext q (.imp f a r)).auth = q.auth ∧ (httpNext q (.imp f a r)).path = q.path := by
  unfold httpNext
  split <;> (try split) <;> (try split) <;> simp_all

/-- `JH2` reads only the requests of the 0.3 state. -/
theorem jh2_keys {W : Web} {st : HSt} {q3 q3' : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (ha : q3'.auth = q3.auth) (hp : q3'.path = q3.path) : JH2 W st q3' q2 :=
  ⟨hJ.1.trans ha.symm, hJ.2.1.trans hp.symm, hJ.2.2⟩

/-- A step of the 0.2 theory on a function it does not check or record. -/
theorem step2_quiet {W : Web} {q : HttpSt} {f : FnName} {a : List Val} {r : Option (List Val)}
    (hok : httpOk W q (.imp f a r) = true) (hn : httpNext q (.imp f a r) = q) :
    (httpTh W).step q (.imp f a r) = some q := by
  have h := gated_step_of (i := HttpSt.init) (n := httpNext) hok
  rwa [hn] at h

/-- A `send` answer `ok(rs)` accepted by the 0.3 check: the web answers a status. -/
theorem sendOk_okStatus {o : HttpOutcome} {rs : BitVec 32}
    (h : sendOk o (some [.variant 0 (some (.u32 rs))]) = true) : ∃ s, o = .status s := by
  cases o with
  | status s => exact ⟨s, rfl⟩
  | error k => simp [sendOk] at h

/-- A `send` answer `error(k)` accepted by the 0.3 check: the web fails with `k`. -/
theorem sendOk_err {o : HttpOutcome} {k : Nat} {p : Option Val}
    (h : sendOk o (some [.variant 1 (some (.variant k p))]) = true) : o = .error k := by
  cases o with
  | status s => simp [sendOk] at h
  | error k' => simp [sendOk] at h; rw [h]

/-- The 0.2 state after `handle` answered `ok(f)`. -/
theorem httpNext_handleOk (q : HttpSt) (r : BitVec 32) (rest : List Val) (fu : BitVec 32) :
    httpNext q (.imp httpHandle (.u32 r :: rest) (some [okV (some (.u32 fu))])) =
      { q with futs := (fu, q.key r) :: q.futs } := by
  simp [httpNext, HttpSt.key, okV]

/-- **Storing a result** that matches the web keeps `JH2`. -/
theorem storeFut_step (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (r : BitVec 32) (rest : List Val) (x : Val × BitVec 16) (hx : PendOk W (q3.key r) x) :
    ∃ q2', (httpTh W).step q2 (.imp httpHandle (.u32 r :: rest) (storeFut st x).2) = some q2' ∧
      JH2 W (storeFut st x).1 q3 q2' := by
  obtain ⟨ha, hp, hpend, hresp⟩ := hJ
  have hk : q2.key r = q3.key r := by simp [HttpSt.key, Http3St.key, ha, hp]
  refine ⟨_, gated_step_of (httpOk_ne W q2 (by decide) (by decide) _ _), ?_⟩
  simp only [storeFut]
  rw [httpNext_handleOk]
  refine ⟨ha, hp, fun fu y hy => ?_, hresp⟩
  by_cases hf : fu = BitVec.ofNat 32 st.next
  · subst hf
    simp only [lookup_cons_self, Option.some.injEq] at hy
    exact ⟨q2.key r, lookup_cons_self _ _ _, hk ▸ hy ▸ hx⟩
  · rw [lookup_cons_ne hf] at hy ⊢
    exact hpend fu y hy

/-- The program after `send` answered `ok(rs)` keeps `JH2`. -/
theorem wp_afterSend (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (r rs : BitVec 32) (rest : List Val) {s₀ : BitVec 16}
    (hW : W (q3.key r).1 (q3.key r).2 = .status s₀) :
    Wp (httpTh3 W) (afterSend st rs)
      (fun x q3' => ∃ q2', (httpTh W).step q2 (.imp httpHandle (.u32 r :: rest) x.2) = some q2' ∧
        JH2 W x.1 q3' q2') { q3 with resps := (rs, q3.key r) :: q3.resps } := by
  intro r₂ q3' h₂
  obtain ⟨hok, hq⟩ := gated_step_iff.1 h₂
  change http3Ok W _ (.imp getStatus3 [.u32 rs] r₂) = true at hok
  change q3' = http3Next _ (.imp getStatus3 [.u32 rs] r₂) at hq
  rw [http3Next_status] at hq
  subst hq
  have hJ' := jh2_keys (q3' := { q3 with resps := (rs, q3.key r) :: q3.resps }) hJ rfl rfl
  beta_reduce
  split
  · next s =>
    have hs : s = s₀ := by simpa [http3Ok, lookup, statusOk, hW, getStatus3, send3] using hok
    refine storeFut_step W hJ' r rest _ ?_
    show PendOk W (q3.key r) _
    exact ⟨by simp [outcomeOk, hW, okV], fun _ _ => by rw [hW, hs]⟩
  · exact ⟨q2, step2_quiet (httpOk_ne W q2 (by decide) (by decide) _ _) (httpNext_none _ _ _), hJ'⟩

/-- `send` answered `error(k)`: storing the error keeps `JH2`. -/
theorem handleErr_step (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (r : BitVec 32) (rest : List Val) (k : Nat) (p : Option Val)
    (hok : http3Ok W q3 (.imp send3 [.u32 r] (some [.variant 1 (some (.variant k p))])) = true) :
    ∃ q2', (httpTh W).step q2
        (.imp httpHandle (.u32 r :: rest) (storeFut st (errV (some (.variant k p)), 0)).2) = some q2' ∧
      JH2 W (storeFut st (errV (some (.variant k p)), 0)).1
        (http3Next q3 (.imp send3 [.u32 r] (some [.variant 1 (some (.variant k p))]))) q2' := by
  have hs : sendOk (W (q3.key r).1 (q3.key r).2) (some [.variant 1 (some (.variant k p))]) = true := by
    simpa [http3Ok] using hok
  have hW : W (q3.key r).1 (q3.key r).2 = .error k := sendOk_err hs
  have hn : http3Next q3 (.imp send3 [.u32 r] (some [.variant 1 (some (.variant k p))])) = q3 := by
    simp [http3Next]
  rw [hn]
  exact storeFut_step W hJ r rest _ ⟨by simp [outcomeOk, hW, errV], fun _ h => by simp [errV] at h⟩

/-- `send` answered `ok(rs)`: the program reading the status keeps `JH2`. -/
theorem handleOk_wp (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (r rs : BitVec 32) (rest : List Val)
    (hok : http3Ok W q3 (.imp send3 [.u32 r] (some [.variant 0 (some (.u32 rs))])) = true) :
    Wp (httpTh3 W) (afterSend st rs)
      (fun x q3' => ∃ q2', (httpTh W).step q2 (.imp httpHandle (.u32 r :: rest) x.2) = some q2' ∧
        JH2 W x.1 q3' q2')
      (http3Next q3 (.imp send3 [.u32 r] (some [.variant 0 (some (.u32 rs))]))) := by
  have hs : sendOk (W (q3.key r).1 (q3.key r).2) (some [.variant 0 (some (.u32 rs))]) = true := by
    simpa [http3Ok] using hok
  obtain ⟨s₀, hW⟩ := sendOk_okStatus hs
  have hq : http3Next q3 (.imp send3 [.u32 r] (some [.variant 0 (some (.u32 rs))])) =
      { q3 with resps := (rs, q3.key r) :: q3.resps } := by simp [http3Next]
  rw [hq]
  exact wp_afterSend W hJ r rs rest hW

/-- **The program of `handle`** keeps `JH2` and answers as the 0.2 theory allows. -/
theorem wp_handle (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (a : List Val) :
    Wp (httpTh3 W) (handleProg st a)
      (fun x q3' => ∃ q2', (httpTh W).step q2 (.imp httpHandle a x.2) = some q2' ∧ JH2 W x.1 q3' q2')
      q3 := by
  have htrap : ∀ q3', q3'.auth = q3.auth → q3'.path = q3.path →
      ∃ q2', (httpTh W).step q2 (.imp httpHandle a none) = some q2' ∧ JH2 W st q3' q2' :=
    fun _ ha hp => ⟨q2, step2_quiet (httpOk_ne W q2 (by decide) (by decide) _ _)
      (httpNext_none _ _ _), jh2_keys hJ ha hp⟩
  unfold handleProg
  split
  · next r rest =>
    intro r₁ q3' h₁
    obtain ⟨hok, hq⟩ := gated_step_iff.1 h₁
    change http3Ok W q3 (.imp send3 [.u32 r] r₁) = true at hok
    change q3' = http3Next q3 (.imp send3 [.u32 r] r₁) at hq
    subst hq
    beta_reduce
    split
    · next rs => exact handleOk_wp W hJ r rs rest hok
    · next k p => exact handleErr_step W hJ r rest k p hok
    · exact htrap _ (http3Next_keys q3 (by decide) (by decide) _ _).1
        (http3Next_keys q3 (by decide) (by decide) _ _).2
  · exact htrap q3 rfl rfl

/-- The answers `get` may retrieve: the stored inner results matching the web. -/
theorem outcomeOk_cases {o : HttpOutcome} {x : Val} (h : outcomeOk o x = true) :
    (∃ rs, x = .variant 0 (some (.u32 rs))) ∨ (∃ c p, x = .variant 1 (some (.variant c p))) := by
  unfold outcomeOk at h
  split at h
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩
  · exact absurd h (by simp)

/-- `some(err)` keeps the 0.2 state and passes its check. -/
theorem got_step (W : Web) (q : HttpSt) (a : List Val) :
    (httpTh W).step q (.imp futGet a (some [gotV])) = some q := by
  refine step2_quiet ?_ (by unfold httpNext; split <;> simp_all [gotV])
  rcases a with _ | ⟨v, a⟩
  · rfl
  · cases v <;> simp [httpOk, getOk, gotV]
    split <;> rfl

/-- **Retrieving a stored result** keeps `JH2`. -/
theorem getStored_step (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (fu : BitVec 32) (rest : List Val) {x : Val} {s : BitVec 16}
    (hx : lookup fu st.pend = some (some (x, s))) :
    ∃ q2', (httpTh W).step q2
        (.imp futGet (.u32 fu :: rest) (some [.variant 1 (some (.variant 0 (some x)))])) = some q2' ∧
      JH2 W { st with pend := (fu, none) :: st.pend, stat := recStat x s st.stat } q3 q2' := by
  obtain ⟨ha, hp, hpend, hresp⟩ := hJ
  obtain ⟨k, hk, hok, hst⟩ := hpend fu (x, s) hx
  have hchk : httpOk W q2
      (.imp futGet (.u32 fu :: rest) (some [.variant 1 (some (.variant 0 (some x)))])) = true := by
    simpa [httpOk, hk, getOk] using hok
  have hpend' : ∀ fu' y, lookup fu' ((fu, none) :: st.pend) = some (some y) →
      ∃ k, lookup fu' q2.futs = some k ∧ PendOk W k y := by
    intro fu' y hy
    by_cases hf : fu' = fu
    · subst hf; simp [lookup_cons_self] at hy
    · rw [lookup_cons_ne hf] at hy; exact hpend fu' y hy
  rcases outcomeOk_cases hok with ⟨rs, rfl⟩ | ⟨c, p, rfl⟩
  · refine ⟨{ q2 with resps := (rs, k) :: q2.resps },
      gated_step_iff.2 ⟨hchk, by simp [httpNext, hk]⟩, ha, hp, hpend', fun rs' k' hl => ?_⟩
    by_cases hr : rs' = rs
    · subst hr
      simp only [lookup_cons_self, Option.some.injEq] at hl
      subst hl
      exact ⟨s, by simp [recStat, lookup_cons_self], by simp [statusOk, hst rs' rfl]⟩
    · rw [lookup_cons_ne hr] at hl
      obtain ⟨s', hs', hok'⟩ := hresp rs' k' hl
      exact ⟨s', by simp only [recStat]; rw [lookup_cons_ne hr]; exact hs', hok'⟩
  · exact ⟨q2, step2_quiet hchk (by simp [httpNext]), ha, hp, hpend', by simpa [recStat] using hresp⟩

/-- **`get` over 0.3** keeps `JH2`. -/
theorem getRes_step (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (a : List Val) :
    ∃ q2', (httpTh W).step q2 (.imp futGet a (getRes st a).2) = some q2' ∧
      JH2 W (getRes st a).1 q3 q2' := by
  unfold getRes
  split
  · next fu rest =>
    split
    · next x s hx => exact getStored_step W hJ fu rest hx
    · exact ⟨q2, got_step W q2 _, hJ⟩
  · exact ⟨q2, got_step W q2 _, hJ⟩

/-- **`status` over 0.3** keeps `JH2`. -/
theorem statusRes_step (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (a : List Val) :
    ∃ q2', (httpTh W).step q2 (.imp respStatus a (statusRes st a).2) = some q2' ∧
      JH2 W (statusRes st a).1 q3 q2' := by
  unfold statusRes
  split
  · next rs rest =>
    refine ⟨q2, step2_quiet ?_ (httpNext_status _ _ _), hJ⟩
    cases hl : lookup rs q2.resps with
    | none => simp [httpOk, hl, respStatus, futGet]
    | some k =>
      obtain ⟨s, hs, hok⟩ := hJ.2.2.2 rs k hl
      simpa [httpOk, hl, hs, respStatus, futGet] using hok
  · next hne =>
    refine ⟨q2, step2_quiet ?_ (httpNext_status _ _ _), hJ⟩
    unfold httpOk
    split <;> simp_all

/-- A forwarded setter keeps `JH2`. -/
theorem setter2_step (W : Web) {st : HSt} {q3 : Http3St} {q2 : HttpSt} (hJ : JH2 W st q3 q2)
    (a : List Val) (r : Option (List Val)) :
    (∃ q2', (httpTh W).step q2 (.imp setAuthority a r) = some q2' ∧
      JH2 W st (http3Next q3 (.imp setAuth3 a r)) q2') ∧
    (∃ q2', (httpTh W).step q2 (.imp setPath a r) = some q2' ∧
      JH2 W st (http3Next q3 (.imp setPath3 a r)) q2') := by
  obtain ⟨ha, hp, hpend, hresp⟩ := hJ
  refine ⟨⟨_, gated_step_of (httpOk_ne W q2 (by decide) (by decide) a r), ?_⟩,
    ⟨_, gated_step_of (httpOk_ne W q2 (by decide) (by decide) a r), ?_⟩⟩
  · rw [httpNext_setAuth, http3Next_setAuth]; exact ⟨by simp [ha], hp, hpend, hresp⟩
  · rw [httpNext_setPath, http3Next_setPath]; exact ⟨ha, by simp [hp], hpend, hresp⟩

/-- The invariant of `http2Over3`. -/
theorem http2Over3_inv (W : Web) : WpInv http2Over3 {} (httpTh3 W) (httpTh W) (JH2 W) where
  init := ⟨rfl, rfl, fun _ _ h => by simp [lookup] at h,
    fun _ _ h => by simp [lookup, httpTh, gated, HttpSt.init] at h⟩
  call := by
    intro st q3 q2 q hJ
    by_cases h₁ : q.1.1 = setAuthority
    · simp only [http2Over3, h₁, ↓reduceIte]
      intro r q3' hs
      rw [(gated_step_iff.1 hs).2]
      exact (setter2_step W hJ q.2 r).1
    by_cases h₂ : q.1.1 = setPath
    · simp only [http2Over3, h₂, ↓reduceIte]
      intro r q3' hs
      rw [(gated_step_iff.1 hs).2]
      exact (setter2_step W hJ q.2 r).2
    by_cases h₃ : q.1.1 = httpHandle
    · simp only [http2Over3, h₃, ↓reduceIte]
      exact wp_handle W hJ q.2
    by_cases h₄ : q.1.1 = futGet
    · simp only [http2Over3, h₄, ↓reduceIte]
      exact getRes_step W hJ q.2
    have h₅ : q.1.1 = respStatus := by
      have hm := q.1.2
      simp only [httpImports_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      exact (((hm.resolve_left h₃).resolve_left h₁).resolve_left h₂).resolve_left h₄
    simp only [http2Over3, h₅]
    exact statusRes_step W hJ q.2

/-- **The component guarantee of outgoing HTTP 0.2 over 0.3.** -/
theorem http2Over3_sat (W : Web) :
    (agP (httpTh3 W) (retG (httpTh W))).holds (ofSBody http2Over3 {}) :=
  ag_of_wpInv (http2Over3_inv W)

/-- **Outgoing HTTP 0.2 over 0.3**: over every host of the 0.3 theory of the web `W`, the
composite is a model of the 0.2 theory of the same web. -/
theorem http2Over3_model (W : Web) {Y : Sig.{0}} {η : Host Y http3Fns}
    (hη : (hostSat (httpTh3 W).Accepts).holds η) :
    (hostSat (httpTh W).Accepts).holds (link η (ofSBody http2Over3 {})) :=
  link_model (http2Over3_sat W) hη

end Silmaril.Wasi.Versions.Net
