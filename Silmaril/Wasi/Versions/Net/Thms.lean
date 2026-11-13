module

public import Silmaril.Wasi.Versions.Net.Defs
public import Silmaril.Wasi.Versions.Stateful.Thms
public import Silmaril.Wasi.Theory.Thms

@[expose] public section

/-!
# WASI 0.2 sockets and http are not implementable over preview1

PROVED. The 0.2 TCP connect theory `tcpTh N` and the outgoing HTTP theory `httpTh W` of
`Silmaril.Wasi.Versions.Net` require observations of a network (`N`) or a web (`W`) that no
preview1 host model determines:

* `not_decides`: two gated theories with no common decisive answer accept no trace with a
  decisive event; `tcp_disjoint`, `http_disjoint` for `netUp`/`netDown`, `webUp`/`webDown`.
* **`tcp_not_both`**, **`http_not_both`**: for *any* host `η` of *any* import world and any
  component `σ`, if `link η σ` ever decides a connect (a request), it is not a model of the
  theory of both networks (webs). A host of the imports does not depend on the network.
* **`no_tcp_over_p1`**, **`no_http_over_p1`**: no component importing preview1 implements the
  0.2 theory over preview1 (correct over every preview1 host model, for every network) and
  decides a connect (a request) over some preview1 host model.
* `no_tcp_over_p1_ag`, `no_http_over_p1_ag`: the same for the component-level sentences
  `agP P1.th (retG (tcpTh N))` of `Silmaril.Wasi.Versions.Stateful`.
* `no_tcp_sys`, `no_http_sys`: for systems `⟨obs, net, web⟩` whose preview1 host depends only on
  `obs`, the systems `⟨o, netUp, _⟩` and `⟨o, netDown, _⟩` agree on every preview1 observation
  and a correct composite cannot decide a connect.
* The theories are satisfiable: `tcpImpl_sat`, `httpImpl_sat` (concrete hosts per network/web).
* `p1_sock_fns`: the preview1 functions named `sock_*` are exactly `sock_accept`, `sock_recv`,
  `sock_send`, `sock_shutdown` (from the witx); none takes an address.

Responsiveness (`TcpResponsive`) is necessary: a component that never returns satisfies every
safety theory vacuously.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

variable {S : Type} {init : S} {next : S → WEv → S}

/-! ## Gated protocols -/

/-- The run of a gated protocol: the state is the fold of `next`, and every event was checked. -/
theorem gated_run {ok : S → WEv → Bool} : ∀ {q : S} {t : List WEv} {q' : S},
    (gated init next ok).run q t = some q' →
      q' = t.foldl next q ∧ ∀ u e v, t = u ++ e :: v → ok (u.foldl next q) e = true
  | q, [], q', h => ⟨(Option.some.inj h).symm, fun u e v huv => absurd huv.symm (by simp)⟩
  | q, x :: t, q', h => by
    have hx : ok q x = true := by
      by_contra hn
      simp [Protocol.run, gated, hn] at h
    have h' : (gated init next ok).run (next q x) t = some q' := by
      simpa [Protocol.run, gated, hx] using h
    obtain ⟨hq', hok⟩ := gated_run h'
    refine ⟨hq', fun u e v huv => ?_⟩
    cases u with
    | nil =>
      obtain ⟨rfl, -⟩ := List.cons.inj huv
      exact hx
    | cons y u =>
      obtain ⟨rfl, ht⟩ := List.cons.inj huv
      exact hok u e v ht

/-- Every event of an accepted trace was checked in the state before it. -/
theorem gated_ok {ok : S → WEv → Bool} {t : List WEv} (h : (gated init next ok).Accepts t) :
    ∀ u e v, t = u ++ e :: v → ok (u.foldl next init) e = true := by
  obtain ⟨q, hq⟩ := (Protocol.accepts_iff_exists _ _).1 h
  exact (gated_run hq).2

/-- **No common decisive answer, no decisive event**: a trace accepted by two gated theories
with the same state and no common decisive answer has no decisive event. -/
theorem not_decides {ok₁ ok₂ : S → WEv → Bool} {D : S → WEv → Prop}
    (hD : ∀ q e, D q e → ok₁ q e = true → ok₂ q e = false) {t : List WEv}
    (h₁ : (gated init next ok₁).Accepts t) (h₂ : (gated init next ok₂).Accepts t) :
    ¬ Decides init next D t := by
  rintro ⟨u, e, v, rfl, hd⟩
  have h := hD _ _ hd (gated_ok h₁ u e v rfl)
  rw [gated_ok h₂ u e v rfl] at h
  exact Bool.noConfusion h

/-- A concrete host whose every answer passes the check is a model of a gated theory. -/
theorem gated_follows {ok : S → WEv → Bool} {impl : Impl}
    (hans : ∀ p f a, ok (p.foldl next init) (.imp f a (impl p f a)) = true)
    (hother : ∀ q e, e.isImp = false → ok q e = true) {t : List WEv} (ht : Follows impl t) :
    (gated init next ok).Accepts t := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t e ih =>
    have ht' : Follows impl t := (prefixClosed_follows impl).2 (List.prefix_append t [e]) ht
    obtain ⟨q, hq⟩ := (Protocol.accepts_iff_exists _ _).1 (ih ht')
    have hqe : q = t.foldl next init := (gated_run hq).1
    have hok : ok q e = true := by
      cases e with
      | imp f a r =>
        have hr : r = impl t f a := ht t f a r (List.prefix_refl _)
        rw [hr, hqe]
        exact hans t f a
      | req f a => exact hother _ _ rfl
      | call f a => exact hother _ _ rfl
      | ret f a r => exact hother _ _ rfl
    refine (Protocol.accepts_iff_exists _ _).2 ⟨next q e, ?_⟩
    rw [Protocol.run_concat, hq]
    simp [gated, hok]

/-! ## TCP -/

/-- The tag of an accepted `finish-connect` answer: `ok` when accepted, `error` otherwise. -/
theorem connectOk_tag {o : Option Nat} {r : Option (List Val)} (h : connectOk o r = true) :
    resTag r = some (if o.isSome then 1 else 0) := by
  unfold connectOk at h
  split at h <;> simp_all [resTag]

/-- `netUp` and `netDown` admit no common decisive answer. -/
theorem tcp_disjoint (q : TcpSt) (e : WEv) (hd : tcpDecisive q e) (h₁ : tcpOk netUp q e = true) :
    tcpOk netDown q e = false := by
  obtain ⟨s, a, r, rfl, hs, hw⟩ := hd
  obtain ⟨addr, hl⟩ := Option.isSome_iff_exists.1 hs
  simp only [tcpOk, ite_true, hl, hw, Bool.false_or] at h₁ ⊢
  have t₁ := connectOk_tag h₁
  cases h₂ : connectOk (netDown addr) r with
  | false => rfl
  | true =>
    have t₂ := connectOk_tag h₂
    rw [t₁] at t₂
    simp [netUp, netDown] at t₂

/-- **Two networks, one host**: if the composite ever decides a connect, it is not a model of
the TCP theories of both `netUp` and `netDown`. -/
theorem tcp_not_both {Y : Sig.{0}} {I X : Set FnName} {η : Host Y I}
    {σ : Strategy (nsig I) (nsig X)} (hresp : ∃ p ∈ link η σ, TcpDecides (htrace p))
    (hUp : (hostSat (tcpTh netUp).Accepts).holds (link η σ)) :
    ¬ (hostSat (tcpTh netDown).Accepts).holds (link η σ) := fun hDown => by
  obtain ⟨p, hp, hd⟩ := hresp
  exact not_decides (ok₁ := tcpOk netUp) (ok₂ := tcpOk netDown) tcp_disjoint (hUp p hp)
    (hDown p hp) hd

/-- **TCP connect is not implementable over preview1.** -/
theorem no_tcp_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (TcpOverP1 σ ∧ TcpResponsive σ) := by
  rintro ⟨hσ, Y, η, hη, hresp⟩
  exact tcp_not_both hresp (hσ netUp Y η hη) (hσ netDown Y η hη)

/-- The same for the component-level sentences. -/
theorem no_tcp_over_p1_ag {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ ((∀ N, (agP P1.th (retG (tcpTh N))).holds σ) ∧
      ∃ s ∈ σ, P1.th.Accepts (hostView (wtrace s)) ∧ TcpDecides (retAsImp (wtrace s))) := by
  rintro ⟨hσ, s, hs, hA, hd⟩
  exact not_decides (ok₁ := tcpOk netUp) (ok₂ := tcpOk netDown) tcp_disjoint
    ((accepts_retG _ _).1 (hσ netUp s hs hA)) ((accepts_retG _ _).1 (hσ netDown s hs hA)) hd

/-- **Systems that agree on every preview1 observation**: if the preview1 host of a system
depends only on what preview1 observes, a composite correct for every system decides no
connect. -/
theorem no_tcp_sys {O : Type} {Y : Sig.{0}} {X : Set FnName} (p1 : O → Host Y P1.imports)
    {σ : Strategy (nsig P1.imports) (nsig X)}
    (hσ : ∀ x : Sys O, (hostSat (tcpTh x.net).Accepts).holds (link (p1 x.obs) σ)) (o : O) :
    ¬ ∃ p ∈ link (p1 o) σ, TcpDecides (htrace p) := fun hresp =>
  tcp_not_both hresp (hσ ⟨o, netUp, webUp⟩) (hσ ⟨o, netDown, webUp⟩)

/-- `finish-connect` answers the outcome. -/
theorem connectOk_ans (n : Nat) (o : Option Nat) : connectOk o (connectAns n o) = true := by
  cases o <;> simp [connectOk, connectAns, okV, errV, errAnsN]

/-- `finish-connect` of the concrete TCP host. -/
theorem tcpImpl_finish (N : Network) (p : List WEv) (s : BitVec 32) (a : List Val) :
    tcpImpl N p finishConnect (.u32 s :: a) =
      (match lookup s (tcpState p) with
       | some addr => connectAns p.length (N addr)
       | none => errAnsN eNotInProgress) := by
  simp [tcpImpl, instanceNetwork, createTcp, startConnect, finishConnect, selfH]; rfl

/-- The answer of `finish-connect` passes the check. -/
theorem tcpImpl_ok_finish (N : Network) (p : List WEv) (s : BitVec 32) (a : List Val) :
    tcpOk N (p.foldl tcpNext []) (.imp finishConnect (.u32 s :: a)
      (tcpImpl N p finishConnect (.u32 s :: a))) = true := by
  have hs : p.foldl tcpNext [] = tcpState p := rfl
  rw [tcpImpl_finish, hs]
  cases hl : lookup s (tcpState p) with
  | none => simp [tcpOk, hl]
  | some addr => simp [tcpOk, hl, connectOk_ans]

/-- Every answer of the concrete TCP host passes the check. -/
theorem tcpImpl_ok (N : Network) (p : List WEv) (f : FnName) (a : List Val) :
    tcpOk N (p.foldl tcpNext []) (.imp f a (tcpImpl N p f a)) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 s =>
    by_cases hf : f = finishConnect
    · rw [hf]
      exact tcpImpl_ok_finish N p s a'
    · simp [tcpOk, hf]
  all_goals rfl

/-- **The concrete TCP host of `N` is a model of `tcpTh N`.** -/
theorem tcpImpl_sat {Y : Sig.{0}} {I : Set FnName} (N : Network) :
    (hostSat (tcpTh N).Accepts).holds (concrete (Y := Y) (I := I) (tcpImpl N)) :=
  concrete_sat _ fun _ ht => gated_follows (tcpImpl_ok N) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## HTTP -/

/-- A status answer is not an error answer. -/
theorem outcomeOk_status_error {s : BitVec 16} {k : Nat} {x : Val}
    (h : outcomeOk (.status s) x = true) : outcomeOk (.error k) x = false := by
  unfold outcomeOk at h
  split at h <;> simp_all [outcomeOk]

/-- `webUp` and `webDown` admit no common decisive answer. -/
theorem http_disjoint (q : HttpSt) (e : WEv) (hd : httpDecisive q e)
    (h₁ : httpOk webUp q e = true) : httpOk webDown q e = false := by
  obtain ⟨h, a, x, rfl, hs⟩ := hd
  obtain ⟨k, hl⟩ := Option.isSome_iff_exists.1 hs
  simp only [httpOk, ite_true, hl, getOk, webUp, webDown_eq_hand] at h₁ ⊢
  exact outcomeOk_status_error h₁

/-- **Two webs, one host.** -/
theorem http_not_both {Y : Sig.{0}} {I X : Set FnName} {η : Host Y I}
    {σ : Strategy (nsig I) (nsig X)} (hresp : ∃ p ∈ link η σ, HttpDecides (htrace p))
    (hUp : (hostSat (httpTh webUp).Accepts).holds (link η σ)) :
    ¬ (hostSat (httpTh webDown).Accepts).holds (link η σ) := fun hDown => by
  obtain ⟨p, hp, hd⟩ := hresp
  exact not_decides (ok₁ := httpOk webUp) (ok₂ := httpOk webDown) http_disjoint (hUp p hp)
    (hDown p hp) hd

/-- **Outgoing HTTP is not implementable over preview1.** -/
theorem no_http_over_p1 {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ (HttpOverP1 σ ∧ HttpResponsive σ) := by
  rintro ⟨hσ, Y, η, hη, hresp⟩
  exact http_not_both hresp (hσ webUp Y η hη) (hσ webDown Y η hη)

/-- The same for the component-level sentences. -/
theorem no_http_over_p1_ag {X : Set FnName} (σ : Strategy (nsig P1.imports) (nsig X)) :
    ¬ ((∀ W, (agP P1.th (retG (httpTh W))).holds σ) ∧
      ∃ s ∈ σ, P1.th.Accepts (hostView (wtrace s)) ∧ HttpDecides (retAsImp (wtrace s))) := by
  rintro ⟨hσ, s, hs, hA, hd⟩
  exact not_decides (ok₁ := httpOk webUp) (ok₂ := httpOk webDown) http_disjoint
    ((accepts_retG _ _).1 (hσ webUp s hs hA)) ((accepts_retG _ _).1 (hσ webDown s hs hA)) hd

/-- Systems that agree on every preview1 observation, for HTTP. -/
theorem no_http_sys {O : Type} {Y : Sig.{0}} {X : Set FnName} (p1 : O → Host Y P1.imports)
    {σ : Strategy (nsig P1.imports) (nsig X)}
    (hσ : ∀ x : Sys O, (hostSat (httpTh x.web).Accepts).holds (link (p1 x.obs) σ)) (o : O) :
    ¬ ∃ p ∈ link (p1 o) σ, HttpDecides (htrace p) := fun hresp =>
  http_not_both hresp (hσ ⟨o, netUp, webUp⟩) (hσ ⟨o, netUp, webDown⟩)

/-- The inner result of `get` matches the outcome. -/
theorem outcomeOk_V (n : Nat) (o : HttpOutcome) : outcomeOk o (outcomeV n o) = true := by
  cases o <;> simp [outcomeOk, outcomeV, okV, errV]

/-- `get` of the concrete HTTP host. -/
theorem httpImpl_get (W : Web) (p : List WEv) (h : BitVec 32) (a : List Val) :
    httpImpl W p futGet (.u32 h :: a) =
      (match lookup h (httpState p).futs with
       | some k => some [.variant 1 (some (okV (some (outcomeV p.length (W k.1 k.2)))))]
       | none => some [.variant 1 (some (errV none))]) := by
  simp [httpImpl, setAuthority, setPath, httpHandle, futGet, selfH]; rfl

/-- `status` of the concrete HTTP host. -/
theorem httpImpl_status (W : Web) (p : List WEv) (h : BitVec 32) (a : List Val) :
    httpImpl W p respStatus (.u32 h :: a) =
      (match lookup h (httpState p).resps with
       | some k => (match W k.1 k.2 with
         | .status s => some [.u16 s]
         | .error _ => some [.u16 200])
       | none => some [.u16 200]) := by
  simp [httpImpl, setAuthority, setPath, httpHandle, futGet, respStatus, selfH]; rfl

/-- The answer of `get` passes the check. -/
theorem httpImpl_ok_get (W : Web) (p : List WEv) (h : BitVec 32) (a : List Val) :
    httpOk W (httpState p) (.imp futGet (.u32 h :: a) (httpImpl W p futGet (.u32 h :: a))) =
      true := by
  rw [httpImpl_get]
  cases hl : lookup h (httpState p).futs with
  | none => simp [httpOk, hl]
  | some k => simp [httpOk, hl, getOk, okV, outcomeOk_V]

/-- The answer of `status` passes the check. -/
theorem httpImpl_ok_status (W : Web) (p : List WEv) (h : BitVec 32) (a : List Val) :
    httpOk W (httpState p)
      (.imp respStatus (.u32 h :: a) (httpImpl W p respStatus (.u32 h :: a))) = true := by
  have hne : respStatus ≠ futGet := by decide
  rw [httpImpl_status]
  cases hl : lookup h (httpState p).resps with
  | none => simp [httpOk, hl, hne]
  | some k => cases hw : W k.1 k.2 <;> simp [httpOk, hl, hne, statusOk, hw]

/-- Every answer of the concrete HTTP host passes the check. -/
theorem httpImpl_ok (W : Web) (p : List WEv) (f : FnName) (a : List Val) :
    httpOk W (p.foldl httpNext HttpSt.init) (.imp f a (httpImpl W p f a)) = true := by
  rcases a with _ | ⟨v, a'⟩
  · rfl
  cases v
  case u32 h =>
    by_cases hg : f = futGet
    · rw [hg]
      exact httpImpl_ok_get W p h a'
    · by_cases hr : f = respStatus
      · rw [hr]
        exact httpImpl_ok_status W p h a'
      · simp [httpOk, hg, hr]
  all_goals rfl

/-- **The concrete HTTP host of `W` is a model of `httpTh W`.** -/
theorem httpImpl_sat {Y : Sig.{0}} {I : Set FnName} (W : Web) :
    (hostSat (httpTh W).Accepts).holds (concrete (Y := Y) (I := I) (httpImpl W)) :=
  concrete_sat _ fun _ ht => gated_follows (httpImpl_ok W) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## The preview1 socket functions -/

/-- The preview1 functions named `sock_*` (from the witx). None takes an address: they act on
existing descriptors. -/
theorem p1_sock_fns : P1.fnNames.filter (fun n => n.toList.take 5 == "sock_".toList) =
    ["sock_accept", "sock_recv", "sock_send", "sock_shutdown"] := by
  decide

end Silmaril.Wasi.Versions.Net
