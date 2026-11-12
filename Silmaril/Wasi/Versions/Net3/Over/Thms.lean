module

public import Silmaril.Wasi.Versions.Net3.Over.Defs
public import Silmaril.Wasi.Versions.Net3.Thms
public import Silmaril.Wasi.Versions.Stateful.Thms

@[expose] public section

/-!
# TCP connect across versions: theorems

PROVED (standard axioms):

* **(b) 0.3 over 0.2**: `tcp3Over2_sat : (agP (tcpTh N) (retG (tcpTh3 (net3of2 N)))).holds
  (ofSBody (tcp3Over2 rounds) ())` and **`tcp3Over2_model`**: for every network `N` (0.2
  codes), every number of rounds, and every host of the 0.2 theory `tcpTh N`, the composite is
  a model of the 0.3 theory of the same network, `tcpTh3 (net3of2 N)`. Key lemma `wp_poll3`:
  while the socket is pending at `addr` in the 0.2 theory state, polling returns `N addr`'s
  outcome or traps.
* **(c) 0.2 over 0.3**: `tcp2Over3_sat`, **`tcp2Over3_model`**: for every network `N3` (0.3
  codes) and every host of `tcpTh3 N3`, the composite is a model of `tcpTh (net2of3 N3)`, with
  the invariant `J2`: every socket pending in the 0.2 theory has a stored outcome matching the
  network, and no stored answer is `would-block`.

Both directions hold over **every** host of the respective theory. They are safety results:
`tcp3Over2` may trap after `rounds` `would-block` answers, and the 0.3 theory admits it.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Gated steps -/

/-- A gated step succeeds exactly on checked events. -/
theorem gated_step_iff {S : Type} {i : S} {n : S → WEv → S} {ok : S → WEv → Bool} {q q' : S}
    {e : WEv} : (gated i n ok).step q e = some q' ↔ ok q e = true ∧ q' = n q e := by
  show (if ok q e then some (n q e) else none) = some q' ↔ _
  by_cases h : ok q e = true <;> simp [h, eq_comm]

/-- A gated step on a checked event. -/
theorem gated_step_of {S : Type} {i : S} {n : S → WEv → S} {ok : S → WEv → Bool} {q : S}
    {e : WEv} (h : ok q e = true) : (gated i n ok).step q e = some (n q e) :=
  gated_step_iff.2 ⟨h, rfl⟩

/-! ## Checks -/

/-- A trap passes the 0.3 check. -/
theorem tcpOk3_trap (N3 : Network) (q : Unit) (f : FnName) (a : List Val) :
    tcpOk3 N3 q (.imp f a none) = true := by
  rcases a with _ | ⟨x, _ | ⟨y, l⟩⟩ <;> simp [tcpOk3]

/-- Functions other than `connect` pass the 0.3 check. -/
theorem tcpOk3_ne (N3 : Network) (q : Unit) {f : FnName} (hf : f ≠ connect3) (a : List Val)
    (r : Option (List Val)) : tcpOk3 N3 q (.imp f a r) = true := by
  unfold tcpOk3
  split <;> simp_all

/-- Functions other than `finish-connect` pass the 0.2 check. -/
theorem tcpOk_ne (N : Network) (q : TcpSt) {f : FnName} (hf : f ≠ finishConnect) (a : List Val)
    (r : Option (List Val)) : tcpOk N q (.imp f a r) = true := by
  unfold tcpOk
  split <;> simp_all

/-- Functions other than `start-connect` and `finish-connect` keep the 0.2 theory state. -/
theorem tcpNext_other (q : TcpSt) {f : FnName} (h₁ : f ≠ startConnect) (h₂ : f ≠ finishConnect)
    (a : List Val) (r : Option (List Val)) : tcpNext q (.imp f a r) = q := by
  simp [tcpNext, h₁, h₂]

/-- A step of the 0.2 theory on another function. -/
theorem tcp_step_other (N : Network) (q : TcpSt) {f : FnName} (h₁ : f ≠ startConnect)
    (h₂ : f ≠ finishConnect) (a : List Val) (r : Option (List Val)) :
    (tcpTh N).step q (.imp f a r) = some q := by
  have h := gated_step_of (i := []) (n := tcpNext) (q := q) (tcpOk_ne N q h₂ a r)
  rwa [tcpNext_other q h₁ h₂] at h

/-! ## Lookups -/

/-- The newest entry. -/
theorem lookup_cons_self {α : Type} (k : BitVec 32) (v : α) (l : List (BitVec 32 × α)) :
    lookup k ((k, v) :: l) = some v := by
  simp [lookup]

/-- Another entry. -/
theorem lookup_cons_ne {α : Type} {k k' : BitVec 32} (h : k' ≠ k) (v : α)
    (l : List (BitVec 32 × α)) : lookup k' ((k, v) :: l) = lookup k' l := by
  simp [lookup, Ne.symm h]

/-- After removing `k`. -/
theorem lookup_filter {α : Type} (k k' : BitVec 32) (l : List (BitVec 32 × α)) :
    lookup k' (l.filter (·.1 != k)) = if k' = k then none else lookup k' l := by
  induction l with
  | nil => split <;> rfl
  | cons x l ih =>
    by_cases hx : x.1 = k
    · have hf : (x :: l).filter (·.1 != k) = l.filter (·.1 != k) := by simp [hx]
      rw [hf, ih]
      by_cases hk : k' = k
      · simp [hk]
      · simp [hk, lookup, hx, Ne.symm hk]
    · have hf : (x :: l).filter (·.1 != k) = x :: l.filter (·.1 != k) := by
        simp [hx]
      rw [hf]
      by_cases hk : k' = k
      · simp [lookup, hk, hx] at ih ⊢
      · simp only [lookup, List.find?_cons] at ih ⊢
        split <;> simp_all

/-! ## (b) 0.3 over 0.2 -/

/-- The value of a 0.3 `error-code` has its code as tag. -/
theorem ecV3_tag (k : Nat) : ∃ p, ecV3 k = .variant k p := by
  rw [ecV3_eq_hand]
  unfold ecV3H
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- An error answer passes the 0.3 outcome check. -/
theorem connectOk3_err (k : Nat) : connectOk3 (some k) (some [errV (some (ecV3 k))]) = true := by
  obtain ⟨p, hp⟩ := ecV3_tag k
  simp [hp, connectOk3, errV]

/-- **A 0.2 outcome, translated, is the translated outcome.** -/
theorem connectOk3_outcome3 {o : Option Nat} {r : Option (List Val)} (h : connectOk o r = true) :
    connectOk3 (o.map e2to3) (outcome3 r) = true := by
  unfold connectOk at h
  split at h
  · rfl
  · next k k' =>
    have hk : k' = k := by simpa using h
    rw [hk]
    exact connectOk3_err _
  · exact absurd h (by simp)

/-- The check of a pending `finish-connect`. -/
theorem tcpOk_finish {N : Network} {q : TcpSt} {s : BitVec 32} {addr : Val}
    (hl : lookup s q = some addr) {r : Option (List Val)}
    (h : tcpOk N q (.imp finishConnect [.u32 s] r) = true) :
    isWouldBlock r = true ∨ connectOk (N addr) r = true := by
  simpa [tcpOk, hl] using h

/-- The theory state after a `finish-connect` answered `would-block`. -/
theorem tcpNext_wouldBlock (q : TcpSt) (s : BitVec 32) {r : Option (List Val)}
    (hw : isWouldBlock r = true) : tcpNext q (.imp finishConnect [.u32 s] r) = q := by
  simp [tcpNext, hw, finishConnect, startConnect]

/-- **Polling a pending socket** returns the network's outcome or traps. -/
theorem wp_poll3 (N : Network) (s : BitVec 32) (addr : Val) (rest : List Val) :
    ∀ (k : Nat) (qT : TcpSt), lookup s qT = some addr →
      Wp (tcpTh N) (poll3 k s)
        (fun x _ => tcpOk3 (net3of2 N) () (.imp connect3 (.u32 s :: addr :: rest) x.2) = true) qT
  | 0, _, _ => tcpOk3_trap _ _ _ _
  | k + 1, qT, hl => fun r qT' hstep => by
    obtain ⟨hok, hq⟩ := gated_step_iff.1 hstep
    show Wp (tcpTh N) (if isWouldBlock r = true then poll3 k s else .pure ((), outcome3 r)) _ qT'
    by_cases hw : isWouldBlock r = true
    · have hq' : qT' = qT := hq.trans (tcpNext_wouldBlock qT s hw)
      simp only [hw, ↓reduceIte]
      exact hq' ▸ wp_poll3 N s addr rest k qT hl
    · have hc : connectOk (N addr) r = true := (tcpOk_finish hl hok).resolve_left hw
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      show tcpOk3 (net3of2 N) () (.imp connect3 (.u32 s :: addr :: rest) (outcome3 r)) = true
      simp [tcpOk3, net3of2, connectOk3_outcome3 hc]

/-- The 0.2 theory state after `instance-network` and a successful `start-connect`. -/
theorem lookup_started (qT : TcpSt) (s : BitVec 32) (nv addr : Val) (r : Option (List Val)) :
    lookup s (tcpNext (tcpNext qT (.imp instanceNetwork [] r))
      (.imp startConnect [.u32 s, nv, addr] (some [.variant 0 none]))) = some addr := by
  rw [tcpNext_other qT (by decide) (by decide)]
  simp [tcpNext, lookup]

/-- **The program of `connect`** returns an outcome accepted by the 0.3 theory. -/
theorem wp_connect3 (N : Network) (rounds : Nat) (a : List Val) (qT : TcpSt) :
    Wp (tcpTh N) (connect3Prog rounds a)
      (fun x _ => tcpOk3 (net3of2 N) () (.imp connect3 a x.2) = true) qT := by
  unfold connect3Prog
  split
  · next s addr rest =>
    intro r qT' h₁
    have hq₁ : qT' = tcpNext qT (.imp instanceNetwork [] r) := (gated_step_iff.1 h₁).2
    beta_reduce
    split
    · next nv =>
      intro r₂ qT'' h₂
      have hq₂ : qT'' = tcpNext qT' (.imp startConnect [.u32 s, nv, addr] r₂) :=
        (gated_step_iff.1 h₂).2
      beta_reduce
      split
      · exact wp_poll3 N s addr rest rounds qT'' (by rw [hq₂, hq₁]; exact lookup_started qT s nv addr _)
      · exact tcpOk3_trap _ _ _ _
    · exact tcpOk3_trap _ _ _ _
  · exact tcpOk3_trap _ _ _ _

/-- The invariant of `tcp3Over2` (none needed). -/
theorem tcp3Over2_inv (N : Network) (rounds : Nat) :
    WpInv (tcp3Over2 rounds) () (tcpTh N) (tcpTh3 (net3of2 N)) (fun _ _ _ => True) where
  init := trivial
  call := by
    intro _ qT _ q _
    by_cases hc : q.1.1 = create3
    · simp only [tcp3Over2, hc, ↓reduceIte]
      exact fun _ _ _ => ⟨(), gated_step_of (tcpOk3_ne _ _ (by decide) _ _), trivial⟩
    · have hconn : q.1.1 = connect3 := by
        have hm := q.1.2
        simp only [tcp3Fns_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        exact hm.resolve_left hc
      simp only [tcp3Over2, hc, ↓reduceIte]
      exact Wp.mono (fun x _ hx => ⟨(), gated_step_of (by rw [hconn]; exact hx), trivial⟩)
        (wp_connect3 N rounds q.2 qT)

/-- **The component guarantee of TCP connect 0.3 over 0.2.** -/
theorem tcp3Over2_sat (N : Network) (rounds : Nat) :
    (agP (tcpTh N) (retG (tcpTh3 (net3of2 N)))).holds (ofSBody (tcp3Over2 rounds) ()) :=
  ag_of_wpInv (tcp3Over2_inv N rounds)

/-- **TCP connect 0.3 over 0.2**: over every host of the 0.2 theory of `N`, the composite is a
model of the 0.3 theory of the same network. -/
theorem tcp3Over2_model (N : Network) (rounds : Nat) {Y : Sig.{0}} {η : Host Y tcpImports}
    (hη : (hostSat (tcpTh N).Accepts).holds η) :
    (hostSat (tcpTh3 (net3of2 N)).Accepts).holds (link η (ofSBody (tcp3Over2 rounds) ())) :=
  link_model (tcp3Over2_sat N rounds) hη

/-! ## (c) 0.2 over 0.3 -/

/-- An error other than `would-block` is not `would-block`. -/
theorem isWouldBlock_err {j : Nat} (h : j ≠ eWouldBlock) : isWouldBlock (errAnsN j) = false := by
  unfold isWouldBlock errAnsN errV
  split <;> simp_all

/-- A step of the 0.2 theory on a checked event. -/
theorem tcp_step_of {N : Network} {q : TcpSt} {e : WEv} (h : tcpOk N q e = true) :
    (tcpTh N).step q e = some (tcpNext q e) :=
  gated_step_of h

/-- The outcome of an `ok` answer. -/
theorem connectOk3_ok {o : Option Nat} (hc : connectOk3 o (some [.variant 0 none]) = true) :
    o = none := by
  cases o with
  | none => rfl
  | some k => simp [connectOk3] at hc

/-- The outcome of an error answer. -/
theorem connectOk3_errTag {o : Option Nat} {k : Nat} {p : Option Val}
    (hc : connectOk3 o (some [.variant 1 (some (.variant k p))]) = true) : o = some k := by
  cases o with
  | none => simp [connectOk3] at hc
  | some k' =>
    have hk : k = k' := by simpa [connectOk3] using hc
    rw [hk]

/-- **A stored answer is the translated 0.3 outcome**, and not `would-block`. -/
theorem fin2_ok {n : Nat} {r : Option (List Val)} {fin : Option (List Val)} {o : Option Nat}
    (h : fin2 n r = some fin) (hc : connectOk3 o r = true) :
    connectOk (o.map e3to2) fin = true ∧ isWouldBlock fin = false := by
  unfold fin2 at h
  split at h
  · have ho : o = none := connectOk3_ok hc
    have hf : fin = connectAns n none := (Option.some.inj h).symm
    rw [ho, hf]
    exact ⟨connectOk_ans n none, rfl⟩
  · next k p =>
    have ho : o = some k := connectOk3_errTag hc
    have hf : fin = errAnsN (e3to2 k) := (Option.some.inj h).symm
    rw [ho, hf]
    exact ⟨connectOk_ans n (some (e3to2 k)), isWouldBlock_err (e3to2_ne_wouldBlock k)⟩
  · exact absurd h (by simp)

/-- The 0.3 check of a `connect` call. -/
theorem tcpOk3_connect {N3 : Network} {s : BitVec 32} {addr : Val} {r : Option (List Val)}
    (h : tcpOk3 N3 () (.imp connect3 [.u32 s, addr] r) = true) :
    r = none ∨ connectOk3 (N3 addr) r = true := by
  cases r with
  | none => exact Or.inl rfl
  | some l => exact Or.inr (by simpa [tcpOk3] using h)

/-- A started connect extends the invariant. -/
theorem j2_cons {N3 : Network} {st : CSt} {qG : TcpSt} (hJ : J2 N3 st () qG) (s : BitVec 32)
    (addr : Val) {fin : Option (List Val)} (hc : connectOk (net2of3 N3 addr) fin = true)
    (hw : isWouldBlock fin = false) (n : Nat) :
    J2 N3 { pend := (s, fin) :: st.pend, next := n } () ((s, addr) :: qG) := by
  refine ⟨fun s' addr' hl => ?_, fun s' fin' hl => ?_⟩
  · by_cases hs : s' = s
    · subst hs
      rw [lookup_cons_self] at hl
      exact ⟨fin, lookup_cons_self _ _ _, Option.some.inj hl ▸ hc⟩
    · rw [lookup_cons_ne hs] at hl
      obtain ⟨f, hf, hfc⟩ := hJ.1 s' addr' hl
      exact ⟨f, by rw [lookup_cons_ne hs]; exact hf, hfc⟩
  · by_cases hs : s' = s
    · subst hs
      rw [lookup_cons_self] at hl
      exact Option.some.inj hl ▸ hw
    · rw [lookup_cons_ne hs] at hl
      exact hJ.2 s' fin' hl

/-- Forgetting a socket keeps the invariant. -/
theorem j2_filter {N3 : Network} {st : CSt} {qG : TcpSt} (hJ : J2 N3 st () qG) (s : BitVec 32) :
    J2 N3 { st with pend := st.pend.filter (·.1 != s) } () (qG.filter (·.1 != s)) := by
  refine ⟨fun s' addr hl => ?_, fun s' fin hl => ?_⟩
  · rw [lookup_filter] at hl
    by_cases hs : s' = s
    · simp [hs] at hl
    · simp only [hs, ↓reduceIte] at hl
      obtain ⟨f, hf, hfc⟩ := hJ.1 s' addr hl
      exact ⟨f, by simp [lookup_filter, hs, hf], hfc⟩
  · have hl' : lookup s' (st.pend.filter (·.1 != s)) = some fin := hl
    rw [lookup_filter] at hl'
    by_cases hs : s' = s
    · simp [hs] at hl'
    · simp only [hs, ↓reduceIte] at hl'
      exact hJ.2 s' fin hl'

/-- Forgetting a socket with no stored answer keeps the invariant. -/
theorem j2_filter_none {N3 : Network} {st : CSt} {qG : TcpSt} (hJ : J2 N3 st () qG)
    (s : BitVec 32) (hn : lookup s st.pend = none) : J2 N3 st () (qG.filter (·.1 != s)) := by
  have h := j2_filter hJ s
  refine ⟨fun s' addr hl => ?_, hJ.2⟩
  obtain ⟨f, hf, hfc⟩ := h.1 s' addr hl
  have hs : s' ≠ s := by
    rintro rfl
    simp [lookup_filter] at hf
  exact ⟨f, by simpa [lookup_filter, hs] using hf, hfc⟩

/-- A successful `start-connect` step of the 0.2 theory. -/
theorem tcp_step_start (N : Network) (qG : TcpSt) (s : BitVec 32) (x addr : Val)
    (rest : List Val) :
    (tcpTh N).step qG (.imp startConnect (.u32 s :: x :: addr :: rest) (some [okV none])) =
      some ((s, addr) :: qG) := by
  rw [tcp_step_of (tcpOk_ne N qG (by decide) _ _)]
  simp [tcpNext, okV]

/-- A `start-connect` step of the 0.2 theory that is not `ok`. -/
theorem tcp_step_start_no (N : Network) (qG : TcpSt) (a : List Val) {r : Option (List Val)}
    (hr : r = none ∨ r = errAnsN eInvalidArg) : (tcpTh N).step qG (.imp startConnect a r) = some qG := by
  rw [tcp_step_of (tcpOk_ne N qG (by decide) _ _)]
  rcases hr with rfl | rfl <;> simp [tcpNext, errAnsN, errV]

/-- **`start-connect` over 0.3** keeps the invariant. -/
theorem wp_start (N3 : Network) {st : CSt} {qG : TcpSt} (hJ : J2 N3 st () qG) (a : List Val)
    (qT : Unit) :
    Wp (tcpTh3 N3) (startProg st a) (fun x qT' => ∃ qG',
      (tcpTh (net2of3 N3)).step qG (.imp startConnect a x.2) = some qG' ∧ J2 N3 x.1 qT' qG') qT := by
  unfold startProg
  split
  · next s x addr rest =>
    intro r qT' h
    have hok : tcpOk3 N3 () (.imp connect3 [.u32 s, addr] r) = true := (gated_step_iff.1 h).1
    beta_reduce
    split
    · next fin hfin =>
      have hc : connectOk3 (N3 addr) r = true := by
        rcases tcpOk3_connect hok with hr | hr
        · subst hr
          simp [fin2] at hfin
        · exact hr
      obtain ⟨hfc, hw⟩ := fin2_ok hfin hc
      exact ⟨(s, addr) :: qG, tcp_step_start _ qG s x addr rest, j2_cons hJ s addr hfc hw _⟩
    · exact ⟨qG, tcp_step_start_no _ qG _ (Or.inl rfl), hJ⟩
  · exact ⟨qG, tcp_step_start_no _ qG _ (Or.inr rfl), hJ⟩

/-- A `finish-connect` step of the 0.2 theory with an answer that is not `would-block`. -/
theorem tcp_step_finish (N : Network) (qG : TcpSt) (s : BitVec 32) (rest : List Val)
    {r : Option (List Val)} (hw : isWouldBlock r = false)
    (hok : ∀ addr, lookup s qG = some addr → connectOk (N addr) r = true) :
    (tcpTh N).step qG (.imp finishConnect (.u32 s :: rest) r) = some (qG.filter (·.1 != s)) := by
  have hc : tcpOk N qG (.imp finishConnect (.u32 s :: rest) r) = true := by
    cases hl : lookup s qG with
    | none => simp [tcpOk, hl]
    | some addr => simp [tcpOk, hl, hok addr hl]
  rw [tcp_step_of hc]
  simp [tcpNext, hw, finishConnect, startConnect]

/-- A `finish-connect` step of the 0.2 theory on arguments without a socket handle. -/
theorem tcp_step_finish_bad (N : Network) (qG : TcpSt) (a : List Val) (r : Option (List Val))
    (ha : ∀ s rest, a = .u32 s :: rest → False) :
    (tcpTh N).step qG (.imp finishConnect a r) = some qG := by
  have hok : tcpOk N qG (.imp finishConnect a r) = true := by
    unfold tcpOk
    split <;> simp_all
  rw [tcp_step_of hok]
  simp only [tcpNext, finishConnect, startConnect]
  split <;> simp_all

/-- **`finish-connect` over 0.3** keeps the invariant. -/
theorem finish_ok (N3 : Network) {st : CSt} {qG : TcpSt} (hJ : J2 N3 st () qG) (a : List Val) :
    ∃ qG', (tcpTh (net2of3 N3)).step qG (.imp finishConnect a (finishRes st a).2) = some qG' ∧
      J2 N3 (finishRes st a).1 () qG' := by
  unfold finishRes
  split
  · next s rest =>
    split
    · next fin hfin =>
      refine ⟨qG.filter (·.1 != s), tcp_step_finish _ qG s rest (hJ.2 s fin hfin)
        (fun addr hl => ?_), j2_filter hJ s⟩
      obtain ⟨f, hf, hfc⟩ := hJ.1 s addr hl
      rw [hfin] at hf
      exact Option.some.inj hf ▸ hfc
    · next hn =>
      refine ⟨qG.filter (·.1 != s), tcp_step_finish _ qG s rest rfl (fun addr hl => ?_),
        j2_filter_none hJ s hn⟩
      obtain ⟨f, hf, -⟩ := hJ.1 s addr hl
      rw [hn] at hf
      exact absurd hf (by simp)
  · next hne => exact ⟨qG, tcp_step_finish_bad _ qG _ _ hne, hJ⟩

/-- The invariant of `tcp2Over3`. -/
theorem tcp2Over3_inv (N3 : Network) :
    WpInv tcp2Over3 {} (tcpTh3 N3) (tcpTh (net2of3 N3)) (J2 N3) where
  init := ⟨fun s addr hl => by simp [lookup, tcpTh, gated] at hl,
    fun s fin hl => by simp [lookup] at hl⟩
  call := by
    intro st qT qG q hJ
    by_cases h₁ : q.1.1 = instanceNetwork
    · simp only [tcp2Over3, h₁, ↓reduceIte]
      exact ⟨qG, tcp_step_other _ qG (by decide) (by decide) _ _, hJ⟩
    by_cases h₂ : q.1.1 = createTcp
    · simp only [tcp2Over3, h₂, ↓reduceIte]
      exact fun _ _ _ => ⟨qG, tcp_step_other _ qG (by decide) (by decide) _ _, hJ⟩
    by_cases h₃ : q.1.1 = startConnect
    · simp only [tcp2Over3, h₃, ↓reduceIte]
      exact wp_start N3 hJ q.2 qT
    have h₄ : q.1.1 = finishConnect := by
      have hm := q.1.2
      simp only [tcpImports_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      exact (((hm.resolve_left h₁).resolve_left h₂).resolve_left h₃)
    simp only [tcp2Over3, h₄]
    exact finish_ok N3 hJ q.2

/-- **The component guarantee of TCP connect 0.2 over 0.3.** -/
theorem tcp2Over3_sat (N3 : Network) :
    (agP (tcpTh3 N3) (retG (tcpTh (net2of3 N3)))).holds (ofSBody tcp2Over3 {}) :=
  ag_of_wpInv (tcp2Over3_inv N3)

/-- **TCP connect 0.2 over 0.3**: over every host of the 0.3 theory of `N3`, the composite is a
model of the 0.2 theory of the same network. -/
theorem tcp2Over3_model (N3 : Network) {Y : Sig.{0}} {η : Host Y tcp3Fns}
    (hη : (hostSat (tcpTh3 N3).Accepts).holds η) :
    (hostSat (tcpTh (net2of3 N3)).Accepts).holds (link η (ofSBody tcp2Over3 {})) :=
  link_model (tcp2Over3_sat N3) hη

end Silmaril.Wasi.Versions.Net
