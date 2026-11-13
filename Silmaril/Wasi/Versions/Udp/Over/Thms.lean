module

public import Silmaril.Wasi.Versions.Udp.Over.Defs
public import Silmaril.Wasi.Versions.Udp.Thms
public import Silmaril.Wasi.Versions.Net3.Over.Thms

@[expose] public section

/-!
# UDP receive across versions: theorems

PROVED (standard axioms):

* **(b) 0.3 over 0.2**: `udp3Over2_sat`, **`udp3Over2_model`**: for every inbox `U`, every
  number of rounds and every host of the 0.2 theory `udpTh U`, the composite
  `link η (ofSBody (udp3Over2 rounds) [])` is a model of the 0.3 theory `udpTh3 U`. Invariant
  `JU3`: an unpoisoned socket bound in 0.3 is bound to the same address in 0.2. Key lemma
  `wp_pollU`: polling a stream tied to `a` returns a datagram `U a` admits, an error, or traps.
* **(c) 0.2 over 0.3**: `udp2Over3_sat`, **`udp2Over3_model`**: for every inbox `U` and every
  host of `udpTh3 U`, the composite `link η (ofSBody udp2Over3 {})` is a model of `udpTh U`.
  Invariant `JU2` (bindings with generations).

Both are safety results: `udp3Over2` traps when the rounds run out, and the theories admit
traps and errors.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## The theory states -/

/-- Functions other than `start-bind` and `stream` keep the 0.2 UDP state. -/
theorem udpNext_other (q : UdpSt) {f : FnName} (h₁ : f ≠ udpBind) (h₂ : f ≠ udpStream)
    (a : List Val) (r : Option (List Val)) : udpNext q (.imp f a r) = q := by
  unfold udpNext
  split <;> simp_all

/-- A `start-bind` answer that is not `ok(_)` keeps the 0.2 UDP state. -/
theorem udpNext_bind_no (q : UdpSt) (a : List Val) {r : Option (List Val)}
    (hr : isOkUnit r = false) : udpNext q (.imp udpBind a r) = q := by
  have hne : udpBind ≠ udpStream := by decide
  unfold udpNext
  split <;> simp_all [isOkUnit]

/-- A successful `start-bind` records the binding. -/
theorem udpNext_bind_ok (q : UdpSt) (s : BitVec 32) (x addr : Val) (rest : List Val) :
    udpNext q (.imp udpBind (.u32 s :: x :: addr :: rest) (some [.variant 0 none])) =
      { q with bound := (s, addr) :: q.bound } := by
  simp [udpNext]

/-- A `stream` answer with an incoming stream `i` ties it to the socket's address. -/
theorem udpNext_stream_in (q : UdpSt) (s : BitVec 32) (rest : List Val) {r : Option (List Val)}
    {i : BitVec 32} (hr : streamIn r = some i) :
    udpNext q (.imp udpStream (.u32 s :: rest) r) =
      (match lookup s q.bound with
       | some addr => { q with ins := (i, addr) :: q.ins }
       | none => q) := by
  have hshape : ∃ o, r = some [.variant 0 (some (.record [.u32 i, o]))] := by
    unfold streamIn at hr
    split at hr <;> simp_all
  obtain ⟨o, rfl⟩ := hshape
  simp [udpNext]; rfl

/-- A `stream` answer without an incoming stream keeps the 0.2 UDP state. -/
theorem udpNext_stream_none (q : UdpSt) (a : List Val) {r : Option (List Val)}
    (hr : streamIn r = none) : udpNext q (.imp udpStream a r) = q := by
  have hne : udpStream ≠ udpBind := by decide
  unfold udpNext
  split <;> simp_all [streamIn]

/-- Functions other than `bind` keep the 0.3 UDP state. -/
theorem udpNext3_other (q : Udp3St) {f : FnName} (h : f ≠ udpBind3) (a : List Val)
    (r : Option (List Val)) : udpNext3 q (.imp f a r) = q := by
  unfold udpNext3
  split <;> simp_all

/-- An answer that is not `ok(_)` keeps the 0.3 UDP state. -/
theorem udpNext3_no (q : Udp3St) (f : FnName) (a : List Val) {r : Option (List Val)}
    (hr : isOkUnit r = false) : udpNext3 q (.imp f a r) = q := by
  unfold udpNext3
  split <;> simp_all [isOkUnit]

/-- A successful `bind` records the binding. -/
theorem udpNext3_bind_ok (q : Udp3St) (s : BitVec 32) (addr : Val) (rest : List Val) :
    udpNext3 q (.imp udpBind3 (.u32 s :: addr :: rest) (some [.variant 0 none])) =
      (s, addr) :: q := by
  simp [udpNext3]

/-- `ok(_)` is the only answer `isOkUnit` accepts. -/
theorem isOkUnit_eq {r : Option (List Val)} (h : isOkUnit r = true) : r = some [.variant 0 none] := by
  unfold isOkUnit at h
  split at h <;> simp_all

/-- A translated 0.2 error is not `ok(_)`. -/
theorem isOkUnit_errOf3 (r : Option (List Val)) : isOkUnit (errOf3 r) = false := by
  unfold errOf3
  split <;> rfl

/-- A translated 0.3 error is not `ok(_)`. -/
theorem isOkUnit_errOf2 (r : Option (List Val)) : isOkUnit (errOf2 r) = false := by
  unfold errOf2
  split <;> rfl

/-- An error answer is not a stream. -/
theorem streamIn_errAnsN (k : Nat) : streamIn (errAnsN k) = none := rfl

/-! ## Checks -/

/-- An answer every receive check accepts passes the 0.2 UDP check. -/
theorem udpOk_of (U : Inbox) (q : UdpSt) (f : FnName) (a : List Val) {r : Option (List Val)}
    (h : ∀ d, recvOk d r = true) : udpOk U q (.imp f a r) = true := by
  unfold udpOk
  split
  · split
    · split <;> simp_all
    · rfl
  · rfl

/-- An answer every receive check accepts passes the 0.3 UDP check. -/
theorem udpOk3_of (U : Inbox) (q : Udp3St) (f : FnName) (a : List Val) {r : Option (List Val)}
    (h : ∀ d, recvOk3 d r = true) : udpOk3 U q (.imp f a r) = true := by
  unfold udpOk3
  split
  · split
    · split <;> simp_all
    · rfl
  · rfl

/-- A translated 0.2 error passes every 0.3 receive check. -/
theorem recvOk3_errOf3 (d : Val → Bool) (r : Option (List Val)) : recvOk3 d (errOf3 r) = true := by
  unfold errOf3
  split <;> rfl

/-- A translated 0.3 error passes every 0.2 receive check. -/
theorem recvOk_errOf2 (d : Val → Bool) (r : Option (List Val)) : recvOk d (errOf2 r) = true := by
  unfold errOf2
  split <;> rfl

/-- **A 0.2 receive answer, translated, passes the 0.3 check.** -/
theorem recvOk3_of2 {d : Val → Bool} {r : Option (List Val)} (h : recvOk d r = true) :
    recvOk3 d (recv3of2 r) = true := by
  unfold recv3of2
  split
  · next x l =>
    have hx : d x = true := by simp_all [recvOk]
    simpa [recvOk3, okV] using hx
  · exact recvOk3_errOf3 d _

/-- **A 0.3 receive answer, translated, passes the 0.2 check.** -/
theorem recvOk_of3 {d : Val → Bool} {r : Option (List Val)} (h : recvOk3 d r = true) :
    recvOk d (recv2of3 r) = true := by
  unfold recv2of3
  split
  · next x =>
    have hx : d x = true := by simpa [recvOk3] using h
    simpa [recvOk, okV] using hx
  · exact recvOk_errOf2 d _

/-! ## (b) 0.3 over 0.2 -/

/-- An exported step of the 0.3 theory that keeps its state. -/
theorem udp3_step_keep {U : Inbox} {qG : Udp3St} {e : WEv} (hok : udpOk3 U qG e = true)
    (hn : udpNext3 qG e = qG) : (udpTh3 U).step qG e = some qG :=
  gated_step_iff.2 ⟨hok, hn.symm⟩

/-- **Polling a stream** returns a datagram the inbox admits for its address, an error, or a
trap; it keeps the component state and the 0.2 theory state. -/
theorem wp_pollU (U : Inbox) (st : PSt) (i : BitVec 32) :
    ∀ (k : Nat) (qT : UdpSt), Wp (udpTh U) (pollU st k i)
      (fun x qT' => x.1 = st ∧ qT' = qT ∧
        ∀ a, lookup i qT.ins = some a → recvOk3 (U a) x.2 = true) qT
  | 0, _ => ⟨rfl, rfl, fun _ _ => rfl⟩
  | k + 1, qT => fun r qT' hstep => by
    obtain ⟨hok, hq⟩ := gated_step_iff.1 hstep
    have hn : udpNext qT (.imp udpReceive [.u32 i, .u64 1] r) = qT :=
      udpNext_other qT (by decide) (by decide) _ _
    have hq' : qT' = qT := hq.trans hn
    have hrecv : ∀ a, lookup i qT.ins = some a → recvOk (U a) r = true := fun a hl => by
      simpa [udpOk, uRecv, hl] using hok
    show Wp (udpTh U) (if isEmptyRecv r then pollU st k i else .pure (st, recv3of2 r)) _ qT'
    rw [hq']
    by_cases he : isEmptyRecv r = true
    · simpa only [he, ↓reduceIte] using wp_pollU U st i k qT
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, rfl, fun a hl => recvOk3_of2 (hrecv a hl)⟩

/-- The post-condition of `receive(s)` over 0.2. -/
def RecvPost3 (U : Inbox) (qG : Udp3St) (a : List Val) (x : PSt × Option (List Val)) (qT' : UdpSt) :
    Prop :=
  udpOk3 U qG (.imp udpReceive3 a x.2) = true ∧ JU3 x.1 qT' qG

/-- Polling the stream `i` that `stream(s)` answered. -/
theorem wp_recv3_in (U : Inbox) (rounds : Nat) {st : PSt} {qT : UdpSt} {qG : Udp3St}
    (hJ : JU3 st qT qG) {s : BitVec 32} (hp : s ∉ st) (rest : List Val) {r : Option (List Val)}
    {i : BitVec 32} (hi : streamIn r = some i) :
    Wp (udpTh U) (pollU st rounds i) (RecvPost3 U qG (.u32 s :: rest))
      (udpNext qT (.imp udpStream [.u32 s, .variant 0 none] r)) := by
  have hb : (udpNext qT (.imp udpStream [.u32 s, .variant 0 none] r)).bound = qT.bound := by
    rw [udpNext_stream_in qT s _ hi]
    split <;> rfl
  have hins : ∀ a, lookup s qT.bound = some a →
      lookup i (udpNext qT (.imp udpStream [.u32 s, .variant 0 none] r)).ins = some a :=
    fun a hl => by
      rw [udpNext_stream_in qT s _ hi, hl]
      exact lookup_cons_self _ _ _
  refine Wp.mono (fun x qT' ⟨hx, hqT', hrecv⟩ => ⟨?_, ?_⟩) (wp_pollU U st i rounds _)
  · show udpOk3 U qG (.imp udpReceive3 (.u32 s :: rest) x.2) = true
    cases hl : lookup s qG with
    | none => simp [udpOk3, hl]
    | some a => simpa [udpOk3, hl] using hrecv a (hins a (hJ s a hp hl))
  · rw [hx, hqT']
    exact fun s' a hs hl => hb ▸ hJ s' a hs hl

/-- After `stream(s)`: poll the incoming stream, or answer the translated error. -/
theorem wp_recv3_after (U : Inbox) (rounds : Nat) {st : PSt} {qT : UdpSt} {qG : Udp3St}
    (hJ : JU3 st qT qG) {s : BitVec 32} (hp : s ∉ st) (rest : List Val) (r : Option (List Val)) :
    Wp (udpTh U) (match streamIn r with
      | some i => pollU st rounds i
      | none => .pure (st, errOf3 r)) (RecvPost3 U qG (.u32 s :: rest))
      (udpNext qT (.imp udpStream [.u32 s, .variant 0 none] r)) := by
  split
  · next i hi => exact wp_recv3_in U rounds hJ hp rest hi
  · next hi =>
    rw [udpNext_stream_none qT _ hi]
    exact ⟨udpOk3_of U qG _ _ fun d => recvOk3_errOf3 d r, hJ⟩

/-- **`receive` over 0.2** passes the 0.3 check and keeps the invariant. -/
theorem wp_recv3 (U : Inbox) (rounds : Nat) {st : PSt} {qT : UdpSt} {qG : Udp3St}
    (hJ : JU3 st qT qG) (a : List Val) :
    Wp (udpTh U) (recv3Prog rounds st a) (RecvPost3 U qG a) qT := by
  unfold recv3Prog
  split
  · next s rest =>
    by_cases hp : s ∈ st
    · simp only [hp, ↓reduceIte]
      exact ⟨udpOk3_of U qG _ _ fun _ => rfl, hJ⟩
    simp only [hp, ↓reduceIte]
    intro r qT₁ h₁
    have hq₁ : qT₁ = udpNext qT (.imp udpStream [.u32 s, .variant 0 none] r) :=
      (gated_step_iff.1 h₁).2
    exact hq₁ ▸ wp_recv3_after U rounds hJ hp rest r
  · exact ⟨udpOk3_of U qG _ _ fun _ => rfl, hJ⟩

/-- A bind that records nothing in either theory keeps the invariant. -/
theorem bind3_keep {U : Inbox} {st : PSt} {qT : UdpSt} {qG : Udp3St} (hJ : JU3 st qT qG)
    (a : List Val) {r : Option (List Val)} (hr : isOkUnit r = false) :
    ∃ qG', (udpTh3 U).step qG (.imp udpBind3 a r) = some qG' ∧ JU3 st qT qG' :=
  ⟨qG, udp3_step_keep (udpOk3_ne U qG (by decide) a r) (udpNext3_no qG _ a hr), hJ⟩

/-- A completed bind keeps the invariant. -/
theorem jU3_bind {st : PSt} {qT : UdpSt} {qG : Udp3St} (hJ : JU3 st qT qG) (s : BitVec 32)
    (addr : Val) : JU3 st { qT with bound := (s, addr) :: qT.bound } ((s, addr) :: qG) := by
  intro s' a hs hl
  by_cases he : s' = s
  · rw [he, lookup_cons_self] at hl ⊢
    exact hl
  · rw [lookup_cons_ne he] at hl ⊢
    exact hJ s' a hs hl

/-- A poisoned bind keeps the invariant. -/
theorem jU3_poison {st : PSt} {qT : UdpSt} {qG : Udp3St} (hJ : JU3 st qT qG) (s : BitVec 32)
    (addr : Val) : JU3 (s :: st) { qT with bound := (s, addr) :: qT.bound } qG := by
  intro s' a hs hl
  have hne : s' ≠ s := fun h => hs (h ▸ List.mem_cons_self ..)
  have hs' : s' ∉ st := fun h => hs (List.mem_cons_of_mem _ h)
  show lookup s' ((s, addr) :: qT.bound) = some a
  rw [lookup_cons_ne hne]
  exact hJ s' a hs' hl

/-- The post-condition of `bind` over 0.2. -/
def BindPost3 (U : Inbox) (qG : Udp3St) (a : List Val) (x : PSt × Option (List Val)) (qT' : UdpSt) :
    Prop :=
  ∃ qG', (udpTh3 U).step qG (.imp udpBind3 a x.2) = some qG' ∧ JU3 x.1 qT' qG'

/-- The answer of `bind` after `start-bind` succeeded and `finish-bind` answered `r₂`. -/
theorem bind3_finish (U : Inbox) {st : PSt} {qT : UdpSt} {qG : Udp3St} (hJ : JU3 st qT qG)
    (s : BitVec 32) (addr : Val) (rest : List Val) (r₂ : Option (List Val)) :
    Wp (udpTh U) (if isOkUnit r₂ then (.pure (st, some [okV none]) : SProg PSt udpImports)
      else .pure (s :: st, errOf3 r₂)) (BindPost3 U qG (.u32 s :: addr :: rest)) { qT with bound := (s, addr) :: qT.bound } := by
  by_cases ho₂ : isOkUnit r₂ = true
  · simp only [ho₂, ↓reduceIte]
    refine ⟨(s, addr) :: qG, gated_step_iff.2 ⟨udpOk3_ne U qG (by decide) _ _, ?_⟩,
      jU3_bind hJ s addr⟩
    exact (udpNext3_bind_ok qG s addr rest).symm
  · simp only [ho₂, Bool.false_eq_true, ↓reduceIte]
    have hstep : (udpTh3 U).step qG (.imp udpBind3 (.u32 s :: addr :: rest) (errOf3 r₂)) =
        some qG :=
      udp3_step_keep (udpOk3_ne U qG (by decide) _ _) (udpNext3_no qG _ _ (isOkUnit_errOf3 r₂))
    exact ⟨qG, hstep, jU3_poison hJ s addr⟩

/-- After `start-bind(s, nv, addr)` answered `r₁`. -/
theorem bind3_started (U : Inbox) {st : PSt} {qT : UdpSt} {qG : Udp3St} (hJ : JU3 st qT qG)
    (s : BitVec 32) (nv addr : Val) (rest : List Val) (r₁ : Option (List Val)) :
    Wp (udpTh U) (if isOkUnit r₁ then ((Prog.call (uFinish, [.u32 s]) fun r₂ =>
          if isOkUnit r₂ then .pure (st, some [okV none]) else .pure (s :: st, errOf3 r₂)) :
            SProg PSt udpImports)
      else .pure (st, errOf3 r₁)) (BindPost3 U qG (.u32 s :: addr :: rest))
      (udpNext qT (.imp udpBind [.u32 s, nv, addr] r₁)) := by
  by_cases ho : isOkUnit r₁ = true
  · have hb : udpNext qT (.imp udpBind [.u32 s, nv, addr] r₁) =
        { qT with bound := (s, addr) :: qT.bound } := by
      rw [isOkUnit_eq ho, udpNext_bind_ok]
    simp only [ho, ↓reduceIte]
    intro r₂ qT₃ h₂
    have hn₂ : udpNext (udpNext qT (.imp udpBind [.u32 s, nv, addr] r₁))
        (.imp udpFinishBind [.u32 s] r₂) = udpNext qT (.imp udpBind [.u32 s, nv, addr] r₁) :=
      udpNext_other _ (by decide) (by decide) _ _
    have hq₃ : qT₃ = { qT with bound := (s, addr) :: qT.bound } :=
      ((gated_step_iff.1 h₂).2.trans hn₂).trans hb
    exact hq₃ ▸ bind3_finish U hJ s addr rest r₂
  · rw [udpNext_bind_no qT _ (Bool.eq_false_iff.2 ho)]
    simp only [ho, Bool.false_eq_true, ↓reduceIte]
    exact bind3_keep hJ _ (isOkUnit_errOf3 r₁)

/-- **`bind` over 0.2** keeps the invariant. -/
theorem wp_bind3 (U : Inbox) {st : PSt} {qT : UdpSt} {qG : Udp3St} (hJ : JU3 st qT qG)
    (a : List Val) : Wp (udpTh U) (bind3Prog st a) (BindPost3 U qG a) qT := by
  unfold bind3Prog
  split
  · next s addr rest =>
    by_cases hp : s ∈ st
    · simp only [hp, ↓reduceIte]
      exact bind3_keep hJ _ rfl
    simp only [hp, ↓reduceIte]
    intro r₀ qT₁ h₀
    have hn : udpNext qT (.imp instanceNetwork [] r₀) = qT :=
      udpNext_other qT (by decide) (by decide) _ _
    have hq₁ : qT₁ = qT := (gated_step_iff.1 h₀).2.trans hn
    rw [hq₁]
    beta_reduce
    split
    · next nv => exact fun r₁ qT₂ h₁ => (gated_step_iff.1 h₁).2 ▸ bind3_started U hJ s nv addr rest r₁
    · exact bind3_keep hJ _ rfl
  · exact bind3_keep hJ _ rfl

/-- The invariant of `udp3Over2`. -/
theorem udp3Over2_inv (U : Inbox) (rounds : Nat) :
    WpInv (udp3Over2 rounds) [] (udpTh U) (udpTh3 U) JU3 where
  init := fun s a _ hl => by simp [lookup, udpTh3, gated] at hl
  call := by
    intro st qT qG q hJ
    by_cases h₁ : q.1.1 = udpCreate3
    · simp only [udp3Over2, h₁, ↓reduceIte]
      intro r qT' h
      have hn : udpNext qT (.imp createUdp q.2 r) = qT :=
        udpNext_other qT (by decide) (by decide) _ _
      have hq : qT' = qT := (gated_step_iff.1 h).2.trans hn
      exact ⟨qG, udp3_step_keep (udpOk3_ne U qG (f := udpCreate3) (by decide) _ _)
        (udpNext3_other qG (f := udpCreate3) (by decide) _ _), hq ▸ hJ⟩
    by_cases h₂ : q.1.1 = udpBind3
    · simp only [udp3Over2, h₂, ↓reduceIte]
      exact wp_bind3 U hJ q.2
    by_cases h₃ : q.1.1 = udpReceive3
    · simp only [udp3Over2, h₃, ↓reduceIte]
      exact Wp.mono (fun x qT' ⟨hok, hJ'⟩ =>
        ⟨qG, udp3_step_keep hok (udpNext3_other qG (f := udpReceive3) (by decide) _ _), hJ'⟩)
        (wp_recv3 U rounds hJ q.2)
    · simp only [udp3Over2, h₁, h₂, h₃, ↓reduceIte]
      exact ⟨qG, udp3_step_keep (udpOk3_ne U qG h₃ _ _) (udpNext3_other qG h₂ _ _), hJ⟩

/-- **The component guarantee of UDP receive 0.3 over 0.2.** -/
theorem udp3Over2_sat (U : Inbox) (rounds : Nat) :
    (agP (udpTh U) (retG (udpTh3 U))).holds (ofSBody (udp3Over2 rounds) []) :=
  ag_of_wpInv (udp3Over2_inv U rounds)

/-- **UDP receive 0.3 over 0.2**: over every host of the 0.2 theory of `U`, the composite is a
model of the 0.3 theory of the same inbox. -/
theorem udp3Over2_model (U : Inbox) (rounds : Nat) {Y : Sig.{0}} {η : Host Y udpImports}
    (hη : (hostSat (udpTh U).Accepts).holds η) :
    (hostSat (udpTh3 U).Accepts).holds (link η (ofSBody (udp3Over2 rounds) [])) :=
  link_model (udp3Over2_sat U rounds) hη

/-! ## (c) 0.2 over 0.3 -/

/-- An exported step of the 0.2 theory that keeps its state. -/
theorem udp_step_keep {U : Inbox} {qG : UdpSt} {e : WEv} (hok : udpOk U qG e = true)
    (hn : udpNext qG e = qG) : (udpTh U).step qG e = some qG :=
  gated_step_iff.2 ⟨hok, hn.symm⟩

/-- An error answer passes every receive check. -/
theorem recvOk_errAnsN (d : Val → Bool) (k : Nat) : recvOk d (errAnsN k) = true := rfl

/-- A new binding keeps the invariant. -/
theorem jU2_bind {st : USt} {qT : Udp3St} {qG : UdpSt} (hJ : JU2 st qT qG) (s : BitVec 32)
    (addr : Val) :
    JU2 { st with bnd := (s, (addr, st.ctr)) :: st.bnd, ctr := st.ctr + 1 } ((s, addr) :: qT)
      { qG with bound := (s, addr) :: qG.bound } := by
  obtain ⟨hG, hT, hS, hC, hB⟩ := hJ
  refine ⟨fun s' => ?_, fun s' => ?_, fun i a hl => ?_, fun i g hl => ?_, fun s' a g hl => ?_⟩
  · by_cases he : s' = s
    · simp only [he, lookup_cons_self, Option.map_some]
    · simp only [lookup_cons_ne he]
      exact hG s'
  · by_cases he : s' = s
    · simp only [he, lookup_cons_self, Option.map_some]
    · simp only [lookup_cons_ne he]
      exact hT s'
  · obtain ⟨g, hg, hag⟩ := hS i a hl
    refine ⟨g, hg, fun a' g' hb hgg => ?_⟩
    by_cases he : i = s
    · rw [he, lookup_cons_self] at hb
      have hg' : g' = st.ctr := (Prod.mk.inj (Option.some.inj hb)).2.symm
      have hlt : g < st.ctr := hC i g hg
      omega
    · rw [lookup_cons_ne he] at hb
      exact hag a' g' hb hgg
  · exact Nat.lt_succ_of_lt (hC i g hl)
  · by_cases he : s' = s
    · rw [he, lookup_cons_self] at hl
      have hg : g = st.ctr := (Prod.mk.inj (Option.some.inj hl)).2.symm
      show g < st.ctr + 1
      omega
    · rw [lookup_cons_ne he] at hl
      exact Nat.lt_succ_of_lt (hB s' a g hl)

/-- **`start-bind` over 0.3** keeps the invariant. -/
theorem wp_bind2 (U : Inbox) {st : USt} {qT : Udp3St} {qG : UdpSt} (hJ : JU2 st qT qG)
    (a : List Val) :
    Wp (udpTh3 U) (bind2Prog st a) (fun x qT' => ∃ qG',
      (udpTh U).step qG (.imp udpBind a x.2) = some qG' ∧ JU2 x.1 qT' qG') qT := by
  unfold bind2Prog
  split
  · next s x addr rest =>
    intro r qT₁ h
    have hq₁ : qT₁ = udpNext3 qT (.imp udpBind3 [.u32 s, addr] r) := (gated_step_iff.1 h).2
    show Wp (udpTh3 U) (if isOkUnit r then _ else .pure (st, errOf2 r)) _ qT₁
    by_cases ho : isOkUnit r = true
    · have hr : r = some [.variant 0 none] := isOkUnit_eq ho
      have hT : qT₁ = (s, addr) :: qT := by rw [hq₁, hr, udpNext3_bind_ok]
      simp only [ho, ↓reduceIte]
      refine ⟨{ qG with bound := (s, addr) :: qG.bound },
        gated_step_iff.2 ⟨udpOk_ne U qG (by decide) _ _, ?_⟩, hT ▸ jU2_bind hJ s addr⟩
      exact (udpNext_bind_ok qG s x addr rest).symm
    · have hT : qT₁ = qT := hq₁.trans (udpNext3_no qT _ _ (Bool.eq_false_iff.2 ho))
      simp only [ho, Bool.false_eq_true, ↓reduceIte]
      exact ⟨qG, udp_step_keep (udpOk_ne U qG (by decide) _ _)
        (udpNext_bind_no qG _ (isOkUnit_errOf2 r)), hT ▸ hJ⟩
  · exact ⟨qG, udp_step_keep (udpOk_ne U qG (by decide) _ _) (udpNext_bind_no qG _ rfl), hJ⟩

/-- A new stream keeps the invariant. -/
theorem jU2_stream {st : USt} {qT : Udp3St} {qG : UdpSt} (hJ : JU2 st qT qG) (s : BitVec 32)
    (a₀ : Val) (g : Nat) (hb : lookup s st.bnd = some (a₀, g)) :
    JU2 { st with strm := (s, g) :: st.strm } qT { qG with ins := (s, a₀) :: qG.ins } := by
  obtain ⟨hG, hT, hS, hC, hB⟩ := hJ
  refine ⟨hG, hT, fun i a hl => ?_, fun i g' hl => ?_, hB⟩
  · by_cases he : i = s
    · rw [he, lookup_cons_self] at hl ⊢
      refine ⟨g, rfl, fun a' g' hb' hgg => ?_⟩
      rw [hb] at hb'
      have ha : a₀ = a' := (Prod.mk.inj (Option.some.inj hb')).1
      exact ha ▸ Option.some.inj hl
    · rw [lookup_cons_ne he] at hl ⊢
      exact hS i a hl
  · by_cases he : i = s
    · rw [he, lookup_cons_self] at hl
      exact Option.some.inj hl ▸ hB s a₀ g hb
    · rw [lookup_cons_ne he] at hl
      exact hC i g' hl

/-- **`stream` over 0.3** keeps the invariant. -/
theorem stream2_ok (U : Inbox) {st : USt} {qT : Udp3St} {qG : UdpSt} (hJ : JU2 st qT qG)
    (a : List Val) : ∃ qG', (udpTh U).step qG (.imp udpStream a (stream2Res st a).2) = some qG' ∧
      JU2 (stream2Res st a).1 qT qG' := by
  have hkeep : ∀ k, ∃ qG', (udpTh U).step qG (.imp udpStream a (errAnsN k)) = some qG' ∧
      JU2 st qT qG' := fun k =>
    ⟨qG, udp_step_keep (udpOk_ne U qG (by decide) _ _) (udpNext_stream_none qG a rfl), hJ⟩
  unfold stream2Res
  split
  · next s rest =>
    split
    · next a₀ g hb =>
      have hbound : lookup s qG.bound = some a₀ := by rw [hJ.1 s, hb]; rfl
      refine ⟨{ qG with ins := (s, a₀) :: qG.ins }, gated_step_iff.2
        ⟨udpOk_ne U qG (by decide) _ _, ?_⟩, jU2_stream hJ s a₀ g hb⟩
      rw [udpNext_stream_in qG s rest (i := s) rfl, hbound]
    · exact hkeep _
  · exact hkeep _

/-- What `current` checks. -/
theorem current_spec {st : USt} {i : BitVec 32} (h : current st i = true) :
    ∃ g a' g', lookup i st.strm = some g ∧ lookup i st.bnd = some (a', g') ∧ g' = g := by
  unfold current at h
  split at h
  · next g a' g' hs hb => exact ⟨g, a', g', hs, hb, by simpa using h⟩
  · exact absurd h (by simp)

/-- **The 0.2 check of a translated 0.3 `receive`** on a stream of the current binding. -/
theorem recv2_check (U : Inbox) {st : USt} {qT : Udp3St} {qG : UdpSt} (hJ : JU2 st qT qG)
    {i : BitVec 32} (hc : current st i = true) (rest : List Val) {r : Option (List Val)}
    (hrecv : ∀ a', lookup i qT = some a' → recvOk3 (U a') r = true) :
    udpOk U qG (.imp udpReceive (.u32 i :: rest) (recv2of3 r)) = true := by
  cases hl : lookup i qG.ins with
  | none => simp [udpOk, hl]
  | some a =>
    obtain ⟨g, hg, hag⟩ := hJ.2.2.1 i a hl
    obtain ⟨g₀, a', g', hs, hb, hgg₀⟩ := current_spec hc
    have hg₀ : g₀ = g := Option.some.inj (hs.symm.trans hg)
    have ha : a' = a := hag a' g' hb (hgg₀.trans hg₀)
    have hT' : lookup i qT = some a' := by rw [hJ.2.1 i, hb]; rfl
    simpa [udpOk, hl] using recvOk_of3 (ha ▸ hrecv a' hT')

/-- **`receive` over 0.3** passes the 0.2 check and keeps the invariant. -/
theorem wp_recv2 (U : Inbox) {st : USt} {qT : Udp3St} {qG : UdpSt} (hJ : JU2 st qT qG)
    (a : List Val) :
    Wp (udpTh3 U) (recv2Prog st a)
      (fun x qT' => udpOk U qG (.imp udpReceive a x.2) = true ∧ JU2 x.1 qT' qG) qT := by
  unfold recv2Prog
  split
  · next i rest =>
    by_cases hc : current st i = true
    · simp only [hc, ↓reduceIte]
      intro r qT₁ h
      obtain ⟨hok, hq⟩ := gated_step_iff.1 h
      have hn : udpNext3 qT (.imp udpReceive3 [.u32 i] r) = qT := udpNext3_other qT (by decide) _ _
      have hrecv : ∀ a', lookup i qT = some a' → recvOk3 (U a') r = true := fun a' hl => by
        simpa [udpOk3, vRecv, hl] using hok
      exact ⟨recv2_check U hJ hc rest hrecv, hq.trans hn ▸ hJ⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨udpOk_of U qG _ _ fun d => recvOk_errAnsN d _, hJ⟩
  · exact ⟨udpOk_of U qG _ _ fun d => recvOk_errAnsN d _, hJ⟩

/-- The invariant of `udp2Over3`. -/
theorem udp2Over3_inv (U : Inbox) : WpInv udp2Over3 {} (udpTh3 U) (udpTh U) JU2 where
  init := ⟨fun s => rfl, fun s => rfl, fun i a hl => by simp [lookup, udpTh, gated] at hl,
    fun i g hl => by simp [lookup] at hl, fun s a g hl => by simp [lookup] at hl⟩
  call := by
    intro st qT qG q hJ
    have hkeep : ∀ (f : FnName) (r : Option (List Val)), f ≠ udpBind → f ≠ udpStream →
        f ≠ udpReceive → ∃ qG', (udpTh U).step qG (.imp f q.2 r) = some qG' ∧ JU2 st qT qG' :=
      fun f r h₁ h₂ h₃ => ⟨qG, udp_step_keep (udpOk_ne U qG h₃ _ _) (udpNext_other qG h₁ h₂ _ _), hJ⟩
    by_cases h₁ : q.1.1 = instanceNetwork
    · simp only [udp2Over3, h₁, ↓reduceIte]
      exact hkeep instanceNetwork _ (by decide) (by decide) (by decide)
    by_cases h₂ : q.1.1 = createUdp
    · simp only [udp2Over3, h₂, ↓reduceIte]
      intro r qT' h
      have hn : udpNext3 qT (.imp udpCreate3 q.2 r) = qT := udpNext3_other qT (by decide) _ _
      have hT : qT' = qT := (gated_step_iff.1 h).2.trans hn
      exact hT ▸ hkeep createUdp _ (by decide) (by decide) (by decide)
    by_cases h₃ : q.1.1 = udpBind
    · simp only [udp2Over3, h₃, ↓reduceIte]
      exact wp_bind2 U hJ q.2
    by_cases h₄ : q.1.1 = udpFinishBind
    · simp only [udp2Over3, h₄, ↓reduceIte]
      exact hkeep udpFinishBind _ (by decide) (by decide) (by decide)
    by_cases h₅ : q.1.1 = udpStream
    · simp only [udp2Over3, h₅, ↓reduceIte]
      exact stream2_ok U hJ q.2
    have h₆ : q.1.1 = udpReceive := by
      have hm := q.1.2
      simp only [udpImports_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      exact ((((hm.resolve_left h₁).resolve_left h₂).resolve_left h₃).resolve_left h₄).resolve_left h₅
    simp only [udp2Over3, h₁, h₂, h₃, h₄, h₅, ↓reduceIte]
    rw [h₆]
    exact Wp.mono (fun x qT' ⟨hok, hJ'⟩ =>
      ⟨qG, udp_step_keep hok (udpNext_other qG (f := udpReceive) (by decide) (by decide) _ _), hJ'⟩)
      (wp_recv2 U hJ q.2)

/-- **The component guarantee of UDP receive 0.2 over 0.3.** -/
theorem udp2Over3_sat (U : Inbox) :
    (agP (udpTh3 U) (retG (udpTh U))).holds (ofSBody udp2Over3 {}) :=
  ag_of_wpInv (udp2Over3_inv U)

/-- **UDP receive 0.2 over 0.3**: over every host of the 0.3 theory of `U`, the composite is a
model of the 0.2 theory of the same inbox. -/
theorem udp2Over3_model (U : Inbox) {Y : Sig.{0}} {η : Host Y udp3Fns}
    (hη : (hostSat (udpTh3 U).Accepts).holds η) :
    (hostSat (udpTh U).Accepts).holds (link η (ofSBody udp2Over3 {})) :=
  link_model (udp2Over3_sat U) hη

end Silmaril.Wasi.Versions.Net
