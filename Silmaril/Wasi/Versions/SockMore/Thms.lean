module

public import Silmaril.Wasi.Versions.SockMore.Defs
public import Silmaril.Wasi.Versions.Udp.Thms

@[expose] public section

/-!
# Sockets: name-lookup and accept hosts, and socket options: theorems

PROVED (standard axioms):

* **`dnsImpl_sat`**, **`dnsImpl3_sat`**: for every resolver `R` and lookup table `L` admitted by
  it, the hosts `dnsImpl L`, `dnsImpl3 L` are models of `dnsTh R`, `dnsTh3 R`.
* **`accImpl_sat`**: for every peers `P` and connections `C` admitted by them, `accImpl C` is a
  model of `acceptTh P`.
* **`optImpl_sat`**: for every option table `O`, `optImpl O inval` is a model of `optTh O`; so
  for the four vendored tables (`tcpOpts2_sat`, `udpOpts2_sat`, `tcpOpts3_sat`, `udpOpts3_sat`).
* **`sendImpl_sat`**: the UDP send host is a model of `sendTh` (0.2 `check-send`/`send`);
  `sendTh_examples`.
* **`optTh_examples`**: `set-hop-limit(0)` answered `ok` is rejected, and so is a
  `keep-alive-enabled` read that does not return the value set; a receive-buffer size read back
  differently is accepted (the WIT allows rounding).
-/

namespace Silmaril.Wasi.Versions.SockMore

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.Net

/-! ## Name lookup -/

theorem dnsOk_ne (R : Resolver) (q : DnsSt) {f : FnName} (hf : f ≠ resolveNext) (a : List Val)
    (r : Option (List Val)) : dnsOk R q (.imp f a r) = true := by
  unfold dnsOk
  split <;> simp_all

theorem nextAns_ok {d : Val → Bool} {l : List Val} (h : ∀ x ∈ l, d x = true) (k : Nat) :
    nextOk d (nextAns l k) = true := by
  unfold nextAns
  split
  · rename_i x hx
    simpa [nextOk, okV] using h x (List.mem_of_getElem? hx)
  · simp [nextOk, okV]

theorem dnsImpl_next (L : Lookup) (p : List WEv) (st : BitVec 32) (a : List Val) :
    dnsImpl L p resolveNext (.u32 st :: a) =
      (match lookup st (p.foldl dnsNext []) with
       | some name => nextAns (L name) (p.filter (isNextOn st)).length
       | none => errAnsN eInvalidState) := by
  simp [dnsImpl, resolve2, resolveNext, selfH]; rfl

/-- Every answer of the 0.2 name-lookup host passes the check. -/
theorem dnsImpl_ok {R : Resolver} {L : Lookup} (hL : LookupOk R L) (p : List WEv) (f : FnName)
    (a : List Val) : dnsOk R (p.foldl dnsNext []) (.imp f a (dnsImpl L p f a)) = true := by
  by_cases hf : f = resolveNext
  · subst hf
    rcases a with _ | ⟨v, a'⟩
    · rfl
    cases v
    case u32 st =>
      rw [dnsImpl_next]
      cases hl : lookup st (p.foldl dnsNext []) with
      | none => simp [dnsOk, hl]
      | some name => simpa [dnsOk, hl] using nextAns_ok (hL name) _
    all_goals rfl
  · exact dnsOk_ne R _ hf a _

/-- **The concrete 0.2 name-lookup host is a model of `dnsTh R`.** -/
theorem dnsImpl_sat {Y : Sig.{0}} {I : Set FnName} {R : Resolver} {L : Lookup}
    (hL : LookupOk R L) :
    (hostSat (dnsTh R).Accepts).holds (concrete (Y := Y) (I := I) (dnsImpl L)) :=
  concrete_sat _ fun _ ht => gated_follows (dnsImpl_ok hL) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-- Every answer of the 0.3 name-lookup host passes the check. -/
theorem dnsImpl3_ok {R : Resolver} {L : Lookup} (hL : LookupOk R L) (p : List WEv) (f : FnName)
    (a : List Val) : dnsOk3 R (p.foldl (fun _ _ => ()) ()) (.imp f a (dnsImpl3 L p f a)) =
      true := by
  by_cases hf : f = resolve3
  · subst hf
    rcases a with _ | ⟨name, a'⟩
    · rfl
    · have h : (L name).all (R name) = true := List.all_eq_true.2 (hL name)
      simpa [dnsOk3, dnsImpl3, listOk, okV] using h
  · unfold dnsOk3
    split <;> simp_all

/-- **The concrete 0.3 name-lookup host is a model of `dnsTh3 R`.** -/
theorem dnsImpl3_sat {Y : Sig.{0}} {I : Set FnName} {R : Resolver} {L : Lookup}
    (hL : LookupOk R L) :
    (hostSat (dnsTh3 R).Accepts).holds (concrete (Y := Y) (I := I) (dnsImpl3 L)) :=
  concrete_sat _ fun _ ht => gated_follows (dnsImpl3_ok hL) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## Accept -/

theorem accOk_ne (P : Peers) (q : AccSt) {f : FnName} (h1 : f ≠ tcpAccept) (h2 : f ≠ tcpRemote)
    (a : List Val) (r : Option (List Val)) : accOk P q (.imp f a r) = true := by
  unfold accOk
  split <;> simp_all

theorem accImpl_accept (C : Conn) (p : List WEv) (s : BitVec 32) (a : List Val) :
    accImpl C p tcpAccept (.u32 s :: a) =
      (match lookup s (p.foldl accNext {}).bound with
       | some addr =>
         (match C addr with
          | some _ => some [okV (some (.record [.u32 (BitVec.ofNat 32 p.length),
              .u32 (BitVec.ofNat 32 (p.length + 1)), .u32 (BitVec.ofNat 32 (p.length + 2))]))]
          | none => errAnsN eWouldBlock)
       | none => errAnsN eInvalidState) := by
  simp [accImpl, tcpBind, tcpListen, tcpAccept, selfH]; rfl

theorem accImpl_remote (C : Conn) (p : List WEv) (s : BitVec 32) (a : List Val) :
    accImpl C p tcpRemote (.u32 s :: a) =
      (match lookup s (p.foldl accNext {}).acc with
       | some addr =>
         (match C addr with
          | some r => some [okV (some r)]
          | none => errAnsN eInvalidState)
       | none => errAnsN eInvalidState) := by
  simp [accImpl, tcpBind, tcpListen, tcpAccept, tcpRemote, selfH]; rfl

/-- `accept` on a socket: the answer passes the check. -/
theorem accImpl_accept_ok {P : Peers} {C : Conn} (hC : ConnOk P C) (p : List WEv)
    (s : BitVec 32) (a : List Val) :
    accOk P (p.foldl accNext {}) (.imp tcpAccept (.u32 s :: a) (accImpl C p tcpAccept (.u32 s :: a)))
      = true := by
  rw [accImpl_accept]
  cases hl : lookup s (p.foldl accNext {}).bound with
  | none => simp [accOk, hl]
  | some addr =>
    dsimp only
    cases hc : C addr with
    | none => simp [accOk, hl, errAnsN, acceptOk, errV]
    | some r => simpa [accOk, hl, acceptOk, okV] using (hC addr r hc).1

/-- `remote-address` of a socket: the answer passes the check. -/
theorem accImpl_remote_ok {P : Peers} {C : Conn} (hC : ConnOk P C) (p : List WEv)
    (s : BitVec 32) (a : List Val) :
    accOk P (p.foldl accNext {}) (.imp tcpRemote (.u32 s :: a) (accImpl C p tcpRemote (.u32 s :: a)))
      = true := by
  rw [accImpl_remote]
  have hne : tcpRemote ≠ tcpAccept := by decide
  cases hl : lookup s (p.foldl accNext {}).acc with
  | none => simp [accOk, hl, hne]
  | some addr =>
    dsimp only
    cases hc : C addr with
    | none => simp [accOk, hl, hne, errAnsN, remoteOk, errV]
    | some r => simpa [accOk, hl, hne, remoteOk, okV] using (hC addr r hc).2

/-- Every answer of the accept host passes the check. -/
theorem accImpl_ok {P : Peers} {C : Conn} (hC : ConnOk P C) (p : List WEv) (f : FnName)
    (a : List Val) : accOk P (p.foldl accNext {}) (.imp f a (accImpl C p f a)) = true := by
  have hs : ∀ g, (∀ s a', accOk P (p.foldl accNext {}) (.imp g (.u32 s :: a') (accImpl C p g
      (.u32 s :: a'))) = true) → accOk P (p.foldl accNext {}) (.imp g a (accImpl C p g a)) = true := by
    intro g hg
    rcases a with _ | ⟨v, a'⟩
    · rfl
    cases v
    case u32 s => exact hg s a'
    all_goals rfl
  by_cases h1 : f = tcpAccept
  · rw [h1]; exact hs _ (accImpl_accept_ok hC p)
  by_cases h2 : f = tcpRemote
  · rw [h2]; exact hs _ (accImpl_remote_ok hC p)
  exact accOk_ne P _ h1 h2 a _

/-- **The concrete accept host is a model of `acceptTh P`.** -/
theorem accImpl_sat {Y : Sig.{0}} {I : Set FnName} {P : Peers} {C : Conn} (hC : ConnOk P C) :
    (hostSat (acceptTh P).Accepts).holds (concrete (Y := Y) (I := I) (accImpl C)) :=
  concrete_sat _ fun _ ht => gated_follows (accImpl_ok hC) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

/-! ## Options -/

theorem numOf_enc (t : OptTy) (n : Nat) : numOf (t.enc n) = some (t.norm n) := by
  cases t <;> simp [OptTy.enc, OptTy.norm, numOf, BitVec.toNat_ofNat]

/-- A setter's answer passes the check. -/
theorem setChk_setAns (o : OptSpec) (inval : Nat) (v : Val) : setChk o v (setAns o inval v) = true := by
  unfold setChk setAns
  by_cases hz : (o.nonzero && numOf v == some 0) = true
  · simp only [hz, ↓reduceIte, Bool.not_true, Bool.false_or]
    rfl
  · simp only [hz, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_or]

/-- A getter's answer passes the check. -/
theorem getChk_ans (o : OptSpec) (x : Option Nat) :
    getChk o x (some [okV (some (o.ty.enc (x.getD o.dflt)))]) = true := by
  cases x with
  | none => rfl
  | some n => simp [getChk, okV, numOf_enc]

/-- Every answer of the option host passes the check. -/
theorem optImpl_ok (O : List OptSpec) (inval : Nat) (p : List WEv) (f : FnName) (a : List Val) :
    optOk O (p.foldl (optNext O) []) (.imp f a (optImpl O inval p f a)) = true := by
  rcases a with _ | ⟨v, rest⟩
  · rfl
  cases v
  case u32 s =>
    unfold optOk optImpl
    dsimp only
    cases hs : setterOf O f with
    | some o =>
      rcases rest with _ | ⟨w, rest'⟩
      · rfl
      · dsimp only
        exact setChk_setAns o inval w
    | none =>
      cases hg : getterOf O f with
      | none => rfl
      | some o => dsimp only; cases o.exact <;> first | rfl | exact getChk_ans o _
  all_goals rfl

/-- **The concrete option host is a model of the option theory**, for every table. -/
theorem optImpl_sat {Y : Sig.{0}} {I : Set FnName} (O : List OptSpec) (inval : Nat) :
    (hostSat (optTh O).Accepts).holds (concrete (Y := Y) (I := I) (optImpl O inval)) :=
  concrete_sat _ fun _ ht => gated_follows (optImpl_ok O inval) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

theorem tcpOpts2_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat (optTh tcpOpts2).Accepts).holds (concrete (Y := Y) (I := I) (optImpl tcpOpts2 eInval2)) :=
  optImpl_sat _ _
theorem udpOpts2_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat (optTh udpOpts2).Accepts).holds (concrete (Y := Y) (I := I) (optImpl udpOpts2 eInval2)) :=
  optImpl_sat _ _
theorem tcpOpts3_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat (optTh tcpOpts3).Accepts).holds (concrete (Y := Y) (I := I) (optImpl tcpOpts3 eInval3)) :=
  optImpl_sat _ _
theorem udpOpts3_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat (optTh udpOpts3).Accepts).holds (concrete (Y := Y) (I := I) (optImpl udpOpts3 eInval3)) :=
  optImpl_sat _ _

/-! ## UDP send -/

theorem sendChk_ans (pm : Option Nat) (n : Nat) :
    sendChk pm n (if pm.any (n ≤ ·) then some [okV (some (.u64 (BitVec.ofNat 64 n)))] else none) =
      true := by
  by_cases h : pm.any (n ≤ ·) = true
  · simp only [h, ↓reduceIte, okV, sendChk, Bool.true_and, BitVec.toNat_ofNat]
    by_cases h0 : n = 0
    · simp [h0]
    · simp [h0, Nat.mod_le]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, sendChk]

/-- Every answer of the UDP send host passes the check. -/
theorem sendImpl_ok (p : List WEv) (f : FnName) (a : List Val) :
    sendOk (p.foldl sendNext []) (.imp f a (sendImpl p f a)) = true := by
  rcases a with _ | ⟨v, rest⟩
  · rfl
  cases v
  case u32 s =>
    unfold sendOk sendImpl
    dsimp only
    by_cases h1 : f = checkSend
    · simp [h1, isWouldBlockA, okV]
    by_cases h2 : f = udpSend
    · simp only [h2, ↓reduceIte]
      rcases rest with _ | ⟨d, rest'⟩
      · rfl
      · dsimp only
        cases hc : countOf d with
        | none => rfl
        | some n => exact sendChk_ans _ n
    simp only [h1, h2, ↓reduceIte]
  all_goals rfl

/-- **The concrete UDP send host is a model of `sendTh`.** -/
theorem sendImpl_sat {Y : Sig.{0}} {I : Set FnName} :
    (hostSat sendTh.Accepts).holds (concrete (Y := Y) (I := I) sendImpl) :=
  concrete_sat _ fun _ ht => gated_follows sendImpl_ok (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht

def chk (n : Nat) : WEv := .imp checkSend [.u32 0] (some [okV (some (.u64 (BitVec.ofNat 64 n)))])
def snd (n k : Nat) : WEv :=
  .imp udpSend [.u32 0, .record (List.replicate n (.record []))]
    (some [okV (some (.u64 (BitVec.ofNat 64 k)))])

/-- **`sendTh` is not trivial**: a permitted send of two answered `2` is accepted; answering `3`,
sending without a permit, or beyond it is rejected. -/
theorem sendTh_examples :
    sendTh.Accepts [chk 2, snd 2 2] ∧ ¬ sendTh.Accepts [chk 2, snd 2 3] ∧
    ¬ sendTh.Accepts [snd 1 1] ∧ ¬ sendTh.Accepts [chk 1, snd 2 1] ∧
    ¬ sendTh.Accepts [chk 2, snd 1 1, snd 1 1] := by
  unfold Protocol.Accepts; decide +kernel

/-! ## The option theory is not trivial -/

def setHop0 : WEv := .imp (tcp2 "[method]tcp-socket.set-hop-limit") [.u32 0, .u8 0] (some [okV none])
def setKa : WEv :=
  .imp (tcp2 "[method]tcp-socket.set-keep-alive-enabled") [.u32 0, .bool true] (some [okV none])
def getKa (b : Bool) : WEv :=
  .imp (tcp2 "[method]tcp-socket.keep-alive-enabled") [.u32 0] (some [okV (some (.bool b))])
def setRcv : WEv :=
  .imp (tcp2 "[method]tcp-socket.set-receive-buffer-size") [.u32 0, .u64 1000] (some [okV none])
def getRcv : WEv :=
  .imp (tcp2 "[method]tcp-socket.receive-buffer-size") [.u32 0] (some [okV (some (.u64 4096))])

theorem optTh_examples :
    ¬ (optTh tcpOpts2).Accepts [setHop0] ∧
    (optTh tcpOpts2).Accepts [setKa, getKa true] ∧
    ¬ (optTh tcpOpts2).Accepts [setKa, getKa false] ∧
    (optTh tcpOpts2).Accepts [setRcv, getRcv] := by
  unfold Protocol.Accepts; decide +kernel

end Silmaril.Wasi.Versions.SockMore
