module

public import Silmaril.Proofs.Servers.LinuxHello.Calls
public import Silmaril.Servers.Sockets.Thms
public import Silmaril.Servers.Wire1.Thms

/-!
# A Linux hello server loop: it serves hello on one connection

For `Silmaril.Servers.LinuxHello.Thms`: for every sequence of requests on the wire, a run of
the loop accepts one connection whose client sends them and then `FIN`, reads them all, and
sends one `helloWire` for each (`serves`).
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.LinuxHello

open Silmaril.Process Silmaril.Process.LPS Silmaril.Servers.LinuxHello Silmaril.Servers.Platform
open Silmaril.Servers.Sockets Silmaril.Servers.Wire1 Silmaril.Servers.Compare

/-! ## Runs -/

theorem hstar_append {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
    {refused : RefusalFilter} {c₁ c₂ c₃ : Config isa} {h₁ h₂ : List StepRecord}
    (s₁ : HStar segs spec refused c₁ h₁ c₂) (s₂ : HStar segs spec refused c₂ h₂ c₃) :
    HStar segs spec refused c₁ (h₁ ++ h₂) c₃ := by
  induction s₁ with
  | refl => exact s₂
  | step st _ ih => exact .step st (ih s₂)

/-- An instruction step of the loop. -/
theorem instr_step (st : St) (hp : pending st = none) (m : LPS.Model) (hh : m.halted = none)
    (hl : m.vm.lazy = []) :
    LStep (isa := isa) [] serverSpec noFilter ⟨st, m⟩ .instr ⟨next st, m⟩ := by
  refine .instr hh hp ?_
  show accountStep isa [] st m = .ok (next st, m)
  unfold accountStep
  simp [isa, materialize_nolazy hl]

/-- The loop's state after a system call returned `r`, having written `g`. -/
def setRet (st : St) (r : Word) (g : List LPS.Byte) : St := { st with ret := r, got := g }

/-- A system-call step of the loop. -/
theorem sys_step (st : St) (x8 : Word) (hp : pending st = some x8) (m : LPS.Model)
    (eff : SyscallEffect) (m' : LPS.Model) (evs : List Event)
    (hs : serverSpec ⟨x8, args st, readByte st, writableByte⟩ m (.ok eff m' evs))
    (hh : m.halted = none) (hh' : m'.halted = none) (hl : m'.vm.lazy = []) :
    LStep (isa := isa) [] serverSpec noFilter ⟨st, m⟩ (.syscall x8 (args st) eff evs)
      ⟨advance (setRet st eff.ret (eff.writes.flatMap fun p => p.2)), m'⟩ :=
  .syscall hh hp hs (fun h => h) hh' (materialize_nolazy hl _)

/-! ## The model during a connection -/

/-- The descriptors while serving a connection whose remaining client stream is `rx`. -/
def connFds (q : NetQueue) (rx : NetStream) : List (Word × FdEntry) :=
  fdInsert baseFds 4 (.socket (.connected (nqPeer q) 3 rx))

/-- The model while serving the first connection. -/
def mConn (q : NetQueue) (rx : NetStream) : LPS.Model := (model0 q).withAccepted (connFds q rx)

theorem fdLookup_connFds (q : NetQueue) (rx : NetStream) :
    fdLookup (mConn q rx).fds 4 = some (.socket (.connected (nqPeer q) 3 rx)) := by
  simp [mConn, Model.withAccepted, Model.fds, connFds, fdLookup, fdInsert]

theorem mConn_withFds (q : NetQueue) (rx rx' : NetStream) :
    (mConn q rx).withFds (fdInsert (mConn q rx).fds 4 (.socket (.connected (nqPeer q) 3 rx'))) =
      mConn q rx' := by
  simp only [mConn, Model.withAccepted, Model.withFds, Model.fds, connFds, fdInsert,
    List.filter_cons, List.filter_filter]
  simp

theorem mConn_halted (q : NetQueue) (rx : NetStream) : (mConn q rx).halted = none := rfl
theorem mConn_lazy (q : NetQueue) (rx : NetStream) : (mConn q rx).vm.lazy = [] := rfl

theorem fd32_four : fd32 (4 : Word) = 4 := by decide
theorem fd32_three : fd32 (3 : Word) = 3 := by decide

theorem lenWord_toInt {α : Type} (l : List α) (h : l.length ≤ 4096) :
    (lenWord l).toInt = l.length := by
  simp only [lenWord, zw, BitVec.toInt_ofInt, Int.bmod]
  split <;> omega

/-! ## Reading until `FIN` -/

theorem readLoop (q : NetQueue) : ∀ (n : Nat) (rest : List LPS.Byte),
    rest.length ≤ n → ∀ st : St, st.pc = .read → st.conn = 4 → st.out = [] →
    ∃ h st', HStar (isa := isa) [] serverSpec noFilter ⟨st, mConn q (ofListFin rest)⟩ h
        ⟨st', mConn q (ofListFin [])⟩ ∧
      st'.pc = .read ∧ st'.conn = 4 ∧ st'.acc = st.acc ++ rest ∧ st'.out = [] ∧
      byteTrace h = rest.map (.readEv 3) ∧ (∀ r ∈ h, accepts genericAccept r = false)
  | n, [], _, st, hp, hc, ho => ⟨[], st, .refl _, hp, hc, by simp, ho, rfl, by simp⟩
  | 0, _ :: _, hn, _, _, _, _ => absurd hn (by simp)
  | n + 1, b :: rest, hn, st, hp, hc, ho => by
    have hne : b :: rest ≠ [] := List.cons_ne_nil _ _
    obtain ⟨bs, hbs⟩ : ∃ bs, (b :: rest).take 4096 = bs := ⟨_, rfl⟩
    obtain ⟨rest', hrest⟩ : ∃ r, (b :: rest).drop 4096 = r := ⟨_, rfl⟩
    have hlen : bs.length ≤ 4096 := hbs ▸ List.length_take_le _ _
    have hpos : 0 < bs.length := by rw [← hbs]; simp
    have hsplit : bs ++ rest' = b :: rest := by rw [← hbs, ← hrest, List.take_append_drop]
    have hlt : rest'.length ≤ n := by
      have := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons] at this hn
      omega
    have ha : args st = [4, BUF, BitVec.ofNat 64 4096, 0, 0, 0] := by simp [args, hp, hc]
    have hs := read_ok (fd := 4) ⟨63, args st, readByte st, writableByte⟩
      (mConn q (ofListFin (b :: rest))) (nqPeer q) 3 (b :: rest) hne bs rest' hbs hrest rfl
      (fdLookup_connFds q _)
    rw [mConn_withFds] at hs
    have hs' : serverSpec ⟨63, args st, readByte st, writableByte⟩
        (mConn q (ofListFin (b :: rest)))
        (.ok (mkEffect (lenWord bs) [(BUF, bs)] []) (mConn q (ofListFin rest'))
          (bs.map (.readEv 3))) := by
      rw [ha] at hs ⊢
      show readSpec (fd32 4) BUF (BitVec.ofNat 64 4096) _ _ _
      rw [fd32_four]
      exact hs
    obtain ⟨st1, hst1⟩ : ∃ s : St,
        s = advance (setRet st (lenWord bs) ([(BUF, bs)].flatMap fun p => p.2)) := ⟨_, rfl⟩
    have s1 : LStep (isa := isa) [] serverSpec noFilter ⟨st, mConn q (ofListFin (b :: rest))⟩
        (.syscall 63 (args st) (mkEffect (lenWord bs) [(BUF, bs)] []) (bs.map (.readEv 3)))
        ⟨st1, mConn q (ofListFin rest')⟩ := by
      rw [hst1]
      exact sys_step st 63 (by simp [pending, hp]) _ _ _ _ hs' rfl rfl rfl
    have hp1 : st1.pc = .readDone := by simp [hst1, advance, setRet, hp]
    have s2 := instr_step st1 (by simp [pending, hp1]) (mConn q (ofListFin rest')) rfl rfl
    have hret : 0 < st1.ret.toInt := by
      have : st1.ret = lenWord bs := by simp [hst1, advance, setRet, hp]
      rw [this, lenWord_toInt _ hlen]
      omega
    have hn2 : (next st1).pc = .read ∧ (next st1).conn = 4 ∧
        (next st1).acc = st.acc ++ bs ∧ (next st1).out = [] := by
      simp only [next, hp1, hret, ↓reduceIte]
      simp [hst1, advance, setRet, hp, hc, ho]
    obtain ⟨h', st', hs3, hp', hc', ha', ho', hb', hacc'⟩ :=
      readLoop q n rest' hlt (next st1) hn2.1 hn2.2.1 hn2.2.2.2
    refine ⟨_ :: .instr :: h', st', .step s1 (.step s2 hs3), hp', hc', ?_, ho', ?_, ?_⟩
    · rw [ha', hn2.2.2.1, List.append_assoc, hsplit]
    · simp only [byteTrace, List.flatMap_cons, StepRecord.events, List.nil_append] at hb' ⊢
      rw [hb', ← List.map_append, hsplit]
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · simp [accepts, genericAccept]
      · rfl
      · exact hacc' r hr


/-! ## Sending everything -/

theorem sendLoop (q : NetQueue) : ∀ (n : Nat) (out : List LPS.Byte), out.length ≤ n →
    ∀ st : St, st.pc = (if out = [] then .close else .send) → st.conn = 4 → st.out = out →
    ∃ h st', HStar (isa := isa) [] serverSpec noFilter ⟨st, mConn q (ofListFin [])⟩ h
        ⟨st', mConn q (ofListFin [])⟩ ∧
      st'.pc = .close ∧ byteTrace h = out.map (.writeEv 3) ∧
      (∀ r ∈ h, accepts genericAccept r = false)
  | n, [], _, st, hp, _, _ => ⟨[], st, .refl _, by simpa using hp, rfl, by simp⟩
  | 0, _ :: _, hn, _, _, _, _ => absurd hn (by simp)
  | n + 1, b :: rest, hn, st, hp, hc, ho => by
    have hne : b :: rest ≠ [] := List.cons_ne_nil _ _
    have hp0 : st.pc = .send := by simpa using hp
    obtain ⟨bs, hbs⟩ : ∃ bs, (b :: rest).take 4096 = bs := ⟨_, rfl⟩
    obtain ⟨rest', hrest⟩ : ∃ r, (b :: rest).drop bs.length = r := ⟨_, rfl⟩
    have hlen : bs.length ≤ 4096 := hbs ▸ List.length_take_le _ _
    have hpos : 0 < bs.length := by rw [← hbs]; simp
    have hpre : bs = (b :: rest).take bs.length :=
      List.prefix_iff_eq_take.1 (hbs ▸ List.take_prefix _ _)
    have hsplit : bs ++ rest' = b :: rest := by
      rw [← hrest]
      calc bs ++ (b :: rest).drop bs.length
          = (b :: rest).take bs.length ++ (b :: rest).drop bs.length := by rw [← hpre]
        _ = b :: rest := List.take_append_drop _ _
    have hlt : rest'.length ≤ n := by
      have := congrArg List.length hsplit
      simp only [List.length_append, List.length_cons] at this hn
      omega
    obtain ⟨eff, hs, hr, hw⟩ := sendto_ok (fd := 4) ⟨206, args st, readByte st, writableByte⟩
      (mConn q (ofListFin [])) (nqPeer q) 3 st rfl (by rw [ho]; exact hne) bs (by rw [ho, hbs])
      (fdLookup_connFds q _)
    have ha : args st = [4, OUT, BitVec.ofNat 64 (min st.out.length 4096), NOSIG, 0, 0] := by
      simp [args, hp0, hc]
    have hs' : serverSpec ⟨206, args st, readByte st, writableByte⟩ (mConn q (ofListFin []))
        (.ok eff (mConn q (ofListFin [])) (bs.map (.writeEv 3))) := by
      rw [ha] at hs ⊢
      show sendtoSpec (fd32 4) OUT (BitVec.ofNat 64 (min st.out.length 4096)) NOSIG 0 0 _ _ _
      rw [fd32_four]
      exact hs
    obtain ⟨st1, hst1⟩ : ∃ s : St,
        s = advance (setRet st (lenWord bs) ([] : List LPS.Byte)) := ⟨_, rfl⟩
    have s1 : LStep (isa := isa) [] serverSpec noFilter ⟨st, mConn q (ofListFin [])⟩
        (.syscall 206 (args st) eff (bs.map (.writeEv 3))) ⟨st1, mConn q (ofListFin [])⟩ := by
      have := sys_step st 206 (by simp [pending, hp0]) _ _ _ _ hs' rfl rfl rfl
      rw [hr, hw] at this
      rw [hst1]
      exact this
    have hp1 : st1.pc = .sent := by simp [hst1, advance, setRet, hp0]
    have s2 := instr_step st1 (by simp [pending, hp1]) (mConn q (ofListFin [])) rfl rfl
    have hret1 : st1.ret = lenWord bs := by simp [hst1, advance, setRet, hp0]
    have hret : 0 < st1.ret.toInt := by
      rw [hret1, lenWord_toInt _ hlen]
      omega
    have hrn : st1.ret.toNat = bs.length := by
      rw [hret1, lenWord_toNat _ (by omega)]
    have hn2 : (next st1).pc = (if rest' = [] then .close else .send) ∧ (next st1).conn = 4 ∧
        (next st1).out = rest' := by
      simp only [next, hp1, hret, ↓reduceIte]
      have ho1 : st1.out = b :: rest := by simp [hst1, advance, setRet, hp0, ho]
      have hc1 : st1.conn = 4 := by simp [hst1, advance, setRet, hp0, hc]
      rw [ho1, hrn, hrest, hc1]
      exact ⟨rfl, rfl, rfl⟩
    obtain ⟨h', st', hs3, hp', hb', hacc'⟩ :=
      sendLoop q n rest' hlt (next st1) hn2.1 hn2.2.1 hn2.2.2
    refine ⟨_ :: .instr :: h', st', .step s1 (.step s2 hs3), hp', ?_, ?_⟩
    · simp only [byteTrace, List.flatMap_cons, StepRecord.events, List.nil_append] at hb' ⊢
      rw [hb', ← List.map_append, hsplit]
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | rfl | hr
      · simp [accepts, genericAccept]
      · rfl
      · exact hacc' r hr


/-! ## Reading the trace -/

theorem accepted_append (a b : List SockEv) : accepted (a ++ b) = accepted a ++ accepted b := by
  induction a with
  | nil => rfl
  | cons e a ih => cases e <;> simp [accepted, ih]

theorem accepted_ofEvents (evs : List Event) : accepted (ofEvents evs) = [] := by
  induction evs with
  | nil => rfl
  | cons e evs ih =>
    rw [Silmaril.Servers.Sockets.ofEvents_cons, accepted_append, ih, List.append_nil]
    cases e with
    | readEv ch b => cases h : connOf ch <;> simp [ofEvent, h, accepted]
    | writeEv ch b => cases h : connOf ch <;> simp [ofEvent, h, accepted]
    | exitEv => rfl
    | killEv => rfl

theorem accepted_ofRecordsC (isAccept isClose : Word → Bool) :
    ∀ (n : Nat) (fds : List (Word × ConnId)) (h : List StepRecord),
      accepted (ofRecordsC isAccept isClose n fds h) = List.range' n (acceptCount isAccept h)
  | _, _, [] => rfl
  | n, fds, r :: rs => by
    rw [Silmaril.Servers.Sockets.acceptCount_cons]
    unfold ofRecordsC
    split
    · next ha =>
      show n :: accepted (ofEvents r.events ++ _) = _
      rw [accepted_append, accepted_ofEvents, List.nil_append,
        accepted_ofRecordsC isAccept isClose (n + 1) _ rs, Nat.add_comm 1, List.range'_succ]
    · next ha =>
      rw [Nat.zero_add]
      split
      · rw [accepted_append, accepted_ofEvents, List.nil_append]
        exact accepted_ofRecordsC isAccept isClose n _ rs
      · rw [accepted_append, accepted_ofEvents, List.nil_append]
        exact accepted_ofRecordsC isAccept isClose n _ rs

theorem acceptCount_zero {isAccept : Word → Bool} {h : List StepRecord}
    (hh : ∀ r ∈ h, accepts isAccept r = false) : acceptCount isAccept h = 0 := by
  simp only [acceptCount, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro r hr
  simp [hh r hr]

theorem recvBytes_append (c : ConnId) (a b : List Event) :
    recvBytes c (a ++ b) = recvBytes c a ++ recvBytes c b := List.flatMap_append

theorem sentBytes_append (c : ConnId) (a b : List Event) :
    sentBytes c (a ++ b) = sentBytes c a ++ sentBytes c b := List.flatMap_append

theorem connOf_three : connOf 3 = some 0 := by decide

theorem recvBytes_readEv (l : List LPS.Byte) :
    recvBytes 0 (l.map (.readEv 3)) = l.map Silmaril.Servers.Sockets.byte := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons]
    rw [show (Event.readEv 3 b :: l.map (.readEv 3)) = [.readEv 3 b] ++ l.map (.readEv 3) from rfl,
      recvBytes_append, ih]
    simp [recvBytes, connOf]

theorem recvBytes_writeEv (l : List LPS.Byte) : recvBytes 0 (l.map (.writeEv 3)) = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons]
    rw [show (Event.writeEv 3 b :: l.map (.writeEv 3)) = [.writeEv 3 b] ++ l.map (.writeEv 3)
      from rfl, recvBytes_append, ih]
    rfl

theorem sentBytes_writeEv (l : List LPS.Byte) :
    sentBytes 0 (l.map (.writeEv 3)) = l.map Silmaril.Servers.Sockets.byte := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons]
    rw [show (Event.writeEv 3 b :: l.map (.writeEv 3)) = [.writeEv 3 b] ++ l.map (.writeEv 3)
      from rfl, sentBytes_append, ih]
    simp [sentBytes, connOf]

theorem sentBytes_readEv (l : List LPS.Byte) : sentBytes 0 (l.map (.readEv 3)) = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons]
    rw [show (Event.readEv 3 b :: l.map (.readEv 3)) = [.readEv 3 b] ++ l.map (.readEv 3) from rfl,
      sentBytes_append, ih]
    rfl

theorem ofBitVec_toBitVec_map (l : List UInt8) : (l.map UInt8.toBitVec).map UInt8.ofBitVec = l := by
  simp [List.map_map, Function.comp_def]

theorem byte_toBitVec (l : List UInt8) :
    (l.map UInt8.toBitVec).map Silmaril.Servers.Sockets.byte = l :=
  ofBitVec_toBitVec_map l

/-! ## The requests on the wire are all answered -/

theorem takeWhile_all {α : Type} {p : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = true) →
    l.takeWhile p = l
  | [], _ => rfl
  | x :: l, h => by
    rw [List.takeWhile_cons, ite_eq_left (h x List.mem_cons_self),
      takeWhile_all fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem helloCount_encode (ms : List WireReq) (hms : ∀ m ∈ ms, WireOk m) :
    helloCount (encRequests ms) = ms.length := by
  unfold helloCount
  rw [requests_encode ms (fun m hm => (hms m hm).1)]
  rw [takeWhile_all]
  · simp
  · intro r hr
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hr
    obtain ⟨-, h1, h2⟩ := hms m hm
    simp [answerable, method_toRequest, h1, h2]

/-! ## The run -/

/-- The connection queue whose first client sends `bs` and then `FIN`. -/
def queue (bs : List LPS.Byte) : NetQueue := fun _ => (⟨0, 0⟩, ofListFin bs)

theorem serves (inp : Cli.Input) : ServesHello L inp := by
  intro ms hms
  set bytes := (encRequests ms).map UInt8.toBitVec with hbytes
  set q := queue bytes with hq
  -- accept
  have hA : serverSpec ⟨202, args ⟨.accept, 0, [], [], 0, []⟩, readByte ⟨.accept, 0, [], [], 0, []⟩,
      writableByte⟩ (model0 q) (.ok (mkEffect 4 [] []) (mConn q (ofListFin bytes)) []) := by
    show accept4Spec (fd32 3) 0 0 0 _ _ _
    rw [fd32_three]
    exact accept_ok _ (model0 q) rfl rfl rfl 4 rfl rfl
  have s1 := sys_step ⟨.accept, 0, [], [], 0, []⟩ 202 rfl _ _ _ _ hA rfl rfl rfl
  obtain ⟨st1, hst1⟩ : ∃ s : St, s = advance (setRet ⟨.accept, 0, [], [], 0, []⟩ 4 []) :=
    ⟨_, rfl⟩
  have s1' : LStep (isa := isa) [] serverSpec noFilter ⟨⟨.accept, 0, [], [], 0, []⟩, model0 q⟩
      (.syscall 202 (args ⟨.accept, 0, [], [], 0, []⟩) (mkEffect 4 [] []) [])
      ⟨st1, mConn q (ofListFin bytes)⟩ := by
    rw [hst1]; exact s1
  have s2 := instr_step st1 (by simp [hst1, pending, advance, setRet])
    (mConn q (ofListFin bytes)) rfl rfl
  have hn1 : (next st1).pc = .read ∧ (next st1).conn = 4 ∧ (next st1).out = [] ∧
      (next st1).acc = [] := by
    have hr : (0 : Int) ≤ st1.ret.toInt := by simp [hst1, advance, setRet]
    simp [next, hst1, advance, setRet]
  -- read everything
  obtain ⟨hR, stR, sR, hpR, hcR, haR, hoR, hbR, haccR⟩ :=
    readLoop q bytes.length bytes le_rfl (next st1) hn1.1 hn1.2.1 hn1.2.2.1
  -- read FIN
  have haR' : args stR = [4, BUF, BitVec.ofNat 64 4096, 0, 0, 0] := by simp [args, hpR, hcR]
  have hF : serverSpec ⟨63, args stR, readByte stR, writableByte⟩ (mConn q (ofListFin []))
      (.ok (mkEffect 0 [] []) (mConn q (ofListFin [])) []) := by
    rw [haR']
    show readSpec (fd32 4) BUF (BitVec.ofNat 64 4096) _ _ _
    rw [fd32_four]
    exact read_fin _ _ _ _ (fdLookup_connFds q _)
  obtain ⟨st3, hst3⟩ : ∃ s : St, s = advance (setRet stR 0 []) := ⟨_, rfl⟩
  have s3 : LStep (isa := isa) [] serverSpec noFilter ⟨stR, mConn q (ofListFin [])⟩
      (.syscall 63 (args stR) (mkEffect 0 [] []) []) ⟨st3, mConn q (ofListFin [])⟩ := by
    rw [hst3]; exact sys_step stR 63 (by simp [pending, hpR]) _ _ _ _ hF rfl rfl rfl
  have hp3 : st3.pc = .readDone := by simp [hst3, advance, setRet, hpR]
  have s4 := instr_step st3 (by simp [pending, hp3]) (mConn q (ofListFin [])) rfl rfl
  set out := (helloOut (helloCount (stR.acc.map UInt8.ofBitVec))).map UInt8.toBitVec with hout
  have hn4 : (next st3).pc = (if out = [] then .close else .send) ∧ (next st3).conn = 4 ∧
      (next st3).out = out := by
    have h0 : st3.ret = 0 := by simp [hst3, advance, setRet, hpR]
    have h0' : ¬ (0 : Int) < st3.ret.toInt := by rw [h0]; decide
    simp only [next, hp3, h0, ↓reduceIte]
    have ha3 : st3.acc = stR.acc := by simp [hst3, advance, setRet, hpR]
    have hc3 : st3.conn = 4 := by simp [hst3, advance, setRet, hpR, hcR]
    rw [ha3, hc3]
    exact ⟨rfl, rfl, rfl⟩
  -- send everything
  obtain ⟨hS, stS, sS, -, hbS, haccS⟩ :=
    sendLoop q out.length out le_rfl (next st3) hn4.1 hn4.2.1 hn4.2.2
  -- the trace
  let h := (.syscall 202 (args ⟨.accept, 0, [], [], 0, []⟩) (mkEffect 4 [] []) [] :: .instr ::
    hR) ++ (.syscall 63 (args stR) (mkEffect 0 [] []) [] :: .instr :: hS)
  have hrun : HStar (isa := isa) [] serverSpec noFilter (launch inp q) h ⟨stS, mConn q (ofListFin [])⟩ :=
    hstar_append (.step s1' (.step s2 sR)) (.step s3 (.step s4 sS))
  have hbt : byteTrace h = bytes.map (.readEv 3) ++ out.map (.writeEv 3) := by
    simp only [h, byteTrace, List.flatMap_append, List.flatMap_cons, StepRecord.events,
      List.nil_append] at hbR hbS ⊢
    rw [hbR, hbS]
  have hacc : stR.acc.map UInt8.ofBitVec = encRequests ms := by
    rw [haR, hn1.2.2.2, List.nil_append, hbytes]
    exact ofBitVec_toBitVec_map (encRequests ms)
  refine ⟨ofRecordsC genericAccept genericClose 0 [] h, ⟨q, h, _, hrun, rfl⟩, ?_, ?_, ?_⟩
  · rw [accepted_ofRecordsC]
    have : acceptCount genericAccept h = 1 := by
      simp only [h, List.cons_append]
      rw [Silmaril.Servers.Sockets.acceptCount_cons, acceptCount_zero]
      · simp [accepts, genericAccept, mkEffect]
      · intro r hr
        simp only [List.mem_cons, List.mem_append] at hr
        rcases hr with rfl | hr | rfl | rfl | hr
        · rfl
        · exact haccR r hr
        · simp [accepts, genericAccept]
        · rfl
        · exact haccS r hr
    rw [this]
    rfl
  · rw [Silmaril.Servers.Sockets.received_ofRecordsC, hbt, recvBytes_append, recvBytes_readEv,
      recvBytes_writeEv, List.append_nil, hbytes, byte_toBitVec]
  · rw [Silmaril.Servers.Sockets.sent_ofRecordsC, hbt, sentBytes_append, sentBytes_readEv,
      sentBytes_writeEv, List.nil_append, hout, byte_toBitVec, hacc, helloCount_encode ms hms,
      helloOut, List.map_const']

end Silmaril.Proofs.Servers.LinuxHello
