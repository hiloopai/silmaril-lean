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

end Silmaril.Proofs.Servers.LinuxHello
