module

public import Silmaril.Servers.Sockets.Defs
public import Silmaril.Process.LPS.Sys.Socket
public import Silmaril.Process.LPS.Sys.Kernel
public import Silmaril.Proofs.Servers.Sockets.Basic

/-!
# Socket events of a Linux process: accepts, channels, `close` and `recvfrom` (proofs)

For `Silmaril.Servers.Sockets.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Sockets

open Silmaril.Process Silmaril.Process.LPS Silmaril.Servers.Platform Silmaril.Servers.Sockets

/-! ## Elimination lemmas for the specification monad -/

theorem bind_ok_iff {α β : Type} (c : Sys α) (k : α → Sys β) (i : SyscallInput) (m : Model)
    (y : β) (m₂ : Model) (evs : List Event) :
    (c >>= k) i m (.ok y m₂ evs) ↔
      ∃ x m₁ evs₁ evs₂, c i m (.ok x m₁ evs₁) ∧ k x i m₁ (.ok y m₂ evs₂) ∧ evs = evs₁ ++ evs₂ :=
  Iff.rfl

theorem retOnly_ok {r : Word} {i : SyscallInput} {m : Model} {eff : SyscallEffect} {m' : Model}
    {evs : List Event} (h : retOnly r i m (.ok eff m' evs)) :
    eff = mkEffect r [] [] ∧ m' = m ∧ evs = [] := by
  simp only [retOnly, Sys.pure, Outcome.ok.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem errRet_ok {e : Int} {i : SyscallInput} {m : Model} {eff : SyscallEffect} {m' : Model}
    {evs : List Event} (h : errRet e i m (.ok eff m' evs)) :
    eff.ret = errnoRet e ∧ m' = m ∧ evs = [] := by
  obtain ⟨rfl, rfl, rfl⟩ := retOnly_ok h
  exact ⟨rfl, rfl, rfl⟩

theorem unmodeled_ok {α : Type} {i : SyscallInput} {m : Model} {x : α} {m' : Model}
    {evs : List Event} (h : (Sys.unmodeled : Sys α) i m (.ok x m' evs)) : False := by
  cases h

/-- An errno return is negative. -/
theorem errnoRet_neg {e : Int} (h₁ : 0 < e) (h₂ : e < 4096) : ¬ 0 ≤ (errnoRet e).toInt := by
  simp only [errnoRet, zw, BitVec.toInt_ofInt, Int.bmod]
  split <;> omega

theorem errRet_ok_neg {e : Int} {i : SyscallInput} {m : Model} {eff : SyscallEffect}
    {m' : Model} {evs : List Event} (h : errRet e i m (.ok eff m' evs)) (h₁ : 0 < e)
    (h₂ : e < 4096) : ¬ 0 ≤ eff.ret.toInt := by
  rw [(errRet_ok h).1]
  exact errnoRet_neg h₁ h₂

/-! ## `accept4` -/

theorem accept4Spec_ok {fd addrp addrlenp flags : Word} {i : SyscallInput} {m : Model}
    {eff : SyscallEffect} {m' : Model} {evs : List Event}
    (h : accept4Spec fd addrp addrlenp flags i m (.ok eff m' evs)) (hr : 0 ≤ eff.ret.toInt) :
    m'.io.connIx = m.io.connIx + 1 ∧ evs = [] ∧ m'.io.net = nqRest m.io.net ∧
      fdLookup m'.fd.table eff.ret =
        some (.socket (.connected (nqPeer m.io.net) (connChannel m.io.connIx)
          (nqScript m.io.net))) := by
  unfold accept4Spec at h
  have h := (Sys.bind_getModel _ i m _).1 h
  beta_reduce at h
  rcases hf : fdLookup m.fds fd with _ | e <;> simp only [hf] at h
  · exact absurd hr (errRet_ok_neg h (by decide) (by decide))
  split at h
  · exact absurd hr (errRet_ok_neg h (by decide) (by decide))
  split at h
  · exact (unmodeled_ok h).elim
  cases e
  all_goals dsimp only at h
  all_goals try exact absurd hr (errRet_ok_neg h (by decide) (by decide))
  rename_i sk
  split at h
  · exact (unmodeled_ok h).elim
  cases sk
  all_goals dsimp only at h
  all_goals try exact absurd hr (errRet_ok_neg h (by decide) (by decide))
  rcases h with h | h
  · obtain ⟨x, m₁, e₁, e₂, hx, hk, -⟩ := h
    obtain ⟨y, hy, hxy⟩ := hx
    simp only [Outcome.ok.injEq] at hxy
    obtain ⟨rfl, rfl, rfl⟩ := hxy
    simp only [acceptErrnos, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;>
      exact absurd hr (errRet_ok_neg hk (by decide) (by decide))
  · split at h
    · obtain ⟨_, hf, _⟩ := h
      exact hf.elim
    · obtain ⟨x, m₁, e₁, e₂, hx, hk, rfl⟩ := h
      obtain ⟨y, -, hxy⟩ := hx
      simp only [Outcome.ok.injEq] at hxy
      obtain ⟨rfl, rfl, rfl⟩ := hxy
      obtain ⟨u, m₂, e₃, e₄, hm, hk, rfl⟩ := hk
      simp only [Sys.modify, Outcome.ok.injEq] at hm
      obtain ⟨-, rfl, rfl⟩ := hm
      obtain ⟨rfl, rfl, rfl⟩ := retOnly_ok hk
      refine ⟨rfl, rfl, rfl, ?_⟩
      simp [Model.withAccepted, mkEffect, fdLookup, fdInsert, Model.connIx, Model.net]

/-! ## `close` and `recvfrom` -/

theorem closeSpec_ok {fd : Word} {i : SyscallInput} {m : Model} {eff : SyscallEffect}
    {m' : Model} {evs : List Event} (h : closeSpec fd i m (.ok eff m' evs)) :
    evs = [] ∧ m'.io = m.io ∧
      (eff.ret = 0 → m'.fd.table = fdRemove m.fd.table fd) := by
  unfold closeSpec at h
  have h := (Sys.bind_getModel _ i m _).1 h
  beta_reduce at h
  rcases hf : fdLookup m.fds fd with _ | e <;> simp only [hf] at h
  · obtain ⟨hret, rfl, rfl⟩ := errRet_ok h
    refine ⟨rfl, rfl, fun h0 => absurd (hret.symm.trans h0) (by decide)⟩
  · obtain ⟨u, m₂, e₃, e₄, hm, hk, rfl⟩ := h
    simp only [Sys.modify, Outcome.ok.injEq] at hm
    obtain ⟨-, rfl, rfl⟩ := hm
    obtain ⟨rfl, rfl, rfl⟩ := retOnly_ok hk
    exact ⟨rfl, rfl, fun _ => rfl⟩

theorem recvFdAnswer_ok {fds : List (Word × FdEntry)} {fd : Word} {i : SyscallInput} {m : Model}
    {eff : SyscallEffect} {m' : Model} {evs : List Event}
    (h : recvFdAnswer fds fd i m (.ok eff m' evs)) : evs = [] ∧ m' = m := by
  unfold recvFdAnswer at h
  rcases hf : sockfdLookupErrno fds fd with _ | e <;> simp only [hf] at h
  · exact (unmodeled_ok h).elim
  · obtain ⟨-, rfl, rfl⟩ := errRet_ok h
    exact ⟨rfl, rfl⟩

theorem recvfromSpec_ok {fd buf size : Word} {i : SyscallInput} {m : Model}
    {eff : SyscallEffect} {m' : Model} {evs : List Event}
    (h : recvfromSpec fd buf size i m (.ok eff m' evs)) : evs = [] ∧ m' = m := by
  unfold recvfromSpec recvfromSpecWith at h
  split at h
  · exact (unmodeled_ok h).elim
  · have h := (Sys.bind_getModel _ i m _).1 h
    beta_reduce at h
    unfold accessOkZero at h
    split at h
    · exact recvFdAnswer_ok h
    · obtain ⟨-, rfl, rfl⟩ := errRet_ok h
      exact ⟨rfl, rfl⟩

theorem recvmsgSpec_ok {fd flags : Word} {i : SyscallInput} {m : Model}
    {eff : SyscallEffect} {m' : Model} {evs : List Event}
    (h : recvmsgSpec fd flags i m (.ok eff m' evs)) : evs = [] ∧ m' = m := by
  unfold recvmsgSpec at h
  split at h
  · exact (unmodeled_ok h).elim
  · have h := (Sys.bind_getModel _ i m _).1 h
    beta_reduce at h
    exact recvFdAnswer_ok h

/-! ## Counting accepts along a run -/

theorem materialize_io {m : Model} {acc : List (Word × Nat)} {m' : Model}
    (h : materializeModelAccesses m acc = some m') : m'.io = m.io := by
  unfold materializeModelAccesses at h
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

theorem accountStep_io {isa : UserIsa} {segs : List Segment} {ms : isa.State} {model : Model}
    {ms' : isa.State} {model' : Model} (h : accountStep isa segs ms model = .ok (ms', model')) :
    model'.io = model.io := by
  unfold accountStep at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
        exact materialize_io (by assumption)
      · cases h
    · cases h
    · cases h

theorem acceptCount_cons (isAccept : Word → Bool) (r : StepRecord) (h : List StepRecord) :
    acceptCount isAccept (r :: h) = (if accepts isAccept r then 1 else 0) + acceptCount isAccept h := by
  unfold acceptCount
  cases hr : accepts isAccept r <;> simp [hr, Nat.add_comm]

theorem connIx_hstar {isa : UserIsa} {segs : List Segment} {spec : Sys SyscallEffect}
    {refused : RefusalFilter} {isAccept : Word → Bool} (hc : CountsConns spec isAccept)
    {c c' : Config isa} {h : List StepRecord} (s : HStar segs spec refused c h c') :
    c'.model.io.connIx.toNat = (c.model.io.connIx.toNat + acceptCount isAccept h) % 2 ^ 64 := by
  induction s with
  | refl c =>
    simp only [acceptCount, List.filter_nil, List.length_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt c.model.io.connIx.isLt).symm
  | @step c₁ r c₂ h c₃ st _ ih =>
    rw [ih, acceptCount_cons]
    have key : c₂.model.io.connIx =
        if accepts isAccept r then c₁.model.io.connIx + 1 else c₁.model.io.connIx := by
      cases st with
      | instr _ _ ha =>
        simp only [accepts, Bool.false_eq_true, ↓reduceIte]
        exact congrArg IoState.connIx (accountStep_io ha)
      | syscall _ _ hs _ _ hm =>
        rw [congrArg IoState.connIx (materialize_io hm), hc _ _ _ _ _ hs]
        rfl
      | exit _ _ hs _ _ => exact hc _ _ _ _ _ hs
      | killed _ _ hs _ => exact hc _ _ _ _ _ hs
    rw [key]
    split
    · have h1 : (1 : Word).toNat = 1 := rfl
      rw [BitVec.toNat_add, h1]
      omega
    · omega

/-! ## Reading `close` does not change the octets -/

theorem received_ofRecordsC (isAccept isClose : Word → Bool) (c : ConnId) :
    ∀ (n : Nat) (fds : List (Word × ConnId)) (h : List StepRecord),
      received c (ofRecordsC isAccept isClose n fds h) = received c (ofEvents (byteTrace h))
  | _, _, [] => rfl
  | n, fds, r :: rs => by
    rw [Silmaril.Proofs.Servers.Sockets.ofEvents_byteTrace, received_append]
    unfold ofRecordsC
    split
    · show received c (ofEvents r.events ++ _) = _
      rw [received_append, received_ofRecordsC isAccept isClose c _ _ rs]
    · split
      · rw [received_append]
        show _ ++ received c (ofRecordsC isAccept isClose n _ rs) = _
        rw [received_ofRecordsC isAccept isClose c _ _ rs]
      · rw [received_append, received_ofRecordsC isAccept isClose c _ _ rs]

theorem sent_ofRecordsC (isAccept isClose : Word → Bool) (c : ConnId) :
    ∀ (n : Nat) (fds : List (Word × ConnId)) (h : List StepRecord),
      sent c (ofRecordsC isAccept isClose n fds h) = sent c (ofEvents (byteTrace h))
  | _, _, [] => rfl
  | n, fds, r :: rs => by
    rw [Silmaril.Proofs.Servers.Sockets.ofEvents_byteTrace, sent_append]
    unfold ofRecordsC
    split
    · show sent c (ofEvents r.events ++ _) = _
      rw [sent_append, sent_ofRecordsC isAccept isClose c _ _ rs]
    · split
      · rw [sent_append]
        show _ ++ sent c (ofRecordsC isAccept isClose n _ rs) = _
        rw [sent_ofRecordsC isAccept isClose c _ _ rs]
      · rw [sent_append, sent_ofRecordsC isAccept isClose c _ _ rs]

end Silmaril.Proofs.Servers.Sockets
