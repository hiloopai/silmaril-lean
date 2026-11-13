module

public import Silmaril.X86.Concurrency.Cir.Proc.Lps.Defs
public import Silmaril.Process.LpsBridge.Threads.Thms
public import Silmaril.Process.LPS.ExitBridge

/-!
# Proofs: the arms LPS shares with the thread layer

`exit_dispatch` repeats the proof of the LPS bridge's private lemma
of the same name (`Silmaril.Proofs.Process.LpsBridge.Syscall`), which another topic may
not import.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps

open Silmaril.Process.LPS
open Silmaril.Process.LpsBridge (spec)
open Silmaril.X86.Concurrency.Cir.Proc
open Silmaril.X86.Concurrency.Cir.Proc.Lps

theorem gettid_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 186) :
    spec i m o = setTidAddressSpec (NativeX86.referenceInputFor ⟨178, 186, "gettid"⟩ i) m o := by
  unfold spec NativeX86.extendedSyscallSpec dispatch
  rw [h]
  rfl

theorem setTid_dispatch (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : i.sysno.toNat = 218) :
    spec i m o =
      setTidAddressSpec (NativeX86.referenceInputFor ⟨96, 218, "set_tid_address"⟩ i) m o := by
  unfold spec NativeX86.extendedSyscallSpec dispatch
  rw [h]
  rfl

theorem setTid_pinned (i : SyscallInput) (m : Model) (t : Word) (ht : m.tid = some t)
    (o : Outcome SyscallEffect) :
    setTidAddressSpec i m o ↔ o = .ok (mkEffect t [] []) m [] := by
  unfold setTidAddressSpec
  cases o with
  | ok eff m' evs =>
    constructor
    · rintro ⟨x, m₁, evs₁, evs₂, get, rest, rfl⟩
      cases get
      simp only [ht] at rest
      cases rest; rfl
    · intro h; cases h
      exact ⟨m, m, [], [], rfl, by simp only [ht]; rfl, rfl⟩
  | unmodeled =>
    simp only [reduceCtorEq, iff_false]
    rintro (get | ⟨x, m₁, evs₁, get, rest⟩)
    · cases get
    · cases get; simp only [ht] at rest; cases rest

theorem setTid_fresh (i : SyscallInput) (m : Model) (ht : m.tid = none)
    (o : Outcome SyscallEffect) :
    setTidAddressSpec i m o ↔ ∃ tid : Word, 0 < uns tid ∧ uns tid < PID_MAX_ENVELOPE ∧
      o = .ok (mkEffect tid [] []) (m.withTid tid) [] := by
  unfold setTidAddressSpec
  constructor
  · intro spec
    cases o with
    | ok eff model' evs =>
      obtain ⟨x, m₁, evs₁, evs₂, get, rest, events⟩ := spec
      cases get
      simp only [ht] at rest
      obtain ⟨tid, m₂, evs₃, evs₄, ⟨t, valid, chosen⟩, rest, events'⟩ := rest
      cases chosen
      obtain ⟨u, m₃, evs₅, evs₆, modified, returned, events''⟩ := rest
      cases modified; cases returned
      subst events events' events''
      exact ⟨_, valid.1, valid.2, rfl⟩
    | unmodeled =>
      rcases spec with get | ⟨x, m₁, evs₁, get, rest⟩
      · cases get
      · cases get
        simp only [ht] at rest
        rcases rest with ⟨t, _, chosen⟩ | ⟨tid, m₂, evs₃, ⟨t, _, chosen⟩, rest⟩
        · cases chosen
        · cases chosen
          rcases rest with modified | ⟨u, m₃, evs₅, modified, returned⟩
          · cases modified
          · cases returned
  · rintro ⟨tid, h0, h1, rfl⟩
    refine ⟨m, m, [], [], rfl, ?_, rfl⟩
    simp only [ht]
    exact ⟨tid, m, [], [], ⟨tid, ⟨h0, h1⟩, rfl⟩, ⟨(), m.withTid tid, [], [], rfl, rfl, rfl⟩, rfl⟩

theorem tidArm_gettid : TidArm nrGettid := fun i m t o hn ht => by
  rw [gettid_dispatch i m o hn]; exact setTid_pinned _ m t ht o

theorem tidArm_setTid : TidArm nrSetTid := fun i m t o hn ht => by
  rw [setTid_dispatch i m o hn]; exact setTid_pinned _ m t ht o

theorem tidArmFresh_gettid : TidArmFresh nrGettid := fun i m o hn ht => by
  rw [gettid_dispatch i m o hn]; exact setTid_fresh _ m ht o

theorem tidArmFresh_setTid : TidArmFresh nrSetTid := fun i m o hn ht => by
  rw [setTid_dispatch i m o hn]; exact setTid_fresh _ m ht o

theorem exitArm : ExitArm := by
  intro i m o number
  rcases number with number | number
  · simp only [spec, NativeX86.extendedSyscallSpec, dispatch, nrExit] at number ⊢
    simp only [number]
    exact ExitBridge.exitSpec_iff (i.arg 0) _ m o
  · simp only [spec, NativeX86.extendedSyscallSpec, dispatch, nrExitGroup] at number ⊢
    simp only [number]
    exact ExitBridge.exitSpec_iff (i.arg 0) _ m o

theorem pendingArms : PendingArms := by
  intro i m h
  rcases h with h | h | h
  · exact Silmaril.Process.LpsBridge.threadNo_unmodeled i m (Or.inl h)
  · exact Silmaril.Process.LpsBridge.threadNo_unmodeled i m (Or.inr (Or.inr h))
  · exact Silmaril.Process.LpsBridge.threadNo_unmodeled i m (Or.inr (Or.inl h))

theorem halt_code (w : Word) : (w &&& 255).toNat = w.toNat % 256 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

end Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps
