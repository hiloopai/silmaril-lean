module

public import Silmaril.Process.LPS.Lattice
public import Silmaril.Process.LPS.MonadIff

/-! # A sound riscv64 reference table: `sendmsg` without LPS's missing `access_ok`

LPS's `sendmsg_spec` (`Sys.Socket.sendmsgSpec`) reads the message's iovecs with
`copy_iovecs_aux`: no `access_ok` on the descriptor array and none on any segment base. Linux's
`copy_msghdr_from_user` imports them through `__import_iovec`, which checks both and answers
`-EFAULT` before anything is sent. So on a vector with a segment Linux refuses (a base in the
non-canonical or kernel half, or a range past the Sv48 user limit) LPS sends the readable prefix
where riscv64 Linux fails: an error turned into a specific success
(`Checks.SoundReference.lps_sends_where_linux_faults`).

Three points of the variant lattice, all over LPS's other 89 arms unchanged:

* `syscallSpec`: LPS literal (`sendmsgSpec`), kept for literal agreement with LPS;
* `linuxSyscallSpec`: `sendmsg` with Linux's import (`Sys.Socket.sendmsgSpecLinux`);
* `soundSyscallSpec`: LPS's arm where the two imports agree, `unmodeled` elsewhere
  (`sendmsgSpecSound`).

`soundSyscallSpec_restricts_lps` and `soundSyscallSpec_restricts_linux` prove that the sound
table restricts both (`Lattice.Restricts`), so by `Lattice.agrees_transfer` an agreement
statement proved against `soundSyscallSpec` holds against LPS's table and against the
Linux-faithful one, with the same traces (`agrees_lps_of_sound`, `agrees_linux_of_sound`).
Statements meant as claims about riscv64 Linux should be stated over `soundSyscallSpec`
(or `linuxSyscallSpec`), not over `syscallSpec`.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.SoundReference

open Silmaril.Process.LPS Sys

/-- At this memory, the header at `msgp` names descriptors on which LPS's `copy_iovecs_aux`
and Linux's `__import_iovec` (Sv48 `access_ok`) give the same import and walk the same
descriptor ranges (or the header's `msg_iov`/`msg_iovlen` are unreadable, where both arms
answer `-EFAULT` before importing). -/
def sendmsgImportsAgree (mp : Word → Option Byte) (msgp : Word) : Bool :=
  match readU64 mp (msgp + 16), readU64 mp (msgp + 24) with
  | some iov, some iovlen =>
    importIovecs mp iov iovlen == copyIovecsAux mp iov (wordToNat iovlen) &&
      importIovecsAccesses mp iov iovlen == copyIovecsAccesses mp iov (wordToNat iovlen)
  | _, _ => true

/-- The sound riscv64 `sendmsg`: LPS's arm where the two imports agree, `unmodeled`
elsewhere (in particular wherever LPS would send the readable prefix of a vector Linux
refuses with `-EFAULT`). -/
def sendmsgSpecSound (fd msgp flags : Word) : Sys SyscallEffect := fun i =>
  if sendmsgImportsAgree i.mem msgp then sendmsgSpec fd msgp flags i else Sys.unmodeled i

/-- `sendmsgSpecWith` reads its import only at the header's `msg_iov`/`msg_iovlen`. -/
theorem sendmsgSpecWith_congr
    (imp₁ imp₂ : (Word → Option Byte) → Word → Word → IovImport)
    (acc₁ acc₂ : (Word → Option Byte) → Word → Word → List (Word × Nat))
    (fd msgp flags : Word) (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect)
    (h : ∀ iov iovlen, readU64 i.mem (msgp + 16) = some iov →
      readU64 i.mem (msgp + 24) = some iovlen →
      imp₁ i.mem iov iovlen = imp₂ i.mem iov iovlen ∧
        acc₁ i.mem iov iovlen = acc₂ i.mem iov iovlen) :
    sendmsgSpecWith imp₁ acc₁ fd msgp flags i m o ↔
      sendmsgSpecWith imp₂ acc₂ fd msgp flags i m o := by
  unfold sendmsgSpecWith
  split
  · exact Iff.rfl
  · rw [bind_input_iff, bind_input_iff, bind_getModel_iff, bind_getModel_iff]
    cases h0 : readU64 i.mem msgp <;> cases h1 : readU64 i.mem (msgp + 8) <;>
      cases hiov : readU64 i.mem (msgp + 16) <;> cases hlen : readU64 i.mem (msgp + 24) <;>
      cases h4 : readU64 i.mem (msgp + 32) <;> cases h5 : readU64 i.mem (msgp + 40) <;>
      first
      | exact Iff.rfl
      | (rename_i iov iovlen _ _
         obtain ⟨e₁, e₂⟩ := h _ _ hiov hlen
         dsimp only
         rw [e₁, e₂])

theorem sendmsgImportsAgree_spec (mp : Word → Option Byte) (msgp : Word)
    (h : sendmsgImportsAgree mp msgp = true) (iov iovlen : Word)
    (hiov : readU64 mp (msgp + 16) = some iov) (hlen : readU64 mp (msgp + 24) = some iovlen) :
    copyIovecsAux mp iov (wordToNat iovlen) = importIovecs mp iov iovlen ∧
      copyIovecsAccesses mp iov (wordToNat iovlen) = importIovecsAccesses mp iov iovlen := by
  simp only [sendmsgImportsAgree, hiov, hlen, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- Where the two imports agree, LPS's `sendmsg_spec` is the Linux-faithful arm. -/
theorem sendmsgSpec_eq_linux (fd msgp flags : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (h : sendmsgImportsAgree i.mem msgp = true) :
    sendmsgSpec fd msgp flags i m o ↔ sendmsgSpecLinux fd msgp flags i m o :=
  sendmsgSpecWith_congr _ _ _ _ fd msgp flags i m o
    (fun iov iovlen hiov hlen => sendmsgImportsAgree_spec i.mem msgp h iov iovlen hiov hlen)

theorem sendmsgSpecSound_restricts_lps (fd msgp flags : Word) :
    Restricts (sendmsgSpecSound fd msgp flags) (sendmsgSpec fd msgp flags) := by
  intro i m
  unfold sendmsgSpecSound
  split
  · exact .inl fun _ => Iff.rfl
  · exact .inr fun _ => Iff.rfl

theorem sendmsgSpecSound_restricts_linux (fd msgp flags : Word) :
    Restricts (sendmsgSpecSound fd msgp flags) (sendmsgSpecLinux fd msgp flags) := by
  intro i m
  unfold sendmsgSpecSound
  split
  · rename_i h; exact .inl fun o => sendmsgSpec_eq_linux fd msgp flags i m o h
  · exact .inr fun _ => Iff.rfl

/-- The riscv64 `sendmsg` arm (211) with LPS's argument extraction. -/
def sendmsgArmWith (spec : Word → Word → Word → Sys SyscallEffect) : SpecArm :=
  arm 211 "sendmsg" (fun i => spec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2))

/-- LPS's table with its `sendmsg` arm replaced. -/
def withSendmsg (spec : Word → Word → Word → Sys SyscallEffect) : List SpecArm :=
  specTable.map fun a => if a.no = 211 then sendmsgArmWith spec else a

/-- The sound riscv64 reference table. -/
def soundSpecTable : List SpecArm := withSendmsg sendmsgSpecSound
/-- The riscv64 reference table with Linux's `sendmsg` import. -/
def linuxSpecTable : List SpecArm := withSendmsg sendmsgSpecLinux
def soundSyscallSpec : Sys SyscallEffect := dispatch soundSpecTable
def linuxSyscallSpec : Sys SyscallEffect := dispatch linuxSpecTable

theorem lookupArm_specTable_sendmsg : lookupArm specTable 211 = some (sendmsgArmWith sendmsgSpec) :=
  rfl

theorem lookupArm_no {t : List SpecArm} {n : Nat} {a : SpecArm} (h : lookupArm t n = some a) :
    a.no = n := by
  induction t with
  | nil => simp [lookupArm] at h
  | cons b r ih =>
    simp only [lookupArm] at h
    split at h
    · cases h; assumption
    · exact ih h

theorem lookupArm_map (g : SpecArm → SpecArm) (hg : ∀ a, (g a).no = a.no) (t : List SpecArm)
    (n : Nat) : lookupArm (t.map g) n = (lookupArm t n).map g := by
  induction t with
  | nil => rfl
  | cons b r ih =>
    simp only [List.map_cons, lookupArm, hg]
    split <;> simp [ih]

theorem lookupArm_withSendmsg (spec : Word → Word → Word → Sys SyscallEffect) (n : Nat) :
    lookupArm (withSendmsg spec) n =
      if n = 211 then some (sendmsgArmWith spec) else lookupArm specTable n := by
  unfold withSendmsg
  rw [lookupArm_map _ (fun a => by split <;> simp_all [sendmsgArmWith, arm])]
  by_cases hn : n = 211
  · subst hn; rw [lookupArm_specTable_sendmsg]; simp [sendmsgArmWith, arm]
  · simp only [hn, ite_false]
    cases h : lookupArm specTable n with
    | none => rfl
    | some a => simp [lookupArm_no h, hn]

/-- Re-installing LPS's own arm gives LPS's table. -/
theorem withSendmsg_lps : dispatch (withSendmsg sendmsgSpec) = syscallSpec := by
  have e : ∀ n, lookupArm (withSendmsg sendmsgSpec) n = lookupArm specTable n := by
    intro n
    rw [lookupArm_withSendmsg]
    split
    · rename_i hn; subst hn; exact lookupArm_specTable_sendmsg.symm
    · rfl
  funext i m o
  simp only [dispatch, syscallSpec, e]

theorem withSendmsg_restricts (p f : Word → Word → Word → Sys SyscallEffect)
    (h : ∀ fd msgp flags, Restricts (p fd msgp flags) (f fd msgp flags)) :
    Restricts (dispatch (withSendmsg p)) (dispatch (withSendmsg f)) := by
  intro i m
  unfold dispatch
  rw [lookupArm_withSendmsg, lookupArm_withSendmsg]
  by_cases hn : i.sysno.toNat = 211
  · simp only [hn, ite_true]; exact h _ _ _ i m
  · simp only [hn, ite_false]; exact .inl fun _ => by simp

/-- The sound table restricts LPS's literal one. -/
theorem soundSyscallSpec_restricts_lps : Restricts soundSyscallSpec syscallSpec := by
  rw [← withSendmsg_lps]; exact withSendmsg_restricts _ _ sendmsgSpecSound_restricts_lps

/-- The sound table restricts the Linux-faithful one. -/
theorem soundSyscallSpec_restricts_linux : Restricts soundSyscallSpec linuxSyscallSpec :=
  withSendmsg_restricts _ _ sendmsgSpecSound_restricts_linux

/-- An agreement statement over the sound table holds over LPS's literal table. -/
theorem agrees_lps_of_sound {isaP isaS : UserIsa} {lp ls : Int} {plain san : Image}
    (h : AgreesOver soundSyscallSpec isaP isaS lp ls plain san) :
    AgreesOver syscallSpec isaP isaS lp ls plain san :=
  agrees_transfer soundSyscallSpec_restricts_lps h

/-- An agreement statement over the sound table holds over the Linux-faithful table. -/
theorem agrees_linux_of_sound {isaP isaS : UserIsa} {lp ls : Int} {plain san : Image}
    (h : AgreesOver soundSyscallSpec isaP isaS lp ls plain san) :
    AgreesOver linuxSyscallSpec isaP isaS lp ls plain san :=
  agrees_transfer soundSyscallSpec_restricts_linux h

end Silmaril.Process.LPS.SoundReference
