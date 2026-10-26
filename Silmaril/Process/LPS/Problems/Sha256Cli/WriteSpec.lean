module

public import Silmaril.Process.LPS.Problems.Sha256Cli.Syscalls

/-! # The LPS `write` arm on stdout, in closed form (VERIFIED)

`write_channel_iff`: on a descriptor bound to channel 1, with a nonzero modelled count and a
non-empty readable source, the outcomes of LPS `write_spec` are exactly: some non-empty prefix
`ds` of the readable source (at most the clamped count) is written, with one `writeEv 1` per
byte, return value `|ds|`, the copy-in `(buf, |ds|)` recorded and the model unchanged. Nothing
is `unmodeled`.

This is the LPS half of the `write` obligation of the bridge.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Sys

theorem input_getModel_iff {β : Type} (k : SyscallInput → Model → Sys β) (i : SyscallInput)
    (m : Model) (o : Outcome β) :
    (do let i' ← input; let m' ← getModel; k i' m') i m o ↔ k i m i m o := by
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, e₁, e₂, hx, ⟨x', m₁', e₁', e₂', hx', hk, rfl⟩, rfl⟩
      cases hx; cases hx'; simpa using hk
    · intro hk
      exact ⟨i, m, [], evs, rfl, ⟨m, m, [], evs, rfl, hk, rfl⟩, rfl⟩
  | unmodeled =>
    constructor
    · rintro (hx | ⟨x, m₁, e₁, hx, hk⟩)
      · cases hx
      · cases hx
        rcases hk with hx' | ⟨x', m₁', e₁', hx', hk'⟩
        · cases hx'
        · cases hx'; exact hk'
    · intro hk
      exact .inr ⟨i, m, [], rfl, .inr ⟨m, m, [], rfl, hk⟩⟩

theorem bind_choose_iff {α β : Type} (P : α → Prop) (k : α → Sys β) (i : SyscallInput)
    (m : Model) (o : Outcome β) : (Sys.choose P >>= k) i m o ↔ ∃ x, P x ∧ k x i m o := by
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, e₁, e₂, ⟨x', hx, hc⟩, hk, rfl⟩
      cases hc; exact ⟨x, hx, by simpa using hk⟩
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, m, [], evs, ⟨x, hx, rfl⟩, hk, rfl⟩
  | unmodeled =>
    constructor
    · rintro (⟨x, -, hc⟩ | ⟨x, m₁, e₁, ⟨x', hx, hc⟩, hk⟩)
      · cases hc
      · cases hc; exact ⟨x, hx, hk⟩
    · rintro ⟨x, hx, hk⟩
      exact .inr ⟨x, m, [], ⟨x, hx, rfl⟩, hk⟩

theorem emit_recordCopyins_retOnly_iff (evs : List Event) (reads : List (Word × Nat)) (r : Word)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect) :
    (emit evs >>= fun _ => recordCopyins reads (retOnly r)) i m o ↔
      o = .ok ((mkEffect r [] []).withCopyins (reads ++ [])) m evs := by
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ e =>
    constructor
    · rintro ⟨u, m₁, e₁, e₂, he, ⟨eff, m₃, e₃, e₄, hr, hp, rfl⟩, rfl⟩
      cases he; cases hr; cases hp; simp [mkEffect]
    · intro h
      rw [h]
      exact ⟨(), m, evs, [], rfl, ⟨_, m, [], [], rfl, rfl, rfl⟩, by simp⟩
  | unmodeled =>
    constructor
    · rintro (he | ⟨u, m₁, e₁, he, hr⟩)
      · cases he
      · cases he
        rcases hr with hr | ⟨eff, m₃, e₃, hr, hp⟩
        · cases hr
        · cases hr; cases hp
    · intro h; cases h

/-- **LPS `write` on channel 1, closed form.** -/
theorem write_channel_iff (fd buf count : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (lookup : fdLookup m.fds fd = some (.channel 1))
    (modeled : modeledRwRangeWith accessOkb buf count = true) (nonzero : wIs0 count = false)
    (source : writeSource i.mem buf count ≠ []) :
    writeSpec fd buf count i m o ↔
      ∃ ds : List Byte, (1 ≤ ds.length ∧ (ds.length : Int) ≤ rwCountClamp count ∧
        ds = (writeSource i.mem buf count).take ds.length) ∧
        o = .ok ((mkEffect (lenWord ds) [] []).withCopyins ([(buf, ds.length)] ++ [])) m
          (ds.map (.writeEv 1)) := by
  have one : wIs0 (1 : Word) = false := by decide
  have len : ((writeSource i.mem buf count).length == 0) = false := by
    cases h : writeSource i.mem buf count with
    | nil => exact absurd h source
    | cons => rfl
  unfold writeSpec writeSpecWith
  rw [input_getModel_iff]
  simp only [lookup, one, modeled, nonzero, len, Bool.not_true, Bool.false_eq_true,
    ite_false]
  rw [bind_choose_iff]
  simp only [emit_recordCopyins_retOnly_iff]

/-! ## The readable view of a successful CLI read -/

theorem readableBytesAux_of_readBytes {memory : Silmaril.Process.Memory} :
    ∀ (k a n : Nat) (bytes : List Byte), memory.readBytes a n = some bytes → k ≤ n →
      readableBytesAux (Machines.viewByte memory .read) (BitVec.ofNat 64 a) k = bytes.take k := by
  intro k
  induction k with
  | zero => intro a n bytes _ _; rfl
  | succ k ih =>
    intro a n bytes read bound
    obtain ⟨hlen, permitted, installed⟩ := Silmaril.X86.Memory.readWith_eq_some_iff.mp read
    have perm := permitted
    rw [Silmaril.Process.Memory.Permitted, Silmaril.Process.Memory.checkSpan_iff] at perm
    obtain ⟨start, limit, perms⟩ := perm
    have pos : 0 < bytes.length := by omega
    have first : Machines.viewByte memory .read (BitVec.ofNat 64 a) = some bytes[0] := by
      have toNat : (BitVec.ofNat 64 a).toNat = a := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simpa [Silmaril.Process.addressLimit] using start)
      unfold Machines.viewByte
      rw [toNat, ite_eq_left (by simpa using perms 0 (by omega))]
      simpa using installed 0 pos
    unfold readableBytesAux
    rw [first]
    obtain ⟨b, rest, rfl⟩ : ∃ b rest, bytes = b :: rest := by
      cases bytes with
      | nil => simp at pos
      | cons b rest => exact ⟨b, rest, rfl⟩
    simp only [List.getElem_cons_zero, List.take_succ_cons, List.cons.injEq, true_and]
    rcases Nat.eq_zero_or_pos k with rfl | kpos
    · rfl
    · have slice := Silmaril.X86.Memory.readWith_slice read 1 (n - 1) (by omega) (by omega)
      have next : BitVec.ofNat 64 a + 1 = BitVec.ofNat 64 (a + 1) := by
        apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
      rw [next, ih (a + 1) (n - 1) _ slice (by omega)]
      simp only [List.drop_one, List.tail_cons, List.take_take]
      congr 1
      omega

/-! ## The CLI `write` step from a pending pair -/

theorem cli_request_write (core : Silmaril.X86.State) (number : (core.read .rax).toNat = 1) :
    CLI.X86Linux.request core = some (.write ((core.read .rdi).setWidth 32).toNat
      (core.read .rsi).toNat (core.read .rdx).toNat) := by
  simp [CLI.X86Linux.request, CLI.X86Linux.readNumber, CLI.X86Linux.writeNumber, number]

/-- The CLI resumption after `write` returned `written`. -/
def resumeWrite (core : Silmaril.X86.State) (written : Nat) (flagsWord : Word) : Silmaril.X86.State :=
  ((({ core with rip := core.rip + 2 } : Silmaril.X86.State).write .rax (BitVec.ofNat 64 written)).write
    .rcx (core.rip + 2)).write .r11 flagsWord

theorem positive_of_not_refusal {fd w : Nat} {l : List Byte}
    (h : ¬ (Syscall.Event.write fd (l.take w)).IsRefusal) : 1 ≤ w := by
  rcases Nat.eq_zero_or_pos w with rfl | pos
  · simp only [List.take_zero] at h
    exact absurd trivial h
  · exact pos

section CliWrite

open Silmaril.Process.LPS.Machines

variable {oracle : Nat → X86FlagChoices.Choice} {MR : DescRel} {c : Config (machine oracle)}
  {x : PS} {h : List Syscall.Event}

/-- Every CLI step from a pending pair whose request is `write` is a positive write of a prefix
of the (fully readable) source buffer. -/
theorem cli_write_cases (p : PendRel MR c x h) (number : (x.core.read .rax).toNat = 1)
    {es : List Syscall.Event} {y : PS} (s : CStep x es y) :
    ∃ (d : Syscall.Descriptor) (bytes : List Byte) (written : Nat) (flagsWord : Word),
      x.env.descriptors ((x.core.read .rdi).setWidth 32).toNat = some d ∧ d.writable = true ∧
      x.env.memory.readBytes (x.core.read .rsi).toNat (x.core.read .rdx).toNat = some bytes ∧
      1 ≤ written ∧ written ≤ (x.core.read .rdx).toNat ∧ written ≤ Syscall.maxTransfer ∧
      es = [.write ((x.core.read .rdi).setWidth 32).toNat (bytes.take written)] ∧
      y = ⟨resumeWrite x.core written flagsWord,
        x.env.setDescriptor ((x.core.read .rdi).setWidth 32).toNat
          { d with output := d.output ++ bytes.take written }⟩ := by
  obtain ⟨core, env⟩ := x
  have trap : CLI.X86Linux.step core env.memory = .syscall { core with rip := core.rip + 2 } :=
    cli_step_trap p.trap
  have req : CLI.X86Linux.request { core with rip := core.rip + 2 } =
      some (.write ((core.read .rdi).setWidth 32).toNat (core.read .rsi).toNat
        (core.read .rdx).toNat) := cli_request_write _ number
  cases s with
  | retire _ step =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
  | exit _ step request effect =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
    have request' : CLI.X86Linux.request _ = some _ := request
    rw [req] at request'; cases request'
    obtain ⟨effect, -⟩ := effect
    cases effect
  | call _ step request effect resume =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
    have request' : CLI.X86Linux.request _ = some _ := request
    rw [req] at request'; cases request'
    obtain ⟨effect, -, reliable⟩ := effect
    cases effect with
    | writeSome _ openFd writable loaded bounded transfer =>
      obtain ⟨flagsWord, rfl⟩ := resume
      exact ⟨_, _, _, flagsWord, openFd, writable, loaded, positive_of_not_refusal reliable,
        bounded, transfer, rfl, rfl⟩
    | writeError => exact absurd trivial reliable
    | writeBadDescriptor => exact absurd trivial reliable
    | writeBadAddress => exact absurd trivial reliable

end CliWrite

end Silmaril.Process.LPS.Problems.Sha256Cli
