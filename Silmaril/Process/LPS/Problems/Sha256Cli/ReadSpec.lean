module

public import Silmaril.Process.LPS.Problems.Sha256Cli.WriteSpec
public import Silmaril.Process.LPS.Problems.Sha256Cli.Syscalls
public import Silmaril.Process.LPS.Machines.ProcessMemorySupport

/-! # The LPS `read` arm on stdin, in closed form (VERIFIED)

`read_channel_iff`: on a descriptor bound to channel 0, with an `access_ok` buffer whose bytes
are writable in the model (the first byte, and as many as the clamped request could deliver),
the outcomes of LPS `read_spec` are exactly: return 0 with nothing changed if the count is
zero or stdin is at its end; otherwise some non-empty prefix `bs` of the remaining stdin (at
most the clamped count) is delivered into the buffer, with one `readEv 0` per byte, return
value `|bs|` and stdin advanced by `|bs|`. Nothing is `unmodeled` and no error is returned.

This is the LPS half of the `read` obligation of the bridge.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.Sha256Cli

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Sys

theorem modify_emit_pure_iff (f : Model → Model) (evs : List Event) (eff : SyscallEffect)
    (i : SyscallInput) (m : Model) (o : Outcome SyscallEffect) :
    (modify f >>= fun _ => emit evs >>= fun _ => Sys.pure eff) i m o ↔ o = .ok eff (f m) evs := by
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ e =>
    constructor
    · rintro ⟨u, m₁, e₁, e₂, hm, ⟨u', m₃, e₃, e₄, he, hp, rfl⟩, rfl⟩
      cases hm; cases he; cases hp; simp
    · intro h
      rw [h]
      exact ⟨(), f m, [], evs, rfl, ⟨(), f m, evs, [], rfl, rfl, by simp⟩, by simp⟩
  | unmodeled =>
    constructor
    · rintro (hm | ⟨u, m₁, e₁, hm, hk⟩)
      · cases hm
      · cases hm
        rcases hk with he | ⟨u', m₃, e₃, he, hp⟩
        · cases he
        · cases he; cases hp
    · intro h; cases h

/-- **LPS `read` on channel 0, closed form.** -/
theorem read_channel_iff (fd buf count : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (lookup : fdLookup m.fds fd = some (.channel 0))
    (ok : accessOkb buf (uns count) = true)
    (first : wIs0 count = false → (readBytesMap i.wmem buf 1).isSome = true)
    (room : wIs0 count = false →
      (readBytesMap i.wmem buf (lenWord (m.stdin.takeZ (rwCountClamp count)).1)).isSome = true) :
    readSpec fd buf count i m o ↔
      ((wIs0 count = true ∨ m.stdin.atEof = true) ∧ o = .ok (mkEffect 0 [] []) m []) ∨
      (wIs0 count = false ∧ m.stdin.atEof = false ∧
        ∃ bs : List Byte, (1 ≤ bs.length ∧ (bs.length : Int) ≤ rwCountClamp count ∧
          (m.stdin.take bs.length).1 = bs ∧ (readBytesMap i.wmem buf (lenWord bs)).isSome) ∧
          o = .ok (mkEffect (lenWord bs) [(buf, bs)] []) (m.withStdin (m.stdin.take bs.length).2)
            (bs.map (.readEv 0))) := by
  have zero : wIs0 (0 : Word) = true := by decide
  unfold readSpec readSpecWith
  rw [input_getModel_iff]
  simp only [lookup, zero, ok, Bool.not_true, Bool.false_eq_true, ite_false]
  by_cases hc : wIs0 count = true
  · simp only [hc, ite_true, true_or, true_and, Bool.true_eq_false, false_and, or_false]
    simp [retOnly, Sys.pure]
  · have hc' : wIs0 count = false := by simpa using hc
    obtain ⟨b₁, hb₁⟩ := Option.isSome_iff_exists.mp (first hc')
    obtain ⟨b₂, hb₂⟩ := Option.isSome_iff_exists.mp (room hc')
    by_cases he : m.stdin.atEof = true
    · simp only [hc', he, ite_true, ite_false, Bool.false_eq_true, or_true, true_and,
        Bool.true_eq_false, false_and, and_false, or_false]
      simp [retOnly, Sys.pure]
    · have he' : m.stdin.atEof = false := by simpa using he
      simp only [hc', he', Bool.false_eq_true, ite_false, hb₁, hb₂, or_self, false_and, true_and,
        false_or]
      rw [bind_choose_iff]
      simp only [modify_emit_pure_iff]

/-! ## The CLI `read` step from a pending pair (VERIFIED) -/

theorem cli_request_read (core : Silmaril.X86.State) (number : (core.read .rax).toNat = 0) :
    CLI.X86Linux.request core = some (.read ((core.read .rdi).setWidth 32).toNat
      (core.read .rsi).toNat (core.read .rdx).toNat) := by
  simp [CLI.X86Linux.request, CLI.X86Linux.readNumber, number]

/-- The CLI resumption after `read` returned `count`. -/
def resumeRead (core : Silmaril.X86.State) (count : Nat) (flagsWord : Word) : Silmaril.X86.State :=
  ((({ core with rip := core.rip + 2 } : Silmaril.X86.State).write .rax (BitVec.ofNat 64 count)).write
    .rcx (core.rip + 2)).write .r11 flagsWord

section CliRead

open Silmaril.Process.LPS.Machines

variable {oracle : Nat → X86FlagChoices.Choice} {MR : DescRel} {c : Config (machine oracle)}
  {x : PS} {h : List Syscall.Event}

/-- Every CLI step from a pending pair whose request is `read`: a positive read of the bytes
at the cursor into a fully writable buffer, an end-of-file read, or a zero-count read. -/
theorem cli_read_cases (p : PendRel MR c x h) (number : (x.core.read .rax).toNat = 0)
    {es : List Syscall.Event} {y : PS} (s : CStep x es y) :
    ∃ (d : Syscall.Descriptor) (flagsWord : Word),
      x.env.descriptors ((x.core.read .rdi).setWidth 32).toNat = some d ∧ d.readable = true ∧
      x.env.memory.Permitted .write (x.core.read .rsi).toNat (x.core.read .rdx).toNat ∧
      ((∃ (bytes : List Byte) (memory' : Silmaril.Process.Memory),
          d.input.Matches d.cursor bytes ∧ 0 < bytes.length ∧
          bytes.length ≤ (x.core.read .rdx).toNat ∧ bytes.length ≤ Syscall.maxTransfer ∧
          x.env.memory.writeBytes (x.core.read .rsi).toNat bytes = some memory' ∧
          es = [.read ((x.core.read .rdi).setWidth 32).toNat bytes] ∧
          y = ⟨resumeRead x.core bytes.length flagsWord,
            { x.env.setDescriptor ((x.core.read .rdi).setWidth 32).toNat
                { d with cursor := d.cursor + bytes.length } with memory := memory' }⟩) ∨
       ((d.input.byteAt d.cursor = none ∨ (x.core.read .rdx).toNat = 0) ∧
          es = [.read ((x.core.read .rdi).setWidth 32).toNat []] ∧
          y = ⟨resumeRead x.core 0 flagsWord, x.env⟩)) := by
  obtain ⟨core, env⟩ := x
  have trap : CLI.X86Linux.step core env.memory = .syscall { core with rip := core.rip + 2 } :=
    cli_step_trap p.trap
  have req : CLI.X86Linux.request { core with rip := core.rip + 2 } =
      some (.read ((core.read .rdi).setWidth 32).toNat (core.read .rsi).toNat
        (core.read .rdx).toNat) := cli_request_read { core with rip := core.rip + 2 } number
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
    generalize (core.read .rdx).toNat = n at effect
    cases effect
  | call _ step request effect resume =>
    have step' : _ = CLI.X86Linux.step core env.memory := step
    rw [trap] at step'; cases step'
    have request' : CLI.X86Linux.request _ = some _ := request
    rw [req] at request'; cases request'
    obtain ⟨effect, -, reliable⟩ := effect
    generalize hn : (core.read .rdx).toNat = n at effect ⊢
    cases effect with
    | readSome _ openFd readable input positive bounded transfer accessible copied =>
      obtain ⟨flagsWord, rfl⟩ := resume
      exact ⟨_, flagsWord, openFd, readable, accessible,
        .inl ⟨_, _, input, positive, bounded, transfer, copied, rfl, rfl⟩⟩
    | readEof _ openFd readable eof accessible =>
      obtain ⟨flagsWord, rfl⟩ := resume
      exact ⟨_, flagsWord, openFd, readable, accessible, .inr ⟨.inl eof, rfl, rfl⟩⟩
    | readZero _ openFd readable accessible =>
      obtain ⟨flagsWord, rfl⟩ := resume
      exact ⟨_, flagsWord, openFd, readable, accessible, .inr ⟨.inr rfl, rfl, rfl⟩⟩
    | readError => exact absurd trivial reliable
    | readBadDescriptor => exact absurd trivial reliable
    | readBadAddress => exact absurd trivial reliable

end CliRead

/-! ## LPS's buffer delivery is the CLI's `writeBytes` (VERIFIED) -/

theorem installWrapping_eq_install (memory : Silmaril.Process.ByteMemory) (base : Nat)
    (bytes : List Byte) (nowrap : base + bytes.length ≤ 2 ^ 64) :
    Machines.installWrapping memory base bytes = Silmaril.Process.Memory.install memory base bytes := by
  apply Std.ExtHashMap.ext_getElem?
  intro address
  by_cases inside : base ≤ address ∧ address < base + bytes.length
  · obtain ⟨index, rfl⟩ : ∃ index, address = base + index := ⟨address - base, by omega⟩
    have bound : index < bytes.length := by omega
    have l := Machines.installWrapping_get memory base bytes index bound nowrap
    have r := Silmaril.Process.Memory.install_get memory base bytes index bound
    exact l.trans r.symm
  · have outside : address < base ∨ base + bytes.length ≤ address := by omega
    have l := Machines.installWrapping_outside memory base bytes address nowrap outside
    have r := Silmaril.Process.Memory.install_outside memory base bytes address outside
    exact l.trans r.symm

/-- Applying the LPS read effect is the CLI's buffer write. -/
theorem applyMemoryEffect_read {memory memory' : Silmaril.Process.Memory} {buf : Word}
    {bytes : List Byte} (r : Word)
    (copied : memory.writeBytes buf.toNat bytes = some memory') :
    Machines.applyMemoryEffect memory (mkEffect r [(buf, bytes)] []) = memory' := by
  unfold Silmaril.Process.Memory.writeBytes at copied
  split at copied
  · rename_i span
    cases copied
    have nowrap : buf.toNat + bytes.length ≤ 2 ^ 64 := by
      rw [Silmaril.Process.Memory.checkSpan_iff] at span
      simpa [Silmaril.Process.addressLimit] using span.2.1
    show { memory with bytes := Machines.installWrapping memory.bytes buf.toNat bytes } = _
    rw [installWrapping_eq_install _ _ _ nowrap]
  · cases copied

end Silmaril.Process.LPS.Problems.Sha256Cli
