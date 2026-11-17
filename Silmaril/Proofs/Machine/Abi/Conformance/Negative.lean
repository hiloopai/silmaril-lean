module

public import Silmaril.Proofs.Machine.Abi.Conformance.LeafArith
public import Silmaril.X86.Open.Thms

/-!
# ABI conformance: negative tests

What `Conforms` rejects, on the admitted call `clamp_i32(5, 0, 3)` of the leaf-arith example
(`ffiSt 0x30 5 0 3`).

* **Schema tests on small machines.** Each machine is an x86-64 segment machine whose step is a
  given function, with no instruction decoder; they test the statement, not x86 code:
  - `stuck`: the machine cannot step, and the call does not conform in either mode;
  - `clobber`: the callee returns with `rbx` changed (a callee-saved register);
  - `unbalanced`: the callee "returns" with `rsp` 16 above its entry, so it never returns and
    then gets stuck;
  - `scribble`: the callee writes the byte at `rsp − 8` with `frame = 0`.
* **Prototypes.** `clamp_i32` with a `long` prototype (wrong widths) or an `unsigned` result
  (wrong signedness) is not what `arith.h` declares; a header declaring an `unsigned` result
  does not declare the `int` prototype, so no code conforms against it.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.Negative

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Process (Memory)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.LeafArith
open Silmaril.Machine.Abi.Conformance.LeafArith.Witness
open Silmaril.Proofs.Machine.Abi.Conformance
open Silmaril.Proofs.Machine.Abi.Conformance.LeafArith



theorem admit (f : MState → Option MState) {S : CallSpec sysvInt.V clampProto}
    (hS : S.objects clampArgs s0.machine.memory = fun _ => False) :
    Admit sysvInt (toy f) clampProto clampCode 0 S clampArgs s0 :=
  ⟨trivial, clamp_entry, placed _ _ _ _ _, hS ▸ stack _ (by decide) _ _ _ _ _, rfl⟩


theorem retOf_s0 : Silmaril.X86.FnContract.retOf s0.machine.core s0.machine.memory = retAt :=
  retOf_st _ _ _ _

theorem not_returned_s0 (f : MState → Option MState) :
    ¬ Silmaril.X86.FnContract.Returned (toy f).isa s0.machine s0.machine :=
  not_returned_entry (M := toy f) (c := clampCode) (by decide)
    (by decide +kernel) (placed _ _ _ _ _)

theorem returned_ret0 (f : MState → Option MState) (c : State) (m : Memory) :
    Silmaril.X86.FnContract.Returned (toy f).isa s0.machine (ret0 c m) := by
  refine ⟨?_, ?_⟩
  · show retAt = _; rw [show (toy f).isa.core s0.machine = s0.machine.core from rfl,
      show (toy f).isa.mem s0.machine = s0.machine.memory from rfl, retOf_s0]
  · show Silmaril.Machine.RegisterFile.write c.regs .rsp (0x8ff8 + 8) .rsp = _
    simp [Silmaril.Machine.RegisterFile.write]; rfl


theorem firstReturn_oneStep (c : State) (m : Memory) :
    Silmaril.X86.FnContract.FirstReturn (toy (oneStep c m)).isa s0.machine (ret0 c m) :=
  ⟨.step (not_returned_s0 _) (by simp [toy, Mach.ofInt, toyIsa, oneStep]; rfl) (.refl _),
    returned_ret0 _ c m⟩

/-! ## Stuck code -/

theorem stuck_not (mode : Mode) (S : CallSpec sysvInt.V clampProto)
    (hS : S.objects clampArgs s0.machine.memory = fun _ => False)
    (hpre : S.pre clampArgs s0.machine.memory) :
    ¬ Conforms sysvInt (toy fun _ => none) mode hdr "clamp_i32" clampProto clampCode 0 S := by
  intro h
  have := Silmaril.Proofs.Machine.Abi.Conformance.Conforms.steps h
    (by decide) (admit _ hS) hpre
  simp [toy, Mach.ofInt, toyIsa] at this

/-! ## A callee-saved register clobbered -/


theorem clobber_not (mode : Mode) :
    ¬ Conforms sysvInt (toy (oneStep clobbered s0.machine.memory)) mode hdr "clamp_i32"
      clampProto clampCode 0 (CallSpec.abiPure sysvInt.V clampProto) := by
  intro h
  have g := h.sound clampArgs s0 (admit _ rfl) trivial _
    (mem_callModelOf (firstReturn_oneStep clobbered s0.machine.memory))
  obtain ⟨_, _, hret⟩ := g.ret
  have := hret.calleeSaved .rbx (by decide)
  revert this
  simp [toy, Mach.ofInt, ret0, clobbered, s0, ffiSt, st, Silmaril.Machine.RegisterFile.write,
    State.read,
    State.write, Silmaril.Machine.Abi.SystemV.callOf]

/-! ## A write below the stack pointer with no frame -/


theorem scribble_not (mode : Mode) :
    ¬ Conforms sysvInt (toy (oneStep s0.machine.core scribbled)) mode hdr "clamp_i32"
      clampProto clampCode 0 (CallSpec.abiPure sysvInt.V clampProto) := by
  intro h
  have g := h.sound clampArgs s0 (admit _ rfl) trivial _
    (mem_callModelOf (firstReturn_oneStep s0.machine.core scribbled))
  have hsp : sp s0 = 0x8ff8 := rfl
  have ha : sysvInt.argArea clampProto = 0 := rfl
  have hw := g.frame.2 (0x8ff8 - 8) (by
    rintro (h | h)
    · exact h
    · unfold Owned at h
      rw [hsp, ha] at h
      rcases h with ⟨_, h2⟩ | ⟨h1, _⟩ | h
      · omega
      · omega
      · exact h)
  have after : scribbled.bytes.get? (0x8ff8 - 8) = some 0xab :=
    Memory.install_get s0.machine.memory.bytes (0x8ff8 - 8) [0xab] 0 (by decide)
  have before : s0.machine.memory.bytes.get? (0x8ff8 - 8) = none := by
    show (Memory.install (Memory.install ∅ 0x8ff8 retEnc) 0x401370 Silmaril.X86.Ladder.LeafArith.code).get? _ = _
    rw [Memory.install_outside _ _ _ _ (.inl (by decide)),
      Memory.install_outside _ _ _ _ (.inl (by decide))]
    simp
  have : (ret0 s0.machine.core scribbled).memory.bytes.get? (0x8ff8 - 8) =
      s0.machine.memory.bytes.get? (0x8ff8 - 8) := hw
  rw [show (ret0 s0.machine.core scribbled).memory = scribbled from rfl, after, before] at this
  cases this

/-! ## An unbalanced stack at the return -/



theorem unbalanced_not (mode : Mode) :
    ¬ Conforms sysvInt (toy unbalancedStep) mode hdr "clamp_i32" clampProto clampCode 0
      (CallSpec.abiPure sysvInt.V clampProto) := by
  intro h
  have hns := h.safe clampArgs s0 (admit _ rfl) trivial
  have hnr : ¬ Silmaril.X86.FnContract.Returned (toy unbalancedStep).isa s0.machine
      ⟨unbalancedCore, s0.machine.memory⟩ := by
    rintro ⟨-, hsp⟩
    revert hsp
    show Silmaril.Machine.RegisterFile.write s0.machine.core.regs .rsp (0x8ff8 + 16) .rsp ≠ _
    simp [Silmaril.Machine.RegisterFile.write]
    decide
  have := hns _
    (.step (not_returned_s0 _) (by simp [toy, Mach.ofInt, toyIsa, unbalancedStep]; rfl) (.refl _))
    hnr
  revert this
  simp [toy, Mach.ofInt, toyIsa, unbalancedStep, unbalancedCore]
  decide

/-! ## A prototype the header does not declare -/


theorem wrong_prototype : ¬ Declares sysvInt hdr "clamp_i32" longProto := by
  rintro ⟨cp, hcp, hl⟩
  have h : hdr.proto? "clamp_i32" =
      some ⟨.int .int .signed, [.int .int .signed, .int .int .signed, .int .int .signed], false⟩ := by
    decide +kernel
  rw [h] at hcp
  cases hcp
  have := congrArg (fun e : Except String Silmaril.Machine.Abi.SystemV.Proto =>
    e.toOption.map (·.signature)) hl
  exact absurd this (by decide)


open Silmaril.X86 (fetchWindow maxInstrLength)

/-! ## Stuck on the real open machine: entry in the middle of an instruction -/

/-- The fetch window inside loaded code is the code's bytes. -/
theorem window_of_loaded {mem : Memory} {base : Word} {code : List Byte} (h : Silmaril.X86.Ext.Loaded mem base code) :
    ∀ (n o : Nat), o + n ≤ code.length →
      fetchWindow mem n (base.toNat + o) = (code.drop o).take n := by
  intro n
  induction n with
  | zero => intro o _; simp [fetchWindow]
  | succ n ih =>
    intro o hfit
    have h1 := Silmaril.X86.Ext.Loaded.fetchBytes_sub h (offset := o) (len := 1) (by decide) (by omega)
    have hd : (code.drop o).take 1 = [code[o]'(by omega)] := by
      rw [List.take_one, List.head?_drop]; simp [List.getElem?_eq_getElem (show o < code.length by omega)]
    rw [hd] at h1
    simp only [fetchWindow, h1]
    rw [show base.toNat + o + 1 = base.toNat + (o + 1) by omega, ih (o + 1) (by omega)]
    rw [List.drop_eq_getElem_cons (show o < code.length by omega), List.take_succ_cons]

/-- `clamp_i32`'s prototype entered at offset 1 of the region (inside `gcd_u32`'s first
instruction): the open machine has no step. -/
theorem open_stuck_mid : Silmaril.X86.Open.step (st 1 5 0 3) = none := by
  have hw : fetchWindow mem maxInstrLength 0x401371 = (Silmaril.X86.Ladder.LeafArith.code.drop 1).take 15 :=
    window_of_loaded loaded 15 1 (by rw [code_length]; omega)
  have hext : Silmaril.X86.Ext.fetch mem 0x401371 = .undecodable := by
    unfold Silmaril.X86.Ext.fetch
    rw [hw]
    have h1 : Silmaril.X86.Ext.decode ((Silmaril.X86.Ladder.LeafArith.code.drop 1).take 15) = none := by
      decide +kernel
    rw [h1]
    have h2 : (match Silmaril.X86.Ext.parseRaw ((Silmaril.X86.Ladder.LeafArith.code.drop 1).take 15) with
        | .eof => false | _ => true) = true := by decide +kernel
    simp only
    revert h2
    cases Silmaril.X86.Ext.parseRaw ((Silmaril.X86.Ladder.LeafArith.code.drop 1).take 15) <;> simp
  have h8 : Silmaril.X86.Ext8.fetch mem 0x401371 = .inl .undecodable := by
    unfold Silmaril.X86.Ext8.fetch
    rw [hext]
    simp only
    rw [hw]
    have h3 : Silmaril.X86.Ext8.decodeNew ((Silmaril.X86.Ladder.LeafArith.code.drop 1).take 15) = none := by
      decide +kernel
    rw [h3]
  unfold Silmaril.X86.Open.step
  rw [show (st 1 5 0 3).memory = mem from rfl,
    show (st 1 5 0 3).core.rip.toNat = 0x401371 from rfl, h8]

/-- **Stuck code does not conform on `Open`**, in either mode and for any spec admitting the call:
`clamp_i32`'s prototype entered in the middle of an instruction. -/
theorem open_mid_not (mode : Mode) (S : CallSpec sysvInt.V clampProto)
    (hS : S.objects clampArgs (ffiSt 1 5 0 3).machine.memory = fun _ => False)
    (hpre : S.pre clampArgs (ffiSt 1 5 0 3).machine.memory) :
    ¬ Conforms sysvInt (Mach.ofInt Silmaril.X86.Open.isa) mode hdr "clamp_i32" clampProto (region 1 19) 0 S := by
  intro h
  have ad : Admit sysvInt (Mach.ofInt Silmaril.X86.Open.isa) clampProto (region 1 19) 0 S clampArgs (ffiSt 1 5 0 3) := by
    refine ⟨trivial, ?_, placed _ _ _ _ _, hS ▸ stack _ (by decide) _ _ _ _ _, rfl⟩
    refine ⟨retAt, rfl, ⟨⟨rfl, _, rfl, (Silmaril.Proofs.Machine.Abi.Conformance.SysvInt.chunk32_iff _ .rdi _).2 rfl⟩,
      ⟨rfl, _, rfl, (Silmaril.Proofs.Machine.Abi.Conformance.SysvInt.chunk32_iff _ .rsi _).2 rfl⟩,
      ⟨rfl, _, rfl, (Silmaril.Proofs.Machine.Abi.Conformance.SysvInt.chunk32_iff _ .rdx _).2 rfl⟩,
      trivial⟩, ?_, ?_, ret_read, rfl, rfl, rfl, fun _ h => nomatch h⟩
    · change ((0x8ff8 : Word).toNat + 8) % 16 = 0
      decide
    · change (0x8ff8 : Word).toNat + 8 + alignUp (8 * (3 - 6)) 16 ≤ 2 ^ 64
      decide
  have := Silmaril.Proofs.Machine.Abi.Conformance.Conforms.steps h
    (by decide) ad hpre
  change (Silmaril.X86.Open.step (st 1 5 0 3)).isSome = true at this
  rw [open_stuck_mid] at this
  cases this

/-- `unsigned clamp_i32(int, int, int)` (wrong result signedness) is not what `arith.h`
declares. -/
theorem wrong_signedness : ¬ Declares sysvInt hdr "clamp_i32" uRetProto := by
  rintro ⟨cp, hcp, hl⟩
  have h : hdr.proto? "clamp_i32" =
      some ⟨.int .int .signed, [.int .int .signed, .int .int .signed, .int .int .signed], false⟩ := by
    decide +kernel
  rw [h] at hcp
  cases hcp
  have := congrArg (fun e : Except String Silmaril.Machine.Abi.SystemV.Proto =>
    e.toOption.map (·.signature)) hl
  exact absurd this (by decide)

/-- A header declaring `unsigned clamp_i32(int, int, int)` does not declare the `int` one. -/
theorem wrong_header : ¬ Declares sysvInt hdrU "clamp_i32" clampProto := by
  rintro ⟨cp, hcp, hl⟩
  have h : hdrU.proto? "clamp_i32" =
      some ⟨.int .int .unsigned, [.int .int .signed, .int .int .signed, .int .int .signed], false⟩ := by
    decide +kernel
  rw [h] at hcp
  cases hcp
  have := congrArg (fun e : Except String Silmaril.Machine.Abi.SystemV.Proto =>
    e.toOption.map (·.signature)) hl
  exact absurd this (by decide)

end Silmaril.Proofs.Machine.Abi.Conformance.Negative

end
