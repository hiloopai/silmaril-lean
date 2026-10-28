module

public import Silmaril.Process.LPS.Machines.X86FlagChoices
public import Silmaril.X86.Ext8.Basic

/-! # The LPS x86-64 machine over the `Ext8` variant (8-bit ALU forms)

`x86WithFlagOracle8 oracle` is `x86WithFlagOracle oracle` (native x86-64, an explicit oracle
for undefined flags at `syscall`) with the instruction fetch of `X86.Ext8`: `X86.Ext`'s decoder
first, then the byte forms gcc emits for character code (`op r/m8, r8`, `op r8, r/m8`,
`op al, imm8`, `80 /digit`, `shl/shr/sar r/m8`, `mov r/m8`, `movzx/movsx r/m8` with
AH-BH, `setcc`). Every other field (system-call interface, loader, address space) is
`x86WithFlagOracle`'s.

* `x86NativeStep8`: `X86.x86NativeStep` with the `Ext8` fetch; a new form reports its
  instruction fetch and its byte memory operand (if any) as accesses.
* `x86NativeStep8_eq` (VERIFIED): wherever `X86.Ext.fetch` decodes (or the bytes are
  `syscall`), the variant's step is `x86NativeStep`, so every result about `x86WithFlagOracle`
  on such a state transfers.

Status: VERIFIED (no `sorry`, no new axiom).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Machines

open Silmaril.X86

namespace X86Accesses

/-- The data span of a byte operand. -/
def rm8 (core : State) (next : Word) : Ext8.RM8 → List (Word × Nat)
  | .reg _ => []
  | .mem address => [(address.addr core next, 1)]

/-- Data spans of a new `Ext8` form. -/
def new8 (core : State) (next : Word) : Ext8.New → List (Word × Nat)
  | .alu _ dst _ | .aluI _ dst _ | .test dst _ | .shift _ dst _ | .mov dst _ | .setcc _ dst =>
    rm8 core next dst
  | .aluR _ _ src | .movR _ src | .movx _ _ _ src => rm8 core next src
  | .aluA .. => []

end X86Accesses

/-- `x86NativeStep` with the `Ext8` fetch. -/
def x86NativeStep8 (s : X86State) : MachineResult (AccessReport X86State) :=
  if s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    match rflagsImage s.m.core.flags with
    | none => .unmodeled
    | some _ => .ok ⟨{ s with pending := some (s.m.core.read .rax) }, [(s.m.core.rip, 2)]⟩
  else
    match Silmaril.X86.Ext8.fetch s.m.memory s.m.core.rip.toNat with
    | .inl .undecodable => .unmodeled
    | .inl .truncated => .fault
    | .inl (.decoded instruction length) =>
      x86ExecResult ((s.m.core.rip, length) :: X86Accesses.canonical s.m.core length instruction)
        (Silmaril.X86.Ext.exec instruction s.m.core s.m.memory length)
    | .inr (instruction, length) =>
      x86ExecResult ((s.m.core.rip, length) ::
          X86Accesses.new8 s.m.core (s.m.core.rip + BitVec.ofNat 64 length) instruction)
        (Silmaril.X86.Ext8.execNew instruction s.m.core s.m.memory
          (s.m.core.rip + BitVec.ofNat 64 length))

/-- **Agreement**: where `X86.Ext` decodes, the variant's step is the native step. -/
theorem x86NativeStep8_eq (s : X86State)
    (h : Silmaril.X86.Ext.fetch s.m.memory s.m.core.rip.toNat ≠ .undecodable) :
    x86NativeStep8 s = x86NativeStep s := by
  unfold x86NativeStep8 x86NativeStep
  rw [Silmaril.X86.Ext8.fetch_of_ne_undecodable h]
  split
  · rfl
  · cases e : Silmaril.X86.Ext.fetch s.m.memory s.m.core.rip.toNat with
    | undecodable => exact absurd e h
    | truncated => rfl
    | decoded i n => rfl

/-- **Agreement**: the variant's step is the native step, or the native step is
`unmodeled`. -/
theorem x86NativeStep8_eq_or_unmodeled (s : X86State) :
    x86NativeStep8 s = x86NativeStep s ∨ x86NativeStep s = .unmodeled := by
  by_cases h : Silmaril.X86.Ext.fetch s.m.memory s.m.core.rip.toNat = .undecodable
  · by_cases hs : s.m.memory.fetchBytes s.m.core.rip.toNat 2 = some [0x0f, 0x05]
    · left; unfold x86NativeStep8 x86NativeStep; simp only [hs, ↓reduceIte]; split <;> rename_i e <;> simp [e]
    · right; unfold x86NativeStep; simp only [hs, h, ↓reduceIte]
  · exact .inl (x86NativeStep8_eq s h)

namespace X86FlagChoices

/-- `X86FlagChoices.step` over the `Ext8` variant. -/
def step8 (oracle : Nat → Choice) (state : State) : MachineResult (AccessReport State) :=
  if state.native.m.memory.fetchBytes state.native.m.core.rip.toNat 2 = some [0x0f, 0x05] then
    lift (state.counter + 1) (x86NativeStep8 (completeState state.native (oracle state.counter)))
  else lift state.counter (x86NativeStep8 state.native)

/-- **Agreement**: where `X86.Ext` decodes, `step8` is `step`. -/
theorem step8_eq (oracle : Nat → Choice) (state : State)
    (h : Silmaril.X86.Ext.fetch state.native.m.memory state.native.m.core.rip.toNat ≠
      .undecodable) :
    step8 oracle state = step oracle state := by
  unfold step8 step
  split
  · rw [x86NativeStep8_eq (completeState state.native (oracle state.counter)) h]
  · rw [x86NativeStep8_eq state.native h]

end X86FlagChoices

/-- `x86WithFlagOracle` over the `Ext8` variant. -/
def x86WithFlagOracle8 (oracle : Nat → X86FlagChoices.Choice) : UserIsa :=
  { x86WithFlagOracle oracle with step := fun _ => X86FlagChoices.step8 oracle }

end Silmaril.Process.LPS.Machines
