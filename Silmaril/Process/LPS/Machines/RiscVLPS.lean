module

public import Silmaril.Process.LPS.Isa
public import Silmaril.Process.LPS.StackLayout
public import Silmaril.RiscV.LPS.Machine

/-!
# LPS's own RV64GC machine under the LPS process layer

`riscvLps : UserIsa` runs `Silmaril.RiscV.LPS`, the translation of LPS's RISC-V ISA
(`Riscv/*.v`) and of its user-mode step over Linux virtual memory (`RiscvSemantics.v`), as an
LPS process. Every field is the literal translation of the LPS definition the process layer
calls:

| `UserIsa` field | LPS definition | Lean |
| --- | --- | --- |
| `State` | `RiscvSemantics.v:100` `machine_state` | `RiscV.LPS.MachineState` |
| `step` | `RiscvSemantics.v:1042` `step_accesses` | `RiscV.LPS.stepAccesses` |
| `svcPending` | `ms_svc_pending` | `MachineState.svcPending` |
| `syscallArgs` | `Run.v:92` `syscall_args` | `MachineState.gpr 0..5` |
| `readByte` | `RiscvSemantics.v:217` `ms_read_byte` | `MachineState.readByte` |
| `writableByte` | `RiscvSemantics.v:542` `ms_writable_byte` | `MachineState.writableByte` |
| `applyEffect` | `Run.v:175` `apply_effect` | `set_reg` of a0, then `Overlay.applyEffect` |
| `advancePastSvc` | `Run.v:191` `advance_past_svc` | pc + 4, pending cleared |
| `init` | `Run.v:1058` `init_machine_state` | `lpsInit` |
| `entryFetchable` | `Equivalence.v:436` `image_entry_fetchable` | `lpsEntryFetchable` |
| `reportsAccesses` | `true`: `step_accesses` reports every data range | |

So the compressed (16-bit parcel) fetch, IALIGN = 16, the w+x fetch through the overlay,
misaligned plain loads and stores performed, misaligned LR/SC/AMO faulting before the
reservation check, the defined-illegal split (all-zero parcel, writes to read-only CSRs) and
the `fault`/`unmodeled` classification of failed fetches are LPS's own; the checks of
`RiscVLPSChecks` pin them.

The only representation change is the segment: the process layer's `Segment`
(`MemImageType.v:16`, `"rwx"` letters and decoded bytes) is converted by `lpsSegment` to the
ISA port's `RiscV.LPS.Segment` (permission bits and a byte array). The letters are read with
the same `String.contains` test as `seg_readable`/`seg_writable`/`seg_executable`
(`MemImageType.v:95-97`), and the bytes are unchanged, so every segment query agrees.
LPS stores segment bytes as hex chunks. The process layer's segment holds a hole-free
`List Byte` (see `MemImage.lean`); the ISA port's holds an `Option Byte` per byte, so that
`RiscV.LPS.Segment.ofHex` keeps a bad hex digit pair as a hole at exactly that byte, as
upstream (`segmentByteAt_ofHex`). `lpsSegment` maps every byte to `some`
(`segmentByteAt_bytesData`). The chunk checks of `RiscvSegmentChunks.v` are ported in
`RiscVLPSChecks`.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Machines

/-- A process-layer segment as an ISA-port segment: the `"rwx"` letters as permission bits
(LPS `MemImageType.v:95-97`), every byte present. -/
def lpsSegment (s : Segment) : RiscV.LPS.Segment where
  base := s.base
  size := s.size
  perms := ⟨s.readable, s.writable, s.executable⟩
  data := RiscV.LPS.Segment.bytesData s.bytes

/-- The loaded segments (`mi_loaded_segments`) in the ISA port's representation. -/
def lpsSegments (segs : List Segment) : List RiscV.LPS.Segment := segs.map lpsSegment

/-- The ISA port's `machine_result`/`access_report` as the process layer's (the same
inductive, `RiscvSemantics.v:203` and `:825`, declared once in each layer). -/
def ofLpsResult {α : Type} :
    RiscV.LPS.MachineResult (RiscV.LPS.AccessReport α) → MachineResult (AccessReport α)
  | .ok r => .ok ⟨r.value, r.ranges⟩
  | .fault => .fault
  | .unmodeled => .unmodeled

/-- LPS `RiscvSemantics.v:1042` `step_accesses`, over the loaded image. -/
def lpsStep (segs : List Segment) (st : RiscV.LPS.MachineState) :
    MachineResult (AccessReport RiscV.LPS.MachineState) :=
  ofLpsResult (RiscV.LPS.stepAccesses (lpsSegments segs) st)

/-- LPS `Run.v:92` `syscall_args`: a0..a5. -/
def lpsSyscallArgs (st : RiscV.LPS.MachineState) : List Word :=
  [st.gpr 0, st.gpr 1, st.gpr 2, st.gpr 3, st.gpr 4, st.gpr 5]

/-- LPS `Run.v:175` `apply_effect`: a0 := the return value (`set_reg`), then unmaps, zeros,
copies from the snapshot and writes on the overlay (`Overlay.applyEffect`); the read-only
backing is unchanged. -/
def lpsApplyEffect (st : RiscV.LPS.MachineState) (eff : SyscallEffect) :
    RiscV.LPS.MachineState :=
  let st' := st.setReg 10 eff.ret
  { st' with mem := Overlay.applyEffect st'.mem eff }

/-- LPS `Run.v:191` `advance_past_svc`: pc + 4, the pending syscall cleared. -/
def lpsAdvancePastSvc (st : RiscV.LPS.MachineState) : RiscV.LPS.MachineState :=
  { st with pcVal := st.pc + 4, svcPending := none }

/-- LPS `Run.v:1058` `init_machine_state`: sp and a0 = 0 in the register map, an empty FP
file, fcsr = 0, no reservation, pc at the entry point; the overlay holds the entry block at
`sp` (`stack_to_mem`) over zeros in the `stack_max_size` bytes below `sp`; the read-only
backing is the readable segments (`memory_read … 1`). -/
def lpsInit (segs : List Segment) (pc : Nat) (sp : Word) (stack : List Byte) :
    RiscV.LPS.MachineState where
  regs := RiscV.LPS.BvMap.set (2 : BitVec 5) sp
    (RiscV.LPS.BvMap.set (10 : BitVec 5) 0 (RiscV.LPS.BvMap.empty (n := 5)))
  fregs := RiscV.LPS.BvMap.empty (n := 5)
  pcVal := BitVec.ofNat 64 pc
  svcPending := none
  resv := none
  fcsr := 0
  mem := fun addr =>
    match stackToMem sp stack addr with
    | some b => some b
    | none => if uns sp - stackMaxSize ≤ uns addr ∧ uns addr < uns sp then some 0 else none
  rom := fun addr =>
    match RiscV.LPS.memoryRead (lpsSegments segs) addr 1 with
    | some (b :: _) => some b
    | _ => none

/-- LPS `Equivalence.v:436` `image_entry_fetchable`: the entry point fetches through
`fetch_word`, `fetch_word_wx` or `fetch_tail_any` over an empty overlay. -/
def lpsEntryFetchable (segs : List Segment) (pc : Nat) : Bool :=
  let addr := BitVec.ofNat 64 pc
  let segs := lpsSegments segs
  match RiscV.LPS.fetchWord segs addr with
  | some _ => true
  | none =>
    match RiscV.LPS.fetchWordWx segs addr with
    | some _ => true
    | none =>
      match RiscV.LPS.fetchTailAny segs (fun _ => none) addr with
      | some _ => true
      | none => false

/-- LPS's own RV64GC machine (`RiscvSemantics.v`) as an LPS user machine. -/
def riscvLps : UserIsa where
  State := RiscV.LPS.MachineState
  step := lpsStep
  svcPending st := st.svcPending
  syscallArgs := lpsSyscallArgs
  readByte _ st := st.readByte
  writableByte segs st := RiscV.LPS.MachineState.writableByte (lpsSegments segs) st
  applyEffect := lpsApplyEffect
  advancePastSvc := lpsAdvancePastSvc
  init := lpsInit
  reportsAccesses := true
  entryFetchable := lpsEntryFetchable

/-! ## The step, unfolded

`step_accesses` decodes the first word one of its three fetch paths returns; `lpsFetch` is
that word. -/

/-- The word `step_accesses` decodes: `fetch_word`, else `fetch_word_ov`, else
`fetch_tail_any` (`RiscvSemantics.v:1042`). -/
def lpsFetch (segs : List RiscV.LPS.Segment) (st : RiscV.LPS.MachineState) :
    Option (BitVec 32) :=
  match RiscV.LPS.fetchWord segs st.pc with
  | some w => some w
  | none =>
    match RiscV.LPS.fetchWordOv segs st.mem st.pc with
    | some w => some w
    | none => RiscV.LPS.fetchTailAny segs st.mem st.pc

theorem stepAccesses_of_lpsFetch {segs : List RiscV.LPS.Segment} {st : RiscV.LPS.MachineState}
    {w : BitVec 32} (h : lpsFetch segs st = some w) :
    RiscV.LPS.stepAccesses segs st = RiscV.LPS.decodeExecAccesses segs st w := by
  unfold lpsFetch at h
  unfold RiscV.LPS.stepAccesses
  cases h1 : RiscV.LPS.fetchWord segs st.pc with
  | some w' => simp only [h1, Option.some.injEq] at h ⊢; rw [h]
  | none =>
    cases h2 : RiscV.LPS.fetchWordOv segs st.mem st.pc with
    | some w' => simp only [h1, h2, Option.some.injEq] at h ⊢; rw [h]
    | none => simp only [h1, h2] at h ⊢; rw [h]

/-- `riscvLps.step` is `step_accesses` with the reports carried over unchanged. -/
theorem riscvLps_step (segs : List Segment) (st : RiscV.LPS.MachineState) :
    riscvLps.step segs st = ofLpsResult (RiscV.LPS.stepAccesses (lpsSegments segs) st) := rfl

end Silmaril.Process.LPS.Machines
