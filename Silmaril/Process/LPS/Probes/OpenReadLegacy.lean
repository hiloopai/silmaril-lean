module

public import Silmaril.Process.LPS.Probes.OpenRead
public import Silmaril.Process.LPS.Probes.Data.OpenReadLegacy

/-! # Probe `open_read_legacy`

`open_read_legacy.s` is `open_read` with the legacy `open("in.txt", O_RDONLY)` (number 2)
in place of `openat(AT_FDCWD, "in.txt", O_RDONLY)`; the open block has the same length, so
every later instruction and the path sit at the same offsets. On Linux the harness recorded
`open(…) = 3`, `read(3, sp, 64) = 3`, `write(1, sp, 3) = 3`, `close(3) = 0`, stdout `hi\n`
and exit status 0 (`Data.OpenReadLegacy.observed`).

* `OpenReadLegacy.admits`: the model admits that run.
* `OpenReadLegacy.exec`, `OpenReadLegacy.sound`: at the harness launch every execution has
  one of `open_read`'s outcomes (`ReadThenPrint`): the hub's legacy `open` (the translated
  arm, `OpenLegacy.hub_open_translated`) opens like `openat` at `AT_FDCWD`, with the same
  injected errnos.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

namespace OpenReadLegacy

open Data.OpenReadLegacy

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInputFiles_valid _ (by unfold Fs.ValidFs; decide) (by decide),
    probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem name_read : cstrOfList (probe.bytes.drop 213) pathMax = .ok inName := by decide +kernel

/-- The entry stack is writable where the `read` delivers. -/
theorem stack_writable :
    (readBytesMap (viewByte probe.mem0 .write) probe.entry.sp (lenWord contents)).isSome = true := by
  rw [readBytesMap_of _ _ _ (probe.stack.take 3) (by decide +kernel)
    (view_of_get _ _ _ _ (by decide +kernel) (fun k bound => ?_) (by decide +kernel))]
  · rfl
  · have length : k < probe.stack.length := by
      simp only [List.length_take] at bound
      omega
    rw [List.getElem_take]
    exact probe.mem0_stack_get (by decide +kernel) k length

/-- The memory after the `read` still holds the image. -/
theorem intact_read : probe.Intact (memWith probe.mem0 probe.entry.sp contents) :=
  (Probe.intact_mem0 probe).install _ _ (by decide +kernel) (by decide +kernel)

/-- After the `read`, the stack holds the file's bytes. -/
theorem view_read : ∀ k (bound : k < contents.length),
    viewByte (memWith probe.mem0 probe.entry.sp contents) .read
      (probe.entry.sp + BitVec.ofNat 64 k) = some contents[k] :=
  view_installed _ _ _ _ (by decide +kernel) (by decide +kernel)

theorem exec : Omni.Exec probe.segs spec noFilter probe.initial (ReadThenPrint contents observed.files) := by
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rbp 0)
  probe_instr 125 5 (.movI32 .rax 2)
  probe_instr 130 5 (.movI32 .rdi 0x4000d5)
  probe_instr 135 5 (.movI32 .rsi 0)
  probe_instr 140 5 (.movI32 .rdx 0)
  probe_trap 145
  probe_open (spec_open_read (clear := ?_) (path := inName) ?_ ?_ ?_
    (readCstr_image (off := 213) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
  · probe_instr 147 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 150 5 (.movI32 .rax 0)
    probe_instr 155 3 (.mov .q (.reg .rdi) .rbx)
    probe_instr 158 3 (.mov .q (.reg .rsi) .rsp)
    probe_instr 161 5 (.movI32 .rdx 64)
    probe_trap 166
    probe_read (spec_read_file (clear := ?_) (path := inName) (off := 0) (data := contents) (bs := contents)
      ?_ ?_ ?_ ?_ ?_ ?_ stack_writable) at probe.entry.sp
    have intact := intact_read
    probe_instrM 168 3 (.mov .q (.reg .rdx) .rax)
    probe_instrM 171 4 (.aluI8 .q .cmp (.reg .rdx) 0)
    probe_instrM 175 4 (.cmov .q .l .rdx (.reg .rbp))
    probe_instrM 179 5 (.movI32 .rax 1)
    probe_instrM 184 5 (.movI32 .rdi 1)
    probe_trapM 189
    probe_channel (spec_write_channel (clear := ?_) (ch := 1) ?_ ?_ ?_ ?_ ?_ (writeSource_of_view ?_ view_read ?_)
      ?_ ?_)
    intro ds delivered
    probe_instrM 191 5 (.movI32 .rax 3)
    probe_instrM 196 3 (.mov .q (.reg .rdi) .rbx)
    probe_trapM 199
    probe_call (spec_close_open (clear := ?_) ?_ ?_)
    -- `close`'s number is not `158`: the registers mention the delivered `ds`, so
    -- `decide` refuses the goal; evaluation by `rfl` still decides it.
    all_goals try exact of_decide_eq_true (by rfl)
    probe_instrM 201 5 (.movI32 .rax 60)
    probe_instrM 206 5 (.movI32 .rdi 0)
    probe_trapM 211
    probe_exitM 0
    exact ReadThenPrint.printed delivered rfl rfl rfl rfl
  · intro e member
    rcases openatErrnos_cases member with rfl | rfl | rfl | rfl
    all_goals
      probe_instr 147 3 (.mov .q (.reg .rbx) .rax)
      probe_instr 150 5 (.movI32 .rax 0)
      probe_instr 155 3 (.mov .q (.reg .rdi) .rbx)
      probe_instr 158 3 (.mov .q (.reg .rsi) .rsp)
      probe_instr 161 5 (.movI32 .rdx 64)
      probe_trap 166
      probe_call (spec_read_badfd (clear := ?_) ?_ ?_)
      probe_instr 168 3 (.mov .q (.reg .rdx) .rax)
      probe_instr 171 4 (.aluI8 .q .cmp (.reg .rdx) 0)
      probe_instr 175 4 (.cmov .q .l .rdx (.reg .rbp))
      probe_instr 179 5 (.movI32 .rax 1)
      probe_instr 184 5 (.movI32 .rdi 1)
      probe_trap 189
      probe_call (spec_write_zero (clear := ?_) (ch := 1) ?_ ?_ ?_ ?_ ?_ ?_)
      probe_instr 191 5 (.movI32 .rax 3)
      probe_instr 196 3 (.mov .q (.reg .rdi) .rbx)
      probe_trap 199
      probe_call (spec_close_badfd (clear := ?_) ?_ ?_)
      probe_instr 201 5 (.movI32 .rax 60)
      probe_instr 206 5 (.movI32 .rdi 0)
      probe_trap 211
      probe_exit 0
      exact .openFailed _ member rfl rfl rfl rfl

theorem sound (refused : RefusalFilter) {trace : List Event} {outcome : Omni.Outcome x86ExtNative}
    (finite : Omni.FiniteExec probe.segs spec refused probe.initial trace outcome) :
    ReadThenPrint contents observed.files trace outcome :=
  Omni.Exec.sound_any exec finite

/-- Reality is admitted: the file's bytes travel from the launch file system
through the stack to stdout. -/
theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rbp 0)
    probe_instr 125 5 (.movI32 .rax 2)
    probe_instr 130 5 (.movI32 .rdi 0x4000d5)
    probe_instr 135 5 (.movI32 .rsi 0)
    probe_instr 140 5 (.movI32 .rdx 0)
    probe_trap 145
    probe_open (spec_open_read (clear := ?_) (path := inName) ?_ ?_ ?_
      (readCstr_image (off := 213) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
    probe_instr 147 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 150 5 (.movI32 .rax 0)
    probe_instr 155 3 (.mov .q (.reg .rdi) .rbx)
    probe_instr 158 3 (.mov .q (.reg .rsi) .rsp)
    probe_instr 161 5 (.movI32 .rdx 64)
    probe_trap 166
    probe_read (spec_read_file (clear := ?_) (path := inName) (off := 0) (data := contents) (bs := contents)
      ?_ ?_ ?_ ?_ ?_ ?_ stack_writable) at probe.entry.sp
    have intact := intact_read
    probe_instrM 168 3 (.mov .q (.reg .rdx) .rax)
    probe_instrM 171 4 (.aluI8 .q .cmp (.reg .rdx) 0)
    probe_instrM 175 4 (.cmov .q .l .rdx (.reg .rbp))
    probe_instrM 179 5 (.movI32 .rax 1)
    probe_instrM 184 5 (.movI32 .rdi 1)
    probe_trapM 189
    probe_channel (spec_write_channel (clear := ?_) (ch := 1) ?_ ?_ ?_ ?_ ?_ (writeSource_of_view ?_ view_read ?_)
      ?_ ?_) with contents
    probe_instrM 191 5 (.movI32 .rax 3)
    probe_instrM 196 3 (.mov .q (.reg .rdi) .rbx)
    probe_trapM 199
    probe_call (spec_close_open (clear := ?_) ?_ ?_)
    probe_instrM 201 5 (.movI32 .rax 60)
    probe_instrM 206 5 (.movI32 .rdi 0)
    probe_trapM 211
    probe_exitM 0
  all_goals probe_side

theorem no_error (refused : RefusalFilter) : ¬ (probe.behavior refused).errors :=
  Omni.Exec.no_error exec (fun _ _ post => by cases post)

end OpenReadLegacy

end Silmaril.Process.LPS.Probes
