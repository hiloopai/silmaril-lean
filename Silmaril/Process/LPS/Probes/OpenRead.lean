module

public import Silmaril.Process.LPS.Probes.Files
public import Silmaril.Process.LPS.Probes.Data.OpenRead
public import Silmaril.Process.LPS.Probes.Data.OpenReadName
public import Silmaril.Process.LPS.Probes.Data.OpenReadWr

/-! # Probe `open_read` and its mutants `open_read_name` and `open_read_wr`

`open_read.s` opens `in.txt` (`openat(AT_FDCWD, "in.txt", O_RDONLY)`), reads up to
64 bytes into the entry stack (`read(fd, rsp, 64)`), writes what it read to stdout
(a negative count becomes 0 through `cmp`/`cmovl`), closes the descriptor and exits 0.
The launch file system, and the harness's work directory, hold `in.txt` = `hi\n`.
On Linux the harness recorded `openat(…) = 3`, `read(3, sp, 64) = 3`,
`write(1, sp, 3) = 3`, `close(3) = 0`, exit status 0, stdout `hi\n` and the work
directory unchanged (`Data.OpenRead.observed`; `sp` is the randomized entry stack
pointer, `Observed.stackArgs`).

* `OpenRead.admits`: the model admits that run of the actual bytes: the file's bytes
  are read from the launch file system into the entry stack, and written from there.
* `OpenRead.exec`, `OpenRead.sound`: every execution exits 0 with the launch file
  system unchanged, in one of three named outcomes (`ReadThenPrint`): `full` (all of
  `hi\n` printed), `shortWrite` (the reference short write: a nonempty proper prefix),
  or `openFailed` (`openat` failed with an injected `ENOMEM`, `EACCES`, `EMFILE` or
  `ENFILE`; `read` and `close` then fail with `EBADF` and nothing is printed).

Mutants (each one byte):

* `open_read_name.s` opens `in.txu`, which the file system lacks: Linux answers
  `ENOENT`, `read`/`close` `EBADF`, and prints nothing. The model determines that run
  (`OpenReadName.determined`) and never shows `hi\n` (`not_traces_original`).
* `open_read_wr.s` calls `write` (1) instead of `read` (0) on the read-only
  descriptor: Linux answers `EBADF` and prints nothing. So does every execution of the
  model (`OpenReadWr.determined`, `not_traces_original`).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Silmaril.Process.LPS.Probes

open Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Machines.X86Launch

/-- The outcomes of a probe that opens a file, reads it and prints what it read. -/
inductive ReadThenPrint (contents : List Byte) (fs : Fs.FileSystem) : Omni.Post x86ExtNative where
  /-- The whole file was printed. -/
  | full {trace : List Event} {final : Config x86ExtNative} :
      trace = contents.map (.writeEv 1) ++ [.exitEv 0 fs] → final.model.halted = some 0 →
      final.model.killedBy = none → final.model.fs = fs → ReadThenPrint contents fs trace (.halt final)
  /-- The reference short write: stdout accepted a nonempty proper prefix. -/
  | shortWrite {ds : List Byte} {trace : List Event} {final : Config x86ExtNative} :
      ds ≠ [] → ds <+: contents → ds ≠ contents →
      trace = ds.map (.writeEv 1) ++ [.exitEv 0 fs] → final.model.halted = some 0 →
      final.model.killedBy = none → final.model.fs = fs → ReadThenPrint contents fs trace (.halt final)
  /-- `openat` failed with the injected errno `e`; nothing was printed. -/
  | openFailed {trace : List Event} {final : Config x86ExtNative} (e : Int) :
      e ∈ openatErrnos → trace = [.exitEv 0 fs] → final.model.halted = some 0 →
      final.model.killedBy = none → final.model.fs = fs → ReadThenPrint contents fs trace (.halt final)

theorem ReadThenPrint.printed {contents ds : List Byte} {fs : Fs.FileSystem} {trace : List Event}
    {final : Config x86ExtNative} (delivered : Probe.WritePrefix contents ds)
    (events : trace = ds.map (.writeEv 1) ++ [.exitEv 0 fs]) (halted : final.model.halted = some 0)
    (unkilled : final.model.killedBy = none) (files : final.model.fs = fs) :
    ReadThenPrint contents fs trace (.halt final) := by
  by_cases all : ds = contents
  · subst all
    exact .full events halted unkilled files
  · exact .shortWrite delivered.1 delivered.2 all events halted unkilled files

/-- The name `open_read` and `open_read_wr` open: `in.txt`. -/
def inName : List Byte := [105, 110, 46, 116, 120, 116]

/-- The contents of `in.txt`: `hi\n`. -/
def contents : List Byte := [104, 105, 10]

namespace OpenRead

open Data.OpenRead

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
  probe_instr 125 5 (.movI32 .rax 257)
  probe_instr 130 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 135 5 (.movI32 .rsi 0x4000d5)
  probe_instr 140 5 (.movI32 .rdx 0)
  probe_trap 145
  probe_open (spec_openat_read (clear := ?_) (path := inName) ?_ ?_ ?_ ?_
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
    probe_instr 125 5 (.movI32 .rax 257)
    probe_instr 130 5 (.movI32 .rdi 0xffffff9c)
    probe_instr 135 5 (.movI32 .rsi 0x4000d5)
    probe_instr 140 5 (.movI32 .rdx 0)
    probe_trap 145
    probe_open (spec_openat_read (clear := ?_) (path := inName) ?_ ?_ ?_ ?_
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

end OpenRead

namespace OpenReadName

open Data.OpenReadName

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInputFiles_valid _ (by unfold Fs.ValidFs; decide) (by decide),
    probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

/-- The mutated name: `in.txu`. -/
def name : List Byte := [105, 110, 46, 116, 120, 117]

theorem name_read : cstrOfList (probe.bytes.drop 213) pathMax = .ok name := by decide +kernel

/-- Every execution: `ENOENT`, then `EBADF` twice, nothing printed, exit 0. -/
theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rbp 0)
  probe_instr 125 5 (.movI32 .rax 257)
  probe_instr 130 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 135 5 (.movI32 .rsi 0x4000d5)
  probe_instr 140 5 (.movI32 .rdx 0)
  probe_trap 145
  probe_call (spec_openat_missing (clear := ?_) (path := name) ?_ ?_ ?_ ?_
    (readCstr_image (off := 213) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_)
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
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rbp 0)
    probe_instr 125 5 (.movI32 .rax 257)
    probe_instr 130 5 (.movI32 .rdi 0xffffff9c)
    probe_instr 135 5 (.movI32 .rsi 0x4000d5)
    probe_instr 140 5 (.movI32 .rdx 0)
    probe_trap 145
    probe_call (spec_openat_missing (clear := ?_) (path := name) ?_ ?_ ?_ ?_
      (readCstr_image (off := 213) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_)
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
  all_goals probe_side

/-- Mutation: no trace of the mutant shows the original's output `hi\n`. -/
theorem not_traces_original (refused : RefusalFilter) (fs : Fs.FileSystem) :
    ¬ (probe.behavior refused).traces (Data.OpenRead.observed.events fs) := by
  intro traced
  obtain ⟨rest, _, pre, final, _, same, _⟩ := Omni.Exec.obsTrace determined traced
  have long := pre.length_le
  rw [same] at long
  have four : (Data.OpenRead.observed.events fs).length = 4 := rfl
  have one : (observed.events final.model.fs).length = 1 := rfl
  omega

end OpenReadName

namespace OpenReadWr

open Data.OpenReadWr

theorem layout : probe.Layout := by probe_layout

instance checked : probe.Checked :=
  ⟨layout, harnessInputFiles_valid _ (by unfold Fs.ValidFs; decide) (by decide),
    probe.snapshot_valid layout, by unfold ValidBrk; decide +kernel⟩

theorem name_read : cstrOfList (probe.bytes.drop 213) pathMax = .ok inName := by decide +kernel

/-- Every execution prints nothing and exits 0, whether `openat` succeeds (the
write to the read-only descriptor is `EBADF`) or fails with an injected errno
(the write to the failed descriptor is `EBADF`). -/
theorem determined : probe.Determined noFilter observed := by
  unfold Probe.Determined
  rw [Probe.initial_at]
  probe_instr 120 5 (.movI32 .rbp 0)
  probe_instr 125 5 (.movI32 .rax 257)
  probe_instr 130 5 (.movI32 .rdi 0xffffff9c)
  probe_instr 135 5 (.movI32 .rsi 0x4000d5)
  probe_instr 140 5 (.movI32 .rdx 0)
  probe_trap 145
  probe_open (spec_openat_read (clear := ?_) (path := inName) ?_ ?_ ?_ ?_
    (readCstr_image (off := 213) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
  · probe_instr 147 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 150 5 (.movI32 .rax 1)
    probe_instr 155 3 (.mov .q (.reg .rdi) .rbx)
    probe_instr 158 3 (.mov .q (.reg .rsi) .rsp)
    probe_instr 161 5 (.movI32 .rdx 64)
    probe_trap 166
    probe_call (spec_write_readOnly (clear := ?_) (path := inName) (off := 0) ?_ ?_)
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
    probe_call (spec_close_open (clear := ?_) ?_ ?_)
    probe_instr 201 5 (.movI32 .rax 60)
    probe_instr 206 5 (.movI32 .rdi 0)
    probe_trap 211
    probe_exit 0
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  · intro e member
    rcases openatErrnos_cases member with rfl | rfl | rfl | rfl
    all_goals
      probe_instr 147 3 (.mov .q (.reg .rbx) .rax)
      probe_instr 150 5 (.movI32 .rax 1)
      probe_instr 155 3 (.mov .q (.reg .rdi) .rbx)
      probe_instr 158 3 (.mov .q (.reg .rsi) .rsp)
      probe_instr 161 5 (.movI32 .rdx 64)
      probe_trap 166
      probe_call (spec_write_badfd (clear := ?_) ?_ ?_)
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
      exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem admits : probe.Admits noFilter observed := by
  apply Probe.admits_of
  case run =>
    rw [Probe.initial_at]
    probe_instr 120 5 (.movI32 .rbp 0)
    probe_instr 125 5 (.movI32 .rax 257)
    probe_instr 130 5 (.movI32 .rdi 0xffffff9c)
    probe_instr 135 5 (.movI32 .rsi 0x4000d5)
    probe_instr 140 5 (.movI32 .rdx 0)
    probe_trap 145
    probe_open (spec_openat_read (clear := ?_) (path := inName) ?_ ?_ ?_ ?_
      (readCstr_image (off := 213) ?_ ?_ ?_ name_read) ?_ ?_ ?_ ?_ ?_)
    probe_instr 147 3 (.mov .q (.reg .rbx) .rax)
    probe_instr 150 5 (.movI32 .rax 1)
    probe_instr 155 3 (.mov .q (.reg .rdi) .rbx)
    probe_instr 158 3 (.mov .q (.reg .rsi) .rsp)
    probe_instr 161 5 (.movI32 .rdx 64)
    probe_trap 166
    probe_call (spec_write_readOnly (clear := ?_) (path := inName) (off := 0) ?_ ?_)
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
    probe_call (spec_close_open (clear := ?_) ?_ ?_)
    probe_instr 201 5 (.movI32 .rax 60)
    probe_instr 206 5 (.movI32 .rdi 0)
    probe_trap 211
    probe_exit 0
  all_goals probe_side

/-- Mutation: no trace of the mutant shows the original's output `hi\n`. -/
theorem not_traces_original (refused : RefusalFilter) (fs : Fs.FileSystem) :
    ¬ (probe.behavior refused).traces (Data.OpenRead.observed.events fs) := by
  intro traced
  obtain ⟨rest, _, pre, final, _, same, _⟩ := Omni.Exec.obsTrace determined traced
  have long := pre.length_le
  rw [same] at long
  have four : (Data.OpenRead.observed.events fs).length = 4 := rfl
  have one : (observed.events final.model.fs).length = 1 := rfl
  omega

end OpenReadWr

end Silmaril.Process.LPS.Probes
