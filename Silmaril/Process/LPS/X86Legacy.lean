module

public import Silmaril.Process.LPS.Run

/-! # Opt-in legacy x86-64 syscall adapters

These are additional native entry points, outside the ninety-arm reference
surface. A supplied reference model and refusal filter are paired, and both
receive the identical transformed input. User memory views are never replaced.

This module deliberately does not install family translations. In particular,
stat/lstat require a separately supplied x86-layout newfstatat model; a RISC-V
stat buffer cannot be used as an x86 stat buffer. Finite poll timeouts need a
value-level poll helper and remain unmodeled instead of inventing a pointer to
a synthetic timespec. Negative signed 32-bit poll timeouts are supported.

getrlimit is fixed to the x86-64 LP64 ABI: its two unsigned-long fields have the
same encoding as the two u64 prlimit64 fields, including RLIM_INFINITY. The
encoding identity below is specific to this ABI.

The wrapper shapes follow Linux v6.12 fs/open.c (open/access), fs/stat.c
(stat/lstat/readlink), fs/namei.c (unlink), fs/pipe.c (pipe), fs/file.c (dup2),
fs/select.c (poll), and kernel/sys.c (getrlimit/prlimit64). This is an adapter
for supplied LPS specifications, not a proof of the Linux implementations.
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.NativeX86.Legacy

/-- Keep specification and refusal interpretation together when adapting calls. -/
structure SourceModel where
  spec : Sys SyscallEffect
  refused : RefusalFilter

structure Backend where
  reference : SourceModel
  /-- Optional newfstatat model with the x86-64 stat output layout, NOT the
  default RISC-V layout. Its input uses reference syscall number 79. -/
  x86Stat : Option SourceModel := none

/-- AT_FDCWD is passed as a C int; the source family performs its usual fd32
narrowing. The original negative constant and all other scalar arguments are
retained in the input translation. -/
def atFdcwd : Word := zw (-100)
def atSymlinkNofollow : Word := 0x100

/-- Change only the syscall selector and argument vector. -/
def referenceInput (input : SyscallInput) (number : Nat) (args : List Word) : SyscallInput :=
  { input with sysno := zw number, args := args }

@[simp] theorem referenceInput_mem (input : SyscallInput) (number : Nat) (args : List Word) :
    (referenceInput input number args).mem = input.mem := rfl

@[simp] theorem referenceInput_wmem (input : SyscallInput) (number : Nat) (args : List Word) :
    (referenceInput input number args).wmem = input.wmem := rfl

@[simp] theorem referenceInput_args (input : SyscallInput) (number : Nat) (args : List Word) :
    (referenceInput input number args).args = args := rfl

/-- Linux poll takes a signed C int, even when the x86 register has high bits. -/
def pollMilliseconds (input : SyscallInput) : Int := ((input.arg 2).setWidth 32).toInt

/-- A useful value-level conversion for a future ppoll helper. None denotes
infinity; a finite pair is (seconds, nanoseconds). It is not a userspace pointer. -/
def millisecondsToTimespec (milliseconds : Int) : Option (Nat × Nat) :=
  if milliseconds < 0 then none
  else some (milliseconds.toNat / 1000, (milliseconds.toNat % 1000) * 1000000)

theorem millisecondsToTimespec_negative (milliseconds : Int) (negative : milliseconds < 0) :
    millisecondsToTimespec milliseconds = none := by
  simp [millisecondsToTimespec, negative]

theorem millisecondsToTimespec_finite (milliseconds : Int) (nonnegative : 0 ≤ milliseconds) :
    millisecondsToTimespec milliseconds =
      some (milliseconds.toNat / 1000, (milliseconds.toNat % 1000) * 1000000) := by
  simp [millisecondsToTimespec, not_lt.mpr nonnegative]

theorem finite_nanoseconds_bound (milliseconds : Int) :
    (milliseconds.toNat % 1000) * 1000000 < 1000000000 := by
  have remainder := Nat.mod_lt milliseconds.toNat (by decide : 0 < 1000)
  omega

inductive Unsupported where
  | unknownNumber
  | finitePollTimeout
  deriving DecidableEq, Repr

/-- Source selection is shared by the semantics and refusal filter. -/
inductive Selection where
  | reference (input : SyscallInput)
  | x86Stat (input : SyscallInput)
  | dup2Self (fd : Word)
  | unsupported (reason : Unsupported)

def select (input : SyscallInput) : Selection :=
  match input.sysno.toNat with
  | 2 => .reference (referenceInput input 56
      [atFdcwd, input.arg 0, input.arg 1, input.arg 2])
  | 4 => .x86Stat (referenceInput input 79 [atFdcwd, input.arg 0, input.arg 1, 0])
  | 6 => .x86Stat (referenceInput input 79
      [atFdcwd, input.arg 0, input.arg 1, atSymlinkNofollow])
  | 7 =>
      if pollMilliseconds input < 0 then
        .reference (referenceInput input 73 [input.arg 0, input.arg 1, 0, 0, 8])
      else .unsupported .finitePollTimeout
  | 21 => .reference (referenceInput input 48 [atFdcwd, input.arg 0, input.arg 1])
  | 22 => .reference (referenceInput input 59 [input.arg 0, 0])
  | 33 =>
      if fd32 (input.arg 0) = fd32 (input.arg 1) then .dup2Self (fd32 (input.arg 0))
      else .reference (referenceInput input 24 [input.arg 0, input.arg 1, 0])
  | 87 => .reference (referenceInput input 35 [atFdcwd, input.arg 0, 0])
  | 89 => .reference (referenceInput input 78
      [atFdcwd, input.arg 0, input.arg 1, input.arg 2])
  | 97 => .reference (referenceInput input 261 [0, input.arg 0, 0, input.arg 1])
  | _ => .unsupported .unknownNumber

/-- dup2(fd,fd) checks the old descriptor and returns it without touching its
flags or closing anything. In particular it is NOT dup3(fd,fd,0), which errors. -/
def dup2SelfSpec (fd : Word) : Sys SyscallEffect := fun input model outcome =>
  match fdLookup model.fds fd with
  | none => errRet EBADF input model outcome
  | some _ => retOnly fd input model outcome

/-- Only selectors and scalar argument vectors are adapted. Neither user
memory view can be replaced by an alias, including optional stat aliases. -/
def Selection.PreservesMemory (input : SyscallInput) : Selection → Prop
  | .reference source | .x86Stat source => source.mem = input.mem ∧ source.wmem = input.wmem
  | .dup2Self _ | .unsupported _ => True

theorem select_preserves_memory (input : SyscallInput) :
    (select input).PreservesMemory input := by
  unfold select
  split <;> first
    | exact ⟨rfl, rfl⟩
    | trivial
    | split <;> first | exact ⟨rfl, rfl⟩ | trivial

theorem select_open (input : SyscallInput) (number : input.sysno = 2) :
    select input = .reference (referenceInput input 56
      [atFdcwd, input.arg 0, input.arg 1, input.arg 2]) := by
  simp only [select, number]
  rfl

theorem select_stat (input : SyscallInput) (number : input.sysno = 4) :
    select input = .x86Stat (referenceInput input 79
      [atFdcwd, input.arg 0, input.arg 1, 0]) := by
  simp only [select, number]
  rfl

theorem select_lstat (input : SyscallInput) (number : input.sysno = 6) :
    select input = .x86Stat (referenceInput input 79
      [atFdcwd, input.arg 0, input.arg 1, atSymlinkNofollow]) := by
  simp only [select, number]
  rfl

theorem select_poll_infinite (input : SyscallInput) (number : input.sysno = 7)
    (negative : pollMilliseconds input < 0) :
    select input = .reference (referenceInput input 73 [input.arg 0, input.arg 1, 0, 0, 8]) := by
  simp only [select, number]
  exact ite_eq_left negative

theorem select_poll_finite (input : SyscallInput) (number : input.sysno = 7)
    (nonnegative : 0 ≤ pollMilliseconds input) :
    select input = .unsupported .finitePollTimeout := by
  simp only [select, number]
  exact ite_eq_right (not_lt.mpr nonnegative)

theorem select_access (input : SyscallInput) (number : input.sysno = 21) :
    select input = .reference (referenceInput input 48 [atFdcwd, input.arg 0, input.arg 1]) := by
  simp only [select, number]
  rfl

theorem select_pipe (input : SyscallInput) (number : input.sysno = 22) :
    select input = .reference (referenceInput input 59 [input.arg 0, 0]) := by
  simp only [select, number]
  rfl

theorem select_dup2_same (input : SyscallInput) (number : input.sysno = 33)
    (same : fd32 (input.arg 0) = fd32 (input.arg 1)) :
    select input = .dup2Self (fd32 (input.arg 0)) := by
  simp only [select, number]
  exact ite_eq_left same

theorem select_dup2_distinct (input : SyscallInput) (number : input.sysno = 33)
    (distinct : fd32 (input.arg 0) ≠ fd32 (input.arg 1)) :
    select input = .reference (referenceInput input 24 [input.arg 0, input.arg 1, 0]) := by
  simp only [select, number]
  exact ite_eq_right distinct

theorem select_unlink (input : SyscallInput) (number : input.sysno = 87) :
    select input = .reference (referenceInput input 35 [atFdcwd, input.arg 0, 0]) := by
  simp only [select, number]
  rfl

theorem select_readlink (input : SyscallInput) (number : input.sysno = 89) :
    select input = .reference (referenceInput input 78
      [atFdcwd, input.arg 0, input.arg 1, input.arg 2]) := by
  simp only [select, number]
  rfl

theorem select_getrlimit (input : SyscallInput) (number : input.sysno = 97) :
    select input = .reference (referenceInput input 261 [0, input.arg 0, 0, input.arg 1]) := by
  simp only [select, number]
  rfl

/-- Interpret an explicitly selected legacy entry point. -/
def spec (backend : Backend) : Sys SyscallEffect := fun input model outcome =>
  match select input with
  | .reference source => backend.reference.spec source model outcome
  | .x86Stat source =>
      match backend.x86Stat with
      | some family => family.spec source model outcome
      | none => Sys.unmodeled source model outcome
  | .dup2Self fd => dup2SelfSpec fd input model outcome
  | .unsupported _ => Sys.unmodeled input model outcome

/-- Every delegated refusal query uses precisely the same source input as the
semantics. Local dup2 self-calls have no injected-failure alternative. -/
def refused (backend : Backend) : RefusalFilter := fun input model effect =>
  match select input with
  | .reference source => backend.reference.refused source model effect
  | .x86Stat source =>
      match backend.x86Stat with
      | some family => family.refused source model effect
      | none => False
  | .dup2Self _ | .unsupported _ => False

/-- Native arms are opt-in. Reference-family completeness and ABI review remain
the responsibility of the explicitly supplied backend. -/
def arms (backend : Backend) : List SpecArm :=
  [⟨2, "open", .translated, spec backend⟩,
   ⟨4, "stat", if backend.x86Stat.isSome then .translated else .pending, spec backend⟩,
   ⟨6, "lstat", if backend.x86Stat.isSome then .translated else .pending, spec backend⟩,
   ⟨7, "poll", .translated, spec backend⟩,
   ⟨21, "access", .translated, spec backend⟩,
   ⟨22, "pipe", .translated, spec backend⟩,
   ⟨33, "dup2", .translated, spec backend⟩,
   ⟨87, "unlink", .translated, spec backend⟩,
   ⟨89, "readlink", .translated, spec backend⟩,
   ⟨97, "getrlimit", .translated, spec backend⟩]

theorem arm_numbers (backend : Backend) :
    armNumbers (arms backend) = [2, 4, 6, 7, 21, 22, 33, 87, 89, 97] := rfl

theorem arm_numbers_nodup (backend : Backend) : (armNumbers (arms backend)).Nodup := by
  rw [arm_numbers]
  decide +kernel

/-- Dispatching any of the ten opt-in numbers reaches its adapter, rather
than accidentally selecting a different native or reference entry point. -/
theorem dispatch_adapter (backend : Backend) (input : SyscallInput)
    (model : Model) (outcome : Outcome SyscallEffect)
    (number : input.sysno.toNat ∈ [2, 4, 6, 7, 21, 22, 33, 87, 89, 97]) :
    dispatch (arms backend) input model outcome ↔ spec backend input model outcome := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at number
  rcases number with number | number | number | number | number | number | number |
    number | number | number <;>
    simp [dispatch, arms, lookupArm, number]

theorem spec_reference (backend : Backend) (input source : SyscallInput)
    (model : Model) (outcome : Outcome SyscallEffect)
    (selected : select input = .reference source) :
    spec backend input model outcome ↔ backend.reference.spec source model outcome := by
  simp [spec, selected]

theorem refused_reference (backend : Backend) (input source : SyscallInput)
    (model : Model) (effect : SyscallEffect)
    (selected : select input = .reference source) :
    refused backend input model effect ↔ backend.reference.refused source model effect := by
  simp [refused, selected]

theorem spec_stat (backend : Backend) (input source : SyscallInput) (family : SourceModel)
    (model : Model) (outcome : Outcome SyscallEffect)
    (selected : select input = .x86Stat source) (installed : backend.x86Stat = some family) :
    spec backend input model outcome ↔ family.spec source model outcome := by
  simp [spec, selected, installed]

theorem stat_requires_layout (backend : Backend) (input source : SyscallInput)
    (model : Model) (outcome : Outcome SyscallEffect)
    (selected : select input = .x86Stat source) (absent : backend.x86Stat = none) :
    spec backend input model outcome ↔ outcome = .unmodeled := by
  simp [spec, selected, absent, Sys.unmodeled]

theorem spec_unsupported (backend : Backend) (input : SyscallInput) (reason : Unsupported)
    (model : Model) (outcome : Outcome SyscallEffect)
    (selected : select input = .unsupported reason) :
    spec backend input model outcome ↔ outcome = .unmodeled := by
  simp [spec, selected, Sys.unmodeled]

theorem spec_dup2_self (backend : Backend) (input : SyscallInput) (fd : Word)
    (model : Model) (outcome : Outcome SyscallEffect)
    (selected : select input = .dup2Self fd) :
    spec backend input model outcome ↔ dup2SelfSpec fd input model outcome := by
  simp [spec, selected]

theorem dup2_self_valid (fd : Word) (input : SyscallInput) (model : Model)
    (entry : FdEntry) (outcome : Outcome SyscallEffect) (valid : fdLookup model.fds fd = some entry) :
    dup2SelfSpec fd input model outcome ↔ outcome = .ok (mkEffect fd [] []) model [] := by
  simp [dup2SelfSpec, valid, retOnly, Sys.pure]

theorem dup2_self_invalid (fd : Word) (input : SyscallInput) (model : Model)
    (outcome : Outcome SyscallEffect) (invalid : fdLookup model.fds fd = none) :
    dup2SelfSpec fd input model outcome ↔
      outcome = .ok (mkEffect (errnoRet EBADF) [] []) model [] := by
  simp [dup2SelfSpec, invalid, errRet, retOnly, Sys.pure]

theorem dup2_self_not_refused (backend : Backend) (input : SyscallInput)
    (model : Model) (effect : SyscallEffect) (fd : Word)
    (selected : select input = .dup2Self fd) :
    ¬ refused backend input model effect := by
  simp [refused, selected]

/-- The fixed LP64 limit conversion is identity, including infinity. This
would fail for the analogous conversion to a 32-bit unsigned long. -/
def limitToX86 (value : Word) : Word :=
  BitVec.ofNat 64 (min value.toNat (2 ^ 64 - 1))

theorem limitToX86_eq (value : Word) : limitToX86 value = value := by
  unfold limitToX86
  rw [Nat.min_eq_left (by have := value.isLt; omega)]
  simp

structure Rlimit64 where
  current : Word
  maximum : Word

def prlimit64Bytes (limit : Rlimit64) : List Byte :=
  zToLeBytes 8 (uns limit.current) ++ zToLeBytes 8 (uns limit.maximum)

def x86RlimitBytes (limit : Rlimit64) : List Byte :=
  zToLeBytes 8 (uns (limitToX86 limit.current)) ++
    zToLeBytes 8 (uns (limitToX86 limit.maximum))

theorem getrlimit_layout_compatible (limit : Rlimit64) :
    x86RlimitBytes limit = prlimit64Bytes limit := by
  simp only [x86RlimitBytes, prlimit64Bytes, limitToX86_eq]

theorem getrlimit_size (limit : Rlimit64) : (x86RlimitBytes limit).length = 16 := by
  simp [x86RlimitBytes, zToLeBytes]

end Silmaril.Process.LPS.NativeX86.Legacy
