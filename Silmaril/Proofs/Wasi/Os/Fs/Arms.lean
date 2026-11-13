module

public import Silmaril.Wasi.Os.Fs.Defs
public import Silmaril.Machine.Process.IoSpec.Thms
public import Silmaril.Machine.Process.LpsBridge.Thms

/-!
# Proofs: the `openat`, file `write` and `close` arms are sound for LPS

* Sys combinators in closed form: `bind_modify_iff`, `recordCopyins_iff`,
  `recordCopyins_retOnly_iff`, `retOnly_ne_unmodeled`.
* Dispatch: `close_dispatch` (number 3 is `close_spec`); number 1 is `write_dispatch` of
  `LpsBridge`. **`openat_pending`** (a refutation of soundness for `openat`): number 257 is
  still *pending* in the bridge's native table (`openat` is not a reviewed name), so `spec`
  answers it `unmodeled`.
* Closed forms: `create_core_iff`, **`openat_create_iff`** (`openat` of a plain name with
  `O_WRONLY|O_CREAT|O_TRUNC`), **`write_fileW_iff`** (`write` to a `fileW` descriptor),
  **`close_iff`** (`close` of a bound descriptor). Each is an `↔` over every outcome, so none
  of them is `unmodeled`.
* **`armSound_writeFile`**, **`armSound_close`** and **`sound_fsEnv`**:
  `Sound (fsEnv segs) segs refused`, for every segment list and refusal filter.
* `openat`: **`openCreate_spec`** (the arm's answers are exactly the outcomes of LPS's
  reference `openat_spec`), **`openCreate_unmodeled`** and **`not_armSound_openCreate`** (it is
  not sound for the bridge's table at any trap it handles in a live process).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Os

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Sys
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Proofs.Machine.Process.LpsBridge (bind_choose_iff input_getModel_iff write_dispatch)
open Silmaril.Proofs.Machine.Process.IoSpec (sound_ofArms armSound_exit armSound_write armSound_read)

/-! ## Sys combinators -/

theorem bind_modify_iff {β : Type} (f : Silmaril.Process.LPS.Model → Silmaril.Process.LPS.Model)
    (k : Unit → Sys β) (i : SyscallInput) (m : Silmaril.Process.LPS.Model) (o : Outcome β) :
    (modify f >>= k) i m o ↔ k () i (f m) o := by
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, e₁, e₂, hx, hk, rfl⟩
      cases hx; simpa using hk
    · intro hk
      exact ⟨(), f m, [], evs, rfl, hk, rfl⟩
  | unmodeled =>
    constructor
    · rintro (hx | ⟨x, m₁, e₁, hx, hk⟩)
      · cases hx
      · cases hx; exact hk
    · intro hk
      exact .inr ⟨(), f m, [], rfl, hk⟩

theorem recordCopyins_iff (reads : List (Word × Nat)) (s : Sys SyscallEffect) (i : SyscallInput)
    (m : Silmaril.Process.LPS.Model) (o : Outcome SyscallEffect) :
    recordCopyins reads s i m o ↔ (o = .unmodeled ∧ s i m .unmodeled) ∨
      ∃ eff m' evs, s i m (.ok eff m' evs) ∧ o = .ok (eff.withCopyins (reads ++ eff.copyins)) m' evs := by
  show Sys.bind _ _ i m o ↔ _
  cases o with
  | ok y m₂ evs =>
    constructor
    · rintro ⟨x, m₁, e₁, e₂, hx, hk, rfl⟩
      cases hk; exact .inr ⟨x, _, _, hx, by simp⟩
    · rintro (⟨h, -⟩ | ⟨eff, m', evs', hs, h⟩)
      · cases h
      · cases h; exact ⟨eff, _, _, [], hs, rfl, by simp⟩
  | unmodeled =>
    constructor
    · rintro (hx | ⟨x, m₁, e₁, hx, hk⟩)
      · exact .inl ⟨rfl, hx⟩
      · cases hk
    · rintro (⟨-, h⟩ | ⟨eff, m', evs', -, h⟩)
      · exact .inl h
      · cases h

theorem recordCopyins_retOnly_iff (reads : List (Word × Nat)) (r : Word) (i : SyscallInput)
    (m : Silmaril.Process.LPS.Model) (o : Outcome SyscallEffect) :
    recordCopyins reads (retOnly r) i m o ↔ o = .ok ((mkEffect r [] []).withCopyins (reads ++ [])) m [] := by
  rw [recordCopyins_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨eff, m', evs, h, rfl⟩)
    · cases h
    · cases h; rfl
  · intro h
    exact .inr ⟨_, m, [], rfl, h⟩

/-! ## Dispatch -/

/-- **Number 257 is still pending in the bridge's native table**: `openat` is not in
`NativeX86.reviewedNames`, so `spec` answers it `unmodeled`. -/
theorem openat_pending (i : SyscallInput) (m : Silmaril.Process.LPS.Model)
    (number : i.sysno.toNat = 257) : NativeX86.extendedSyscallSpec i m .unmodeled := by
  simp only [NativeX86.extendedSyscallSpec, dispatch, number]
  exact rfl

/-- Number 3 of the native table is LPS `close_spec`. -/
theorem close_dispatch (i : SyscallInput) (m : Silmaril.Process.LPS.Model)
    (o : Outcome SyscallEffect) (number : i.sysno.toNat = 3) :
    NativeX86.extendedSyscallSpec i m o ↔
      closeSpec (fd32 (i.arg 0)) (NativeX86.referenceInputFor ⟨57, 3, "close"⟩ i) m o := by
  simp only [NativeX86.extendedSyscallSpec, dispatch, number]
  rfl

/-! ## `openat` of a plain name for writing -/

/-- `create_wronly` in closed form. -/
theorem createWronly_iff (p : Fs.Path) (i : SyscallInput) (m : Silmaril.Process.LPS.Model)
    (o : Outcome SyscallEffect) :
    createWronly p m i m o ↔
      (∃ err ∈ openatErrnos, o = .ok (mkEffect (errnoRet err) [] []) m []) ∨
      (fdLookup m.fds (allocFd m.fds) = none ∧
        o = .ok (mkEffect (allocFd m.fds) [] []) (createModel m p (allocFd m.fds)) []) := by
  unfold createWronly
  show _ ∨ _ ↔ _
  refine or_congr ?_ ?_
  · exact bind_choose_iff _ _ i m o
  · unfold lowestFd
    rw [bind_choose_iff]
    simp only [bind_modify_iff]
    constructor
    · rintro ⟨fd, ⟨h1, rfl⟩, h⟩
      exact ⟨h1, h⟩
    · rintro ⟨h1, h⟩
      exact ⟨_, ⟨h1, rfl⟩, h⟩

/-- The `openat` core on a plain name with `O_WRONLY|O_CREAT|O_TRUNC`. -/
theorem create_core_iff (dirfd pathp flags : Word) (p : Fs.Path) (i : SyscallInput)
    (m : Silmaril.Process.LPS.Model) (o : Outcome SyscallEffect)
    (hfl : openResidue flags = wrCreateFlags) (hd : (dirfd == AT_FDCWD32) = true)
    (hp : readCstr i.mem pathp = .ok p) (hne : Fs.pathEqb p [] = false)
    (hsl : pathHasSlash p = false) (hdot : pathIsDirref p = false) (hu : fsUnder m.fs p = false) :
    openatCoreSpec dirfd pathp flags i m o ↔ createWronly p m i m o := by
  have hmod : modeledOpenFlags flags = true := by simp [modeledOpenFlags, hfl]
  have h0 : (wrCreateFlags == 0) = false := by decide
  unfold openatCoreSpec
  rw [bind_input_iff, bind_getModel_iff]
  simp only [hmod, Bool.not_true, Bool.false_eq_true, ite_false]
  unfold openatBodySpec openatResolvedSpec openatCreateSpec
  simp only [hp, hne, hd, hsl, hdot, hu, hfl, h0, Bool.not_true, Bool.false_eq_true, ite_false,
    beq_self_eq_true, ite_true, Bool.or_self]

/-- **LPS `openat` of a plain name for writing, closed form.** -/
theorem openat_create_iff (dirfd pathp flags : Word) (p : Fs.Path) (i : SyscallInput)
    (m : Silmaril.Process.LPS.Model) (o : Outcome SyscallEffect)
    (hfl : openResidue flags = wrCreateFlags) (hd : (dirfd == AT_FDCWD32) = true)
    (hp : readCstr i.mem pathp = .ok p) (hne : Fs.pathEqb p [] = false)
    (hsl : pathHasSlash p = false) (hdot : pathIsDirref p = false) (hu : fsUnder m.fs p = false) :
    openatSpec dirfd pathp flags i m o ↔
      ∃ r m', ((∃ err ∈ openatErrnos, r = errnoRet err ∧ m' = m) ∨
          (fdLookup m.fds (allocFd m.fds) = none ∧ r = allocFd m.fds ∧
            m' = createModel m p (allocFd m.fds))) ∧
        o = .ok ((mkEffect r [] []).withCopyins
          ([(pathp, cstrAccessLenAux i.mem pathp pathMax)] ++ [])) m' [] := by
  unfold openatSpec
  rw [bind_input_iff, recordCopyins_iff]
  have hc := fun o' => (create_core_iff dirfd pathp flags p i m o' hfl hd hp hne hsl hdot hu).trans
    (createWronly_iff p i m o')
  constructor
  · rintro (⟨-, h⟩ | ⟨eff, m', evs, h, rfl⟩)
    · rcases (hc _).1 h with ⟨err, -, h'⟩ | ⟨-, h'⟩ <;> cases h'
    · rcases (hc _).1 h with ⟨err, he, h'⟩ | ⟨hl, h'⟩ <;> cases h'
      · exact ⟨_, _, .inl ⟨err, he, rfl, rfl⟩, rfl⟩
      · exact ⟨_, _, .inr ⟨hl, rfl, rfl⟩, rfl⟩
  · rintro ⟨r, m', (⟨err, he, rfl, rfl⟩ | ⟨hl, rfl, rfl⟩), rfl⟩
    · exact .inr ⟨_, _, [], (hc _).2 (.inl ⟨err, he, rfl⟩), rfl⟩
    · exact .inr ⟨_, _, [], (hc _).2 (.inr ⟨hl, rfl⟩), rfl⟩

/-! ## `write` to a write-only file -/

/-- **LPS `write` to a `fileW` descriptor, closed form.** -/
theorem write_fileW_iff (fd buf count : Word) (p : Fs.Path) (off : Word) (data : List Byte)
    (i : SyscallInput) (m : Silmaril.Process.LPS.Model) (o : Outcome SyscallEffect)
    (lookup : fdLookup m.fds fd = some (.fileW p off)) (hdata : Fs.lookup m.fs p = some data)
    (modeled : modeledRwRangeWith accessOkb buf count = true) (nonzero : wIs0 count = false)
    (source : writeSource i.mem buf count ≠ [])
    (gap : modeledFileGap data off (writeSource i.mem buf count) = true) :
    writeSpec fd buf count i m o ↔
      o = .ok ((mkEffect (lenWord (writeSource i.mem buf count)) [] []).withCopyins
          ([(buf, (writeSource i.mem buf count).length)] ++ []))
        (writeFileModel m fd p off data (writeSource i.mem buf count)) [] := by
  have len : ((writeSource i.mem buf count).length == 0) = false := by
    cases h : writeSource i.mem buf count with
    | nil => exact absurd h source
    | cons => rfl
  unfold writeSpec writeSpecWith
  rw [input_getModel_iff]
  simp only [lookup]
  unfold writeFileWith writeRangeGateWith writeFileTailWith writeLedger
  simp only [modeled, nonzero, len, hdata, gap, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.and_false, ite_false]
  rw [bind_modify_iff, bind_modify_iff, recordCopyins_retOnly_iff]
  rfl

/-! ## `close` -/

/-- **LPS `close` of a bound descriptor, closed form.** -/
theorem close_iff (fd : Word) (i : SyscallInput) (m : Silmaril.Process.LPS.Model)
    (o : Outcome SyscallEffect) (h : (fdLookup m.fds fd).isSome) :
    closeSpec fd i m o ↔ o = .ok (mkEffect 0 [] []) (m.withFds (fdRemove m.fds fd)) [] := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
  unfold closeSpec
  rw [bind_getModel_iff]
  simp only [hx]
  exact bind_modify_iff _ _ i m o

/-! ## Soundness of the arms -/

variable {segs : List Segment} {refused : RefusalFilter}

/-- A model update that keeps the process fields: it is not killed and keeps no lazy
reservation when the model was alive and had none. -/
theorem alive_of_proc {model model' : Silmaril.Process.LPS.Model}
    (hp : model'.proc = model.proc) (hv : model'.vm.lazy = model.vm.lazy)
    (hh : model.halted = none) (hl : model.vmLazy = []) :
    model'.killedBy = none ∧ (model'.halted = none → model'.vmLazy = []) ∧
      ∀ code, model'.halted = some code → False := by
  have hh' : model'.halted = none := by simpa [Model.halted, hp] using hh
  refine ⟨?_, fun _ => by simpa [Model.vmLazy, hv] using hl, fun code hc => ?_⟩
  · simp only [Model.killedBy]
    simp only [Model.halted] at hh'
    simp [hh']
  · rw [hh'] at hc
    cases hc

/-- **The `openat` arm is not sound for the bridge's table**: at every trap it handles, LPS's
native x86-64 table answers `unmodeled` (number 257 is pending). -/
theorem openCreate_unmodeled {s : X86State} {e : Silmaril.Process.LPS.Model}
    (h : (openCreateArm segs).Handles s e) : spec (reqOf segs s) e .unmodeled :=
  openat_pending _ e h.1

/-- So `openCreateArm` is `ArmSound` only if it handles no trap of a live process. -/
theorem not_armSound_openCreate {m : MState} {ch : X86FlagChoices.Choice}
    {e : Silmaril.Process.LPS.Model} (hh : e.halted = none) (hl : e.vmLazy = [])
    (ht : AtSyscall m) (hH : (openCreateArm segs).Handles (trapped ⟨m, none⟩ ch) e) :
    ¬ ArmSound segs refused (openCreateArm segs) := fun hS =>
  (hS m ch e e rfl hh hl ht ⟨_, List.mem_singleton_self _, hH⟩).1 (openCreate_unmodeled hH)

/-- **`openat` of a plain name for writing, against LPS's reference `openat_spec`**: every
outcome of `openat_spec` (at the request's arguments) is an answer of `openCreateArm`, so the
arm is what a native table with a reviewed `openat` would answer. -/
theorem openCreate_spec {s : X86State} {e : Silmaril.Process.LPS.Model}
    (h : (openCreateArm segs).Handles s e) (eff : SyscallEffect)
    (model' : Silmaril.Process.LPS.Model) (evs : List Event)
    (hs : openatSpec (reqFd segs s) ((reqOf segs s).arg 1) ((reqOf segs s).arg 2) (reqOf segs s) e
      (.ok eff model' evs)) :
    (openCreateArm segs).out s e (.resume (resume s eff) model' evs) := by
  obtain ⟨-, hfl, hd, p, hp, hne, hsl, hdot, hu⟩ := h
  obtain ⟨r, m', hcase, ho⟩ := (openat_create_iff _ _ _ p _ e _ hfl hd hp hne hsl hdot hu).1 hs
  cases ho
  rcases hcase with ⟨err, he, rfl, rfl⟩ | ⟨hlk, rfl, rfl⟩
  · exact ⟨p, hp, .inl ⟨err, he, rfl⟩⟩
  · exact ⟨p, hp, .inr ⟨hlk, rfl⟩⟩

/-- Nor is `openat_spec` ever `unmodeled` there. -/
theorem openCreate_spec_modeled {s : X86State} {e : Silmaril.Process.LPS.Model}
    (h : (openCreateArm segs).Handles s e) :
    ¬ openatSpec (reqFd segs s) ((reqOf segs s).arg 1) ((reqOf segs s).arg 2) (reqOf segs s) e
      .unmodeled := fun hs => by
  obtain ⟨-, hfl, hd, p, hp, hne, hsl, hdot, hu⟩ := h
  obtain ⟨r, m', -, ho⟩ := (openat_create_iff _ _ _ p _ e _ hfl hd hp hne hsl hdot hu).1 hs
  cases ho

/-- **The file `write` arm is sound.** -/
theorem armSound_writeFile : ArmSound segs refused (writeFileArm segs) := by
  intro m ch model e he hh hl ht ⟨a, ha, hH⟩
  rw [List.mem_singleton] at ha
  subst ha
  have hH0 := hH
  change e = model at he
  subst he
  obtain ⟨hno, p, off, data, lookup, hdata, modeled, nonzero, source, gap⟩ := hH
  have iff := fun o => (write_dispatch _ e o hno).trans
    (write_fileW_iff _ _ _ p off data _ e o lookup hdata modeled nonzero source gap)
  refine ⟨fun hs => ?_, fun eff model' evs hs => ?_⟩
  · cases (iff _).1 hs
  · have h := (iff _).1 hs
    cases h
    refine ⟨(alive_of_proc rfl rfl hh hl).1, fun hh' => ⟨(alive_of_proc rfl rfl hh hl).2.1 hh',
      fun _ => ⟨_, rfl, _, List.mem_singleton_self _, hH0, p, off, data, lookup, hdata, rfl⟩⟩,
      fun code hc => ((alive_of_proc rfl rfl hh hl).2.2 code hc).elim⟩

/-- **The `close` arm is sound.** -/
theorem armSound_close : ArmSound segs refused (closeArm segs) := by
  intro m ch model e he hh hl ht ⟨a, ha, hH⟩
  rw [List.mem_singleton] at ha
  subst ha
  have hH0 := hH
  change e = model at he
  subst he
  obtain ⟨hno, hsome⟩ := hH
  have iff := fun o => (close_dispatch _ e o hno).trans (close_iff _ _ e o hsome)
  refine ⟨fun hs => ?_, fun eff model' evs hs => ?_⟩
  · cases (iff _).1 hs
  · have h := (iff _).1 hs
    cases h
    refine ⟨(alive_of_proc rfl rfl hh hl).1, fun hh' => ⟨(alive_of_proc rfl rfl hh hl).2.1 hh',
      fun _ => ⟨_, rfl, _, List.mem_singleton_self _, hH0, rfl⟩⟩,
      fun code hc => ((alive_of_proc rfl rfl hh hl).2.2 code hc).elim⟩

/-- **The LPS environment with the filesystem arms is sound.** -/
theorem sound_fsEnv : Sound (fsEnv segs) segs refused :=
  sound_ofArms fun a ha => by
    simp only [fsArms, lpsArms, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact armSound_exit
    · exact armSound_write
    · exact armSound_read
    · exact armSound_writeFile
    · exact armSound_close

end Silmaril.Wasi.Os
