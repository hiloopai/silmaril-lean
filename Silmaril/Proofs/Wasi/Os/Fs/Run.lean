module

public import Silmaril.Proofs.Wasi.Os.Fs.Arms
public import Silmaril.Wasi.Os.Thms

/-!
# Proofs: `writeFile`'s x86 runtimes through `IoSpec`, and the end-to-end theorems

* Dispatch on environments made of the arms of `allArms`: `mem_allArms`, `arm_exit`,
  `arm_close`, `arm_writeFile`, `arm_open`; the `exit` rule `ioSafe_exitA`.
* `tail_close`, **`tail_write`**: the tail of a runtime (`WriteTail`: `write` of `hi`, `close`,
  `exit 0`) is `IoSafeN` from a model where its descriptor is a `fileW` on an empty `out.txt`.
* **`redirectRt_ioSafe`**, **`redirectRt_psafe`**: a runtime launched with `out.txt` open
  (`RedirectRt`) is `IoSafeN` with the sound `fsEnv`, for `redirAllowed`, and LPS process-safe
  on every agreeing native machine.
* **`writeFileRt_ioSafe`**: a runtime that opens `out.txt` itself (`WriteFileRt`) is `IoSafeN`
  with `fsEnvO`, for `wfAllowed`. **`writeFileRt_not_sound`** (refutation): on a live model,
  such a runtime makes `fsEnvO` unsound for the bridge's table, so no process-safety statement
  follows (`openat` is pending there).
* The WASI side: `fsOs_wfRun` (the replay of `wfRun`'s answers, in closed form),
  **`fsOs_wfRun_absent`**, **`fsOs_wfRun_empty`**.
* **`redirect_e2e`**, **`writeFile_e2e`**: the exit event's file system is the OS image
  `fsOs` of `writeFile`'s WASI run against `fsImpl`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Os

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Proofs.Machine.Process.IoSpec (ioSafe_of_safeN ioSafe_trap ioSafe_psafe)
open Silmaril.Wasi.Examples (hiBytes)

variable {c : MState → Option MState} {segs : List Segment} {arms : List Arm}
  {Q : MState → Silmaril.Process.LPS.Model → (List Event → Prop) → Prop}

/-! ## Dispatch -/

theorem mem_allArms {a : Arm} (h : a ∈ allArms segs) :
    a = exitArm ∨ a = writeArm segs ∨ a = readArm segs ∨ a = writeFileArm segs ∨
      a = closeArm segs ∨ a = openCreateArm segs := by
  simpa only [allArms, fsArms, lpsArms, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc] using h

/-- At an `exit` trap, the answers are `exitArm`'s. -/
theorem arm_exit (hsub : arms ⊆ allArms segs) {s : X86State} {e : Silmaril.Process.LPS.Model}
    {o : IoOut Silmaril.Process.LPS.Model} (h60 : (s.m.core.read .rax).toNat = 60)
    (ho : (ofArms arms).arm s e o) : exitArm.out s e o := by
  obtain ⟨a, ha, hH, ho⟩ := ho
  have hr : (reqOf segs s).sysno.toNat = 60 := h60
  rcases mem_allArms (hsub ha) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)

/-- At a `close` trap, the answers are `closeArm`'s. -/
theorem arm_close (hsub : arms ⊆ allArms segs) {s : X86State} {e : Silmaril.Process.LPS.Model}
    {o : IoOut Silmaril.Process.LPS.Model} (h3 : (reqOf segs s).sysno.toNat = 3)
    (ho : (ofArms arms).arm s e o) : (closeArm segs).out s e o := by
  obtain ⟨a, ha, hH, ho⟩ := ho
  have hr : (s.m.core.read .rax).toNat = 3 := h3
  rcases mem_allArms (hsub ha) with rfl | rfl | rfl | rfl | rfl | rfl
  · have hx : (s.m.core.read .rax).toNat = 60 ∨ (s.m.core.read .rax).toNat = 231 := hH
    omega
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)
  · exact ho
  · exact absurd hH.1 (by omega)

/-- At a `write` trap on a `fileW` descriptor, the answers are `writeFileArm`'s. -/
theorem arm_writeFile (hsub : arms ⊆ allArms segs) {s : X86State}
    {e : Silmaril.Process.LPS.Model} {o : IoOut Silmaril.Process.LPS.Model} {p : Fs.Path}
    {off : Word} (h1 : (reqOf segs s).sysno.toNat = 1)
    (hlk : fdLookup e.fds (reqFd segs s) = some (.fileW p off))
    (ho : (ofArms arms).arm s e o) : (writeFileArm segs).out s e o := by
  obtain ⟨a, ha, hH, ho⟩ := ho
  have hr : (s.m.core.read .rax).toNat = 1 := h1
  rcases mem_allArms (hsub ha) with rfl | rfl | rfl | rfl | rfl | rfl
  · have hx : (s.m.core.read .rax).toNat = 60 ∨ (s.m.core.read .rax).toNat = 231 := hH
    omega
  · obtain ⟨ch, hch, -⟩ := hH.2
    have hx : some (FdEntry.fileW p off) = some (.channel ch) := hlk.symm.trans hch
    cases hx
  · exact absurd hH.1 (by omega)
  · exact ho
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)

/-- At an `openat` trap, the answers are `openCreateArm`'s. -/
theorem arm_open (hsub : arms ⊆ allArms segs) {s : X86State} {e : Silmaril.Process.LPS.Model}
    {o : IoOut Silmaril.Process.LPS.Model} (h257 : (reqOf segs s).sysno.toNat = 257)
    (ho : (ofArms arms).arm s e o) : (openCreateArm segs).out s e o := by
  obtain ⟨a, ha, hH, ho⟩ := ho
  have hr : (s.m.core.read .rax).toNat = 257 := h257
  rcases mem_allArms (hsub ha) with rfl | rfl | rfl | rfl | rfl | rfl
  · have hx : (s.m.core.read .rax).toNat = 60 ∨ (s.m.core.read .rax).toNat = 231 := hH
    omega
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)
  · exact absurd hH.1 (by omega)
  · exact ho

/-- **The `exit` rule** on an environment of `allArms` containing `exitArm`. -/
theorem ioSafe_exitA (hsub : arms ⊆ allArms segs) (hx : exitArm ∈ arms) {m : MState}
    {e : Silmaril.Process.LPS.Model} {A : List Event → Prop} (ht : AtSyscall m)
    (number : (m.core.read .rax).toNat = 60) (hA : A [])
    (hE : A [.exitEv (m.core.read .rdi &&& 255) e.fs]) :
    ∀ n, IoSafeN c (ofArms arms) Q n m e A :=
  ioSafe_trap ht hA fun _ => ⟨⟨exitArm, hx, .inl number⟩, fun o ho => by
    rw [arm_exit hsub number ho]
    exact hE⟩

/-! ## The tail: `write`, `close`, `exit 0` -/

/-- The `close` and the `exit 0`. -/
theorem tail_close {fd : Word} (T : WriteTail c segs fd) (hsub : arms ⊆ allArms segs)
    (hc : closeArm segs ∈ arms) (hx : exitArm ∈ arms) {e2 : Silmaril.Process.LPS.Model}
    (hfd : (fdLookup e2.fds fd).isSome) {A : List Event → Prop} (hA : A [])
    (hE : A [.exitEv 0 e2.fs]) : ∀ n, IoSafeN c (ofArms arms) Q n T.closeSt e2 A := by
  have hexit : ∀ e' : Silmaril.Process.LPS.Model, e'.fs = e2.fs →
      ∀ n, IoSafeN c (ofArms arms) Q n T.exitSt e' A := fun e' hfs =>
    ioSafe_exitA hsub hx T.exitTrap T.exitNo hA (by rw [T.exitCode, hfs]; exact hE)
  refine ioSafe_trap T.closeTrap hA fun k => ⟨⟨closeArm segs, hc, T.closeNo k, ?_⟩, fun o ho => ?_⟩
  · show (fdLookup e2.fds (fd32 ((reqAt segs T.closeSt k).arg 0))).isSome
    rw [T.closeFd k]
    exact hfd
  · rw [arm_close hsub (T.closeNo k) ho]
    exact fun n => ioSafe_of_safeN hA (fun _ hm => hm ▸ hexit _ rfl) n (T.closed k)

/-- The model after writing `hi` to an empty `out.txt` through `fd` keeps `fd` bound. -/
theorem writeFileModel_bound (e : Silmaril.Process.LPS.Model) (fd : Word) :
    (fdLookup (writeFileModel e fd outPath 0 [] hiBytes).fds fd).isSome := by
  simp [writeFileModel, Model.withFds, Model.withFs, Model.fds, fdInsert, fdLookup]

/-- The `write` request of the tail is handled by `writeFileArm` on such a model. -/
theorem tail_handles {fd : Word} (T : WriteTail c segs fd) {e1 : Silmaril.Process.LPS.Model}
    (hfd : fdLookup e1.fds fd = some (.fileW outPath 0)) (hfs : Fs.lookup e1.fs outPath = some [])
    (k : X86FlagChoices.Choice) : (writeFileArm segs).Handles (trapAt T.writeSt k) e1 := by
  have hfd' : fdLookup e1.fds (reqFd segs (trapAt T.writeSt k)) = some (.fileW outPath 0) := by
    show fdLookup e1.fds (fd32 ((reqAt segs T.writeSt k).arg 0)) = _
    rw [T.writeFd k]
    exact hfd
  have hne : reqSource segs (trapAt T.writeSt k) ≠ [] := by rw [T.writeBytes k]; decide
  have hgap : modeledFileGap [] 0 (reqSource segs (trapAt T.writeSt k)) = true := by
    rw [T.writeBytes k]; decide
  exact ⟨T.writeNo k, outPath, 0, [], hfd', hfs, T.writeRange k, T.writeCount k, hne, hgap⟩

/-- **The tail is `IoSafe`** from a model where `fd` is a `fileW` on an empty `out.txt`. -/
theorem tail_write {fd : Word} (T : WriteTail c segs fd) (hsub : arms ⊆ allArms segs)
    (hw : writeFileArm segs ∈ arms) (hc : closeArm segs ∈ arms) (hx : exitArm ∈ arms)
    {e1 : Silmaril.Process.LPS.Model} (hfd : fdLookup e1.fds fd = some (.fileW outPath 0))
    (hfs : Fs.lookup e1.fs outPath = some []) {A : List Event → Prop} (hA : A [])
    (hE : A [.exitEv 0 (tailFs e1.fs)]) : ∀ n, IoSafeN c (ofArms arms) Q n T.writeSt e1 A := by
  have hnext : ∀ n, IoSafeN c (ofArms arms) Q n T.closeSt
      (writeFileModel e1 fd outPath 0 [] hiBytes) A :=
    tail_close T hsub hc hx (writeFileModel_bound e1 fd) hA hE
  refine ioSafe_trap T.writeTrap hA fun k =>
    ⟨⟨writeFileArm segs, hw, tail_handles T hfd hfs k⟩, fun o ho => ?_⟩
  have hfd' : fdLookup e1.fds (reqFd segs (trapAt T.writeSt k)) = some (.fileW outPath 0) := by
    show fdLookup e1.fds (fd32 ((reqAt segs T.writeSt k).arg 0)) = _
    rw [T.writeFd k]
    exact hfd
  obtain ⟨p, off, data, h1, h2, h3⟩ := arm_writeFile hsub (T.writeNo k) hfd' ho
  have hpo : FdEntry.fileW p off = .fileW outPath 0 := Option.some.inj (h1.symm.trans hfd')
  cases hpo
  have hd : data = [] := Option.some.inj (h2.symm.trans hfs)
  have ho' : o = .resume (resume (trapAt T.writeSt k) (fileWEff segs (trapAt T.writeSt k) hiBytes))
      (writeFileModel e1 fd outPath 0 [] hiBytes) [] := by
    rw [h3, hd, T.writeBytes k]
    show IoOut.resume _ (writeFileModel e1 (fd32 ((reqAt segs T.writeSt k).arg 0)) _ _ _ _) _ = _
    rw [T.writeFd k]
    rfl
  rw [ho']
  exact fun n => ioSafe_of_safeN hA (fun _ hm => hm ▸ hnext) n (T.written k)

/-! ## The runtime launched with `out.txt` open -/

theorem fsArms_sub : fsArms segs ⊆ allArms segs := List.subset_append_left _ _

/-- **The redirected runtime is `IoSafe`** with the sound `fsEnv`. -/
theorem redirectRt_ioSafe {fd : Word} (R : RedirectRt c segs fd) {e : Silmaril.Process.LPS.Model}
    (hfd : fdLookup e.fds fd = some (.fileW outPath 0)) (hfs : Fs.lookup e.fs outPath = some []) :
    ∀ n, IoSafeN c (fsEnv segs) (fun _ _ _ => False) n R.start e (redirAllowed e.fs) := by
  have ht : ∀ n, IoSafeN c (fsEnv segs) (fun _ _ _ => False) n R.writeSt e (redirAllowed e.fs) :=
    tail_write R.toWriteTail fsArms_sub (by simp [fsArms]) (by simp [fsArms])
      (by simp [fsArms, lpsArms]) hfd hfs (.inl rfl) (.inr rfl)
  exact fun n => ioSafe_of_safeN (.inl rfl) (fun _ hm => hm ▸ ht) n R.toWrite

/-- **The redirected runtime is process-safe for LPS**, on every agreeing native machine. -/
theorem redirectRt_psafe {oracle : Oracle} {nstep : NStep} {refused : RefusalFilter} {fd : Word}
    (hM : Agrees nstep c) (R : RedirectRt c segs fd) {cfg : Config (flagMachine oracle nstep)}
    (al : AlignedF cfg R.start) (hfd : fdLookup cfg.model.fds fd = some (.fileW outPath 0))
    (hfs : Fs.lookup cfg.model.fs outPath = some []) :
    PSafeF segs refused (redirAllowed cfg.model.fs) cfg :=
  ioSafe_psafe hM sound_fsEnv (fun _ _ _ _ _ _ h => h.elim) al rfl (redirectRt_ioSafe R hfd hfs)

/-! ## The runtime that opens `out.txt` -/

/-- The model `openat` creates keeps the new descriptor on an empty `out.txt`. -/
theorem createModel_fd (e : Silmaril.Process.LPS.Model) (fd : Word) :
    fdLookup (createModel e outPath fd).fds fd = some (.fileW outPath 0) := by
  simp [createModel, Model.withFds, Model.withFs, Model.fds, fdInsert, fdLookup]

theorem createModel_fs (e : Silmaril.Process.LPS.Model) (fd : Word) :
    Fs.lookup (createModel e outPath fd).fs outPath = some [] :=
  lookup_set_self _ _ _

/-- The `openat` trap of the runtime is handled by `openCreateArm`. -/
theorem open_handles {e : Silmaril.Process.LPS.Model} (R : WriteFileRt c segs e)
    (hu : fsUnder e.fs outPath = false) (k : X86FlagChoices.Choice) :
    (openCreateArm segs).Handles (trapAt R.openSt k) e :=
  ⟨R.openNo k, R.openFlags k, R.openDir k, outPath, R.openPath k, by decide, by decide,
    by decide, hu⟩

/-- **The runtime that opens `out.txt` is `IoSafe`** with `fsEnvO`. -/
theorem writeFileRt_ioSafe {e : Silmaril.Process.LPS.Model} (R : WriteFileRt c segs e)
    (hu : fsUnder e.fs outPath = false) :
    ∀ n, IoSafeN c (fsEnvO segs) (fun _ _ _ => False) n R.start e (wfAllowed e.fs) := by
  have hfail : ∀ n, IoSafeN c (fsEnvO segs) (fun _ _ _ => False) n R.failSt e (wfAllowed e.fs) :=
    ioSafe_exitA (fun _ h => h) (by simp [allArms, fsArms, lpsArms]) R.failTrap R.failNo (.inl rfl)
      (by rw [R.failCode]; exact .inr (.inr rfl))
  have htail : ∀ n, IoSafeN c (fsEnvO segs) (fun _ _ _ => False) n R.writeSt
      (createModel e outPath (allocFd e.fds)) (wfAllowed e.fs) :=
    tail_write R.toWriteTail (fun _ h => h) (by simp [allArms, fsArms])
      (by simp [allArms, fsArms]) (by simp [allArms, fsArms, lpsArms]) (createModel_fd e _)
      (createModel_fs e _) (.inl rfl) (.inr (.inl rfl))
  have hopen : ∀ n, IoSafeN c (fsEnvO segs) (fun _ _ _ => False) n R.openSt e (wfAllowed e.fs) := by
    refine ioSafe_trap R.openTrap (.inl rfl) fun k =>
      ⟨⟨openCreateArm segs, by simp [allArms], open_handles R hu k⟩, fun o ho => ?_⟩
    obtain ⟨p, hp, hcase⟩ := arm_open (fun _ h => h) (R.openNo k) ho
    have hpo : CstrResult.ok p = .ok outPath := hp.symm.trans (R.openPath k)
    cases hpo
    rcases hcase with ⟨err, herr, rfl⟩ | ⟨-, rfl⟩
    · exact fun n => ioSafe_of_safeN (.inl rfl) (fun _ hm => hm ▸ hfail) n (R.failed k err herr)
    · exact fun n => ioSafe_of_safeN (.inl rfl) (fun _ hm => hm ▸ htail) n (R.opened k)
  exact fun n => ioSafe_of_safeN (.inl rfl) (fun _ hm => hm ▸ hopen) n R.toOpen

/-- **Refutation**: on a live model, a runtime that opens `out.txt` makes `fsEnvO` unsound for
the bridge's table, whose `openat` is pending. -/
theorem writeFileRt_not_sound {e : Silmaril.Process.LPS.Model} {refused : RefusalFilter}
    (R : WriteFileRt c segs e) (hu : fsUnder e.fs outPath = false) (hh : e.halted = none)
    (hl : e.vmLazy = []) (k : X86FlagChoices.Choice) : ¬ Sound (fsEnvO segs) segs refused :=
  fun hS => (hS R.openSt k e e rfl hh hl R.openTrap
    ⟨openCreateArm segs, by simp [allArms], open_handles R hu k⟩).1
      (openCreate_unmodeled (open_handles R hu k))

/-! ## The WASI side and the end-to-end theorems -/

open Silmaril.Wasi Silmaril.Wasi.Examples in
/-- The replay of `wfRun`'s host answers, in closed form. -/
theorem fsOs_wfRun (fs : Fs.FileSystem) :
    fsOs fs (hostView (wtrace wfRun)) =
      Fs.set (if (Fs.lookup fs outPath).isSome then fs else Fs.set fs outPath []) outPath
        (writeAt ((Fs.lookup (if (Fs.lookup fs outPath).isSome then fs else Fs.set fs outPath [])
          outPath).getD []) 0 (bytesOf (bytesV hiBytes))) :=
  rfl

theorem writeAt_hi : writeAt [] 0 hiBytes = Fs.fileWrite [] 0 hiBytes := by decide

/-- **On a file system without `out.txt`**, the replay of `wfRun` is `wfFs`. -/
theorem fsOs_wfRun_absent (fs : Fs.FileSystem) (h : Fs.lookup fs outPath = none) :
    fsOs fs (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace wfRun)) = wfFs fs := by
  rw [fsOs_wfRun, h]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
  rw [lookup_set_self, bytesOf_bytesV, Option.getD_some, writeAt_hi]
  rfl

/-- **On a file system where `out.txt` is empty**, the replay of `wfRun` is `tailFs`. -/
theorem fsOs_wfRun_empty (fs : Fs.FileSystem) (h : Fs.lookup fs outPath = some []) :
    fsOs fs (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace wfRun)) = tailFs fs := by
  rw [fsOs_wfRun, h]
  simp only [Option.isSome_some, ite_true]
  rw [h, bytesOf_bytesV, Option.getD_some, writeAt_hi]
  rfl

/-- **End to end, redirected**: the runtime is `IoSafeN` with the sound `fsEnv` for "nothing,
or `exit 0` with the OS image of `writeFile`'s WASI run against `fsImpl`". -/
theorem redirect_e2e {fd : Word} (R : RedirectRt c segs fd) {e : Silmaril.Process.LPS.Model}
    (hfd : fdLookup e.fds fd = some (.fileW outPath 0)) (hfs : Fs.lookup e.fs outPath = some []) :
    ∀ n, IoSafeN c (fsEnv segs) (fun _ _ _ => False) n R.start e
      (fun tr => tr = [] ∨
        tr = [.exitEv 0 (fsOs e.fs (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace wfRun)))]) := by
  rw [fsOs_wfRun_empty e.fs hfs]
  exact redirectRt_ioSafe R hfd hfs

/-- **End to end, with `openat`**: the runtime is `IoSafeN` with `fsEnvO` for "nothing, `exit 0`
with the OS image of `writeFile`'s WASI run against `fsImpl`, or `exit 1`". -/
theorem writeFile_e2e {e : Silmaril.Process.LPS.Model} (R : WriteFileRt c segs e)
    (hu : fsUnder e.fs outPath = false) (hn : Fs.lookup e.fs outPath = none) :
    ∀ n, IoSafeN c (fsEnvO segs) (fun _ _ _ => False) n R.start e
      (fun tr => tr = [] ∨
        tr = [.exitEv 0 (fsOs e.fs (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace wfRun)))] ∨
        tr = [.exitEv 1 e.fs]) := by
  rw [fsOs_wfRun_absent e.fs hn]
  exact writeFileRt_ioSafe R hu

end Silmaril.Wasi.Os
