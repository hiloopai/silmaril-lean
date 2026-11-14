module

public import Silmaril.Wasi.Runtime.Fs.Defs
public import Silmaril.Wasi.Runtime.Thms
public import Silmaril.Wasi.Os.Fs.Thms
public import Silmaril.Machine.X86.Open.Thms

/-!
# Proofs: the concrete x86 runtime of `writeFile` meets `RedirectRt`

The program `fsCode` with memory `fsMem` (`Silmaril.Wasi.Runtime.Fs`) on the open machine
`Open.step`, by the technique of `Silmaril.Proofs.Wasi.Runtime.Image`: every step is one
`Open.step_of_listed` with a `decide`d decoding, and `simp` on `Ext.exec`. Every state is an
`fsSt`, so the trap states are reached exactly.

* `fsMem_loaded`, `fsView_data0`, `fsView_data1`: the code is fetchable, `hi` readable.
* `fs_step`, `mov_exec`: one step at an offset; a `mov $imm32` on an `fsSt` core.
* `fs_trap`: an `fsSt` at offset `20`, `32` or `44` is at a `syscall`.
* `fs_resume`: LPS resumes an `fsSt` at a `syscall` (for every flag choice: the flags are
  defined) at the next offset, with `rax` the answer, `rcx` the return address and
  `r11 = flagsImg`, for an effect without memory writes.
* `fs_toWrite`, `fs_written`, `fs_closed`: the three syscall-free runs.
* **`redirectImg`**: the program is a `RedirectRt Open.step segs 3` for every segment list.
  **`redirectRt_exists`**: `Task.redirectRt_exists` holds.
* **`redirectImg_ioSafe`**, **`redirectImg_psafe`**, **`redirectImg_psafe8`**,
  **`redirectImg_e2e`**: the concrete instances of `redirectRt_ioSafe`, `redirectRt_psafe` (on
  every native machine agreeing with `Open.step`, and on the bridge's release machine for every
  flag oracle) and `redirect_e2e`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Runtime.Fs

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (State MState Reg)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Wasi.Os
open Silmaril.Wasi.Runtime (codeBase dataBase open_decode safe_step safe_now)
open Silmaril.Wasi.Examples (hiBytes)

/-! ## Memory -/

/-- The code is fetchable at `codeBase`. -/
theorem fsMem_loaded : Loaded fsMem codeBase fsCode := by
  unfold Loaded Memory.fetchBytes
  refine Memory.readWith_eq _ _ _ _ (by decide) ?_
  intro i hi
  exact Memory.install_get _ _ _ _ hi

theorem fsMem_data (i : Nat) (hi : i < 2) :
    fsMem.bytes[0x402000 + i]? = some (hiBytes[i]'(by simp [hiBytes]; omega)) := by
  have h1 := Memory.install_outside (Memory.install ∅ 0x402000 hiBytes) 0x401000 fsCode
    (0x402000 + i) (.inr (by simp [fsCode]; omega))
  have h2 := Memory.install_get ∅ 0x402000 hiBytes i (by simp [hiBytes]; omega)
  simp only [Std.ExtHashMap.get?_eq_getElem?] at h1 h2
  exact h1.trans h2

theorem fsView_data0 : viewByte fsMem .read dataBase = some 0x68 := by
  have h := fsMem_data 0 (by omega)
  simp only [viewByte, show fsMem.permits .read dataBase.toNat = true by decide, ↓reduceIte]
  exact h

theorem fsView_data1 : viewByte fsMem .read (dataBase + 1#64) = some 0x69 := by
  have h := fsMem_data 1 (by omega)
  simp only [viewByte, show fsMem.permits .read (dataBase + 1#64).toNat = true by decide,
    ↓reduceIte]
  exact h

/-- The readable source of `write(·, dataBase, 2)` in `fsMem` is `hi`. -/
theorem fs_writeSource : writeSource (viewByte fsMem .read) dataBase 2#64 = hiBytes := by
  have e2 : (zw (rwCountClamp 2#64)).toNat = 2 := by decide
  simp only [writeSource, readableBytes]
  rw [e2]
  simp [readableBytesAux, fsView_data0, fsView_data1, hiBytes]

/-! ## Steps -/

/-- **One step of the program** from an `fsSt` at offset `o`. -/
theorem fs_step {o l : Nat} {a c d s di r11 : Word} {i : Silmaril.X86.Ext.Instr} {core : State}
    (hfit : o + l ≤ fsCode.length)
    (hdec : Silmaril.X86.Ext.decode ((fsCode.drop o).take l) = some (i, l))
    (hx : Silmaril.X86.Ext.exec i (fsSt o a c d s di r11).core fsMem l = .ok core fsMem) :
    Silmaril.Machine.X86.Open.step (fsSt o a c d s di r11) = some ⟨core, fsMem⟩ :=
  Silmaril.Machine.X86.Open.step_of_listed fsMem_loaded rfl hfit (open_decode hdec)
    (by simp [Silmaril.X86.Ext8.exec]; exact hx)

/-- A `mov $imm32` to `rax`. -/
theorem movRax_exec (imm : BitVec 32) (a c d s di r11 rip : Word) :
    Silmaril.X86.Ext.exec (.movI32 .rax imm) ⟨fsRegs a c d s di r11, rip, clearFlags, 0⟩ fsMem 5 =
      .ok ⟨fsRegs (imm.setWidth 64) c d s di r11, rip + 5#64, clearFlags, 0⟩ fsMem := by
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.retire,
    State.write, Silmaril.X86.Ext.Result.ok.injEq, and_true]
  congr 1
  funext r
  cases r <;> rfl

/-- A `mov $imm32` to `rdx`. -/
theorem movRdx_exec (imm : BitVec 32) (a c d s di r11 rip : Word) :
    Silmaril.X86.Ext.exec (.movI32 .rdx imm) ⟨fsRegs a c d s di r11, rip, clearFlags, 0⟩ fsMem 5 =
      .ok ⟨fsRegs a c (imm.setWidth 64) s di r11, rip + 5#64, clearFlags, 0⟩ fsMem := by
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.retire,
    State.write, Silmaril.X86.Ext.Result.ok.injEq, and_true]
  congr 1
  funext r
  cases r <;> rfl

/-- A `mov $imm32` to `rsi`. -/
theorem movRsi_exec (imm : BitVec 32) (a c d s di r11 rip : Word) :
    Silmaril.X86.Ext.exec (.movI32 .rsi imm) ⟨fsRegs a c d s di r11, rip, clearFlags, 0⟩ fsMem 5 =
      .ok ⟨fsRegs a c d (imm.setWidth 64) di r11, rip + 5#64, clearFlags, 0⟩ fsMem := by
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.retire,
    State.write, Silmaril.X86.Ext.Result.ok.injEq, and_true]
  congr 1
  funext r
  cases r <;> rfl

/-- A `mov $imm32` to `rdi`. -/
theorem movRdi_exec (imm : BitVec 32) (a c d s di r11 rip : Word) :
    Silmaril.X86.Ext.exec (.movI32 .rdi imm) ⟨fsRegs a c d s di r11, rip, clearFlags, 0⟩ fsMem 5 =
      .ok ⟨fsRegs a c d s (imm.setWidth 64) r11, rip + 5#64, clearFlags, 0⟩ fsMem := by
  simp only [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.retire,
    State.write, Silmaril.X86.Ext.Result.ok.injEq, and_true]
  congr 1
  funext r
  cases r <;> rfl

variable {a c d s di r11 : Word}

/-- `mov $imm,%eax` at offset `o`. -/
theorem movRax_step {o o' : Nat} (imm : BitVec 32) (v : Word)
    (hfit : o + 5 ≤ fsCode.length)
    (hdec : Silmaril.X86.Ext.decode ((fsCode.drop o).take 5) = some (.movI32 .rax imm, 5))
    (hv : imm.setWidth 64 = v)
    (hr : codeBase + BitVec.ofNat 64 o + 5#64 = codeBase + BitVec.ofNat 64 o') :
    Silmaril.Machine.X86.Open.step (fsSt o a c d s di r11) = some (fsSt o' v c d s di r11) := by
  rw [fs_step hfit hdec (movRax_exec imm a c d s di r11 _), hv, hr]
  rfl

/-- `mov $imm,%edx` at offset `o`. -/
theorem movRdx_step {o o' : Nat} (imm : BitVec 32) (v : Word)
    (hfit : o + 5 ≤ fsCode.length)
    (hdec : Silmaril.X86.Ext.decode ((fsCode.drop o).take 5) = some (.movI32 .rdx imm, 5))
    (hv : imm.setWidth 64 = v)
    (hr : codeBase + BitVec.ofNat 64 o + 5#64 = codeBase + BitVec.ofNat 64 o') :
    Silmaril.Machine.X86.Open.step (fsSt o a c d s di r11) = some (fsSt o' a c v s di r11) := by
  rw [fs_step hfit hdec (movRdx_exec imm a c d s di r11 _), hv, hr]
  rfl

/-- `mov $imm,%esi` at offset `o`. -/
theorem movRsi_step {o o' : Nat} (imm : BitVec 32) (v : Word)
    (hfit : o + 5 ≤ fsCode.length)
    (hdec : Silmaril.X86.Ext.decode ((fsCode.drop o).take 5) = some (.movI32 .rsi imm, 5))
    (hv : imm.setWidth 64 = v)
    (hr : codeBase + BitVec.ofNat 64 o + 5#64 = codeBase + BitVec.ofNat 64 o') :
    Silmaril.Machine.X86.Open.step (fsSt o a c d s di r11) = some (fsSt o' a c d v di r11) := by
  rw [fs_step hfit hdec (movRsi_exec imm a c d s di r11 _), hv, hr]
  rfl

/-- `mov $imm,%edi` at offset `o`. -/
theorem movRdi_step {o o' : Nat} (imm : BitVec 32) (v : Word)
    (hfit : o + 5 ≤ fsCode.length)
    (hdec : Silmaril.X86.Ext.decode ((fsCode.drop o).take 5) = some (.movI32 .rdi imm, 5))
    (hv : imm.setWidth 64 = v)
    (hr : codeBase + BitVec.ofNat 64 o + 5#64 = codeBase + BitVec.ofNat 64 o') :
    Silmaril.Machine.X86.Open.step (fsSt o a c d s di r11) = some (fsSt o' a c d s v r11) := by
  rw [fs_step hfit hdec (movRdi_exec imm a c d s di r11 _), hv, hr]
  rfl

/-! ## The `syscall`s -/

/-- An `fsSt` at offset `o` where `fsCode` holds `syscall` is at a `syscall`. -/
theorem fs_trap {o : Nat} (hfit : o + 2 ≤ fsCode.length)
    (hb : (fsCode.drop o).take 2 = [0x0f, 0x05]) : AtSyscall (fsSt o a c d s di r11) := by
  have hf := fsMem_loaded.fetchBytes_sub (offset := o) (len := 2) (by omega) hfit
  unfold AtSyscall
  rw [hb] at hf
  have hn : (codeBase + BitVec.ofNat 64 o).toNat = codeBase.toNat + o := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : codeBase.toNat = 0x401000 := rfl
    simp only [fsCode, List.length_cons, List.length_nil] at hfit
    omega
  exact (congrArg (fsMem.fetchBytes · 2) hn).trans hf

theorem clearFlags_defined : X86FlagChoices.Defined clearFlags := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **LPS resumes an `fsSt` at a `syscall`** at the next offset, with `rax` the answer, `rcx` the
return address (the new `rip`) and `r11 = flagsImg`, for every flag choice and every effect
without memory writes. -/
theorem fs_resume {o o' : Nat} (k : X86FlagChoices.Choice) (eff : SyscallEffect)
    (ha : a ≠ 158#64) (hw : eff.writes = []) (hz : eff.zeros = []) (hu : eff.unmaps = [])
    (hc : eff.copies = [])
    (hr : codeBase + BitVec.ofNat 64 o + 2#64 = codeBase + BitVec.ofNat 64 o') :
    resume (trapAt (fsSt o a c d s di r11) k) eff =
      fsSt o' eff.ret (codeBase + BitVec.ofNat 64 o') d s di flagsImg := by
  have hfl := X86FlagChoices.completeFlags_eq_self clearFlags k clearFlags_defined
  have hm : applyMemoryEffect fsMem eff = fsMem := by
    simp [applyMemoryEffect, hw, hz, hu, hc]
  simp only [resume, x86AdvancePastSvc, x86ApplyEffectNative, trapAt, trapped,
    X86FlagChoices.completeState, fsSt, hfl, hm, State.read, fsRegs, Option.some.injEq,
    State.write]
  have hr' : codeBase + BitVec.ofNat 64 o + 2 = codeBase + BitVec.ofNat 64 o' := hr
  simp only [show ¬ (a = 158 ∧ di = 4098 ∧ eff.ret = 0) from fun h => ha h.1, ↓reduceIte, hr']
  congr 2
  funext r
  cases r <;> rfl

/-! ## Runs between the `syscall`s -/

/-- From the launch state to the `write`. -/
theorem fs_toWrite : ∀ n, SafeN Silmaril.Machine.X86.Open.step (fun m => m = fsWriteSt) n fsStart := by
  have h1 := movRsi_step (o := 0) (o' := 5) (a := 0) (c := 0) (d := 0) (s := 0) (di := 0) (r11 := 0)
    0x402000#32 dataBase (by decide) (by decide) (by decide) (by decide)
  have h2 := movRdx_step (o := 5) (o' := 10) (a := 0) (c := 0) (d := 0) (s := dataBase) (di := 0)
    (r11 := 0) 2#32 2#64 (by decide) (by decide) (by decide) (by decide)
  have h3 := movRax_step (o := 10) (o' := 15) (a := 0) (c := 0) (d := 2#64) (s := dataBase)
    (di := 0) (r11 := 0) 1#32 1#64 (by decide) (by decide) (by decide) (by decide)
  have h4 := movRdi_step (o := 15) (o' := 20) (a := 1#64) (c := 0) (d := 2#64) (s := dataBase)
    (di := 0) (r11 := 0) 3#32 outFd (by decide) (by decide) (by decide) (by decide)
  exact safe_step h1 (safe_step h2 (safe_step h3 (safe_step h4 (safe_now rfl))))

/-- After the `write`, to the `close`. -/
theorem fs_written {segs : List Segment} (k : X86FlagChoices.Choice) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step (fun m => m = fsCloseSt) n
      (resume (trapAt fsWriteSt k) (fileWEff segs (trapAt fsWriteSt k) hiBytes)) := by
  have h0 : resume (trapAt fsWriteSt k) (fileWEff segs (trapAt fsWriteSt k) hiBytes) =
      fsSt 22 (lenWord hiBytes) rcWrite 2#64 dataBase outFd flagsImg :=
    fs_resume (o := 20) (o' := 22) (a := 1#64) (c := 0) (d := 2#64) (s := dataBase) (di := outFd)
      (r11 := 0) k (fileWEff segs (trapAt fsWriteSt k) hiBytes) (by decide) rfl rfl rfl rfl
      (by decide)
  have h1 := movRax_step (o := 22) (o' := 27) (a := lenWord hiBytes) (c := rcWrite) (d := 2#64)
    (s := dataBase) (di := outFd) (r11 := flagsImg) 3#32 3#64 (by decide) (by decide) (by decide)
    (by decide)
  have h2 := movRdi_step (o := 27) (o' := 32) (a := 3#64) (c := rcWrite) (d := 2#64)
    (s := dataBase) (di := outFd) (r11 := flagsImg) 3#32 outFd (by decide) (by decide) (by decide)
    (by decide)
  rw [h0]
  exact safe_step h1 (safe_step h2 (safe_now rfl))

/-- After the `close`, to the `exit`. -/
theorem fs_closed (k : X86FlagChoices.Choice) :
    ∀ n, SafeN Silmaril.Machine.X86.Open.step (fun m => m = fsExitSt) n
      (resume (trapAt fsCloseSt k) (mkEffect 0 [] [])) := by
  have h0 : resume (trapAt fsCloseSt k) (mkEffect 0 [] []) =
      fsSt 34 0 rcClose 2#64 dataBase outFd flagsImg :=
    fs_resume (o := 32) (o' := 34) (a := 3#64) (c := rcWrite) (d := 2#64) (s := dataBase)
      (di := outFd) (r11 := flagsImg) k (mkEffect 0 [] []) (by decide) rfl rfl rfl rfl (by decide)
  have h1 := movRax_step (o := 34) (o' := 39) (a := 0) (c := rcClose) (d := 2#64)
    (s := dataBase) (di := outFd) (r11 := flagsImg) 60#32 60#64 (by decide) (by decide) (by decide)
    (by decide)
  have h2 := movRdi_step (o := 39) (o' := 44) (a := 60#64) (c := rcClose) (d := 2#64)
    (s := dataBase) (di := outFd) (r11 := flagsImg) 0#32 0#64 (by decide) (by decide) (by decide)
    (by decide)
  rw [h0]
  exact safe_step h1 (safe_step h2 (safe_now rfl))

/-! ## The runtime -/

/-- **The program is a runtime of `writeFile` launched with `out.txt` open on descriptor `3`**,
on the open machine, for every segment list. -/
def redirectImg (segs : List Segment) : RedirectRt Silmaril.Machine.X86.Open.step segs outFd where
  writeSt := fsWriteSt
  writeTrap := fs_trap (o := 20) (by decide) (by decide)
  writeNo _ := rfl
  writeFd _ := by
    show fd32 outFd = outFd
    decide
  writeRange _ := by
    show modeledRwRangeWith accessOkb dataBase 2#64 = true
    decide
  writeCount _ := by
    show wIs0 2#64 = false
    decide
  writeBytes _ := fs_writeSource
  closeSt := fsCloseSt
  written k := fs_written k
  closeTrap := fs_trap (o := 32) (by decide) (by decide)
  closeNo _ := rfl
  closeFd _ := by
    show fd32 outFd = outFd
    decide
  exitSt := fsExitSt
  closed k := fs_closed k
  exitTrap := fs_trap (o := 44) (by decide) (by decide)
  exitNo := rfl
  exitCode := by decide
  start := fsStart
  toWrite := fs_toWrite

/-- **`Task.redirectRt_exists` holds.** -/
theorem redirectRt_exists : Task.redirectRt_exists :=
  ⟨Silmaril.Machine.X86.Open.step, [], outFd, fun h => h, ⟨redirectImg []⟩⟩

/-- **The concrete runtime is `IoSafeN`** with the sound `fsEnv`, from every model whose
descriptor `3` is a write-only `out.txt` at offset `0` and where `out.txt` is empty. -/
theorem redirectImg_ioSafe {segs : List Segment} {e : Silmaril.Process.LPS.Model}
    (hfd : fdLookup e.fds outFd = some (.fileW outPath 0))
    (hfs : Fs.lookup e.fs outPath = some []) :
    ∀ n, IoSafeN Silmaril.Machine.X86.Open.step (fsEnv segs) (fun _ _ _ => False) n fsStart e
      (redirAllowed e.fs) :=
  redirectRt_ioSafe (redirectImg segs) hfd hfs

/-- **The concrete runtime is process-safe for LPS**, on every native machine agreeing with
`Open.step`: nothing, or `exit 0` with `hi` written to `out.txt`. -/
theorem redirectImg_psafe {oracle : Oracle} {nstep : NStep} {refused : RefusalFilter}
    {segs : List Segment} (hM : Agrees nstep Silmaril.Machine.X86.Open.step)
    {cfg : Config (flagMachine oracle nstep)} (al : AlignedF cfg fsStart)
    (hfd : fdLookup cfg.model.fds outFd = some (.fileW outPath 0))
    (hfs : Fs.lookup cfg.model.fs outPath = some []) :
    PSafeF segs refused (redirAllowed cfg.model.fs) cfg :=
  redirectRt_psafe hM (redirectImg segs) al hfd hfs

/-- **End to end**: the concrete runtime is `IoSafeN` for "nothing, or `exit 0` with the OS image
of `writeFile`'s WASI run against `fsImpl`". -/
theorem redirectImg_e2e {segs : List Segment} {e : Silmaril.Process.LPS.Model}
    (hfd : fdLookup e.fds outFd = some (.fileW outPath 0))
    (hfs : Fs.lookup e.fs outPath = some []) :
    ∀ n, IoSafeN Silmaril.Machine.X86.Open.step (fsEnv segs) (fun _ _ _ => False) n fsStart e
      (fun tr => tr = [] ∨
        tr = [.exitEv 0 (fsOs e.fs (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace wfRun)))]) :=
  redirect_e2e (redirectImg segs) hfd hfs

/-- **The concrete runtime on the bridge's release machine** (`x86WithFlagOracle8`, every flag
oracle), with the exit event's file system read as the OS image of `writeFile`'s WASI run
against `fsImpl`. -/
theorem redirectImg_psafe8 {oracle : Oracle} {refused : RefusalFilter} {segs : List Segment}
    {cfg : Config (machine oracle)} (al : Aligned cfg fsStart)
    (hfd : fdLookup cfg.model.fds outFd = some (.fileW outPath 0))
    (hfs : Fs.lookup cfg.model.fs outPath = some []) :
    PSafe segs refused (fun tr => tr = [] ∨
      tr = [.exitEv 0 (fsOs cfg.model.fs (Silmaril.Wasi.hostView (Silmaril.Wasi.wtrace wfRun)))])
      cfg := by
  rw [fsOs_wfRun_empty cfg.model.fs hfs]
  exact (Silmaril.Proofs.Machine.Process.LpsBridge.psafeF_iff).1
    (redirectImg_psafe Silmaril.Proofs.Machine.Process.LpsBridge.agrees_open8
      (Silmaril.Proofs.Machine.Process.LpsBridge.alignedF_iff.2 al) hfd hfs)

end Silmaril.Wasi.Runtime.Fs
