module

public import Silmaril.Formats.Compression.Inflate.Stream.Protocol
public import Silmaril.Formats.Compression.Inflate.Common

/-! Unrefined proofs about the definitions in `Silmaril.Formats.Compression.Inflate.Stream.Protocol`. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.Protocol

theorem sub32_eq_sub (initial remaining : Nat)
    (hremaining : remaining ≤ initial) (hinitial : initial < word32) :
    sub32 initial remaining = initial - remaining := by
  have hr : remaining < word32 := by omega
  have hd : initial - remaining < word32 := by omega
  unfold sub32
  rw [Nat.mod_eq_of_lt hinitial, Nat.mod_eq_of_lt hr]
  have h : initial + word32 - remaining = initial - remaining + word32 := by omega
  rw [h, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hd]

theorem sub32_conserves (initial remaining : Nat)
    (hremaining : remaining ≤ initial) (hinitial : initial < word32) :
    remaining + sub32 initial remaining = initial := by
  rw [sub32_eq_sub initial remaining hremaining hinitial]
  omega

@[simp] theorem sub32_self (count : Nat) : sub32 count count = 0 := by
  unfold sub32
  have h : count % word32 + word32 - count % word32 = word32 := by omega
  rw [h, Nat.mod_self]

theorem returnCode_versions_agree (ret flush : Int) (consumed produced : Nat) :
    returnCode131 ret flush consumed produced = returnCodeDevelop ret flush consumed produced := by
  by_cases hret : ret = ok <;>
    by_cases hp : consumed = 0 ∧ produced = 0 <;>
    by_cases hf : flush = finish <;>
    simp [returnCode131, returnCodeDevelop, hret, hp, hf]

theorem returnCode_nonok (ret flush : Int) (consumed produced : Nat) (hret : ret ≠ ok) :
    returnCode131 ret flush consumed produced = ret := by
  simp [returnCode131, hret]

theorem returnCode_ok_iff (ret flush : Int) (consumed produced : Nat) :
    returnCode131 ret flush consumed produced = ok ↔
      ret = ok ∧ flush ≠ finish ∧ (consumed ≠ 0 ∨ produced ≠ 0) := by
  by_cases hr : ret = ok
  · subst ret
    by_cases hf : flush = finish <;>
      by_cases hi : consumed = 0 <;> by_cases ho : produced = 0 <;>
      simp [returnCode131, hf, hi, ho, ok, bufError]
  · rw [returnCode_nonok ret flush consumed produced hr]
    simp [hr]

theorem finish_never_ok (ret : Int) (consumed produced : Nat) :
    returnCode131 ret finish consumed produced ≠ ok := by
  intro h
  exact (returnCode_ok_iff ret finish consumed produced).1 h |>.2.1 rfl

theorem no_progress_buffer_error (flush : Int) :
    returnCode131 ok flush 0 0 = bufError := by simp [returnCode131]

@[simp] theorem consumed_restore (f : ExitFields) : consumed (restore f) = consumed f := rfl
@[simp] theorem produced_restore (f : ExitFields) : produced (restore f) = produced f := rfl
@[simp] theorem windowWanted_restore (f : ExitFields) :
    windowWanted (restore f) = windowWanted f := rfl

theorem checkOutput_rebases (update : UpdateCheck) (f : ExitFields) (hwrap : f.wrap ≠ 0) :
    produced (checkOutput update f) = 0 := by
  simp only [checkOutput, ite_eq_right hwrap, produced, sub32_self]

theorem checkOutput_total (update : UpdateCheck) (f : ExitFields) (hwrap : f.wrap ≠ 0) :
    (checkOutput update f).publicFields.totalOut = add64 f.publicFields.totalOut (produced f) := by
  simp only [checkOutput, ite_eq_right hwrap]

theorem checkReady_bad (update : UpdateCheck) (f : ExitFields)
    (hwrap : f.wrap ≠ 0) (hvalidate : validateChecks f = true)
    (hmismatch : trailerCheck f ≠ (checkOutput update f).check) :
    (checkReady update f).mode = .bad := by
  simp [checkReady, hwrap, hvalidate, hmismatch]

theorem checkReady_good (update : UpdateCheck) (f : ExitFields)
    (hwrap : f.wrap ≠ 0) (hcheck : trailerCheck f = (checkOutput update f).check) :
    (checkReady update f).mode = (if f.gzipEnabled then .length else .done) ∧
    (checkReady update f).hold = 0 ∧ (checkReady update f).bits = 0 := by
  simp [checkReady, hwrap, hcheck]

theorem lengthReady_bad (f : ExitFields) (hgzip : f.gzipEnabled = true)
    (hwrap : f.wrap ≠ 0) (hflags : f.flags ≠ 0)
    (hvalidate : validateChecks f = true) (hmismatch : f.hold ≠ f.privateTotal % word32) :
    (lengthReady f).mode = .bad := by
  simp [lengthReady, hgzip, hwrap, hflags, hvalidate, hmismatch]

theorem lengthReady_good (f : ExitFields) (hgzip : f.gzipEnabled = true)
    (hwrap : f.wrap ≠ 0) (hflags : f.flags ≠ 0)
    (hsize : f.hold = f.privateTotal % word32) :
    (lengthReady f).mode = .done ∧
    (lengthReady f).hold = 0 ∧ (lengthReady f).bits = 0 := by
  simp [lengthReady, hgzip, hwrap, hflags, hsize]

theorem infLeave_versions_agree (update : UpdateCheck) (windowFailed : Bool)
    (ret : Int) (f : ExitFields) :
    infLeave131 update windowFailed ret f = infLeaveDevelop update windowFailed ret f := by
  have h : returnCode131 = returnCodeDevelop :=
    funext fun ret => funext fun flush => funext fun i => funext fun o =>
      returnCode_versions_agree ret flush i o
  rw [infLeave131, infLeaveDevelop, h]

theorem infLeave_commits (update : UpdateCheck) (windowFailed : Bool)
    (ret : Int) (f : ExitFields) (hwindow : (windowWanted f && windowFailed) = false) :
    (infLeave131 update windowFailed ret f).stage = .committed ∧
    (infLeave131 update windowFailed ret f).fields.publicFields.totalIn =
      add64 f.publicFields.totalIn (consumed f) ∧
    (infLeave131 update windowFailed ret f).fields.publicFields.totalOut =
      add64 f.publicFields.totalOut (produced f) ∧
    (infLeave131 update windowFailed ret f).fields.privateTotal =
      add64 f.privateTotal (produced f) ∧
    (infLeave131 update windowFailed ret f).fields.publicFields.dataType =
      dataType f.mode f.bits f.last := by
  simp only [infLeave131, infLeaveWith, windowWanted_restore, hwindow,
    Bool.false_eq_true, ↓reduceIte]
  exact ⟨trivial, rfl, rfl, rfl, rfl⟩

theorem window_failure_restores (update : UpdateCheck) (ret : Int) (f : ExitFields)
    (hwindow : windowWanted f = true) :
    infLeave131 update true ret f =
      ⟨memError, { restore f with mode := .mem }, .restored, true⟩ := by
  simp [infLeave131, infLeaveWith, hwindow]

/-- An allocation failure can override even a pending STREAM_END. It preserves
old totals/checksum/data_type while committing the local cursors and bits. -/
theorem window_failure_skips_totals (update : UpdateCheck) (ret : Int) (f : ExitFields)
    (hwindow : windowWanted f = true) :
    (infLeave131 update true ret f).status = memError ∧
    (infLeave131 update true ret f).fields.publicFields.totalIn = f.publicFields.totalIn ∧
    (infLeave131 update true ret f).fields.publicFields.totalOut = f.publicFields.totalOut ∧
    (infLeave131 update true ret f).fields.publicFields.adler = f.publicFields.adler ∧
    (infLeave131 update true ret f).fields.publicFields.dataType = f.publicFields.dataType := by
  rw [window_failure_restores update ret f hwindow]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem dictionary_preserves_totals (update : UpdateCheck) (windowFailed : Bool) (f : ExitFields) :
    (returnVia update windowFailed .dictionary f).status = needDict ∧
    (returnVia update windowFailed .dictionary f).fields.publicFields.totalIn =
      f.publicFields.totalIn ∧
    (returnVia update windowFailed .dictionary f).fields.publicFields.totalOut =
      f.publicFields.totalOut ∧
    (returnVia update windowFailed .dictionary f).fields.publicFields.dataType =
      f.publicFields.dataType := by exact ⟨rfl, rfl, rfl, rfl⟩

theorem dictionary_restores_cursors (update : UpdateCheck) (windowFailed : Bool) (f : ExitFields) :
    (returnVia update windowFailed .dictionary f).fields.publicFields.nextIn = f.nextIn ∧
    (returnVia update windowFailed .dictionary f).fields.publicFields.nextOut = f.nextOut ∧
    (returnVia update windowFailed .dictionary f).fields.publicFields.availIn = f.inputLeft ∧
    (returnVia update windowFailed .dictionary f).fields.publicFields.availOut = f.left ∧
    (returnVia update windowFailed .dictionary f).fields.storedHold = f.hold ∧
    (returnVia update windowFailed .dictionary f).fields.storedBits = f.bits := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem memory_route_immediate (update : UpdateCheck) (windowFailed : Bool) (f : ExitFields) :
    returnVia update windowFailed .immediateMemory f =
      ⟨memError, f, .immediate, false⟩ := rfl

theorem dictionary_route_missing : terminalRoute .dict false = some .dictionary := rfl
theorem dictionary_route_ready : terminalRoute .dict true = none := rfl
theorem done_route : terminalRoute .done false = some (.leave streamEnd) := rfl
theorem bad_route : terminalRoute .bad false = some (.leave dataError) := rfl

theorem leave_consumed_conserves (f : ExitFields)
    (hhave : f.inputLeft ≤ f.savedIn) (hwidth : f.savedIn < word32) :
    f.inputLeft + consumed f = f.savedIn := sub32_conserves _ _ hhave hwidth

theorem leave_produced_conserves (f : ExitFields)
    (hleft : f.left ≤ f.savedOut) (hwidth : f.savedOut < word32) :
    f.left + produced f = f.savedOut := sub32_conserves _ _ hleft hwidth

theorem dataType_bound (mode : Mode) (bits : Nat) (last : Bool) (hbits : bits ≤ 32) :
    dataType mode bits last ≤ 352 := by
  cases mode <;> cases last <;> simp [dataType] <;> omega

end Silmaril.Formats.Compression.Inflate.Stream.Protocol
