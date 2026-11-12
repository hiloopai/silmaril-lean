module

public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# Kernel-reducible runs of the verified interpreter: equations

* `dropX_eq`, `takeX_eq`, `lenGe_eq`, `overL_eq`, `writeL_eq`: the list functions;
* `fload_eq : fload = Memory.load`, `fstore_eq : fstore = Memory.store`;
* `headF_eq : headF o = interpHead o`, hence **`runIF_eq : runIF o = runI o`** and
  **`runInvokeF_eq : runInvokeF o = runInvoke? o`**;
* `splitK_eq`, `stepK_eq : stepK head d = step? head`, `runK_eq`, hence **`runIK_eq`** and
  **`runInvokeK_eq : runInvokeK o = runInvoke? o`**.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify.Kernel

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec

variable {α : Type} {H : Type}

/-! ## Lists -/

theorem dropX_eq (l : List α) (n : Nat) :
    dropX l n = if n ≤ l.length then some (l.drop n) else none := by
  induction l generalizing n with
  | nil => cases n <;> simp [dropX]
  | cons a l ih =>
    cases n with
    | zero => simp [dropX]
    | succ n =>
      have h : dropX (a :: l) (n + 1) = dropX l n := rfl
      simp [h, ih]

theorem takeX_eq (l : List α) (n : Nat) :
    takeX l n = if n ≤ l.length then some (l.take n) else none := by
  induction l generalizing n with
  | nil => cases n <;> simp [takeX]
  | cons a l ih =>
    cases n with
    | zero => simp [takeX]
    | succ n =>
      have h : takeX (a :: l) (n + 1) = (takeX l n).map (a :: ·) := rfl
      rw [h, ih]
      by_cases hn : n ≤ l.length <;> simp [hn]

theorem lenGe_eq (l : List α) (n : Nat) : lenGe l n = decide (n ≤ l.length) := by
  induction l generalizing n with
  | nil => cases n <;> simp [lenGe]
  | cons a l ih =>
    cases n with
    | zero => simp [lenGe]
    | succ n =>
      have h : lenGe (a :: l) (n + 1) = lenGe l n := rfl
      simp [h, ih]

theorem overL_eq (l bs : List α) (h : bs.length ≤ l.length) :
    overL l bs = bs ++ l.drop bs.length := by
  induction l generalizing bs with
  | nil => cases bs <;> simp_all [overL]
  | cons a l ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      have e : overL (a :: l) (b :: bs) = b :: overL l bs := rfl
      simp only [List.length_cons, Nat.add_le_add_iff_right] at h
      simp [e, ih bs h]

theorem writeL_eq (l : List α) (n : Nat) (bs : List α) (h : n + bs.length ≤ l.length) :
    writeL l n bs = l.take n ++ bs ++ l.drop (n + bs.length) := by
  induction l generalizing n with
  | nil =>
    simp only [List.length_nil, Nat.le_zero, Nat.add_eq_zero_iff, List.length_eq_zero_iff] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons a l ih =>
    cases n with
    | zero =>
      have e : writeL (a :: l) 0 bs = overL (a :: l) bs := rfl
      rw [e, overL_eq _ _ (by simpa using h)]
      simp
    | succ n =>
      have e : writeL (a :: l) (n + 1) bs = a :: writeL l n bs := rfl
      simp only [List.length_cons] at h
      rw [e, ih n (by omega)]
      simp [Nat.add_right_comm n 1]

/-! ## Memory accesses -/

theorem toList_extract (m : Memory.Bytes) (a b : Nat) :
    (m.extract a b).data.toList = (m.data.toList.drop a).take (b - a) := by
  simp [ByteArray.data_extract, Array.toList_extract]

theorem length_toList (m : Memory.Bytes) : m.data.toList.length = m.size := rfl

theorem fload_eq : @fload = @Memory.load := by
  funext m st count
  simp only [fload, Memory.load, Memory.readBytes, dropX_eq, takeX_eq, length_toList]
  by_cases h : st + count ≤ m.size
  · have h₁ : st ≤ m.size := by omega
    have h₂ : count ≤ (m.data.toList.drop st).length := by
      rw [List.length_drop, length_toList]; omega
    simp only [h₁, h₂, h, ite_true, Option.bind_some, Option.map_some]
    congr 3
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [toList_extract]
    simp
  · simp only [h, ite_false, Option.map_none]
    by_cases h₁ : st ≤ m.size
    · have h₂ : ¬ count ≤ (m.data.toList.drop st).length := by
        rw [List.length_drop, length_toList]; omega
      simp only [h₁, h₂, ite_true, ite_false, Option.bind_some, Option.map_none]
    · simp only [h₁, ite_false, Option.bind_none, Option.map_none]

theorem writeL_copySlice (m b : Memory.Bytes) (st : Nat) (h : st + b.size ≤ m.size) :
    (⟨⟨writeL m.data.toList st b.data.toList⟩⟩ : Memory.Bytes) = b.copySlice 0 m st b.size := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have hb : b.data.toList.length = b.size := length_toList b
  have hbs : b.data.size = b.size := rfl
  have hm : m.data.size = m.size := rfl
  have e₁ : (m.data.toList.drop (st + b.size)).take (m.size - (st + b.size)) =
      m.data.toList.drop (st + b.size) :=
    List.take_of_length_le (by rw [List.length_drop, length_toList])
  rw [writeL_eq _ _ _ (by rw [hb, length_toList]; omega), ByteArray.copySlice_eq_append]
  simp only [ByteArray.data_append, Array.toList_append, toList_extract, hb, hbs, hm,
    Nat.zero_add, Nat.min_self, Nat.sub_zero, List.drop_zero,
    List.take_of_length_le (Nat.le_of_eq hb), e₁, List.append_assoc]

theorem fstore_eq : @fstore = @Memory.store := by
  funext m st count w
  have hb : (Memory.encodeLE count w.toNat).size = count := Memory.encodeLE_size _ _
  by_cases h : st + count ≤ m.size
  · have hl : lenGe m.data.toList (st + count) = true := by
      rw [lenGe_eq, length_toList]
      exact decide_eq_true h
    have hs : st + (Memory.encodeLE count w.toNat).size ≤ m.size := by rw [hb]; exact h
    calc fstore m st w
        = some ⟨⟨writeL m.data.toList st (Memory.encodeLE count w.toNat).data.toList⟩⟩ :=
          ite_eq_left hl
      _ = some ((Memory.encodeLE count w.toNat).copySlice 0 m st
            (Memory.encodeLE count w.toNat).size) := by rw [writeL_copySlice m _ st hs]
      _ = Memory.store m st w := (ite_eq_left hs).symm
  · have hl : ¬ lenGe m.data.toList (st + count) = true := by
      rw [lenGe_eq, length_toList]
      exact fun h' => h (of_decide_eq_true h')
    have hs : ¬ st + (Memory.encodeLE count w.toNat).size ≤ m.size := by rw [hb]; exact h
    calc fstore m st w = none := ite_eq_right hl
      _ = Memory.store m st w := (ite_eq_right hs).symm

/-! ## The head step and the run -/

theorem loadIntF_eq : @loadIntF H = @Mem.loadInt H := by
  funext s f t x arg args
  unfold loadIntF Mem.loadInt
  rw [fload_eq]
  rfl

theorem storeIntF_eq : @storeIntF H = @Mem.storeInt H := by
  funext s f t x arg args
  unfold storeIntF Mem.storeInt
  rw [fstore_eq]
  rfl

theorem stepArgsF_eq : @stepArgsF H = @Mem.stepArgs H := by
  funext o s f args e
  unfold stepArgsF
  split <;> simp only [Mem.stepArgs, loadIntF_eq, storeIntF_eq]

theorem memoryStepF_eq : @memoryStepF H = @memoryStep? H := by
  funext o s f vs e
  simp only [memoryStepF, memoryStep?, stepArgsF_eq]
  rfl

theorem headF_eq (o : GrowOracle) : headF (H := H) o = interpHead o := by
  funext s f vs e
  unfold headF
  split
  · rename_i h
    simp only [interpHead, h, memoryStepF_eq]
  · rfl

/-- **The kernel-reducible run is the verified interpreter's run.** -/
theorem runIF_eq (o : GrowOracle) : runIF (H := H) o = runI o := by
  simp only [runIF, runI, headF_eq]

/-- **The kernel-reducible `$invoke` run is `runInvoke?`.** -/
theorem runInvokeF_eq (o : GrowOracle) : runInvokeF (H := H) o = runInvoke? o := by
  funext n s a vs
  simp only [runInvokeF, runInvoke?, runIF_eq]

/-! ## The kernel-friendly driver -/

theorem splitK_eq : splitK = splitVals := by
  funext l
  induction l with
  | nil => rfl
  | cons a as ih =>
    show (match a.val? with
      | some v => (v :: (splitK as).1, (splitK as).2)
      | none => ([], a :: as)) = splitVals (a :: as)
    rw [ih, splitVals]
    cases a.val? <;> rfl

theorem stepK_eq (head : HeadFn H) (d : Nat) : stepK head d = step? head := by
  induction d with
  | zero => funext c; rfl
  | succ d ih =>
    funext c
    show (match splitK c.code with
      | (_, []) => none
      | (vs, e :: rest) => Drv.layer head c.store c.frame vs e rest fun c' _ => stepK head d c') =
      step? head c
    rw [splitK_eq, ih]
    match hs : splitVals c.code with
    | (vs, []) => exact (step?_nil hs).symm
    | (vs, e :: rest) => exact (step?_cons hs).symm

theorem runK_eq (head : HeadFn H) : runK head = run? head := by
  funext n
  induction n with
  | zero => funext c; rfl
  | succ n ih =>
    funext c
    simp only [runK, run?, stepK_eq, ih]
    cases step? head c <;> rfl

/-- **The kernel-friendly run is the verified interpreter's run.** -/
theorem runIK_eq (o : GrowOracle) : runIK (H := H) o = runI o := by
  simp only [runIK, runK_eq, runI, headF_eq]

/-- **The kernel-friendly `$invoke` run is `runInvoke?`.** -/
theorem runInvokeK_eq (o : GrowOracle) : runInvokeK (H := H) o = runInvoke? o := by
  funext n s a vs
  simp only [runInvokeK, runInvoke?, runIK_eq]

end Silmaril.Wasm.Verify.Kernel
