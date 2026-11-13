module

public import Silmaril.Wasm.Perf.CoreDecode.Defs

/-!
# The fast Core decoder is silmaril's decoder: proofs

The main equations are restated in `Silmaril.Wasm.Perf.CoreDecode.Thms`.

`decodeF_eq : decodeF = Silmaril.Wasm.Binary.Core.decode?`. The leaves are equal because
`a <<< s = a * 2 ^ s` and `n >>> N = 0 ↔ n < 2 ^ N`; every copied reader is then equal to its
original by rewriting the readers it calls (earlier lemmas) and unfolding.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Perf.CoreDecode

open Silmaril Silmaril.Wasm Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core
open Silmaril.Wasm.Perf.CoreDecode

theorem readByte_eq : readByte = Decode.readByte := by
  funext c
  unfold readByte Decode.readByte
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set, pure, Except.pure,
    Except.bind, throw, throwThe, MonadExceptOf.throw]
  split <;> rfl

theorem peekByte_eq : peekByte = Decode.peekByte := by
  funext c
  rfl

theorem remaining_eq : remaining = Decode.remaining := by
  funext c
  rfl

/-! The proofs below rewrite with `readByte_eq`, `peekByte_eq` and `remaining_eq` in every
`simp only` (where a reader does not use one of them, the argument is unused). -/
set_option linter.unusedSimpArgs false

private theorem shiftRight_eq_zero {n N : Nat} : n >>> N = 0 ↔ n < 2 ^ N := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos N)]

private theorem pow_mul128 (shift : Nat) : 2 ^ shift * 128 = 2 ^ (shift + 7) := by
  rw [Nat.pow_add]

theorem readU_go_eq : ∀ fuel shift, readU.go (2 ^ shift) fuel = Decode.readU.go shift fuel
  | 0, _ => rfl
  | fuel + 1, shift => by
    simp only [readByte_eq, peekByte_eq, remaining_eq, readU.go, Decode.readU.go, pow_mul128, readU_go_eq fuel (shift + 7)]

theorem readU_eq : readU = Decode.readU := by
  funext N
  have h := readU_go_eq ((N + 6) / 7) 0
  rw [Nat.pow_zero] at h
  simp only [readByte_eq, peekByte_eq, remaining_eq, readU, Decode.readU, h, shiftRight_eq_zero]

theorem fitsBits_iff {n N : Nat} : fitsBits n N = true ↔ n < 2 ^ N := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, fitsBits, beq_iff_eq, shiftRight_eq_zero]

theorem sRange_iff (N : Nat) (i : Int) :
    sRange N i = true ↔ -(2 ^ (N - 1) : Int) ≤ i ∧ i < 2 ^ (N - 1) := by
  have hp : (0 : Int) < 2 ^ (N - 1) := by exact_mod_cast Nat.two_pow_pos (N - 1)
  have hc : ((2 ^ (N - 1) : Nat) : Int) = 2 ^ (N - 1) := by push_cast; rfl
  cases i with
  | ofNat k =>
    show fitsBits k (N - 1) = true ↔ _
    rw [fitsBits_iff, ← hc, Int.ofNat_eq_natCast]
    omega
  | negSucc k =>
    show fitsBits k (N - 1) = true ↔ _
    rw [fitsBits_iff, ← hc, Int.negSucc_eq]
    omega

private theorem cast_add_mul (acc x s : Nat) :
    ((acc + x * 2 ^ s : Nat) : Int) = (acc : Int) + (x : Int) * 2 ^ s := by
  push_cast
  rfl

private theorem subNatNat_pow (a t : Nat) :
    Int.subNatNat a (2 ^ t) = (a : Int) - 2 ^ t := by
  rw [Int.subNatNat_eq_coe]
  push_cast
  rfl

theorem readS_go_eq : ∀ fuel shift acc,
    readS.go (2 ^ shift) fuel acc = Decode.readS.go shift fuel (acc : Int)
  | 0, _, _ => rfl
  | fuel + 1, shift, acc => by
    simp only [readByte_eq, peekByte_eq, remaining_eq, readS.go, Decode.readS.go, Int.ofNat_eq_natCast, pow_mul128, subNatNat_pow,
      cast_add_mul, readS_go_eq fuel (shift + 7)]

theorem readS_eq : readS = Decode.readS := by
  funext N
  have hr : ∀ i : Int, sRange N i = true ↔ -(2 ^ (N - 1) : Int) ≤ i ∧ i < 2 ^ (N - 1) :=
    sRange_iff N
  have h := readS_go_eq ((N + 6) / 7) 0 0
  rw [Nat.pow_zero] at h
  simp only [readByte_eq, peekByte_eq, remaining_eq, readS, Decode.readS, h, Int.natCast_zero, hr]

private theorem ofIntF_ofNat (n k : Nat) : ofIntF n (.ofNat k) = BitVec.ofInt n (.ofNat k) := by
  have hp : (0 : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos n
  by_cases h : fitsBits k n = true
  · have hk : k < 2 ^ n := fitsBits_iff.mp h
    have hm : (k : Int) % ((2 ^ n : Nat) : Int) = k := Int.emod_eq_of_lt (by omega) (by omega)
    simp only [readByte_eq, peekByte_eq, remaining_eq, ofIntF, h, dite_true]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNatLT, BitVec.toNat_ofInt, Int.ofNat_eq_natCast, hm, Int.toNat_natCast]
  · simp only [readByte_eq, peekByte_eq, remaining_eq, ofIntF, h, Bool.false_eq_true, dite_false]

private theorem ofIntF_negSucc (n k : Nat) :
    ofIntF n (.negSucc k) = BitVec.ofInt n (.negSucc k) := by
  have hp : (0 : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos n
  by_cases h : fitsBits k n = true
  · have hk : k < 2 ^ n := fitsBits_iff.mp h
    have h1 : maxN n = 2 ^ n - 1 := maxN_eq n
    have hm : (k : Int) % ((2 ^ n : Nat) : Int) = k := Int.emod_eq_of_lt (by omega) (by omega)
    simp only [readByte_eq, peekByte_eq, remaining_eq, ofIntF, h, dite_true]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNatLT, BitVec.toNat_ofInt, h1, Int.negSucc_emod _ hp, hm]
    omega
  · simp only [readByte_eq, peekByte_eq, remaining_eq, ofIntF, h, Bool.false_eq_true, dite_false]

theorem ofIntF_eq : ofIntF = BitVec.ofInt := by
  funext n v
  cases v with
  | ofNat k => exact ofIntF_ofNat n k
  | negSucc k => exact ofIntF_negSucc n k

/-- The bound `2 ^ 32 - 1` the copies compare with. -/
private theorem le_u32 (n : Nat) : n ≤ 4294967295 ↔ n < 2 ^ 32 := by
  have : (2 : Nat) ^ 32 = 4294967296 := rfl
  omega

theorem readIdx_eq : @readIdx = @Decode.readIdx := by
  funext k
  simp only [readByte_eq, peekByte_eq, remaining_eq, readIdx, Decode.readIdx, readU_eq, le_u32]

theorem readCount_eq : readCount = Decode.readCount := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readCount, Decode.readCount, readU_eq]

theorem readVec_go_eq {α : Type} (f : Decode.DecodeM α) :
    ∀ n, readVec.go f n = Decode.readVec.go f n
  | 0 => rfl
  | n + 1 => by simp only [readByte_eq, peekByte_eq, remaining_eq, readVec.go, Decode.readVec.go, readVec_go_eq f n]

theorem readVec_eq : @readVec = @Decode.readVec := by
  funext α f
  simp only [readByte_eq, peekByte_eq, remaining_eq, readVec, Decode.readVec, readVec_go_eq, readCount_eq]

theorem readName_eq : readName = Decode.readName := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readName, Decode.readName, readCount_eq]
  rfl

theorem readRefType_absHeapType_eq : readRefType.absHeapType = Decode.readRefType.absHeapType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readRefType.absHeapType, Decode.readRefType.absHeapType]
  rfl

theorem readRefType_heapType_eq : readRefType.heapType = Decode.readRefType.heapType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readRefType.heapType, Decode.readRefType.heapType, readRefType_absHeapType_eq, readS_eq,
    le_u32]
  rfl

theorem readRefType_eq : readRefType = Decode.readRefType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readRefType, Decode.readRefType, readRefType_absHeapType_eq, readRefType_heapType_eq]
  rfl

theorem readValType_eq : readValType = Decode.readValType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readValType, Decode.readValType, readRefType_eq]
  rfl

theorem readBlockType_eq : readBlockType = Decode.readBlockType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readBlockType, Decode.readBlockType, readValType_eq, readS_eq, le_u32]

theorem readLimits_readBound_eq : readLimits.readBound = Decode.readLimits.readBound := by
  funext N
  simp only [readByte_eq, peekByte_eq, remaining_eq, readLimits.readBound, Decode.readLimits.readBound, readU_eq]

theorem readLimits_eq : readLimits = Decode.readLimits := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readLimits, Decode.readLimits, readLimits_readBound_eq]
  rfl

theorem readTableType_eq : readTableType = Decode.readTableType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readTableType, Decode.readTableType, readRefType_eq, readLimits_eq]

theorem readMemType_eq : readMemType = Decode.readMemType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readMemType, Decode.readMemType, readLimits_eq]

theorem readMemArg_eq : readMemArg = Decode.readMemArg := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readMemArg, Decode.readMemArg, readU_eq, readIdx_eq, shiftRight_eq_zero]

theorem plainOpT_eq (op : UInt8) : plainOpT op = plainOp? op := by
  simp [plainOpT, plainTable]

theorem memOpT_eq (op : UInt8) : memOpT op = memOp? op := by
  simp [memOpT, memTable]

theorem readOpOnly_eq : readOpOnly = Decode.readOpOnly := by
  funext op
  simp only [readByte_eq, peekByte_eq, remaining_eq, readOpOnly, Decode.readOpOnly, readMemArg_eq, plainOpT_eq, memOpT_eq]
  rfl

theorem readVecInstr_eq : readVecInstr = Decode.readVecInstr := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readVecInstr, Decode.readVecInstr, readU_eq, readMemArg_eq]
  rfl

theorem readGCInstr_eq : readGCInstr = Decode.readGCInstr := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readGCInstr, Decode.readGCInstr, readU_eq, readIdx_eq, readRefType_heapType_eq]
  rfl

theorem readPlainCases_eq : readPlainCases = Decode.readPlain := by
  funext op
  simp only [readByte_eq, peekByte_eq, remaining_eq, readPlainCases, Decode.readPlain, readU_eq, readS_eq, ofIntF_eq, readIdx_eq, readVec_eq,
    readValType_eq, readRefType_heapType_eq, readGCInstr_eq, readVecInstr_eq, readOpOnly_eq]
  rfl

/-- On a numeric opcode, `readPlain`'s cases are `readOpOnly`. -/
theorem readPlain_numeric {op : Nat} (h : 0x45 ≤ op ∧ op ≤ 0xC4) :
    readPlainCases op = readOpOnly op := by
  unfold readPlainCases
  split <;> first | omega | rfl

theorem readPlain_eq : readPlain = Decode.readPlain := by
  funext op
  unfold readPlain
  split
  · rename_i h
    rw [← readPlain_numeric h, readPlainCases_eq]
  · rw [readPlainCases_eq]

theorem readCatch_eq : readCatch = Decode.readCatch := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readCatch, Decode.readCatch, readIdx_eq]
  rfl

theorem readInstr_readSeq_eq : ∀ fuel,
    (∀ op, readInstr fuel op = Decode.readInstr fuel op) ∧ readSeq fuel = Decode.readSeq fuel
  | 0 => ⟨fun _ => rfl, rfl⟩
  | fuel + 1 => by
    have ih := readInstr_readSeq_eq fuel
    have hi : ∀ op, readInstr (fuel + 1) op = Decode.readInstr (fuel + 1) op := fun op => by
      simp only [readByte_eq, peekByte_eq, remaining_eq, readInstr, Decode.readInstr, readBlockType_eq, readVec_eq, readCatch_eq,
        readPlain_eq, ih.2]
      rfl
    have hs : readSeq (fuel + 1) = Decode.readSeq (fuel + 1) := by
      simp only [readByte_eq, peekByte_eq, remaining_eq, readSeq, Decode.readSeq, ih.1, ih.2]
    exact ⟨hi, hs⟩

theorem readSeq_eq : readSeq = Decode.readSeq := by
  funext fuel
  exact (readInstr_readSeq_eq fuel).2

theorem readExpr_eq : readExpr = Decode.readExpr := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readExpr, Decode.readExpr, readSeq_eq]

theorem readStorageType_eq : readStorageType = Decode.readStorageType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readStorageType, Decode.readStorageType, readValType_eq]
  rfl

theorem readFieldType_eq : readFieldType = Decode.readFieldType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readFieldType, Decode.readFieldType, readStorageType_eq]
  rfl

theorem readCompType_eq : readCompType = Decode.readCompType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readCompType, Decode.readCompType, readFieldType_eq, readVec_eq, readValType_eq]
  rfl

theorem readSubType_eq : readSubType = Decode.readSubType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readSubType, Decode.readSubType, readVec_eq, readIdx_eq, readCompType_eq]
  rfl

theorem readRecType_eq : readRecType = Decode.readRecType := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readRecType, Decode.readRecType, readVec_eq, readSubType_eq]

theorem readTable_eq : readTable = Decode.readTable := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readTable, Decode.readTable, readTableType_eq, readExpr_eq]

theorem readTag_eq : readTag = Decode.readTag := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readTag, Decode.readTag, readIdx_eq]

theorem readImport_eq : readImport = Decode.readImport := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readImport, Decode.readImport, readName_eq, readIdx_eq, readTableType_eq,
    readMemType_eq, readValType_eq, readTag_eq]
  rfl

theorem readGlobal_eq : readGlobal = Decode.readGlobal := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readGlobal, Decode.readGlobal, readValType_eq, readExpr_eq]
  rfl

theorem readExport_eq : readExport = Decode.readExport := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readExport, Decode.readExport, readName_eq, readIdx_eq]
  rfl

theorem readCode_eq : readCode = Decode.readCode := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readCode, Decode.readCode, readU_eq, readVec_eq, readValType_eq, readExpr_eq]

theorem readData_readByteVec_eq : readData.readByteVec = Decode.readData.readByteVec := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readData.readByteVec, Decode.readData.readByteVec, readCount_eq]

theorem readData_eq : readData = Decode.readData := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readData, Decode.readData, readU_eq, readExpr_eq, readData_readByteVec_eq,
    readIdx_eq]
  rfl

theorem readElem_funcInits_eq : readElem.funcInits = Decode.readElem.funcInits := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readElem.funcInits, Decode.readElem.funcInits, readVec_eq, readIdx_eq]

theorem readElem_eq : readElem = Decode.readElem := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readElem, Decode.readElem, readU_eq, readExpr_eq, readVec_eq, readIdx_eq,
    readElem_funcInits_eq, readRefType_eq]
  rfl

theorem readCustom_eq : readCustom = Decode.readCustom := by
  funext size
  simp only [readByte_eq, peekByte_eq, remaining_eq, readCustom, Decode.readCustom, readName_eq]

theorem readSectionBody_eq : readSectionBody = Decode.readSectionBody := by
  funext id s
  simp only [readByte_eq, peekByte_eq, remaining_eq, readSectionBody, Decode.readSectionBody, readVec_eq, readRecType_eq, readImport_eq,
    readIdx_eq, readTable_eq, readMemType_eq, readGlobal_eq, readExport_eq, readElem_eq,
    readCode_eq, readData_eq, readU_eq, readTag_eq]
  rfl

theorem readModule_go_eq : ∀ fuel last s,
    readModule.go fuel last s = Decode.readModule.go fuel last s
  | 0, _, _ => rfl
  | fuel + 1, last, s => by
    simp only [readByte_eq, peekByte_eq, remaining_eq, readModule.go, Decode.readModule.go, readU_eq, readCustom_eq, readSectionBody_eq,
      readModule_go_eq fuel]

theorem readModule_eq : readModule = Decode.readModule := by
  simp only [readByte_eq, peekByte_eq, remaining_eq, readModule, Decode.readModule, readModule_go_eq]

theorem decodeModule_eq : decodeModule = Decode.decodeModule := by
  funext b
  simp only [readByte_eq, peekByte_eq, remaining_eq, decodeModule, Decode.decodeModule, readModule_eq]

/-- **The fast decoder is silmaril's decoder.** -/
theorem decodeF_eq : decodeF = decode? := by
  funext b
  simp only [readByte_eq, peekByte_eq, remaining_eq, decodeF, decode?, decodeModule_eq]
  rfl

end Silmaril.Proofs.Wasm.Perf.CoreDecode
