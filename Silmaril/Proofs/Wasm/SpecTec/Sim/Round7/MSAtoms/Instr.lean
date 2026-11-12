module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.InstrV

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge: instructions and administrative instructions

* `nh_instrToV_flat`: an instruction other than a block form, a memory SIMD instruction and
  `call_ref` has an `instrToV` image without an atom of `HStep.hAtoms`.
* `instrOk cr i`: no memory SIMD instruction in `i` at any depth, and no `call_ref` unless `cr`.
  `instrOk true` is `Round6.MemSimd.instrMS` (`instrOk_true`).
* `na_instrToV`, `na_adminToV`: under `instrOk cr` (and `adminOk cr` for administrative
  instructions), the `instrToV`/`adminToV` image has no atom of `A`, for every `A ⊆ hAtoms`
  that leaves out `CALL_REF` when `cr` allows `call_ref`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open HStep (hAtoms)
open Round6.MemSimd (memSimd instrMS instrsMS AdminMS AdminsMS)

/-! ## The flat instructions -/

/-- The four block forms. -/
def blockForm : Instr → Bool
  | .block .. | .loop .. | .if_ .. | .tryTable .. => true
  | _ => false

theorem nh_list_map_of {α : Type} {f : α → Value} (h : ∀ x, NH (f x)) (l : List α) :
    NoAtomsL hAtoms (l.map f) :=
  noAtoms_list_map (A := hAtoms) (fun x _ => h x)

theorem nh_opt_map_of {α : Type} {f : α → Value} (h : ∀ x, NH (f x)) (o : Option α) :
    NoAtoms hAtoms (.opt (o.map f)) :=
  noAtoms_opt_map fun x _ => h x

theorem nh_getD_vec {i : Instr} {d : Value} (hs : (Vec.vecInstrV? i).isSome = true) :
    NH ((Vec.vecInstrV? i).getD d) := by
  cases h : Vec.vecInstrV? i with
  | none => simp [h] at hs
  | some v => exact nh_vecInstrV? h

theorem nh_select (ts : Option (List ValType)) : NH (Sim.instrToV (.select ts)) := by
  cases ts with
  | none => exact atomsFreeB_sound _ _ (by decide)
  | some ts =>
    have h : NoAtomsL hAtoms (ts.map Encode.toValue) := nh_list_map_of nh_valType ts
    show NH (.case "SELECT" (.opt (some (.list (ts.map Encode.toValue)))))
    nh_close

theorem nh_intLoad (t : IntType) (p : Option (PackSize × Signedness)) (m : MemIdx) (a : MemArg) :
    NH (Sim.instrToV (.intLoad t p m a)) := by
  have h₁ : NH (Encode.toValue (NumType.int t)) := nh_numType (.int t)
  have h₂ : NH (Encode.toValue m) := nh_idx m
  have h₃ : NH (Sim.memargV a) := nh_memargV a
  have h₄ : NH (.opt (p.map fun q => .case "%_%" (.tuple [Sim.szV q.1, Sim.sxV q.2]))) :=
    noAtoms_opt_map fun q _ => by
      have h₅ : NH (Sim.szV q.1) := nh_szV q.1
      have h₆ : NH (Sim.sxV q.2) := nh_sxV q.2
      nh_close
  unfold Sim.instrToV
  nh_close

theorem nh_intStore (t : IntType) (p : Option PackSize) (m : MemIdx) (a : MemArg) :
    NH (Sim.instrToV (.intStore t p m a)) := by
  have h₁ : NH (Encode.toValue (NumType.int t)) := nh_numType (.int t)
  have h₂ : NH (Encode.toValue m) := nh_idx m
  have h₃ : NH (Sim.memargV a) := nh_memargV a
  have h₄ : NH (.opt (p.map fun q => .case "%" (.tuple [Sim.szV q]))) :=
    noAtoms_opt_map fun q _ => by
      have h₅ : NH (Sim.szV q) := nh_szV q
      nh_close
  unfold Sim.instrToV
  nh_close

/-- The remaining flat instructions: one of three closing steps. -/
macro "nh_flat_arm" : tactic =>
  `(tactic| (unfold Sim.instrToV
             first
               | exact nh_instrV _ (by simp)
               | exact nh_getD_vec rfl
               | exact nh_valV _
               | exact nh_convertInstrV _
               | nh_close [nh_idx, nh_refType, nh_blockType, nh_valType, nh_numType, nh_sxV,
                   nh_szV, nh_memargV, nh_pctV, nh_list_map_of nh_idx, nh_opt_map_of nh_sxV,
                   caseNilV]))

/-- **A flat instruction off memory SIMD and `call_ref` has no atom of `hAtoms`.** -/
theorem nh_instrToV_flat (i : Instr) (hb : blockForm i = false) (hms : memSimd i = false)
    (hc : ∀ x, i ≠ .callRef x) : NH (Sim.instrToV i) := by
  cases i
  case block | loop | if_ | tryTable => simp [blockForm] at hb
  case vecLoad | vecLoadLane | vecStore | vecStoreLane => simp [memSimd] at hms
  case callRef x => exact absurd rfl (hc x)
  case select ts => exact nh_select ts
  case intLoad t p m a => exact nh_intLoad t p m a
  case intStore t p m a => exact nh_intStore t p m a
  all_goals nh_flat_arm

/-! ## The recursion through block bodies -/


mutual
/-- **`instrOk true` is `instrMS`.** -/
theorem instrOk_true : ∀ i : Instr, instrOk true i = instrMS i
  | .block _ body => by simp only [instrOk, instrMS, instrsOk_true body]
  | .loop _ body => by simp only [instrOk, instrMS, instrsOk_true body]
  | .if_ _ b₁ b₂ => by simp only [instrOk, instrMS, instrsOk_true b₁, instrsOk_true b₂]
  | .tryTable _ _ body => by simp only [instrOk, instrMS, instrsOk_true body]
  | .callRef _ => by simp [instrOk, instrMS, memSimd]
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .brOnNull _
  | .brOnNonNull _ | .brOnCast .. | .brOnCastFail .. | .call _ | .callIndirect .. | .return_
  | .returnCall _ | .returnCallRef _ | .returnCallIndirect .. | .throw _ | .throwRef
  | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _ | .tableGet _
  | .tableSet _ | .tableSize _ | .tableGrow _ | .tableFill _ | .tableCopy .. | .tableInit ..
  | .elemDrop _ | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. | .vecLoad ..
  | .vecLoadLane .. | .vecStore .. | .vecStoreLane .. | .memorySize _ | .memoryGrow _
  | .memoryFill _ | .memoryCopy .. | .memoryInit .. | .dataDrop _ | .refNull _ | .refIsNull
  | .refAsNonNull | .refEq | .refTest _ | .refCast _ | .refFunc _ | .refI31 | .i31Get _
  | .structNew _ | .structNewDefault _ | .structGet .. | .structSet .. | .arrayNew _
  | .arrayNewDefault _ | .arrayNewFixed .. | .arrayNewData .. | .arrayNewElem .. | .arrayGet ..
  | .arraySet _ | .arrayLen | .arrayFill _ | .arrayCopy .. | .arrayInitData .. | .arrayInitElem ..
  | .externConvertAny | .anyConvertExtern | .intConst .. | .floatConst .. | .intUnOp ..
  | .intBinOp .. | .intTestOp .. | .intRelOp .. | .floatUnOp .. | .floatBinOp .. | .floatRelOp ..
  | .convert _ | .vecConst _ | .vecUnOp _ | .vecBinOp _ | .vecTernOp _ | .vecTestOp _
  | .vecIntUnOp .. | .vecFloatUnOp .. | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp ..
  | .vecFloatTernOp .. | .vecAllTrue _ | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp ..
  | .vecBitmask _ | .vecSwizzle _ | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp ..
  | .vecExtTernOp .. | .vecNarrow .. | .vecConvert .. | .vecSplat _ | .vecExtractLane ..
  | .vecReplaceLane .. => by simp [instrOk, instrMS]

theorem instrsOk_true : ∀ is : List Instr, instrsOk true is = instrsMS is
  | [] => rfl
  | i :: is => by simp only [instrsOk, instrsMS, instrOk_true i, instrsOk_true is]
end

section
variable {A : List MixopS} (hA : ∀ a ∈ A, a ∈ hAtoms) {cr : Bool}

include hA in
/-- The flat case of `na_instrToV`. -/
theorem na_flat (i : Instr) (h : instrOk cr i = true) (hb : blockForm i = false)
    (hc : ∀ x, i ≠ .callRef x) : NoAtoms A (Sim.instrToV i) := by
  have hms : memSimd i = false := by
    cases i <;> simp_all [instrOk, blockForm]
  exact noAtoms_mono hA _ (nh_instrToV_flat i hb hms hc)

include hA in
theorem na_of_nh {v : Value} (h : NH v) : NoAtoms A v := noAtoms_mono hA v h

mutual
/-- **`instrToV` has no atom of `A` under `instrOk cr`.** -/
theorem na_instrToV (hA : ∀ a ∈ A, a ∈ hAtoms) (hcr : cr = true → "CALL_REF" ∉ A) :
    ∀ i : Instr, instrOk cr i = true → NoAtoms A (Sim.instrToV i)
  | .block bt body, h => by
      have h₁ := na_instrsToV hA hcr body (by simpa only [instrOk] using h)
      have h₂ := na_of_nh hA (nh_blockType bt)
      unfold Sim.instrToV
      exact ⟨fun hm => absurd (hA _ hm) (by simp [mem_hAtoms]), ⟨h₂, h₁, trivial⟩⟩
  | .loop bt body, h => by
      have h₁ := na_instrsToV hA hcr body (by simpa only [instrOk] using h)
      have h₂ := na_of_nh hA (nh_blockType bt)
      unfold Sim.instrToV
      exact ⟨fun hm => absurd (hA _ hm) (by simp [mem_hAtoms]), ⟨h₂, h₁, trivial⟩⟩
  | .if_ bt b₁ b₂, h => by
      simp only [instrOk, Bool.and_eq_true] at h
      have h₁ := na_instrsToV hA hcr b₁ h.1
      have h₂ := na_instrsToV hA hcr b₂ h.2
      have h₃ := na_of_nh hA (nh_blockType bt)
      unfold Sim.instrToV
      exact ⟨fun hm => absurd (hA _ hm) (by simp [mem_hAtoms]), ⟨h₃, h₁, h₂, trivial⟩⟩
  | .tryTable bt cs body, h => by
      have h₁ := na_instrsToV hA hcr body (by simpa only [instrOk] using h)
      have h₂ := na_of_nh hA (nh_blockType bt)
      have h₃ : NoAtoms A (.case "%" (.tuple [.list (cs.map Encode.toValue)])) :=
        na_of_nh hA (by
          have := nh_list_map_of nh_catch cs
          nh_close)
      unfold Sim.instrToV
      exact ⟨fun hm => absurd (hA _ hm) (by simp [mem_hAtoms]), ⟨h₂, h₃, h₁, trivial⟩⟩
  | .callRef x, h => by
      have hc : cr = true := by simpa only [instrOk] using h
      have hx := na_of_nh hA (nh_idx x)
      unfold Sim.instrToV
      show NoAtoms A (.case "CALL_REF" (.case "_IDX" (Encode.toValue x)))
      exact ⟨hcr hc, fun hm => absurd (hA _ hm) (by simp [mem_hAtoms]), hx⟩
  | .nop, h | .unreachable, h | .drop, h | .select _, h | .br _, h | .brIf _, h | .brTable _ _, h
  | .brOnNull _, h | .brOnNonNull _, h | .brOnCast .., h | .brOnCastFail .., h | .call _, h
  | .callIndirect .., h | .return_, h | .returnCall _, h | .returnCallRef _, h
  | .returnCallIndirect .., h | .throw _, h | .throwRef, h | .localGet _, h | .localSet _, h
  | .localTee _, h | .globalGet _, h | .globalSet _, h | .tableGet _, h | .tableSet _, h
  | .tableSize _, h | .tableGrow _, h | .tableFill _, h | .tableCopy .., h | .tableInit .., h
  | .elemDrop _, h | .intLoad .., h | .floatLoad .., h | .intStore .., h | .floatStore .., h
  | .vecLoad .., h | .vecLoadLane .., h | .vecStore .., h | .vecStoreLane .., h
  | .memorySize _, h | .memoryGrow _, h | .memoryFill _, h | .memoryCopy .., h
  | .memoryInit .., h | .dataDrop _, h | .refNull _, h | .refIsNull, h | .refAsNonNull, h
  | .refEq, h | .refTest _, h | .refCast _, h | .refFunc _, h | .refI31, h | .i31Get _, h
  | .structNew _, h | .structNewDefault _, h | .structGet .., h | .structSet .., h
  | .arrayNew _, h | .arrayNewDefault _, h | .arrayNewFixed .., h | .arrayNewData .., h
  | .arrayNewElem .., h | .arrayGet .., h | .arraySet _, h | .arrayLen, h | .arrayFill _, h
  | .arrayCopy .., h | .arrayInitData .., h | .arrayInitElem .., h | .externConvertAny, h
  | .anyConvertExtern, h | .intConst .., h | .floatConst .., h | .intUnOp .., h | .intBinOp .., h
  | .intTestOp .., h | .intRelOp .., h | .floatUnOp .., h | .floatBinOp .., h | .floatRelOp .., h
  | .convert _, h | .vecConst _, h | .vecUnOp _, h | .vecBinOp _, h | .vecTernOp _, h
  | .vecTestOp _, h | .vecIntUnOp .., h | .vecFloatUnOp .., h | .vecIntBinOp .., h
  | .vecFloatBinOp .., h | .vecIntTernOp .., h | .vecFloatTernOp .., h | .vecAllTrue _, h
  | .vecIntRelOp .., h | .vecFloatRelOp .., h | .vecShiftOp .., h | .vecBitmask _, h
  | .vecSwizzle _, h | .vecShuffle _, h | .vecExtUnOp .., h | .vecExtBinOp .., h
  | .vecExtTernOp .., h | .vecNarrow .., h | .vecConvert .., h | .vecSplat _, h
  | .vecExtractLane .., h | .vecReplaceLane .., h =>
      na_flat hA _ h rfl (fun _ => by simp)

/-- `na_instrToV` on a sequence. -/
theorem na_instrsToV (hA : ∀ a ∈ A, a ∈ hAtoms) (hcr : cr = true → "CALL_REF" ∉ A) :
    ∀ is : List Instr, instrsOk cr is = true →
    NoAtomsL A (Sim.instrsToV is)
  | [], _ => trivial
  | i :: is, h => by
      simp only [instrsOk, Bool.and_eq_true] at h
      exact ⟨na_instrToV hA hcr i h.1, na_instrsToV hA hcr is h.2⟩
end

end

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
