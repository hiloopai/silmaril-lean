module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms

/-!
# Re-encoding export lists: the value map

* `swapV_swapV`: when `τ` is an involution, so is `swapV τ`.
* `swapV_of_nxB`: `swapV τ` fixes every value without a record with an `EXPORTS` field
  (`Round7.Swap.nxB`).
* `nxB_*`: the 2.0 encoders other than `moduleInstV` build no such record: types, values,
  operators, instructions (`nxB_instrToV`), and the store's instances.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)
open Silmaril.Wasm.SpecTec.Sim20

variable {τ : Value → Value}

/-! ## Unfolding -/

@[simp] theorem swapV_bool (b : Bool) : swapV τ (.bool b) = .bool b := rfl
@[simp] theorem swapV_num (n : IL.Num) : swapV τ (.num n) = .num n := rfl
@[simp] theorem swapV_text (t : IL.Text) : swapV τ (.text t) = .text t := rfl
@[simp] theorem swapV_case (op : IL.MixopS) (w : Value) :
    swapV τ (.case op w) = .case op (swapV τ w) := rfl
@[simp] theorem swapV_struct (gs : List (IL.AtomS × Value)) :
    swapV τ (.struct gs) = .struct (swapVf τ gs) := rfl
@[simp] theorem swapVf_nil : swapVf τ [] = [] := rfl
@[simp] theorem swapVf_cons (a : IL.AtomS) (v : Value) (gs : List (IL.AtomS × Value)) :
    swapVf τ ((a, v) :: gs) = (a, if a = "EXPORTS" then τ v else swapV τ v) :: swapVf τ gs :=
  rfl

theorem swapVs_eq_map : ∀ vs : List Value, swapVs τ vs = vs.map (swapV τ)
  | [] => rfl
  | v :: vs => by simp only [swapVs, swapVs_eq_map vs, List.map_cons]

@[simp] theorem swapV_list (vs : List Value) : swapV τ (.list vs) = .list (vs.map (swapV τ)) := by
  simp only [swapV, swapVs_eq_map]

@[simp] theorem swapV_tuple (vs : List Value) :
    swapV τ (.tuple vs) = .tuple (vs.map (swapV τ)) := by
  simp only [swapV, swapVs_eq_map]

@[simp] theorem swapV_opt (o : Option Value) : swapV τ (.opt o) = .opt (o.map (swapV τ)) := by
  cases o <;> rfl

/-! ## An involution -/

mutual
/-- **`swapV τ` is an involution when `τ` is.** -/
theorem swapV_swapV (hτ : ∀ u, τ (τ u) = u) : ∀ v : Value, swapV τ (swapV τ v) = v
  | .bool _ | .num _ | .text _ | .opt none => rfl
  | .tuple vs => by
    simp only [swapV]
    rw [swapVs_swapVs hτ vs]
  | .case op w => by
    simp only [swapV]
    rw [swapV_swapV hτ w]
  | .struct gs => by
    simp only [swapV]
    rw [swapVf_swapVf hτ gs]
  | .list vs => by
    simp only [swapV]
    rw [swapVs_swapVs hτ vs]
  | .opt (some w) => by
    simp only [swapV]
    rw [swapV_swapV hτ w]

/-- `swapV_swapV` on a list. -/
theorem swapVs_swapVs (hτ : ∀ u, τ (τ u) = u) : ∀ vs : List Value, swapVs τ (swapVs τ vs) = vs
  | [] => rfl
  | v :: vs => by
    simp only [swapVs]
    rw [swapV_swapV hτ v, swapVs_swapVs hτ vs]

/-- `swapV_swapV` on the fields of a record. -/
theorem swapVf_swapVf (hτ : ∀ u, τ (τ u) = u) :
    ∀ gs : List (IL.AtomS × Value), swapVf τ (swapVf τ gs) = gs
  | [] => rfl
  | (a, v) :: gs => by
    simp only [swapVf]
    rw [swapVf_swapVf hτ gs]
    by_cases ha : a = "EXPORTS"
    · simp only [ha, ite_true, hτ]
    · simp only [ha, ite_false, swapV_swapV hτ v]
end

/-! ## Values without `EXPORTS` records are fixed -/

mutual
/-- **`swapV τ` fixes a value without an `EXPORTS` record.** -/
theorem swapV_of_nxB : ∀ v : Value, nxB v = true → swapV τ v = v
  | .bool _, _ | .num _, _ | .text _, _ | .opt none, _ => rfl
  | .tuple vs, h => by
    simp only [swapV]
    rw [swapVs_of_nxBs vs h]
  | .case _ w, h => by
    simp only [swapV]
    rw [swapV_of_nxB w h]
  | .struct gs, h => by
    simp only [swapV]
    rw [swapVf_of_nxBf gs h]
  | .list vs, h => by
    simp only [swapV]
    rw [swapVs_of_nxBs vs h]
  | .opt (some w), h => by
    simp only [swapV]
    rw [swapV_of_nxB w h]

/-- `swapV_of_nxB` on a list. -/
theorem swapVs_of_nxBs : ∀ vs : List Value, nxBs vs = true → swapVs τ vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [nxBs, Bool.and_eq_true] at h
    simp only [swapVs]
    rw [swapV_of_nxB v h.1, swapVs_of_nxBs vs h.2]

/-- `swapV_of_nxB` on the fields of a record. -/
theorem swapVf_of_nxBf : ∀ gs : List (IL.AtomS × Value), nxBf gs = true → swapVf τ gs = gs
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [nxBf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [swapVf, h.1.2, ite_false]
    rw [swapV_of_nxB v h.1.1, swapVf_of_nxBf gs h.2]
end

/-! ## The 2.0 encoders build no `EXPORTS` record -/

/-- Close `nxB e = true` for an encoder at a constructor, splitting finite arguments. -/
syntax "nx_leaf" : tactic
macro_rules
  | `(tactic| nx_leaf) => `(tactic| first | rfl | (rename_i x; cases x; all_goals nx_leaf))

@[simp] theorem nxB_pctV (n : Nat) : nxB (pctV n) = true := rfl
@[simp] theorem nxB_caseNilV (op : IL.MixopS) : nxB (caseNilV op) = true := rfl
@[simp] theorem nxB_numTypeV (t : NumType) : nxB (numTypeV t) = true := by
  rcases t with (_ | _) | (_ | _) <;> rfl
@[simp] theorem nxB_refTypeV (t : V2.RefType) : nxB (refTypeV t) = true := by cases t <;> rfl
@[simp] theorem nxB_valTypeV (t : V2.ValType) : nxB (valTypeV t) = true := by
  rcases t with t | ⟨⟩ | t <;> simp [valTypeV]
@[simp] theorem nxB_resultTypeV (ts : List V2.ValType) : nxB (resultTypeV ts) = true := by
  simp [resultTypeV]
@[simp] theorem nxB_funcTypeV (ft : V2.FuncType) : nxB (funcTypeV ft) = true := by
  simp [funcTypeV]
@[simp] theorem nxB_limitsV (l : V2.Limits) : nxB (limitsV l) = true := by
  simp [limitsV]
@[simp] theorem nxB_mutV (m : Mutability) : nxB (mutV m) = true := by cases m <;> rfl
@[simp] theorem nxB_globalTypeV (g : V2.GlobalType) : nxB (globalTypeV g) = true := by
  simp [globalTypeV]
@[simp] theorem nxB_tableTypeV (t : V2.TableType) : nxB (tableTypeV t) = true := by
  simp [tableTypeV]
@[simp] theorem nxB_memTypeV (m : V2.MemoryType) : nxB (memTypeV m) = true := by
  simp [memTypeV]
@[simp] theorem nxB_idxV {k : IndexKind} (x : Idx k) : nxB (idxV x) = true := rfl
@[simp] theorem nxB_blockTypeV (bt : V2.BlockType) : nxB (blockTypeV bt) = true := by
  cases bt <;> simp [blockTypeV]
@[simp] theorem nxB_floatV (t : FloatType) (b : BitVec t.width) : nxB (Sim.floatV t b) = true := by
  simp only [Sim.floatV]
  split_ifs <;> rfl
@[simp] theorem nxB_numV (n : NumVal) : nxB (numV n) = true := by
  rcases n with ⟨_ | t, b⟩
  · simp [numV]
  · exact nxB_floatV t b
@[simp] theorem nxB_refV (r : Ref) : nxB (refV r) = true := by cases r <;> simp [refV]
@[simp] theorem nxB_valV (v : Val) : nxB (valV v) = true := by cases v <;> simp [valV]
@[simp] theorem nxB_sxV (s : Signedness) : nxB (sxV s) = true := by cases s <;> rfl
@[simp] theorem nxB_intUnOpV (o : IntUnOp) : nxB (intUnOpV o) = true := by cases o <;> nx_leaf
@[simp] theorem nxB_floatUnOpV (o : FloatUnOp) : nxB (floatUnOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_intBinOpV (o : IntBinOp) : nxB (intBinOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_floatBinOpV (o : FloatBinOp) : nxB (floatBinOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_intTestOpV (o : IntTestOp) : nxB (intTestOpV o) = true := by
  cases o; nx_leaf
@[simp] theorem nxB_intRelOpV (o : IntRelOp) : nxB (intRelOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_floatRelOpV (o : FloatRelOp) : nxB (floatRelOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_cvtOpV (o : V2.CvtOp) : nxB (cvtOpV o) = true := by cases o <;> nx_leaf
@[simp] theorem nxB_jnnV (s : IntShape) : nxB (jnnV s) = true := by cases s <;> rfl
@[simp] theorem nxB_fnnV (s : FloatShape) : nxB (fnnV s) = true := by cases s <;> rfl
@[simp] theorem nxB_ishapeV (s : IntShape) : nxB (ishapeV s) = true := by cases s <;> rfl
@[simp] theorem nxB_shapeV (s : Shape) : nxB (shapeV s) = true := by
  rcases s with s | s <;> cases s <;> rfl
@[simp] theorem nxB_halfV (h : Half) : nxB (halfV h) = true := by cases h <;> rfl
@[simp] theorem nxB_vecIntUnOpV (o : VecIntUnOp) : nxB (vecIntUnOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_vecIntBinOpV (o : V2.VecIntBinOp) : nxB (vecIntBinOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_vecFloatBinOpV (o : V2.VecFloatBinOp) : nxB (vecFloatBinOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_vecIntRelOpV (o : IntRelOp) : nxB (vecIntRelOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_vecShiftOpV (o : VecShiftOp) : nxB (vecShiftOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_vecExtUnOpV (o : VecExtUnOp) : nxB (vecExtUnOpV o) = true := by
  cases o; nx_leaf
@[simp] theorem nxB_vecExtBinOpV (o : V2.VecExtBinOp) : nxB (vecExtBinOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_vecCvtOpV (o : V2.VecCvtOp) : nxB (vecCvtOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_vecLoadOpV (o : V2.VecLoadOp) : nxB (vecLoadOpV o) = true := by
  cases o <;> nx_leaf
@[simp] theorem nxB_memargV (a : V2.MemArg) : nxB (memargV a) = true := rfl
@[simp] theorem nxB_szV (p : PackSize) : nxB (szV p) = true := rfl

/-- **Instruction images have no `EXPORTS` record.** -/
theorem nxB_instrToV (i : V2.Instr) : nxB (instrToV i) = true := by
  induction i using V2.Instr.rec (motive_2 := fun l => nxBs (instrsToV l) = true) with
  | nil => rfl
  | cons _ _ h₁ h₂ => simp only [instrsToV, Silmaril.Wasm.SpecTec.Sim.Round7.Swap.nxBs_cons, h₁, h₂,
      Bool.and_self]
  | block _ _ h => simp [instrToV, h]
  | loop _ _ h => simp [instrToV, h]
  | if_ _ _ _ h₁ h₂ => simp [instrToV, h₁, h₂]
  | vvUnOp o => cases o; rfl
  | vvBinOp o => cases o <;> rfl
  | vvTernOp o => cases o; rfl
  | vvTestOp o => cases o; rfl
  | intLoad _ p _ => cases p <;> simp [instrToV]
  | intStore _ p _ => cases p <;> simp [instrToV]
  | vecLoad o _ => cases o <;> simp [instrToV]
  | vecExtractLane _ s _ => cases s <;> simp [instrToV]
  | select ts => cases ts <;> simp [instrToV]
  | _ => simp [instrToV]

@[simp] theorem nxBs_instrsToV (l : List V2.Instr) : nxBs (instrsToV l) = true := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [instrsToV, Silmaril.Wasm.SpecTec.Sim.Round7.Swap.nxBs_cons,
      nxB_instrToV, ih, Bool.and_self]

@[simp] theorem nxB_instrToV' (i : V2.Instr) : nxB (instrToV i) = true := nxB_instrToV i

@[simp] theorem nxB_bytesV (b : ByteArray) : nxB (bytesV b) = true := by simp [bytesV]
@[simp] theorem nxB_nameV (s : String) : nxB (nameV s) = true := by simp [nameV]
@[simp] theorem nxB_externAddrV (a : ExternAddr) : nxB (externAddrV a) = true := by
  cases a <;> rfl
@[simp] theorem nxB_addrsV (xs : List Nat) : nxB (addrsV xs) = true := by simp [addrsV]
@[simp] theorem nxB_globalInstV (g : GlobalInst) : nxB (globalInstV g) = true := by
  simp [globalInstV]
@[simp] theorem nxB_tableInstV (t : TableInst) : nxB (tableInstV t) = true := by
  simp [tableInstV]
@[simp] theorem nxB_memInstV (m : MemInst) : nxB (memInstV m) = true := by simp [memInstV]
@[simp] theorem nxB_elemInstV (e : ElemInst) : nxB (elemInstV e) = true := by simp [elemInstV]
@[simp] theorem nxB_dataInstV (d : DataInst) : nxB (dataInstV d) = true := by simp [dataInstV]

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
