module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecAgreeVOk
public import Silmaril.Wasm.SpecTec.Sim20.Encode.Defs

/-!
# Every image of V2 data is `VOk`

V2's float vector operators are nullary and named as in the float instance of their family
(`floatUnOpV`, `vecFloatBinOpV`, `floatRelOpV`), so every `VUNOP`, `VBINOP` and `VRELOP` image at
a float shape carries an operator the corrected script's float instance accepts.

**`vokB_instrToV`**, `vokB_adminToV`, **`vOk_stateV`**, `vOk_configV`: instruction, administrative
instruction, state and configuration images are `VOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim20 (instrToV instrsToV adminToV adminsToV)

/-- A case that is not an operator case. -/
theorem vokB_case_of {op : String} (h : famOfOp? op = none) (w : Value) :
    vokB (.case op w) = vokB w := by
  simp [payOkB_of_none h]

@[simp] theorem vokB_caseNilV (o : String) : vokB (caseNilV o) = true := by
  simp only [caseNilV, vokB_case, vokB_tuple, vokBs_nil, Bool.true_and, payOkB]
  split <;> simp_all

@[simp] theorem vokB_pctV (n : Nat) : vokB (pctV n) = true := by
  simp [pctV, payOkB, famOfOp?]

@[simp] theorem vokB_numTypeV (t : NumType) : vokB (numTypeV t) = true := by
  rcases t with (_ | _) | (_ | _) <;> simp [numTypeV]

@[simp] theorem vokB_refTypeV (t : V2.RefType) : vokB (refTypeV t) = true := by
  cases t <;> simp [refTypeV]

@[simp] theorem vokB_valTypeV (t : V2.ValType) : vokB (valTypeV t) = true := by
  rcases t with t | ⟨⟩ | t <;> simp [valTypeV]

@[simp] theorem vokB_valTypes (ts : List V2.ValType) : vokBs (ts.map valTypeV) = true := by
  simp [vokBs_eq_all]

@[simp] theorem vokB_resultTypeV (ts : List V2.ValType) : vokB (resultTypeV ts) = true := by
  simp [resultTypeV, payOkB, famOfOp?]

@[simp] theorem vokB_funcTypeV (ft : V2.FuncType) : vokB (funcTypeV ft) = true := by
  simp [funcTypeV, payOkB, famOfOp?]

@[simp] theorem vokB_idxV {k : IndexKind} (x : Idx k) : vokB (idxV x) = true := by
  simp [idxV]

@[simp] theorem vokB_blockTypeV (bt : V2.BlockType) : vokB (blockTypeV bt) = true := by
  rcases bt with (_ | t) | x <;> simp [blockTypeV, payOkB, famOfOp?]

@[simp] theorem vokB_sxV (s : Signedness) : vokB (sxV s) = true := by
  cases s <;> simp [sxV]

theorem vokB_floatV (t : FloatType) (b : BitVec t.width) : vokB (Sim.floatV t b) = true := by
  simp only [Sim.floatV]
  split_ifs <;> simp [payOkB, famOfOp?]

@[simp] theorem vokB_numV (n : NumVal) : vokB (numV n) = true := by
  obtain ⟨t, b⟩ := n
  cases t with
  | int _ => simp [numV]
  | float t => exact vokB_floatV t b

@[simp] theorem vokB_refV (r : Ref) : vokB (refV r) = true := by
  cases r <;> simp [refV, payOkB, famOfOp?]

@[simp] theorem vokB_valV (v : Val) : vokB (valV v) = true := by
  cases v <;> simp [valV, payOkB, famOfOp?]

@[simp] theorem vokB_intUnOpV (op : IntUnOp) : vokB (intUnOpV op) = true := by
  cases op <;> simp [intUnOpV, payOkB, famOfOp?]

@[simp] theorem vokB_floatUnOpV (op : FloatUnOp) : vokB (floatUnOpV op) = true := by
  cases op <;> simp [floatUnOpV]

@[simp] theorem vokB_intBinOpV (op : IntBinOp) : vokB (intBinOpV op) = true := by
  cases op <;> simp [intBinOpV, payOkB, famOfOp?]

@[simp] theorem vokB_floatBinOpV (op : FloatBinOp) : vokB (floatBinOpV op) = true := by
  cases op <;> simp [floatBinOpV]

@[simp] theorem vokB_intTestOpV (op : IntTestOp) : vokB (intTestOpV op) = true := by
  cases op; simp [intTestOpV]

@[simp] theorem vokB_intRelOpV (op : IntRelOp) : vokB (intRelOpV op) = true := by
  cases op <;> simp [intRelOpV, payOkB, famOfOp?]

@[simp] theorem vokB_floatRelOpV (op : FloatRelOp) : vokB (floatRelOpV op) = true := by
  cases op <;> simp [floatRelOpV]

@[simp] theorem vokB_cvtOpV (op : V2.CvtOp) : vokB (cvtOpV op) = true := by
  cases op <;> simp [cvtOpV, payOkB, famOfOp?]

@[simp] theorem vokB_shapeV (s : Shape) : vokB (shapeV s) = true := by
  rcases s with s | s <;> cases s <;> simp [shapeV, ishapeV, jnnV, fnnV, dimV, payOkB, famOfOp?]

@[simp] theorem vokB_ishapeV (s : IntShape) : vokB (ishapeV s) = true := by
  simpa [shapeV] using vokB_shapeV (.int s)

@[simp] theorem vokB_halfV (h : Half) : vokB (halfV h) = true := by
  cases h <;> simp [halfV]

@[simp] theorem vokB_vecIntUnOpV (op : VecIntUnOp) : vokB (vecIntUnOpV op) = true := by
  cases op <;> simp [vecIntUnOpV]

@[simp] theorem vokB_vecIntBinOpV (op : V2.VecIntBinOp) : vokB (vecIntBinOpV op) = true := by
  cases op <;> simp [vecIntBinOpV, payOkB, famOfOp?]

@[simp] theorem vokB_vecFloatBinOpV (op : V2.VecFloatBinOp) : vokB (vecFloatBinOpV op) = true := by
  cases op <;> simp [vecFloatBinOpV]

@[simp] theorem vokB_vecIntRelOpV (op : IntRelOp) : vokB (vecIntRelOpV op) = true := by
  cases op <;> simp [vecIntRelOpV, payOkB, famOfOp?]

@[simp] theorem vokB_vecShiftOpV (op : VecShiftOp) : vokB (vecShiftOpV op) = true := by
  cases op <;> simp [vecShiftOpV, payOkB, famOfOp?]

@[simp] theorem vokB_vecExtUnOpV (op : VecExtUnOp) : vokB (vecExtUnOpV op) = true := by
  cases op; simp [vecExtUnOpV, payOkB, famOfOp?]

@[simp] theorem vokB_vecExtBinOpV (op : V2.VecExtBinOp) : vokB (vecExtBinOpV op) = true := by
  cases op <;> simp [vecExtBinOpV, payOkB, famOfOp?]

@[simp] theorem vokB_vecCvtOpV (op : V2.VecCvtOp) : vokB (vecCvtOpV op) = true := by
  cases op with
  | truncSat s z => cases z <;> simp [vecCvtOpV, payOkB, famOfOp?]
  | convert h s => cases h <;> simp [vecCvtOpV, payOkB, famOfOp?]
  | _ => simp [vecCvtOpV, payOkB, famOfOp?]

@[simp] theorem vokB_vecLoadOpV (op : V2.VecLoadOp) : vokB (vecLoadOpV op) = true := by
  cases op <;> simp [vecLoadOpV, payOkB, famOfOp?]

@[simp] theorem vokB_memargV (a : V2.MemArg) : vokB (memargV a) = true := by
  simp [memargV]

@[simp] theorem vokB_szV (p : PackSize) : vokB (szV p) = true := by
  simp [szV]

/-! ## Instructions -/

theorem payOkB_vunop (s : Shape) (w : Value) (hw : ∀ fs, s = .float fs → nullInB "vunop_" w = true) :
    payOkB "VUNOP" (.tuple [shapeV s, w]) = true := by
  rcases s with s | s
  · cases s <;> simp [payOkB, famOfOp?, shapeV, ishapeV, jnnV, floatShB, caseNilV]
  · simp [payOkB, famOfOp?, hw s rfl]

theorem payOkB_vbinop (s : Shape) (w : Value) (hw : ∀ fs, s = .float fs → nullInB "vbinop_" w = true) :
    payOkB "VBINOP" (.tuple [shapeV s, w]) = true := by
  rcases s with s | s
  · cases s <;> simp [payOkB, famOfOp?, shapeV, ishapeV, jnnV, floatShB, caseNilV]
  · simp [payOkB, famOfOp?, hw s rfl]

theorem payOkB_vrelop (s : Shape) (w : Value) (hw : ∀ fs, s = .float fs → nullInB "vrelop_" w = true) :
    payOkB "VRELOP" (.tuple [shapeV s, w]) = true := by
  rcases s with s | s
  · cases s <;> simp [payOkB, famOfOp?, shapeV, ishapeV, jnnV, floatShB, caseNilV]
  · simp [payOkB, famOfOp?, hw s rfl]

mutual
@[simp] theorem vokB_instrToV (i : V2.Instr) : vokB (instrToV i) = true := by
  cases i
  case block bt body => simp [instrToV, payOkB, famOfOp?, vokB_instrsToV body]
  case loop bt body => simp [instrToV, payOkB, famOfOp?, vokB_instrsToV body]
  case if_ bt b₁ b₂ => simp [instrToV, payOkB, famOfOp?, vokB_instrsToV b₁, vokB_instrsToV b₂]
  case vecIntUnOp s op =>
    simp only [instrToV, vokB_case, vokB_tuple, vokBs_cons, vokB_shapeV, vokB_vecIntUnOpV,
      vokBs_nil, Bool.and_self, Bool.true_and]
    exact payOkB_vunop _ _ (fun _ h => by cases h)
  case vecFloatUnOp s op =>
    simp only [instrToV, vokB_case, vokB_tuple, vokBs_cons, vokB_shapeV, vokB_floatUnOpV,
      vokBs_nil, Bool.and_self, Bool.true_and]
    exact payOkB_vunop _ _ (fun _ _ => by cases op <;> rfl)
  case vecIntBinOp s op =>
    simp only [instrToV, vokB_case, vokB_tuple, vokBs_cons, vokB_shapeV, vokB_vecIntBinOpV,
      vokBs_nil, Bool.and_self, Bool.true_and]
    exact payOkB_vbinop _ _ (fun _ h => by cases h)
  case vecFloatBinOp s op =>
    simp only [instrToV, vokB_case, vokB_tuple, vokBs_cons, vokB_shapeV, vokB_vecFloatBinOpV,
      vokBs_nil, Bool.and_self, Bool.true_and]
    exact payOkB_vbinop _ _ (fun _ _ => by cases op <;> rfl)
  case vecIntRelOp s op =>
    simp only [instrToV, vokB_case, vokB_tuple, vokBs_cons, vokB_shapeV, vokB_vecIntRelOpV,
      vokBs_nil, Bool.and_self, Bool.true_and]
    exact payOkB_vrelop _ _ (fun _ h => by cases h)
  case vecFloatRelOp s op =>
    simp only [instrToV, vokB_case, vokB_tuple, vokBs_cons, vokB_shapeV, vokB_floatRelOpV,
      vokBs_nil, Bool.and_self, Bool.true_and]
    exact payOkB_vrelop _ _ (fun _ _ => by cases op <;> rfl)
  case select ts => cases ts <;> simp [instrToV, payOkB, famOfOp?, vokBs_eq_all]
  case vvBinOp op => cases op <;> simp [instrToV, payOkB, famOfOp?]
  case intLoad t p a => cases p <;> simp [instrToV, payOkB, famOfOp?]
  case intStore t p a => cases p <;> simp [instrToV, payOkB, famOfOp?]
  case vecLoad op a => cases op <;> simp [instrToV, payOkB, famOfOp?]
  case vecExtractLane s sx l => cases sx <;> simp [instrToV, payOkB, famOfOp?]
  all_goals simp [instrToV, payOkB, famOfOp?, vokBs_eq_all]
termination_by sizeOf i

theorem vokB_instrsToV : ∀ l : List V2.Instr, vokBs (instrsToV l) = true
  | [] => rfl
  | i :: l => by simp [instrsToV, vokB_instrToV i, vokB_instrsToV l]
termination_by l => sizeOf l
end

@[simp] theorem vokB_instrsToV' (l : List V2.Instr) : (instrsToV l).all vokB = true := by
  rw [← vokBs_eq_all]; exact vokB_instrsToV l

/-! ## Runtime structure -/

@[simp] theorem vokB_externAddrV (a : ExternAddr) : vokB (externAddrV a) = true := by
  cases a <;> simp [externAddrV, payOkB, famOfOp?]

@[simp] theorem vokB_moduleInstV (m : ModuleInst) : vokB (moduleInstV m) = true := by
  simp [moduleInstV, addrsV, nameV, vokBs_eq_all, payOkB, famOfOp?]

@[simp] theorem vokB_frameV (f : Frame) : vokB (frameV f) = true := by
  simp [frameV, vokBs_eq_all]

mutual
@[simp] theorem vokB_adminToV (a : Admin) : vokB (adminToV a) = true := by
  cases a
  case plain i => exact vokB_instrToV i
  case label n cont body =>
    simp [adminToV, payOkB, famOfOp?, vokB_adminsToV body, vokB_instrsToV cont]
  case frame n f body => simp [adminToV, payOkB, famOfOp?, vokB_adminsToV body]
  all_goals simp [adminToV, payOkB, famOfOp?]

theorem vokB_adminsToV : ∀ l : List Admin, vokBs (adminsToV l) = true
  | [] => rfl
  | a :: l => by simp [adminsToV, vokB_adminToV a, vokB_adminsToV l]
end

theorem vokB_funcInstV {H : Type} (hn : H → String) (fi : FuncInst H) :
    vokB (funcInstV hn fi) = true := by
  rcases fi with ⟨t, m, c⟩
  cases c <;> simp [funcInstV, payOkB, famOfOp?, vokBs_eq_all]

@[simp] theorem vokB_mutV (m : Mutability) : vokB (mutV m) = true := by
  cases m <;> simp [mutV]

@[simp] theorem vokB_optPct (o : Option Nat) : vokB (.opt (o.map pctV)) = true := by
  cases o <;> simp

@[simp] theorem vokB_optPctFin {k : Nat} (o : Option (Fin k)) :
    vokB (.opt (o.map fun m => pctV m.val)) = true := by
  cases o <;> simp

theorem vokB_storeV {H : Type} (hn : H → String) (s : Store H) : vokB (storeV hn s) = true := by
  simp [storeV, vokBs_eq_all, vokB_funcInstV, globalInstV, tableInstV, memInstV, elemInstV,
    dataInstV, bytesV, globalTypeV, tableTypeV, memTypeV, limitsV, payOkB, famOfOp?]

/-- **Every state image is `VOk`.** -/
theorem vOk_stateV {H : Type} (hn : H → String) (s : Store H) (f : Frame) :
    VOk (stateV hn s f) :=
  vOk_of_vokB _ (by simp [stateV, vokB_storeV, payOkB, famOfOp?])

/-- **Every image of administrative code is `VOk`.** -/
theorem vOk_adminsToV (l : List Admin) : VOk (.list (adminsToV l)) :=
  vOk_of_vokB _ (by simpa using vokB_adminsToV l)

/-- Every configuration image is `VOk`. -/
theorem vOk_configV {H : Type} (hn : H → String) (c : Config H) : VOk (configV hn c) :=
  vOk_of_vokB _ (by simp [configV, stateV, vokB_storeV, vokB_adminsToV, payOkB, famOfOp?])

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
