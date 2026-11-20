module

public import Silmaril.Wasm.Execution.MemRep.Sim.Defs
public import Silmaril.Wasm.Execution.MemRep.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.Interp
import Silmaril.Proofs.Wasm.Execution.MemRepSim

/-! Proofs for the interpreter-step part of `Silmaril.Wasm.Execution.MemRep.Sim.Thms`:
every instruction family, the driver `step?`, `stepI` and `runI` commute with `toBytes`. -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Execution.MemRepStep

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded.Exec
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)
open Silmaril.Wasm.Validation (CRefType)

variable {H R : Type} [MemRep R]

/-! ## `toBytes` touches only the memories -/

section Store
variable (s : Store H R)

theorem tags_toBytes : s.toBytes.tags = s.tags := rfl
theorem globals_toBytes : s.toBytes.globals = s.globals := rfl
theorem tables_toBytes : s.toBytes.tables = s.tables := rfl
theorem funcs_toBytes : s.toBytes.funcs = s.funcs := rfl
theorem datas_toBytes : s.toBytes.datas = s.datas := rfl
theorem elems_toBytes : s.toBytes.elems = s.elems := rfl
theorem structs_toBytes : s.toBytes.structs = s.structs := rfl
theorem arrays_toBytes : s.toBytes.arrays = s.arrays := rfl
theorem exns_toBytes : s.toBytes.exns = s.exns := rfl

theorem config_toBytes (f : Frame) (code : List Admin) :
    (Config.toBytes ⟨s, f, code⟩ : Config H) = ⟨s.toBytes, f, code⟩ := rfl

theorem setGlobal_toBytes (a : Nat) (v : Val) :
    (s.setGlobal a v).toBytes = s.toBytes.setGlobal a v := rfl
theorem setTable_toBytes (a : Nat) (ti : TableInst) :
    (s.setTable a ti).toBytes = s.toBytes.setTable a ti := rfl
theorem setElem_toBytes (a : Nat) (refs : List Ref) :
    (s.setElem a refs).toBytes = s.toBytes.setElem a refs := rfl
theorem setStructField_toBytes (a i : Nat) (fv : FieldVal) :
    (s.setStructField a i fv).toBytes = s.toBytes.setStructField a i fv := rfl
theorem setArrayField_toBytes (a i : Nat) (fv : FieldVal) :
    (s.setArrayField a i fv).toBytes = s.toBytes.setArrayField a i fv := rfl
theorem addStruct_toBytes (si : StructInst) : (s.addStruct si).toBytes = s.toBytes.addStruct si :=
  rfl
theorem addArray_toBytes (ai : ArrayInst) : (s.addArray ai).toBytes = s.toBytes.addArray ai := rfl
theorem addExn_toBytes (e : ExnInst) : (s.addExn e).toBytes = s.toBytes.addExn e := rfl

theorem tag?_toBytes (f : Frame) (x : TagIdx) : s.toBytes.tag? f x = s.tag? f x := rfl
theorem global?_toBytes (f : Frame) (x : GlobalIdx) : s.toBytes.global? f x = s.global? f x := rfl
theorem table?_toBytes (f : Frame) (x : TableIdx) : s.toBytes.table? f x = s.table? f x := rfl
theorem elem?_toBytes (f : Frame) (x : ElemIdx) : s.toBytes.elem? f x = s.elem? f x := rfl
theorem data?_toBytes (f : Frame) (x : DataIdx) : s.toBytes.data? f x = s.data? f x := rfl
theorem func?_toBytes (f : Frame) (x : FuncIdx) : s.toBytes.func? f x = s.func? f x := rfl

theorem type?_toBytes (r : Ref) : Ref.type? s.toBytes r = Ref.type? s r := by
  cases r <;> rfl

theorem refOk?_toBytes (r : Ref) (rt : CRefType) : refOk? s.toBytes r rt = refOk? s r rt := by
  induction r generalizing rt with
  | extern r ih => simp only [refOk?, type?_toBytes, ih]
  | _ => simp only [refOk?, type?_toBytes]

end Store

/-- `toBytes` on a head-step result. -/
abbrev tb (p : Nat × Config H R) : Nat × Config H := (p.1, p.2.toBytes)

/-- Push `Option.map tb` through binds, `if`s and `match`es of a head-step function whose store
reads are not of memory bytes, and close each leaf. -/
local macro "nat_close" : tactic => `(tactic| (
  try simp only [Option.bind_eq_bind, Option.pure_def, Option.map_bind, Option.map_map, Function.comp_def,
    Option.map_some, Option.map_none, tb, config_toBytes, tag?_toBytes, global?_toBytes,
    table?_toBytes, elem?_toBytes, data?_toBytes, func?_toBytes, tags_toBytes, globals_toBytes,
    tables_toBytes, funcs_toBytes, datas_toBytes, elems_toBytes, structs_toBytes,
    arrays_toBytes, exns_toBytes, setGlobal_toBytes, setTable_toBytes, setElem_toBytes,
    setStructField_toBytes, setArrayField_toBytes, addStruct_toBytes, addArray_toBytes,
    addExn_toBytes, refOk?_toBytes, type?_toBytes]
  repeat' (first
    | refine congrArg (Option.bind _) (funext fun _ => ?_)
    | refine congrArg (fun g => Option.map g _) (funext fun _ => ?_)
    | split)
  all_goals first | rfl | (simp_all; done) | (simp_all; rfl)))

/-! ## The non-memory families -/

section Families
variable (o : GrowOracle) (s : Store H R) (f : Frame) (vs : List Val) (e : Admin)

theorem parametricStep?_toBytes :
    (parametricStep? o s f vs e).map tb = parametricStep? o s.toBytes f vs e := by
  unfold parametricStep?; split <;> nat_close

theorem numericStep?_toBytes :
    (numericStep? o s f vs e).map tb = numericStep? o s.toBytes f vs e := by
  unfold numericStep?; split <;> nat_close

theorem vectorStep?_toBytes :
    (vectorStep? o s f vs e).map tb = vectorStep? o s.toBytes f vs e := by
  unfold vectorStep?; split
  · rw [Option.map_map]; rfl
  · rfl

theorem variableStep?_toBytes :
    (variableStep? o s f vs e).map tb = variableStep? o s.toBytes f vs e := by
  unfold variableStep?; split <;> nat_close

theorem tableStep?_toBytes :
    (tableStep? o s f vs e).map tb = tableStep? o s.toBytes f vs e := by
  unfold tableStep?; split
  · unfold VarTab.tableGet?; nat_close
  · unfold VarTab.tableSet?; nat_close
  · unfold VarTab.tableSize?; nat_close
  · unfold VarTab.tableGrow?; nat_close
  · unfold VarTab.tableFill?; nat_close
  · unfold VarTab.tableCopy?; nat_close
  · unfold VarTab.tableInit?; nat_close
  · unfold VarTab.elemDrop?; nat_close
  · rfl

theorem referenceStep?_toBytes :
    (referenceStep? o s f vs e).map tb = referenceStep? o s.toBytes f vs e := by
  unfold referenceStep? refStepRev?; nat_close

theorem aggNewStep?_toBytes :
    (aggNewStep? o s f vs e).map tb = aggNewStep? o s.toBytes f vs e := by
  unfold aggNewStep?; split
  · unfold AggNew.structNew?; nat_close
  · unfold AggNew.structNewDefault?; nat_close
  · unfold AggNew.arrayNew?; nat_close
  · unfold AggNew.arrayNewDefault?; nat_close
  · unfold AggNew.arrayNewFixed?; nat_close
  · unfold AggNew.arrayNewElem?; nat_close
  · unfold AggNew.arrayNewData?; nat_close
  · rfl

theorem oobA_toBytes (a b : Nat) : AggAcc.oobA s.toBytes a b = AggAcc.oobA s a b := rfl
theorem oobE_toBytes (y : ElemIdx) (b : Nat) : AggAcc.oobE s.toBytes f y b = AggAcc.oobE s f y b :=
  rfl
theorem oobD_toBytes (x : TypeIdx) (y : DataIdx) (j n : Nat) :
    AggAcc.oobD s.toBytes f x y j n = AggAcc.oobD s f x y j n := rfl

theorem aggAccessStep?_toBytes :
    (aggAccessStep? o s f vs e).map tb = aggAccessStep? o s.toBytes f vs e := by
  unfold aggAccessStep?; split
  · unfold AggAcc.structGet; nat_close
  · unfold AggAcc.structSet; nat_close
  · unfold AggAcc.arrayGet; nat_close
  · unfold AggAcc.arraySet; nat_close
  · unfold AggAcc.arrayLen; nat_close
  · unfold AggAcc.arrayFill AggAcc.fillArr; nat_close
  · unfold AggAcc.arrayCopy AggAcc.copyArr; simp only [oobA_toBytes]; nat_close
  · unfold AggAcc.arrayInitElem AggAcc.initElemArr; simp only [oobA_toBytes, oobE_toBytes]
    nat_close
  · unfold AggAcc.arrayInitData AggAcc.initDataArr; simp only [oobA_toBytes, oobD_toBytes]
    nat_close
  · rfl

theorem controlStep?_toBytes :
    (controlStep? refOk? o s f vs e).map tb = controlStep? refOk? o s.toBytes f vs e := by
  unfold controlStep?; split
  · unfold Ctl.callRef?; nat_close
  · split
    · rename_i i _
      cases i <;> simp only [Ctl.plainStep?] <;> (try unfold Ctl.block?) <;> nat_close
    · rfl

theorem catchStep_toBytes (a : Nat) (c : Catch) :
    Adm.catchStep s.toBytes f a c = Adm.catchStep s f a c := by
  cases c <;> rfl

theorem adminStep?_toBytes :
    (adminStep? o s f vs e).map tb = adminStep? o s.toBytes f vs e := by
  unfold adminStep?; split
  · unfold Adm.labelStep Adm.labelAt; rw [Option.map_map]; nat_close
  · unfold Adm.handlerStep Adm.handlerAt Adm.throwHandler
    rw [Option.map_map]; simp only [catchStep_toBytes]; nat_close
  · unfold Adm.frameStep Adm.frameAt Adm.frameRCR; rw [Option.map_map]; nat_close
  · rfl

end Families

/-! ## The head step, the driver and the run loop -/

theorem orElse_map {α β : Type} (g : α → β) (a b : Option α) :
    (a <|> b).map g = (a.map g <|> b.map g) := by
  cases a <;> rfl

variable [LawfulMemRep R]

theorem interpHead_toBytes (o : GrowOracle) (s : Store H R) (f : Frame) (vs : List Val)
    (e : Admin) : (interpHead o s f vs e).map tb = interpHead o s.toBytes f vs e := by
  unfold interpHead; split
  · exact parametricStep?_toBytes ..
  · exact numericStep?_toBytes ..
  · exact vectorStep?_toBytes ..
  · exact variableStep?_toBytes ..
  · exact tableStep?_toBytes ..
  · exact MemRepSim.memoryStep?_toBytes ..
  · exact referenceStep?_toBytes ..
  · rw [orElse_map, aggNewStep?_toBytes, aggAccessStep?_toBytes]
  · rw [orElse_map, controlStep?_toBytes, adminStep?_toBytes]

omit [LawfulMemRep R] in
/-- The driver commutes with `toBytes` whenever its head step does. -/
theorem step?_toBytes (head : HeadFn H R) (head' : HeadFn H)
    (hh : ∀ s f vs e, (head s f vs e).map tb = head' s.toBytes f vs e) :
    ∀ (n : Nat) (c : Config H R), sizeOf c.code = n →
      (step? head c).map Config.toBytes = step? head' c.toBytes := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨s, f, code⟩ rfl
  rcases hsp : splitVals code with ⟨vs, _ | ⟨e, rest⟩⟩
  · rw [step?_nil (c := ⟨s, f, code⟩) hsp, step?_nil (c := Config.toBytes ⟨s, f, code⟩) hsp]
    rfl
  · rw [step?_cons (c := ⟨s, f, code⟩) hsp, step?_cons (c := Config.toBytes ⟨s, f, code⟩) hsp]
    have hlt := Drv.sizeOf_lt_of_split hsp
    simp only [Config.toBytes]
    unfold Drv.layer
    split
    · split <;> rfl
    · split
      · split <;> rfl
      · rw [← hh]
        cases head s f vs e with
        | some p => rfl
        | none =>
          simp only [Option.map_none]
          cases e with
          | label n' cont is =>
            have := ih (sizeOf is) (by simp at hlt ⊢; omega) ⟨s, f, is⟩ rfl
            dsimp only
            rw [show (⟨s.toBytes, _, is⟩ : Config H) = Config.toBytes ⟨s, _, is⟩ from rfl, ← this,
              Option.map_map, Option.map_map]
            rfl
          | handler n' cs is =>
            have := ih (sizeOf is) (by simp at hlt ⊢; omega) ⟨s, f, is⟩ rfl
            dsimp only
            rw [show (⟨s.toBytes, _, is⟩ : Config H) = Config.toBytes ⟨s, _, is⟩ from rfl, ← this,
              Option.map_map, Option.map_map]
            rfl
          | frame n' fi is =>
            have := ih (sizeOf is) (by simp at hlt ⊢; omega) ⟨s, fi, is⟩ rfl
            dsimp only
            rw [show (⟨s.toBytes, _, is⟩ : Config H) = Config.toBytes ⟨s, _, is⟩ from rfl, ← this,
              Option.map_map, Option.map_map]
            rfl
          | _ => rfl

theorem stepI_toBytes (o : GrowOracle) (c : Config H R) :
    (stepI o c).map Config.toBytes = stepI o c.toBytes :=
  step?_toBytes (interpHead o) (interpHead o) (interpHead_toBytes o) _ c rfl

theorem runI_toBytes (o : GrowOracle) :
    ∀ (n : Nat) (c : Config H R),
      Prod.map Config.toBytes id (runI o n c) = runI o n c.toBytes
  | 0, _ => rfl
  | n + 1, c => by
    have h := stepI_toBytes o c
    cases hs : step? (interpHead o) c with
    | none =>
      have h' : step? (interpHead o) c.toBytes = none := by
        change stepI o c.toBytes = _; rw [← h]; simp [stepI, hs]
      show Prod.map _ _ (run? _ _ _) = run? _ _ _
      rw [run?_succ_none hs, run?_succ_none h']; rfl
    | some d =>
      have h' : step? (interpHead o) c.toBytes = some d.toBytes := by
        change stepI o c.toBytes = _; rw [← h]; simp [stepI, hs]
      show Prod.map _ _ (run? _ _ _) = run? _ _ _
      rw [run?_succ_some hs, run?_succ_some h']
      exact runI_toBytes o n d

/-! ## Threads, status and the fuelled runner -/

omit [LawfulMemRep R] in
theorem config_toBytes_thread (s : Store H R) (t : Thread) :
    (t.config s).toBytes = t.config s.toBytes := by
  cases t <;> rfl

omit [LawfulMemRep R] in
theorem decompose?_toBytes (s : Store H R) :
    ∀ (n : Nat) (code : List Admin), sizeOf code = n →
      decompose? s.toBytes code = decompose? s code := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro code hn
  have hlt : ∀ {vs : List Val} {c : Admin} {rest : List Admin}, splitVals code = (vs, c :: rest) →
      sizeOf c < n := by
    intro vs c rest h
    have := splitVals_snd_sizeOf code
    rw [h] at this; simp only [List.cons.sizeOf_spec] at this; omega
  unfold decompose?
  split
  · rename_i hs; have := hlt hs; simp only [Admin.label.sizeOf_spec] at this
    rw [ih _ (by omega) _ rfl]
  · rename_i hs; have := hlt hs; simp only [Admin.handler.sizeOf_spec] at this
    rw [ih _ (by omega) _ rfl]
  · rename_i hs; have := hlt hs; simp only [Admin.frame.sizeOf_spec] at this
    rw [ih _ (by omega) _ rfl]
  · rfl
  · rfl

theorem statusC_toBytes (o : GrowOracle) (s : Store H R) (t : Thread) :
    statusC (stepI o) s.toBytes t = statusC (stepI o) s t := by
  unfold statusC
  dsimp only
  rw [← config_toBytes_thread, decompose?_toBytes s _ _ rfl, ← stepI_toBytes, Option.isSome_map]
  rfl

theorem internalC_toBytes (o : GrowOracle) (s : Store H R) (t : Thread) :
    (internalC (stepI o) (s, t)).map (fun p => (p.1.toBytes, p.2)) =
      internalC (stepI o) (s.toBytes, t) := by
  unfold internalC
  rw [← config_toBytes_thread, ← stepI_toBytes, Option.map_map, Option.map_map]
  rfl

theorem runC_toBytes (o : GrowOracle) :
    ∀ (n : Nat) (s : Store H R) (t : Thread),
      (fun r => (r.1.toBytes, r.2)) (runC (stepI o) n s t) = runC (stepI o) n s.toBytes t
  | 0, _, _ => rfl
  | n + 1, s, t => by
    have hi := internalC_toBytes o s t
    simp only [runC, statusC_toBytes]
    split
    · cases h : internalC (stepI o) (s, t) with
      | none => rw [h] at hi; simp only [Option.map_none] at hi; rw [← hi]
      | some p =>
        rw [h] at hi; simp only [Option.map_some] at hi; rw [← hi]
        exact runC_toBytes o n p.1 p.2
    · rfl

omit [LawfulMemRep R] in
theorem resume_toBytes (s : Store H R) (t : Thread) (r : CallResult) :
    resume s.toBytes t r = resume s t r := by
  unfold resume
  dsimp only
  rw [← config_toBytes_thread, decompose?_toBytes s _ _ rfl]
  rfl

end Silmaril.Proofs.Wasm.Execution.MemRepStep
