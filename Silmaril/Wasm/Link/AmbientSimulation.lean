module

public import Silmaril.Wasm.Link.SimulationDefs

/-! # Ambient memory, table and exception simulation

Unchanged module views observe identical table, memory, segment and exception
data, while stored function definitions may carry static relocation. These
rules transport the actual reductions and retain the store relation.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.AmbientSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open AdminRelation

variable {H : Type} {P : Profile} {host : HostSemantics H}

private theorem table_lookup {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    {x : TableIdx} {a : Nat} {ti : TableInst} (h : source.table? left x = some (a,ti)) :
    target.table? right x = some (a,ti) := by
  simpa only [Store.table?,← modules,← stores.tables] using h

private theorem elem_lookup {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    {x : ElemIdx} {a : Nat} {ei : ElemInst} (h : source.elem? left x = some (a,ei)) :
    target.elem? right x = some (a,ei) := by
  simpa only [Store.elem?,← modules,← stores.elems] using h

private theorem mem_lookup {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    {x : MemIdx} {a : Nat} {mi : MemInst} (h : source.mem? left x = some (a,mi)) :
    target.mem? right x = some (a,mi) := by
  simpa only [Store.mem?,← modules,← stores.mems] using h

private theorem data_lookup {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    {x : DataIdx} {a : Nat} {di : DataInst} (h : source.data? left x = some (a,di)) :
    target.data? right x = some (a,di) := by
  simpa only [Store.data?,← modules,← stores.datas] using h

/-- Every table and element-segment reduction transports with the same
operands, result values, profile policy and exact matching store mutation. -/
theorem table_same {source target source' : Store H} {left right left' : Frame} {code out : List Admin}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    (h : TableStep P ⟨source,left,code⟩ ⟨source',left',out⟩) :
    ∃ target', TableStep P ⟨target,right,code⟩ ⟨target',right,out⟩ ∧
      StoreRelation.Related source' target' ∧ left' = left := by
  cases h with
  | getOob ht h => exact ⟨target,.getOob (table_lookup stores modules ht) h,stores,rfl⟩
  | getVal ht h => exact ⟨target,.getVal (table_lookup stores modules ht) h,stores,rfl⟩
  | setOob ht h => exact ⟨target,.setOob (table_lookup stores modules ht) h,stores,rfl⟩
  | setVal ht h => exact ⟨_,.setVal (table_lookup stores modules ht) h,stores.setTable _ _,rfl⟩
  | size ht => exact ⟨target,.size (table_lookup stores modules ht),stores,rfl⟩
  | growSucceed ht hg hp => exact ⟨_,.growSucceed (table_lookup stores modules ht) hg hp,stores.setTable _ _,rfl⟩
  | growFail ht hp => exact ⟨target,.growFail (table_lookup stores modules ht) hp,stores,rfl⟩
  | fillOob ht h => exact ⟨target,.fillOob (table_lookup stores modules ht) h,stores,rfl⟩
  | fillZero ht h => exact ⟨target,.fillZero (table_lookup stores modules ht) h,stores,rfl⟩
  | fillSucc ht h hn => exact ⟨target,.fillSucc (table_lookup stores modules ht) h hn,stores,rfl⟩
  | copyOob h₁ h₂ h => exact ⟨target,.copyOob (table_lookup stores modules h₁) (table_lookup stores modules h₂) h,stores,rfl⟩
  | copyZero h₁ h₂ h => exact ⟨target,.copyZero (table_lookup stores modules h₁) (table_lookup stores modules h₂) h,stores,rfl⟩
  | copyLe h₁ h₂ h hn hle => exact ⟨target,.copyLe (table_lookup stores modules h₁) (table_lookup stores modules h₂) h hn hle,stores,rfl⟩
  | copyGt h₁ h₂ h hn hgt => exact ⟨target,.copyGt (table_lookup stores modules h₁) (table_lookup stores modules h₂) h hn hgt,stores,rfl⟩
  | initOob ht he h => exact ⟨target,.initOob (table_lookup stores modules ht) (elem_lookup stores modules he) h,stores,rfl⟩
  | initZero ht he h => exact ⟨target,.initZero (table_lookup stores modules ht) (elem_lookup stores modules he) h,stores,rfl⟩
  | initSucc ht he h hn hr => exact ⟨target,.initSucc (table_lookup stores modules ht) (elem_lookup stores modules he) h hn hr,stores,rfl⟩
  | elemDrop he => exact ⟨_,.elemDrop (elem_lookup stores modules he),stores.setElem _ [],rfl⟩

/-- Integer, float and vector loads/stores, growth, bulk-memory expansion and
data drop transport across the exact memory and data-segment store fields. -/
theorem memory_same {source target source' : Store H} {left right left' : Frame} {code out : List Admin}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    (h : MemoryStep P ⟨source,left,code⟩ ⟨source',left',out⟩) :
    ∃ target', MemoryStep P ⟨target,right,code⟩ ⟨target',right,out⟩ ∧
      StoreRelation.Related source' target' ∧ left' = left := by
  cases h with
  | loadIntOob hm h => exact ⟨target,.loadIntOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | loadIntVal hm hl => exact ⟨target,.loadIntVal (mem_lookup stores modules hm) hl,stores,rfl⟩
  | loadPackOob hm h => exact ⟨target,.loadPackOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | loadPackVal hm hl => exact ⟨target,.loadPackVal (mem_lookup stores modules hm) hl,stores,rfl⟩
  | loadFloatOob hm h => exact ⟨target,.loadFloatOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | loadFloatVal hm hl => exact ⟨target,.loadFloatVal (mem_lookup stores modules hm) hl,stores,rfl⟩
  | vecLoadOob hm h => exact ⟨target,.vecLoadOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | vecLoadVal hm hl => exact ⟨target,.vecLoadVal (mem_lookup stores modules hm) hl,stores,rfl⟩
  | vecLoadLaneOob hm h => exact ⟨target,.vecLoadLaneOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | vecLoadLaneVal hm hl => exact ⟨target,.vecLoadLaneVal (mem_lookup stores modules hm) hl,stores,rfl⟩
  | storeIntOob hm h => exact ⟨target,.storeIntOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | storeIntVal hm hs => exact ⟨_,.storeIntVal (mem_lookup stores modules hm) hs,stores.setMem _ _,rfl⟩
  | storePackOob hm h => exact ⟨target,.storePackOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | storePackVal hm hs => exact ⟨_,.storePackVal (mem_lookup stores modules hm) hs,stores.setMem _ _,rfl⟩
  | storeFloatOob hm h => exact ⟨target,.storeFloatOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | storeFloatVal hm hs => exact ⟨_,.storeFloatVal (mem_lookup stores modules hm) hs,stores.setMem _ _,rfl⟩
  | vecStoreOob hm h => exact ⟨target,.vecStoreOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | vecStoreVal hm hs => exact ⟨_,.vecStoreVal (mem_lookup stores modules hm) hs,stores.setMem _ _,rfl⟩
  | vecStoreLaneOob hm h => exact ⟨target,.vecStoreLaneOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | vecStoreLaneVal hm hs => exact ⟨_,.vecStoreLaneVal (mem_lookup stores modules hm) hs,stores.setMem _ _,rfl⟩
  | size hm => exact ⟨target,.size (mem_lookup stores modules hm),stores,rfl⟩
  | growSucceed hm hg hp => exact ⟨_,.growSucceed (mem_lookup stores modules hm) hg hp,stores.setMem _ _,rfl⟩
  | growFail hm hp => exact ⟨target,.growFail (mem_lookup stores modules hm) hp,stores,rfl⟩
  | fillOob hm h => exact ⟨target,.fillOob (mem_lookup stores modules hm) h,stores,rfl⟩
  | fillZero hm h => exact ⟨target,.fillZero (mem_lookup stores modules hm) h,stores,rfl⟩
  | fillSucc hm h hn => exact ⟨target,.fillSucc (mem_lookup stores modules hm) h hn,stores,rfl⟩
  | copyOob h₁ h₂ h => exact ⟨target,.copyOob (mem_lookup stores modules h₁) (mem_lookup stores modules h₂) h,stores,rfl⟩
  | copyZero h₁ h₂ h => exact ⟨target,.copyZero (mem_lookup stores modules h₁) (mem_lookup stores modules h₂) h,stores,rfl⟩
  | copyLe h₁ h₂ h hn hle => exact ⟨target,.copyLe (mem_lookup stores modules h₁) (mem_lookup stores modules h₂) h hn hle,stores,rfl⟩
  | copyGt h₁ h₂ h hn hgt => exact ⟨target,.copyGt (mem_lookup stores modules h₁) (mem_lookup stores modules h₂) h hn hgt,stores,rfl⟩
  | initOob hm hd h => exact ⟨target,.initOob (mem_lookup stores modules hm) (data_lookup stores modules hd) h,stores,rfl⟩
  | initZero hm hd h => exact ⟨target,.initZero (mem_lookup stores modules hm) (data_lookup stores modules hd) h,stores,rfl⟩
  | initSucc hm hd h hn hb => exact ⟨target,.initSucc (mem_lookup stores modules hm) (data_lookup stores modules hd) h hn hb,stores,rfl⟩
  | dataDrop hd => exact ⟨_,.dataDrop (data_lookup stores modules hd),stores.setData _ _,rfl⟩

private def FlatAdmin : Admin → Prop
  | .label _ _ _ | .handler _ _ _ | .frame _ _ _ => False
  | _ => True

private def Flat (xs : List Admin) : Prop := ∀ a ∈ xs, FlatAdmin a

@[simp] private theorem flat_val (v : Val) : FlatAdmin v.toAdmin := by
  cases v with
  | num v => rcases v with ⟨⟨t⟩ | ⟨t⟩,b⟩ <;> trivial
  | vec b => trivial
  | ref r => trivial

private theorem same_flat {source target : ModuleInst} {xs ys : List Admin}
    (h : Control .same source target xs ys) (flat : Flat xs) : ys = xs := by
  generalize hm : Mode.same = mode at h
  induction h <;> subst_vars <;> simp_all [Flat,FlatAdmin]

@[simp] private theorem flat_plain (i : Instr) : FlatAdmin (.plain i) := trivial

@[simp] private theorem flat_ref (r : Ref) : FlatAdmin (.ref r) := trivial

private theorem table_flat {c c' : Config H} (h : TableStep P c c') : Flat c.code := by
  cases h <;> simp [Flat,aconst,constI32]

private theorem memory_flat {c c' : Config H} (h : MemoryStep P c c') : Flat c.code := by
  cases h <;> simp [Flat,aconst,constI32]

private theorem view_same_modules {left right : ModuleInst} (h : View .same left right) :
    left = right := by cases h; rfl

private theorem same_modules {left right : Frame} (h : Frames .same left right) :
    left.module = right.module := view_same_modules h.view

/-- Related unchanged callers execute every table-family step with related
final stores, frames and complete administrative output. -/
theorem table_unchanged {source sourceFinal target : Config H}
    (h : TableStep P source sourceFinal) (matching : Simulation.Matching .same source target) :
    ∃ targetFinal, Step P host target targetFinal ∧ Simulation.Matching .same sourceFinal targetFinal := by
  cases source with | mk s f xs =>
    cases sourceFinal with | mk s' f' out =>
      cases target with | mk t g ys =>
        have he := same_flat matching.code (table_flat h)
        change ys = xs at he
        subst ys
        obtain ⟨t',ht,stores,rfl⟩ := table_same matching.stores (same_modules matching.frames) h
        exact ⟨⟨t',g,out⟩,.table ht,⟨stores,matching.frames,by
          rw [← same_modules matching.frames]; exact Control.same _ _⟩⟩

/-- Related unchanged callers execute every memory-family step, including
bulk expansion and data drop, with the complete final relation preserved. -/
theorem memory_unchanged {source sourceFinal target : Config H}
    (h : MemoryStep P source sourceFinal) (matching : Simulation.Matching .same source target) :
    ∃ targetFinal, Step P host target targetFinal ∧ Simulation.Matching .same sourceFinal targetFinal := by
  cases source with | mk s f xs =>
    cases sourceFinal with | mk s' f' out =>
      cases target with | mk t g ys =>
        have he := same_flat matching.code (memory_flat h)
        change ys = xs at he
        subst ys
        obtain ⟨t',ht,stores,rfl⟩ := memory_same matching.stores (same_modules matching.frames) h
        exact ⟨⟨t',g,out⟩,.memory ht,⟨stores,matching.frames,by
          rw [← same_modules matching.frames]; exact Control.same _ _⟩⟩

private def RejectedLast (xs : List Admin) : Prop :=
  ∃ i, xs.getLast? = some (.plain i) ∧ (Admin.plain i).val? = none ∧ i ≠ .throwRef ∧
    ∀ r, instruction? r i = none

private theorem rejected_last_same {mode : Mode} {left right : ModuleInst} {xs ys : List Admin}
    (h : Control mode left right xs ys) (rejected : RejectedLast xs) : mode = .same := by
  obtain ⟨i,last,nonvalue,nonthrow,reject⟩ := rejected
  obtain ⟨pre,rfl⟩ := List.getLast?_eq_some_iff.mp last
  obtain ⟨pre',tail,shape,hpre,htail⟩ := h.split
  obtain ⟨j,rest,shape,rewrite,empty⟩ := htail.plain_cons nonvalue nonthrow
  cases mode with
  | same => rfl
  | relocated r =>
    change instruction? r i = some j at rewrite
    rw [reject r] at rewrite
    cases rewrite

private theorem table_rejected_last {c c' : Config H} (h : TableStep P c c') : RejectedLast c.code := by
  cases h <;> refine ⟨_,rfl,rfl,?_,?_⟩
  all_goals first | solve | intro he; cases he
                  | intro r; simp only [instruction?]

private theorem memory_rejected_last {c c' : Config H} (h : MemoryStep P c c') : RejectedLast c.code := by
  cases h <;> refine ⟨_,rfl,rfl,?_,?_⟩
  all_goals first | solve | intro he; cases he
                  | intro r; simp only [instruction?]

/-- Table instructions are excluded by relocated source code. The generic
configuration relation therefore reduces a table step to its ambient mode. -/
theorem table {mode : Mode} {source sourceFinal target : Config H}
    (h : TableStep P source sourceFinal) (matching : Simulation.Matching mode source target) :
    ∃ targetFinal, Step P host target targetFinal ∧ Simulation.Matching mode sourceFinal targetFinal := by
  have hm := rejected_last_same matching.code (table_rejected_last h)
  subst mode
  exact table_unchanged h matching

/-- Every memory-family input is likewise rejected by source relocation,
while its unchanged ambient execution retains the complete relation. -/
theorem memory {mode : Mode} {source sourceFinal target : Config H}
    (h : MemoryStep P source sourceFinal) (matching : Simulation.Matching mode source target) :
    ∃ targetFinal, Step P host target targetFinal ∧ Simulation.Matching mode sourceFinal targetFinal := by
  have hm := rejected_last_same matching.code (memory_rejected_last h)
  subst mode
  exact memory_unchanged h matching

theorem table_step {mode : Mode} {source sourceFinal target : Config H}
    (h : TableStep P source sourceFinal) (matching : Simulation.Matching mode source target) :
    ∃ targetFinal, Step P host target targetFinal ∧ Simulation.Matching mode sourceFinal targetFinal :=
  table h matching

theorem memory_step {mode : Mode} {source sourceFinal target : Config H}
    (h : MemoryStep P source sourceFinal) (matching : Simulation.Matching mode source target) :
    ∃ targetFinal, Step P host target targetFinal ∧ Simulation.Matching mode sourceFinal targetFinal :=
  memory h matching

/-- The exception constructors of the actual core step relation. Witnesses
classify the reduction rule without assuming any target execution. -/
inductive IsException : {c c' : Config H} → Step P host c c' → Prop where
  | throw {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat} {ti : TagInst}
      {ts : Ty (.list .val)} (ht : s.tag? f x = some (ta,ti)) (he : Expand ti.type (.func ts .nil))
      (hn : vs.length = ts.length) : IsException (.throw (P := P) (host := host) ht he hn)
  | throwRefNull {s : Store H} {f : Frame} :
      IsException (.throwRefNull (P := P) (host := host) (s := s) (f := f))
  | throwRefInstrs {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {rest : List Admin}
      (hne : vs ≠ [] ∨ rest ≠ []) : IsException (.throwRefInstrs (P := P) (host := host) (s := s) (f := f) (a := a) hne)
  | throwRefLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat} :
      IsException (.throwRefLabel (P := P) (host := host) (s := s) (f := f) (n := n) (cont := cont) (a := a))
  | throwRefFrame {s : Store H} {f fi : Frame} {n : Nat} {a : Nat} :
      IsException (.throwRefFrame (P := P) (host := host) (s := s) (f := f) (fi := fi) (n := n) (a := a))
  | throwRefHandlerEmpty {s : Store H} {f : Frame} {n : Nat} {a : Nat} :
      IsException (.throwRefHandlerEmpty (P := P) (host := host) (s := s) (f := f) (n := n) (a := a))
  | throwRefHandlerCatch {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      IsException (.throwRefHandlerCatch (P := P) (host := host) (n := n) (l := l) (cs := cs) he ht)
  | throwRefHandlerCatchRef {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      IsException (.throwRefHandlerCatchRef (P := P) (host := host) (n := n) (l := l) (cs := cs) he ht)
  | throwRefHandlerCatchAll {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch} {a : Nat} :
      IsException (.throwRefHandlerCatchAll (P := P) (host := host) (s := s) (f := f) (n := n) (l := l) (cs := cs) (a := a))
  | throwRefHandlerCatchAllRef {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch} {a : Nat} :
      IsException (.throwRefHandlerCatchAllRef (P := P) (host := host) (s := s) (f := f) (n := n) (l := l) (cs := cs) (a := a))
  | throwRefHandlerNext {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch} {a : Nat}
      (h : ¬ CatchMatches s f a c) :
      IsException (.throwRefHandlerNext (P := P) (host := host) (n := n) (cs := cs) h)
  | tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
      {vs : List Val} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁,t₂))
      (hm : vs.length = t₁.length) : IsException (.tryTable (P := P) (host := host) (s := s) (cs := cs) (body := body) hbt hm)
  | handlerVals {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val} :
      IsException (.handlerVals (P := P) (host := host) (s := s) (f := f) (n := n) (cs := cs) (vs := vs))

private theorem throwing_related (mode : Mode) (left right : ModuleInst) (a : Nat) :
    Control mode left right (throwing a) (throwing a) := .ref (.throwRef .nil)

private theorem static_exception_code {mode : Mode} {left right : ModuleInst}
    {vs : List Val} {i : Instr} {ys : List Admin}
    (h : Control mode left right (vals vs ++ [.plain i]) ys)
    (nonvalue : (Admin.plain i).val? = none) (nonthrow : i ≠ .throwRef)
    (reject : ∀ r, instruction? r i = none) : mode = .same ∧ ys = vals vs ++ [.plain i] := by
  obtain ⟨j,shape,rewrite⟩ := h.values_instruction nonvalue nonthrow
  cases mode with
  | same =>
    change i = j at rewrite
    subst j
    exact ⟨rfl,shape⟩
  | relocated r =>
    change instruction? r i = some j at rewrite
    rw [reject r] at rewrite
    cases rewrite

private theorem handler_throwing_input {mode : Mode} {left right : ModuleInst}
    {n : Nat} {cs : List Catch} {a : Nat} {ys : List Admin}
    (h : Control mode left right [.handler n cs (throwing a)] ys) :
    mode = .same ∧ ys = [.handler n cs (throwing a)] := by
  obtain ⟨hm,modules,body,rest,shape,inner,empty⟩ := h.handler_cons
  rw [empty.nil_left,inner.throwing_left] at shape
  exact ⟨hm,shape⟩

private theorem tag_lookup {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    {x : TagIdx} {a : Nat} {ti : TagInst} (h : source.tag? left x = some (a,ti)) :
    target.tag? right x = some (a,ti) := by
  simpa only [Store.tag?,← modules,← stores.tags] using h

private theorem catch_matches {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    (a : Nat) (c : Catch) : CatchMatches source left a c ↔ CatchMatches target right a c := by
  cases c <;> simp only [CatchMatches,stores.exns,modules]

/-- The exception rules preserve matching configurations. Runtime `throwRef`
propagation can leave an ambient callee for a relocated caller; the resulting
exception address and structural throw marker remain identical. -/
theorem step {mode : Mode} {source sourceFinal target : Config H}
    (sourceStep : Step P host source sourceFinal) (accepted : IsException sourceStep)
    (matching : Simulation.Matching mode source target) :
    ∃ targetFinal, Step P host target targetFinal ∧ Simulation.Matching mode sourceFinal targetFinal := by
  cases target with | mk t g ys =>
    cases accepted with
    | @throw s f x vs ta ti ts ht he hn =>
      obtain ⟨hm,shape⟩ := static_exception_code matching.code rfl (by intro h; cases h) (by intro r; simp only [instruction?])
      subst mode
      change ys = vals vs ++ [.plain (.throw x)] at shape
      subst ys
      refine ⟨⟨t.addExn ⟨ta,vs⟩,g,throwing t.exns.length⟩,
        .throw (tag_lookup matching.stores (same_modules matching.frames) ht) he hn,
        ⟨matching.stores.addExn _,matching.frames,?_⟩⟩
      rw [matching.stores.exns]
      exact throwing_related _ _ _ _
    | @throwRefNull s f =>
      obtain ⟨rest,shape,hr⟩ := matching.code.ref_cons
      obtain ⟨tail,rfl,empty⟩ := hr.throwRef_cons
      rw [empty.nil_left] at shape
      change ys = [.ref .null,.plain .throwRef] at shape
      subst ys
      exact ⟨⟨t,g,[.trap]⟩,.throwRefNull,⟨matching.stores,matching.frames,.trap .nil⟩⟩
    | @throwRefInstrs s f vs a rest hne =>
      have input : Control mode f.module g.module (vals vs ++ (throwing a ++ rest)) ys := by
        simpa only [List.append_assoc] using matching.code
      obtain ⟨suffix,shape,hr⟩ := input.values_prefix
      change Control mode f.module g.module (.ref (.exn a) :: .plain .throwRef :: rest) suffix at hr
      obtain ⟨tail,refShape,afterRef⟩ := hr.ref_cons
      subst suffix
      obtain ⟨rest',throwShape,afterThrow⟩ := afterRef.throwRef_cons
      subst tail
      change ys = vals vs ++ (throwing a ++ rest') at shape
      subst ys
      have hne' : vs ≠ [] ∨ rest' ≠ [] := by
        rcases hne with hvs | hrest
        · exact .inl hvs
        · exact .inr (by intro he; subst rest'; have := afterThrow.length_eq; simp only [List.length_nil] at this; exact hrest (List.length_eq_zero_iff.mp this))
      exact ⟨⟨t,g,throwing a⟩,by simpa only [List.append_assoc] using Step.throwRefInstrs hne',
        ⟨matching.stores,matching.frames,throwing_related _ _ _ _⟩⟩
    | @throwRefLabel s f n cont a =>
      obtain ⟨cont',body',shape,hcont,inner⟩ := matching.code.label_singleton
      rw [inner.throwing_left] at shape
      change ys = [.label n cont' (throwing a)] at shape
      subst ys
      exact ⟨⟨t,g,throwing a⟩,.throwRefLabel,⟨matching.stores,matching.frames,throwing_related _ _ _ _⟩⟩
    | @throwRefFrame s f fi n a =>
      obtain ⟨innerMode,fi',body',shape,frames,inner⟩ := matching.code.frame_singleton
      rw [inner.throwing_left] at shape
      change ys = [.frame n fi' (throwing a)] at shape
      subst ys
      exact ⟨⟨t,g,throwing a⟩,.throwRefFrame,⟨matching.stores,matching.frames,throwing_related _ _ _ _⟩⟩
    | @throwRefHandlerEmpty s f n a =>
      obtain ⟨hm,shape⟩ := handler_throwing_input matching.code
      subst mode
      change ys = [.handler n [] (throwing a)] at shape
      subst ys
      exact ⟨⟨t,g,throwing a⟩,.throwRefHandlerEmpty,⟨matching.stores,matching.frames,throwing_related _ _ _ _⟩⟩
    | @throwRefHandlerCatch s f n x l cs a e he ht =>
      obtain ⟨hm,shape⟩ := handler_throwing_input matching.code
      subst mode
      change ys = [.handler n (.catch_ x l :: cs) (throwing a)] at shape
      subst ys
      refine ⟨⟨t,g,vals e.fields ++ [.plain (.br l)]⟩,
        .throwRefHandlerCatch (matching.stores.exns ▸ he) (same_modules matching.frames ▸ ht),
        ⟨matching.stores,matching.frames,?_⟩⟩
      rw [← same_modules matching.frames]
      exact Control.same _ _
    | @throwRefHandlerCatchRef s f n x l cs a e he ht =>
      obtain ⟨hm,shape⟩ := handler_throwing_input matching.code
      subst mode
      change ys = [.handler n (.catchRef x l :: cs) (throwing a)] at shape
      subst ys
      refine ⟨⟨t,g,vals e.fields ++ [.ref (.exn a),.plain (.br l)]⟩,
        .throwRefHandlerCatchRef (matching.stores.exns ▸ he) (same_modules matching.frames ▸ ht),
        ⟨matching.stores,matching.frames,?_⟩⟩
      rw [← same_modules matching.frames]
      exact Control.same _ _
    | @throwRefHandlerCatchAll s f n l cs a =>
      obtain ⟨hm,shape⟩ := handler_throwing_input matching.code
      subst mode
      change ys = [.handler n (.catchAll l :: cs) (throwing a)] at shape
      subst ys
      refine ⟨⟨t,g,[.plain (.br l)]⟩,.throwRefHandlerCatchAll,⟨matching.stores,matching.frames,?_⟩⟩
      rw [← same_modules matching.frames]
      exact Control.same _ _
    | @throwRefHandlerCatchAllRef s f n l cs a =>
      obtain ⟨hm,shape⟩ := handler_throwing_input matching.code
      subst mode
      change ys = [.handler n (.catchAllRef l :: cs) (throwing a)] at shape
      subst ys
      refine ⟨⟨t,g,[.ref (.exn a),.plain (.br l)]⟩,.throwRefHandlerCatchAllRef,⟨matching.stores,matching.frames,?_⟩⟩
      rw [← same_modules matching.frames]
      exact Control.same _ _
    | @throwRefHandlerNext s f n c cs a h =>
      obtain ⟨hm,shape⟩ := handler_throwing_input matching.code
      subst mode
      change ys = [.handler n (c :: cs) (throwing a)] at shape
      subst ys
      refine ⟨⟨t,g,[.handler n cs (throwing a)]⟩,
        .throwRefHandlerNext (fun ht => h ((catch_matches matching.stores (same_modules matching.frames) a c).mpr ht)),
        ⟨matching.stores,matching.frames,?_⟩⟩
      rw [← same_modules matching.frames]
      exact Control.same _ _
    | @tryTable s f bt cs body vs t₁ t₂ hbt hm =>
      obtain ⟨modeEq,shape⟩ := static_exception_code matching.code rfl (by intro h; cases h) (by intro r; simp only [instruction?])
      subst mode
      change ys = vals vs ++ [.plain (.tryTable bt cs body)] at shape
      subst ys
      refine ⟨⟨t,g,[.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩,
        .tryTable (same_modules matching.frames ▸ hbt) hm,⟨matching.stores,matching.frames,?_⟩⟩
      rw [← same_modules matching.frames]
      exact Control.same _ _
    | @handlerVals s f n cs vs =>
      obtain ⟨hm,modules,body,rest,shape,inner,empty⟩ := matching.code.handler_cons
      subst mode
      rw [empty.nil_left,inner.values_left] at shape
      change ys = [.handler n cs (vals vs)] at shape
      subst ys
      exact ⟨⟨t,g,vals vs⟩,.handlerVals,⟨matching.stores,matching.frames,Control.values _ _ _ _⟩⟩

end Silmaril.Wasm.Link.GC.AmbientSimulation
