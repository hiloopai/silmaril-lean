module

public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Execution.Core.Typing.Store

@[expose] public section

/-! # Replacing function code in a store

`Store.withFuncs s X` replaces the function instances of `s` by `X`. When `X` has the
same function types as `s.funcs`, every reduction of the families (`MemoryStep`,
`TableStep`, `RefStep`, `AggregateStep`, `VariableStep`) is unaffected: it does not look
at function code and does not change the function list. This is the store half of the
inlining simulation (`Binaryen/Inline.lean`), where the two stores differ only in the
code of the caller.
-/

namespace Silmaril.Wasm.Binaryen.InlS

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- Replace the function instances of a store. -/
def withFuncs (s : Store H) (X : List (FuncInst H)) : Store H := { s with funcs := X }

@[simp] theorem withFuncs_funcs (s : Store H) (X : List (FuncInst H)) :
    (withFuncs s X).funcs = X := rfl

/-- The function types of two function lists agree. -/
def SameTypes (X Y : List (FuncInst H)) : Prop := X.map FuncInst.type = Y.map FuncInst.type

theorem SameTypes.get {X Y : List (FuncInst H)} (h : SameTypes X Y) {a : Nat}
    {fi : FuncInst H} (hf : Y[a]? = some fi) : ∃ fi', X[a]? = some fi' ∧ fi'.type = fi.type := by
  have h' := congrArg (fun l => l[a]?) h
  simp only [List.getElem?_map, hf, Option.map_some] at h'
  cases hx : X[a]? with
  | none => rw [hx] at h'; cases h'
  | some fi' => rw [hx] at h'; exact ⟨fi', rfl, Option.some.inj h'⟩

theorem SameTypes.symm {X Y : List (FuncInst H)} (h : SameTypes X Y) : SameTypes Y X := Eq.symm h

theorem refOk_withFuncs {s : Store H} {X : List (FuncInst H)} (hX : SameTypes X s.funcs)
    {r : Ref} {rt : CRefType} (h : RefOk s r rt) : RefOk (withFuncs s X) r rt := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | func h =>
    obtain ⟨fi', h', ht⟩ := hX.get h
    have := RefOk.func (s := withFuncs s X) h'
    rwa [ht] at this
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem refOk_withFuncs_iff {s : Store H} {X : List (FuncInst H)} (hX : SameTypes X s.funcs)
    {r : Ref} {rt : CRefType} : RefOk (withFuncs s X) r rt ↔ RefOk s r rt := by
  refine ⟨fun h => ?_, refOk_withFuncs hX⟩
  have e : s = withFuncs (withFuncs s X) s.funcs := rfl
  rw [e]
  exact refOk_withFuncs (s := withFuncs s X) hX.symm h

section families

variable {P : Numerics.Profile} {s s' : Store H} {f f' : Frame} {is is' : List Admin}
  {X : List (FuncInst H)}

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem memoryStep_withFuncs (h : MemoryStep P ⟨s, f, is⟩ ⟨s', f', is'⟩) (X : List (FuncInst H)) :
    s'.funcs = s.funcs ∧ f' = f ∧ ∀ gl : List (Option Val),
      MemoryStep P ⟨withFuncs s X, ⟨gl, f.module⟩, is⟩ ⟨withFuncs s' X, ⟨gl, f.module⟩, is'⟩ := by
  cases h <;> refine ⟨rfl, rfl, fun gl => ?_⟩
  all_goals first
    | (apply MemoryStep.loadIntOob <;> assumption)
    | (apply MemoryStep.loadIntVal <;> assumption)
    | (apply MemoryStep.loadPackOob <;> assumption)
    | (apply MemoryStep.loadPackVal <;> assumption)
    | (apply MemoryStep.loadFloatOob <;> assumption)
    | (apply MemoryStep.loadFloatVal <;> assumption)
    | (apply MemoryStep.vecLoadOob <;> assumption)
    | (apply MemoryStep.vecLoadVal <;> assumption)
    | (apply MemoryStep.vecLoadLaneOob <;> assumption)
    | (apply MemoryStep.vecLoadLaneVal <;> assumption)
    | (apply MemoryStep.storeIntOob <;> assumption)
    | (apply MemoryStep.storeIntVal <;> assumption)
    | (apply MemoryStep.storePackOob <;> assumption)
    | (apply MemoryStep.storePackVal <;> assumption)
    | (apply MemoryStep.storeFloatOob <;> assumption)
    | (apply MemoryStep.storeFloatVal <;> assumption)
    | (apply MemoryStep.vecStoreOob <;> assumption)
    | (apply MemoryStep.vecStoreVal <;> assumption)
    | (apply MemoryStep.vecStoreLaneOob <;> assumption)
    | (apply MemoryStep.vecStoreLaneVal <;> assumption)
    | (apply MemoryStep.size <;> assumption)
    | (apply MemoryStep.growSucceed <;> assumption)
    | (apply MemoryStep.growFail <;> assumption)
    | (apply MemoryStep.fillOob <;> assumption)
    | (apply MemoryStep.fillZero <;> assumption)
    | (apply MemoryStep.fillSucc <;> assumption)
    | (apply MemoryStep.copyOob <;> assumption)
    | (apply MemoryStep.copyZero <;> assumption)
    | (apply MemoryStep.copyLe <;> assumption)
    | (apply MemoryStep.copyGt <;> assumption)
    | (apply MemoryStep.initOob <;> assumption)
    | (apply MemoryStep.initZero <;> assumption)
    | (apply MemoryStep.initSucc <;> assumption)
    | (apply MemoryStep.dataDrop <;> assumption)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem tableStep_withFuncs (h : TableStep P ⟨s, f, is⟩ ⟨s', f', is'⟩) (X : List (FuncInst H)) :
    s'.funcs = s.funcs ∧ f' = f ∧ ∀ gl : List (Option Val),
      TableStep P ⟨withFuncs s X, ⟨gl, f.module⟩, is⟩ ⟨withFuncs s' X, ⟨gl, f.module⟩, is'⟩ := by
  cases h <;> refine ⟨rfl, rfl, fun gl => ?_⟩
  all_goals first
    | (apply TableStep.getOob <;> assumption)
    | (apply TableStep.getVal <;> assumption)
    | (apply TableStep.setOob <;> assumption)
    | (apply TableStep.setVal <;> assumption)
    | (apply TableStep.size <;> assumption)
    | (apply TableStep.growSucceed <;> assumption)
    | (apply TableStep.growFail <;> assumption)
    | (apply TableStep.fillOob <;> assumption)
    | (apply TableStep.fillZero <;> assumption)
    | (apply TableStep.fillSucc <;> assumption)
    | (apply TableStep.copyOob <;> assumption)
    | (apply TableStep.copyZero <;> assumption)
    | (apply TableStep.copyLe <;> assumption)
    | (apply TableStep.copyGt <;> assumption)
    | (apply TableStep.initOob <;> assumption)
    | (apply TableStep.initZero <;> assumption)
    | (apply TableStep.initSucc <;> assumption)
    | (apply TableStep.elemDrop <;> assumption)

theorem variableStep_withFuncs (h : VariableStep ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (X : List (FuncInst H)) :
    s'.funcs = s.funcs ∧ VariableStep ⟨withFuncs s X, f, is⟩ ⟨withFuncs s' X, f', is'⟩ := by
  cases h with
  | localGet h => exact ⟨rfl, .localGet h⟩
  | localSet h => exact ⟨rfl, .localSet h⟩
  | localTee => exact ⟨rfl, .localTee⟩
  | globalGet h => exact ⟨rfl, .globalGet h⟩
  | globalSet h => exact ⟨rfl, .globalSet h⟩

theorem refStep_withFuncs (h : RefStep ⟨s, f, is⟩ ⟨s', f', is'⟩) (hX : SameTypes X s.funcs) :
    s'.funcs = s.funcs ∧ f' = f ∧ ∀ gl : List (Option Val),
      RefStep ⟨withFuncs s X, ⟨gl, f.module⟩, is⟩ ⟨withFuncs s' X, ⟨gl, f.module⟩, is'⟩ := by
  cases h with
  | refNull ht => exact ⟨rfl, rfl, fun _ => .refNull ht⟩
  | refFunc h => exact ⟨rfl, rfl, fun _ => .refFunc h⟩
  | refI31 i => exact ⟨rfl, rfl, fun _ => .refI31 i⟩
  | isNullTrue => exact ⟨rfl, rfl, fun _ => .isNullTrue⟩
  | isNullFalse h => exact ⟨rfl, rfl, fun _ => .isNullFalse h⟩
  | asNonNullNull => exact ⟨rfl, rfl, fun _ => .asNonNullNull⟩
  | asNonNullAddr h => exact ⟨rfl, rfl, fun _ => .asNonNullAddr h⟩
  | eqNull => exact ⟨rfl, rfl, fun _ => .eqNull⟩
  | eqTrue h => exact ⟨rfl, rfl, fun _ => .eqTrue h⟩
  | eqFalse h => exact ⟨rfl, rfl, fun _ => .eqFalse h⟩
  | testTrue h => exact ⟨rfl, rfl, fun _ => .testTrue ((refOk_withFuncs_iff hX).2 h)⟩
  | testFalse h =>
    exact ⟨rfl, rfl, fun _ => .testFalse fun h' => h ((refOk_withFuncs_iff hX).1 h')⟩
  | castSucceed h => exact ⟨rfl, rfl, fun _ => .castSucceed ((refOk_withFuncs_iff hX).2 h)⟩
  | castFail h =>
    exact ⟨rfl, rfl, fun _ => .castFail fun h' => h ((refOk_withFuncs_iff hX).1 h')⟩
  | i31GetNull sx => exact ⟨rfl, rfl, fun _ => .i31GetNull sx⟩
  | i31GetNum sx i => exact ⟨rfl, rfl, fun _ => .i31GetNum sx i⟩
  | externConvertNull => exact ⟨rfl, rfl, fun _ => .externConvertNull⟩
  | externConvertAddr h => exact ⟨rfl, rfl, fun _ => .externConvertAddr h⟩
  | anyConvertNull => exact ⟨rfl, rfl, fun _ => .anyConvertNull⟩
  | anyConvertAddr r => exact ⟨rfl, rfl, fun _ => .anyConvertAddr r⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem aggregateStep_withFuncs (h : AggregateStep ⟨s, f, is⟩ ⟨s', f', is'⟩)
    (X : List (FuncInst H)) :
    s'.funcs = s.funcs ∧ f' = f ∧ ∀ gl : List (Option Val),
      AggregateStep ⟨withFuncs s X, ⟨gl, f.module⟩, is⟩ ⟨withFuncs s' X, ⟨gl, f.module⟩, is'⟩ := by
  cases h <;> refine ⟨rfl, rfl, fun gl => ?_⟩
  all_goals first
    | (apply AggregateStep.structNew <;> assumption)
    | (apply AggregateStep.structNewDefault <;> assumption)
    | (apply AggregateStep.structGetNull <;> assumption)
    | (apply AggregateStep.structGetStruct <;> assumption)
    | (apply AggregateStep.structSetNull <;> assumption)
    | (apply AggregateStep.structSetStruct <;> assumption)
    | (apply AggregateStep.arrayNew <;> assumption)
    | (apply AggregateStep.arrayNewDefault <;> assumption)
    | (apply AggregateStep.arrayNewFixed <;> assumption)
    | (apply AggregateStep.arrayNewElemOob <;> assumption)
    | (apply AggregateStep.arrayNewElemAlloc <;> assumption)
    | (apply AggregateStep.arrayNewDataOob <;> assumption)
    | (apply AggregateStep.arrayNewDataNum <;> assumption)
    | (apply AggregateStep.arrayGetNull <;> assumption)
    | (apply AggregateStep.arrayGetOob <;> assumption)
    | (apply AggregateStep.arrayGetArray <;> assumption)
    | (apply AggregateStep.arraySetNull <;> assumption)
    | (apply AggregateStep.arraySetOob <;> assumption)
    | (apply AggregateStep.arraySetArray <;> assumption)
    | (apply AggregateStep.arrayLenNull <;> assumption)
    | (apply AggregateStep.arrayLenArray <;> assumption)
    | (apply AggregateStep.arrayFillNull <;> assumption)
    | (apply AggregateStep.arrayFillOob <;> assumption)
    | (apply AggregateStep.arrayFillZero <;> assumption)
    | (apply AggregateStep.arrayFillSucc <;> assumption)
    | (apply AggregateStep.arrayCopyNull₁ <;> assumption)
    | (apply AggregateStep.arrayCopyNull₂ <;> assumption)
    | (apply AggregateStep.arrayCopyOob₁ <;> assumption)
    | (apply AggregateStep.arrayCopyOob₂ <;> assumption)
    | (apply AggregateStep.arrayCopyZero <;> assumption)
    | (apply AggregateStep.arrayCopyLe <;> assumption)
    | (apply AggregateStep.arrayCopyGt <;> assumption)
    | (apply AggregateStep.arrayInitElemNull <;> assumption)
    | (apply AggregateStep.arrayInitElemOob₁ <;> assumption)
    | (apply AggregateStep.arrayInitElemOob₂ <;> assumption)
    | (apply AggregateStep.arrayInitElemZero <;> assumption)
    | (apply AggregateStep.arrayInitElemSucc <;> assumption)
    | (apply AggregateStep.arrayInitDataNull <;> assumption)
    | (apply AggregateStep.arrayInitDataOob₁ <;> assumption)
    | (apply AggregateStep.arrayInitDataOob₂ <;> assumption)
    | (apply AggregateStep.arrayInitDataZero <;> assumption)
    | (apply AggregateStep.arrayInitDataNum <;> assumption)

end families

section typing

variable {s : Store H} {X : List (FuncInst H)}

theorem valOk_withFuncs (hX : SameTypes X s.funcs) {v : Val} {t : CValType} (h : ValOk s v t) :
    ValOk (withFuncs s X) v t := by
  cases h with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref h => exact .ref (refOk_withFuncs hX h)

theorem fieldValOk_withFuncs (hX : SameTypes X s.funcs) {v : FieldVal} {t : CStorageType}
    (h : FieldValOk s v t) : FieldValOk (withFuncs s X) v t := by
  cases h with
  | val h => exact .val (valOk_withFuncs hX h)
  | pack p b => exact .pack p b

theorem externAddrOk_withFuncs (hX : SameTypes X s.funcs) {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) : ExternAddrOk (withFuncs s X) xa xt := by
  induction h with
  | tag h => exact .tag h
  | global h => exact .global h
  | mem h => exact .mem h
  | table h => exact .table h
  | func h =>
    obtain ⟨fi', h', ht⟩ := hX.get h
    have := ExternAddrOk.func (s := withFuncs s X) h'
    rwa [ht] at this
  | sub _ hok hs ih => exact .sub ih hok hs

theorem elemInstOk_withFuncs (hX : SameTypes X s.funcs) {ei : ElemInst} (h : ElemInstOk s ei) :
    ElemInstOk (withFuncs s X) ei :=
  ⟨h.1, fun r hr => refOk_withFuncs hX (h.2 r hr)⟩

theorem moduleInstOk_withFuncs (hX : SameTypes X s.funcs) {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : ModuleInstOk (withFuncs s X) mi C := by
  cases h with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems hexports hdisjoint hexportAddrs
      hk =>
    refine .mk htypes (htags.imp fun _ _ h => externAddrOk_withFuncs hX h)
      (hglobals.imp fun _ _ h => externAddrOk_withFuncs hX h)
      (hfuncs.imp fun _ _ h => externAddrOk_withFuncs hX h)
      (hmems.imp fun _ _ h => externAddrOk_withFuncs hX h)
      (htables.imp fun _ _ h => externAddrOk_withFuncs hX h) hdatas
      (helems.imp fun _ _ h => ?_) (fun xi hxi => ?_) hdisjoint hexportAddrs hk
    · obtain ⟨ei, hei, hok, he⟩ := h
      exact ⟨ei, hei, elemInstOk_withFuncs hX hok, he⟩
    · obtain ⟨xt, hxt⟩ := hexports xi hxi
      exact ⟨xt, externAddrOk_withFuncs hX hxt⟩

theorem funcInstOk_withFuncs (hX : SameTypes X s.funcs) {fi : FuncInst H} (h : FuncInstOk s fi) :
    FuncInstOk (withFuncs s X) fi := by
  cases h with
  | wasm hdt hm hcode hf hs => exact .wasm hdt (moduleInstOk_withFuncs hX hm) hcode hf hs
  | host hdt he hcode => exact .host hdt he hcode

theorem immutReachable_withFuncs {a b : FieldVal} (h : ImmutReachable (withFuncs s X) a b) :
    ImmutReachable s a b := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct hs he hi hfv
  | refArray hs he hfv => exact .refArray hs he hfv
  | refExn hs hv => exact .refExn hs hv
  | refExtern r => exact .refExtern r

/-- **Replacing function code keeps the store valid**, if the new function instances
are valid and have the old types. -/
theorem storeOk_withFuncs (hs : StoreOk s) (hX : SameTypes X s.funcs)
    (hf : ∀ fi ∈ X, FuncInstOk (withFuncs s X) fi) : StoreOk (withFuncs s X) where
  tags := hs.tags
  globals := fun gi hg => ⟨(hs.globals gi hg).1, valOk_withFuncs hX (hs.globals gi hg).2⟩
  mems := hs.mems
  tables := fun ti ht => ⟨(hs.tables ti ht).1, (hs.tables ti ht).2.1,
    fun r hr => refOk_withFuncs hX ((hs.tables ti ht).2.2 r hr)⟩
  funcs := hf
  elems := fun ei he => elemInstOk_withFuncs hX (hs.elems ei he)
  structs := fun si hsi => by
    obtain ⟨fs, he, hfs⟩ := hs.structs si hsi
    exact ⟨fs, he, hfs.imp fun _ _ h => fieldValOk_withFuncs hX h⟩
  arrays := fun ai hai => by
    obtain ⟨ft, he, hfs⟩ := hs.arrays ai hai
    exact ⟨ft, he, fun fv hfv => fieldValOk_withFuncs hX (hfs fv hfv)⟩
  exns := fun e he => by
    obtain ⟨ti, ts, ht, hex, hvs⟩ := hs.exns e he
    exact ⟨ti, ts, ht, hex, hvs.imp fun _ _ h => valOk_withFuncs hX h⟩
  acyclicStructs := fun a ha h => hs.acyclicStructs a ha (immutReachable_withFuncs h)
  acyclicArrays := fun a ha h => hs.acyclicArrays a ha (immutReachable_withFuncs h)
  acyclicExns := fun a ha h => hs.acyclicExns a ha (immutReachable_withFuncs h)
  structsClosed := hs.structsClosed
  arraysClosed := hs.arraysClosed

end typing

end Silmaril.Wasm.Binaryen.InlS
