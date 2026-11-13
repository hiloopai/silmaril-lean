module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreBulkRun

/-!
# `Good20B` at invocation: what remains of the state typing

`good20B_invoke` asks for the erased state typed in `simEnv20`. Here that hypothesis is taken
apart, and every part that holds of every V2 value is discharged:

* **every global instance is a `globalinst`** (`typedV_globalInst20`: `mut`, `valtype`, `val`)
  and **every element instance an `eleminst`** (`typedV_elemInst20`), with no hypothesis, as
  round 3 did for tables, memories and data instances;
* a Wasm function instance whose type, module and erased body are typed is a `funcinst`
  (`typedV_funcInst_erased20`; the type index and the locals are typed in general);
* a frame whose module is typed is a `frame`.

**`typedV_erasedState_of`**: the erased state is typed in `simEnv20` once, for the frame's module
and for every function of the store, the module instance (`moduleinst`), the function type
(`functype`) and the erased body (`instr*`) are typed. **`good20B_invoke_of`** is
`good20B_invoke` with that hypothesis.

What is left open, and why it is not general:
* `functype = resulttype -> resulttype`, with `resulttype = list(valtype)`, whose premise
  bounds the length by `2 ^ 32`: true of validated modules, not of every V2 value;
* `moduleinst`: its `EXPORTS` hold `name`s, whose premise calls `$utf8`, which the 2.0 script
  does not evaluate on a non-empty name;
* the erased bodies as `instr*`: the IL typing of the covered instructions, an instruction-wise
  case analysis that is not done here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreBulk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.Whole (storeB typedV_structG hasTypFields_consG hasTypFields_oneG
  typedV_aliasG)
open Silmaril.Wasm.SpecTec.Sim20.StoreFn (eraseS eraseFI eraseFI_code)

set_option maxRecDepth 100000

variable {H : Type} {hn : H → String} {B : Builtins}

local notation "E20" => Silmaril.Wasm.SpecTec.Sim20.simEnv20

/-! ## Global and element instances -/

theorem findTyp_MUT20 : (E20 B).findTyp? "MUT" =
    some ([], [.instD [] [] (.variantT [.mk "MUT" (.tupT []) [] []])]) := rfl

theorem findTyp_mut20 : (E20 B).findTyp? "mut" =
    some ([], [.instD [] [] (.aliasT (.iterT (.varT "MUT" []) .opt))]) := rfl

theorem findTyp_globaltype20 : (E20 B).findTyp? "globaltype" = some ([], [.instD [] []
    (.variantT [.mk "%%" (.tupT [.mk "mut" (.varT "mut" []), .mk "valtype" (.varT "valtype" [])])
      [] []])]) := rfl

theorem findTyp_elemtype20 : (E20 B).findTyp? "elemtype" =
    some ([], [.instD [] [] (.aliasT (.varT "reftype" []))]) := rfl

/-- Every mutability is a `mut`. -/
theorem typedV_mut20 (m : Mutability) : TypedV (E20 B) (.varT "mut" []) (mutV m) := by
  cases m with
  | const => exact typedV_aliasG findTyp_mut20 (hasTyp_iterT_opt_iff.2 (.inl rfl))
  | var =>
    exact typedV_aliasG findTyp_mut20 (hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl,
      Pure.typedV_closedCase20 findTyp_MUT20 rfl hasTyp_tupT_nil _ ⟨rfl, rfl, rfl⟩⟩))

/-- Every global type is a `globaltype`. -/
theorem typedV_globalType20 (g : V2.GlobalType) :
    TypedV (E20 B) (.varT "globaltype" []) (globalTypeV g) :=
  Pure.typedV_closedCase20 findTyp_globaltype20 rfl
    (Whole.hasTyp_tup2G (typedV_mut20 g.mutability) (Whole.typedV_valType20 g.value))

/-- **Every V2 global instance is a `globalinst`.** -/
theorem typedV_globalInst20 (gi : GlobalInst) :
    TypedV (E20 B) (.varT "globalinst" []) (globalInstV gi) :=
  typedV_structG Whole.findTyp_globalinst20 (hasTypFields_consG (typedV_globalType20 gi.type)
    (hasTypFields_oneG (Whole.typedV_val20 gi.value)))

/-- **Every V2 element instance is an `eleminst`.** -/
theorem typedV_elemInst20 (ei : ElemInst) :
    TypedV (E20 B) (.varT "eleminst" []) (elemInstV ei) :=
  typedV_structG Whole.findTyp_eleminst20 (hasTypFields_consG
    (typedV_aliasG findTyp_elemtype20 (Whole.typedV_refType20 ei.type _ ⟨rfl, rfl, rfl⟩))
    (hasTypFields_oneG (Sim.typedV_list_iff.2 fun u hu => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hu
      exact Whole.typedV_ref20 r)))

/-! ## Function instances -/

theorem findTyp_local20 : (E20 B).findTyp? "local" =
    some ([], [.instD [] [] (.variantT [.mk "LOCAL" (.varT "valtype" []) [] []])]) := rfl

theorem findTyp_typeidx20 : (E20 B).findTyp? "typeidx" =
    some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

/-- The locals of every function are a `local*`. -/
theorem typedV_locals20 (ts : List V2.ValType) :
    TypedV (E20 B) (.iterT (.varT "local" []) .list) (.list ((ts.map valTypeV).map (.case "LOCAL"))) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hv
    exact Pure.typedV_closedCase20 findTyp_local20 rfl
      (Whole.typedV_valType20 t _ ⟨rfl, rfl, rfl⟩)

/-- **A Wasm function instance is a `funcinst` once its type, its module and its body are
typed.** -/
theorem typedV_funcInst_wasm20 {fi : FuncInst H} {fn : V2.Func} (hc : fi.code = .wasm fn)
    (hty : TypedV (E20 B) (.varT "functype" []) (funcTypeV fi.type))
    (hmo : TypedV (E20 B) (.varT "moduleinst" []) (moduleInstV fi.module))
    (hb : TypedV (E20 B) Pure.instrsT (.list (instrsToV fn.body))) :
    TypedV (E20 B) (.varT "funcinst" []) (funcInstV hn fi) := by
  have hfunc : TypedV (E20 B) (.varT "func" []) (Whole.codeV20 fn) :=
    StoreFn.func_mk Whole.findTyp_func20 Whole.findTyp_expr20
      (typedV_aliasG findTyp_typeidx20 (Whole.typedV_idx20 fn.type _ ⟨rfl, rfl, rfl⟩))
      (typedV_locals20 fn.locals) hb
  rw [Whole.funcInstV_wasm hc]
  exact typedV_structG Whole.findTyp_funcinst20 (hasTypFields_consG hty
    (hasTypFields_consG hmo (hasTypFields_oneG hfunc)))

/-- **The erased Wasm function instance is a `funcinst`** once its type, its module and its
erased body are typed. -/
theorem typedV_funcInst_erased20 {fi : FuncInst H} {fn : V2.Func} (hc : fi.code = .wasm fn)
    (hty : TypedV (E20 B) (.varT "functype" []) (funcTypeV fi.type))
    (hmo : TypedV (E20 B) (.varT "moduleinst" []) (moduleInstV fi.module))
    (hb : TypedV (E20 B) Pure.instrsT (.list (instrsToV (fn.body.map StoreDeep.eD)))) :
    TypedV (E20 B) (.varT "funcinst" []) (funcInstV hn (eraseFI fi)) :=
  typedV_funcInst_wasm20 (fn := { fn with body := fn.body.map StoreDeep.eD }) (eraseFI_code hc)
    hty hmo hb

/-! ## The erased state -/

/-- **What the erased state needs**: for the frame's module and for every (Wasm) function of the
store, the module instance, the function type and the erased body typed in `simEnv20`. -/
structure InvokeTy (B : Builtins) (s : Store H) (f : Frame) : Prop where
  frame : TypedV (E20 B) (.varT "moduleinst" []) (moduleInstV f.module)
  funcs : ∀ fi ∈ s.funcs, ∃ fn, fi.code = .wasm fn ∧
    TypedV (E20 B) (.varT "functype" []) (funcTypeV fi.type) ∧
    TypedV (E20 B) (.varT "moduleinst" []) (moduleInstV fi.module) ∧
    TypedV (E20 B) Pure.instrsT (.list (instrsToV (fn.body.map StoreDeep.eD)))

/-- A list of values each typed at a closed type name. -/
theorem typedV_map20 {α : Type} {x : IL.Id} (g : α → Value) (l : List α)
    (h : ∀ a, TypedV (E20 B) (.varT x []) (g a)) :
    TypedV (E20 B) (.iterT (.varT x []) .list) (.list (l.map g)) :=
  Sim.typedV_list_iff.2 fun u hu => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hu
    exact h a

/-- The erased function instances under `InvokeTy`. -/
theorem typedV_erasedFuncs {s : Store H} {f : Frame} (h : InvokeTy B s f) :
    TypedV (E20 B) (.iterT (.varT "funcinst" []) .list)
      (.list ((eraseS s).funcs.map (funcInstV hn))) :=
  Sim.typedV_list_iff.2 fun u hu => by
    have hu' : u ∈ s.funcs.map (fun fi => funcInstV hn (eraseFI fi)) := by
      simpa only [StoreFn.eraseS_funcs, List.map_map, Function.comp_def] using hu
    obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hu'
    obtain ⟨fn, hc, hty, hmo, hb⟩ := h.funcs fi hfi
    exact typedV_funcInst_erased20 hc hty hmo hb

/-- **The erased state is typed in `simEnv20`** under `InvokeTy`: globals, tables, memories,
element and data instances are typed in general, function instances and the frame from
`InvokeTy`. -/
theorem typedV_erasedState_of {s : Store H} {f : Frame} (h : InvokeTy B s f) :
    TypedV (E20 B) stateT (stateV hn (eraseS s) f) :=
  Whole.typedV_stateV_iff.2 ⟨Whole.typedV_storeV_iff.2 ⟨typedV_erasedFuncs h,
    typedV_map20 _ _ typedV_globalInst20, typedV_map20 _ _ Whole.typedV_tableInst20,
    typedV_map20 _ _ Whole.typedV_memInst20, typedV_map20 _ _ typedV_elemInst20,
    typedV_map20 _ _ Whole.typedV_dataInst20⟩, Whole.typedV_frame_of20 h.frame f.locals⟩

/-- **`Good20B` at an invocation `val* (CALL_ADDR a)`**, from `InvokeTy`, a `StoreOkB` store and
`StoreSmall`. -/
theorem good20B_invoke_of {P : Profile} {s : Store H} {f : Frame} {args : List Val}
    {a : FuncAddr} (h : InvokeTy (storeB P) s f) (hs : StoreOkB s) (hm : StoreSmall s) :
    Good20B hn P ⟨s, f, vals args ++ [.callAddr a]⟩ :=
  good20B_invoke (typedV_erasedState_of h) hs hm

end Silmaril.Wasm.SpecTec.Sim20.StoreBulk
