module

public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Game.Instantiate.Defs

/-!
# Changing the host type of a Core 3.0 store

The component machine runs Core 3.0 code in stores `Store (CanonHost E)` (host functions are
the canonical built-ins and lowered functions), while the game semantics of Core 3.0 instances
uses `Store Nat`. `Store.mapH g` changes the host type along `g : H → H'`: it renames the code
of host functions and keeps everything else, including their types.

* `Step.mapH`: a host-free step (`noHost`) is matched by a host-free step of the mapped
  configurations, so runs (`Steps.mapH`) and divergence (`Diverges.mapH`) are carried over.
  No rule of the host-free relation reads host code (host calls need the empty host
  relation), and every other rule reads function instances only through their types and wasm
  code, which `mapH` keeps.
* `instantiateOnce?_mapH`: instantiation (`instantiateOnce?`, through constant evaluation,
  allocation and segment initialisation) commutes with `mapH`; `invoke_mapH`: so does the
  invocation configuration.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {H H' : Type} (g : H → H')

/-- Rename the host code of a function. -/
def FuncCode.mapH : FuncCode H → FuncCode H'
  | .wasm f => .wasm f
  | .host h => .host (g h)

/-- Rename the host code of a function instance. -/
def FuncInst.mapH (fi : FuncInst H) : FuncInst H' :=
  { type := fi.type, module := fi.module, code := FuncCode.mapH g fi.code }

/-- Change the host type of a store. -/
def Store.mapH (s : Store H) : Store H' :=
  { tags := s.tags, globals := s.globals, mems := s.mems, tables := s.tables,
    funcs := s.funcs.map (FuncInst.mapH g), datas := s.datas, elems := s.elems,
    structs := s.structs, arrays := s.arrays, exns := s.exns }

/-- Change the host type of a configuration. -/
def Config.mapH (c : Config H) : Config H' := ⟨Store.mapH g c.store, c.frame, c.code⟩

/-- The empty host relation. -/
abbrev noHostH (H : Type) : HostSemantics H := fun _ _ _ _ => False

namespace Store

variable (s : Store H)

theorem mapH_funcs_getElem? (a : Nat) :
    (Store.mapH g s).funcs[a]? = (s.funcs[a]?).map (FuncInst.mapH g) := by
  simp only [Store.mapH, List.getElem?_map]

theorem mapH_setGlobal (a : Nat) (v : Val) :
    Store.mapH g (s.setGlobal a v) = (Store.mapH g s).setGlobal a v := rfl
theorem mapH_setTable (a : Nat) (ti : TableInst) :
    Store.mapH g (s.setTable a ti) = (Store.mapH g s).setTable a ti := rfl
theorem mapH_setMem (a : Nat) (mi : MemInst) :
    Store.mapH g (s.setMem a mi) = (Store.mapH g s).setMem a mi := rfl
theorem mapH_setElem (a : Nat) (refs : List Ref) :
    Store.mapH g (s.setElem a refs) = (Store.mapH g s).setElem a refs := rfl
theorem mapH_setData (a : Nat) (bytes : ByteArray) :
    Store.mapH g (s.setData a bytes) = (Store.mapH g s).setData a bytes := rfl
theorem mapH_setStructField (a i : Nat) (fv : FieldVal) :
    Store.mapH g (s.setStructField a i fv) = (Store.mapH g s).setStructField a i fv := rfl
theorem mapH_setArrayField (a i : Nat) (fv : FieldVal) :
    Store.mapH g (s.setArrayField a i fv) = (Store.mapH g s).setArrayField a i fv := rfl
theorem mapH_addStruct (si : StructInst) :
    Store.mapH g (s.addStruct si) = (Store.mapH g s).addStruct si := rfl
theorem mapH_addArray (ai : ArrayInst) :
    Store.mapH g (s.addArray ai) = (Store.mapH g s).addArray ai := rfl
theorem mapH_addExn (e : ExnInst) :
    Store.mapH g (s.addExn e) = (Store.mapH g s).addExn e := rfl

end Store

/-- `RefOk` reads function instances only through their types. -/
theorem RefOk.mapH {s : Store H} {r : Ref} {t : CRefType} (h : RefOk s r t) :
    RefOk (Store.mapH g s) r t := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | @func a fi h =>
    have h' : (Store.mapH g s).funcs[a]? = some (FuncInst.mapH g fi) := by
      rw [Store.mapH_funcs_getElem?, h]
      rfl
    exact .func h'
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

/-- The converse of `RefOk.mapH`. -/
theorem RefOk.of_mapH {s : Store H} {r : Ref} {t : CRefType}
    (h : RefOk (Store.mapH g s) r t) : RefOk s r t := by
  induction h with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct h => exact .struct h
  | array h => exact .array h
  | @func a fi h =>
    obtain ⟨fi₀, h₀, rfl⟩ : ∃ fi₀, s.funcs[a]? = some fi₀ ∧ FuncInst.mapH g fi₀ = fi := by
      rw [Store.mapH_funcs_getElem?] at h
      exact Option.map_eq_some_iff.mp h
    exact .func h₀
  | exn h => exact .exn h
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem RefOk.mapH_iff {s : Store H} {r : Ref} {t : CRefType} :
    RefOk (Store.mapH g s) r t ↔ RefOk s r t :=
  ⟨RefOk.of_mapH g, RefOk.mapH g⟩

/-! ## Family steps -/

section Families

variable {P : Profile} {c c' : Config H}

theorem VariableStep.mapH (h : VariableStep c c') :
    VariableStep (Config.mapH g c) (Config.mapH g c') := by
  cases h <;> (try simp only [Config.mapH, Store.mapH_setGlobal]) <;> constructor! <;>
    assumption

theorem TableStep.mapH (h : TableStep P c c') :
    TableStep P (Config.mapH g c) (Config.mapH g c') := by
  cases h <;> (try simp only [Config.mapH, Store.mapH_setTable, Store.mapH_setElem]) <;>
    constructor! <;> assumption

theorem MemoryStep.mapH (h : MemoryStep P c c') :
    MemoryStep P (Config.mapH g c) (Config.mapH g c') := by
  cases h <;> (try simp only [Config.mapH, Store.mapH_setMem, Store.mapH_setData]) <;>
    constructor! <;> assumption

theorem RefStep.mapH (h : RefStep c c') :
    RefStep (Config.mapH g c) (Config.mapH g c') := by
  cases h <;> (try simp only [Config.mapH]) <;> constructor! <;>
    first
      | assumption
      | exact (RefOk.mapH_iff g).2 ‹_›
      | exact fun h' => ‹¬ RefOk _ _ _› ((RefOk.mapH_iff g).1 h')

theorem AggregateStep.mapH (h : AggregateStep c c') :
    AggregateStep (Config.mapH g c) (Config.mapH g c') := by
  cases h <;>
    (try simp only [Config.mapH, Store.mapH_setStructField, Store.mapH_setArrayField,
      Store.mapH_addStruct, Store.mapH_addArray]) <;>
    first
      | (constructor! <;> assumption)
      | (apply AggregateStep.arrayCopyOob₂ <;> assumption)
      | (apply AggregateStep.arrayInitElemOob₂ <;> assumption)
      | (apply AggregateStep.arrayInitDataOob₂ <;> assumption)

end Families

/-! ## Host-free steps -/


variable {P : Profile}

theorem funcs_mapH {s : Store H} {a : Nat} {fi : FuncInst H} (h : s.funcs[a]? = some fi) :
    (Store.mapH g s).funcs[a]? = some (FuncInst.mapH g fi) := by
  rw [Store.mapH_funcs_getElem?, h]
  rfl

theorem code_mapH {fi : FuncInst H} {code : Func} (h : fi.code = .wasm code) :
    (FuncInst.mapH g fi).code = .wasm code := by
  simp only [FuncInst.mapH, h, FuncCode.mapH]

theorem catchMatches_mapH {s : Store H} {f : Frame} {a : Nat} {c : Catch} :
    CatchMatches (Store.mapH g s) f a c ↔ CatchMatches s f a c := by
  cases c <;> exact Iff.rfl

/-- **Host-free steps commute with changing the host type.** -/
theorem Step.mapH {c c' : Config H} (h : Step P (noHostH H) c c') :
    Step P (noHostH H') (Config.mapH g c) (Config.mapH g c') := by
  induction h with
  | «variable» h => exact .variable (VariableStep.mapH g h)
  | table h => exact .table (TableStep.mapH g h)
  | memory h => exact .memory (MemoryStep.mapH g h)
  | reference h => exact .reference (RefStep.mapH g h)
  | aggregate h => exact .aggregate (AggregateStep.mapH g h)
  | callRefHost _ _ _ _ _ hh => exact hh.elim
  | callRefHostDiv _ _ _ _ _ hh => exact hh.elim
  | call hx hf => exact .call hx (funcs_mapH g hf)
  | callRefFunc hc hf he hn hcode => exact .callRefFunc hc (funcs_mapH g hf) he hn (code_mapH g hcode)
  | returnCall hx hf => exact .returnCall hx (funcs_mapH g hf)
  | returnCallRefFrameAddr hc hf he hn => exact .returnCallRefFrameAddr hc (funcs_mapH g hf) he hn
  | throwRefHandlerNext h => exact .throwRefHandlerNext fun h' => h ((catchMatches_mapH g).1 h')
  | parametric h => exact .parametric h
  | numeric h => exact .numeric h
  | vector h => exact .vector h
  | ctxtInstrs _ hne ih => exact .ctxtInstrs ih hne
  | ctxtLabel _ ih => exact .ctxtLabel ih
  | ctxtHandler _ ih => exact .ctxtHandler ih
  | ctxtFrame _ ih => exact .ctxtFrame ih
  | throw ht he hn =>
    simp only [Config.mapH, Store.mapH_addExn]
    exact .throw ht he hn
  | block => apply Step.block <;> assumption
  | loop => apply Step.loop <;> assumption
  | ifTrue => exact Step.ifTrue ‹_›
  | ifFalse => apply Step.ifFalse
  | labelVals => apply Step.labelVals
  | brLabelZero => apply Step.brLabelZero <;> assumption
  | brLabelSucc => exact Step.brLabelSucc ‹_›
  | brHandler => apply Step.brHandler
  | brIfTrue => exact Step.brIfTrue ‹_›
  | brIfFalse => apply Step.brIfFalse
  | brTableLt => exact Step.brTableLt ‹_›
  | brTableGe => exact Step.brTableGe ‹_›
  | brOnNullNull => apply Step.brOnNullNull
  | brOnNullAddr => exact Step.brOnNullAddr ‹_›
  | brOnNonNullNull => apply Step.brOnNonNullNull
  | brOnNonNullAddr => exact Step.brOnNonNullAddr ‹_›
  | brOnCastSucceed h => exact .brOnCastSucceed ((RefOk.mapH_iff g).2 h)
  | brOnCastFail h => exact .brOnCastFail fun h' => h ((RefOk.mapH_iff g).1 h')
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed ((RefOk.mapH_iff g).2 h)
  | brOnCastFailFail h => exact .brOnCastFailFail fun h' => h ((RefOk.mapH_iff g).1 h')
  | callRefNull => exact Step.callRefNull ‹_›
  | returnCallRefLabel => exact Step.returnCallRefLabel ‹_›
  | returnCallRefHandler => exact Step.returnCallRefHandler ‹_›
  | returnCallRefFrameNull => exact Step.returnCallRefFrameNull ‹_›
  | callIndirect => apply Step.callIndirect
  | returnCallIndirect => apply Step.returnCallIndirect
  | frameVals => exact Step.frameVals ‹_›
  | returnFrame => exact Step.returnFrame ‹_›
  | returnLabel => apply Step.returnLabel
  | returnHandler => apply Step.returnHandler
  | throwRefNull => apply Step.throwRefNull
  | throwRefInstrs => exact Step.throwRefInstrs ‹_›
  | throwRefLabel => apply Step.throwRefLabel
  | throwRefFrame => apply Step.throwRefFrame
  | throwRefHandlerEmpty => apply Step.throwRefHandlerEmpty
  | throwRefHandlerCatch => apply Step.throwRefHandlerCatch <;> assumption
  | throwRefHandlerCatchRef => apply Step.throwRefHandlerCatchRef <;> assumption
  | throwRefHandlerCatchAll => apply Step.throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => apply Step.throwRefHandlerCatchAllRef
  | tryTable => apply Step.tryTable <;> assumption
  | handlerVals => apply Step.handlerVals
  | trapInstrs => exact Step.trapInstrs ‹_›
  | trapLabel => apply Step.trapLabel
  | trapHandler => apply Step.trapHandler
  | trapFrame => apply Step.trapFrame

/-- Host-free runs commute with changing the host type. -/
theorem Steps.mapH {c c' : Config H} (h : Steps P (noHostH H) c c') :
    Steps P (noHostH H') (Config.mapH g c) (Config.mapH g c') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (Step.mapH g hs)

/-- Host-free divergence is carried over by changing the host type. -/
theorem Diverges.mapH {c : Config H} (h : Diverges P (noHostH H) c) :
    Diverges P (noHostH H') (Config.mapH g c) :=
  Silmaril.InfiniteTrace.map (f := Config.mapH g) (fun _ _ hs => Step.mapH g hs) h

/-! ## Instantiation -/

/-- Change the host type of the store of an optional result. -/
def mapS {α : Type} : Option (Store H × α) → Option (Store H' × α) :=
  Option.map fun p => (Store.mapH g p.1, p.2)

@[simp] theorem mapS_some {α} (s : Store H) (a : α) : mapS g (some (s, a)) = some (Store.mapH g s, a) := rfl
@[simp] theorem mapS_none {α} : mapS (α := α) g (none : Option (Store H × α)) = none := rfl
@[simp] theorem mapH_globals (s : Store H) : (Store.mapH g s).globals = s.globals := rfl
@[simp] theorem mapH_structs (s : Store H) : (Store.mapH g s).structs = s.structs := rfl
@[simp] theorem mapH_arrays (s : Store H) : (Store.mapH g s).arrays = s.arrays := rfl
@[simp] theorem global?_mapH (s : Store H) f x : (Store.mapH g s).global? f x = s.global? f x := rfl
@[simp] theorem addStruct_mapH (s : Store H) si : (Store.mapH g s).addStruct si = Store.mapH g (s.addStruct si) := rfl
@[simp] theorem addArray_mapH (s : Store H) si : (Store.mapH g s).addArray si = Store.mapH g (s.addArray si) := rfl

@[simp] theorem mapS_bind {α β} (o : Option β) (k : β → Option (Store H × α)) :
    mapS g (o.bind k) = o.bind fun b => mapS g (k b) := by cases o <;> rfl
@[simp] theorem mapS_ite {α} (c : Prop) [Decidable c] (a b : Option (Store H × α)) :
    mapS g (if c then a else b) = if c then mapS g a else mapS g b := by split <;> rfl

theorem structNew?_mapH (s : Store H) f vs x : structNew? (Store.mapH g s) f vs x = mapS g (structNew? s f vs x) := by
  simp [structNew?]


theorem arrayNewFixed?_mapH (s : Store H) f vs x n : arrayNewFixed? (Store.mapH g s) f vs x n = mapS g (arrayNewFixed? s f vs x n) := by
  simp [arrayNewFixed?]

theorem constInstr?_mapH (s : Store H) f vs i : constInstr? (Store.mapH g s) f vs i = mapS g (constInstr? s f vs i) := by
  cases i <;> simp only [constInstr?, structNew?_mapH, arrayNewFixed?_mapH, mapS_bind, mapS_some,
    mapS_none, mapS_ite, global?_mapH, Option.bind_eq_bind] <;>
    first
      | (congr 1; funext p; split <;> (try split_ifs) <;> rfl)
      | (split_ifs <;> first | rfl | (congr 1; funext p; congr 1; funext x; congr 1; funext y; split <;> rfl))

theorem constExpr?_mapH (s : Store H) f e : constExpr? (Store.mapH g s) f e = mapS g (constExpr? s f e) := by
  unfold constExpr?
  generalize ([] : List Val) = vs
  induction e generalizing s vs with
  | nil => rfl
  | cons i e ih =>
    simp only [List.foldlM_cons, constInstr?_mapH]
    cases constInstr? s f vs i with
    | none => rfl
    | some p => exact ih p.1 p.2

theorem evalConst?_mapH (s : Store H) f e : evalConst? (Store.mapH g s) f e = mapS g (evalConst? s f e) := by
  unfold evalConst?
  rw [constExpr?_mapH]
  cases constExpr? s f e with
  | none => rfl
  | some p =>
    obtain ⟨s', vs⟩ := p
    match vs with
    | [] => rfl
    | [v] => rfl
    | _ :: _ :: _ => rfl

/-- The frame after allocating one global. -/
abbrev withGlobal (f : Frame) (a : Nat) : Frame :=
  { f with module := { f.module with globals := f.module.globals ++ [a] } }

/-- Consing a value onto the result commutes with `mapS`. -/
theorem mapS_consVal (o : Option (Store H × Frame × List Val)) (v : Val) :
    (match mapS g o with | none => none | some (s'', f'', vs) => some (s'', f'', v :: vs)) =
      mapS g (match o with | none => none | some (s'', f'', vs) => some (s'', f'', v :: vs)) := by
  rcases o with _ | ⟨s'', f'', vs⟩ <;> rfl

theorem evalGlobals?_mapH (s : Store H) f gs es :
    evalGlobals? evalConst? (Store.mapH g s) f gs es = mapS g (evalGlobals? evalConst? s f gs es) := by
  induction gs generalizing s f es with
  | nil => cases es <;> rfl
  | cons gt gs ih =>
    cases es with
    | nil => rfl
    | cons e es =>
      simp only [evalGlobals?, evalConst?_mapH]
      rcases evalConst? s f e with _ | ⟨s', v⟩
      · rfl
      · have hf := ih (allocGlobal s' gt v).1 (withGlobal f (allocGlobal s' gt v).2) es
        exact (congrArg (fun o => match o with
          | none => none | some (s'', f'', vs) => some (s'', f'', v :: vs)) hf).trans
          (mapS_consVal g _ v)

theorem evalExprs?_mapH (s : Store H) f es :
    evalExprs? evalConst? (Store.mapH g s) f es = mapS g (evalExprs? evalConst? s f es) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    simp only [evalExprs?, evalConst?_mapH]
    rcases evalConst? s f e with _ | ⟨s', _ | _ | r⟩ <;> try rfl
    simp only [mapS_some, ih]
    rcases evalExprs? evalConst? s' f es with _ | ⟨s'', f'', rs⟩ <;> rfl

theorem evalExprss?_mapH (s : Store H) f ess :
    evalExprss? evalConst? (Store.mapH g s) f ess = mapS g (evalExprss? evalConst? s f ess) := by
  induction ess generalizing s f with
  | nil => rfl
  | cons es ess ih =>
    simp only [evalExprss?, evalExprs?_mapH]
    rcases evalExprs? evalConst? s f es with _ | ⟨s', f', rs⟩ <;> try rfl
    simp only [mapS_some, ih]
    rcases evalExprss? evalConst? s' f' ess with _ | ⟨s'', f'', rss⟩ <;> rfl

theorem allocMany_mapH {α : Type} (alloc : ∀ {H : Type}, Store H → α → Store H × Nat)
    (h : ∀ (s : Store H) x, alloc (Store.mapH g s) x = (Store.mapH g (alloc s x).1, (alloc s x).2))
    (s : Store H) (xs : List α) :
    allocMany alloc (Store.mapH g s) xs =
      (Store.mapH g (allocMany alloc s xs).1, (allocMany alloc s xs).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [allocMany, h, ih]

@[simp] theorem mapH_funcs_length (s : Store H) : (Store.mapH g s).funcs.length = s.funcs.length := by
  simp [Store.mapH]

theorem allocFunc_mapH (s : Store H) d (code : Func) mi :
    allocFunc (Store.mapH g s) d (.wasm code) mi =
      (Store.mapH g (allocFunc s d (.wasm code) mi).1, (allocFunc s d (.wasm code) mi).2) := by
  simp only [allocFunc, Store.mapH, List.map_append, List.map_cons, List.map_nil, List.length_map]
  rfl

theorem allocModule?_mapH (s : Store H) m xas valsG refsT refsE :
    allocModule? (Store.mapH g s) m xas valsG refsT refsE =
      mapS g (allocModule? s m xas valsG refsT refsE) := by
  simp only [allocModule?, mapH_funcs_length,
    allocMany_mapH g (fun s d => allocTag s d) (fun _ _ => rfl),
    allocMany_mapH g (fun s (p : CGlobalType × Val) => allocGlobal s p.1 p.2) (fun _ _ => rfl),
    allocMany_mapH g (fun s d => allocMem s d) (fun _ _ => rfl),
    allocMany_mapH g (fun s (p : CTableType × Ref) => allocTable s p.1 p.2) (fun _ _ => rfl),
    allocMany_mapH g (fun s d => allocData s d) (fun _ _ => rfl),
    allocMany_mapH g (fun s (p : CRefType × List Ref) => allocElem s p.1 p.2) (fun _ _ => rfl),
    Option.bind_eq_bind, mapS_bind]
  congr 1; funext tagTypes; congr 1; funext funcTypes; congr 1; funext xi
  rw [allocMany_mapH g (fun s (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) _)
    (fun _ _ => allocFunc_mapH g _ _ _ _)]
  rfl

theorem tableInitLoop_mapH (s : Store H) f x y a i j n :
    tableInitLoop (Store.mapH g s) f x y a i j n = (tableInitLoop s f x y a i j n).map (Store.mapH g) := by
  induction hn : n.toNat using Nat.strong_induction_on generalizing s i j n with
  | _ k ih =>
    rw [tableInitLoop, tableInitLoop]
    show (match s.table? f x, s.elem? f y with
      | some (ta, ti), some (_, ei) => _ | _, _ => none) = _
    rcases s.table? f x with _ | ⟨ta, ti⟩ <;> rcases s.elem? f y with _ | ⟨_, ei⟩ <;> try rfl
    dsimp only
    split_ifs with h₁ h₂
    · rfl
    · rcases ei.refs[j.toNat]? with _ | r
      · rfl
      · exact ih _ (hn ▸ bv32_sub_one_lt h₂) (s.setTable ta _) _ _ _ rfl
    · rfl

theorem memoryInitLoop_mapH (s : Store H) f x y a i j n :
    memoryInitLoop (Store.mapH g s) f x y a i j n = (memoryInitLoop s f x y a i j n).map (Store.mapH g) := by
  induction hn : n.toNat using Nat.strong_induction_on generalizing s i j n with
  | _ k ih =>
    rw [memoryInitLoop, memoryInitLoop]
    show (match s.mem? f x, s.data? f y with
      | some (ma, mi), some (_, di) => _ | _, _ => none) = _
    rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> rcases s.data? f y with _ | ⟨_, di⟩ <;> try rfl
    dsimp only
    split_ifs with h₁ h₂
    · rfl
    · rcases di.bytes.data[j.toNat]? with _ | byte
      · rfl
      · dsimp only
        split
        · exact ih _ (hn ▸ bv32_sub_one_lt h₂) (s.setMem ma _) _ _ _ rfl
        · rfl
    · rfl

theorem initElemSeg?_mapH (s : Store H) f k e :
    initElemSeg? evalConst? (Store.mapH g s) f k e = (initElemSeg? evalConst? s f k e).map (Store.mapH g) := by
  unfold initElemSeg?
  split
  · rfl
  · simp only [elemDrop?, Option.map_map]; rfl
  · rw [evalConst?_mapH]
    rcases evalConst? s f _ with _ | ⟨s₁, v⟩
    · rfl
    · dsimp only [mapS_some]
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · dsimp only
        rw [tableInitLoop_mapH]
        rcases tableInitLoop s₁ f _ _ a i 0 _ with _ | s₂
        · rfl
        · simp only [Option.map_some, elemDrop?, Option.map_map]; rfl

theorem initDataSeg?_mapH (s : Store H) f k d :
    initDataSeg? evalConst? (Store.mapH g s) f k d = (initDataSeg? evalConst? s f k d).map (Store.mapH g) := by
  unfold initDataSeg?
  split
  · rfl
  · rw [evalConst?_mapH]
    rcases evalConst? s f _ with _ | ⟨s₁, v⟩
    · rfl
    · dsimp only [mapS_some]
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · dsimp only
        rw [memoryInitLoop_mapH]
        rcases memoryInitLoop s₁ f _ _ a i 0 _ with _ | s₂
        · rfl
        · simp only [Option.map_some, dataDrop?, Option.map_map]; rfl

theorem initElemList?_mapH (s : Store H) f es :
    initElemList? evalConst? (Store.mapH g s) f es = (initElemList? evalConst? s f es).map (Store.mapH g) := by
  induction es generalizing s with
  | nil => rfl
  | cons p es ih =>
    obtain ⟨k, e⟩ := p
    simp only [initElemList?, initElemSeg?_mapH]
    rcases initElemSeg? evalConst? s f k e with _ | s₁
    · rfl
    · exact ih s₁

theorem initDataList?_mapH (s : Store H) f ds :
    initDataList? evalConst? (Store.mapH g s) f ds = (initDataList? evalConst? s f ds).map (Store.mapH g) := by
  induction ds generalizing s with
  | nil => rfl
  | cons p ds ih =>
    obtain ⟨k, d⟩ := p
    simp only [initDataList?, initDataSeg?_mapH]
    rcases initDataSeg? evalConst? s f k d with _ | s₁
    · rfl
    · exact ih s₁

theorem initSegments?_mapH (s : Store H) f m :
    initSegments? evalConst? (Store.mapH g s) f m = mapS g (initSegments? evalConst? s f m) := by
  simp only [initSegments?, initElem?, initData?, initElemList?_mapH]
  rcases initElemList? evalConst? s f _ with _ | s₁
  · rfl
  · simp only [Option.map_some, initDataList?_mapH]
    rcases initDataList? evalConst? s₁ f _ with _ | s₂ <;> rfl

theorem initial_mapH (s : Store H) m xas :
    ModuleInst.initial (Store.mapH g s) m xas = ModuleInst.initial s m xas := by
  simp only [ModuleInst.initial, mapH_funcs_length]

/-- `mapS` on configurations. -/
def mapC {α : Type} : Option (Config H × α) → Option (Config H' × α) :=
  Option.map fun p => (Config.mapH g p.1, p.2)

theorem prepare?_mapH (s : Store H) m xas :
    prepare? evalConst? (Store.mapH g s) m xas = mapC g (prepare? evalConst? s m xas) := by
  unfold prepare?
  split_ifs
  · rw [initial_mapH, evalGlobals?_mapH]
    rcases evalGlobals? evalConst? s _ _ _ with _ | ⟨s₁, f₁, valsG⟩
    · rfl
    · dsimp only [mapS_some]
      rw [evalExprs?_mapH]
      rcases evalExprs? evalConst? s₁ f₁ _ with _ | ⟨s₂, f₂, refsT⟩
      · rfl
      · dsimp only [mapS_some]
        rw [evalExprss?_mapH]
        rcases evalExprss? evalConst? s₂ f₂ _ with _ | ⟨s₃, f₃, refsE⟩
        · rfl
        · dsimp only [mapS_some]
          rw [allocModule?_mapH]
          rcases allocModule? s₃ m xas valsG refsT refsE with _ | ⟨s₄, mi⟩ <;> rfl
  · rfl

theorem instantiateDirect?_mapH (s : Store H) m xas :
    instantiateDirect? (Store.mapH g s) m xas = mapS g (instantiateDirect? s m xas) := by
  simp only [instantiateDirect?, prepareDirect?, prepare?_mapH]
  rcases prepare? evalConst? s m xas with _ | ⟨c, st⟩
  · rfl
  · show (match initSegments? evalConst? (Store.mapH g c.store) c.frame m with
      | none => none | some (s', f') => some (s', f', st)) =
      mapS g (match initSegments? evalConst? c.store c.frame m with
      | none => none | some (s', f') => some (s', f', st))
    rw [initSegments?_mapH]
    rcases initSegments? evalConst? c.store c.frame m with _ | ⟨s', f'⟩ <;> rfl

theorem mapH_globals_length (s : Store H) : (Store.mapH g s).globals.length = s.globals.length := rfl

/-- **Instantiation commutes with changing the host type.** -/
theorem instantiateOnce?_mapH (s : Store H) m xas :
    instantiateOnce? (Store.mapH g s) m xas = mapS g (instantiateOnce? s m xas) := by
  unfold instantiateOnce?
  rw [initial_mapH, evalGlobals?_mapH]
  rcases evalGlobals? evalConst? s _ _ _ with _ | ⟨s₁, f₁, vs⟩
  · rfl
  · exact instantiateDirect?_mapH g s₁ _ _


theorem invoke_mapH (s : Store H) (a : Nat) (vs : List Val) :
    Config.mapH g (invoke s a vs) = invoke (Store.mapH g s) a vs := by
  simp only [Config.mapH, invoke, Store.mapH_funcs_getElem?, Option.map_map]
  rfl

theorem empty_mapH : Store.mapH g ({} : Store H) = ({} : Store H') := rfl


/-- The game semantics instantiates import-free modules in the empty `Store Nat`. -/
theorem importStore_nil : Silmaril.Wasm.Game.importStore [] = ({} : Store Nat) := rfl

/-- **The instance store of the game semantics is the host-renamed instance store at any host
type**: instantiating an import-free module in `importStore []` is instantiating it in the
empty `Store H` and renaming the host code. -/
theorem instantiateOnce?_importStore (g : H → Nat) (m : Module) :
    instantiateOnce? (Silmaril.Wasm.Game.importStore []) m [] =
      mapS g (instantiateOnce? ({} : Store H) m []) := by
  rw [importStore_nil, ← empty_mapH g]
  exact instantiateOnce?_mapH g _ m []

/-- A host-free Core run from an invocation, carried to the renamed store. -/
theorem invoke_steps_mapH {s : Store H} {a : Nat} {xs : List Val} {c' : Config H}
    (h : Steps P (noHostH H) (invoke s a xs) c') :
    Steps P (noHostH H') (invoke (Store.mapH g s) a xs) (Config.mapH g c') := by
  rw [← invoke_mapH]
  exact Steps.mapH g h

/-- A host-free divergent invocation, carried to the renamed store. -/
theorem invoke_diverges_mapH {s : Store H} {a : Nat} {xs : List Val}
    (h : Diverges P (noHostH H) (invoke s a xs)) :
    Diverges P (noHostH H') (invoke (Store.mapH g s) a xs) := by
  rw [← invoke_mapH]
  exact Diverges.mapH g h

end Silmaril.Proofs.Wasm.Component.Reference
