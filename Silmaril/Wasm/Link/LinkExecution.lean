module

public import Silmaril.Wasm.Link.GC
public import Silmaril.Wasm.Execution.Core.Step

/-! # Operational transport of relocated leaf instructions

A module correspondence relates the linker's actual partial index maps to
runtime lookups. Relocated instructions resolve the same function/global
addresses and the same closed GC type tags. The leaf rules below therefore
preserve their results, mutations and allocation addresses in a shared store.

This is the instruction-level part of a static-linking proof. It does not yet
identify the instances obtained by separately preparing two source modules
with the instance of `link?`: that needs recursive-type allocation agreement,
initializer/store correspondence, and transport of stored function bodies and
administrative call frames. No execution-preservation premise is hidden in the
lookup correspondence.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.LinkExecution

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The partial source-index relocation preserves runtime lookup results.
This is a syntactic/data relation, independent of the execution relation. -/
structure Correspondence (r : Relocation) (source target : ModuleInst) : Prop where
  functions : ∀ {x y : FuncIdx}, function? r x = some y → target.funcs[y.toNat]? = source.funcs[x.toNat]?
  globals : ∀ {x y : GlobalIdx}, shiftIdx? r.globals x = some y → target.globals[y.toNat]? = source.globals[x.toNat]?
  types : ∀ {x y : TypeIdx}, shiftIdx? r.types x = some y → target.types[y.toNat]? = source.types[x.toNat]?

/-- Module indices change; locals and all references keep their values. -/
def frame (target : ModuleInst) (f : Frame) : Frame := {f with module := target}

theorem shiftIdx?_toNat {kind : IndexKind} {offset : Nat} {x y : Idx kind}
    (h : shiftIdx? offset x = some y) : y.toNat = offset+x.toNat :=
  ((Idx.ofNat?_eq_some_iff _ _).mp h).symm

/-- Prefixing runtime index spaces gives a concrete correspondence for
arbitrary nonzero offsets. It requires no boundedness assumption beyond the
partial relocation succeeding at each index being transported. -/
theorem correspondence_prefix (source : ModuleInst) (types : List DefType)
    (functions globals : List Nat) :
    Correspondence ⟨types.length,functions.length,globals.length,[]⟩ source
      {source with
        types := types ++ source.types
        funcs := functions ++ source.funcs
        globals := globals ++ source.globals} := by
  refine ⟨?_,?_,?_⟩
  · intro x y h
    have h' : Idx.ofNat? (functions.length+x.toNat) = some y := by
      simpa only [function?,List.length_nil,Nat.not_lt_zero,ite_false,Nat.sub_zero] using h
    rw [((Idx.ofNat?_eq_some_iff _ _).mp h').symm]
    rw [List.getElem?_append_right (Nat.le_add_right _ _)]
    simp
  · intro x y h
    rw [shiftIdx?_toNat h]
    rw [List.getElem?_append_right (Nat.le_add_right _ _)]
    simp
  · intro x y h
    rw [shiftIdx?_toNat h]
    rw [List.getElem?_append_right (Nat.le_add_right _ _)]
    simp

theorem Correspondence.type_lookup {r : Relocation} {f : Frame} {target : ModuleInst} {x y : TypeIdx}
    {d : DefType} (h : Correspondence r f.module target) (hr : shiftIdx? r.types x = some y)
    (hd : f.type? x = some d) : (frame target f).type? y = some d :=
  (h.types hr).trans hd

theorem Correspondence.global_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : GlobalIdx} (h : Correspondence r f.module target) (hr : shiftIdx? r.globals x = some y) :
    s.global? (frame target f) y = s.global? f x := by
  simp only [Store.global?,frame,h.globals hr]

/-- Relocated direct calls dispatch to exactly the same function address and
closed call tag. Transport of the callee's stored body is a separate layer. -/
theorem call_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hy : target.funcs[y.toNat]? = some a) (hr : function? r x = some y)
    (hf : s.funcs[a]? = some fi) :
    instruction? r (.call x) = some (.call y) ∧
      Step P host ⟨s,frame target f,[.plain (.call y)]⟩
        ⟨s,frame target f,[.ref (.func a),.callRefType fi.type]⟩ :=
  ⟨by simp [instruction?,hr],.call hy hf⟩

theorem call_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : FuncIdx} {a : Nat} {fi : FuncInst H}
    (h : Correspondence r f.module target) (hr : function? r x = some y)
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
    instruction? r (.call x) = some (.call y) ∧
      Step P host ⟨s,frame target f,[.plain (.call y)]⟩
        ⟨s,frame target f,[.ref (.func a),.callRefType fi.type]⟩ :=
  call_transport_of_lookup ((h.functions hr).trans hx) hr hf

theorem refFunc_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : FuncIdx} {a : Nat} (hy : target.funcs[y.toNat]? = some a)
    (hr : function? r x = some y) :
    instruction? r (.refFunc x) = some (.refFunc y) ∧
      Step P host ⟨s,frame target f,[.plain (.refFunc y)]⟩ ⟨s,frame target f,[.ref (.func a)]⟩ :=
  ⟨by simp [instruction?,hr],.reference (.refFunc hy)⟩

theorem refFunc_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : FuncIdx} {a : Nat} (h : Correspondence r f.module target)
    (hr : function? r x = some y) (hx : f.module.funcs[x.toNat]? = some a) :
    instruction? r (.refFunc x) = some (.refFunc y) ∧
      Step P host ⟨s,frame target f,[.plain (.refFunc y)]⟩ ⟨s,frame target f,[.ref (.func a)]⟩ :=
  refFunc_transport_of_lookup ((h.functions hr).trans hx) hr

theorem globalGet_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst} (hy : s.global? (frame target f) y = some (a,g))
    (hr : shiftIdx? r.globals x = some y) :
    instruction? r (.globalGet x) = some (.globalGet y) ∧
      Step P host ⟨s,frame target f,[.plain (.globalGet y)]⟩ ⟨s,frame target f,[g.value.toAdmin]⟩ :=
  ⟨by simp [instruction?,hr],.variable (.globalGet hy)⟩

theorem globalGet_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst} (h : Correspondence r f.module target)
    (hr : shiftIdx? r.globals x = some y) (hg : s.global? f x = some (a,g)) :
    instruction? r (.globalGet x) = some (.globalGet y) ∧
      Step P host ⟨s,frame target f,[.plain (.globalGet y)]⟩ ⟨s,frame target f,[g.value.toAdmin]⟩ :=
  globalGet_transport_of_lookup ((h.global_lookup hr).trans hg) hr

theorem globalSet_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst} (v : Val) (hy : s.global? (frame target f) y = some (a,g))
    (hr : shiftIdx? r.globals x = some y) :
    instruction? r (.globalSet x) = some (.globalSet y) ∧
      Step P host ⟨s,frame target f,[v.toAdmin,.plain (.globalSet y)]⟩
        ⟨s.setGlobal a v,frame target f,[]⟩ :=
  ⟨by simp [instruction?,hr],.variable (.globalSet hy)⟩

theorem globalSet_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst} (v : Val) (h : Correspondence r f.module target)
    (hr : shiftIdx? r.globals x = some y) (hg : s.global? f x = some (a,g)) :
    instruction? r (.globalSet x) = some (.globalSet y) ∧
      Step P host ⟨s,frame target f,[v.toAdmin,.plain (.globalSet y)]⟩
        ⟨s.setGlobal a v,frame target f,[]⟩ :=
  globalSet_transport_of_lookup v ((h.global_lookup hr).trans hg) hr

/-- Closed GC-tag agreement preserves fresh allocation at the same heap
address, including the exact fields packed by the real `struct.new` rule. -/
theorem structNew_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {d : DefType} {fields : Ty (.list .field)} {vs : List Val}
    (hy : (frame target f).type? y = some d) (hr : shiftIdx? r.types x = some y)
    (he : Expand d (.struct fields)) (hn : vs.length = fields.length)
    (hp : ∀ p ∈ fields.toList.zip vs,packable (fieldStorage p.1) p.2) :
    instruction? r (.structNew x) = some (.structNew y) ∧
      Step P host ⟨s,frame target f,vals vs ++ [.plain (.structNew y)]⟩
        ⟨s.addStruct ⟨d,(fields.toList.zip vs).map fun (ft,v) => packField (fieldStorage ft) v⟩,
          frame target f,[.ref (.struct s.structs.length)]⟩ :=
  ⟨by simp [instruction?,hr],.aggregate (.structNew hy he hn hp)⟩

theorem structNew_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {d : DefType} {fields : Ty (.list .field)} {vs : List Val}
    (h : Correspondence r f.module target) (hr : shiftIdx? r.types x = some y)
    (hd : f.type? x = some d) (he : Expand d (.struct fields)) (hn : vs.length = fields.length)
    (hp : ∀ p ∈ fields.toList.zip vs,packable (fieldStorage p.1) p.2) :
    instruction? r (.structNew x) = some (.structNew y) ∧
      Step P host ⟨s,frame target f,vals vs ++ [.plain (.structNew y)]⟩
        ⟨s.addStruct ⟨d,(fields.toList.zip vs).map fun (ft,v) => packField (fieldStorage ft) v⟩,
          frame target f,[.ref (.struct s.structs.length)]⟩ :=
  structNew_transport_of_lookup (h.type_lookup hr hd) hr he hn hp

theorem structGet_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {sx : Option Signedness} {field : FieldIdx} {a : Nat} {si : StructInst} {fv : FieldVal}
    {d : DefType} {fields : Ty (.list .field)} {ft : CFieldType}
    (hy : (frame target f).type? y = some d) (hr : shiftIdx? r.types x = some y)
    (hs : s.structs[a]? = some si) (hf : si.fields[field.toNat]? = some fv)
    (he : Expand d (.struct fields)) (hi : fields.toList[field.toNat]? = some ft)
    (hu : unpackable (fieldStorage ft) sx fv) :
    instruction? r (.structGet sx x field) = some (.structGet sx y field) ∧
      Step P host ⟨s,frame target f,[.ref (.struct a),.plain (.structGet sx y field)]⟩
        ⟨s,frame target f,[(unpackField sx fv).toAdmin]⟩ :=
  ⟨by simp [instruction?,hr],.aggregate (.structGetStruct hs hf hy he hi hu)⟩

theorem structGet_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {sx : Option Signedness} {field : FieldIdx} {a : Nat} {si : StructInst} {fv : FieldVal}
    {d : DefType} {fields : Ty (.list .field)} {ft : CFieldType}
    (h : Correspondence r f.module target) (hr : shiftIdx? r.types x = some y)
    (hs : s.structs[a]? = some si) (hf : si.fields[field.toNat]? = some fv)
    (hd : f.type? x = some d) (he : Expand d (.struct fields)) (hi : fields.toList[field.toNat]? = some ft)
    (hu : unpackable (fieldStorage ft) sx fv) :
    instruction? r (.structGet sx x field) = some (.structGet sx y field) ∧
      Step P host ⟨s,frame target f,[.ref (.struct a),.plain (.structGet sx y field)]⟩
        ⟨s,frame target f,[(unpackField sx fv).toAdmin]⟩ :=
  structGet_transport_of_lookup (h.type_lookup hr hd) hr hs hf he hi hu

theorem structSet_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {field : FieldIdx} {a : Nat} {si : StructInst} {v : Val}
    {d : DefType} {fields : Ty (.list .field)} {ft : CFieldType}
    (hy : (frame target f).type? y = some d) (hr : shiftIdx? r.types x = some y)
    (he : Expand d (.struct fields)) (hi : fields.toList[field.toNat]? = some ft)
    (hs : s.structs[a]? = some si) (hf : field.toNat < si.fields.length) (hp : packable (fieldStorage ft) v) :
    instruction? r (.structSet x field) = some (.structSet y field) ∧
      Step P host ⟨s,frame target f,[.ref (.struct a),v.toAdmin,.plain (.structSet y field)]⟩
        ⟨s.setStructField a field.toNat (packField (fieldStorage ft) v),frame target f,[]⟩ :=
  ⟨by simp [instruction?,hr],.aggregate (.structSetStruct hy he hi hs hf hp)⟩

theorem structSet_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {field : FieldIdx} {a : Nat} {si : StructInst} {v : Val}
    {d : DefType} {fields : Ty (.list .field)} {ft : CFieldType}
    (h : Correspondence r f.module target) (hr : shiftIdx? r.types x = some y)
    (hd : f.type? x = some d) (he : Expand d (.struct fields)) (hi : fields.toList[field.toNat]? = some ft)
    (hs : s.structs[a]? = some si) (hf : field.toNat < si.fields.length) (hp : packable (fieldStorage ft) v) :
    instruction? r (.structSet x field) = some (.structSet y field) ∧
      Step P host ⟨s,frame target f,[.ref (.struct a),v.toAdmin,.plain (.structSet y field)]⟩
        ⟨s.setStructField a field.toNat (packField (fieldStorage ft) v),frame target f,[]⟩ :=
  structSet_transport_of_lookup (h.type_lookup hr hd) hr he hi hs hf hp

theorem arrayNewFixed_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {n : Fin (2^32)} {d : DefType} {ft : CFieldType} {vs : List Val}
    (hy : (frame target f).type? y = some d) (hr : shiftIdx? r.types x = some y)
    (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs,packable (fieldStorage ft) v) :
    instruction? r (.arrayNewFixed x n) = some (.arrayNewFixed y n) ∧
      Step P host ⟨s,frame target f,vals vs ++ [.plain (.arrayNewFixed y n)]⟩
        ⟨s.addArray ⟨d,vs.map (packField (fieldStorage ft))⟩,frame target f,[arrRef s.arrays.length]⟩ :=
  ⟨by simp [instruction?,hr],.aggregate (.arrayNewFixed hy he hn hp)⟩

theorem arrayNewFixed_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {n : Fin (2^32)} {d : DefType} {ft : CFieldType} {vs : List Val}
    (h : Correspondence r f.module target) (hr : shiftIdx? r.types x = some y)
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hn : vs.length = n.val)
    (hp : ∀ v ∈ vs,packable (fieldStorage ft) v) :
    instruction? r (.arrayNewFixed x n) = some (.arrayNewFixed y n) ∧
      Step P host ⟨s,frame target f,vals vs ++ [.plain (.arrayNewFixed y n)]⟩
        ⟨s.addArray ⟨d,vs.map (packField (fieldStorage ft))⟩,frame target f,[arrRef s.arrays.length]⟩ :=
  arrayNewFixed_transport_of_lookup (h.type_lookup hr hd) hr he hn hp

theorem arrayGet_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {sx : Option Signedness} {i : BitVec 32} {a : Nat} {ai : ArrayInst} {fv : FieldVal}
    {d : DefType} {ft : CFieldType} (hy : (frame target f).type? y = some d)
    (hr : shiftIdx? r.types x = some y) (ha : s.arrays[a]? = some ai)
    (hi : ai.fields[i.toNat]? = some fv) (he : Expand d (.array ft))
    (hu : unpackable (fieldStorage ft) sx fv) :
    instruction? r (.arrayGet sx x) = some (.arrayGet sx y) ∧
      Step P host ⟨s,frame target f,[arrRef a,constI32 i,.plain (.arrayGet sx y)]⟩
        ⟨s,frame target f,[(unpackField sx fv).toAdmin]⟩ :=
  ⟨by simp [instruction?,hr],.aggregate (.arrayGetArray ha hi hy he hu)⟩

theorem arrayGet_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {sx : Option Signedness} {i : BitVec 32} {a : Nat} {ai : ArrayInst} {fv : FieldVal}
    {d : DefType} {ft : CFieldType} (h : Correspondence r f.module target)
    (hr : shiftIdx? r.types x = some y) (ha : s.arrays[a]? = some ai)
    (hi : ai.fields[i.toNat]? = some fv) (hd : f.type? x = some d) (he : Expand d (.array ft))
    (hu : unpackable (fieldStorage ft) sx fv) :
    instruction? r (.arrayGet sx x) = some (.arrayGet sx y) ∧
      Step P host ⟨s,frame target f,[arrRef a,constI32 i,.plain (.arrayGet sx y)]⟩
        ⟨s,frame target f,[(unpackField sx fv).toAdmin]⟩ :=
  arrayGet_transport_of_lookup (h.type_lookup hr hd) hr ha hi he hu

theorem arraySet_transport_of_lookup {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {i : BitVec 32} {a : Nat} {ai : ArrayInst} {v : Val} {d : DefType} {ft : CFieldType}
    (hy : (frame target f).type? y = some d) (hr : shiftIdx? r.types x = some y)
    (ha : s.arrays[a]? = some ai) (hi : i.toNat < ai.fields.length)
    (he : Expand d (.array ft)) (hp : packable (fieldStorage ft) v) :
    instruction? r (.arraySet x) = some (.arraySet y) ∧
      Step P host ⟨s,frame target f,[arrRef a,constI32 i,v.toAdmin,.plain (.arraySet y)]⟩
        ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v),frame target f,[]⟩ :=
  ⟨by simp [instruction?,hr],.aggregate (.arraySetArray ha hi hy he hp)⟩

theorem arraySet_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {i : BitVec 32} {a : Nat} {ai : ArrayInst} {v : Val} {d : DefType} {ft : CFieldType}
    (h : Correspondence r f.module target) (hr : shiftIdx? r.types x = some y)
    (ha : s.arrays[a]? = some ai) (hi : i.toNat < ai.fields.length)
    (hd : f.type? x = some d) (he : Expand d (.array ft)) (hp : packable (fieldStorage ft) v) :
    instruction? r (.arraySet x) = some (.arraySet y) ∧
      Step P host ⟨s,frame target f,[arrRef a,constI32 i,v.toAdmin,.plain (.arraySet y)]⟩
        ⟨s.setArrayField a i.toNat (packField (fieldStorage ft) v),frame target f,[]⟩ :=
  arraySet_transport_of_lookup (h.type_lookup hr hd) hr ha hi he hp

theorem instRef_type_of_lookup {source target : ModuleInst} {x y : TypeIdx}
    {d : DefType} (nullable : Bool) (hd' : target.types[y.toNat]? = some d)
    (hd : source.types[x.toNat]? = some d) :
    target.instRef ⟨nullable,.typeIdx y⟩ = source.instRef ⟨nullable,.typeIdx x⟩ := by
  simp [ModuleInst.instRef,liftRef,liftHeap,liftTypeIdx,Ty.substAll,Ty.subst,Subst.all,
    List.getElem?_map,hd,hd']

theorem Correspondence.instRef_type {r : Relocation} {source target : ModuleInst} {x y : TypeIdx}
    {d : DefType} (nullable : Bool) (h : Correspondence r source target)
    (hr : shiftIdx? r.types x = some y) (hd : source.types[x.toNat]? = some d) :
    target.instRef ⟨nullable,.typeIdx y⟩ = source.instRef ⟨nullable,.typeIdx x⟩ :=
  instRef_type_of_lookup nullable ((h.types hr).trans hd) hd

/-- The same closed type tag preserves both successful and failing casts;
relocation cannot turn a rejected reference into an accepted reference. -/
theorem refCast_transport_of_tag {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {value : Ref} (nullable : Bool)
    (htag : target.instRef ⟨nullable,.typeIdx y⟩ = f.module.instRef ⟨nullable,.typeIdx x⟩) (hr : shiftIdx? r.types x = some y)
    (hv : RefOk s value (f.module.instRef ⟨nullable,.typeIdx x⟩)) :
    instruction? r (.refCast ⟨nullable,.typeIdx x⟩) = some (.refCast ⟨nullable,.typeIdx y⟩) ∧
      Step P host ⟨s,frame target f,[.ref value,.plain (.refCast ⟨nullable,.typeIdx y⟩)]⟩
        ⟨s,frame target f,[.ref value]⟩ := by
  refine ⟨by simp [instruction?,refType?,heap?,hr],.reference (.castSucceed ?_)⟩
  change RefOk s value (target.instRef ⟨nullable,.typeIdx y⟩)
  rw [htag]
  exact hv

theorem refCast_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {d : DefType} {value : Ref} (nullable : Bool)
    (h : Correspondence r f.module target) (hr : shiftIdx? r.types x = some y)
    (hd : f.type? x = some d) (hv : RefOk s value (f.module.instRef ⟨nullable,.typeIdx x⟩)) :
    instruction? r (.refCast ⟨nullable,.typeIdx x⟩) = some (.refCast ⟨nullable,.typeIdx y⟩) ∧
      Step P host ⟨s,frame target f,[.ref value,.plain (.refCast ⟨nullable,.typeIdx y⟩)]⟩
        ⟨s,frame target f,[.ref value]⟩ :=
  refCast_transport_of_tag nullable (h.instRef_type nullable hr hd) hr hv

theorem refCastFail_transport_of_tag {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {value : Ref} (nullable : Bool)
    (htag : target.instRef ⟨nullable,.typeIdx y⟩ = f.module.instRef ⟨nullable,.typeIdx x⟩) (hr : shiftIdx? r.types x = some y)
    (hv : ¬ RefOk s value (f.module.instRef ⟨nullable,.typeIdx x⟩)) :
    instruction? r (.refCast ⟨nullable,.typeIdx x⟩) = some (.refCast ⟨nullable,.typeIdx y⟩) ∧
      Step P host ⟨s,frame target f,[.ref value,.plain (.refCast ⟨nullable,.typeIdx y⟩)]⟩
        ⟨s,frame target f,[.trap]⟩ := by
  refine ⟨by simp [instruction?,refType?,heap?,hr],.reference (.castFail ?_)⟩
  change ¬ RefOk s value (target.instRef ⟨nullable,.typeIdx y⟩)
  rw [htag]
  exact hv

theorem refCastFail_transport {r : Relocation} {s : Store H} {f : Frame} {target : ModuleInst}
    {x y : TypeIdx} {d : DefType} {value : Ref} (nullable : Bool)
    (h : Correspondence r f.module target) (hr : shiftIdx? r.types x = some y)
    (hd : f.type? x = some d) (hv : ¬ RefOk s value (f.module.instRef ⟨nullable,.typeIdx x⟩)) :
    instruction? r (.refCast ⟨nullable,.typeIdx x⟩) = some (.refCast ⟨nullable,.typeIdx y⟩) ∧
      Step P host ⟨s,frame target f,[.ref value,.plain (.refCast ⟨nullable,.typeIdx y⟩)]⟩
        ⟨s,frame target f,[.trap]⟩ :=
  refCastFail_transport_of_tag nullable (h.instRef_type nullable hr hd) hr hv

end Silmaril.Wasm.Link.GC.LinkExecution
