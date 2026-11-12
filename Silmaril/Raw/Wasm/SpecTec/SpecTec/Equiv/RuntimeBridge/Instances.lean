module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.RuntimeBridge.Types
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.InstrEncoding

/-!
# The runtime bridge, layers 2 and 3: instances and configurations

The ten `*Inst` records, `ExportInst`, `ModuleInst`, and then `Frame`, `Store`
and `Config`.  Each is a `Value.struct` whose field names and order are those
of the pinned `1.4-runtime.spectec` declaration.

The field-by-field correspondence is the content of this file.  Silmaril's
records and the pinned ones were written independently and agree on the shape
of every one, including the order of the fields:

| Silmaril | IL | fields |
| --- | --- | --- |
| `Store` | `store` | TAGS GLOBALS MEMS TABLES FUNCS DATAS ELEMS STRUCTS ARRAYS EXNS |
| `ModuleInst` | `moduleinst` | TYPES TAGS GLOBALS MEMS TABLES FUNCS DATAS ELEMS EXPORTS |
| `Frame` | `frame` | LOCALS MODULE |
| `TagInst` | `taginst` | TYPE |
| `GlobalInst` | `globalinst` | TYPE VALUE |
| `MemInst` | `meminst` | TYPE BYTES |
| `TableInst` | `tableinst` | TYPE REFS |
| `FuncInst` | `funcinst` | TYPE MODULE CODE |
| `DataInst` | `datainst` | BYTES |
| `ElemInst` | `eleminst` | TYPE REFS |
| `StructInst` | `structinst` | TYPE FIELDS |
| `ArrayInst` | `arrayinst` | TYPE FIELDS |
| `ExnInst` | `exninst` | TAG FIELDS |
| `ExportInst` | `exportinst` | NAME ADDR |
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.RuntimeBridge

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core

/-! ## Layer 2 — the instance records

Each is a `Value.struct` whose field names and order are those of the pinned
`1.4-runtime.spectec` declaration, read off the table in this file's header. -/

variable (C : ClosedTypes)

/-- `taginst = {TYPE tagtype}`; `tagtype` aliases `typeuse`, and Silmaril
stores the defined type directly. -/
def tagInstToValue (t : TagInst) : Value := .struct [("TYPE", C.defType t.type)]

/-- `globalinst = {TYPE globaltype, VALUE val}`. -/
def globalInstToValue (g : GlobalInst) : Value :=
  .struct [("TYPE", C.globalType g.type), ("VALUE", valToValue g.value)]

/-- `meminst = {TYPE memtype, BYTES byte*}`. -/
def memInstToValue (m : MemInst) : Value :=
  .struct [("TYPE", Encode.toValue m.type), ("BYTES", bytesToValue m.bytes)]

/-- `tableinst = {TYPE tabletype, REFS ref*}`. -/
def tableInstToValue (t : TableInst) : Value :=
  .struct [("TYPE", C.tableType t.type), ("REFS", .list (t.refs.map refToValue))]

/-- `datainst = {BYTES byte*}`. -/
def dataInstToValue (d : DataInst) : Value := .struct [("BYTES", bytesToValue d.bytes)]

/-- `eleminst = {TYPE elemtype, REFS ref*}`. -/
def elemInstToValue (e : ElemInst) : Value :=
  .struct [("TYPE", C.elemType e.type), ("REFS", .list (e.refs.map refToValue))]

/-- `structinst = {TYPE deftype, FIELDS fieldval*}`. -/
def structInstToValue (s : StructInst) : Value :=
  .struct [("TYPE", C.defType s.type), ("FIELDS", .list (s.fields.map fieldValToValue))]

/-- `arrayinst = {TYPE deftype, FIELDS fieldval*}`. -/
def arrayInstToValue (a : ArrayInst) : Value :=
  .struct [("TYPE", C.defType a.type), ("FIELDS", .list (a.fields.map fieldValToValue))]

/-- `exninst = {TAG tagaddr, FIELDS val*}`. -/
def exnInstToValue (e : ExnInst) : Value :=
  .struct [("TAG", .num (.natN e.tag)), ("FIELDS", .list (e.fields.map valToValue))]

/-- `char = % nat` (`1.1-syntax.values`): a character is a `%`-wrapped code point. -/
def charToValue (c : Char) : Value := .case "%" (.tuple [.num (.natN c.toNat)])

/-- `name = % char*` (`1.1-syntax.values`): a one-case variant whose payload is the list of
characters. (Silmaril repair, upstream item U4 of `docs/projects/spectec/README.md`: the copy wrote the
name as `.text`, which no `name` is; that encoding is kept as `exportInstToValueText`.) -/
def nameToValue (n : String) : Value := .case "%" (.tuple [.list (n.toList.map charToValue)])

/-- `exportinst = {NAME name, ADDR externaddr}`. -/
def exportInstToValue (e : ExportInst) : Value :=
  .struct [("NAME", nameToValue e.name), ("ADDR", externAddrToValue e.addr)]

/-- The export encoding as copied from silmaril (`NAME` as a `.text`), kept as the documented
defect of upstream item U4: no value of this shape is an `exportinst`
(`ConfigOk.not_hasTyp_exportinstText`). -/
def exportInstToValueText (e : ExportInst) : Value :=
  .struct [("NAME", .text e.name), ("ADDR", externAddrToValue e.addr)]

/-- `moduleinst = {TYPES deftype*, TAGS tagaddr*, GLOBALS globaladdr*,
MEMS memaddr*, TABLES tableaddr*, FUNCS funcaddr*, DATAS dataaddr*,
ELEMS elemaddr*, EXPORTS exportinst*}` — nine fields, in that order. -/
def moduleInstToValue (m : ModuleInst) : Value :=
  .struct
    [("TYPES", .list (m.types.map C.defType)),
     ("TAGS", .list (m.tags.map fun a => .num (.natN a))),
     ("GLOBALS", .list (m.globals.map fun a => .num (.natN a))),
     ("MEMS", .list (m.mems.map fun a => .num (.natN a))),
     ("TABLES", .list (m.tables.map fun a => .num (.natN a))),
     ("FUNCS", .list (m.funcs.map fun a => .num (.natN a))),
     ("DATAS", .list (m.datas.map fun a => .num (.natN a))),
     ("ELEMS", .list (m.elems.map fun a => .num (.natN a))),
     ("EXPORTS", .list (m.exports.map (exportInstToValue)))]

/-- `funcinst = {TYPE deftype, MODULE moduleinst, CODE funccode}`.  The code
is `FUNC typeidx local* expr` or `_HOSTFUNC text`; the host case is
parameterised by `host`, because `Store` is parameterised by the host type and
the specification names a host function only by an opaque text. -/
def funcInstToValue {H : Type} (host : H → String) (f : FuncInst H) : Value :=
  .struct
    [("TYPE", C.defType f.type),
     ("MODULE", moduleInstToValue C f.module),
     ("CODE", match f.code with
        | .wasm fn => .case "FUNC" (.tuple
            [percentV (.num (.natN fn.type.toNat)),
             .list (fn.locals.map Encode.toValue),
             .list (fn.body.map Equiv.instrV)])
        | .host h => .case "_HOSTFUNC" (.text (host h)))]

/-! ## Layer 3 — the configurations -/

/-- `store = {TAGS …, GLOBALS …, MEMS …, TABLES …, FUNCS …, DATAS …,
ELEMS …, STRUCTS …, ARRAYS …, EXNS …}` — ten fields, in that order. -/
def storeToValue {H : Type} (host : H → String) (s : Store H) : Value :=
  .struct
    [("TAGS", .list (s.tags.map (tagInstToValue C))),
     ("GLOBALS", .list (s.globals.map (globalInstToValue C))),
     ("MEMS", .list (s.mems.map memInstToValue)),
     ("TABLES", .list (s.tables.map (tableInstToValue C))),
     ("FUNCS", .list (s.funcs.map (funcInstToValue C host))),
     ("DATAS", .list (s.datas.map dataInstToValue)),
     ("ELEMS", .list (s.elems.map (elemInstToValue C))),
     ("STRUCTS", .list (s.structs.map (structInstToValue C))),
     ("ARRAYS", .list (s.arrays.map (arrayInstToValue C))),
     ("EXNS", .list (s.exns.map exnInstToValue))]

/-- `frame = {LOCALS (val?)*, MODULE moduleinst}`. -/
def frameToValue (f : Frame) : Value :=
  .struct
    [("LOCALS", .list (f.locals.map fun o => .opt (o.map valToValue))),
     ("MODULE", moduleInstToValue C f.module)]

/-- `state = store; frame`, the `%;%` injection. -/
def stateToValue {H : Type} (host : H → String) (s : Store H) (f : Frame) : Value :=
  .case "%;%" (.tuple [storeToValue C host s, frameToValue C f])

/-- `config = state; instr*`.  The instruction list uses
`Equiv/Execution.lean`'s `adminsV?`, which is partial; a total `Admin`
encoding is layer 0 work that `Equiv/Execution.lean` left open. -/
def configToValue {H : Type} (host : H → String) (s : Store H) (f : Frame)
    (is : List Value) : Value :=
  .case "%;%" (.tuple [stateToValue C host s f, .list is])


/-! ### Injectivity, layer by layer

Each record's encoding is injective.  The leaf facts come from
`Equiv/RuntimeBridge/Values.lean`'s round-trip laws — an `ofValue` that
inverts `toValue` *is* injectivity — and the closed types' come from the
`ClosedTypes` interface, so nothing here re-proves either. -/

/-- A decoder that inverts an encoder makes it injective.  Stated once; the
four leaf encodings use it. -/
theorem injective_of_leftInverse {α : Type} {f : α → Value} {g : Value → Option α}
    (h : ∀ a, g (f a) = some a) : Function.Injective f := by
  intro a b hab
  have ha := h a
  rw [hab, h b] at ha
  exact (Option.some_inj.mp ha).symm

theorem refToValue_inj : Function.Injective refToValue :=
  injective_of_leftInverse refOfValue_toValue

theorem valToValue_inj : Function.Injective valToValue :=
  injective_of_leftInverse valOfValue_toValue

theorem fieldValToValue_inj : Function.Injective fieldValToValue :=
  injective_of_leftInverse fieldValOfValue_toValue

theorem externAddrToValue_inj : Function.Injective externAddrToValue :=
  injective_of_leftInverse externAddrOfValue_toValue

/-- A byte array is determined by its encoding.  `bytesToValue` is
definitionally `Encode.toValue` on the byte list (`bytesToValue_eq`), so this
is `Encode`'s injectivity plus the fact that a `ByteArray` is its list. -/
theorem bytesToValue_inj : Function.Injective bytesToValue := by
  intro a b h
  rw [bytesToValue_eq, bytesToValue_eq] at h
  have hl : a.data.toList = b.data.toList := Encode.toValue_injective h
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  simp only [ByteArray.mk.injEq]
  exact Array.toList_inj.1 hl

/-- An address list is determined by its encoding. -/
theorem addrList_inj : Function.Injective (fun (ns : List Nat) =>
    ns.map fun a => (Value.num (.natN a))) := by
  intro a b h
  refine List.map_injective_iff.2 ?_ h
  intro x y hxy
  simpa using hxy

/-! ### The instance records -/

theorem tagInstToValue_inj : Function.Injective (tagInstToValue C) := by
  intro a b h
  simp only [tagInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    true_and, and_true] at h
  cases a; cases b; simpa using C.defType_inj h

theorem globalInstToValue_inj : Function.Injective (globalInstToValue C) := by
  intro a b h
  simp only [globalInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [GlobalInst.mk.injEq]
  exact ⟨C.globalType_inj h₁, valToValue_inj h₂⟩

theorem memInstToValue_inj : Function.Injective memInstToValue := by
  intro a b h
  simp only [memInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [MemInst.mk.injEq]
  exact ⟨Encode.toValue_injective h₁, bytesToValue_inj h₂⟩

theorem tableInstToValue_inj : Function.Injective (tableInstToValue C) := by
  intro a b h
  simp only [tableInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [TableInst.mk.injEq]
  exact ⟨C.tableType_inj h₁, List.map_injective_iff.2 refToValue_inj h₂⟩

theorem dataInstToValue_inj : Function.Injective dataInstToValue := by
  intro a b h
  simp only [dataInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    true_and, and_true] at h
  cases a; cases b; simpa using bytesToValue_inj h

theorem elemInstToValue_inj : Function.Injective (elemInstToValue C) := by
  intro a b h
  simp only [elemInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [ElemInst.mk.injEq]
  exact ⟨C.elemType_inj h₁, List.map_injective_iff.2 refToValue_inj h₂⟩

theorem structInstToValue_inj : Function.Injective (structInstToValue C) := by
  intro a b h
  simp only [structInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [StructInst.mk.injEq]
  exact ⟨C.defType_inj h₁, List.map_injective_iff.2 fieldValToValue_inj h₂⟩

theorem arrayInstToValue_inj : Function.Injective (arrayInstToValue C) := by
  intro a b h
  simp only [arrayInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [ArrayInst.mk.injEq]
  exact ⟨C.defType_inj h₁, List.map_injective_iff.2 fieldValToValue_inj h₂⟩

theorem exnInstToValue_inj : Function.Injective exnInstToValue := by
  intro a b h
  simp only [exnInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, Value.num.injEq, Num.natN.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [ExnInst.mk.injEq]
  exact ⟨h₁, List.map_injective_iff.2 valToValue_inj h₂⟩

theorem charToValue_inj : Function.Injective charToValue := by
  intro a b h
  simp only [charToValue, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
    Num.natN.injEq, true_and, and_true] at h
  exact Char.toNat_inj.1 h

theorem nameToValue_inj : Function.Injective nameToValue := by
  intro a b h
  simp only [nameToValue, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    true_and, and_true] at h
  exact String.toList_inj.1 (List.map_injective_iff.2 charToValue_inj h)

theorem exportInstToValue_inj : Function.Injective exportInstToValue := by
  intro a b h
  simp only [exportInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [ExportInst.mk.injEq]
  exact ⟨nameToValue_inj h₁, externAddrToValue_inj h₂⟩

/-! ## Layer 3 — the records built from them

`ModuleInst` and `Frame` are injective outright.  `Store` is not, yet: its
`FUNCS` field carries a `funcinst`, whose `CODE` is a function body, and
`Equiv/BinaryInstr.lean`'s `instrV` is **not** proved injective — `Wasm.Instr`
has some two hundred constructors and nothing in the development needs its
injectivity so far.  Rather than hide that, `storeToValue_inj` takes it as a
hypothesis and names it.

This is not a hole in the bridge for the purpose it exists.  The forward
direction of an equivalence — "a Silmaril step has an IL derivation" — needs
only `toValue`, and that is what `Equiv/Execution.lean` proves unconditionally
for `Step_pure`.  Injectivity is what the *converse* needs, and the converse is
exactly where the development has always been explicit about its hypotheses. -/

theorem optValToValue_inj :
    Function.Injective (fun (o : Option Val) => Value.opt (o.map valToValue)) := by
  intro a b h
  simp only [Value.opt.injEq] at h
  exact Option.map_injective valToValue_inj h

theorem moduleInstToValue_inj : Function.Injective (moduleInstToValue C) := by
  intro a b h
  simp only [moduleInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := h
  cases a; cases b
  have hn : ∀ {u v : List Nat},
      u.map (fun a => Value.num (.natN a)) = v.map (fun a => Value.num (.natN a)) → u = v := by
    intro u v huv
    exact List.map_injective_iff.2 (by intro x y hxy; simpa using hxy) huv
  simp only [ModuleInst.mk.injEq]
  exact ⟨List.map_injective_iff.2 C.defType_inj h₁, hn h₂, hn h₃, hn h₄, hn h₅, hn h₆,
    hn h₇, hn h₈, List.map_injective_iff.2 exportInstToValue_inj h₉⟩

theorem frameToValue_inj : Function.Injective (frameToValue C) := by
  intro a b h
  simp only [frameToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂⟩ := h
  cases a; cases b
  simp only [Frame.mk.injEq]
  exact ⟨List.map_injective_iff.2 optValToValue_inj h₁, moduleInstToValue_inj C h₂⟩

/-- A function instance is determined by its encoding, **given** that the
instruction encoding and the host naming are injective. -/
theorem funcInstToValue_inj {H : Type} (host : H → String)
    (hhost : Function.Injective host)
    (hinstr : Function.Injective Equiv.instrV)
    (hlocal : Function.Injective (Encode.toValue (α := Wasm.ValType))) :
    Function.Injective (funcInstToValue C host) := by
  intro a b h
  simp only [funcInstToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    true_and, and_true] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  obtain ⟨ta, ma, ca⟩ := a
  obtain ⟨tb, mb, cb⟩ := b
  simp only [FuncInst.mk.injEq]
  refine ⟨C.defType_inj h₁, moduleInstToValue_inj C h₂, ?_⟩
  cases ca with
  | wasm fa =>
      cases cb with
      | wasm fb =>
          simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq,
            Value.list.injEq, percentV, caseV, Num.natN.injEq, Value.num.injEq,
            true_and, and_true] at h₃
          obtain ⟨hty, hlo, hbo⟩ := h₃
          obtain ⟨tya, loa, boa⟩ := fa
          obtain ⟨tyb, lob, bob⟩ := fb
          simp only [FuncCode.wasm.injEq, Wasm.Declaration.Func.mk.injEq]
          exact ⟨Wasm.Idx.toNat_injective hty, List.map_injective_iff.2 hlocal hlo,
            List.map_injective_iff.2 hinstr hbo⟩
      | host hb => simp at h₃
  | host ha =>
      cases cb with
      | wasm fb => simp at h₃
      | host hb =>
          simp only [Value.case.injEq, Value.text.injEq, true_and] at h₃
          simp only [FuncCode.host.injEq]
          exact hhost h₃

/-- A store is determined by its encoding, given the same two hypotheses. -/
theorem storeToValue_inj {H : Type} (host : H → String)
    (hhost : Function.Injective host)
    (hinstr : Function.Injective Equiv.instrV)
    (hlocal : Function.Injective (Encode.toValue (α := Wasm.ValType))) :
    Function.Injective (storeToValue C host) := by
  intro a b h
  simp only [storeToValue, Value.struct.injEq, List.cons.injEq, Prod.mk.injEq,
    Value.list.injEq, true_and, and_true] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ := h
  cases a; cases b
  simp only [Store.mk.injEq]
  exact ⟨List.map_injective_iff.2 (tagInstToValue_inj C) h₁,
    List.map_injective_iff.2 (globalInstToValue_inj C) h₂,
    List.map_injective_iff.2 memInstToValue_inj h₃,
    List.map_injective_iff.2 (tableInstToValue_inj C) h₄,
    List.map_injective_iff.2 (funcInstToValue_inj C host hhost hinstr hlocal) h₅,
    List.map_injective_iff.2 dataInstToValue_inj h₆,
    List.map_injective_iff.2 (elemInstToValue_inj C) h₇,
    List.map_injective_iff.2 (structInstToValue_inj C) h₈,
    List.map_injective_iff.2 (arrayInstToValue_inj C) h₉,
    List.map_injective_iff.2 exnInstToValue_inj h₁₀⟩


end Silmaril.SpecTec.Equiv.RuntimeBridge
