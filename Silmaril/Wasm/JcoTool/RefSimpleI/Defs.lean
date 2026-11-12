module

public import Silmaril.Wasm.JcoTool.RefSimple.Defs
public import Silmaril.Wasm.Perf.ValidateR.Defs

/-!
# Components with imports that the reference machine runs as their IR component

`RefSimple` for the reference bridge with imports, `SimpleI` (`Reference.Bridge`): the
component imports functions, `canon lower`s each into the core instance passed to the core
module as `"env"`, and lifts core exports. `SimpleI.sound` and `SimpleI.sound_seq`
(`Reference.Sound.Thms`) say that the reference machine, with the imports answered by a host,
runs `s.toRef` as `s.toComp` over `impSem P`. This module reads that layout back:

* `ofRefI? c`: the simple component with imports whose reference component is `c`, for scalar
  types: per import `(type (func …))` and `(import "name" (func (type n)))`, the core module,
  one `(canon lower (func k))` per import, the core instance exporting them under the names of
  the module's imports, `(core instance (instantiate 0 (with "env" (instance 0))))`, then the
  exports of `Simple.toRef` aliased from core instance `1`, shifted by the number of imports.
  `RefSimpleI.Thms`: `ofRefI?_toRef`.
* `checkI s`: the decidable conditions of `SimpleI.sound` (`SimpleI.Good`, `FloatFree`,
  `Arity`, and every part of `SimpleI.Inst` but the existence of an instance).
* `readSimpleI b`: bytes read as such a component.
* **`wasm-jco new --ref`** for a world with imports (`newRefI`): the core module must import
  each world import, in order, as `"env" "name"`. The output is refused unless `readSimpleI`
  reads it back with the world's imports and exports.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.RefSimpleI

open Silmaril.Wasm.Component (Syntax.Definition Syntax.Component Syntax.VT)
open Silmaril.Wasm.Component (ValTy FuncTy CoreFuncTy CoreIface Iface)
open Silmaril.Wasm.Component.Reference (SimpleI SimpleExport ImpModule labels Core3Component
  funcExportNames floatFreeList)
open Silmaril.Wasm.JcoTool.RefSimple (scalarVT resultsOf exportIface)

/-- The function imports of a Core 3.0 module with their flat types, in order (`none` if one is
not a function of numeric type). -/
def importIface (m : Silmaril.Wasm.Module) : Option CoreIface :=
  m.imports.mapM fun i => match i.type with
    | .func t => match Silmaril.Wasm.Component.Binary.Lower.coreFuncTy m t with
      | .ok ft => some (i.name, ft)
      | .error _ => none
    | _ => none

/-- A component function type of scalar types with the parameter names of the bridge. -/
def funcTyOf (ft : Silmaril.Wasm.Component.Syntax.FuncType) : Option FuncTy :=
  if ft.async_ = false ∧ ft.params = labels "a" (ft.params.map (·.2)) then
    match ft.params.mapM (fun p => scalarVT p.2), resultsOf ft.result with
    | some ps, some rs => some ⟨ps, rs⟩
    | _, _ => none
  else none

/-- One import: its function type at type index `n`, and the import of that type. -/
def importPair? (n : Nat) : Syntax.Definition Silmaril.Wasm.Module →
    Syntax.Definition Silmaril.Wasm.Module → Option (String × FuncTy)
  | .type (.func ft), .import_ en (.func t) =>
    if t = n ∧ en.attrs = [] then (funcTyOf ft).map (en.name, ·) else none
  | _, _ => none

/-- The imports from type index `n` on, and the definitions after them. -/
def importsGroup (n : Nat) : Core3Component → Iface × Core3Component
  | d₁ :: d₂ :: rest => match importPair? n d₁ d₂ with
    | some p => let r := importsGroup (n + 1) rest; (p :: r.1, r.2)
    | none => ([], d₁ :: d₂ :: rest)
  | ds => ([], ds)

/-- `k`, …, `k + m - 1` lowers of component functions. -/
def dropLowers : Nat → Nat → Core3Component → Option Core3Component
  | _, 0, ds => some ds
  | k, m + 1, .canon (.lower f []) :: ds => if f = k then dropLowers (k + 1) m ds else none
  | _, _ + 1, _ => none

/-- One export of core instance `inst`, number `i`, after `base` functions. -/
def exportAt? (names : CoreIface) (inst base i n : Nat) (d₁ d₂ d₃ d₄ : Syntax.Definition Silmaril.Wasm.Module) :
    Option SimpleExport :=
  match d₁, d₂, d₃, d₄ with
  | .type (.func ft), .alias (.coreExport inst' cn .func), .canon (.lift f os t),
      .export_ en ⟨.func, k⟩ none =>
    if inst' = inst ∧ f = base + i ∧ os = [] ∧ t = n ∧ k = base + 2 * i ∧ en.attrs = [] then
      match funcTyOf ft, names.findIdx? (·.1 == cn) with
      | some ty, some core =>
        if (names[core]?).map (·.1) = some cn then some ⟨en.name, ty, core⟩ else none
      | _, _ => none
    else none
  | _, _, _, _ => none

/-- The exports from number `i` and type index `n` on. -/
def groupAt (names : CoreIface) (inst base : Nat) : Nat → Nat → Core3Component →
    Option (List SimpleExport)
  | _, _, [] => some []
  | i, n, d₁ :: d₂ :: d₃ :: d₄ :: rest => do
    let x ← exportAt? names inst base i n d₁ d₂ d₃ d₄
    let xs ← groupAt names inst base (i + 1) (n + 1) rest
    pure (x :: xs)
  | _, _, _ => none

/-- **The simple component with imports a reference component is.** -/
def ofRefI? (c : Core3Component) : Option SimpleI :=
  let (ims, rest) := importsGroup 0 c
  match rest with
  | .coreModule m :: rest₁ => do
    let imps ← importIface m
    let ex ← exportIface m
    let rest₂ ← dropLowers 0 ims.length rest₁
    match rest₂ with
    | .coreInstance (.exports es) :: .coreInstance (.instantiate 0 [("env", 0)]) :: rest₃ =>
      if es = imps.mapIdx (fun k p => (p.1, ⟨.func, k⟩)) then
        let xs ← groupAt ex 1 ims.length 0 ims.length rest₃
        pure ⟨⟨m, imps, ex⟩, ims, xs⟩
      else none
    | _ => none
  | _ => none

/-- The import types the reference machine's `canon lower` allocates are the validated ones. -/
def importTypesOk (s : SimpleI) : Bool :=
  match Silmaril.Wasm.Perf.ValidateR.validateR s.mod.mod with
  | some mt => decide (mt.imports = s.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩))
  | none => false

/-- The decidable conditions of `SimpleI.sound`. -/
def checkI (s : SimpleI) : Bool :=
  decide (s.exports.map (·.name)).Nodup &&
  s.exports.all (fun x => decide ((s.mod.exports[x.core]?).map (·.2) = some x.ty.flat)) &&
  decide (s.mod.imports = s.imports.map fun p => (p.1, p.2.flat)) &&
  s.exports.all (fun x => floatFreeList x.ty.params && floatFreeList x.ty.results) &&
  s.imports.all (fun p => floatFreeList p.2.params && floatFreeList p.2.results) &&
  s.exports.all (fun x => decide ((ValTy.flatList x.ty.params).length ≤ 16) &&
    decide ((ValTy.flatList x.ty.results).length ≤ 1) && decide (x.ty.results.length ≤ 1)) &&
  s.imports.all (fun p => decide ((ValTy.flatList p.2.params).length ≤ 16) &&
    decide ((ValTy.flatList p.2.results).length ≤ 1) && decide (p.2.results.length ≤ 1)) &&
  decide (funcExportNames s.mod.mod = s.mod.exports.map (·.1)) &&
  decide (s.imports.map (·.1)).Nodup &&
  decide (s.mod.mod.imports.map (fun i => (i.moduleName, i.name)) =
    s.imports.map fun p => ("env", p.1)) &&
  importTypesOk s

/-- **Bytes read as a simple component with imports.** -/
def readSimpleI (b : ByteArray) : Except String SimpleI := do
  let c ← ToolV.refCore3 b
  match ofRefI? c with
  | none => throw "the component does not have the layout of SimpleI.toRef (scalar types)"
  | some s => if checkI s then pure s else throw "the component is outside the soundness fragment of SimpleI (Good, FloatFree, Arity, the wiring of SimpleI.Inst)"

/-! ## `wasm-jco new --ref` with imports -/

open Silmaril.Wasm.Wit.Binary (World)
open Silmaril.Wasm.Component.Binary

/-- The functions a world imports and exports, at their IR types. -/
def expectedIface (w : World) : Except String (Iface × List (String × FuncTy)) := do
  let ims ← w.imports.mapM fun
    | .func f => do
      if f.async then throw s!"--ref: {f.name} is async"
      if f.kind != .freestanding then throw s!"--ref: {f.name} is not a freestanding function"
      let ps ← f.params.mapM fun (_, t) => RefSimple.irTy t
      let rs ← match f.result with
        | none => pure []
        | some t => do pure [← RefSimple.irTy t]
      pure (f.name, (⟨ps, rs⟩ : FuncTy))
    | _ => throw "--ref: the world may only import functions"
  let exs ← RefSimple.expectedExports { w with imports := [] }
  pure (ims, exs)

/-- The sections of one import (number `k`, type index `k`). -/
def importSecs (k : Nat) (name : String) (ft : FuncTy) : Except String (List XSection) := do
  let ps ← ft.params.mapM RefSimple.primOf
  let r ← ft.results.head?.mapM RefSimple.primOf
  let t : Silmaril.Wasm.Component.Binary.FuncType := ⟨labels "a" (ps.map Silmaril.Wasm.Component.Binary.ValType.prim), r.map Silmaril.Wasm.Component.Binary.ValType.prim, false⟩
  pure [.sec (.types [.func t]), .sec (.imports [⟨⟨name, .plain0⟩, .func k⟩])]

/-- The sections of export number `i` after `n` imports. -/
def exportSecsAt (n i : Nat) (name : String) (ft : FuncTy) : Except String (List XSection) := do
  let ps ← ft.params.mapM RefSimple.primOf
  let r ← ft.results.head?.mapM RefSimple.primOf
  let t : Silmaril.Wasm.Component.Binary.FuncType := ⟨labels "a" (ps.map Silmaril.Wasm.Component.Binary.ValType.prim), r.map Silmaril.Wasm.Component.Binary.ValType.prim, false⟩
  pure [.sec (.types [.func t]),
    .sec (.aliases [⟨.core .func, .coreExport 1 name⟩]),
    .sec (.canons [.lift (n + i) [] (n + i)]),
    .sec (.exports [⟨⟨name, .plain0⟩, ⟨.func, n + 2 * i⟩, none⟩])]

/-- **The component of `wasm-jco new --ref` for a world with imports.** -/
def emitRefI (core : ByteArray) (ims : Iface) (xs : List (String × FuncTy)) : Except String XAst := do
  let is ← ims.zipIdx.mapM fun ((n, ft), k) => importSecs k n ft
  let es ← xs.zipIdx.mapM fun ((n, ft), i) => exportSecsAt ims.length i n ft
  let n := ims.length
  pure ⟨is.flatten ++ [.sec (.coreModule core)] ++
    (List.range n).map (fun k => .sec (.canons [.lower k []])) ++
    [.sec (.coreInstances [.exports (ims.zipIdx.map fun ((nm, _), k) => (nm, ⟨.func, k⟩))]),
     .sec (.coreInstances [.instantiate 0 [("env", 0)]])] ++ es.flatten⟩

/-- **`wasm-jco new --ref CORE.wasm`** for a world with imports. -/
def newRefI (core : ByteArray) (w : World) : Except String (ByteArray × SimpleI) := do
  let (ims, xs) ← expectedIface w
  let x ← emitRefI core ims xs
  let some b := x.encode | throw "--ref: the component does not encode"
  let s ← readSimpleI b
  if s.imports = ims ∧ s.exports.map (fun e => (e.name, e.ty)) = xs then pure (b, s)
  else throw "--ref: the output does not read back with the world's imports and exports"

/-- The summary lines of `wasm-jco new --ref` with imports. -/
def summary (s : SimpleI) : List String :=
  [s!"ref: the bytes are the reference component SimpleI.toRef of a simple component with {s.imports.length} imports and {s.exports.length} exports (RefSimpleI.newRefI_correct)",
   "ref: with its imports answered by a host in the IR's types, every reference-machine behaviour of an export call is an IR observation of SimpleI.toComp over Core 3.0, given that the core module instantiates (RefSimpleI.readSimpleI_sound)"]

end Silmaril.Wasm.JcoTool.RefSimpleI
