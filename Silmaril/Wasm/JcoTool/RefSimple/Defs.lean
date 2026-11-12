module

public import Silmaril.Wasm.JcoTool.LayoutRef.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Component.BinaryAsync.Defs
public import Silmaril.Wasm.Perf.CoreMod.Defs

/-!
# Components the reference machine runs as their IR component

The reference soundness theorems (`Silmaril.Wasm.Component.Reference.Sound.Thms`:
`Simple.sound`, `Simple.sound_seq`) say that the reference machine (silmaril's component
instantiation and machine over Core 3.0) runs the reference component `s.toRef` of a simple
component `s` (one import-free core module, exports that are `canon lift`s of its core exports)
as the IR component `s.toComp` (`Comp.den` over `modSem P`, the Core 3.0 semantics of modules).
This module reads that layout **back** from a reference component, so that the theorems apply
to bytes:

* `ofRef? c`: the simple component whose reference component is `c`, when `c` has the layout
  of `Simple.toRef` with scalar types (`bool`, the integers, `f32`, `f64`, `char`): the core
  module, its instance, and per export `(type (func (param "a" …) …))`,
  `(alias core export 0 "f" (core func))`, `(canon lift (core func i) (type n))`,
  `(export "name" (func 2i))`. `RefSimple.Thms`: `ofRef?_toRef` (`s.toRef = c`).
* `check s`: the decidable fragment conditions of the soundness theorem (`Simple.Good`,
  `Simple.FloatFree`, `Simple.Arity`, and the export names half of `Simple.Inst`).
* `readSimple b`: bytes read as a reference component (`ToolV.refCore3`: `xparse`, then
  `LayoutRef.toRef` with silmaril's verified core decoder), then `ofRef?` and `check`.
* `xcompOfX`, `rdRef`: the same reading for a package of a WAC composition (`AstX`, as
  `Emit.binPkgs` hands packages to the algebra); `rdRef a` is the IR component `s.toComp`.
* **`wasm-jco new --ref`** (`newRef core w`): for a world of synchronous exported functions
  over float-free scalar types and a core module without imports, the component in the layout
  of `Simple.toRef`. The output is refused unless `readSimple` reads it back as a simple
  component whose exports are the world's functions at their IR types (`expectedExports`).
  Parameter names are those of `Simple.toRef` (`a`, `ax`, `axx`, …), not the world's.

The theorems (`RefSimple.Thms`) are the soundness theorems at the bytes: every reference
behaviour of a call of an export of the component the bytes are is an IR observation of
`s.toComp`, under the one semantic hypothesis that the core module instantiates
(`∃ I, s.mod.IsInst I`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.RefSimple

open Silmaril.Wasm.Component (Syntax.Definition Syntax.Component Syntax.VT Syntax.Prim)
open Silmaril.Wasm.Component (ValTy FuncTy CoreFuncTy CoreIface Comp)
open Silmaril.Wasm.Component.Reference (Simple SimpleExport NumModule labels Core3Component
  funcExportNames floatFreeList)

/-! ## Scalar types -/

/-- The IR scalar type of a reference primitive. -/
def scalarOf : Syntax.Prim → Option ValTy
  | .bool => some .bool
  | .s8 => some .s8
  | .u8 => some .u8
  | .s16 => some .s16
  | .u16 => some .u16
  | .s32 => some .s32
  | .u32 => some .u32
  | .s64 => some .s64
  | .u64 => some .u64
  | .f32 => some .f32
  | .f64 => some .f64
  | .char => some .char
  | .string => none
  | .errorContext => none

/-- The IR scalar type of a reference value type (primitives only). -/
def scalarVT : Syntax.VT → Option ValTy
  | .prim p => scalarOf p
  | .idx _ => none

/-- The results of a reference function type: none, or one scalar. -/
def resultsOf : Option Syntax.VT → Option (List ValTy)
  | none => some []
  | some v => (scalarVT v).map ([·])

/-! ## The core module's function interface -/

/-- The function exports of a Core 3.0 module with their flat (numeric) types, in export
order (`none` if one is not numeric). -/
def exportIface (m : Silmaril.Wasm.Module) : Option CoreIface :=
  (m.exports.filterMap fun e => match e.index with
    | .func f => some (e.name, f)
    | _ => none).mapM fun (n, f) => match m.functionTypes[f.value.val]? with
      | some t => match Silmaril.Wasm.Component.Binary.Lower.coreFuncTy m t with
        | .ok ft => some (n, ft)
        | .error _ => none
      | none => none

/-! ## Reading the layout of `Simple.toRef` -/

/-- The exports of a simple component from export number `i` and type index `n` on. -/
def group (nm : NumModule) (i n : Nat) : Syntax.Component Silmaril.Wasm.Module → Option (List SimpleExport)
  | [] => some []
  | .type (.func ft) :: .alias (.coreExport 0 cn .func) :: .canon (.lift i' os n') ::
      .export_ en ⟨.func, k⟩ none :: rest =>
    if ft.async_ = false ∧ i' = i ∧ os = [] ∧ n' = n ∧ k = 2 * i ∧ en.attrs = [] ∧
        ft.params = labels "a" (ft.params.map (·.2)) then
      match ft.params.mapM (fun p => scalarVT p.2), resultsOf ft.result,
          nm.exports.findIdx? (·.1 == cn) with
      | some ps, some rs, some core =>
        if (nm.exports[core]?).map (·.1) = some cn then
          (group nm (i + 1) (n + 1) rest).map (⟨en.name, ⟨ps, rs⟩, core⟩ :: ·)
        else none
      | _, _, _ => none
    else none
  | _ => none

/-- **The simple component a reference component is**, when it has the layout of
`Simple.toRef` with scalar types. -/
def ofRef? : Core3Component → Option Simple
  | .coreModule m :: .coreInstance (.instantiate 0 []) :: rest => do
    let ex ← exportIface m
    let xs ← group ⟨m, ex⟩ 0 0 rest
    pure ⟨⟨m, ex⟩, xs⟩
  | _ => none

/-! ## The fragment conditions, decided -/

/-- The decidable conditions of the soundness theorem: export names distinct, every lifted core
export at the flat type of its function type, no floats, the flat arities, and the core
module's function export names in order. -/
def check (s : Simple) : Bool :=
  decide (s.exports.map (·.name)).Nodup &&
  s.exports.all (fun x => decide ((s.mod.exports[x.core]?).map (·.2) = some x.ty.flat)) &&
  s.exports.all (fun x => floatFreeList x.ty.params && floatFreeList x.ty.results) &&
  s.exports.all (fun x => decide ((ValTy.flatList x.ty.params).length ≤ 16) &&
    decide ((ValTy.flatList x.ty.results).length ≤ 1) && decide (x.ty.results.length ≤ 1)) &&
  decide (funcExportNames s.mod.mod = s.mod.exports.map (·.1))

/-! ## Bytes -/

/-- **Bytes read as a simple component**: the reference component they are
(`ToolV.refCore3`), read back by `ofRef?`, in the fragment (`check`). -/
def readSimple (b : ByteArray) : Except String Simple := do
  let c ← ToolV.refCore3 b
  match ofRef? c with
  | none => throw "the component does not have the layout of Simple.toRef (scalar types)"
  | some s => if check s then pure s else throw "the simple component is outside the soundness fragment (Simple.Good, FloatFree, Arity, export names)"

/-- A package of a composition (`AstX`) as a parsed output (`XComp`); `none` for nested
components and for built-ins outside `wasm-jco`'s (`CanonX.extra`). -/
def xsecOfX : Silmaril.Wasm.Component.BinaryAsync.SectionX → Option XSec
  | .custom n d => some (.sec (.custom n d))
  | .coreModule b => some (.sec (.coreModule b))
  | .coreInstances xs => some (.sec (.coreInstances xs))
  | .coreTypes xs => some (.sec (.coreTypes xs))
  | .component _ => none
  | .instances xs => some (.sec (.instances xs))
  | .aliases xs => some (.sec (.aliases xs))
  | .types xs => some (.sec (.types xs))
  | .canons xs => (xs.mapM fun (c : Silmaril.Wasm.Component.BinaryAsync.CanonX) => match c with
      | .base c => some (XCanon.canon c)
      | .builtin b => some (XCanon.builtin b)
      | .extra _ => none).map XSec.canons
  | .start s => some (.sec (.start s))
  | .imports xs => some (.sec (.imports xs))
  | .exports xs => some (.sec (.exports xs))
  | .values xs => some (.sec (.values xs))

/-- `xsecOfX` on a package. -/
def xcompOfX (a : Silmaril.Wasm.Component.BinaryAsync.AstX) : Option XComp :=
  (a.sections.mapM xsecOfX).map XComp.mk

/-- A package read as a simple component. -/
def simpleOfX (a : Silmaril.Wasm.Component.BinaryAsync.AstX) : Option Simple := do
  let x ← xcompOfX a
  let c ← LayoutRef.toRef Silmaril.Wasm.Perf.CoreDecode.decodeF x
  let s ← ofRef? c
  if check s then some s else none

/-- **The package lowering for the algebra** (`rd` of `Emit.binCompX`): a package that reads as
a simple component means its IR component `s.toComp`. -/
def rdRef (a : Silmaril.Wasm.Component.BinaryAsync.AstX) : Option (Comp NumModule) :=
  (simpleOfX a).map Simple.toComp

/-! ## `wasm-jco new --ref` -/

open Silmaril.Wasm.Wit.Binary (Ty Func World WorldItem)
open Silmaril.Wasm.Component.Binary

/-- The IR scalar type of a WIT type (float-free primitives only). -/
def irTy : Silmaril.Wasm.Wit.Binary.Ty → Except String ValTy
  | .prim .bool => pure .bool
  | .prim .s8 => pure .s8
  | .prim .u8 => pure .u8
  | .prim .s16 => pure .s16
  | .prim .u16 => pure .u16
  | .prim .s32 => pure .s32
  | .prim .u32 => pure .u32
  | .prim .s64 => pure .s64
  | .prim .u64 => pure .u64
  | .prim .char => pure .char
  | _ => throw "--ref: only bool, integers and char (no floats, strings or compound types)"

/-- The binary primitive of an IR scalar type. -/
def primOf : ValTy → Except String PrimValType
  | .bool => pure .bool
  | .s8 => pure .s8
  | .u8 => pure .u8
  | .s16 => pure .s16
  | .u16 => pure .u16
  | .s32 => pure .s32
  | .u32 => pure .u32
  | .s64 => pure .s64
  | .u64 => pure .u64
  | .f32 => pure .f32
  | .f64 => pure .f64
  | .char => pure .char
  | _ => throw "--ref: not a scalar type"

/-- The exports a world asks for: its synchronous freestanding functions at their IR types (the
world may import nothing). -/
def expectedExports (w : World) : Except String (List (String × FuncTy)) := do
  unless w.imports.isEmpty do throw "--ref: the world must import nothing"
  w.exports.mapM fun
    | .func f => do
      if f.async then throw s!"--ref: {f.name} is async"
      if f.kind != .freestanding then throw s!"--ref: {f.name} is not a freestanding function"
      let ps ← f.params.mapM fun (_, t) => irTy t
      let rs ← match f.result with
        | none => pure []
        | some t => do pure [← irTy t]
      pure (f.name, ⟨ps, rs⟩)
    | _ => throw "--ref: the world may only export functions"

/-- The sections of one export (number `i`, type index `i`): its function type with the
parameter names of `Simple.toRef`, the alias of the core export, the lift and the export. -/
def exportSecs (i : Nat) (name : String) (ft : FuncTy) : Except String (List XSection) := do
  let ps ← ft.params.mapM primOf
  let r ← ft.results.head?.mapM primOf
  let t : Silmaril.Wasm.Component.Binary.FuncType := ⟨labels "a" (ps.map Silmaril.Wasm.Component.Binary.ValType.prim), r.map Silmaril.Wasm.Component.Binary.ValType.prim, false⟩
  pure [.sec (.types [.func t]),
    .sec (.aliases [⟨.core .func, .coreExport 0 name⟩]),
    .sec (.canons [.lift i [] i]),
    .sec (.exports [⟨⟨name, .plain0⟩, ⟨.func, 2 * i⟩, none⟩])]

/-- **The component of `wasm-jco new --ref`**: the core module, its instance, and per export
the sections of `exportSecs` (each export lifts the core export of the same name). -/
def emitRef (core : ByteArray) (xs : List (String × FuncTy)) : Except String XAst := do
  let es ← (xs.zipIdx.mapM fun ((n, ft), i) => exportSecs i n ft)
  pure ⟨[.sec (.coreModule core), .sec (.coreInstances [.instantiate 0 []])] ++ es.flatten⟩

/-- **`wasm-jco new --ref CORE.wasm`**: the bytes, and the simple component they are read
back as, whose exports are the world's (`expectedExports`). -/
def newRef (core : ByteArray) (w : World) : Except String (ByteArray × Simple) := do
  let xs ← expectedExports w
  let x ← emitRef core xs
  let some b := x.encode | throw "--ref: the component does not encode"
  let s ← readSimple b
  if s.exports.map (fun e => (e.name, e.ty)) = xs then pure (b, s)
  else throw "--ref: the output does not read back with the world's exports (a core export missing or at another type)"

/-- The summary lines of `wasm-jco new --ref`. -/
def summary (s : Simple) : List String :=
  [s!"ref: the bytes are the reference component Simple.toRef of a simple component with {s.exports.length} exports (RefSimple.newRef_correct)",
   "ref: every reference-machine behaviour of an export call is an IR observation of Simple.toComp over Core 3.0, given that the core module instantiates (RefSimple.newRef_sound)"]

end Silmaril.Wasm.JcoTool.RefSimple
