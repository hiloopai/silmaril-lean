module

public import Silmaril.Wasm.Component.BinaryGC.Defs
public import Silmaril.Wasm.Component.Conformance.DecodeP3.Defs

/-!
# The runner's decoder with WebAssembly 3.0 core types and the 🛸 GC options

`decodeGC bytes` is `decodeP3 bytes` (the verified `BinaryP3` grammar, then `toRefP3`)
whenever that succeeds; otherwise it parses with `BinaryGC` (the same grammar with
WebAssembly 3.0 `core:deftype`s in core type sections and in type declarators, and wasmtime's 🛸 `canonopt`s `0x08`
`core-type` and `0x09` `gc` on `lift`/`lower`) and maps that to reference syntax
(`toRefGC`). So `decodeGC` extends `decodeP3` by construction (`decodeGC_of_decodeP3`).

The reference AST has core types of WebAssembly 3.0 (`Silmaril.Wasm.RecType`), so `BinaryGC`
decodes them straight into it. It has no GC canonical ABI. With `gc`, values cross the
boundary as GC references instead of through linear memory; for a function type with no
parameters and no result nothing crosses, so both ABIs coincide. `toRefGC` therefore drops
`gc` and `core-type`, and `gcEmpty` first checks that every `lift`/`lower` carrying them has
such a type (and that a `core-type` names the core function type `(func)`), by following the
component's index spaces of types, functions and core types; anything it cannot follow is
rejected (`🛸 gc canonical ABI` error).

Not proved: that `BinaryGC`'s grammar includes `BinaryP3`'s (the fallback makes it
unnecessary for the runner), round trips for `BinaryGC`, and the agreement of its core type
productions with silmaril's `Silmaril.Wasm.Binary.RecType` grammar (they are written from
the same Wasm 3.0 binary format; the runner compares `BinaryGC` with `BinaryP3` on every
binary both read, `gcAgrees`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance

open Silmaril.Wasm.Component

namespace ToRefGC

/-- An option the reference keeps (`none`: a 🛸 option, dropped). -/
def canonOpt : BinaryGC.CanonOpt → Option Syntax.CanonOpt
  | .v0 o => some (ToRef.canonOpt o)
  | _ => none

def canon : BinaryGC.Canon → Except String Syntax.Canon
  | .lift f opts t => .ok (.lift f (opts.filterMap canonOpt) t)
  | .lower f opts => .ok (.lower f (opts.filterMap canonOpt))
  | .p3 c => ToRefP3.canonRef c

def canons : List BinaryGC.Canon → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | [] => .ok []
  | c :: cs => do pure (.canon (← canon c) :: (← canons cs))

mutual

def section_ : BinaryGC.Section → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | .p3 s => ToRefP3.section_ s
  | .coreTypes xs => .ok (xs.map .coreType)
  | .types xs => .ok (xs.map .type)
  | .canons xs => canons xs
  | .component c => do pure [.component (← ast c)]

def sections : List BinaryGC.Section →
    Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | [] => .ok []
  | s :: ss => do pure ((← section_ s) ++ (← sections ss))

def ast : BinaryGC.Ast → Except String (List (Syntax.Definition Silmaril.Wasm.Module))
  | .mk ss => sections ss

end

end ToRefGC

namespace GcCheck

/-- A 🛸 option. -/
def isGcOpt : BinaryGC.CanonOpt → Bool
  | .v0 _ => false
  | _ => true

/-- The core type index of a `core-type` option. -/
def coreTypeOf? (opts : List BinaryGC.CanonOpt) : Option Nat :=
  opts.findSome? fun | .coreType t => some t | _ => none

/-- One component's index spaces, as far as they are followed (`none`: not followed). -/
structure Spaces where
  types : Array (Option Syntax.DefType) := #[]
  funcs : Array (Option Nat) := #[]
  coreTypes : Array (Option Syntax.CoreTypeDef) := #[]

/-- Type index `t` is `func()` with no parameters and no result. -/
def Spaces.emptyFunc (sp : Spaces) (t : Nat) : Bool :=
  match sp.types.getD t none with
  | some (.func ft) => ft.params.isEmpty && ft.result.isNone
  | _ => false

/-- The core function type `(func)`. -/
def emptyCore : Syntax.CoreTypeDef := .rec_ ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩

/-- The options are fine for a function of type index `t?`. -/
def Spaces.optsOk (sp : Spaces) (t? : Option Nat) (opts : List BinaryGC.CanonOpt) : Bool :=
  if !opts.any isGcOpt then true else
  (t?.map sp.emptyFunc).getD false &&
    match coreTypeOf? opts with
    | none => true
    | some i => sp.coreTypes.getD i none == some emptyCore

def Spaces.pushTypes (sp : Spaces) (n : Nat) : Spaces :=
  { sp with types := sp.types ++ Array.replicate n none }

/-- The canons of a section: the functions they define, and whether their options are fine. -/
def canonsOk (sp : Spaces) : List BinaryGC.Canon → Spaces × Bool
  | [] => (sp, true)
  | .lift _ opts t :: cs =>
    let ok := sp.optsOk (some t) opts
    let (sp', ok') := canonsOk { sp with funcs := sp.funcs.push (some t) } cs
    (sp', ok && ok')
  | .lower f opts :: cs =>
    let ok := sp.optsOk (sp.funcs.getD f none) opts
    let (sp', ok') := canonsOk sp cs
    (sp', ok && ok')
  | .p3 _ :: cs => canonsOk sp cs

/-- A `BinaryP3` section's effect on the followed index spaces. -/
def p3Section (sp : Spaces) : BinaryP3.Section → Spaces
  | .types _ => sp
  | .imports xs => xs.foldl (fun sp i => match i.desc with
      | .func t => { sp with funcs := sp.funcs.push (some t) }
      | .type _ => sp.pushTypes 1
      | _ => sp) sp
  | .exports xs => xs.foldl (fun sp e => match e.item.sort with
      | .func => { sp with funcs := sp.funcs.push (match e.desc with
          | some (.func t) => some t
          | _ => sp.funcs.getD e.item.idx none) }
      | .type => sp.pushTypes 1
      | _ => sp) sp
  | .aliases xs => xs.foldl (fun sp a => match a.sort with
      | .func => { sp with funcs := sp.funcs.push none }
      | .type => sp.pushTypes 1
      | .core .type => { sp with coreTypes := sp.coreTypes.push none }
      | _ => sp) sp
  | _ => sp

mutual

/-- Every 🛸 option of a component sits on a `func()`. -/
def ast : BinaryGC.Ast → Bool
  | .mk ss => sections {} ss

def sections (sp : Spaces) : List BinaryGC.Section → Bool
  | [] => true
  | .p3 s :: ss => sections (p3Section sp s) ss
  | .coreTypes xs :: ss =>
    sections { sp with coreTypes := sp.coreTypes ++ (xs.map some).toArray } ss
  | .types xs :: ss => sections { sp with types := sp.types ++ (xs.map some).toArray } ss
  | .canons xs :: ss =>
    let (sp', ok) := canonsOk sp xs
    ok && sections sp' ss
  | .component c :: ss => ast c && sections sp ss

end

end GcCheck

/-- `BinaryGC` syntax as reference syntax, after the 🛸 check. -/
def toRefGC (a : BinaryGC.Ast) : Except String RefComponent :=
  if GcCheck.ast a then ToRefGC.ast a
  else .error "🛸 gc canonical ABI on a function that is not func() (not in the reference)"

/-- **The runner's decoder**: `decodeP3`, and `BinaryGC` where it fails. -/
def decodeGC (bytes : ByteArray) : Except String RefComponent :=
  match decodeP3 bytes with
  | .ok d => .ok d
  | .error e =>
    match BinaryGC.parse bytes with
    | .error _ => .error e
    | .ok a => toRefGC a

theorem decodeGC_of_decodeP3 {b : ByteArray} {d : RefComponent} (h : decodeP3 b = .ok d) :
    decodeGC b = .ok d := by
  simp only [decodeGC, h]

/-- The cross-check: on a binary `decodeP3` reads, the `BinaryGC` path gives the same
reference syntax (core modules erased); `false` also when `BinaryGC` cannot read it. -/
def gcAgrees (bytes : ByteArray) : Bool :=
  match decodeP3 bytes, BinaryGC.parse bytes with
  | .ok d, .ok a => sameDecoding (.ok d) (toRefGC a)
  | .ok _, .error _ => false
  | .error _, _ => true

end Silmaril.Wasm.Component.Conformance
