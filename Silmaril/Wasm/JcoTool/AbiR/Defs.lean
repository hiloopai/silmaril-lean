module

public import Silmaril.Wasm.JcoTool.Abi.Defs

/-!
# `wasm-jco`: canonical-ABI core signatures with named types

`Silmaril.Wasm.JcoTool.Abi` flattens anonymous types only. Worlds with interfaces use named
types: records, variants, enums, flags and resources (as `own`/`borrow` handles), defined in
an interface or a world and referred to by `Ty.ref`. This module flattens them, given a
resolver `ρ` from a reference (in the scope it occurs in) to the definition's kind and the
scope the definition lives in:

* `record`: the concatenation of the fields' flattenings;
* `variant`: the discriminant (`i32`), then the pointwise `join` of the cases' flattenings;
* `enum`: `i32`; `flags` with `n` labels: `⌈n / 32⌉` times `i32`;
* `type t` (an alias): the flattening of `t` in the definition's scope;
* a resource name as a value type is an `own` handle: `i32`.

The definitions of `design/mvp/CanonicalABI.md` (`flatten_type`) are followed. Recursion through
the resolver is bounded by `fuel` (WIT types are not recursive, so the depth of nesting
suffices). The core types of the entry points (`liftCoreR`, `lowerCoreR`, …) are those of
`Abi` with this flattening.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool

open Silmaril.Wasm.Wit.Binary (Ty Func TyRef TyDefKind Labeled IfaceName)
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Component (CoreFuncTy)

/-- Where a reference is resolved: the world, or an interface (by id or inline name). -/
inductive Scope where
  | world
  | iface (key : IfaceName ⊕ String)
  deriving Repr, DecidableEq, Inhabited

/-- A resolver: the kind of a referenced type and the scope of its definition. -/
abbrev Resolver := Scope → TyRef → Except String (Scope × TyDefKind)

/-- `⌈n / 32⌉` `i32`s: the flattening of `flags` with `n` labels. -/
def flagsFlat (n : Nat) : List NumType := List.replicate ((n + 31) / 32) ti32

mutual
/-- The flattening of a type in scope `sc`. -/
def flatR (ρ : Resolver) : Nat → Scope → Ty → Except String (List NumType)
  | 0, _, _ => throw "type nesting too deep"
  | fuel + 1, sc, t => match t with
    | .prim p => pure (primFlat p)
    | .list _ | .map _ _ => pure [ti32, ti32]
    | .option t => do pure (ti32 :: (← flatR ρ fuel sc t))
    | .result ok err => do
      let a ← flatOptR ρ fuel sc ok
      let b ← flatOptR ρ fuel sc err
      pure (ti32 :: joinList a b)
    | .tuple ts => flatListR ρ fuel sc ts
    | .stream _ | .future _ | .own _ | .borrow _ => pure [ti32]
    | .fixedList _ _ => throw "fixed-size lists are not supported"
    | .ref r => do
      let (sc', k) ← ρ sc r
      flatKindR ρ fuel sc' k
/-- The flattening of a named type's definition. -/
def flatKindR (ρ : Resolver) : Nat → Scope → TyDefKind → Except String (List NumType)
  | 0, _, _ => throw "type nesting too deep"
  | fuel + 1, sc, k => match k with
    | .record fs => flatListR ρ fuel sc (fs.map (·.ty))
    | .variant cs => do
      let fs ← cs.mapM fun c => flatOptR ρ fuel sc c.ty
      pure (ti32 :: fs.foldl joinList [])
    | .enum _ => pure [ti32]
    | .flags fs => pure (flagsFlat fs.length)
    | .resource => pure [ti32]
    | .type t => flatR ρ fuel sc t
def flatOptR (ρ : Resolver) : Nat → Scope → Option Ty → Except String (List NumType)
  | _, _, none => pure []
  | fuel, sc, some t => flatR ρ fuel sc t
def flatListR (ρ : Resolver) : Nat → Scope → List Ty → Except String (List NumType)
  | _, _, [] => pure []
  | fuel, sc, t :: ts => do
    let a ← flatR ρ fuel sc t
    let b ← flatListR ρ fuel sc ts
    pure (a ++ b)
end

mutual
/-- Whether lifting or lowering a value of the type touches linear memory. -/
def usesMemR (ρ : Resolver) : Nat → Scope → Ty → Except String Bool
  | 0, _, _ => throw "type nesting too deep"
  | fuel + 1, sc, t => match t with
    | .prim .string => pure true
    | .prim _ => pure false
    | .list _ | .map _ _ => pure true
    | .option t => usesMemR ρ fuel sc t
    | .result ok err => do pure ((← usesMemOptR ρ fuel sc ok) || (← usesMemOptR ρ fuel sc err))
    | .tuple ts => usesMemListR ρ fuel sc ts
    | .fixedList t _ => usesMemR ρ fuel sc t
    | .stream _ | .future _ | .own _ | .borrow _ => pure false
    | .ref r => do
      let (sc', k) ← ρ sc r
      match k with
      | .record fs => usesMemListR ρ fuel sc' (fs.map (·.ty))
      | .variant cs => usesMemListR ρ fuel sc' (cs.filterMap (·.ty))
      | .enum _ | .flags _ | .resource => pure false
      | .type t => usesMemR ρ fuel sc' t
def usesMemOptR (ρ : Resolver) : Nat → Scope → Option Ty → Except String Bool
  | _, _, none => pure false
  | fuel, sc, some t => usesMemR ρ fuel sc t
def usesMemListR (ρ : Resolver) : Nat → Scope → List Ty → Except String Bool
  | _, _, [] => pure false
  | fuel, sc, t :: ts => do pure ((← usesMemR ρ fuel sc t) || (← usesMemListR ρ fuel sc ts))
end

/-- The fuel for flattening: deeper than any type a world can write. -/
def flatFuel : Nat := 64

section
variable (ρ : Resolver) (sc : Scope)

def flatParamsR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String (List NumType) :=
  flatListR ρ flatFuel sc (f.params.map (·.2))

def flatResultR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String (List NumType) := flatOptR ρ flatFuel sc f.result

def paramsMemR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Bool := usesMemListR ρ flatFuel sc (f.params.map (·.2))

def resultMemR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Bool := usesMemOptR ρ flatFuel sc f.result

/-- `liftCore` with named types. -/
def liftCoreR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String CoreFuncTy := do
  let ps ← flatParamsR ρ sc f
  let rs ← flatResultR ρ sc f
  pure ⟨spill maxFlatParams ps, if rs.length ≤ maxFlatResults then rs else [ti32]⟩

/-- `liftAsyncCore` with named types. -/
def liftAsyncCoreR (f : Silmaril.Wasm.Wit.Binary.Func) (callback : Bool) : Except String CoreFuncTy := do
  let ps ← flatParamsR ρ sc f
  pure ⟨spill maxFlatParams ps, if callback then [ti32] else []⟩

/-- `lowerCore` with named types. -/
def lowerCoreR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String CoreFuncTy := do
  let ps ← flatParamsR ρ sc f
  let rs ← flatResultR ρ sc f
  if rs.length ≤ maxFlatResults then pure ⟨spill maxFlatParams ps, rs⟩
  else pure ⟨spill maxFlatParams ps ++ [ti32], []⟩

/-- `lowerAsyncCore` with named types. -/
def lowerAsyncCoreR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String CoreFuncTy := do
  let ps ← flatParamsR ρ sc f
  pure ⟨spill maxFlatAsyncParams ps ++ (if f.result.isSome then [ti32] else []), [ti32]⟩

/-- `taskReturnCore` with named types. -/
def taskReturnCoreR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String CoreFuncTy := do
  let rs ← flatResultR ρ sc f
  pure ⟨spill maxFlatParams rs, []⟩

/-- `usesMemory` with named types. -/
def usesMemoryR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Bool := do
  let ps ← flatParamsR ρ sc f
  let rs ← flatResultR ρ sc f
  pure ((← paramsMemR ρ sc f) || (← resultMemR ρ sc f) ||
    decide (maxFlatParams < ps.length) || decide (maxFlatResults < rs.length))

/-- Whether `canon lift` of `f` needs the `memory` option: for an async lift the result goes
through `task.return`, so only the parameters count. -/
def liftUsesMemoryR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Bool := do
  if f.async then
    let ps ← flatParamsR ρ sc f
    -- the result goes through `task.return`; the validator still asks the lift for the memory
    -- when that call needs it (a pointer in the result, or more than 16 flat values)
    let rs ← flatResultR ρ sc f
    pure ((← paramsMemR ρ sc f) || decide (maxFlatParams < ps.length) ||
      (← resultMemR ρ sc f) || decide (maxFlatParams < rs.length))
  else usesMemoryR ρ sc f

/-- `needsRealloc` with named types. -/
def needsReallocR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Bool := do
  let ps ← flatParamsR ρ sc f
  pure ((← paramsMemR ρ sc f) || decide (maxFlatParams < ps.length))

/-- `taskReturnUsesMemory` with named types. -/
def taskReturnUsesMemoryR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Bool := do
  let rs ← flatResultR ρ sc f
  pure ((← resultMemR ρ sc f) || decide (maxFlatParams < rs.length))

/-- `lowerAsyncUsesMemory` with named types. -/
def lowerAsyncUsesMemoryR (f : Silmaril.Wasm.Wit.Binary.Func) : Except String Bool := do
  let ps ← flatParamsR ρ sc f
  pure ((← paramsMemR ρ sc f) || f.result.isSome || decide (maxFlatAsyncParams < ps.length))

end

end Silmaril.Wasm.JcoTool
