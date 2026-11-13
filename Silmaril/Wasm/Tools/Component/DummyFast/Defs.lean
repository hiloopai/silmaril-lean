module

public import Silmaril.Wasm.Tools.Component.Dummy.Defs

/-!
# The dummy module with bounded flattening

`Dummy.dummy` computes the core signature of every function with wasm-jco's `liftCoreR` and
`lowerCoreR`, which flatten the parameters completely (`flatR`) and only then compare the
length with `MAX_FLAT_PARAMS = 16` / `MAX_FLAT_RESULTS = 1`. A type whose flattening is
exponentially long (`wit-deep-record.wit` of upstream's `tests/cli`: eight records of sixteen
fields nested, `16^8` flat values) never finishes. wit-parser's `push_flat` stops as soon as
the limit is passed; this module does the same:

* `flatB ρ fuel sc t lim` is `flatR ρ fuel sc t` cut at `lim` (`cut`): `some l` when the
  flattening `l` has at most `lim` values, `none` when it is longer, found without computing
  the rest (a list's elements get the budget left by the ones before; a variant's cases and an
  option's payload one less, for the discriminant);
* `liftCoreB`, `lowerCoreB`: the core signatures from bounded flattenings;
* `dummyFast`: `Dummy.dummy` with them; `dummyOfPayloadFast`: `Dummy.dummyOfPayload`.

Fixed-length lists, which `flatR` refuses, are flattened as the canonical ABI does (the
element's flattening `n` times; `flatten_type` of `CanonicalABI.md`).

Theorems (`DummyFast.Thms`): `flatB_eq` (when `flatR` succeeds, `flatB` is its cut),
`liftCoreB_eq`, `lowerCoreB_eq`, `dummyFast_eq` (when `Dummy.dummy` succeeds, `dummyFast`
gives the same module) and `dummyOfPayloadFast_eq`. Where `Dummy.dummy` fails, `dummyFast` can
succeed: on fixed-length lists, and when a failure (an unresolved reference, fuel) lies in a
part of a type that is past the limit and so is never looked at, as in wit-parser.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.DummyFast

open Silmaril.Wasm.JcoTool
open Silmaril.Wasm.Wit.Binary (Ty Func TyDefKind DItem WorldFull IfaceName)
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Tools.Component.Dummy

/-- A flattening cut at `lim`: itself when it has at most `lim` values, else `none`. -/
def cut (lim : Nat) (l : List NumType) : Option (List NumType) :=
  if l.length ≤ lim then some l else none

/-- All present, or `none`. -/
def allSome : List (Option (List NumType)) → Option (List (List NumType))
  | [] => some []
  | none :: _ => none
  | some a :: as => (allSome as).map (a :: ·)

/-- `n` copies of a flattening, cut at `lim` (an empty element gives the empty list). -/
def repCut (lim n : Nat) (e : List NumType) : Option (List NumType) :=
  if e.isEmpty then some [] else if e.length * n ≤ lim then some (List.replicate n e).flatten
  else none

mutual
/-- **Bounded flattening** of a type in scope `sc`: `flatR` cut at `lim`. -/
def flatB (ρ : Resolver) : Nat → Scope → Ty → Nat → Except String (Option (List NumType))
  | 0, _, _, _ => throw "type nesting too deep"
  | fuel + 1, sc, t, lim => match t with
    | .prim p => pure (cut lim (primFlat p))
    | .list _ | .map _ _ => pure (cut lim [ti32, ti32])
    | .option t =>
      if lim = 0 then pure none
      else do pure ((← flatB ρ fuel sc t (lim - 1)).map (ti32 :: ·))
    | .result ok err =>
      if lim = 0 then pure none
      else do
        match ← flatOptB ρ fuel sc ok (lim - 1) with
        | none => pure none
        | some a =>
          match ← flatOptB ρ fuel sc err (lim - 1) with
          | none => pure none
          | some b => pure (some (ti32 :: joinList a b))
    | .tuple ts => flatListB ρ fuel sc ts lim
    | .stream _ | .future _ | .own _ | .borrow _ => pure (cut lim [ti32])
    | .fixedList t n =>
      if n = 0 then pure (some [])
      else do
        match ← flatB ρ fuel sc t lim with
        | none => pure none
        | some e => pure (repCut lim n e)
    | .ref r => do
      let (sc', k) ← ρ sc r
      flatKindB ρ fuel sc' k lim
/-- Bounded flattening of a named type's definition. -/
def flatKindB (ρ : Resolver) : Nat → Scope → TyDefKind → Nat →
    Except String (Option (List NumType))
  | 0, _, _, _ => throw "type nesting too deep"
  | fuel + 1, sc, k, lim => match k with
    | .record fs => flatListB ρ fuel sc (fs.map (·.ty)) lim
    | .variant cs =>
      if lim = 0 then pure none
      else do
        let fs ← cs.mapM fun c => flatOptB ρ fuel sc c.ty (lim - 1)
        pure ((allSome fs).map fun fs => ti32 :: fs.foldl joinList [])
    | .enum _ => pure (cut lim [ti32])
    | .flags fs => pure (cut lim (flagsFlat fs.length))
    | .resource => pure (cut lim [ti32])
    | .type t => flatB ρ fuel sc t lim
/-- Bounded flattening of an optional payload. -/
def flatOptB (ρ : Resolver) : Nat → Scope → Option Ty → Nat →
    Except String (Option (List NumType))
  | _, _, none, _ => pure (some [])
  | fuel, sc, some t, lim => flatB ρ fuel sc t lim
/-- Bounded flattening of a list of types: each gets the budget the earlier ones left. -/
def flatListB (ρ : Resolver) : Nat → Scope → List Ty → Nat →
    Except String (Option (List NumType))
  | _, _, [], _ => pure (some [])
  | fuel, sc, t :: ts, lim => do
    match ← flatB ρ fuel sc t lim with
    | none => pure none
    | some a => pure ((← flatListB ρ fuel sc ts (lim - a.length)).map (a ++ ·))
end

/-- The spilled parameters of a bounded flattening (`none`: past the limit, one pointer). -/
def spillB : Option (List NumType) → List NumType
  | some ps => ps
  | none => [ti32]

section
variable (ρ : Resolver) (sc : Scope)

/-- `liftCoreR` with bounded flattening. -/
def liftCoreB (f : Silmaril.Wasm.Wit.Binary.Func) : Except String CoreFuncTy := do
  let ps ← flatListB ρ flatFuel sc (f.params.map (·.2)) maxFlatParams
  let rs ← flatOptB ρ flatFuel sc f.result maxFlatResults
  pure ⟨spillB ps, spillB rs⟩

/-- `lowerCoreR` with bounded flattening. -/
def lowerCoreB (f : Silmaril.Wasm.Wit.Binary.Func) : Except String CoreFuncTy := do
  let ps ← flatListB ρ flatFuel sc (f.params.map (·.2)) maxFlatParams
  let rs ← flatOptB ρ flatFuel sc f.result maxFlatResults
  match rs with
  | some rs => pure ⟨spillB ps, rs⟩
  | none => pure ⟨spillB ps ++ [ti32], []⟩

end

/-- `Dummy.importsOf` with bounded flattening. -/
def importsOfB (ρ : Resolver) (m : Mangling) : List DItem →
    Except String (List (String × String × CoreFuncTy))
  | [] => pure []
  | .func f :: is => do
    noAsync f
    let t ← lowerCoreB ρ .world f
    pure ((importModule m none, fname f, t) :: (← importsOfB ρ m is))
  | .iface k b :: is => do
    let fs ← b.funcs.mapM fun f => do
      noAsync f
      pure (importModule m (some k), fname f, ← lowerCoreB ρ (.iface k) f)
    let ds := (resources b.types).map fun r =>
      (importModule m (some k), importedDrop m r, (⟨[t32], []⟩ : CoreFuncTy))
    pure (fs ++ ds ++ (← importsOfB ρ m is))
  | .type t :: is => do
    let ds := (resources [t]).map fun r =>
      (importModule m none, importedDrop m r, (⟨[t32], []⟩ : CoreFuncTy))
    pure (ds ++ (← importsOfB ρ m is))

/-- `Dummy.exportFunc` with bounded flattening. -/
def exportFuncB (ρ : Resolver) (m : Mangling) (k : Option (IfaceName ⊕ String)) (f : Silmaril.Wasm.Wit.Binary.Func) :
    Except String (List DFunc) := do
  noAsync f
  let sc : Scope := match k with
    | none => .world
    | some k => .iface k
  let t ← liftCoreB ρ sc f
  pure [⟨exportName m k (fname f) false, t, true⟩, ⟨exportName m k (fname f) true, ⟨t.results, []⟩, false⟩]

/-- `Dummy.funcsOf` with bounded flattening. -/
def funcsOfB (ρ : Resolver) (m : Mangling) : List DItem → Except String (List DFunc)
  | [] => pure []
  | .func f :: es => do pure ((← exportFuncB ρ m none f) ++ (← funcsOfB ρ m es))
  | .iface k b :: es => do
    let fs := (← b.funcs.mapM (exportFuncB ρ m (some k))).flatten
    let ds := (resources b.types).map fun r => (⟨dtorName m k r, ⟨[t32], []⟩, false⟩ : DFunc)
    pure (fs ++ ds ++ (← funcsOfB ρ m es))
  | .type _ :: es => funcsOfB ρ m es

/-- **`dummy_module`** with bounded flattening. -/
def dummyFast (wf : WorldFull) (m : Mangling) : Except String Silmaril.Wasm.Tools.Component.Dummy.Module := do
  let ρ := JcoTool.NewI.rho wf
  let is ← importsOfB ρ m wf.imports
  let fs ← funcsOfB ρ m wf.exports
  let tail : List DFunc := [⟨reallocName m, ⟨[t32, t32, t32, t32], [t32]⟩, true⟩,
    ⟨initializeName m, ⟨[], []⟩, false⟩]
  pure ⟨is ++ exportBuiltins m wf.exports, fs ++ tail, m⟩

/-- The dummy module of the world of a `component-type` payload, with bounded flattening. -/
def dummyOfPayloadFast (payload : ByteArray) (m : Mangling) : Except String ByteArray := do
  let wf ← Silmaril.Wasm.Wit.Binary.decodeWorldFull payload
  let d ← dummyFast wf m
  match encode d with
  | some b => pure b
  | none => throw "a number or size of the dummy module exceeds 2^32"

end Silmaril.Wasm.Tools.Component.DummyFast
