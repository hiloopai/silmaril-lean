module

public import Silmaril.Wasm.Wit.Binary.Model.Defs
public import Silmaril.Wasm.Component.Iface.Defs

/-!
# `wasm-jco`: the canonical ABI's core signatures of WIT functions

The tool `wasm-jco new` (`Silmaril.Wasm.JcoTool.New`) wraps a core module whose imports and
exports follow the canonical ABI of a WIT world. This module fixes, for a resolved WIT function
(`Silmaril.Wasm.Wit.Binary.Func`), the core signature each canonical-ABI entry point must have:

* `flat t`: the flattening of a value type (`Flatten` of `design/mvp/CanonicalABI.md`), with
  `join` of variant payloads; `string`, `list<T>` and `map<K, V>` are `(ptr, len)`; handles,
  streams and futures are one `i32`.
* `liftCore f`: the core type of the export that `canon lift` of `f` calls (sync): more than
  `MAX_FLAT_PARAMS = 16` flat parameters are passed by one pointer, more than
  `MAX_FLAT_RESULTS = 1` flat results are returned through a returned pointer.
* `liftAsyncCore f cb`: an async lift: parameters as for a sync lift, no results (stackful), or
  one `i32` (the callback code) with a callback.
* `lowerCore f`: the core type of `canon lower` of `f` (sync): spilled parameters as above,
  more than one flat result through a return pointer appended to the parameters.
* `taskReturnCore f`: the core type of `canon task.return` of `f`'s result.
* `usesMemory`/`needsRealloc`: when `canon lift` needs the `memory` and `realloc` options.

Named types (`Ty.ref`) are outside the fragment of this pass: they need type exports.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool

open Silmaril.Wasm.Wit.Binary (Ty Func)
open Silmaril.Wasm.Component (CoreFuncTy)
open Silmaril.Wasm.Component.Binary (PrimValType)
open Silmaril.Wasm (NumType)

abbrev ti32 : NumType := .int .i32
abbrev ti64 : NumType := .int .i64
abbrev tf32 : NumType := .float .f32
abbrev tf64 : NumType := .float .f64

/-- The flattening of a primitive type. -/
def primFlat : PrimValType → List NumType
  | .bool | .s8 | .u8 | .s16 | .u16 | .s32 | .u32 | .char | .errorContext => [ti32]
  | .s64 | .u64 => [ti64]
  | .f32 => [tf32]
  | .f64 => [tf64]
  | .string => [ti32, ti32]

/-- `join` of two flat types (`CanonicalABI.md`, `flatten_variant`). -/
def join (a b : NumType) : NumType :=
  if a = b then a
  else if (a = ti32 ∧ b = tf32) ∨ (a = tf32 ∧ b = ti32) then ti32
  else ti64

/-- Pointwise `join`, the longer list's tail kept. -/
def joinList : List NumType → List NumType → List NumType
  | a :: as, b :: bs => join a b :: joinList as bs
  | [], bs => bs
  | as, [] => as

mutual
/-- The flattening of a resolved WIT value type, or why it is outside the fragment. -/
def flat : Ty → Except String (List NumType)
  | .prim p => pure (primFlat p)
  | .list _ => pure [ti32, ti32]
  | .map _ _ => pure [ti32, ti32]
  | .option t => do
    let f ← flat t
    pure (ti32 :: f)
  | .result ok err => do
    let a ← flatOpt ok
    let b ← flatOpt err
    pure (ti32 :: joinList a b)
  | .tuple ts => flatList ts
  | .stream _ | .future _ | .own _ | .borrow _ => pure [ti32]
  | .fixedList _ _ => throw "fixed-size lists are not supported"
  | .ref r => throw s!"named type `{r.name}` is not supported (anonymous types only)"
/-- An optional payload. -/
def flatOpt : Option Ty → Except String (List NumType)
  | none => pure []
  | some t => flat t
/-- The concatenated flattening of a list of types. -/
def flatList : List Ty → Except String (List NumType)
  | [] => pure []
  | t :: ts => do
    let a ← flat t
    let b ← flatList ts
    pure (a ++ b)
end

mutual
/-- Whether lifting or lowering a value of the type touches linear memory. -/
def usesMem : Ty → Bool
  | .prim .string => true
  | .prim _ => false
  | .list _ | .map _ _ => true
  | .option t => usesMem t
  | .result ok err => usesMemOpt ok || usesMemOpt err
  | .tuple ts => usesMemList ts
  | .fixedList t _ => usesMem t
  | .stream _ | .future _ | .own _ | .borrow _ | .ref _ => false
def usesMemOpt : Option Ty → Bool
  | none => false
  | some t => usesMem t
def usesMemList : List Ty → Bool
  | [] => false
  | t :: ts => usesMem t || usesMemList ts
end

/-- `MAX_FLAT_PARAMS`. -/
def maxFlatParams : Nat := 16
/-- `MAX_FLAT_RESULTS`. -/
def maxFlatResults : Nat := 1
/-- `MAX_FLAT_ASYNC_PARAMS`. -/
def maxFlatAsyncParams : Nat := 4

/-- The flat parameters of a function. -/
def flatParams (f : Func) : Except String (List NumType) := flatList (f.params.map (·.2))

/-- The flat results of a function. -/
def flatResult (f : Func) : Except String (List NumType) := flatOpt f.result

/-- Parameters of a core entry point: flat, or one pointer above `limit`. -/
def spill (limit : Nat) (ps : List NumType) : List NumType :=
  if ps.length ≤ limit then ps else [ti32]

/-- The core type of the export `canon lift` calls (sync). -/
def liftCore (f : Func) : Except String CoreFuncTy := do
  let ps ← flatParams f
  let rs ← flatResult f
  pure ⟨spill maxFlatParams ps, if rs.length ≤ maxFlatResults then rs else [ti32]⟩

/-- The core type of the export an async `canon lift` calls: no results without a callback,
the callback code with one. -/
def liftAsyncCore (f : Func) (callback : Bool) : Except String CoreFuncTy := do
  let ps ← flatParams f
  pure ⟨spill maxFlatParams ps, if callback then [ti32] else []⟩

/-- The core type of the callback of an async lift: `(event, p1, p2) -> code`. -/
def callbackCore : CoreFuncTy := ⟨[ti32, ti32, ti32], [ti32]⟩

/-- The core type of `canon lower` of `f` (sync). -/
def lowerCore (f : Func) : Except String CoreFuncTy := do
  let ps ← flatParams f
  let rs ← flatResult f
  if rs.length ≤ maxFlatResults then pure ⟨spill maxFlatParams ps, rs⟩
  else pure ⟨spill maxFlatParams ps ++ [ti32], []⟩

/-- The core type of `canon lower` of `f` with the `async` option: more than
`MAX_FLAT_ASYNC_PARAMS = 4` flat parameters are passed by one pointer, a result is written
through a pointer appended to the parameters, and the call returns the subtask status. -/
def lowerAsyncCore (f : Func) : Except String CoreFuncTy := do
  let ps ← flatParams f
  pure ⟨spill maxFlatAsyncParams ps ++ (if f.result.isSome then [ti32] else []), [ti32]⟩

/-- Whether an async lower of `f` needs the `memory` option: its parameters or result touch
memory, its parameters spill, or it has a result (written through a pointer). -/
def lowerAsyncUsesMemory (f : Func) : Except String Bool := do
  let ps ← flatParams f
  pure (usesMemList (f.params.map (·.2)) || f.result.isSome || decide (maxFlatAsyncParams < ps.length))

/-- The core type of `canon task.return` of `f`'s result. -/
def taskReturnCore (f : Func) : Except String CoreFuncTy := do
  let rs ← flatResult f
  pure ⟨spill maxFlatParams rs, []⟩

/-- Whether the parameters or the result of `f` touch linear memory (or spill). -/
def usesMemory (f : Func) : Except String Bool := do
  let ps ← flatParams f
  let rs ← flatResult f
  pure (usesMemList (f.params.map (·.2)) || usesMemOpt f.result ||
    decide (maxFlatParams < ps.length) || decide (maxFlatResults < rs.length))

/-- Whether lifting `f` allocates in the callee (`realloc`): its parameters touch memory or
spill. -/
def needsRealloc (f : Func) : Except String Bool := do
  let ps ← flatParams f
  pure (usesMemList (f.params.map (·.2)) || decide (maxFlatParams < ps.length))

/-- Whether `task.return` of `f`'s result needs the `memory` option. -/
def taskReturnUsesMemory (f : Func) : Except String Bool := do
  let rs ← flatResult f
  pure (usesMemOpt f.result || decide (maxFlatParams < rs.length))

/-! ## Streams and futures of a signature -/

/-- An occurrence of a stream or future type in a signature, with its payload. -/
inductive Chan where
  | stream (t : Option Ty)
  | future (t : Option Ty)
  deriving Repr, DecidableEq, Inhabited

mutual
/-- The streams and futures of a type, outermost first, left to right (wit-component's
`TypeInfo` order of `[stream-new-N]` indices). -/
def chans : Ty → List Chan
  | .stream t => .stream t :: chansOpt t
  | .future t => .future t :: chansOpt t
  | .list t | .option t | .fixedList t _ => chans t
  | .map k v => chans k ++ chans v
  | .result ok err => chansOpt ok ++ chansOpt err
  | .tuple ts => chansList ts
  | .prim _ | .own _ | .borrow _ | .ref _ => []
def chansOpt : Option Ty → List Chan
  | none => []
  | some t => chans t
def chansList : List Ty → List Chan
  | [] => []
  | t :: ts => chans t ++ chansList ts
end

/-- The first occurrences, in order. -/
def firstOccurrences {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The distinct stream and future types of a function, in order of first occurrence:
parameters, then the result (the `N` of wit-component's `[stream-new-N]f`; checked against
`wasm-tools component embed --dummy-names legacy`, wit-component 0.262.0). -/
def funcChans (f : Func) : List Chan :=
  firstOccurrences (chansList (f.params.map (·.2)) ++ chansOpt f.result)

end Silmaril.Wasm.JcoTool
