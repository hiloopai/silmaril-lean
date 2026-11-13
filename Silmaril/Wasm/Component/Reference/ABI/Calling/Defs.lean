module

public import Silmaril.Wasm.Component.Reference.ABI.Flatten.Defs
public import Silmaril.Wasm.V1.Types
public import Mathlib.Tactic.SplitIfs

/-!
# Canonical ABI function calling conventions

These are the static core signatures selected by canonical lift/lower options.
Asynchronous signature calculation does not implement task scheduling,
callbacks, streams, futures, resource ownership, or post-return behavior.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.ABI

universe u

structure FuncType (Resource : Type u) where
  params : List (WIT.ClosedType Resource)
  results : List (WIT.ClosedType Resource)
  deriving Repr

def FuncType.ofWIT {Resource : Type u} (f : WIT.FuncType Empty Resource) : FuncType Resource :=
  ⟨f.params.map Prod.snd, f.result.toList⟩

inductive Direction where
  | lift | lower
  deriving Repr, DecidableEq

structure Options where
  memory : AddrType := .i32
  async_ : Bool := false
  callback : Bool := false
  deriving Repr, DecidableEq

def maxFlatParams : Nat := 16
def maxFlatAsyncParams : Nat := 4
def maxFlatResults : Nat := 1

/-- Replace an oversized flattened argument sequence with a memory pointer. -/
def fitParams (limit : Nat) (memory : AddrType) (params : List CoreType) : List CoreType :=
  if params.length ≤ limit then params else [pointerType memory]

/-- Function signatures use the existing four-scalar core function type.
A synchronous lowered out-pointer is appended *after* argument indirection. -/
def flattenFunc {Resource : Type u} (opts : Options) (direction : Direction)
    (ft : FuncType Resource) : V1.FuncType :=
  let params := flattenTypes opts.memory ft.params
  let results := flattenTypes opts.memory ft.results
  if !opts.async_ then
    let params := fitParams maxFlatParams opts.memory params
    if results.length ≤ maxFlatResults then ⟨params, results⟩
    else match direction with
      | .lift => ⟨params, [pointerType opts.memory]⟩
      | .lower => ⟨params ++ [pointerType opts.memory], []⟩
  else match direction with
    | .lift =>
      ⟨fitParams maxFlatParams opts.memory params, if opts.callback then [.int .i32] else []⟩
    | .lower =>
      let params := fitParams maxFlatAsyncParams opts.memory params
      ⟨if results.isEmpty then params else params ++ [pointerType opts.memory], [.int .i32]⟩

end Silmaril.Wasm.Component.ABI
