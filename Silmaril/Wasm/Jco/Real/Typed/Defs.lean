module

public import Silmaril.Wasm.Jco.Styles.Wide.Defs
public import Silmaril.Wasm.Jco.Styles.Lime.Defs

/-!
# Adaptor functions with typed locals, and the multi-value adaptor as a Lime1 module

`XFn` declares its extra locals by number only: `XFn.run` initializes them to `i32` zeros and
`XFn.toLime` declares them `i32`. The multi-value shim `mvShim` (`Styles/Wide`) pops the
results of the wrapped function into locals `n + 1 …`, so a result field of type `i64`, `f32` or
`f64` goes into an `i32` local: the encoding does not validate (`local.set` of an `i64` into an
`i32` local). This module fixes that, as a variant, without changing `XFn`:

* `XFnT`: an `XFn` with the **types of its extra locals** (`tys`); `XFnT.run` initializes each to
  the zero of its type (`zeroOf`), `XFnT.toLime` declares them with these types;
* `XFnT.ofX`: an `XFn` with all extra locals `i32` (the old reading);
* **`mvShimT md s ts ns`**: `mvShim` with locals `i32` (the block pointer) followed by the flat
  types of the fields (`ValTy.flatList ts`);
* `exportShimWT`, `calleeTypeW`, `shimTypeW`, **`adaptorLimeW md`**: the adaptor of `wrapW md` (the
  multi-value style) as a Lime1 module, with the callee types of the multi-value convention
  (a wide result is returned as its flat fields, not through an out-pointer) and typed locals.

Theorems in `Silmaril.Wasm.Jco.Real.Typed.Thms`: the typed shim computes what `mvShim` computes
(the initial values of the locals are never read), and its locals have the types of the
fields.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm.Component (Flat ValTy)
open Silmaril.Wasm (NumType)

/-- The zero of a number type. -/
def zeroOf (t : NumType) : Flat := ⟨t, 0⟩

/-- An adaptor function with the types of its extra locals. -/
structure XFnT where
  fn : XFn
  /-- The types of the extra locals (`fn.locals` of them). -/
  tys : List NumType
  deriving Repr, Inhabited

variable (M : CoreInst)

/-- Run a typed adaptor function: the extra locals start at the zeros of their types. -/
def XFnT.run (g : XFnT) (args : List Flat) : RM M.St (List Flat) := do
  RM.check (args.length == g.fn.params)
  let f ← execX M g.fn.body ⟨args ++ g.tys.map zeroOf, []⟩
  pure f.stack.reverse

/-- A typed adaptor function as a Lime1 function of type index `ty`. -/
def XFnT.toLime (fi : String → Nat) (ty : Nat) (g : XFnT) : Silmaril.Wasm.Lime1.Func :=
  ⟨mkIdx ty, g.tys, XInstr.toLimeL fi g.fn.body⟩

/-- An `XFn` with all extra locals `i32`. -/
def XFnT.ofX (fn : XFn) : XFnT := ⟨fn, List.replicate fn.locals (.int .i32)⟩

/-- **The multi-value shim with typed locals**: the block pointer (`i32`), then one local per
field, of the field's flat type. -/
def mvShimT (md : Meta) (s : Sig) (ts : List ValTy) (ns : List Nat) : XFnT :=
  ⟨mvShim md s ts ns, .int .i32 :: ValTy.flatList ts⟩

/-- The export shim of the multi-value style, typed. -/
def exportShimWT (md : Meta) (s : Sig) : XFnT :=
  match wideOf s.result with
  | some (ts, ns) => mvShimT md s ts ns
  | none => XFnT.ofX (exportShim md s).toX

/-- The core type of the export `s` of the wrapped module in the multi-value style. -/
def calleeTypeW (s : Sig) : Silmaril.Wasm.V1.FuncType :=
  match wideOf s.result with
  | some (ts, _) => ⟨flatParams s.params, ValTy.flatList ts⟩
  | none => calleeType s

/-- The core type of an export shim in the multi-value style: a wide result is returned as a
pointer to its block (`shimType` would give the flat fields). -/
def shimTypeW (s : Sig) : Silmaril.Wasm.V1.FuncType :=
  match wideOf s.result with
  | some _ => ⟨flatParams s.params, [.int .i32]⟩
  | none => shimType s

/-- **The adaptor of `wrapW md` as a Lime1 module**, with typed locals. Types: the allocator,
the world's callees (multi-value convention), `cabi_realloc`, the shims. -/
def adaptorLimeW (md : Meta) : Silmaril.Wasm.Lime1.Module :=
  let n := md.world.length
  let fi := funcIdxOf md
  { types := allocType :: md.world.map calleeTypeW ++ reallocType :: md.world.map shimTypeW
    imports := ⟨"m", "memory", .memory ⟨⟨0, none⟩⟩⟩ ::
      ⟨"m", md.alloc, .func (mkIdx 0)⟩ ::
        (md.world.zipIdx.map fun (s, i) => ⟨"m", s.name, .func (mkIdx (i + 1))⟩)
    funcs := (XFnT.ofX (reallocShim md.alloc).toX).toLime fi (n + 1) ::
      (md.world.zipIdx.map fun (s, i) => (exportShimWT md s).toLime fi (n + 2 + i))
    exports := ⟨"cabi_realloc", .func (mkIdx (n + 1))⟩ ::
      (md.world.zipIdx.map fun (s, i) => ⟨s.name, .func (mkIdx (n + 2 + i))⟩) }

end Silmaril.Wasm.Jco.Real
