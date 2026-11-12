module

public import Silmaril.Wasm.Component.IR.Defs

/-!
# Thin-wrapper recognition (jco part (b))

A core module `m` *follows the FFI pattern* of a world when every function the
world exports is a core export of `m` with the flattened type, under a naming
convention, and every core import of `m` is a world import with the flattened
type. Then no adaptor code is needed: the component is a *thin wrapper*, one
core instance of `m` whose imports are `canon lower`s of world imports and
whose exports are `canon lift`s of core exports of `m`.

* `World`: the metadata (world imports and exports as WIT-like interfaces).
* `Style`: an FFI naming convention, mapping world function names to the core
  names a module uses. Two variants: `Style.plain` (the names themselves) and
  `Style.cm32p2` (the `cm32p2` mangling of the canonical ABI's name mangling
  proposal, `cm32p2||f` for exports and `cm32p2|f` for imports). Nothing
  depends on the choice: every result is stated for an arbitrary `Style`.
* `recognize s w imps exps : Option Plan`: the partial recognizer. A `Plan`
  gives, for each core import of the module, the world import it is wired to,
  and for each world export, the core export of the module implementing it.
  `Plan.Fits` is the specification of a plan.
* `thin w m p : Comp M`: the thin wrapper of `m` along the plan `p`.

## The local adaptor interface

The monadic direction (part (a), the adaptor track) wraps `m` together with a
generated adaptor. Here an adaptor is represented by its *glue*: a stateless
wiring program (`Impl`) for each world export, over the core exports of `m`.
`wrapGlue w m args G` is the component with an instance of `m` and the
adaptor as a nested component without instances (pure glue), whose exports
are lifted. `Plan.glue p` is the identity glue a plan determines (export `k`
of the adaptor forwards to export `p.exports[k]` of `m`); this is the adaptor
that the monadic construction produces for a module already following the FFI
pattern. Agreement of (a) and (b) is `Silmaril.Wasm.Jco.Thin.denU_wrapGlue_glue`
(`Silmaril.Wasm.Jco.Thin.Thms`).

What is modelled: the flat (memory-free) canonical ABI of the component IR.
Strings, lists, `realloc` conventions, return pointers and spilling beyond
`MAX_FLAT_PARAMS` are outside the IR, so the flattened core type is
`FuncTy.flat` and the only convention varying between styles is naming.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Thin

open Silmaril.Wasm.Component
open Silmaril.Wasm (NumType)

/-- World metadata: the functions a world imports and exports. -/
structure World where
  /-- World imports. -/
  imports : Iface
  /-- World exports. -/
  exports : Iface
  deriving Repr, Inhabited, DecidableEq

/-- An FFI naming convention: the core names of world functions. -/
structure Style where
  /-- The core import name of a world import. -/
  importName : String → String
  /-- The core export name of a world export. -/
  exportName : String → String

/-- Core names are world names. -/
def Style.plain : Style := ⟨id, id⟩

/-- The `cm32p2` mangling of world-level functions. -/
def Style.cm32p2 : Style := ⟨fun n => "cm32p2|" ++ n, fun n => "cm32p2||" ++ n⟩

/-- A thin-wrapper plan. -/
structure Plan where
  /-- For each core import of the module, the world import wired to it. -/
  imports : List Nat
  /-- For each world export, the core export of the module implementing it. -/
  exports : List Nat
  deriving Repr, Inhabited, DecidableEq

/-- The first index of a core function with the given name and type. -/
def findCore (n : String) (ty : CoreFuncTy) : CoreIface → Option Nat
  | [] => none
  | (n', ty') :: cs =>
    if n' = n ∧ ty' = ty then some 0 else (findCore n ty cs).map (· + 1)

/-- The first index of a world function whose core name (by `name`) and
flattened type are the given ones. -/
def findWorld (name : String → String) (n : String) (ty : CoreFuncTy) : Iface → Option Nat
  | [] => none
  | (n', ft) :: fs =>
    if name n' = n ∧ ft.flat = ty then some 0 else (findWorld name n ty fs).map (· + 1)

/-- **Thin-wrapper recognition** (partial): a plan when every core import of
the module (`imps`) is a world import and every world export is a core export
of the module (`exps`), with flattened types and names by the style `s`. -/
def recognize (s : Style) (w : World) (imps exps : CoreIface) : Option Plan := do
  let is ← imps.mapM fun c => findWorld s.importName c.1 c.2 w.imports
  let xs ← w.exports.mapM fun f => findCore (s.exportName f.1) f.2.flat exps
  pure ⟨is, xs⟩

/-- **Specification of a plan**: indices in range, names and flattened types
agree. -/
structure Plan.Fits (s : Style) (w : World) (imps exps : CoreIface) (p : Plan) : Prop where
  imports_length : p.imports.length = imps.length
  exports_length : p.exports.length = w.exports.length
  imports_ok : ∀ (k : Nat) (hk : k < imps.length), ∃ (i : Nat) (f : String × FuncTy),
    p.imports[k]? = some i ∧ w.imports[i]? = some f ∧
      s.importName f.1 = imps[k].1 ∧ f.2.flat = imps[k].2
  exports_ok : ∀ (k : Nat) (hk : k < w.exports.length), ∃ (j : Nat) (c : String × CoreFuncTy),
    p.exports[k]? = some j ∧ exps[j]? = some c ∧
      c.1 = s.exportName w.exports[k].1 ∧ c.2 = w.exports[k].2.flat

/-- The wiring of the core imports: `canon lower` of the world import. -/
def importWiring (w : World) (p : Plan) : List Impl :=
  p.imports.map fun i => ⟨[.lower (w.imports[i]?.getD default).2], .call i⟩

/-- The exports of a thin wrapper: `canon lift` of the core exports of the
instance (which starts at environment index `e`). -/
def thinExports (e : Nat) (fs : Iface) (js : List Nat) : List Export :=
  (fs.zip js).map fun x => ⟨x.1.1, x.1.2, ⟨[.lift x.1.2], .call (e + x.2)⟩⟩

variable {M : Type} [CoreModule M]

/-- **The thin wrapper** of `m` along a plan: one core instance, `canon lower`
imports and `canon lift` exports, no adaptor code. -/
def thin (w : World) (m : M) (p : Plan) : Comp M :=
  .mk w.imports [.core m (importWiring w p)]
    (thinExports w.imports.length w.exports p.exports)

/-- Recognize and wrap. -/
def thinWrap? (s : Style) (w : World) (m : M) : Option (Comp M) :=
  (recognize s w (CoreModule.imports m) (CoreModule.exports m)).map (thin w m)

/-! ## The local adaptor interface -/

/-- A component value type represented by a single core value of type `t`. -/
def numValTy : NumType → ValTy
  | .int .i32 => .s32
  | .int .i64 => .s64
  | .float .f32 => .f32
  | .float .f64 => .f64

/-- A core function type as a component function type (by `numValTy`). -/
def CoreFuncTy.asFuncTy (t : CoreFuncTy) : FuncTy :=
  ⟨t.params.map numValTy, t.results.map numValTy⟩

/-- The adaptor as a nested component without instances: its imports are the
core exports `exps` of the wrapped module, its exports are the glue `G`, at the
core types `tys`. -/
def adaptor (exps tys : CoreIface) (G : List Impl) : Comp M :=
  .mk (exps.map fun c => (c.1, CoreFuncTy.asFuncTy c.2)) []
    ((tys.zip G).map fun x => ⟨x.1.1, CoreFuncTy.asFuncTy x.1.2, x.2⟩)

/-- The core types of the adaptor's exports. -/
def adaptorTys (s : Style) (w : World) : CoreIface :=
  w.exports.map fun f => (s.exportName f.1, f.2.flat)

/-- **The wrapped component** (monadic shape, local interface): an instance of
`m` with the wiring `args`, the adaptor glue `G` over the exports of `m`, and
the `canon lift` of the adaptor's exports. -/
def wrapGlue (s : Style) (w : World) (m : M) (args G : List Impl) : Comp M :=
  let W := (CoreModule.exports m).length
  .mk w.imports
    [.core m args,
     .inst (adaptor (CoreModule.exports m) (adaptorTys s w) G)
       ((List.range W).map fun i => Impl.fwd (w.imports.length + i))]
    (thinExports (w.imports.length + W) w.exports (List.range G.length))

/-- The identity glue of a plan: adaptor export `k` forwards to core export
`p.exports[k]` of the module. -/
def Plan.glue (p : Plan) : List Impl := p.exports.map Impl.fwd

end Silmaril.Wasm.Jco.Thin
