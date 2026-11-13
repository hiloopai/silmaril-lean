module

public import Silmaril.Wasm.Wac.Nest.Defs
public import Silmaril.Wasm.Wac.Example.Defs
public import Silmaril.Wasm.Component.Passes.Flatten.Defs
meta import Silmaril.Wasm.Wac.Nest.Defs
meta import Silmaril.Wasm.Wac.Example.Defs
meta import Silmaril.Wasm.Component.Passes.Flatten.Defs

/-!
# WAC: nesting = inlining on the worked composition

Nesting = inlining is proved in `Silmaril.Wasm.Wac.NestInline.Thms`. This module checks
its two sides on an instance, by evaluation: the worked composition `Example.expected` (`greeter`
and `app` sharing `host#print`, exporting `run`; here with packages `pkgsF` that
forward `run` to `greet` and `greet` to `host#print`) is package `2` of a composition with
one instance of it, exporting its `run`. Inlining gives `Example.expected`'s nodes with
explicit arguments (`inline_outer`, kernel-checked); both sides, with sorted imports,
have the same flat imports (`imports_flatten_eq`, kernel-checked) and the same flat
node count and export wiring (compiled evaluation, `#guard`), as
`flatten_nest_inline` predicts.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.NestExample

open Silmaril.Wasm.Component

/-- The example's packages have no core instances. -/
instance : CoreModule Unit := ⟨fun _ => [], fun _ => []⟩

/-- A composition with one instance of the composition `Example.expected` (package 2). -/
def outer : Graph where
  nodes := [⟨2, []⟩]
  exports := [("run", .out 0 "run")]

/-- The example's packages, forwarding: `greet` calls `host#print`, `run` calls
`greeter#greet` (the interfaces of `Example.pkgs`). -/
def pkgsF : Nat → Comp Unit
  | 0 => .mk [("host#print", Example.ft)] [] [⟨"greet", Example.ft, Impl.fwd 0⟩]
  | 1 => .mk [("greeter#greet", Example.ft), ("host#print", Example.ft)] []
      [⟨"run", Example.ft, Impl.fwd 0⟩]
  | _ => .mk [] [] []

def sigsU (k : Nat) : PkgSig := sigOf (pkgsF k)

def nested : Comp Unit := outer.toCompSorted (nestPkgs pkgsF 2 Example.expected)

def inlined : Comp Unit := (Graph.inline sigsU 2 Example.expected outer).toCompSorted pkgsF

theorem inline_outer : Graph.inline sigsU 2 Example.expected outer =
    { Example.expected with imports := [] } := by
  decide +kernel

theorem imports_flatten_eq : (flatten nested).imports = (flatten inlined).imports := by
  decide +kernel

/-! `flattenNodes` recurses through nested components by well-founded recursion, which
the kernel does not evaluate; the flat nodes and the export wiring are compared by
compiled evaluation (`#guard`), not by a theorem. -/

#guard (flatten nested).nodes.length == (flatten inlined).nodes.length
#guard (flatten nested).exports.map (·.impl) == (flatten inlined).exports.map (·.impl)
#guard (flatten nested).exports.map (·.name) == (flatten inlined).exports.map (·.name)
#guard (flatten inlined).exports.map (·.impl) == [Impl.fwd 0]

end Silmaril.Wasm.Wac.NestExample
