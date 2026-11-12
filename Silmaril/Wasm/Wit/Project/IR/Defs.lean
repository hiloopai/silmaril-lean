module

public import Silmaril.Wasm.Component.Pipeline.Defs

/-!
# The world of a component of the IR

The component IR `Silmaril.Wasm.Component.Comp` keeps only functions, so its
world is a pair of interfaces: the imported functions and the exported
functions with their types (`IRWorld`). `compWorld` and `linkedWorld` read it
off; the theorems of `Silmaril.Wasm.Wit.Project.IR.Thms` show what the IR's
composition and optimisation operations do to it.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Project

open Silmaril.Wasm.Component

/-- The world of an IR component: its imported and exported functions. -/
structure IRWorld where
  /-- The imported functions. -/
  imports : Iface
  /-- The exported functions. -/
  exports : Iface
  deriving Repr, DecidableEq, Inhabited

/-- The named function types of exports. -/
def exportIface (xs : List Export) : Iface := xs.map fun x => (x.name, x.ty)

/-- The world of a nested IR component. -/
def compWorld {M : Type} (c : Comp M) : IRWorld := ⟨c.imports, exportIface c.exports⟩

/-- The world of a flat IR component. -/
def linkedWorld {M : Type} (l : Linked M) : IRWorld := ⟨l.imports, exportIface l.exports⟩

end Silmaril.Wasm.Wit.Project
