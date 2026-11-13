module

public import Silmaril.Wasm.Models.FunCompile.Defs
public import Silmaril.Wasm.Models.FunRefCompile.Defs

/-!
# The instantiated stores of the FunLang and FunRef compilers

`FunCompile.storeOf p` and `FunRefCompile.storeOf p` are built directly: their module instance
has the defined types and the function address of `main`, and no exports. Instantiating the
compiled module (`Thms.instantiate_funCompile`, `Thms.instantiate_funRefCompile`) gives the
same store except that the instance also records the export of `main`:

* `FunCompile.instX`, `FunCompile.storeX p` and `FunRefCompile.instX`,
  `FunRefCompile.storeX p`: the instance with the export and the store holding `main` with it.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FunLang (Prog)

/-- The module instance that instantiation produces: `instOf` and the export of `main`. -/
def instX : ModuleInst := { instOf with exports := [⟨"main", .func 0⟩] }

/-- The function instance of `main` in `instX`. -/
def mainInstX (p : Prog) : FuncInst Nat := ⟨dMain, instX, .wasm (funcOf p)⟩

/-- **The instantiated store of a program**: `main` at address `0`, in `instX`. -/
def storeX (p : Prog) : Store Nat := { funcs := [mainInstX p] }

end Silmaril.Wasm.Models.FunCompile

namespace Silmaril.Wasm.Models.FunRefCompile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FunRef (Prog)

/-- The module instance that instantiation produces: `instOf` and the export of `main`. -/
def instX : ModuleInst := { instOf with exports := [⟨"main", .func 0⟩] }

/-- The function instance of `main` in `instX`. -/
def mainInstX (p : Prog) : FuncInst Nat := ⟨FunCompile.dMain, instX, .wasm (funcOf p)⟩

/-- **The instantiated store of a program**: `main` at address `0`, in `instX`. -/
def storeX (p : Prog) : Store Nat := { funcs := [mainInstX p] }

end Silmaril.Wasm.Models.FunRefCompile
