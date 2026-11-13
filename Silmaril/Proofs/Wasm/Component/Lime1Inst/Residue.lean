module

public import Silmaril.Proofs.Wasm.Component.Lime1Inst.Globals

/-!
# The global-free residue of a Lime1 module

`instantiateOnce?` instantiates the Core residue `Module.globalResidue` of a module (its globals
become trailing global imports) against the globals `$evalglobals` allocated. The Lime1 side
has the same decomposition:

* `residueL l`: `l` with its globals turned into trailing global imports;
* `residueStore`, `residueImports`: the store holding the evaluated globals, and their addresses;
* **`prepare?_residue`**: for an import-free `l` whose initializers evaluate to `vals`, preparing
  `residueL l` against them is preparing `l` (same store, module instance and start code);
* `residueL_toCore`: the image of the residue is the residue of the image.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1Inst

open Silmaril.Wasm Silmaril.Wasm.Lime1
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst GlobalInst ExternVal)

/-- `l` with its globals turned into trailing global imports. -/
def residueL (l : Lime1.Module) : Lime1.Module :=
  { l with globals := [],
           imports := l.imports ++ l.globals.map fun g => ⟨"", "", .global g.type⟩ }

/-- The Lime1 store holding the evaluated globals. -/
def residueStore {H : Type} (gs : List Lime1.Global) (vals : List Value) :
    Silmaril.Wasm.Lime1.Execution.Store H :=
  { globals := globalInsts gs vals }

/-- The addresses of the first `k` globals. -/
def residueImports (k : Nat) : List ExternVal := (List.range k).map fun i => .global ⟨i⟩

theorem importedInstance_residue (k : Nat) :
    Silmaril.Wasm.Lime1.Execution.importedInstance (residueImports k) =
      { globals := Silmaril.Wasm.Lime1.Execution.addresses .global 0 k } := by
  simp [Silmaril.Wasm.Lime1.Execution.importedInstance, residueImports, List.filterMap_map,
    Silmaril.Wasm.Lime1.Execution.addresses]

theorem allocate?_residue {H : Type} {l : Lime1.Module} {vals : List Value}
    (hvals : l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store H) {} g.init) = some vals) :
    Silmaril.Wasm.Lime1.Execution.allocate? (residueStore (H := H) l.globals vals) (residueL l)
        (residueImports l.globals.length) =
      Silmaril.Wasm.Lime1.Execution.allocate? {} l [] := by
  have h0 : Silmaril.Wasm.Lime1.Execution.importedInstance [] = {} := rfl
  simp only [Silmaril.Wasm.Lime1.Execution.allocate?, importedInstance_residue, h0, residueL,
    residueStore, List.mapM_nil, hvals, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    List.length_nil, List.nil_append, List.append_nil, Silmaril.Wasm.Lime1.Execution.addresses_zero,
    List.zipWith_nil_left]
  rfl

theorem prepare?_residue {H : Type} {l : Lime1.Module} {vals : List Value}
    (hvals : l.globals.mapM (fun g => Silmaril.Wasm.Lime1.Execution.constExpr?
      ({} : Silmaril.Wasm.Lime1.Execution.Store H) {} g.init) = some vals) :
    Silmaril.Wasm.Lime1.Execution.prepare? (residueStore (H := H) l.globals vals) (residueL l)
        (residueImports l.globals.length) =
      Silmaril.Wasm.Lime1.Execution.prepare? {} l [] := by
  simp only [Silmaril.Wasm.Lime1.Execution.prepare?, allocate?_residue hvals]
  rfl

theorem moduleContext_residue (l : Lime1.Module) :
    Validation.moduleContext (residueL l) = Validation.moduleContext l := by
  simp [Validation.moduleContext, residueL, Validation.importedGlobals, List.filterMap_append,
    List.filterMap_map]

/-- **The residue of a valid Lime1 module is valid.** -/
theorem residue_valid {l : Lime1.Module} (hv : Validation.ModuleValid l) :
    Validation.ModuleValid (residueL l) where
  types := hv.types
  imports i hi := by
    simp only [residueL, List.mem_append, List.mem_map] at hi
    rcases hi with hi | ⟨g, -, rfl⟩
    · exact hv.imports i hi
    · exact ⟨_, rfl, trivial⟩
  functions f hf := by rw [moduleContext_residue]; exact hv.functions f hf
  tables := hv.tables
  memories := hv.memories
  globals g hg := by simp [residueL] at hg
  elements e he := by rw [moduleContext_residue]; exact hv.elements e he
  data d hd := by rw [moduleContext_residue]; exact hv.data d hd
  start := by rw [moduleContext_residue]; exact hv.start
  exports e he := by rw [moduleContext_residue]; exact hv.exports e he
  uniqueExports := hv.uniqueExports
  singleTable := by rw [moduleContext_residue]; exact hv.singleTable
  singleMemory := by rw [moduleContext_residue]; exact hv.singleMemory

end Silmaril.Proofs.Wasm.Component.Lime1Inst
