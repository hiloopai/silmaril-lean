module

public import Silmaril.Proofs.Wasm.Wit.Elab.Sound
public import Silmaril.Wasm.Wit.Bridge.Thms

/-!
# Elaboration and the projection

`elaborate_world_projects`: for an elaborated surface package, the bytes
wit-component writes parse to a component whose projection shows, under the
name of each world, the world's wrapper; the world it wraps is the component
type the encoder writes for the elaborated world and decodes to its normal form.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Component.Wat
open Silmaril.Wasm.Wit.Project

/-- **Surface worlds project back** (Project ∘ encodePackage ∘ elaborate). -/
theorem elaborate_world_projects {U : Universe} {p : PackageName} {fs : List Name} {P : Binary.Package}
    {deps : Binary.Env} (h : elaborate U p fs = .ok (P, deps)) {b : ByteArray}
    (hb : Binary.encodePackage deps P = .ok b) :
    ∃ c its, parse b = .ok c ∧ (project c).bind (packageItems 0) = some its ∧
      ∀ nw ∈ P.worlds, ∃ ds d, Binary.encodeWorld (P.env deps) nw.2 = .ok ds ∧ (nw.1, d) ∈ its ∧
        Bridge.wrappedWorld d = some ds ∧ Binary.decWorld ds = .ok nw.2.normalize :=
  Bridge.world_project_encodePackage (elaborate_sound h).2.1 hb

end Silmaril.Wasm.Wit.Elab
