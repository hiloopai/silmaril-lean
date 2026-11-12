module

public import Silmaril.Proofs.Wasm.SpecTec.Surface.Elab
public import Silmaril.Wasm.SpecTec.Surface.Lexer.Thms
public import Silmaril.Wasm.SpecTec.Surface.Parser.Thms

/-!
# SpecTec surface elaborator: theorems

* `elab?_sound`: what `elab?` returns is an `ElabScript` derivation;
* `surface?_sound`: the whole pipeline is sound for `SurfaceRel`, so a single
  evaluation `surface? Γ src = some s` proves `SurfaceRel Γ src s`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Elab

open Silmaril.Wasm.SpecTec.Surface.Syntax
open Silmaril.SpecTec

/-- The elaborator is sound: its output is an elaboration of the declarations
(`ElabScript`). -/
theorem elab?_sound {Γ : Ctx} {ds : List Def} {s : IL.Script} (h : elab? Γ ds = some s) :
    ElabScript Γ ds s :=
  elabDecls?_sound ds Γ ds h

end Silmaril.Wasm.SpecTec.Surface.Elab

namespace Silmaril.Wasm.SpecTec.Surface

open Silmaril.SpecTec

/-- Lexing, parsing and elaboration together are sound for `SurfaceRel`. -/
theorem surface?_sound {Γ : Elab.Ctx} {src : String} {s : IL.Script} (h : surface? Γ src = some s) :
    SurfaceRel Γ src s := by
  obtain ⟨ds, hds, he⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ts, hts, hp⟩ := Option.bind_eq_some_iff.mp hds
  exact ⟨ts, ds, Lexer.lex?_sound hts, Parser.parse?_sound hp, Elab.elab?_sound he⟩

end Silmaril.Wasm.SpecTec.Surface
