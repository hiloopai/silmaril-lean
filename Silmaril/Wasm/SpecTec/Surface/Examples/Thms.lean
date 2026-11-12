module

public import Silmaril.Wasm.SpecTec.Surface.Elab.Thms
public import Silmaril.Wasm.SpecTec.Surface.Sources.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Examples
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.DecodeSound
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51

/-!
# SpecTec surface text to the IL of the `--ast` stream, on real declarations

Each theorem takes an exact excerpt of a vendored `.spectec` source
(`Silmaril.Wasm.SpecTec.Surface.Sources`, checked against the files at build
time) and proves `SurfaceRel`: the text lexes (`lexer.mll`), parses
(`parser.mly`) and elaborates (`elab.ml`) to exactly the definitions that the
official frontend printed into `specs/spectec/wasm-3.0.ast`, as imported in
`Silmaril.SpecTec.Specs.wasm30`.

The proofs run the verified pipeline `surface?` in the kernel
(`decide +kernel`) and compare the result with the imported definitions
through their printed S-expressions (`IL.scriptS`, which is injective,
`IL.scriptS_injective`), because `IL.Def` has no decidable equality. No
native code, no `ofReduceBool`.

What the kernel checks is the link between the excerpt and the imported Lean
terms. The link from the imported terms to the bytes of the `.ast` file is the
elaboration-time `spectec_import`, as everywhere else in this topic.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Surface.Examples

open Silmaril.SpecTec
open Silmaril.Wasm.SpecTec.Surface.Elab (Ctx)

/-- A pipeline run whose printed result is `scriptS s` proves `SurfaceRel`. -/
theorem surfaceRel_of_printed {Γ : Ctx} {src : String} {s : IL.Script}
    (h : (surface? Γ src).map IL.scriptS = some (IL.scriptS s)) : SurfaceRel Γ src s := by
  obtain ⟨s', hs', he⟩ := Option.map_eq_some_iff.mp h
  have hs : s' = s := IL.scriptS_injective he
  exact surface?_sound (hs ▸ hs')

/-- `syntax N hint(macro none) = nat` (`0.1-aux.vars.spectec:5`) elaborates to
the first definition of the wasm-3.0 stream, `(typ "N" (inst (alias nat)))`. -/
theorem vars_N_elaborates :
    SurfaceRel Ctx.empty Sources.wasm30_vars_line5 (Specs.wasm30.take 1) :=
  surfaceRel_of_printed (by decide +kernel)

/-- `0.1-aux.vars.spectec:5-8` (`N`, `K`, `n`, `m`) elaborates to the first
four definitions of the wasm-3.0 stream. -/
theorem vars_NKnm_elaborates :
    SurfaceRel Ctx.empty Sources.wasm30_vars_lines5_8 (Specs.wasm30.take 4) :=
  surfaceRel_of_printed (by decide +kernel)

/-- `$min` (`0.2-aux.num.spectec:5-7`: a signature and two clauses, with an
`if` and an `otherwise` premise) elaborates to definition 4 of the wasm-3.0
stream, one `DecD` with both clauses. -/
theorem num_min_elaborates :
    SurfaceRel Ctx.empty Sources.wasm30_num_lines5_7 ((Specs.wasm30.drop 4).take 1) :=
  surfaceRel_of_printed (by decide +kernel)

/-- Text to `--ast`, end to end on one declaration: line 5 of
`0.1-aux.vars.spectec` elaborates to a definition `d` that prints as the
stream's first entry `(typ "N" (inst (alias nat)))`, and `d` is the first
definition imported from `wasm-3.0.ast`. -/
theorem vars_N_text_to_ast :
    ∃ d, SurfaceRel Ctx.empty Sources.wasm30_vars_line5 [d] ∧
      IL.defS d = spectec_sexp% "(typ \"N\" (inst (alias nat)))" ∧
      Specs.wasm30.head? = some d := by
  have hd : Specs.wasm30.take 1 = [IL.Def.typD "N" [] [.instD [] [] (.aliasT (.numT .natT))]] := rfl
  exact ⟨_, hd ▸ vars_N_elaborates, by decide +kernel, rfl⟩

/-! ## `Bi32` and erratum #654, as a source patch -/

/-- The context `Bi32` is elaborated in: the type `i32` and the signatures of
the LEB128 grammars `BuN(N) : uN(N)` and `BiN(N) : iN(N)`. That these are the
stream's signatures is `binaryCtx_grams_eq`. -/
def binaryCtx : Ctx where
  typs := [("i32", .varT "i32" [])]
  grams := [("BuN", "N", .varT "uN" [.expA (.varE "N")]),
    ("BiN", "N", .varT "iN" [.expA (.varE "N")])]

/-- The signature of a one-parameter grammar definition, result type printed. -/
def gramSig? : IL.Def → Option (String × String × SExp)
  | .gramD x [.expP p _] t _ => some (x, p, IL.typS t)
  | _ => none

/-- The one-parameter grammar signatures declared by IL definitions, looking
one level into recursion groups (structural, so the kernel reduces it). -/
def gramSigs : List IL.Def → List (String × String × SExp)
  | [] => []
  | .recD inner :: ds => inner.filterMap gramSig? ++ gramSigs ds
  | d :: ds => (gramSig? d).toList ++ gramSigs ds

/-- `binaryCtx` records the signatures that the wasm-3.0 stream declares for
`BuN` (definition 749, inside a recursion group) and `BiN` (definition 751). -/
theorem binaryCtx_grams_eq :
    gramSigs ((Specs.wasm30.drop 749).take 1 ++ (Specs.wasm30.drop 751).take 1) =
      binaryCtx.grams.map fun (x, p, t) => (x, p, IL.typS t) := by
  decide +kernel

/-- `grammar Bi32 : i32 = BuN(32)` (`5.1-binary.values.spectec:31`) elaborates
to the `Bi32` of the pinned wasm-3.0 stream (definition 756), including the
implicit production result of type `uN(32)`: the unsigned decoding of #654. -/
theorem bi32_original_elaborates :
    SurfaceRel binaryCtx Sources.wasm30_binary_line31 ((Specs.wasm30.drop 756).take 1) :=
  surfaceRel_of_printed (by decide +kernel)

/-- The source fix of #654, `grammar Bi32 : i32 = BiN(32)`, elaborates to the
`Bi32` of the corrected script `IL.Binary51.wasm30binary51`, whose erratum was
written as a patch of the printed IL. The elaborator also infers the new
production-result type `iN(32)`, so the IL patch and the source patch agree. -/
theorem bi32_fixed_elaborates :
    SurfaceRel binaryCtx Sources.wasm30_binary_line31_fixed
      ((IL.Binary51.wasm30binary51.drop 756).take 1) :=
  surfaceRel_of_printed (by decide +kernel)

end Silmaril.Wasm.SpecTec.Surface.Examples
