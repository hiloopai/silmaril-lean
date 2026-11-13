module

public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Defs

/-!
# Module typing of the wasm-3.0 script, definitions

`Instr30X` showed that `Module_ok` has no facts at the concrete primitives `BI`, because
`$clos_moduletype` never has a value, and that the repaired evaluator `withClosMod BI` validates
the empty module. This topic validates the first non-empty modules there: modules whose only
definitions are memories.

* `memV mt`: `MEMORY mt`, the image of a Core memory definition (`Encode.toValue mt` is
  `%%PAGE(at, [n .. m?])`).
* `memModule mts`: the Core module with the memories `mts` and nothing else; `memModuleV mts`: its
  image, in the shape of `Module_ok`'s conclusion (the fifth component is `%(MEMORY mt*)`).
* `ctxMems ms`: the context value `{MEMS ms}` (all other fields empty), which `Module_ok`'s
  premise 12 makes `C` at such a module.
* `FragOkZ is it`: `Instr30X.FragOkX` (bounded Core derivations of `{} ⊢ is : it` over `fragX`)
  with `Instrs_ok/sub` added at any bounded valid instruction types, not only towards number and
  vector types as in `Instr30Y.FragOkY`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Institution.Instr30 (pctNil ItBnd)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (fragX)

/-- `MEMORY mt`. -/
def memV (mt : Silmaril.Wasm.MemoryType) : Value := .case "MEMORY" (Encode.toValue mt)

/-- The Core module whose only definitions are the memories `mts`. -/
def memModule (mts : List Silmaril.Wasm.MemoryType) : Silmaril.Wasm.Module := { memories := mts }

/-- **The image of `memModule mts`**: `MODULE` with eight empty lists, `%(MEMORY mt*)` in the
memory position, no start function and no exports. -/
def memModuleV (mts : List Silmaril.Wasm.MemoryType) : Value :=
  .case "MODULE" (.tuple [pctNil, pctNil, pctNil, pctNil, .case "%" (.tuple [.list (mts.map memV)]),
    pctNil, pctNil, pctNil, pctNil, .opt none, pctNil])

/-- `{MEMS ms}`. -/
def ctxMems (ms : List Value) : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list []), ("MEMS", .list ms),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list []), ("ELEMS", .list []),
    ("LOCALS", .list []), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list [])]

/-- **Bounded Core derivations over `fragX` in `{}`, with subsumption at any types.** -/
inductive FragOkZ : List Instr → InstrType → Prop where
  /-- `Instrs_ok/empty`. -/
  | nil : FragOkZ [] (.plain [] [])
  /-- `Instrs_ok/instr`. -/
  | instr {i : Instr} {ps rs : List CValType} (hf : fragX i = true) (hb : ItBnd (.plain ps rs))
      (h : InstrOk {} i (.plain ps rs)) : FragOkZ [i] (.plain ps rs)
  /-- `Instrs_ok/seq`, without locals, at a bounded intermediate stack. -/
  | seq {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
      (hb : ∀ t ∈ t₂, Silmaril.Wasm.SpecTec.Sim.Round4.tyBnd t = true) (h₁ : FragOkZ is₁ (.plain t₁ t₂))
      (h₂ : FragOkZ is₂ (.plain t₂ t₃)) : FragOkZ (is₁ ++ is₂) (.plain t₁ t₃)
  /-- `Instrs_ok/frame`, at a bounded, valid frame (any value types). -/
  | frame {is : List Instr} {ts t₁ t₂ : List CValType} (hb : ∀ t ∈ ts, Silmaril.Wasm.SpecTec.Sim.Round4.tyBnd t = true)
      (hok : ResultOk {} ts) (h : FragOkZ is (.plain t₁ t₂)) :
      FragOkZ is (.plain (ts ++ t₁) (ts ++ t₂))
  /-- `Instrs_ok/sub`, between bounded valid instruction types without locals (any value types),
  with result types of `u32` length. -/
  | sub {is : List Instr} {ps rs ps' rs' : List CValType} (h : FragOkZ is (.plain ps rs))
      (hb' : ItBnd (.plain ps' rs')) (hs : InstrTypeSub {} (.plain ps rs) (.plain ps' rs'))
      (hok : InstrTypeOk {} (.plain ps rs)) (hok' : InstrTypeOk {} (.plain ps' rs'))
      (hlen : ps.length < 2 ^ 32 ∧ rs.length < 2 ^ 32) : FragOkZ is (.plain ps' rs')

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
