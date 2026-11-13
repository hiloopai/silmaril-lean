module

public import Silmaril.Wasm.SpecTec.Institution.Instr30Z.Defs
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Defs
public import Silmaril.Wasm.SpecTec.Institution.Instr30Y.Defs

/-!
# Module typing of the wasm-3.0 script, definitions

`Instr30Z` validated memory-only modules at the repaired primitives `withClosMod BI`.
This topic proves the converse there (reflection), and adds the first modules with a second kind
of definition: passive data segments.

* `Passive d`: the data segment `d` is passive.
* `dataV d`: `DATA(b*, PASSIVE)`, the image of a passive data segment (`b*` is
  `Sim.FwdMem.bytesV d.bytes`).
* `okV`: `OK`, the one value of `datatype`.
* `mdModule mts ds`: the Core module with the memories `mts`, the data segments `ds`, and nothing
  else; `mdModuleV mts ds`: its image, in the shape of `Module_ok`'s conclusion.
* `ctxMD ms oks`: the context value `{MEMS ms, DATAS oks}` (all other fields empty), which
  `Module_ok`'s premise 12 makes `C` at such a module.
* `FragOkW L G is it`: an earlier `Instr30Y.FragOkY` (bounded Core derivations of
  `{locals := L, globals := G} ⊢ is : it` over `fragY`) with `Instrs_ok/frame` and `Instrs_ok/sub`
  at any bounded valid value types, not only at flat ones.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30W

open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Institution.Instr30 (pctNil)
open Silmaril.Wasm.SpecTec.Institution.Instr30Z (memV)

/-- The data segment `d` is passive. -/
def Passive (d : Silmaril.Wasm.Data) : Prop :=
  match d.mode with
  | .passive => True
  | .active _ _ => False

/-- `OK`, the one value of `datatype`. -/
def okV : Value := .case "OK" (.tuple [])

/-- `DATA(b*, PASSIVE)`: the image of a passive data segment. -/
def dataV (d : Silmaril.Wasm.Data) : Value :=
  .case "DATA" (.tuple [.list (Silmaril.Wasm.SpecTec.Sim.FwdMem.bytesV d.bytes),
    .case "PASSIVE" (.tuple [])])

/-- The Core module whose only definitions are the memories `mts` and the data segments `ds`. -/
def mdModule (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) :
    Silmaril.Wasm.Module :=
  { memories := mts, data := ds }

/-- **The image of `mdModule mts ds`**: `%(MEMORY mt*)` in the memory position, `%(dataV d*)` in
the data position, everything else empty. -/
def mdModuleV (mts : List Silmaril.Wasm.MemoryType) (ds : List Silmaril.Wasm.Data) : Value :=
  .case "MODULE" (.tuple [pctNil, pctNil, pctNil, pctNil, .case "%" (.tuple [.list (mts.map memV)]),
    pctNil, pctNil, .case "%" (.tuple [.list (ds.map dataV)]), pctNil, .opt none, pctNil])

/-- `{MEMS ms, DATAS oks}`. -/
def ctxMD (ms oks : List Value) : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list []), ("MEMS", .list ms),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list oks), ("ELEMS", .list []),
    ("LOCALS", .list []), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list [])]

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Institution.Instr30 (ItBnd)
open Silmaril.Wasm.SpecTec.Institution.Instr30Y (ctxLoc fragY ParamOk)

/-- **Bounded Core derivations over `fragY` in `{locals := L, globals := G}`, with `frame` and
`sub` at any bounded valid types.** -/
inductive FragOkW (L : List LocalType) (G : List CGlobalType) : List Instr → InstrType → Prop where
  /-- `Instrs_ok/empty`. -/
  | nil : FragOkW L G [] (.plain [] [])
  /-- `Instrs_ok/instr`, as in `FragOkY`. -/
  | instr {i : Instr} {it : InstrType} (hf : fragY i = true) (hb : ItBnd it) (hp : ParamOk i it)
      (h : InstrOk (ctxLoc L G) i it) : FragOkW L G [i] it
  /-- `Instrs_ok/seq`, without initialised locals, at a bounded intermediate stack. -/
  | seq {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
      (hb : ∀ t ∈ t₂, Silmaril.Wasm.SpecTec.Sim.Round4.tyBnd t = true)
      (h₁ : FragOkW L G is₁ (.plain t₁ t₂)) (h₂ : FragOkW L G is₂ (.plain t₂ t₃)) :
      FragOkW L G (is₁ ++ is₂) (.plain t₁ t₃)
  /-- `Instrs_ok/frame`, at a bounded, valid frame of any value types. -/
  | frame {is : List Instr} {ts t₁ t₂ : List CValType}
      (hb : ∀ t ∈ ts, Silmaril.Wasm.SpecTec.Sim.Round4.tyBnd t = true)
      (hok : ResultOk (ctxLoc L G).toTypeCtx ts) (h : FragOkW L G is (.plain t₁ t₂)) :
      FragOkW L G is (.plain (ts ++ t₁) (ts ++ t₂))
  /-- `Instrs_ok/sub`, between bounded valid instruction types without initialised locals, of
  any value types, with result types of `u32` length. -/
  | sub {is : List Instr} {ps rs ps' rs' : List CValType} (h : FragOkW L G is (.plain ps rs))
      (hb' : ItBnd (.plain ps' rs')) (hs : InstrTypeSub (ctxLoc L G) (.plain ps rs) (.plain ps' rs'))
      (hok : InstrTypeOk (ctxLoc L G) (.plain ps rs))
      (hok' : InstrTypeOk (ctxLoc L G) (.plain ps' rs'))
      (hlen : ps.length < 2 ^ 32 ∧ rs.length < 2 ^ 32) : FragOkW L G is (.plain ps' rs')

end Silmaril.Wasm.SpecTec.Institution.Instr30W
