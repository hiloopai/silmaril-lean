module

public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Defs

/-!
# Instruction typing of the wasm-3.0 script, definitions

`Instr30` and `Instr30X` relate `Instr_ok`/`Instrs_ok` in `stepModel BI` to Core 3.0 validation
at `nop`, `unreachable`, `drop`, the integer numeric instructions and `local.get`/`local.set`,
mostly in the empty context. This topic widens the instructions and the contexts.

* `ctxLoc L G`: the Core context `{locals := L, globals := G}`; `ctxLG ls gs`: the SpecTec
  context value `{LOCALS ls, GLOBALS gs}` (all other fields empty), the image of `ctxLoc` at
  `ls = L.map localV`, `gs = G.map globalV`; `CtxBnd L G`: their value types are bounded.
* `Flat t`: numbers, vectors, `BOT` and references to abstract heap types. Their
  `Valtype_ok`/`Valtype_sub` derivations use no field of the context, so they hold in `ctxLG`
 . `SrcFlat`:
  source value types without type indices (the annotation of `select t`).
* `fragY i`: `nop`, `unreachable`, `drop`, `select`, the integer and float numeric instructions
  other than conversions, and the five variable instructions.
* `ParamOk i it`: the side condition of the parametric instructions: flat types, and a `SrcFlat`
  annotation for `select t`.
* `FragOkY L G is it`: bounded Core derivations of `ctxLoc L G ⊢ is : it` over `fragY`, by
  `Instrs_ok/empty`, `instr`, `seq` (no initialised locals in either part), `frame` (at flat
  frame types) and `sub` (towards number and vector types).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Y

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.SpecTec.Equiv.Validation (tyV mutV)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Instr30 (ItBnd)

/-! ## Contexts -/

/-- The image of a global type, `%%(mut?, t)`. -/
def globalV (gt : CGlobalType) : Value := .case "%%" (.tuple [mutV gt.mutability, tyV gt.type])

/-- `{LOCALS ls, GLOBALS gs}`. -/
def ctxLG (ls gs : List Value) : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list gs), ("MEMS", .list []),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list []), ("ELEMS", .list []),
    ("LOCALS", .list ls), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list [])]

/-- A global type is bounded when its value type is. -/
def GlobalBnd (gt : CGlobalType) : Prop := Round4.tyBnd gt.type = true

/-- The Core context with locals and globals only. -/
def ctxLoc (L : List LocalType) (G : List CGlobalType) : Context := { locals := L, globals := G }

/-- The context is bounded when its local and global types are. -/
def CtxBnd (L : List LocalType) (G : List CGlobalType) : Prop :=
  (∀ lt ∈ L, Round4.tyBnd lt.type = true) ∧ ∀ gt ∈ G, GlobalBnd gt

/-! ## Flat types -/

/-- **Flat value types**: numbers, vectors, `BOT`, and references to abstract heap types. -/
def Flat : CValType → Bool
  | .num _ | .vec _ | .botv => true
  | .refv (.ref _ (.abs _)) => true
  | _ => false

/-- **Source value types without type indices**: numbers, vectors, and references to abstract
heap types. -/
def SrcFlat : ValType → Bool
  | .num _ | .vec _ => true
  | .ref ⟨_, .abstract _⟩ => true
  | _ => false

/-! ## Instructions -/

/-- The parametric instructions. -/
def param : Instr → Bool
  | .nop | .unreachable | .drop | .select _ => true
  | _ => false

/-- The integer and float numeric instructions, conversions excluded. -/
def numY : Instr → Bool
  | .intConst .. | .intUnOp .. | .intBinOp .. | .intTestOp .. | .intRelOp .. => true
  | .floatConst .. | .floatUnOp .. | .floatBinOp .. | .floatRelOp .. => true
  | _ => false

/-- The variable instructions. -/
def var : Instr → Bool
  | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _ => true
  | _ => false

/-- The instructions this pass reaches. -/
def fragY (i : Instr) : Bool := param i || numY i || var i

/-- **The side condition of the parametric instructions**: flat types, and an annotation without
type indices. -/
def ParamOk (i : Instr) (it : InstrType) : Prop :=
  param i = true → (∀ t ∈ it.params ++ it.results, Flat t = true) ∧
    ∀ ts, i = .select (some ts) → ∀ t ∈ ts, SrcFlat t = true

/-- **Bounded Core derivations over `fragY`** in `{locals := L, globals := G}`. -/
inductive FragOkY (L : List LocalType) (G : List CGlobalType) : List Instr → InstrType → Prop where
  /-- `Instrs_ok/empty`. -/
  | nil : FragOkY L G [] (.plain [] [])
  /-- `Instrs_ok/instr`, at any instruction type (initialised locals included). -/
  | instr {i : Instr} {it : InstrType} (hf : fragY i = true) (hb : ItBnd it) (hp : ParamOk i it)
      (h : InstrOk (ctxLoc L G) i it) : FragOkY L G [i] it
  /-- `Instrs_ok/seq`, without initialised locals, at a bounded intermediate stack. -/
  | seq {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType}
      (hb : ∀ t ∈ t₂, Round4.tyBnd t = true) (h₁ : FragOkY L G is₁ (.plain t₁ t₂))
      (h₂ : FragOkY L G is₂ (.plain t₂ t₃)) : FragOkY L G (is₁ ++ is₂) (.plain t₁ t₃)
  /-- `Instrs_ok/frame`, at a flat, valid frame. -/
  | frame {is : List Instr} {ts t₁ t₂ : List CValType} (hf : ∀ t ∈ ts, Flat t = true)
      (hok : ResultOk (ctxLoc L G).toTypeCtx ts) (h : FragOkY L G is (.plain t₁ t₂)) :
      FragOkY L G is (.plain (ts ++ t₁) (ts ++ t₂))
  /-- `Instrs_ok/sub`, towards number and vector types: the subsumed type's parameters and the
  new type's results are numbers or vectors (so every type involved is flat), and the result
  types have `u32` length. -/
  | sub {is : List Instr} {ps rs ps' rs' : List CValType} (h : FragOkY L G is (.plain ps rs))
      (hs : InstrTypeSub (ctxLoc L G) (.plain ps rs) (.plain ps' rs'))
      (hok : InstrTypeOk (ctxLoc L G) (.plain ps' rs'))
      (hp : ∀ t ∈ ps, t.IsNumOrVec) (hr : ∀ t ∈ rs', t.IsNumOrVec)
      (hlen : ps.length < 2 ^ 32 ∧ rs.length < 2 ^ 32) : FragOkY L G is (.plain ps' rs')

end Silmaril.Wasm.SpecTec.Institution.Instr30Y
