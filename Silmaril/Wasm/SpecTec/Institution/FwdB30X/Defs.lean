module

public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Defs
public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs

/-!
# Existence of `Step_pure`/`Step_read` facts at `Wasm30.builtins`, by inversion: definitions

`FwdB30` reached the classified rules whose forward leaves hold at every evaluator. The rest use
primitives (`$binop_`, `$blocktype_`, `$table`, …) of which nothing is known at the
choice-made `Wasm30.builtins`. This header names the data for the other way round: what is known
at `builtins` is that Core's successor is a `Step` fact (`Wasm30.fwd_upto`), and a `Step` fact
from a short flat redex can only come from `Step/pure` (or `Step/read`) at the whole redex,
whatever the primitives. That last claim is syntactic: it reads the left-hand sides of the rules
of `Step`, `Step_pure` and `Step_read` only.

* `ruleLen r`: the length of the code a rule's left-hand side forces, when that code is a list
  literal (`instr*` for `Step_pure`, `z; instr*` for `Step_read` and `Step`).
* `pureInfoT`, `readInfoT`, `stepInfoT`: `(RefsGC.ruleTags r, ruleLen r)` for every rule of the
  three relations of the pinned wasm-3.0 script, in order (79, 103 and 36 rules); checked against
  the script by kernel `rfl` in `Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30XTables`.
* `valTags`: the constructors of the images of Core values.
* `FlatK k t l`: `l` is `k` values followed by one injection named `t` (or junk).
* `chkProper k t T`: every rule of `T` names a constructor outside `t :: valTags`, or one
  outside `valTags` and forces a code longer than `k`. Then no rule of `T` fires on a proper
  infix of a `FlatK k t` code.
* `chkFull k t T`: every rule of `T` names a constructor outside `t :: valTags` or forces a code
  of length other than `k + 1`. Then no rule of `T` fires on the whole `FlatK k t` code.
* `pureOk k t`, `readOk k t`: the checks for a `Step_pure` (`Step_read`) redex of shape
  `FlatK k t`: every proper infix is inert, and at the whole redex only `Step_pure` (`Step_read`)
  can fire.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Forced lengths -/

/-- The length of a list literal. -/
def lenOf : Exp → Option Nat
  | .listE es => some es.length
  | _ => none

/-- The forced length of a left-hand side, looking through `z; instr*` (as `RefsGC.codeTags`). -/
def codeLen : Exp → Option Nat
  | .caseE "%;%" (.tupE [_, c]) => lenOf c
  | e => lenOf e

/-- The forced length of a conclusion `lhs ~> rhs`. -/
def concLen : Exp → Option Nat
  | .tupE [l, _] => codeLen l
  | _ => none

/-- The forced length of a rule's left-hand side. -/
def ruleLen : Rule → Option Nat
  | .ruleD _ _ _ e _ => concLen e

/-- What the inversion reads off a rule: its forced constructors and forced length. -/
def ruleInfo (r : Rule) : List MixopS × Option Nat := (Sim.RefsGC.ruleTags r, ruleLen r)

/-! ## The tables of the pinned script -/

/-- The 79 rules of `Step_pure`, read by `ruleInfo`. -/
def pureInfoT : List (List MixopS × Option Nat) :=
  [(["UNREACHABLE"], some 1), (["NOP"], some 1), (["DROP"], some 2), (["CONST", "SELECT"], some 4),
   (["CONST", "SELECT"], some 4), (["CONST", "IF%%ELSE%"], some 2),
   (["CONST", "IF%%ELSE%"], some 2), (["LABEL_%{%}%"], some 1), (["LABEL_%{%}%"], some 1),
   (["LABEL_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1), (["CONST", "BR_IF"], some 2),
   (["CONST", "BR_IF"], some 2), (["CONST", "BR_TABLE"], some 2), (["CONST", "BR_TABLE"], some 2),
   (["BR_ON_NULL"], some 2), (["BR_ON_NULL"], some 2), (["BR_ON_NON_NULL"], some 2),
   (["BR_ON_NON_NULL"], some 2), (["CALL_INDIRECT"], some 1), (["RETURN_CALL_INDIRECT"], some 1),
   (["FRAME_%{%}%"], some 1), (["FRAME_%{%}%"], some 1), (["LABEL_%{%}%"], some 1),
   (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1), (["TRAP"], none),
   (["LABEL_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1), (["FRAME_%{%}%"], some 1),
   (["LOCAL.TEE"], some 2), (["CONST", "REF.I31"], some 2), (["REF.IS_NULL"], some 2),
   (["REF.IS_NULL"], some 2), (["REF.AS_NON_NULL"], some 2), (["REF.AS_NON_NULL"], some 2),
   (["REF.EQ"], some 3), (["REF.EQ"], some 3), (["REF.EQ"], some 3),
   (["REF.NULL_ADDR", "I31.GET"], some 2), (["REF.I31_NUM", "I31.GET"], some 2),
   (["CONST", "ARRAY.NEW"], some 3), (["EXTERN.CONVERT_ANY"], some 2),
   (["EXTERN.CONVERT_ANY"], some 2), (["REF.NULL_ADDR", "ANY.CONVERT_EXTERN"], some 2),
   (["REF.EXTERN", "ANY.CONVERT_EXTERN"], some 2), (["CONST", "UNOP"], some 2),
   (["CONST", "UNOP"], some 2), (["CONST", "CONST", "BINOP"], some 3),
   (["CONST", "CONST", "BINOP"], some 3), (["CONST", "TESTOP"], some 2),
   (["CONST", "CONST", "RELOP"], some 3), (["CONST", "CVTOP"], some 2),
   (["CONST", "CVTOP"], some 2), (["VCONST", "VVUNOP"], some 2),
   (["VCONST", "VCONST", "VVBINOP"], some 3), (["VCONST", "VCONST", "VCONST", "VVTERNOP"], some 4),
   (["VCONST", "VVTESTOP"], some 2), (["VCONST", "VUNOP"], some 2), (["VCONST", "VUNOP"], some 2),
   (["VCONST", "VCONST", "VBINOP"], some 3), (["VCONST", "VCONST", "VBINOP"], some 3),
   (["VCONST", "VCONST", "VCONST", "VTERNOP"], some 4),
   (["VCONST", "VCONST", "VCONST", "VTERNOP"], some 4), (["VCONST", "VTESTOP"], some 2),
   (["VCONST", "VCONST", "VRELOP"], some 3), (["VCONST", "CONST", "VSHIFTOP"], some 3),
   (["VCONST", "VBITMASK"], some 2), (["VCONST", "VCONST", "VSWIZZLOP"], some 3),
   (["VCONST", "VCONST", "VSHUFFLE"], some 3), (["CONST", "VSPLAT"], some 2),
   (["VCONST", "VEXTRACT_LANE"], some 2), (["VCONST", "VEXTRACT_LANE"], some 2),
   (["VCONST", "CONST", "VREPLACE_LANE"], some 3), (["VCONST", "VEXTUNOP"], some 2),
   (["VCONST", "VCONST", "VEXTBINOP"], some 3),
   (["VCONST", "VCONST", "VCONST", "VEXTTERNOP"], some 4),
   (["VCONST", "VCONST", "VNARROW"], some 3), (["VCONST", "VCVTOP"], some 2)]

/-- The 103 rules of `Step_read`, read by `ruleInfo`. -/
def readInfoT : List (List MixopS × Option Nat) :=
  [(["BLOCK"], none), (["LOOP"], none), (["BR_ON_CAST"], some 2), (["BR_ON_CAST"], some 2),
   (["BR_ON_CAST_FAIL"], some 2), (["BR_ON_CAST_FAIL"], some 2), (["CALL"], some 1),
   (["RETURN_CALL"], some 1), (["LABEL_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["FRAME_%{%}%"], some 1), (["FRAME_%{%}%"], some 1), (["REF.NULL_ADDR", "THROW_REF"], some 2),
   (["REF.EXN_ADDR", "THROW_REF"], none), (["LABEL_%{%}%"], some 1), (["FRAME_%{%}%"], some 1),
   (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["TRY_TABLE"], none), (["LOCAL.GET"], some 1), (["GLOBAL.GET"], some 1),
   (["CONST", "TABLE.GET"], some 2), (["CONST", "TABLE.GET"], some 2), (["TABLE.SIZE"], some 1),
   (["CONST", "CONST", "TABLE.FILL"], some 4), (["CONST", "CONST", "TABLE.FILL"], some 4),
   (["CONST", "CONST", "TABLE.FILL"], some 4), (["CONST", "CONST", "CONST", "TABLE.COPY"], some 4),
   (["CONST", "CONST", "CONST", "TABLE.COPY"], some 4),
   (["CONST", "CONST", "CONST", "TABLE.COPY"], some 4),
   (["CONST", "CONST", "CONST", "TABLE.COPY"], some 4),
   (["CONST", "CONST", "CONST", "TABLE.INIT"], some 4),
   (["CONST", "CONST", "CONST", "TABLE.INIT"], some 4),
   (["CONST", "CONST", "CONST", "TABLE.INIT"], some 4), (["CONST", "LOAD"], some 2),
   (["CONST", "LOAD"], some 2), (["CONST", "LOAD"], some 2), (["CONST", "LOAD"], some 2),
   (["CONST", "VLOAD"], some 2), (["CONST", "VLOAD"], some 2), (["CONST", "VLOAD"], some 2),
   (["CONST", "VLOAD"], some 2), (["CONST", "VLOAD"], some 2), (["CONST", "VLOAD"], some 2),
   (["CONST", "VLOAD"], some 2), (["CONST", "VLOAD"], some 2),
   (["CONST", "VCONST", "VLOAD_LANE"], some 3), (["CONST", "VCONST", "VLOAD_LANE"], some 3),
   (["MEMORY.SIZE"], some 1), (["CONST", "CONST", "MEMORY.FILL"], some 4),
   (["CONST", "CONST", "MEMORY.FILL"], some 4), (["CONST", "CONST", "MEMORY.FILL"], some 4),
   (["CONST", "CONST", "CONST", "MEMORY.COPY"], some 4),
   (["CONST", "CONST", "CONST", "MEMORY.COPY"], some 4),
   (["CONST", "CONST", "CONST", "MEMORY.COPY"], some 4),
   (["CONST", "CONST", "CONST", "MEMORY.COPY"], some 4),
   (["CONST", "CONST", "CONST", "MEMORY.INIT"], some 4),
   (["CONST", "CONST", "CONST", "MEMORY.INIT"], some 4),
   (["CONST", "CONST", "CONST", "MEMORY.INIT"], some 4), (["REF.NULL"], some 1),
   (["REF.FUNC"], some 1), (["REF.TEST"], some 2), (["REF.TEST"], some 2), (["REF.CAST"], some 2),
   (["REF.CAST"], some 2), (["STRUCT.NEW_DEFAULT"], some 1),
   (["REF.NULL_ADDR", "STRUCT.GET"], some 2), (["REF.STRUCT_ADDR", "STRUCT.GET"], some 2),
   (["CONST", "ARRAY.NEW_DEFAULT"], some 2), (["CONST", "CONST", "ARRAY.NEW_ELEM"], some 3),
   (["CONST", "CONST", "ARRAY.NEW_ELEM"], some 3), (["CONST", "CONST", "ARRAY.NEW_DATA"], some 3),
   (["CONST", "CONST", "ARRAY.NEW_DATA"], some 3),
   (["REF.NULL_ADDR", "CONST", "ARRAY.GET"], some 3),
   (["REF.ARRAY_ADDR", "CONST", "ARRAY.GET"], some 3),
   (["REF.ARRAY_ADDR", "CONST", "ARRAY.GET"], some 3), (["REF.NULL_ADDR", "ARRAY.LEN"], some 2),
   (["REF.ARRAY_ADDR", "ARRAY.LEN"], some 2),
   (["REF.NULL_ADDR", "CONST", "CONST", "ARRAY.FILL"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.FILL"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.FILL"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.FILL"], some 5),
   (["REF.NULL_ADDR", "CONST", "CONST", "CONST", "ARRAY.COPY"], some 6),
   (["CONST", "REF.NULL_ADDR", "CONST", "CONST", "ARRAY.COPY"], some 6),
   (["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"], some 6),
   (["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"], some 6),
   (["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"], some 6),
   (["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"], some 6),
   (["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"], some 6),
   (["REF.NULL_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"], some 5),
   (["REF.NULL_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"], some 5),
   (["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"], some 5)]

/-- The 36 rules of `Step`, read by `ruleInfo`. Rules 0–2 (`pure`, `read`, `ctxt-instrs`) force
nothing and are inverted directly. -/
def stepInfoT : List (List MixopS × Option Nat) :=
  [([], none), ([], none), ([], none), (["LABEL_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["FRAME_%{%}%"], some 1), (["REF.NULL_ADDR", "CALL_REF"], some 2),
   (["REF.FUNC_ADDR", "CALL_REF"], none), (["REF.FUNC_ADDR", "CALL_REF"], none),
   (["REF.FUNC_ADDR", "CALL_REF"], none), (["THROW"], none), (["LOCAL.SET"], some 2),
   (["GLOBAL.SET"], some 2), (["CONST", "TABLE.SET"], some 3), (["CONST", "TABLE.SET"], some 3),
   (["CONST", "TABLE.GROW"], some 3), (["CONST", "TABLE.GROW"], some 3), (["ELEM.DROP"], some 1),
   (["CONST", "CONST", "STORE"], some 3), (["CONST", "CONST", "STORE"], some 3),
   (["CONST", "CONST", "STORE"], some 3), (["CONST", "CONST", "STORE"], some 3),
   (["CONST", "VCONST", "VSTORE"], some 3), (["CONST", "VCONST", "VSTORE"], some 3),
   (["CONST", "VCONST", "VSTORE_LANE"], some 3), (["CONST", "VCONST", "VSTORE_LANE"], some 3),
   (["CONST", "MEMORY.GROW"], some 2), (["CONST", "MEMORY.GROW"], some 2), (["DATA.DROP"], some 1),
   (["STRUCT.NEW"], none), (["REF.NULL_ADDR", "STRUCT.SET"], some 3),
   (["REF.STRUCT_ADDR", "STRUCT.SET"], some 3), (["ARRAY.NEW_FIXED"], none),
   (["REF.NULL_ADDR", "CONST", "ARRAY.SET"], some 4),
   (["REF.ARRAY_ADDR", "CONST", "ARRAY.SET"], some 4),
   (["REF.ARRAY_ADDR", "CONST", "ARRAY.SET"], some 4)]

/-! ## The checks -/

/-- The constructors of the images of Core values (`num`, `vec` and the eight references). -/
def valTags : List MixopS :=
  ["CONST", "VCONST", "REF.NULL_ADDR", "REF.I31_NUM", "REF.STRUCT_ADDR", "REF.ARRAY_ADDR",
   "REF.FUNC_ADDR", "REF.EXN_ADDR", "REF.HOST_ADDR", "REF.EXTERN"]

/-- `l` is `k` values (constructors in `valTags`) followed by one value that, if an injection,
is named `t` (an encoded instruction is an injection named by its head, or junk). -/
def FlatK (k : Nat) (t : MixopS) (l : List Value) : Prop :=
  ∃ vs x, l = vs ++ [x] ∧ vs.length = k ∧ Sim.RefsGC.TagsIn valTags vs ∧ Sim.RefsGC.TagsIn [t] [x]

/-- A row names a constructor outside `S`. -/
def outside (S : List MixopS) (row : List MixopS × Option Nat) : Bool :=
  row.1.any fun op => !S.contains op

/-- No rule of `T` fires on a proper infix of a `FlatK k t` code. -/
def chkProper (k : Nat) (t : MixopS) (T : List (List MixopS × Option Nat)) : Bool :=
  T.all fun row => outside (t :: valTags) row || (outside valTags row && row.2.any (k < ·))

/-- No rule of `T` fires on a whole `FlatK k t` code. -/
def chkFull (k : Nat) (t : MixopS) (T : List (List MixopS × Option Nat)) : Bool :=
  T.all fun row => outside (t :: valTags) row || row.2.any (· != k + 1)

/-- The rules of `Step` the inversion reads by their table (all but the first three). -/
def stepRestT : List (List MixopS × Option Nat) := stepInfoT.drop 3

/-- **A `Step_pure` redex of shape `FlatK k t`**: every proper infix is inert, and at the whole
redex no `Step_read` rule and no `Step` rule beyond the first three fires. -/
def pureOk (k : Nat) (t : MixopS) : Bool :=
  chkProper k t pureInfoT && chkProper k t readInfoT && chkProper k t stepRestT &&
    chkFull k t readInfoT && chkFull k t stepRestT

/-- **A `Step_read` redex of shape `FlatK k t`**: every proper infix is inert, and at the whole
redex no `Step_pure` rule and no `Step` rule beyond the first three fires. -/
def readOk (k : Nat) (t : MixopS) : Bool :=
  chkProper k t pureInfoT && chkProper k t readInfoT && chkProper k t stepRestT &&
    chkFull k t pureInfoT && chkFull k t stepRestT

/-! ## The checks, on the instruction constructors only

Every row of the three tables names exactly one constructor outside `valTags` (or none, for
`Step` rules 0–2), so the checks only compare `t` against that one. `FwdB30XTables` proves
`pureOk k t = pureOkN k t` and `readOk k t = readOkN k t`; the `…N` forms are the ones
`decide` evaluates. -/

/-- A row with its value constructors dropped. -/
def nonV (row : List MixopS × Option Nat) : List MixopS × Option Nat :=
  (row.1.filter fun op => !valTags.contains op, row.2)

/-- `chkProper`, on rows without value constructors. -/
def chkProperN (k : Nat) (t : MixopS) (N : List (List MixopS × Option Nat)) : Bool :=
  N.all fun row => row.1.any (· != t) || (!row.1.isEmpty && row.2.any (k < ·))

/-- `chkFull`, on rows without value constructors. -/
def chkFullN (k : Nat) (t : MixopS) (N : List (List MixopS × Option Nat)) : Bool :=
  N.all fun row => row.1.any (· != t) || row.2.any (· != k + 1)

/-- `pureInfoT.map nonV`. -/
def pureNVT : List (List MixopS × Option Nat) :=
  [(["UNREACHABLE"], some 1), (["NOP"], some 1), (["DROP"], some 2), (["SELECT"], some 4),
   (["SELECT"], some 4), (["IF%%ELSE%"], some 2), (["IF%%ELSE%"], some 2),
   (["LABEL_%{%}%"], some 1), (["LABEL_%{%}%"], some 1), (["LABEL_%{%}%"], some 1),
   (["HANDLER_%{%}%"], some 1), (["BR_IF"], some 2), (["BR_IF"], some 2), (["BR_TABLE"], some 2),
   (["BR_TABLE"], some 2), (["BR_ON_NULL"], some 2), (["BR_ON_NULL"], some 2),
   (["BR_ON_NON_NULL"], some 2), (["BR_ON_NON_NULL"], some 2), (["CALL_INDIRECT"], some 1),
   (["RETURN_CALL_INDIRECT"], some 1), (["FRAME_%{%}%"], some 1), (["FRAME_%{%}%"], some 1),
   (["LABEL_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["TRAP"], none), (["LABEL_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["FRAME_%{%}%"], some 1), (["LOCAL.TEE"], some 2), (["REF.I31"], some 2),
   (["REF.IS_NULL"], some 2), (["REF.IS_NULL"], some 2), (["REF.AS_NON_NULL"], some 2),
   (["REF.AS_NON_NULL"], some 2), (["REF.EQ"], some 3), (["REF.EQ"], some 3), (["REF.EQ"], some 3),
   (["I31.GET"], some 2), (["I31.GET"], some 2), (["ARRAY.NEW"], some 3),
   (["EXTERN.CONVERT_ANY"], some 2), (["EXTERN.CONVERT_ANY"], some 2),
   (["ANY.CONVERT_EXTERN"], some 2), (["ANY.CONVERT_EXTERN"], some 2), (["UNOP"], some 2),
   (["UNOP"], some 2), (["BINOP"], some 3), (["BINOP"], some 3), (["TESTOP"], some 2),
   (["RELOP"], some 3), (["CVTOP"], some 2), (["CVTOP"], some 2), (["VVUNOP"], some 2),
   (["VVBINOP"], some 3), (["VVTERNOP"], some 4), (["VVTESTOP"], some 2), (["VUNOP"], some 2),
   (["VUNOP"], some 2), (["VBINOP"], some 3), (["VBINOP"], some 3), (["VTERNOP"], some 4),
   (["VTERNOP"], some 4), (["VTESTOP"], some 2), (["VRELOP"], some 3), (["VSHIFTOP"], some 3),
   (["VBITMASK"], some 2), (["VSWIZZLOP"], some 3), (["VSHUFFLE"], some 3), (["VSPLAT"], some 2),
   (["VEXTRACT_LANE"], some 2), (["VEXTRACT_LANE"], some 2), (["VREPLACE_LANE"], some 3),
   (["VEXTUNOP"], some 2), (["VEXTBINOP"], some 3), (["VEXTTERNOP"], some 4), (["VNARROW"], some 3),
   (["VCVTOP"], some 2)]

/-- `readInfoT.map nonV`. -/
def readNVT : List (List MixopS × Option Nat) :=
  [(["BLOCK"], none), (["LOOP"], none), (["BR_ON_CAST"], some 2), (["BR_ON_CAST"], some 2),
   (["BR_ON_CAST_FAIL"], some 2), (["BR_ON_CAST_FAIL"], some 2), (["CALL"], some 1),
   (["RETURN_CALL"], some 1), (["LABEL_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["FRAME_%{%}%"], some 1), (["FRAME_%{%}%"], some 1), (["THROW_REF"], some 2),
   (["THROW_REF"], none), (["LABEL_%{%}%"], some 1), (["FRAME_%{%}%"], some 1),
   (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["TRY_TABLE"], none), (["LOCAL.GET"], some 1), (["GLOBAL.GET"], some 1),
   (["TABLE.GET"], some 2), (["TABLE.GET"], some 2), (["TABLE.SIZE"], some 1),
   (["TABLE.FILL"], some 4), (["TABLE.FILL"], some 4), (["TABLE.FILL"], some 4),
   (["TABLE.COPY"], some 4), (["TABLE.COPY"], some 4), (["TABLE.COPY"], some 4),
   (["TABLE.COPY"], some 4), (["TABLE.INIT"], some 4), (["TABLE.INIT"], some 4),
   (["TABLE.INIT"], some 4), (["LOAD"], some 2), (["LOAD"], some 2), (["LOAD"], some 2),
   (["LOAD"], some 2), (["VLOAD"], some 2), (["VLOAD"], some 2), (["VLOAD"], some 2),
   (["VLOAD"], some 2), (["VLOAD"], some 2), (["VLOAD"], some 2), (["VLOAD"], some 2),
   (["VLOAD"], some 2), (["VLOAD_LANE"], some 3), (["VLOAD_LANE"], some 3),
   (["MEMORY.SIZE"], some 1), (["MEMORY.FILL"], some 4), (["MEMORY.FILL"], some 4),
   (["MEMORY.FILL"], some 4), (["MEMORY.COPY"], some 4), (["MEMORY.COPY"], some 4),
   (["MEMORY.COPY"], some 4), (["MEMORY.COPY"], some 4), (["MEMORY.INIT"], some 4),
   (["MEMORY.INIT"], some 4), (["MEMORY.INIT"], some 4), (["REF.NULL"], some 1),
   (["REF.FUNC"], some 1), (["REF.TEST"], some 2), (["REF.TEST"], some 2), (["REF.CAST"], some 2),
   (["REF.CAST"], some 2), (["STRUCT.NEW_DEFAULT"], some 1), (["STRUCT.GET"], some 2),
   (["STRUCT.GET"], some 2), (["ARRAY.NEW_DEFAULT"], some 2), (["ARRAY.NEW_ELEM"], some 3),
   (["ARRAY.NEW_ELEM"], some 3), (["ARRAY.NEW_DATA"], some 3), (["ARRAY.NEW_DATA"], some 3),
   (["ARRAY.GET"], some 3), (["ARRAY.GET"], some 3), (["ARRAY.GET"], some 3),
   (["ARRAY.LEN"], some 2), (["ARRAY.LEN"], some 2), (["ARRAY.FILL"], some 5),
   (["ARRAY.FILL"], some 5), (["ARRAY.FILL"], some 5), (["ARRAY.FILL"], some 5),
   (["ARRAY.COPY"], some 6), (["ARRAY.COPY"], some 6), (["ARRAY.COPY"], some 6),
   (["ARRAY.COPY"], some 6), (["ARRAY.COPY"], some 6), (["ARRAY.COPY"], some 6),
   (["ARRAY.COPY"], some 6), (["ARRAY.INIT_ELEM"], some 5), (["ARRAY.INIT_ELEM"], some 5),
   (["ARRAY.INIT_ELEM"], some 5), (["ARRAY.INIT_ELEM"], some 5), (["ARRAY.INIT_ELEM"], some 5),
   (["ARRAY.INIT_DATA"], some 5), (["ARRAY.INIT_DATA"], some 5), (["ARRAY.INIT_DATA"], some 5),
   (["ARRAY.INIT_DATA"], some 5), (["ARRAY.INIT_DATA"], some 5)]

/-- `stepInfoT.map nonV`. -/
def stepNVT : List (List MixopS × Option Nat) :=
  [([], none), ([], none), ([], none), (["LABEL_%{%}%"], some 1), (["HANDLER_%{%}%"], some 1),
   (["FRAME_%{%}%"], some 1), (["CALL_REF"], some 2), (["CALL_REF"], none), (["CALL_REF"], none),
   (["CALL_REF"], none), (["THROW"], none), (["LOCAL.SET"], some 2), (["GLOBAL.SET"], some 2),
   (["TABLE.SET"], some 3), (["TABLE.SET"], some 3), (["TABLE.GROW"], some 3),
   (["TABLE.GROW"], some 3), (["ELEM.DROP"], some 1), (["STORE"], some 3), (["STORE"], some 3),
   (["STORE"], some 3), (["STORE"], some 3), (["VSTORE"], some 3), (["VSTORE"], some 3),
   (["VSTORE_LANE"], some 3), (["VSTORE_LANE"], some 3), (["MEMORY.GROW"], some 2),
   (["MEMORY.GROW"], some 2), (["DATA.DROP"], some 1), (["STRUCT.NEW"], none),
   (["STRUCT.SET"], some 3), (["STRUCT.SET"], some 3), (["ARRAY.NEW_FIXED"], none),
   (["ARRAY.SET"], some 4), (["ARRAY.SET"], some 4), (["ARRAY.SET"], some 4)]

/-- `pureOk`, on the `nonV` tables. -/
def pureOkN (k : Nat) (t : MixopS) : Bool :=
  chkProperN k t pureNVT && chkProperN k t readNVT && chkProperN k t (stepNVT.drop 3) &&
    chkFullN k t readNVT && chkFullN k t (stepNVT.drop 3)

/-- `readOk`, on the `nonV` tables. -/
def readOkN (k : Nat) (t : MixopS) : Bool :=
  chkProperN k t pureNVT && chkProperN k t readNVT && chkProperN k t (stepNVT.drop 3) &&
    chkFullN k t pureNVT && chkFullN k t (stepNVT.drop 3)

/-! ## The redex shapes the inversion is used at -/

/-- The shapes `(k, t)` of the `Step_pure` redexes of `FwdX30.PureHeadX` that use primitives:
the numeric and vector families, `ref.i31` and `i31.get` at a number. -/
def pureCombos : List (Nat × MixopS) :=
  [(1, "UNOP"), (2, "BINOP"), (1, "TESTOP"), (2, "RELOP"), (1, "CVTOP"), (1, "VVUNOP"),
   (2, "VVBINOP"), (3, "VVTERNOP"), (1, "VVTESTOP"), (1, "VUNOP"), (2, "VBINOP"), (3, "VTERNOP"),
   (1, "VTESTOP"), (2, "VRELOP"), (2, "VSHIFTOP"), (1, "VBITMASK"), (2, "VSWIZZLOP"),
   (2, "VSHUFFLE"), (1, "VSPLAT"), (1, "VEXTRACT_LANE"), (2, "VREPLACE_LANE"), (1, "VEXTUNOP"),
   (2, "VEXTBINOP"), (3, "VEXTTERNOP"), (2, "VNARROW"), (1, "VCVTOP"), (1, "REF.I31"),
   (1, "I31.GET")]

/-- The shapes `(k, t)` of the `Step_read` redexes of `FwdX30.ReadHeadX` that read the store:
`ref.func` and the table, memory and aggregate reads. -/
def readCombos : List (Nat × MixopS) :=
  [(0, "REF.FUNC"), (1, "TABLE.GET"), (0, "TABLE.SIZE"), (3, "TABLE.FILL"), (3, "TABLE.COPY"),
   (3, "TABLE.INIT"), (1, "LOAD"), (1, "VLOAD"), (2, "VLOAD_LANE"), (0, "MEMORY.SIZE"),
   (3, "MEMORY.FILL"), (3, "MEMORY.COPY"), (3, "MEMORY.INIT"), (0, "STRUCT.NEW_DEFAULT"),
   (1, "STRUCT.GET"), (1, "ARRAY.NEW_DEFAULT"), (2, "ARRAY.NEW_ELEM"), (2, "ARRAY.NEW_DATA"),
   (2, "ARRAY.GET"), (1, "ARRAY.LEN"), (4, "ARRAY.FILL"), (5, "ARRAY.COPY"),
   (4, "ARRAY.INIT_ELEM"), (4, "ARRAY.INIT_DATA")]

/-! ## The store-reading redexes reached -/

section Reads

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **The `Step_read` rules of `FwdX30.ReadHeadX` that read the store**, which `FwdB30.ReadG`
leaves out and the inversion reaches: `ref.func` and the table, memory and aggregate reads. -/
inductive ReadB (P : Profile) : Config H → List Admin → Prop where
  /-- `Step_read/ref.func`. -/
  | refFunc {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
      (h : f.module.funcs[x.toNat]? = some a) :
      ReadB P ⟨s, f, [.plain (.refFunc x)]⟩ [.ref (.func a)]
  /-- The table rules of `Step_read`. -/
  | table {c : Config H} {is' : List Admin} (h : FwdX30.TableRead P c is') : ReadB P c is'
  /-- The memory rules of `Step_read`. -/
  | memory {c : Config H} {is' : List Admin} (h : FwdX30.MemRead P c is') : ReadB P c is'
  /-- The aggregate rules of `Step_read`. -/
  | aggregate {c : Config H} {is' : List Admin} (h : FwdX30.AggRead c is') : ReadB P c is'

/-- **The block rules of `FwdX30.CtrlRead`**, which `FwdB30.ReadG` leaves out: `block`, `loop`
and `try_table`. Their value prefix has any length, so they are not `FlatK` redexes of a fixed
shape; the inversion uses the shape of Core's successor instead (one label or handler). -/
inductive ReadC : Config H → List Admin → Prop where
  /-- `Step_read/block`. -/
  | block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List Silmaril.Wasm.Validation.CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      ReadC ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
        [.label t₂.length [] (vals vs ++ expression body)]
  /-- `Step_read/loop`. -/
  | loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List Silmaril.Wasm.Validation.CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      ReadC ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
        [.label t₁.length [.loop bt body] (vals vs ++ expression body)]
  /-- `Step_read/try_table`. -/
  | tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
      {vs : List Val} {t₁ t₂ : List Silmaril.Wasm.Validation.CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      ReadC ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
        [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]

/-- **The `throw_ref` handler rules of `FwdX30.CtrlRead` that read the store**, which
`FwdB30.ReadG` leaves out: `catch`, `catch_ref` and `next`. The redex is one handler. -/
inductive ReadH : Config H → List Admin → Prop where
  /-- `Step_read/throw_ref-handler-catch`. -/
  | catch_ {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
      {a : Nat} {e : ExnInst} (he : s.exns[a]? = some e)
      (ht : f.module.tags[x.toNat]? = some e.tag) :
      ReadH ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩
        (vals e.fields ++ [.plain (.br l)])
  /-- `Step_read/throw_ref-handler-catch_ref`. -/
  | catchRef {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch}
      {a : Nat} {e : ExnInst} (he : s.exns[a]? = some e)
      (ht : f.module.tags[x.toNat]? = some e.tag) :
      ReadH ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
        (vals e.fields ++ [.ref (.exn a), .plain (.br l)])
  /-- `Step_read/throw_ref-handler-next`. -/
  | next {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch} {a : Nat}
      (h : ¬ CatchMatches s f a c) :
      ReadH ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ [.handler n cs (throwing a)]

end Reads

end Silmaril.Wasm.SpecTec.Institution.FwdB30X
