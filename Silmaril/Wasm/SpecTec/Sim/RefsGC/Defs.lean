module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# SpecTec ↔ Core 3.0, family R (references and GC): definitions

Two kinds of definitions.

1. **Opcode tags, for `otherwise` premises.** An `otherwise` premise of rule `i` holds when no
   earlier rule fires on the same left-hand side (`Sim.otherwiseAt`). Almost every earlier rule
   is excluded by its *opcode*: the left-hand side of every rule of `Step_pure`, `Step_read` and
   `Step` (except `Step/pure`, `Step/read`, `Step/ctxt-instrs`) names at least one instruction
   constructor at top level (`ruleTags`), and a left-hand side whose top-level constructors all lie
   in a set `S` (`TagsIn`) cannot be matched by a rule naming a constructor outside `S`. The rules
   that share an opcode with the instruction at hand are the only ones left to invert by hand.
   `pureTagTable` and `readTagTable` are the tags of the 79 `Step_pure` and 103 `Step_read` rules,
   checked against the pinned script (`Proofs/…/RefsGC/Otherwise.lean`).
2. **The family's assumptions** (`RTyping`), stated as structures so that the per-rule theorems
   are conditional on exactly these and on nothing else; see `docs/projects/spectec/README.md`, family R.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefsGC

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## Opcode tags -/

/-- The constructor of an expression that is literally an injection. -/
def caseTag? : Exp → Option MixopS
  | .caseE op _ => some op
  | _ => none

/-- The constructors a list pattern forces to occur at top level of the list it denotes: the
literal injections of `listE` components, through `catE`. -/
def mustTags : Exp → List MixopS
  | .listE es => es.filterMap caseTag?
  | .catE e₁ e₂ => mustTags e₁ ++ mustTags e₂
  | _ => []

/-- The forced constructors of a left-hand side, looking through `z; instr*`. -/
def codeTags : Exp → List MixopS
  | .caseE "%;%" (.tupE [_, c]) => mustTags c
  | e => mustTags e

/-- The forced constructors of a conclusion `lhs ~> rhs`. -/
def concTags : Exp → List MixopS
  | .tupE [l, _] => codeTags l
  | _ => []

/-- The forced constructors of a rule `lhs ~> rhs`. -/
def ruleTags : Rule → List MixopS
  | .ruleD _ _ _ e _ => concTags e

/-- Every top-level injection in `l` has its constructor in `S`. -/
def TagsIn (S : List MixopS) (l : List Value) : Prop :=
  ∀ x ∈ l, ∀ op w, x = .case op w → op ∈ S

/-- A left-hand side whose code is `l` with `TagsIn S l`: `instr*` (for `Step_pure`) or
`z; instr*` (for `Step_read` and `Step`). -/
def LhsIn (S : List MixopS) (a : Value) : Prop :=
  (∃ l, a = .list l ∧ TagsIn S l) ∨ (∃ z l, a = cfgV z l ∧ TagsIn S l)

/-- Rules `j < i`, except those in `exc`, each name a constructor outside `S`, by the tag table
`T`. -/
def checkAvoid (T : List (List MixopS)) (i : Nat) (exc : List Nat) (S : List MixopS) : Bool :=
  (List.range i).all fun j => exc.contains j || (T[j]?.getD []).any fun op => !(S.contains op)

/-- The tags of the 79 rules of `Step_pure`, in order. -/
def pureTagTable : List (List MixopS) :=
  [["UNREACHABLE"], ["NOP"], ["DROP"], ["CONST", "SELECT"], ["CONST", "SELECT"],
   ["CONST", "IF%%ELSE%"], ["CONST", "IF%%ELSE%"], ["LABEL_%{%}%"], ["LABEL_%{%}%"],
   ["LABEL_%{%}%"], ["HANDLER_%{%}%"], ["CONST", "BR_IF"], ["CONST", "BR_IF"],
   ["CONST", "BR_TABLE"], ["CONST", "BR_TABLE"], ["BR_ON_NULL"], ["BR_ON_NULL"],
   ["BR_ON_NON_NULL"], ["BR_ON_NON_NULL"], ["CALL_INDIRECT"], ["RETURN_CALL_INDIRECT"],
   ["FRAME_%{%}%"], ["FRAME_%{%}%"], ["LABEL_%{%}%"], ["HANDLER_%{%}%"], ["HANDLER_%{%}%"],
   ["TRAP"], ["LABEL_%{%}%"], ["HANDLER_%{%}%"], ["FRAME_%{%}%"], ["LOCAL.TEE"],
   ["CONST", "REF.I31"], ["REF.IS_NULL"], ["REF.IS_NULL"], ["REF.AS_NON_NULL"],
   ["REF.AS_NON_NULL"], ["REF.EQ"], ["REF.EQ"], ["REF.EQ"], ["REF.NULL_ADDR", "I31.GET"],
   ["REF.I31_NUM", "I31.GET"], ["CONST", "ARRAY.NEW"], ["EXTERN.CONVERT_ANY"],
   ["EXTERN.CONVERT_ANY"], ["REF.NULL_ADDR", "ANY.CONVERT_EXTERN"],
   ["REF.EXTERN", "ANY.CONVERT_EXTERN"]]

/-- The tags of the first 103 rules of `Step_read`, in order. -/
def readTagTable : List (List MixopS) :=
  [["BLOCK"], ["LOOP"], ["BR_ON_CAST"], ["BR_ON_CAST"], ["BR_ON_CAST_FAIL"], ["BR_ON_CAST_FAIL"],
   ["CALL"], ["RETURN_CALL"], ["LABEL_%{%}%"], ["HANDLER_%{%}%"], ["FRAME_%{%}%"],
   ["FRAME_%{%}%"], ["REF.NULL_ADDR", "THROW_REF"], ["REF.EXN_ADDR", "THROW_REF"],
   ["LABEL_%{%}%"], ["FRAME_%{%}%"], ["HANDLER_%{%}%"], ["HANDLER_%{%}%"], ["HANDLER_%{%}%"],
   ["HANDLER_%{%}%"], ["HANDLER_%{%}%"], ["HANDLER_%{%}%"], ["TRY_TABLE"], ["LOCAL.GET"],
   ["GLOBAL.GET"], ["CONST", "TABLE.GET"], ["CONST", "TABLE.GET"], ["TABLE.SIZE"],
   ["CONST", "CONST", "TABLE.FILL"], ["CONST", "CONST", "TABLE.FILL"],
   ["CONST", "CONST", "TABLE.FILL"], ["CONST", "CONST", "CONST", "TABLE.COPY"],
   ["CONST", "CONST", "CONST", "TABLE.COPY"], ["CONST", "CONST", "CONST", "TABLE.COPY"],
   ["CONST", "CONST", "CONST", "TABLE.COPY"], ["CONST", "CONST", "CONST", "TABLE.INIT"],
   ["CONST", "CONST", "CONST", "TABLE.INIT"], ["CONST", "CONST", "CONST", "TABLE.INIT"],
   ["CONST", "LOAD"], ["CONST", "LOAD"], ["CONST", "LOAD"], ["CONST", "LOAD"],
   ["CONST", "VLOAD"], ["CONST", "VLOAD"], ["CONST", "VLOAD"], ["CONST", "VLOAD"],
   ["CONST", "VLOAD"], ["CONST", "VLOAD"], ["CONST", "VLOAD"], ["CONST", "VLOAD"],
   ["CONST", "VCONST", "VLOAD_LANE"], ["CONST", "VCONST", "VLOAD_LANE"], ["MEMORY.SIZE"],
   ["CONST", "CONST", "MEMORY.FILL"], ["CONST", "CONST", "MEMORY.FILL"],
   ["CONST", "CONST", "MEMORY.FILL"], ["CONST", "CONST", "CONST", "MEMORY.COPY"],
   ["CONST", "CONST", "CONST", "MEMORY.COPY"], ["CONST", "CONST", "CONST", "MEMORY.COPY"],
   ["CONST", "CONST", "CONST", "MEMORY.COPY"], ["CONST", "CONST", "CONST", "MEMORY.INIT"],
   ["CONST", "CONST", "CONST", "MEMORY.INIT"], ["CONST", "CONST", "CONST", "MEMORY.INIT"],
   ["REF.NULL"], ["REF.FUNC"], ["REF.TEST"], ["REF.TEST"], ["REF.CAST"], ["REF.CAST"],
   ["STRUCT.NEW_DEFAULT"], ["REF.NULL_ADDR", "STRUCT.GET"], ["REF.STRUCT_ADDR", "STRUCT.GET"],
   ["CONST", "ARRAY.NEW_DEFAULT"], ["CONST", "CONST", "ARRAY.NEW_ELEM"],
   ["CONST", "CONST", "ARRAY.NEW_ELEM"], ["CONST", "CONST", "ARRAY.NEW_DATA"],
   ["CONST", "CONST", "ARRAY.NEW_DATA"], ["REF.NULL_ADDR", "CONST", "ARRAY.GET"],
   ["REF.ARRAY_ADDR", "CONST", "ARRAY.GET"], ["REF.ARRAY_ADDR", "CONST", "ARRAY.GET"],
   ["REF.NULL_ADDR", "ARRAY.LEN"], ["REF.ARRAY_ADDR", "ARRAY.LEN"],
   ["REF.NULL_ADDR", "CONST", "CONST", "ARRAY.FILL"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.FILL"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.FILL"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.FILL"],
   ["REF.NULL_ADDR", "CONST", "CONST", "CONST", "ARRAY.COPY"],
   ["CONST", "REF.NULL_ADDR", "CONST", "CONST", "ARRAY.COPY"],
   ["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"],
   ["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"],
   ["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"],
   ["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"],
   ["REF.ARRAY_ADDR", "CONST", "REF.ARRAY_ADDR", "CONST", "CONST", "ARRAY.COPY"],
   ["REF.NULL_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_ELEM"],
   ["REF.NULL_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"],
   ["REF.ARRAY_ADDR", "CONST", "CONST", "CONST", "ARRAY.INIT_DATA"]]

/-- The constructors `refToValue` produces. -/
def refTags : List MixopS :=
  ["REF.I31_NUM", "REF.NULL_ADDR", "REF.STRUCT_ADDR", "REF.ARRAY_ADDR", "REF.FUNC_ADDR",
   "REF.EXN_ADDR", "REF.HOST_ADDR", "REF.EXTERN"]

/-- The constructors `valV` produces. -/
def valTags : List MixopS := "CONST" :: "VCONST" :: refTags

/-! ## The family's assumptions -/

section Assumptions

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm.Validation (CRefType)

/-- The module instance encoding at `CT`. -/
abbrev moduleInstToValue' (m : ModuleInst) : Value :=
  Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT m

/-- The IL type `ref`. -/
abbrev refT : Typ := .varT "ref" []
/-- The IL type `val`. -/
abbrev valT : Typ := .varT "val" []
/-- The IL type `num_(I32)`. -/
abbrev i32T : Typ := .varT "num_" [.expA (.caseE "I32" (.tupE []))]

/-- The IL type `heaptype`. -/
abbrev heaptypeT : Typ := .varT "heaptype" []
/-- The IL type `reftype`. -/
abbrev reftypeT : Typ := .varT "reftype" []
/-- The IL type `idx`. -/
abbrev idxT : Typ := .varT "idx" []
/-- The IL type `labelidx`. -/
abbrev labelidxT : Typ := .varT "labelidx" []

/-- Instructions with one immediate, and the type the reduction rules quantify it at (the IL's
`instr` case type, or an alias of it). -/
def argTypes : List (MixopS × Typ) :=
  [("REF.NULL", heaptypeT), ("REF.FUNC", idxT), ("REF.TEST", reftypeT), ("REF.CAST", reftypeT)]

/-- Instructions with three immediates, and their types. -/
def argTypes3 : List (MixopS × List Typ) :=
  [("BR_ON_CAST", [labelidxT, reftypeT, reftypeT]),
   ("BR_ON_CAST_FAIL", [labelidxT, reftypeT, reftypeT])]

/-- **Typing facts the family uses** (to be discharged by family E, which owns the typing of the
encoding). Each is a fact about `Sem.HasTyp` on encoded values: a reference typed as an
instruction is typed as a `ref` (the IL's `instr` includes `ref` by subtyping); the payload of a
typed `REF.EXTERN` is a `ref`; the numerals and signedness flags are typed. -/
structure RTyping (env : Env) : Prop where
  /-- A reference that is a typed instruction is a typed `ref`. -/
  ref : ∀ r : Ref, TypedV env instrsT (.list [refToValue r]) → TypedV env refT (refToValue r)
  /-- The payload of a typed `REF.EXTERN` is a typed `ref`. -/
  externArg : ∀ r : Ref, TypedV env instrsT (.list [refToValue (.extern r)]) →
    TypedV env refT (refToValue r)
  /-- A value that is a typed instruction is a typed `val`. -/
  val : ∀ v : Val, TypedV env instrsT (.list [valV v]) → TypedV env valT (valV v)
  /-- `i32` numerals. -/
  i32 : ∀ b : BitVec 32, TypedV env i32T (pctV b.toNat)
  /-- `u31` numerals. -/
  u31 : ∀ b : BitVec 31, TypedV env (.varT "u31" []) (pctV b.toNat)
  /-- Signedness flags. -/
  sx : ∀ s : Signedness, TypedV env (.varT "sx" []) (sxV s)
  /-- Indices (`u32`, `%`-wrapped) at `idx`. -/
  idx : ∀ n : Nat, n < 2 ^ 32 → TypedV env idxT (pctV n)
  /-- Indices at `fieldidx`. -/
  fieldidx : ∀ n : Nat, n < 2 ^ 32 → TypedV env (.varT "fieldidx" []) (pctV n)
  /-- Naturals at `n`. -/
  nat : ∀ n : Nat, TypedV env nT (.num (.natN n))
  /-- Naturals at `addr`. -/
  addr : ∀ n : Nat, TypedV env (.varT "addr" []) (.num (.natN n))
  /-- Optional signedness flags at `sx?`. -/
  sxOpt : ∀ o : Option Signedness, TypedV env (.iterT (.varT "sx" []) .opt) (.opt (o.map sxV))
  /-- The immediate of a typed one-immediate instruction (`argTypes`). -/
  arg : ∀ (op : MixopS) (w : Value) (t : Typ), (op, t) ∈ argTypes →
    TypedV env instrsT (.list [.case op w]) → TypedV env t w
  /-- The immediates of a typed three-immediate instruction (`argTypes3`). -/
  arg3 : ∀ (op : MixopS) (w₁ w₂ w₃ : Value) (t₁ t₂ t₃ : Typ), (op, [t₁, t₂, t₃]) ∈ argTypes3 →
    TypedV env instrsT (.list [.case op (.tuple [w₁, w₂, w₃])]) →
    TypedV env t₁ w₁ ∧ TypedV env t₂ w₂ ∧ TypedV env t₃ w₃

/-- **The two numeric primitives the `i31` rules call** (to be discharged by family N, which owns
the numeric part of `B`): `$wrap__(32, 31, i)` and `$extend__(31, 32, sx, i)` agree with Core's
`setWidth` and `signExtend`. Stated for arbitrary argument expressions, since evaluation is
compositional, in every scope that binds term variables only (`ValsOnly`: a scope binding a
definition variable could rename the callee, so the unrestricted statement would be false). -/
structure RFuns (env : Env) : Prop where
  /-- `$wrap__(32, 31, i)`. -/
  wrap : ∀ (ρ : VarEnv) (e : Exp) (i : BitVec 32), ValsOnly ρ → EvalExp env ρ e (pctV i.toNat) →
    EvalExp env ρ (.callE "wrap__" [.expA (.numE (.natN 32)), .expA (.numE (.natN 31)), .expA e])
      (pctV (i.setWidth 31).toNat)
  /-- `$extend__(31, 32, sx, i)`. -/
  extend : ∀ (ρ : VarEnv) (es e : Exp) (s : Signedness) (i : BitVec 31), ValsOnly ρ →
    EvalExp env ρ es (sxV s) → EvalExp env ρ e (pctV i.toNat) →
    EvalExp env ρ (.callE "extend__" [.expA (.numE (.natN 31)), .expA (.numE (.natN 32)),
      .expA es, .expA e])
      (pctV (match s with | .signed => i.signExtend 32 | .unsigned => i.setWidth 32).toNat)

/-- **Store-reading primitives** (to be proved by unfolding the spec functions, or supplied by
the encoding family): `$moduleinst(z)` is the frame's module, `$inst_reftype(m, rt)` is Core's
`ModuleInst.instRef`. Stated in scopes binding term variables only (`ValsOnly`): in a scope that
binds a definition variable `moduleinst ↦ g` the call evaluates `$g` instead, so the
unrestricted statement was false. -/
structure RStoreFuns (env : Env) : Prop where
  /-- `$moduleinst((s; f)) = f.MODULE`. -/
  moduleinst : ∀ {H : Type} (hn : H → String) (ρ : VarEnv) (e : Exp) (s : Store H) (f : Frame),
    ValsOnly ρ → EvalExp env ρ e (stateV hn s f) →
    EvalExp env ρ (.callE "moduleinst" [.expA e]) (moduleInstToValue' f.module)
  /-- `$arrayinst((s; f)) = s.ARRAYS`. -/
  arrayinst : ∀ {H : Type} (hn : H → String) (ρ : VarEnv) (e : Exp) (s : Store H) (f : Frame),
    ValsOnly ρ → EvalExp env ρ e (stateV hn s f) →
    EvalExp env ρ (.callE "arrayinst" [.expA e]) (.list (s.arrays.map arrayInstV))
  /-- `$structinst((s; f)) = s.STRUCTS`. -/
  structinst : ∀ {H : Type} (hn : H → String) (ρ : VarEnv) (e : Exp) (s : Store H) (f : Frame),
    ValsOnly ρ → EvalExp env ρ e (stateV hn s f) →
    EvalExp env ρ (.callE "structinst" [.expA e]) (.list (s.structs.map structInstV))
  /-- `$elem((s; f), y)` is the element instance `y` resolves to. -/
  elem : ∀ {H : Type} (hn : H → String) (ρ : VarEnv) (ez ey : Exp) (s : Store H) (f : Frame)
    (y : ElemIdx) (ea : Nat) (ei : ElemInst), ValsOnly ρ → s.elem? f y = some (ea, ei) →
    EvalExp env ρ ez (stateV hn s f) → EvalExp env ρ ey (Encode.toValue y) →
    EvalExp env ρ (.callE "elem" [.expA ez, .expA ey])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.elemInstToValue CT ei)
  /-- `$inst_reftype(m, rt)`. -/
  instReftype : ∀ (ρ : VarEnv) (e₁ e₂ : Exp) (m : ModuleInst) (rt : RefType), ValsOnly ρ →
    EvalExp env ρ e₁ (moduleInstToValue' m) → EvalExp env ρ e₂ (Encode.toValue rt) →
    EvalExp env ρ (.callE "inst_reftype" [.expA e₁, .expA e₂]) (CT.elemType (m.instRef rt))

/-- **`Ref_ok` is Core's `RefOk`**, under any reading of `otherwise` (`Ref_ok` and the relations
it uses have no `otherwise` premise). This is the reference-typing bridge the cast rules need; it
is an assumption of the family, to be proved by induction on both sides. -/
structure RefOkBridge (env : Env) : Prop where
  /-- `s ⊢ ref : rt` iff `RefOk s r rt`. -/
  refOk : ∀ {H : Type} (hn : H → String) (O : ElseI) (s : Store H) (r : Ref) (rt : CRefType),
    DDerives env O "Ref_ok" "%|-%:%" [] (.tuple [storeV hn s, refToValue r, CT.elemType rt]) ↔
      RefOk s r rt

end Assumptions

end Silmaril.Wasm.SpecTec.Sim.RefsGC
