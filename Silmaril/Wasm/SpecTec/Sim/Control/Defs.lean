module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# SpecTec ↔ Core 3.0, family C (control and calls): definitions

The family's forward lemmas build SpecTec derivations under the declarative reading, and every
rule quantifies over its variables *with their IL types* (`QuantsOk`). The typing of an encoded
immediate or sub-sequence is family E's business; this file names exactly the typing facts the
control rules consume, as one hypothesis structure `CtrlTyping`, so that every lemma of the family
is stated against it and family E can discharge it once.

Each field is one of two kinds, and none says anything about the reduction relations:

* a **closed fact** about the encoding of a Core datum that is always in range (`nat`, `labelidx`,
  `idx`, `i32`, `typeuseIdx`): a natural number is an `n`, a label index is a `labelidx`, …;
* an **inversion** of the IL type `instr` at one variant case (`ifInv`, `blockInv`, `loopInv`,
  `callRefInv`, `retCallRefInv`): a typed `IF bt instr* ELSE instr*` has typed components.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV)

/-- The IL type `m` (a natural number). -/
abbrev mT : Typ := .varT "m" []
/-- The IL type `labelidx`. -/
abbrev labelidxT : Typ := .varT "labelidx" []
/-- The IL type `labelidx*`. -/
abbrev labelidxsT : Typ := .iterT (.varT "labelidx" []) .list
/-- The IL type `idx`. -/
abbrev idxT : Typ := .varT "idx" []
/-- The IL type `typeuse`. -/
abbrev typeuseT : Typ := .varT "typeuse" []
/-- The IL type `blocktype`. -/
abbrev blocktypeT : Typ := .varT "blocktype" []
/-- The IL type `val`. -/
abbrev valT : Typ := .varT "val" []
/-- The IL type `addr`. -/
abbrev addrT : Typ := .varT "addr" []
/-- The IL type `instr`. -/
abbrev instrT : Typ := .varT "instr" []
/-- The IL type `num_(I32)`. -/
abbrev i32T : Typ := .varT "num_" [.expA (.caseE "I32" (.tupE []))]

/-- **The typing facts family C consumes.** Closed facts about always-in-range encodings, and
inversions of the IL type `instr` at the control cases. Family E discharges it for `simEnv B`. -/
structure CtrlTyping (env : Env) : Prop where
  /-- A natural number is an `n`. -/
  nat : ∀ k : Nat, TypedV env nT (.num (.natN k))
  /-- A natural number is an `m`. -/
  natM : ∀ k : Nat, TypedV env mT (.num (.natN k))
  /-- A natural number is an `addr`. -/
  addr : ∀ k : Nat, TypedV env addrT (.num (.natN k))
  /-- A label index is a `labelidx`. -/
  labelidx : ∀ l : Silmaril.Wasm.LabelIdx, TypedV env labelidxT (Encode.toValue l)
  /-- Any index is an `idx`. -/
  idx : ∀ {k : Silmaril.Wasm.IndexKind} (x : Silmaril.Wasm.Idx k), TypedV env idxT (Encode.toValue x)
  /-- A 32-bit pattern is a `num_(I32)`. -/
  i32 : ∀ c : BitVec 32, TypedV env i32T (pctV c.toNat)
  /-- `_IDX y` is a `typeuse`. -/
  typeuseIdx : ∀ y : Silmaril.Wasm.TypeIdx,
    TypedV env typeuseT (.case "_IDX" (Encode.toValue y))
  /-- The components of a typed `IF bt instr_1* ELSE instr_2*`. -/
  ifInv : ∀ (bt : Value) (b₁ b₂ : List Value),
    TypedV env instrT (.case "IF%%ELSE%" (.tuple [bt, .list b₁, .list b₂])) →
      TypedV env blocktypeT bt ∧ TypedV env instrsT (.list b₁) ∧ TypedV env instrsT (.list b₂)
  /-- The components of a typed `BLOCK bt instr*`. -/
  blockInv : ∀ (bt : Value) (b : List Value),
    TypedV env instrT (.case "BLOCK" (.tuple [bt, .list b])) →
      TypedV env blocktypeT bt ∧ TypedV env instrsT (.list b)
  /-- The components of a typed `LOOP bt instr*`. -/
  loopInv : ∀ (bt : Value) (b : List Value),
    TypedV env instrT (.case "LOOP" (.tuple [bt, .list b])) →
      TypedV env blocktypeT bt ∧ TypedV env instrsT (.list b)
  /-- The annotation of a typed `CALL_REF yy`. -/
  callRefInv : ∀ yy : Value, TypedV env instrT (.case "CALL_REF" yy) → TypedV env typeuseT yy
  /-- The annotation of a typed `RETURN_CALL_REF yy`. -/
  retCallRefInv : ∀ yy : Value,
    TypedV env instrT (.case "RETURN_CALL_REF" yy) → TypedV env typeuseT yy

/-- The IL type `valtype*`. -/
abbrev valtypesT : Typ := .iterT (.varT "valtype" []) .list

open Silmaril.SpecTec.Equiv.ExecNumeric (Applies) in
open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core in
/-- **The state accessors family C consumes**, as facts about SpecTec's functions on the encoded
state: `$funcinst(z)` is the encoded function instances, `$moduleinst(z)` the encoded module of
the frame, and `$blocktype_(z, bt)` agrees with Core's `blockType?` up to the encoding of the
value types (the rules only use the lengths). These are the "store helpers" that the earlier
execution work assumed through `ExecNumeric.Applies`; a bridge for the state's SpecTec functions
discharges them. -/
structure CtrlState {H : Type} (env : Env) (hn : H → String) : Prop where
  /-- `$funcinst(s; f) = s.FUNCS`, encoded. -/
  funcinst : ∀ (s : Store H) (f : Frame),
    Applies env "funcinst" [.val (stateV hn s f)] (.list (s.funcs.map (funcInstV hn)))
  /-- `$moduleinst(s; f) = f.MODULE`, encoded. -/
  moduleinst : ∀ (s : Store H) (f : Frame),
    Applies env "moduleinst" [.val (stateV hn s f)] (Equiv.RuntimeBridge.moduleInstToValue CT f.module)
  /-- `$blocktype_(z, bt)` is the encoding of `blockType? bt`, with typed value types. -/
  blocktype : ∀ (s : Store H) (f : Frame) (bt : BlockType) (t₁ t₂ : List CValType),
    f.module.blockType? bt = some (t₁, t₂) →
      ∃ T₁ T₂ : List Value, T₁.length = t₁.length ∧ T₂.length = t₂.length ∧
        TypedV env valtypesT (.list T₁) ∧ TypedV env valtypesT (.list T₂) ∧
        Applies env "blocktype_" [.val (stateV hn s f), .val (Encode.toValue bt)]
          (.case "%->_%%" (.tuple [.case "%" (.tuple [.list T₁]), .list [],
            .case "%" (.tuple [.list T₂])]))

open Silmaril.SpecTec.Equiv.ExecNumeric (Applies) in
open Silmaril.Wasm Silmaril.Wasm.Execution.Core in
/-- **The state reads the backward call rules use** (round 5): `CtrlState` without its forward
`blocktype` field, which asserts that encoded closed value types are `valtype*` and so fails for
indices of `2 ^ 32` or more. Both fields hold in every `simEnv B`. A `CtrlState` coerces to it. -/
structure CtrlReads {H : Type} (env : Env) (hn : H → String) : Prop where
  /-- `$funcinst(s; f) = s.FUNCS`, encoded. -/
  funcinst : ∀ (s : Store H) (f : Frame),
    Applies env "funcinst" [.val (stateV hn s f)] (.list (s.funcs.map (funcInstV hn)))
  /-- `$moduleinst(s; f) = f.MODULE`, encoded. -/
  moduleinst : ∀ (s : Store H) (f : Frame),
    Applies env "moduleinst" [.val (stateV hn s f)] (Equiv.RuntimeBridge.moduleInstToValue CT f.module)

/-- `CtrlState` without `blocktype`. -/
theorem CtrlState.reads {H : Type} {env : Env} {hn : H → String} (S : CtrlState env hn) :
    CtrlReads env hn :=
  ⟨S.funcinst, S.moduleinst⟩

instance {H : Type} {env : Env} {hn : H → String} : Coe (CtrlState env hn) (CtrlReads env hn) :=
  ⟨CtrlState.reads⟩

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core in
open Silmaril.SpecTec.Equiv.Validation (tyV) in
/-- The `FUNC t_1* -> t_2*` image of a function type. -/
def funcTypeV (ps rs : Ty (.list .val)) : Value :=
  .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list (ps.toList.map tyV)]),
    .case "%" (.tuple [.list (rs.toList.map tyV)])])

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core in
open Silmaril.SpecTec.Equiv.Validation (tyV) in
/-- **The type facts the call rules consume**: SpecTec's `Expand` relation, read declaratively,
holds of the images of Core's `Expand d (.func ps rs)`, and an encoded result type is a
`valtype*`. -/
structure CtrlCall (env : Env) : Prop where
  /-- `Expand` on images. -/
  expand : ∀ (d : DefType) (ps rs : Ty (.list .val)), Expand d (.func ps rs) →
    DDerives env (otherwise env) "Expand" "%~~%" [] (.tuple [CT.defType d, funcTypeV ps rs])
  /-- An encoded result type is a `valtype*`. -/
  valtypes : ∀ ts : Ty (.list .val), TypedV env valtypesT (.list (ts.toList.map tyV))
  /-- Encoded declared locals are a `valtype*`. -/
  locals : ∀ ts : List ValType, TypedV env valtypesT (.list (ts.map Encode.toValue))
  /-- `$default_(t)` is Core's default value of `t` closed over any module's types (the
  default depends only on `t`'s shape and nullability, not on the substitution). -/
  default : ∀ (m : ModuleInst) (t : ValType), Silmaril.SpecTec.Equiv.ExecNumeric.Applies env
    "default_" [.val (Encode.toValue t)]
    (.opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV))

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core in
/-- **The one `CtrlCall` field the backward call rules use** (round 5): `$default_`. It holds in
every `simEnv B` (`Integrate.ctrlCallDefault_simEnv`); `CtrlCall` itself does not, since its
`valtypes` field is refuted (`ConfigOk.not_ctrlCall`). A `CtrlCall` coerces to it. -/
structure CtrlDefault (env : Env) : Prop where
  /-- `$default_(t)` is Core's default value of `t`, closed over any module's types. -/
  default : ∀ (m : ModuleInst) (t : ValType), Silmaril.SpecTec.Equiv.ExecNumeric.Applies env
    "default_" [.val (Encode.toValue t)]
    (.opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV))

/-- `CtrlCall` without `expand`, `valtypes` and `locals`. -/
theorem CtrlCall.toDefault {env : Env} (C : CtrlCall env) : CtrlDefault env := ⟨C.default⟩

instance {env : Env} : Coe (CtrlCall env) (CtrlDefault env) := ⟨CtrlCall.toDefault⟩

section Host

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- `result = _VALS val* | (REF.EXN_ADDR a) THROW_REF | TRAP`. -/
def resultV : Result → Value
  | .values vs => .case "_VALS" (.list (vs.map valV))
  | .throw a => .case "(REF.EXN_ADDR%)THROW_REF" (.num (.natN a))
  | .trap => .case "TRAP" (.tuple [])

/-- `hostcallresult = RES store result | BOT`. -/
def outcomeV {H : Type} (hn : H → String) : Silmaril.Wasm.Execution.Host.Outcome (Store H) Result → Value
  | .returned s r => .case "RES" (.tuple [storeV hn s, resultV r])
  | .diverged => .case "BOT" (.tuple [])

/-- The IL type `result`. -/
abbrev resultT : Typ := .varT "result" []
/-- The IL type `funcinst`. -/
abbrev funcinstT : Typ := .varT "funcinst" []

open Silmaril.SpecTec.Equiv.ExecNumeric (Applies) in
/-- **The host interface family C consumes.** `$hostcall`, which the script declares without
clauses, is a primitive of `B`: at the images of a host function, a store and arguments it returns
a list containing the image of every outcome Core's host allows (`hostcall`; the converse,
`hostcall_sound`, is what the backward direction needs). `$lift_result` agrees with
`Result.toAdmin` on images, an encoded result is a `result`, and a function instance of a typed
store is a `funcinst`. -/
structure CtrlHost {H : Type} (env : Env) (hn : H → String) (host : HostSemantics H) : Prop where
  /-- Every outcome Core allows is listed by `$hostcall`. -/
  hostcall : ∀ (h : H) (s : Store H) (vs : List Val), ∃ os : List Value,
    Applies env "hostcall" [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeV hn s),
      .val (.list (vs.map valV))] (.list os) ∧ ∀ o, host h s vs o → outcomeV hn o ∈ os
  /-- `$lift_result` on images. -/
  liftResult : ∀ r : Result, Applies env "lift_result" [.val (resultV r)] (.list (adminsToV r.toAdmin))
  /-- An encoded result whose code is typed is a `result`. (Stated conditionally because in round 1
  no float value was typed; since the typing track's fix every value is, `Typing.typedV_val`.) -/
  result : ∀ r : Result, TypedV env instrsT (.list (adminsToV r.toAdmin)) →
    TypedV env resultT (resultV r)
  /-- A function instance of a typed store is a `funcinst`. -/
  funcinst : ∀ (s : Store H) (a : Nat) (fi : FuncInst H), TypedV env storeT (storeV hn s) →
    s.funcs[a]? = some fi → TypedV env funcinstT (funcInstV hn fi)

open Silmaril.SpecTec.Equiv.ExecNumeric (Applies) in
/-- **The one `CtrlHost` field the backward host-call rule uses** (round 5): `$lift_result` on
images. It holds in every `Prims.builtins`, with no hypothesis on the host. -/
structure CtrlLift (env : Env) : Prop where
  /-- `$lift_result` on images. -/
  liftResult : ∀ r : Result, Applies env "lift_result" [.val (resultV r)] (.list (adminsToV r.toAdmin))

/-- `CtrlHost` without `hostcall`, `result` and `funcinst`. -/
theorem CtrlHost.toLift {H : Type} {env : Env} {hn : H → String} {host : HostSemantics H}
    (Hs : CtrlHost env hn host) : CtrlLift env :=
  ⟨Hs.liftResult⟩

instance {H : Type} {env : Env} {hn : H → String} {host : HostSemantics H} :
    CoeOut (CtrlHost env hn host) (CtrlLift env) :=
  ⟨CtrlHost.toLift⟩

end Host

section Decode

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Execution (caseNilV)

/-- **The decoders family C's backward lemmas consume** (family E's decoders): which Core
administrative instruction has an image with a given head constructor, and that a code sequence
whose image is typed as `val*` is a value sequence. -/
structure CtrlDecode (env : Env) : Prop where
  /-- `TRAP`. -/
  trap : ∀ a : Admin, adminToV a = caseNilV "TRAP" → a = .trap
  /-- `LABEL_n{…} …`. -/
  label : ∀ (a : Admin) (x : Value), adminToV a = .case "LABEL_%{%}%" x →
    ∃ n cont body, a = .label n cont body
  /-- `HANDLER_n{…} …`. -/
  handler : ∀ (a : Admin) (x : Value), adminToV a = .case "HANDLER_%{%}%" x →
    ∃ n cs body, a = .handler n cs body
  /-- `FRAME_n{…} …`. -/
  frame : ∀ (a : Admin) (x : Value), adminToV a = .case "FRAME_%{%}%" x →
    ∃ n fi body, a = .frame n fi body
  /-- `CONST I32 c`. -/
  constI32 : ∀ (a : Admin) (cv : Value), adminToV a = .case "CONST" (.tuple [caseNilV "I32", cv]) →
    ∃ c : BitVec 32, a = constI32 c
  /-- `IF bt instr* ELSE instr*`. -/
  ifElse : ∀ (a : Admin) (x : Value), adminToV a = .case "IF%%ELSE%" x →
    ∃ bt b₁ b₂, a = .plain (.if_ bt b₁ b₂)
  /-- `BR_IF l`. -/
  brIf : ∀ (a : Admin) (x : Value), adminToV a = .case "BR_IF" x → ∃ l, a = .plain (.brIf l)
  /-- `CALL_INDIRECT x y`. -/
  callIndirect : ∀ (a : Admin) (x : Value), adminToV a = .case "CALL_INDIRECT" x →
    ∃ t y, a = .plain (.callIndirect t y)
  /-- `RETURN_CALL_INDIRECT x y`. -/
  returnCallIndirect : ∀ (a : Admin) (x : Value), adminToV a = .case "RETURN_CALL_INDIRECT" x →
    ∃ t y, a = .plain (.returnCallIndirect t y)
  /-- `BR l`. -/
  br : ∀ (a : Admin) (x : Value), adminToV a = .case "BR" x → ∃ l, a = .plain (.br l)
  /-- `RETURN`. -/
  ret : ∀ a : Admin, adminToV a = caseNilV "RETURN" → a = .plain .return_
  /-- `BR_TABLE l* l'`. -/
  brTable : ∀ (a : Admin) (x : Value), adminToV a = .case "BR_TABLE" x →
    ∃ ls l', a = .plain (.brTable ls l')
  /-- `CALL x`. -/
  call : ∀ (a : Admin) (x : Value), adminToV a = .case "CALL" x → ∃ y, a = .plain (.call y)
  /-- `RETURN_CALL x`. -/
  returnCall : ∀ (a : Admin) (x : Value), adminToV a = .case "RETURN_CALL" x →
    ∃ y, a = .plain (.returnCall y)
  /-- `REF.NULL_ADDR`. -/
  refNull : ∀ a : Admin, adminToV a = caseNilV "REF.NULL_ADDR" → a = .ref .null
  /-- `BR_ON_NULL l`. -/
  brOnNull : ∀ (a : Admin) (x : Value), adminToV a = .case "BR_ON_NULL" x →
    ∃ l, a = .plain (.brOnNull l)
  /-- `BR_ON_NON_NULL l`. -/
  brOnNonNull : ∀ (a : Admin) (x : Value), adminToV a = .case "BR_ON_NON_NULL" x →
    ∃ l, a = .plain (.brOnNonNull l)
  /-- `CALL_REF yy`, in either representation. -/
  callRef : ∀ (a : Admin) (x : Value), adminToV a = .case "CALL_REF" x → a.IsCallRef
  /-- A code sequence whose image is a `val*` is a value sequence. -/
  vals : ∀ (ρ : VarEnv) (l : List Admin), ValsOnly ρ → HasTyp env ρ valsT (.list (adminsToV l)) →
    ∃ vs, l = vals vs

end Decode

end Silmaril.Wasm.SpecTec.Sim
