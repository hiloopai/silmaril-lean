module

public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Thms

/-!
# SpecTec ↔ Core 3.0, round 5, track fwd: the forward conjunct without `Residue`/`Extra`

Round 4's forward conjunct (`R4Fwd.forward_concrete4_valid`) still took round 2's bundles
`Integrate.Residue` and `Integrate.Extra`. Both are refuted (`ConfigOk.not_residue`,
`RefOk.not_aggTypes'`): their typing fields quantify over **every** Core type, and SpecTec's
syntax bounds type indices and `list(·)` lengths by `2 ^ 32`. So that route is vacuous.

This topic proves the forward conjunct for the concrete `B := Prims.builtins P hn host` from
**per-rule obligations** that are not refuted, and carries `Round4.Bounded` (not just
`StoreOk`) through the recursion. Every family structure the recursion uses is one already
discharged for the concrete `B` (`TypingFacts`, `StateTyping`, `RTyping`, `RFuns`,
`RStoreFuns`, `CtrlTyping`, `Exn.Typing`, `IntB`, `FloatB`, `BytesFuns`, `VVB`, `MemTyping`,
`GrowFuns`, `InstTyping`). The rules whose earlier proofs consumed a refuted field are listed in
`Obl`, one field per rule (or per class), each **from a bounded source** (`Round4.Bounded`):

* `vector`: the non-bitwise SIMD operators (round 4's `Open4.vector`, now with `Bounded`);
* `aggregate`: every aggregate step (their proofs used `Aggregates.AggTypes`, refuted);
* `refTest`, `refCast`, `brOnCast`, `brOnCastFail`: the cast rules (they used
  `RefsGC.RefOkBridge`, argued false for ill-typed stores);
* `block`, `loop`, `tryTable`: the block rules (`$blocktype_` with typed results used
  `Residue.valtypes`, refuted);
* `callRefFunc`, `callRefHost`, `callRefHostDiv`, `returnCallRefFrameAddr`: the call rules
  (`CtrlCall.expand`/`valtypes`, refuted; the host rules also used `Prims.HostRespects`);
* `throw`, `throwRefHandlerCatch`, `throwRefHandlerCatchRef`, `throwRefHandlerNext`: the
  exception rules that took `Exn.Helpers` (its `expand`/`blocktype` fields used the refuted
  type typing).

Round 4's `Open4.vecMem` is gone: `Bounded` excludes the memory SIMD instructions
(`Round4.instrBnd`), so those steps never start from a bounded configuration.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Fwd

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded)
open R4Fwd (VecArith)

variable {H : Type}

/-- **The per-rule forward obligations left open by round 5, track fwd** (module doc). Each is
the forward case of one Core rule (or class), stated from a bounded source configuration. -/
structure Obl (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- The non-bitwise SIMD operators. -/
  vector : ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
    (∃ i, Admin.plain i ∈ is ∧ VecArith i = true) → Bounded ⟨s, f, is⟩ →
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- Every aggregate step. -/
  aggregate : ∀ c c' : Config H, AggregateStep c c' → Bounded c → FwdP (simEnv B) hn c c'
  /-- `ref.test`. -/
  refTest : ∀ (s : Store H) (f : Frame) (r : Ref) (rt : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ →
    (RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 1]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 0]⟩)
  /-- `ref.cast`. -/
  refCast : ∀ (s : Store H) (f : Frame) (r : Ref) (rt : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ →
    (RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩)
  /-- `br_on_cast`. -/
  brOnCast : ∀ (s : Store H) (f : Frame) (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ →
    (RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩)
  /-- `br_on_cast_fail`. -/
  brOnCastFail : ∀ (s : Store H) (f : Frame) (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ →
    (RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩)
  /-- `block`. -/
  block : ∀ (s : Store H) (f : Frame) (bt : BlockType) (body : List Instr) (vs : List Val)
    (t₁ t₂ : List CValType), f.module.blockType? bt = some (t₁, t₂) → vs.length = t₁.length →
    Bounded ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ →
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩
  /-- `loop`. -/
  loop : ∀ (s : Store H) (f : Frame) (bt : BlockType) (body : List Instr) (vs : List Val)
    (t₁ t₂ : List CValType), f.module.blockType? bt = some (t₁, t₂) → vs.length = t₁.length →
    Bounded ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩ →
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩
  /-- `try_table`. -/
  tryTable : ∀ (s : Store H) (f : Frame) (bt : BlockType) (cs : List Catch) (body : List Instr)
    (vs : List Val) (t₁ t₂ : List CValType), f.module.blockType? bt = some (t₁, t₂) →
    vs.length = t₁.length → Bounded ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩ →
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
      ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩
  /-- `call_ref` into a Wasm function. -/
  callRefFunc : ∀ (s : Store H) (f : Frame) (c : Admin) (vs : List Val) (a : Nat) (fi : FuncInst H)
    (ps rs : Ty (.list .val)) (code : Func), c.IsCallRef → s.funcs[a]? = some fi →
    Expand fi.type (.func ps rs) → vs.length = ps.length → fi.code = .wasm code →
    Bounded ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ →
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩
  /-- `call_ref` into a host function that returns. -/
  callRefHost : ∀ (s s' : Store H) (f : Frame) (c : Admin) (vs : List Val) (a : Nat)
    (fi : FuncInst H) (ps rs : Ty (.list .val)) (h : H) (r : Result), c.IsCallRef →
    s.funcs[a]? = some fi → Expand fi.type (.func ps rs) → vs.length = ps.length →
    fi.code = .host h → host h s vs (.returned s' r) →
    Bounded ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ →
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩
  /-- `call_ref` into a host function that diverges. -/
  callRefHostDiv : ∀ (s : Store H) (f : Frame) (c : Admin) (vs : List Val) (a : Nat)
    (fi : FuncInst H) (ps rs : Ty (.list .val)) (h : H), c.IsCallRef →
    s.funcs[a]? = some fi → Expand fi.type (.func ps rs) → vs.length = ps.length →
    fi.code = .host h → host h s vs .diverged →
    Bounded ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ →
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
  /-- `return_call_ref` out of a frame, up to call annotations. -/
  returnCallRefFrameAddr : ∀ (s : Store H) (f fi : Frame) (k : Nat) (vs' vs : List Val) (a : Nat)
    (c : Admin) (rest : List Admin) (fn : FuncInst H) (ps rs : Ty (.list .val)),
    c.IsReturnCallRef → s.funcs[a]? = some fn → Expand fn.type (.func ps rs) →
    vs.length = ps.length →
    Bounded ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩ →
    FwdMem.FwdUp (simEnv B) hn ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩
  /-- `throw`. -/
  throw : ∀ (s : Store H) (f : Frame) (x : TagIdx) (vs : List Val) (ta : Nat) (ti : TagInst)
    (ts : Ty (.list .val)), s.tag? f x = some (ta, ti) → Expand ti.type (.func ts .nil) →
    vs.length = ts.length → Bounded ⟨s, f, vals vs ++ [.plain (.throw x)]⟩ →
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.plain (.throw x)]⟩
      ⟨s.addExn ⟨ta, vs⟩, f, throwing s.exns.length⟩
  /-- `throw_ref` caught by `catch`. -/
  throwRefHandlerCatch : ∀ (s : Store H) (f : Frame) (n : Nat) (x : TagIdx) (l : LabelIdx)
    (cs : List Catch) (a : Nat) (e : ExnInst), s.exns[a]? = some e →
    f.module.tags[x.toNat]? = some e.tag →
    Bounded ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩ →
    FwdP (simEnv B) hn ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩
      ⟨s, f, vals e.fields ++ [.plain (.br l)]⟩
  /-- `throw_ref` caught by `catch_ref`. -/
  throwRefHandlerCatchRef : ∀ (s : Store H) (f : Frame) (n : Nat) (x : TagIdx) (l : LabelIdx)
    (cs : List Catch) (a : Nat) (e : ExnInst), s.exns[a]? = some e →
    f.module.tags[x.toNat]? = some e.tag →
    Bounded ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩ →
    FwdP (simEnv B) hn ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
      ⟨s, f, vals e.fields ++ [.ref (.exn a), .plain (.br l)]⟩
  /-- `throw_ref` past a non-matching catch clause. -/
  throwRefHandlerNext : ∀ (s : Store H) (f : Frame) (n : Nat) (c : Catch) (cs : List Catch)
    (a : Nat), ¬ CatchMatches s f a c → Bounded ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ →
    FwdP (simEnv B) hn ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩
      ⟨s, f, [.handler n cs (throwing a)]⟩

/-- **What remains of `Obl` given `TypesB`** (and, for the host calls, a finite host respecting
the encoding): the non-bitwise SIMD operators, the aggregate steps and the four cast rules
(`Round5.Fwd.obl_of`). Same statements as the corresponding fields of `Obl`. -/
structure Rest (B : Builtins) (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- The non-bitwise SIMD operators. -/
  vector : ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
    (∃ i, Admin.plain i ∈ is ∧ VecArith i = true) → Bounded ⟨s, f, is⟩ →
    FwdP (simEnv B) hn ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- Every aggregate step. -/
  aggregate : ∀ c c' : Config H, AggregateStep c c' → Bounded c → FwdP (simEnv B) hn c c'
  /-- `ref.test`. -/
  refTest : ∀ (s : Store H) (f : Frame) (r : Ref) (rt : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ →
    (RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 1]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩ ⟨s, f, [constI32 0]⟩)
  /-- `ref.cast`. -/
  refCast : ∀ (s : Store H) (f : Frame) (r : Ref) (rt : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ →
    (RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩)
  /-- `br_on_cast`. -/
  brOnCast : ∀ (s : Store H) (f : Frame) (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ →
    (RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩)
  /-- `br_on_cast_fail`. -/
  brOnCastFail : ∀ (s : Store H) (f : Frame) (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType),
    Bounded ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ →
    (RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdP (simEnv B) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩)

open Silmaril.SpecTec.Equiv.Validation (tyV) in
/-- **Positive typing of the images of bounded types** (`Round4.tyBnd`): the restatement of round
2's refuted `Prims.TypeTyping`, `Residue.valtypes` and `Aggregates.AggTypes.storagetype` to the
bounded types that `Round4.Bounded` configurations hold. These are facts about SpecTec's type
syntax alone (no builtin is consulted), and the same facts `Round4.PosTyping` needs for its
`deftype` positions. Not proved here; `Round5.Fwd.Obl`'s type-dependent fields are proved from it
(`Round5.Fwd.obl_of`). -/
structure TypesB (env : Env) : Prop where
  /-- A bounded defined type is a `deftype`. -/
  deftype : ∀ d : DefType, Round4.tyBnd d = true → TypedV env (.varT "deftype" []) (tyV d)
  /-- A bounded composite type is a `comptype`. -/
  comptype : ∀ ct : CCompType, Round4.tyBnd ct = true →
    TypedV env (.varT "comptype" []) (tyV ct)
  /-- `final?`. -/
  final : ∀ b : Bool, TypedV env (.iterT (.varT "final" []) .opt)
    (Silmaril.SpecTec.Equiv.Validation.finalV b)
  /-- A bounded list of type uses is a `typeuse*`. -/
  typeuses : ∀ us : Ty (.list .use), Round4.tyBnd us = true →
    TypedV env (.iterT (.varT "typeuse" []) .list) (tyV us)
  /-- A bounded list of value types is a `valtype*`. -/
  valtypes : ∀ ts : Ty (.list .val), Round4.tyBnd ts = true →
    TypedV env valtypesT (.list (ts.toList.map tyV))
  /-- A bounded storage type is a `storagetype`. -/
  storagetype : ∀ zt : CStorageType, Round4.tyBnd zt = true →
    TypedV env Aggregates.storagetypeT (tyV zt)

open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue) in
/-- **SpecTec's `Ref_ok` is Core's `RefOk` at one store and one reference type**, under every
reading of `otherwise`. -/
def RefOkAt (env : Env) (hn : H → String) (s : Store H) (rt : CRefType) : Prop :=
  ∀ (O : ElseI) (r : Ref), DDerives env O "Ref_ok" "%|-%:%" []
    (.tuple [storeV hn s, refToValue r, CT.elemType rt]) ↔ RefOk s r rt

/-- **`RefsGC.RefOkBridge`, restated to typed stores and bounded reference types.** Round 3
argued the unrestricted bridge false (track refok, `RefOk.storeTyped_of_refOkBridge`: it forces
every store image to be typed). The cast rules are proved from this restatement
(`Round5.Fwd.rest_of`); it is not proved here: it needs SpecTec's `Reftype_ok`/`Reftype_sub` to
agree with Core's `TyOk`/`Sub` on bounded types. -/
structure RefOkB (env : Env) : Prop where
  /-- On a typed store and a bounded reference type. -/
  refOk : ∀ {H : Type} (hn : H → String) (s : Store H) (rt : CRefType),
    TypedV env storeT (storeV hn s) → Round4.tyBnd rt = true → RefOkAt env hn s rt

/-- **`array.new_data-num`, forward, from a bounded frame module** (round 4's
`R4Fwd.NewDataNumObl` with `ModuleBnd`: the rule's `Expand` premise needs the array type
bounded). -/
def NewDataNumB (B : Builtins) (hn : H → String) : Prop :=
  ∀ (s : Store H) (f : Frame) (x : TypeIdx) (y : DataIdx) (i n : BitVec 32) (d : DefType)
    (ft : CFieldType) (da : Nat) (di : DataInst) (vs : List Val), Round4.ModuleBnd f.module →
    f.type? x = some d → Expand d (.array ft) → s.data? f y = some (da, di) →
    0 < storageSize (fieldStorage ft) →
    i.toNat + n.toNat * storageSize (fieldStorage ft) / 8 ≤ di.bytes.size →
    (List.range n.toNat).mapM (fun k => readField? (fieldStorage ft) di.bytes
      (i.toNat + k * (storageSize (fieldStorage ft) / 8))) = some vs →
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewData x y)]⟩
      ⟨s, f, vals vs ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)]⟩

/-- **`array.init_data-zero`, forward, from a bounded configuration** (round 4's
`R4Fwd.InitDataZeroObl` with `Round4.Bounded`). -/
def InitDataZeroB (B : Builtins) (hn : H → String) : Prop :=
  ∀ (s : Store H) (f : Frame) (x : TypeIdx) (y : DataIdx) (i j : BitVec 32) (a da : Nat)
    (ai : ArrayInst) (di : DataInst),
    Bounded ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0, .plain (.arrayInitData x y)]⟩ →
    s.arrays[a]? = some ai → s.data? f y = some (da, di) →
    i.toNat ≤ ai.fields.length ∧ j.toNat ≤ di.bytes.size →
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
      .plain (.arrayInitData x y)]⟩ ⟨s, f, []⟩

end Silmaril.Wasm.SpecTec.Sim.Round5.Fwd
