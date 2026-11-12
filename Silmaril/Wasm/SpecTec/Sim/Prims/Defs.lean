module

public import Silmaril.Wasm.SpecTec.Sim.Whole.Defs
public import Silmaril.Wasm.SpecTec.Sim.Floats.Defs
public import Silmaril.Wasm.SpecTec.Sim.FwdMem.Defs
public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Defs
public import Silmaril.Wasm.SpecTec.Sim.ZBytes.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Lanes.Defs

/-!
# SpecTec ↔ Core 3.0: one concrete interpretation `B` of the primitives

`Task.wholeStep` is existential in `B : Builtins`, and `Whole.Assumptions B hn host` collects what
the families assumed about it. This file constructs one `B`, `Prims.builtins prof hn host`, so that those
assumptions can be discharged for a concrete interpretation rather than assumed for an arbitrary one.

`callDef` consults `B` only where every clause of a definition *definitely* fails
(`Res.elimUndef … .undef`), so `B` only has to answer at the names whose clauses the evaluator
cannot run:

* the integer primitives of family N (`IntNumeric.intCall`, consulted first, so `IntB` holds);
* `$wrap__` and `$extend__`, declared `hint(builtin)` with no clause;
* `$hostcall`, declared without clauses: the list of the images of the outcomes Core's host allows
  (at a chosen preimage of the arguments; see `HostRespects`);
* `$unrolldt`, whose only clause binds `subtype*` through an `if` premise: the image of Core's
  `unrolldt` (this is what makes SpecTec's `Expand` hold of images);
* `$blocktype_` at `_IDX x`, whose clause binds `t_1*`, `t_2*` through an `Expand` premise: the image
  of Core's `ModuleInst.blockType?`, read off the encoded frame's `MODULE.TYPES`;
* `$growtable`, `$growmem`, whose only clauses bind the grown instance's components in `if`
  premises: the images of Core's `TableInst.grow?`, `MemInst.grow?` (round 3, track refok);
* `$nbytes_` and `$ibytes_`, declared `hint(builtin)` with no clause: Core's little-endian byte
  encoding (`FwdMem.nbytesCall`, `FwdMem.ibytesCall`; round 3, track fwd-mem);
* `$zbytes_`, declared `hint(builtin)` with no clause: the same encoding at a storage type
  (`ZBytes.zbytesCall`; round 4, track r4-fwd);
* `$lanes_` and `$inv_lanes_`, declared `hint(builtin)` with no clause: Core's lanes of a 128-bit
  pattern (`Round5.Simd.lanesCall`, `Round5.Simd.invLanesCall`; round 5, track simd).

Every other name gets `none`. Decoding uses only the injectivity of `tyV` and of the `Encode`
instances: `tyInv` is a classical left inverse of `tyV`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv (bvV)
open Silmaril.SpecTec.Equiv.ExecBuiltins (asBits?)

/-- A classical left inverse of `tyV` at the sort `k` (`tyV` is injective, `tyV_inj`). -/
noncomputable def tyInv (k : TKind) (v : Value) : Option (Ty k) :=
  open Classical in if h : ∃ t : Ty k, tyV t = v then some h.choose else none

/-- The `MODULE.TYPES` list of an encoded state `s; f`. -/
def moduleTypesV? : Value → Option (List Value)
  | .case "%;%" (.tuple [_, F]) => do
      let M ← F.field? "MODULE"
      let T ← M.field? "TYPES"
      T.asList?
  | _ => none

/-- `$blocktype_(z, _IDX x)`: Core's `blockType? (.typeIdx x)` on the module read off `z`. -/
noncomputable def blocktypeCall (z xv : Value) : Option Value := do
  let Ts ← moduleTypesV? z
  let ds ← Ts.mapM (tyInv .def)
  let x ← Encode.ofValue (α := TypeIdx) xv
  let d ← ds[x.toNat]?
  let p ← DefType.funcType? d
  some (Exn.instrTypeV (p.1.map tyV) (p.2.map tyV))

/-- `$unrolldt(dt)`: Core's `unrolldt`, on images. -/
noncomputable def unrolldtCall (v : Value) : Option Value := do
  let d ← tyInv .def v
  let st ← unrolldt d
  some (tyV st)

variable {H : Type}

/-- The arguments of `$hostcall(hf, s, val*)` for a Core host call. -/
def hostArgs (hn : H → String) (h : H) (s : Store H) (vs : List Val) : List ArgV :=
  [.val (.case "_HOSTFUNC" (.text (hn h))), .val (storeV hn s), .val (.list (vs.map valV))]

/-- `$hostcall`: at the image of some host call with finitely many outcomes, the images of the
outcomes of a chosen such call. -/
noncomputable def hostcallCall (hn : H → String) (host : HostSemantics H) (ws : List ArgV) :
    Option Value :=
  open Classical in
  if h : ∃ p : H × Store H × List Val, ws = hostArgs hn p.1 p.2.1 p.2.2 ∧
      ∃ os : List (Silmaril.Wasm.Execution.Host.Outcome (Store H) Result),
        ∀ o, host p.1 p.2.1 p.2.2 o ↔ o ∈ os then
    some (.list (h.choose_spec.2.choose.map (outcomeV hn)))
  else none

open Silmaril.SpecTec.Equiv.RuntimeBridge (tableInstToValue memInstToValue refToValue) in
/-- `$growtable(ti, n, r)`: at the images of a table instance, a count and a reference, the image
of Core's `TableInst.grow?` (round 3, track refok; `$growtable`'s only clause binds `at`, `i`, `j?`,
`rt`, `r'*` in `if` premises, so it definitely fails and `callDef` falls back to `B`). -/
noncomputable def growtableCall (tv nv rv : Value) : Option Value :=
  open Classical in
  if h : ∃ p : TableInst × Nat × Ref, tv = tableInstToValue CT p.1 ∧
      nv = .num (.natN p.2.1) ∧ rv = refToValue p.2.2 then
    (h.choose.1.grow? h.choose.2.1 h.choose.2.2).map (tableInstToValue CT)
  else none

open Silmaril.SpecTec.Equiv.RuntimeBridge (memInstToValue) in
/-- `$growmem(mi, n)`: at the images of a memory instance and a count, the image of Core's
`MemInst.grow?` (round 3, track refok; same fallback as `$growtable`). -/
noncomputable def growmemCall (mv nv : Value) : Option Value :=
  open Classical in
  if h : ∃ p : MemInst × Nat, mv = memInstToValue p.1 ∧ nv = .num (.natN p.2) then
    (h.choose.1.grow? h.choose.2).map memInstToValue
  else none

/-- The interpretation of the primitives under the numeric profile `prof`: the float and
conversion primitives of the float track (`Floats.floatCall prof`, which also answers `$wrap__` and
`$extend__` at every width) first, then the integer primitives (`IntNumeric.intCall`), then the
names this track interprets, and the bitwise vector primitives `$inot_`, `$iandnot_`,
`$ibitselect_` and the reference-type fallback of `$sx` (round 3, `FwdSimdAgg.vvCall`). -/
noncomputable def call (prof : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : HostSemantics H) (x : IL.Id) (ws : List ArgV) : Option Value :=
  match Floats.floatCall prof x ws with
  | some v => some v
  | none =>
  match IntNumeric.intCall x ws with
  | some v => some v
  | none =>
    match x, ws with
    | "hostcall", ws => hostcallCall hn host ws
    | "unrolldt", [.val v] => unrolldtCall v
    | "blocktype_", [.val z, .val (.case "_IDX" xv)] => blocktypeCall z xv
    | "growtable", [.val tv, .val nv, .val rv] => growtableCall tv nv rv
    | "growmem", [.val mv, .val nv] => growmemCall mv nv
    | "nbytes_", [.val nt, .val c] => FwdMem.nbytesCall nt c
    | "ibytes_", [.val n, .val c] => FwdMem.ibytesCall n c
    | "zbytes_", [.val zt, .val c] => ZBytes.zbytesCall zt c
    | "inot_", ws => FwdSimdAgg.vvCall "inot_" ws
    | "iandnot_", ws => FwdSimdAgg.vvCall "iandnot_" ws
    | "ibitselect_", ws => FwdSimdAgg.vvCall "ibitselect_" ws
    | "sx", ws => FwdSimdAgg.vvCall "sx" ws
    | "lanes_", [.val sv, .val v] => Round5.Simd.lanesCall sv v
    | "inv_lanes_", [.val sv, .val lv] => Round5.Simd.invLanesCall sv lv
    | "vunop_", ws => Round5.Simd.vecOpCall prof "vunop_" ws
    | "vbinop_", ws => Round5.Simd.vecOpCall prof "vbinop_" ws
    | "vternop_", ws => Round5.Simd.vecOpCall prof "vternop_" ws
    | "vrelop_", ws => Round5.Simd.vecOpCall prof "vrelop_" ws
    | "vshiftop_", ws => Round5.Simd.vecOpCall prof "vshiftop_" ws
    | "vbitmaskop_", ws => Round5.Simd.vecOpCall prof "vbitmaskop_" ws
    | "vswizzlop_", ws => Round5.Simd.vecOpCall prof "vswizzlop_" ws
    | "vshufflop_", ws => Round5.Simd.vecOpCall prof "vshufflop_" ws
    | "vextunop__", ws => Round5.Simd.vecOpCall prof "vextunop__" ws
    | "vextbinop__", ws => Round5.Simd.vecOpCall prof "vextbinop__" ws
    | "vextternop__", ws => Round5.Simd.vecOpCall prof "vextternop__" ws
    | "vnarrowop__", ws => Round5.Simd.vecOpCall prof "vnarrowop__" ws
    | "vcvtop__", ws => Round5.Simd.vecOpCall prof "vcvtop__" ws
    | _, _ => none

/-- **The concrete `B`**, for the numeric profile `prof`. -/
noncomputable def builtins (prof : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : HostSemantics H) : Builtins :=
  ⟨call prof hn host⟩

/-- **A host that respects the encoding**: two host calls with the same SpecTec image have the
same outcome images. `$hostcall` is a function of the images, so without this no single `B` can
list every outcome of every call (`instrToV` is not injective on invalid instructions, so neither
is `storeV`). It holds whenever the image of the arguments determines them
(`hostRespects_of_injective`). -/
def HostRespects (hn : H → String) (host : HostSemantics H) : Prop :=
  ∀ (h h' : H) (s s' : Store H) (vs vs' : List Val), hostArgs hn h s vs = hostArgs hn h' s' vs' →
    ∀ o, host h s vs o → ∃ o', host h' s' vs' o' ∧ outcomeV hn o = outcomeV hn o'

/-- **Typing of the images of closed types** (family E facts, about the encoding alone): the
values SpecTec's `Expand` rule quantifies over have their IL types. Used to discharge the `Expand`
fields of `CtrlCall` and `Exn.Helpers`. -/
structure TypeTyping (env : Env) : Prop where
  /-- A defined type is a `deftype`. -/
  deftype : ∀ d : DefType, TypedV env (.varT "deftype" []) (tyV d)
  /-- A composite type is a `comptype`. -/
  comptype : ∀ ct : CCompType, TypedV env (.varT "comptype" []) (tyV ct)
  /-- `final?`. -/
  final : ∀ b : Bool, TypedV env (.iterT (.varT "final" []) .opt)
    (Silmaril.SpecTec.Equiv.Validation.finalV b)
  /-- A list of type uses is a `typeuse*`. -/
  typeuses : ∀ us : Ty (.list .use), TypedV env (.iterT (.varT "typeuse" []) .list) (tyV us)

/-- **The typing parts of `Whole.Assumptions`**, plus the typing facts the discharged helper fields
consume (all facts about the encoding alone, for the typing track). The first five are
`Whole.Assumptions` fields verbatim; `valtypes`, `locals`, `result` and `funcinst` are the typing
fields of `CtrlCall`/`CtrlHost`, also used for `$blocktype_`'s result types; `types` types the
quantifiers of SpecTec's `Expand`. -/
structure TypingInputs (env : Env) (hn : H → String) : Prop where
  typing : TypingFacts env hn
  state : State.StateTyping env
  rTyping : RefsGC.RTyping env
  ctrlTyping : CtrlTyping env
  exnTyping : Exn.Typing env
  types : TypeTyping env
  valtypes : ∀ ts : Ty (.list .val), TypedV env valtypesT (.list (ts.toList.map tyV))
  locals : ∀ ts : List ValType, TypedV env valtypesT (.list (ts.map Encode.toValue))
  result : ∀ r : Result, TypedV env instrsT (.list (adminsToV r.toAdmin)) →
    TypedV env resultT (resultV r)
  funcinst : ∀ (s : Store H) (a : Nat) (fi : FuncInst H), TypedV env storeT (storeV hn s) →
    s.funcs[a]? = some fi → TypedV env funcinstT (funcInstV hn fi)

/-- **What the builtins track leaves open** (not typing facts, and not discharged):

* `refOk`: SpecTec's `Ref_ok` is Core's `RefOk` (needs a bridge between SpecTec's and Core's type
  validity and subtyping);
* `instReftype`: `$inst_reftype(m, rt)` evaluates to `CT.elemType (m.instRef rt)` (needs the
  evaluation of `$subst_all_reftype`/`$subst_heaptype`/`$subst_typevar` on images);
* `default`: `CtrlCall.default`. Round 2 refuted it for every `B` (the evaluator did not test
  `SubE` argument patterns); after the typing track's fix it holds in every `simEnv B`
  (`Integrate.ctrlCallDefault_simEnv`). -/
structure Residual (env : Env) : Prop where
  refOk : RefsGC.RefOkBridge env
  instReftype : ∀ (ρ : VarEnv) (e₁ e₂ : Exp) (m : ModuleInst) (rt : RefType),
    ρ.findDef? "inst_reftype" = none → EvalExp env ρ e₁ (RefsGC.moduleInstToValue' m) →
    EvalExp env ρ e₂ (Encode.toValue rt) →
    EvalExp env ρ (.callE "inst_reftype" [.expA e₁, .expA e₂]) (CT.elemType (m.instRef rt))
  default : ∀ (m : ModuleInst) (t : ValType), Silmaril.SpecTec.Equiv.ExecNumeric.Applies env
    "default_" [.val (Encode.toValue t)]
    (.opt ((defaultVal? ((liftVal t).substAll (m.types.map .dt))).map valV))

end Silmaril.Wasm.SpecTec.Sim.Prims
