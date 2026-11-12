module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# SpecTec ↔ Core 3.0, family X (exceptions): the family's hypotheses

Family X covers `throw`, the `throw_ref` rules, `try_table` and `handler-vals`. Most of the work
goes through without extra assumptions. A few facts belong to other families and are stated here
as hypotheses:

* `Typing`: the IL typing of the scalar values the rules quantify over (`addr`, `n`, `m`, `idx`,
  `labelidx`, `blocktype`, `exninst`). These are family E facts. They are not derivable from
  `TypingFacts`, which only types configurations, instruction sequences and the components of
  `LABEL`/`HANDLER`/`FRAME`.
* `Helpers`: what the store helpers `$exninst`, `$tagaddr`, `$tag`, `$as_deftype`,
  `$add_exninst` and `$blocktype_` compute on encoded states, and how the relation `Expand`
  relates to Core's `Expand` on function types. Helper calls go through the evaluator
  (`ExecNumeric.Applies`), as in the existing `Equiv.ExecRead*` characterisations. `Expand`
  belongs to family R.

For the backward direction, the inverse facts are included (`tag_inv`, `expand_inv`,
`blocktype_inv`). Where a helper has a builtin fallback (an out-of-range `$tag`, for example),
they depend on `B`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Exn

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.RuntimeBridge (tagInstToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation

/-- The IL type `addr`. -/
abbrev addrT : Typ := .varT "addr" []
/-- The IL type `m`. -/
abbrev mT : Typ := .varT "m" []
/-- The IL type `idx`. -/
abbrev idxT : Typ := .varT "idx" []
/-- The IL type `labelidx`. -/
abbrev labelidxT : Typ := .varT "labelidx" []
/-- The IL type `catch`. -/
abbrev catchT : Typ := .varT "catch" []
/-- The IL type `exninst`. -/
abbrev exninstT : Typ := .varT "exninst" []
/-- The IL type `blocktype`. -/
abbrev blocktypeT : Typ := .varT "blocktype" []
/-- The IL type `valtype*`. -/
abbrev valtypesT : Typ := .iterT (.varT "valtype" []) .list

/-- `t_1* ->_[] t_2*`, the image of an `instrtype` with no locals, as `$blocktype_` returns it. -/
def instrTypeV (a b : List Value) : Value :=
  .case "%->_%%" (.tuple [.case "%" (.tuple [.list a]), .list [], .case "%" (.tuple [.list b])])

/-- `FUNC t_1* -> t_2*`, the composite type `Expand` relates a defined type to. -/
def funcTypeV (a b : List Value) : Value :=
  .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list a]), .case "%" (.tuple [.list b])])

/-- The family's typing hypotheses (family E facts): the scalar values the exception rules
quantify over have their IL types. -/
structure Typing (env : Env) : Prop where
  /-- An address is an `addr`. -/
  addr : ∀ a : Nat, TypedV env addrT (.num (.natN a))
  /-- A number is an `n`. -/
  n : ∀ k : Nat, TypedV env nT (.num (.natN k))
  /-- A number is an `m`. -/
  m : ∀ k : Nat, TypedV env mT (.num (.natN k))
  /-- A tag index is an `idx`. -/
  idx : ∀ x : TagIdx, TypedV env idxT (Encode.toValue x)
  /-- A label index is a `labelidx`. -/
  labelidx : ∀ l : LabelIdx, TypedV env labelidxT (Encode.toValue l)
  /-- A block type is a `blocktype`. -/
  blocktype : ∀ bt : BlockType, TypedV env blocktypeT (Encode.toValue bt)
  /-- An exception instance whose fields are typed values is an `exninst`. -/
  exninst : ∀ e : ExnInst, TypedV env valsT (.list (e.fields.map valV)) →
    TypedV env exninstT (exnInstV e)
  /-- The elements of a typed `catch*` are `catch`es. -/
  catch_ : ∀ (c : Catch) (cs : List Catch),
    TypedV env catchesT (.list ((c :: cs).map Encode.toValue)) →
    TypedV env catchT (Encode.toValue c) ∧ TypedV env catchesT (.list (cs.map Encode.toValue))

variable {H : Type}

/-- The family's hypotheses about the store helpers and `Expand` (evaluated by the evaluator,
with `B`'s builtins as the fallback). -/
structure Helpers (env : Env) (hn : H → String) : Prop where
  /-- `$exninst(s; f) = s.EXNS`. -/
  exninst : ∀ (s : Store H) (f : Frame),
    Applies env "exninst" [.val (stateV hn s f)] (.list (s.exns.map exnInstV))
  /-- `$tagaddr(s; f) = f.MODULE.TAGS`. -/
  tagaddr : ∀ (s : Store H) (f : Frame),
    Applies env "tagaddr" [.val (stateV hn s f)] (.list (f.module.tags.map fun a => .num (.natN a)))
  /-- `$tag(z, x)` is the tag instance Core's `Store.tag?` finds. -/
  tag : ∀ (s : Store H) (f : Frame) (x : TagIdx) (ta : Nat) (ti : TagInst),
    s.tag? f x = some (ta, ti) →
    Applies env "tag" [.val (stateV hn s f), .val (Encode.toValue x)] (tagInstToValue CT ti)
  /-- …and nothing else. -/
  tag_inv : ∀ (s : Store H) (f : Frame) (x : TagIdx) (w : Value),
    Applies env "tag" [.val (stateV hn s f), .val (Encode.toValue x)] w →
    ∃ ta ti, s.tag? f x = some (ta, ti) ∧ w = tagInstToValue CT ti
  /-- `$as_deftype(dt) = dt`. -/
  asDeftype : ∀ d : DefType, Applies env "as_deftype" [.val (CT.defType d)] (CT.defType d)
  /-- `$add_exninst(z, [exn])` appends `exn` to the store's exceptions. -/
  addExn : ∀ (s : Store H) (f : Frame) (e : ExnInst),
    Applies env "add_exninst" [.val (stateV hn s f), .val (.list [exnInstV e])]
      (stateV hn (s.addExn e) f)
  /-- Core's `Expand d (func ts → [])` is SpecTec's `Expand`, with typed result types. -/
  expand : ∀ (d : DefType) (ts : Ty (.list .val)), Expand d (.func ts .nil) →
    ∃ tvs : List Value, tvs.length = ts.length ∧ TypedV env valtypesT (.list tvs) ∧
      DDerives env (otherwise env) "Expand" "%~~%" [] (.tuple [CT.defType d, funcTypeV tvs []])
  /-- …and conversely. -/
  expand_inv : ∀ (d : DefType) (tvs : List Value),
    DDerives env (otherwise env) "Expand" "%~~%" [] (.tuple [CT.defType d, funcTypeV tvs []]) →
    ∃ ts : Ty (.list .val), Expand d (.func ts .nil) ∧ tvs.length = ts.length
  /-- `$blocktype_(z, bt)` is Core's `ModuleInst.blockType?`, with typed result types. -/
  blocktype : ∀ (s : Store H) (f : Frame) (bt : BlockType) (t₁ t₂ : List CValType),
    f.module.blockType? bt = some (t₁, t₂) →
    ∃ v₁ v₂ : List Value, v₁.length = t₁.length ∧ v₂.length = t₂.length ∧
      TypedV env valtypesT (.list v₁) ∧ TypedV env valtypesT (.list v₂) ∧
      Applies env "blocktype_" [.val (stateV hn s f), .val (Encode.toValue bt)] (instrTypeV v₁ v₂)
  /-- …and conversely. -/
  blocktype_inv : ∀ (s : Store H) (f : Frame) (bt : BlockType) (v₁ v₂ : List Value),
    Applies env "blocktype_" [.val (stateV hn s f), .val (Encode.toValue bt)] (instrTypeV v₁ v₂) →
    ∃ t₁ t₂ : List CValType, f.module.blockType? bt = some (t₁, t₂) ∧
      v₁.length = t₁.length ∧ v₂.length = t₂.length

/-- **The store helpers the backward direction reads** (round 5): `Helpers` without its two
forward fields `expand` and `blocktype`. Those two assert that encoded closed value types are
`valtype*`, which fails for indices of `2 ^ 32` or more (the refutation of `CtrlCall.valtypes`,
`ConfigOk.not_ctrlCall`), so `Helpers` itself does not hold for the concrete builtins. Every
field here holds for every `Prims.builtins` (`Round5.Bwd.helpersInv_builtins`). The backward
lemmas of this family take `HelpersInv`; a `Helpers` coerces to it. -/
structure HelpersInv (env : Env) (hn : H → String) : Prop where
  /-- `$exninst(s; f) = s.EXNS`. -/
  exninst : ∀ (s : Store H) (f : Frame),
    Applies env "exninst" [.val (stateV hn s f)] (.list (s.exns.map exnInstV))
  /-- `$tagaddr(s; f) = f.MODULE.TAGS`. -/
  tagaddr : ∀ (s : Store H) (f : Frame),
    Applies env "tagaddr" [.val (stateV hn s f)] (.list (f.module.tags.map fun a => .num (.natN a)))
  /-- `$tag(z, x)` is the tag instance Core's `Store.tag?` finds. -/
  tag : ∀ (s : Store H) (f : Frame) (x : TagIdx) (ta : Nat) (ti : TagInst),
    s.tag? f x = some (ta, ti) →
    Applies env "tag" [.val (stateV hn s f), .val (Encode.toValue x)] (tagInstToValue CT ti)
  /-- …and nothing else. -/
  tag_inv : ∀ (s : Store H) (f : Frame) (x : TagIdx) (w : Value),
    Applies env "tag" [.val (stateV hn s f), .val (Encode.toValue x)] w →
    ∃ ta ti, s.tag? f x = some (ta, ti) ∧ w = tagInstToValue CT ti
  /-- `$as_deftype(dt) = dt`. -/
  asDeftype : ∀ d : DefType, Applies env "as_deftype" [.val (CT.defType d)] (CT.defType d)
  /-- `$add_exninst(z, [exn])` appends `exn` to the store's exceptions. -/
  addExn : ∀ (s : Store H) (f : Frame) (e : ExnInst),
    Applies env "add_exninst" [.val (stateV hn s f), .val (.list [exnInstV e])]
      (stateV hn (s.addExn e) f)
  /-- SpecTec's `Expand` to `FUNC t* -> []`, read back. -/
  expand_inv : ∀ (d : DefType) (tvs : List Value),
    DDerives env (otherwise env) "Expand" "%~~%" [] (.tuple [CT.defType d, funcTypeV tvs []]) →
    ∃ ts : Ty (.list .val), Expand d (.func ts .nil) ∧ tvs.length = ts.length
  /-- `$blocktype_(z, bt)`, read back. -/
  blocktype_inv : ∀ (s : Store H) (f : Frame) (bt : BlockType) (v₁ v₂ : List Value),
    Applies env "blocktype_" [.val (stateV hn s f), .val (Encode.toValue bt)] (instrTypeV v₁ v₂) →
    ∃ t₁ t₂ : List CValType, f.module.blockType? bt = some (t₁, t₂) ∧
      v₁.length = t₁.length ∧ v₂.length = t₂.length

/-- `Helpers` without its forward `expand` and `blocktype` fields. -/
theorem Helpers.toInv {env : Env} {hn : H → String} (Hp : Helpers env hn) : HelpersInv env hn :=
  ⟨Hp.exninst, Hp.tagaddr, Hp.tag, Hp.tag_inv, Hp.asDeftype, Hp.addExn, Hp.expand_inv,
    Hp.blocktype_inv⟩

instance {env : Env} {hn : H → String} : Coe (Helpers env hn) (HelpersInv env hn) :=
  ⟨Helpers.toInv⟩

/-- The family's decoding and store-typing hypotheses for the backward direction (family E
facts):

* `vals`: an instruction sequence whose image is typed as `val*` is a value sequence;
* `exnFields`: in a typed state, every exception instance's fields are typed values. -/
structure Decoders (env : Env) (hn : H → String) : Prop where
  /-- A `val*`-typed image is the image of `vals vs`. -/
  vals : ∀ ρ : VarEnv, ValsOnly ρ → ∀ l : List Admin, HasTyp env ρ valsT (.list (adminsToV l)) →
    ∃ vs, l = Silmaril.Wasm.Execution.Core.vals vs
  /-- The fields of the exceptions of a typed state are typed values. -/
  exnFields : ∀ (s : Store H) (f : Frame), TypedV env stateT (stateV hn s f) →
    ∀ (a : Nat) (e : ExnInst), s.exns[a]? = some e → TypedV env valsT (.list (e.fields.map valV))

end Silmaril.Wasm.SpecTec.Sim.Exn
