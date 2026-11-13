module

public import Silmaril.Wasm.Game.Shared.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs

/-!
# The untyped shared-store game: arbitrary (reference-typed) interfaces

The games of `Silmaril.Wasm.Game.{Strategy,StatefulEnv,Shared}` name interface
values by the scalar types of `Silmaril.Wasm.Game.Signature` (`Typed`,
`ScalarType.HasVal`), whose typing does not depend on the store. That excludes
every reference type whose values name store objects (`funcref`, `externref`,
struct, array and exception references), and, in the shared-store game, it forces
the `HostKeeps` hypothesis: a `HostOk` host may add a host function of a type no
index-named scalar signature can pose.

This module removes types from the moves altogether.

## The untyped signature

`untypedSig ι` has as operations the calls `⟨x, s, args⟩ : UCall ι`: target `x`, the
caller's store `s` and **raw** Core values `args : List Val`; and as answers
`⟨s', r⟩ : UReply`: the callee's store and a raw Core `Result` (values, trap, or an
exception address). For imports the target is the host code `h : Nat` of the called
host function, exactly the data Core passes to a host relation
(`host h s args out`); for exports it is an export name `x : U.X`, implemented by the
function address `U.addr x`.

Typing is not part of the moves. It is a property of moves, relative to the store
they carry (silmaril-lean's `ValOk`, `ResultTyped`, `StoreOk`, `Extend`):

* `UCall.CallsHost e ps rs`: `e` calls a host function of `e.store` of type
  `func ps rs`, with arguments typed in `e.store`;
* `UInstance.CallOk f ps rs`: the export call `f` invokes a function of type
  `func ps rs` with arguments typed in `f.store` (`InvokeOk`, at a typed store);
* `UReply.OkFor s rs a`: the reply `a` to a call made in `s` is Core's host contract:
  a typed store extending `s` and a result typed at `rs` *in the new store*;
* `UEnvOk s₀ L`: every answer of the environment `L` to a well-typed host call (at a
  store extending `s₀`) is well typed. For `SEnv.uOfHost host` this is the
  returned-outcome half of `HostOk host`, so every `HostOk` host is well formed
  (`uEnvOk_uOfHost`, `Silmaril.Wasm.Game.Untyped.Thms`); the other half (an outcome
  exists) is not needed, since an unanswered call is silent.

So reference values cross interfaces as plain `Val`s, typed relative to the store of
the move that carries them; store growth (`Extend`) preserves that typing
(`ValOk.extend`).

## The instance strategy

An untyped instance `U : UInstance` is a set of export names `U.X` with function
addresses `U.addr`. Its store-passing strategy `U.strategy P` (M1) answers an export
question `⟨x, s, args⟩` by running `$invoke(U.addr x, args)` in `s`; at **every**
callout `h args` (no typing filter) it asks `⟨h, s, args⟩` in the current store and
resumes in the store of the answer, with the raw result (`resumeResult`); it answers
with the final store and raw result. Host-free steps are silent (`U.lts P`), and
`U.dstrategy P` observes divergence. The closed program against a stateful,
nondeterministic environment `L : SEnv UImp` is
`U.closedD P L q = (L.dstrategy q).comp (U.dstrategy P)`.

`UStep P L` is Core reduction in product with `L`, an answer continuing the code in
the store it returns (Core's `callRefHost` reduct); `uBehavioursOf` its behaviours.

## Typed views

* `ScalarInstance.toU`: a scalar instance is the untyped instance of its export
  addresses; `eraseOp`/`eraseAr`/`ScalarInstance.eraseMove` forget the typing of
  shared moves (injectively), and `SEnv.erase` an environment over a typed shared
  signature. `Silmaril.Wasm.Game.Untyped.Thms` shows that the typed shared strategy is
  the untyped one read on typed plays.
* `SEnv.uOfHost host`: every Core host relation, as a one-state environment.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded

/-- A call of the target `target` made in the store `store` with raw arguments `args`. -/
structure UCall (ι : Type) where
  /-- The callee: a host code (imports) or an export name (exports). -/
  target : ι
  /-- The caller's store. -/
  store : Store Nat
  /-- The raw arguments. -/
  args : List Val

/-- A reply: the callee's store and its raw Core result. -/
structure UReply where
  /-- The store after the call. -/
  store : Store Nat
  /-- The Core result (values, trap or exception address). -/
  result : Result

/-- **The untyped shared signature** over call targets `ι`. -/
abbrev untypedSig (ι : Type) : Sig.{0} where
  Op := UCall ι
  Ar _ := UReply

/-- The untyped import signature: calls of host code `h : Nat`. -/
abbrev UImp : Sig.{0} := untypedSig Nat

/-! ### Store-relative typing of moves -/

/-- The call `e` is a well-typed call, in a typed store, of a host function of `e.store`
with host code `e.target` and type `func ps rs`. -/
def UCall.CallsHost (e : UCall Nat) (ps rs : Ty (.list .val)) : Prop :=
  StoreOk e.store ∧ ∃ fi ∈ e.store.funcs, fi.code = .host e.target ∧
    Expand fi.type (.func ps rs) ∧ List.Forall₂ (ValOk e.store) e.args ps.toList

/-- The reply `a` to a call made in the store `s` returning `rs` satisfies Core's host
contract: a typed store extending `s`, and a result typed at `rs` in that store. -/
def UReply.OkFor (s : Store Nat) (rs : Ty (.list .val)) (a : UReply) : Prop :=
  StoreOk a.store ∧ Extend s a.store ∧ ResultTyped a.store a.result rs.toList

/-- **Well-formed untyped environments**, from the store `s₀`: every answer to a
well-typed host call made at a store extending `s₀` satisfies the host contract. -/
def UEnvOk (s₀ : Store Nat) (L : SEnv UImp) : Prop :=
  ∀ (q : L.S) (e : UCall Nat) (a : UReply) (q' : L.S) (ps rs : Ty (.list .val)),
    Extend s₀ e.store → e.CallsHost ps rs → L.Ans q e a q' → a.OkFor e.store rs

namespace SEnv

/-- **Every Core host relation is an untyped environment**: a one-state machine answering
the call `⟨h, s, args⟩` as `host h s args` returns, and diverging when it may. -/
abbrev uOfHost (host : HostSemantics Nat) : SEnv UImp where
  S := Unit
  Ans _ e a _ := host e.target e.store e.args (.returned a.store a.result)
  Div _ e := host e.target e.store e.args .diverged

end SEnv

/-! ### Untyped instances -/

/-- An untyped instance: export names with the function addresses implementing them. -/
structure UInstance where
  /-- The export names. -/
  X : Type
  /-- The function address of each export. -/
  addr : X → Nat

namespace UInstance

variable (U : UInstance)

/-- The import signature (the same for every untyped instance). -/
abbrev E (_U : UInstance) : Sig.{0} := UImp

/-- The export signature. -/
abbrev F : Sig.{0} := untypedSig U.X

/-- The export call `f` is a well-typed invocation, in a typed store, of a function of type
`func ps rs`. -/
def CallOk (f : U.F.Op) (ps rs : Ty (.list .val)) : Prop :=
  StoreOk f.store ∧ ∃ fi, f.store.funcs[U.addr f.target]? = some fi ∧
    Expand fi.type (.func ps rs) ∧ List.Forall₂ (ValOk f.store) f.args ps.toList

/-- The thread of an export question: the pending invocation. -/
def init (f : U.F.Op) : Thread := .pending (U.addr f.target) f.args

/-- Hidden states of the untyped instance: no store while idle. -/
inductive State where
  /-- No export call is active. -/
  | idle
  /-- The export call `f` is active, its thread `t` running in the store `s`. -/
  | running (f : U.F.Op) (s : Store Nat) (t : Thread)
  /-- The export call `f` waits for the answer to the import question `e`. -/
  | waiting (f : U.F.Op) (s : Store Nat) (t : Thread) (e : U.E.Op)

/-- The game position of a hidden state. -/
def State.pos {U : UInstance} : U.State → Pos U.E U.F
  | .idle => .idle
  | .running f _ _ => .run f
  | .waiting f _ _ e => .wait f e

/-- Transitions of the untyped instance, host-free steps silent. -/
inductive Trans (P : Profile) : U.State → Option (Move U.E U.F) → U.State → Prop where
  /-- An export question starts the invocation in the store it carries (Opponent). -/
  | call (f : U.F.Op) : Trans P .idle (some (.inr (.ask f))) (.running f f.store (U.init f))
  /-- A host-free machine step (silent). -/
  | tau {f : U.F.Op} {s s' : Store Nat} {t t' : Thread} (h : InternalP P (s, t) (s', t')) :
      Trans P (.running f s t) none (.running f s' t')
  /-- **Every** callout asks its raw call in the current store (Proponent). -/
  | ucall {f : U.F.Op} {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
      (callout : CalloutAt s t h args) :
      Trans P (.running f s t) (some (.inl (.ask ⟨h, s, args⟩))) (.waiting f s t ⟨h, s, args⟩)
  /-- The answer resumes the thread with the raw result, in the store of the answer
  (Opponent). -/
  | uret {f : U.F.Op} {s : Store Nat} {t : Thread} {e : U.E.Op} (a : UReply) :
      Trans P (.waiting f s t e) (some (.inl (.ans e a)))
        (.running f a.store (resumeResult s t a.result))
  /-- A finished thread answers with its raw result and the final store (Proponent). -/
  | oret {f : U.F.Op} {s : Store Nat} {t : Thread} {r : Result} (final : ResultAt s t r) :
      Trans P (.running f s t) (some (.inr (.ans f ⟨s, r⟩))) .idle

/-- The transition system of the untyped instance. -/
def lts (P : Profile) : LTS U.E U.F := ⟨U.State, .idle, U.Trans P⟩

/-- **The strategy of the untyped instance** (M1). -/
noncomputable def strategy (P : Profile) : Strategy U.E U.F := Strategy.ofLTS (U.lts P)

/-- **The divergence-observing strategy of the untyped instance.** -/
noncomputable def dstrategy (P : Profile) : DStrategy U.E U.F := DStrategy.ofLTS (U.lts P)

/-- The closed program against the environment `L` in state `q`. -/
noncomputable def closed (P : Profile) (L : SEnv UImp) (q : L.S) : Strategy Sig.empty U.F :=
  (L.strategy q).comp (U.strategy P)

/-- **The closed program as a divergence-observing strategy**: a composite. -/
noncomputable def closedD (P : Profile) (L : SEnv UImp) (q : L.S) : DStrategy Sig.empty U.F :=
  (L.dstrategy q).comp (U.dstrategy P)

end UInstance

/-- One step of Core reduction in product with an untyped environment: every host call is
asked raw, and an answer continues the code in the store of the answer. -/
inductive UStep (P : Profile) (L : SEnv UImp) : Config Nat × L.S → Config Nat × L.S → Prop where
  /-- A host-free Core step; the host state is unchanged. -/
  | internal {c c' : Config Nat} {q : L.S}
      (h : Execution.Core.Step P (fun _ _ _ _ => False) c c') : UStep P L (c, q) (c', q)
  /-- The host answers the call made in the current store with `a`. -/
  | answer {c : Config Nat} {E : Ctx} {fa h : Nat} {args : List Val} {a : UReply} {q q' : L.S}
      (hd : decompose? c.store c.code = some (E, fa, h, args))
      (ans : L.Ans q ⟨h, c.store, args⟩ a q') :
      UStep P L (c, q) (⟨a.store, c.frame, E.fill a.result.toAdmin⟩, q')
  /-- The host diverges on the call: a self-loop. -/
  | silent {c : Config Nat} {E : Ctx} {fa h : Nat} {args : List Val} {q : L.S}
      (hd : decompose? c.store c.code = some (E, fa, h, args))
      (hs : L.Silent q ⟨h, c.store, args⟩) : UStep P L (c, q) (c, q)

/-- Runs of the untyped product semantics. -/
abbrev USteps (P : Profile) (L : SEnv UImp) : Config Nat × L.S → Config Nat × L.S → Prop :=
  Relation.ReflTransGen (UStep P L)

/-- The behaviours of `c` against the untyped environment `L` in state `q`. -/
def uBehavioursOf (P : Profile) (L : SEnv UImp) (q : L.S) (c : Config Nat) :
    Set (Behaviour Val) :=
  {b | ∃ (c' : Config Nat) (q' : L.S) (r : Result),
      USteps P L (c, q) (c', q') ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour} ∪
    {b | b = .diverges ∧ InfiniteTrace (UStep P L) (c, q)}

/-- The observations of a closed divergence-observing strategy over an untyped signature for
the question `f`: the Core behaviours of its answers (any final store), and `diverges`. -/
def uDCompositeObs {ι : Type} (δ : DStrategy Sig.empty (untypedSig ι)) (f : UCall ι) :
    Set (Behaviour Val) :=
  {b | ∃ a : UReply, Responds δ.toStrategy f a ∧ b = a.result.toBehaviour} ∪
    {b | b = .diverges ∧ [.inr (.ask f)] ∈ δ.div}

/-- The observations of a closed strategy over an untyped signature for the question `f`: the
behaviours of its answers, and `diverges` when it never answers. -/
def uCompositeObs {ι : Type} (C : Strategy Sig.empty (untypedSig ι)) (f : UCall ι) :
    Set (Behaviour Val) :=
  {b | ∃ a : UReply, Responds C f a ∧ b = a.result.toBehaviour} ∪
    {b | b = .diverges ∧ ∀ a, ¬ Responds C f a}

/-! ### Typed views -/

/-- Forget the typing of a typed shared call. -/
def eraseOp {ts : List FnType} (e : (sharedSig ts).Op) : UCall Nat := ⟨e.1.val, e.2.1, e.2.2.1⟩

/-- Forget the typing of a typed shared answer. -/
def eraseAr {ts : List FnType} {e : (sharedSig ts).Op} (a : (sharedSig ts).Ar e) : UReply :=
  ⟨a.1, Answer.toResult (ft := ts.get e.1) a.2⟩

namespace SEnv

/-- **The untyped reading of a typed shared environment**: it answers the erasure of a typed
call with the erasure of an answer, and diverges where `L` may. -/
def erase {ts : List FnType} (L : SEnv (sharedSig ts)) : SEnv UImp where
  S := L.S
  Ans q e a q' := ∃ (e' : (sharedSig ts).Op) (a' : (sharedSig ts).Ar e'),
    eraseOp e' = e ∧ eraseAr a' = a ∧ L.Ans q e' a' q'
  Div q e := ∃ e' : (sharedSig ts).Op, eraseOp e' = e ∧ L.Div q e'

end SEnv

namespace ScalarInstance

variable (I : ScalarInstance)

/-- **A scalar instance as an untyped instance**: its exports, at their addresses. -/
def toU : UInstance := ⟨Fin I.exports.length, I.addr⟩

/-- Forget the typing of a typed shared export call. -/
def eraseF (f : I.shF.Op) : I.toU.F.Op := ⟨f.1, f.2.1, f.2.2.1⟩

/-- Forget the typing of a move of the typed shared game. -/
def eraseMove : Move I.shE I.shF → Move I.toU.E I.toU.F
  | .inl (.ask e) => .inl (.ask (eraseOp e))
  | .inl (.ans e a) => .inl (.ans (eraseOp e) (eraseAr a))
  | .inr (.ask f) => .inr (.ask (I.eraseF f))
  | .inr (.ans f a) => .inr (.ans (I.eraseF f) (eraseAr a))

end ScalarInstance

/-! ### Worked example: references across both interfaces -/

namespace UntypedExample

/-- `externref = (ref null extern)`. -/
def externRef : ValType := .ref ⟨true, .abstract .extern⟩

/-- The module: imports `env.pass : [externref] → [externref]` and exports
`relay : [externref] → [externref]`, whose body is `local.get 0; call 0`: it hands its
reference argument to the import and returns the import's reference result. -/
def exRelay : Module where
  types := [⟨[⟨true, [], .func ⟨[externRef], [externRef]⟩⟩]⟩]
  imports := [⟨"env", "pass", .func ⟨0⟩⟩]
  funcs := [⟨⟨0⟩, [], [.localGet ⟨0⟩, .call ⟨0⟩]⟩]
  exports := [⟨"relay", .func ⟨1⟩⟩]

/-- The validated type of `exRelay`. -/
def exRelayMT : CModuleType := (validate? exRelay).getD ⟨[], []⟩

/-- The store providing the import: one host function (host code `0`). -/
def exRelayStore : Store Nat := importStore (CExternType.funcs exRelayMT.imports)

/-- The spec's allocation of `exRelay` against its import. -/
def exRelayPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? exRelayStore exRelay (importAddrs exRelayMT)).getD (⟨{}, {}, []⟩, none)

/-- The instantiated store. -/
def exRelayS : Store Nat := exRelayPrep.1.store

/-- The untyped instance: the single export `relay` at function address `1`. -/
def exRelayU : UInstance := ⟨Unit, fun _ => 1⟩

/-- **A host passing references back**: a call of host code `h` returns its arguments
unchanged in the same store when every host function with code `h` has equal parameter and
result types, and diverges otherwise. -/
def echoHost : HostSemantics Nat := fun h s vs out =>
  ((∀ fi ∈ s.funcs, fi.code = .host h → ∀ ps rs, Expand fi.type (.func ps rs) → ps = rs) ∧
      out = .returned s (.values vs)) ∨
    (¬ (∀ fi ∈ s.funcs, fi.code = .host h → ∀ ps rs, Expand fi.type (.func ps rs) → ps = rs) ∧
      out = .diverged)

end UntypedExample

end Silmaril.Wasm.Game
