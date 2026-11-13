module

public import Silmaril.Wasm.Component.Reference.Sound.Defs
public import Silmaril.Wasm.Component.Reference.Link.Defs
import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR
import Silmaril.Proofs.Wasm.Component.Reference.HostMap
import Silmaril.Proofs.Wasm.Component.Reference.CoreRun
import Silmaril.Proofs.Wasm.Component.Reference.MachineDet
import Silmaril.Proofs.Wasm.Component.Reference.FlatABI
import Silmaril.Proofs.Wasm.Component.Reference.RefToSpec
import Silmaril.Proofs.Wasm.Component.Reference.InstRun
import Silmaril.Proofs.Wasm.Component.Reference.CallRun
import Silmaril.Proofs.Wasm.Component.Reference.ValidRun
import Silmaril.Proofs.Wasm.Component.Reference.FloatSound
import Silmaril.Proofs.Wasm.Component.Reference.MultiSeq
import Silmaril.Proofs.Wasm.Component.Reference.MultiIR
import Silmaril.Proofs.Wasm.Component.Reference.ImpIR
import Silmaril.Proofs.Wasm.Component.Reference.SoundI
import Silmaril.Proofs.Wasm.Component.Reference.SoundSeqI
import Silmaril.Proofs.Wasm.Component.Reference.FloatSeqSound
import Silmaril.Proofs.Wasm.Component.Reference.LinkIR

/-!
# Soundness of the component IR against the reference machine: theorems

For simple components (one core instance of an import-free numeric Core 3.0 module, exports
`canon lift`ed at scalar/record/variant types), at every silmaril profile `P`:

* `specToIR` (proved): every terminating outcome of the canonical-ABI specification
  `exportSpec P c x vs` is a play of the IR denotation `c.toComp.den (modSem P)`: the play
  `ask (j, vals vs) · ans (vals ws)` for returned results `ws`, `ask · ans none` for a trap;
* `refToSpec_of_arity` (proved): the reference-machine half for every component in the
  fragment within the flat arities (`Simple.Arity`), with no validity hypothesis; it is the
  instantiation phase (`instPhase`: the machine runs deterministically to the instance) and the
  call phase (`callPhase`: `canon lift`, the core activation as a Core run, the flat ABI);
* `validArity` (proved): the validator imposes the flat arities (`Simple.ValidArity`), by
  symbolic execution of the validator over `toRef`; hence `refToSpec : RefToSpecAll`;
* `Simple.sound` (proved, with `Simple.Arity` as a hypothesis): for float-free `c` whose module
  is instantiated as the IR assumes (`Simple.Inst`), every
  behaviour of the reference machine calling export `j` of `c.toRef` on the reference images of well-typed IR
  values, after instantiation from the empty store, over `core3P P` and at any component choice
  profile, is matched by the IR denotation (`IRObs`). This is the direction that makes IR-level
  verification sound: a property of all plays of the IR denotation holds of every reference
  outcome.

Divergence is not observed by the IR's (finite-play) strategies and imposes nothing.

Beyond the float-free single call (definitions in `Sound.Defs`):

* floats (`Simple.sound_float`, proved): without `FloatFree` (floats anywhere except in variant
  payloads, `SimpleFloatOk`), a reference behaviour is the IR's on some admissible NaN lowering
  `vs'` of the arguments (`NanAtList prof`), with returned NaNs canonicalised (`IRObsF`); under
  the deterministic component profile `vs'` is the canonicalisation
  (`Simple.sound_float_deterministic`);
* call sequences on one instance (`Simple.sound_seq`, proved): every behaviour of a sequence of
  calls (`seqBehaviours`) is a chain of canonical-ABI specification outcomes threading the Core
  store (`seq_refToSpec`: `SeqSpec`, `specAt`), and every such chain is a multi-question play of
  the IR denotation, the instance's state persisting between questions
  (`seqSpecToIR : SeqSpecToIR`); with floats outside variant payloads
  (`Simple.sound_seq_float`, proved) on admissible NaN lowerings of each call (`NanCalls`),
  results reported canonicalised (`canonResults`, `SeqIRObsF`).

Imports (`SimpleI`, core import `k` the `canon lower` of component import `k`): the IR side
`simpleI_specToIR : SimpleI.SpecToIR` (proved): a play of the core instance answering an export
call after import calls is the IR play of the export question, the component import calls
(`ImpRel`) and the lifted answer, over `impSem P`, the semantics of modules with imports
(`impSem_toImp`: it is `modSem P` on import-free modules). The reference side is proved in two
phases (`Silmaril.Proofs.Wasm.Component.Reference.instPhaseI`: instantiating `c.toRef` from the
store of host functions of its imports only reaches the configuration after instantiation;
`callPhaseI`: from it, every behaviour of an export call over `core3P P` with `answerHost P g`
is matched by the IR, `IRObsI`), assembled in `SimpleI.sound` (proved, every profile and
component choice profile) for components wired as `SimpleI.toRef` assumes (`SimpleI.Inst`).
Sequences of calls on one instance with imports: `SimpleI.sound_seq` (proved, every profile and
component choice profile): every behaviour of `seqBehavioursI` is the IR play `seqMovesI` of the
resolved calls, each with its component import calls answered by `g`, followed by the last
outcome as `SeqIRObsI` prescribes. Stateful hosts (`answerHostS`, host state of any type,
answers and next state a function of the state and the arguments): `SimpleI.soundS` and
`SimpleI.sound_seqS` (proved), the import calls answered with the host state threaded
(`HostRun`); the stateless theorems are their instances at `statelessG g` (`answerHost`).

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.{ImpIR,SpecToIR,RefToSpec,InstRun,CallRun,ValidRun,
FloatSound,MultiSeq,MultiIR,FloatSeqSound,InstImpPhase,CallPhaseI,SoundI,CallKI,CallPhaseKI,SeqIRI,
SoundSeqI}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

/-- **The IR side of soundness** (proved). -/
theorem specToIR : Simple.SpecToIR :=
  Silmaril.Proofs.Wasm.Component.Reference.specToIR

/-- **The reference-machine half within the flat arities** (proved): for a float-free
simple component within the flat arities whose module is instantiated as the IR assumes, every
behaviour of calling an export on the reference images of well-typed IR values, after
instantiating `c.toRef` from the empty store, over `core3P P` at any component choice profile,
is an outcome of the canonical-ABI specification. No validity hypothesis is needed. -/
theorem refToSpec_of_arity (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) :
    ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHost P) () c.toRef [] x.name (vs.map toRefVal) ⊆
        exportSpec P c x vs :=
  fun x hx vs hvs => Silmaril.Proofs.Wasm.Component.Reference.refToSpec_of_phases
    Silmaril.Proofs.Wasm.Component.Reference.instPhase
    Silmaril.Proofs.Wasm.Component.Reference.callPhase P prof c hc hf hi ha x hx vs hvs

/-- **The validator imposes the flat arities** (proved). -/
theorem validArity : Simple.ValidArity :=
  Silmaril.Proofs.Wasm.Component.Reference.validArity_holds

/-- **The reference-machine half** (proved). -/
theorem refToSpec : RefToSpecAll :=
  fun P prof c hc hf hi hv => refToSpec_of_arity P prof c hc hf hi (validArity c hc hf hi hv)

/-- **Soundness of the component IR w.r.t. the reference Component Model semantics over
Core 3.0**, for simple components within the flat arities (proved). -/
theorem Simple.sound (P : Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  specToIR P c hc j vs b
    (refToSpec_of_arity P prof c hc hf hi ha _ (List.getElem_mem j.isLt) vs hvs hb)

/-- **`Simple.sound` for components accepted by the reference validator** (proved). -/
theorem Simple.sound_of_valid (P : Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple) (hc : c.Good) (hf : c.FloatFree)
    (hi : c.Inst) (hv : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 c.toRef = .ok ct)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b :=
  Simple.sound P prof c hc hf hi (validArity c hc hf hi hv) j vs hvs b hb

/-! ## Floats -/

/-- **Soundness with floats** (outside variant payloads; proved): every behaviour of the
reference machine calling export `j` of `c.toRef` on the reference images of well-typed IR
values `vs`, over `core3P P` at the component choice profile `prof`, is the IR observation of
the call on an admissible lowering `vs'` of `vs`, with returned values canonicalised. -/
theorem Simple.sound_float (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    ∃ vs', NanAtList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      IRObsF (k := c.toComp.exports.length) (c.toComp.den (modSem P))
        ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results vs' b :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_float P prof c hc hf hi ha j vs hvs b hb

/-- **Soundness with floats under the deterministic component profile** (proved): the IR is
called on the canonicalisation of the arguments. -/
theorem Simple.sound_float_deterministic (P : Profile) (c : Simple) (hc : c.Good)
    (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (b : Outcome)
    (hb : b ∈ exportBehaviours .deterministic (refHost P) () c.toRef [] c.exports[j].name
      (vs.map toRefVal)) :
    IRObsF (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ c.exports[j].ty.results
      (canonAtList c.exports[j].ty.params vs) b :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_float_deterministic P c hc hf hi ha j vs
    hvs b hb

/-! ## Sequences of calls -/

/-- **The reference-machine half for sequences of calls** (proved, every profile and component
choice profile). -/
theorem seq_refToSpec (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple)
    (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (wss : List (List Silmaril.Wasm.Component.Val))
      (s : Silmaril.Wasm.Execution.Core.Store Nat), c.mod.IsInst I ∧
      SeqSpec P c I I.store (specCalls c calls) wss s ∧ p.1 = wss.map (·.map toRefVal) ∧
      p.2 ∈ specAt P c I c.exports[j] vs s :=
  Silmaril.Proofs.Wasm.Component.Reference.seq_refToSpec P prof c hc hf hi ha calls j vs ht hvs p hp

/-- **The IR half for sequences of calls** (proved). -/
theorem seqSpecToIR : SeqSpecToIR :=
  Silmaril.Proofs.Wasm.Component.Reference.seqSpecToIR

/-- **Soundness of the component IR for sequences of calls on one instance** (proved, every
profile and component choice profile): for a float-free simple component within the flat
arities whose module is instantiated as the IR assumes, every behaviour of instantiating
`c.toRef`, calling its exports `calls` in order, each resolving, then export `j`, on reference
images of well-typed IR values, over `core3P P`, records reference images of IR results `wss`;
the IR denotation plays the resolved calls with these results (the instance's state persisting
between questions), and the last outcome as in `SeqIRObs`. -/
theorem Simple.sound_seq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : Simple)
    (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_seq P prof c hc hf hi ha calls j vs ht hvs
    p hp

/-- **`Simple.sound_seq` for components accepted by the reference validator** (proved). -/
theorem Simple.sound_seq_of_valid (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : c.FloatFree) (hi : c.Inst)
    (hv : ∃ ct, check? Silmaril.Wasm.Component.Features.p2 c.toRef = .ok ct)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves c calls wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs p.2 :=
  Simple.sound_seq P prof c hc hf hi (validArity c hc hf hi hv) calls j vs ht hvs p hp

/-- **Soundness for sequences of calls with floats** (outside variant payloads; proved, every
profile and component choice profile): as `Simple.sound_seq` without `FloatFree`. Every
behaviour `p` is the IR play of admissible NaN lowerings `calls'` of the calls (`NanCalls`, one
`NanAtList` witness per call) with IR results `wss`, which the reference reports canonicalised
(`canonResults`); the last call is matched on an admissible lowering `vs'` of `vs` as
`SeqIRObsF` prescribes (returned NaNs canonicalised). -/
theorem Simple.sound_seq_float (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : Simple) (hc : c.Good) (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (calls' : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val)) (vs' : List Silmaril.Wasm.Component.Val),
      NanCalls prof c calls calls' ∧ TypedCalls c calls' ∧
      NanAtList prof c.exports[j].ty.params vs vs' ∧
      ValTy.checkList c.exports[j].ty.params vs' = true ∧
      p.1 = canonResults c calls' wss ∧ seqMoves c calls' wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObsF c (c.toComp.den (modSem P)) calls' wss j vs' p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_seq_float P prof c hc hf hi ha calls j vs
    ht hvs p hp

/-- **Sequences with floats under the deterministic component profile** (proved): the IR is
called on the canonicalised arguments (`canonCalls`, `canonAtList`). -/
theorem Simple.sound_seq_float_deterministic (P : Profile) (c : Simple) (hc : c.Good)
    (hf : SimpleFloatOk c) (hi : c.Inst) (ha : c.Arity)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours .deterministic (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = canonResults c (canonCalls c calls) wss ∧
      seqMoves c (canonCalls c calls) wss ∈ c.toComp.den (modSem P) ∧
      SeqIRObsF c (c.toComp.den (modSem P)) (canonCalls c calls) wss j
        (canonAtList c.exports[j].ty.params vs) p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.Simple.sound_seq_float_deterministic P c hc hf hi ha
    calls j vs ht hvs p hp

/-! ## Imports -/

/-- On import-free modules `impSem P` is `modSem P`. -/
theorem impSem_toImp (P : Profile) (m : NumModule) :
    (impSem P).sem m.toImp = (modSem P).sem m :=
  Silmaril.Proofs.Wasm.Component.Reference.impSem_toImp P m

/-- **The IR side with imports** (proved). -/
theorem simpleI_specToIR : SimpleI.SpecToIR :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_specToIR

/-- **Soundness of the component IR with imports answered by a host** (proved, every profile
and component choice profile): for a float-free component with imports within the flat arities,
wired as `SimpleI.toRef` assumes, and a host `g` answering in the IR's types, every behaviour of
instantiating `c.toRef` with import `k` bound to host function `k` and calling export `j` on the
reference images of well-typed IR values, over `core3P P` with `answerHost P g`, is matched by
the IR denotation over `impSem P` (`IRObsI`). -/
theorem SimpleI.sound (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : SimpleI)
    (hc : c.Good) (hi : c.Inst) (hff : c.FloatFree) (har : c.Arity)
    (g : Silmaril.Wasm.Component.Runtime.HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val)) (hg : c.HostOk g)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehavioursI prof (answerHost P g) () c.toRef c.imports c.exports[j].name
      (vs.map toRefVal)) :
    IRObsI (c.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g b :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_sound P prof c hc hi hff har g hg j vs hvs b hb

/-- **Soundness of the component IR for sequences of calls with imports answered by a host**
(proved, every profile and component choice profile): for a float-free component with imports
within the flat arities, wired as `SimpleI.toRef` assumes, and a host `g` answering in the IR's
types, every behaviour of instantiating `c.toRef` with its imports bound to the host functions of
`g`, calling its exports `calls` in order, each resolving, then export `j`, on reference images
of well-typed IR values, over `core3P P` with `answerHost P g`, records reference images of IR
results `wss`; the IR denotation over `impSem P` plays the resolved calls with these results,
each after component import calls (`dss`) answered by `g`, the instance's state persisting
between questions, and the last outcome as `SeqIRObsI` prescribes. -/
theorem SimpleI.sound_seq (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : SimpleI) (hc : c.Good) (hi : c.Inst) (hff : c.FloatFree) (har : c.Arity)
    (g : Silmaril.Wasm.Component.Runtime.HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val)) (hg : c.HostOk g)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHost P g) () c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))),
      p.1 = wss.map (·.map toRefVal) ∧ (∀ ds ∈ dss, ∀ d ∈ ds, HostAnswers g d) ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSem P) ∧
      SeqIRObsI c (c.toComp.den (impSem P)) calls dss wss j vs g p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_sound_seq P prof c hc hi hff har g hg calls j vs
    ht hvs p hp

/-- **Soundness of the component IR with imports answered by a stateful host** (proved, every
profile and component choice profile): for a float-free component with imports within the flat
arities, wired as `SimpleI.toRef` assumes, and a stateful host `g` (`answerHostS`: host state of
any type `σ`, the answer and the next state a function of the state and the arguments)
answering in the IR's types in every state, every behaviour of instantiating `c.toRef` from
host state `s₀` and calling export `j` on reference images of well-typed IR values, over
`core3P P`, is matched by the IR denotation over `impSem P`, the component import calls answered
by `g` with the host state threaded from `s₀` (`IRObsIS`). -/
theorem SimpleI.soundS (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (c : SimpleI)
    (hc : c.Good) (hi : c.Inst) (hff : c.FloatFree) (har : c.Arity) {σ : Type}
    (g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ)) (hg : c.HostOkS g) (s₀ : σ)
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome)
    (hb : b ∈ exportBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports c.exports[j].name
      (vs.map toRefVal)) :
    IRObsIS (c.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g s₀ b :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_soundS P prof c hc hi hff har g hg s₀ j vs hvs b
    hb

/-- **Soundness of the component IR for sequences of calls with imports answered by a stateful
host** (proved, every profile and component choice profile): as `SimpleI.sound_seq`, with the
stateful host `answerHostS P g` from host state `s₀`; the component import calls `dss` of the
resolved calls are answered by `g` with the host state threaded from `s₀` to `s₁`
(`HostRun g s₀ dss.flatten s₁`), and the last call's from `s₁` (`SeqIRObsIS`). -/
theorem SimpleI.sound_seqS (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (c : SimpleI) (hc : c.Good) (hi : c.Inst) (hff : c.FloatFree) (har : c.Arity) {σ : Type}
    (g : σ → Silmaril.Wasm.Component.Runtime.HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val × σ)) (hg : c.HostOkS g) (s₀ : σ)
    (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin c.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : c.TypedCalls calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehavioursI prof (answerHostS P g) s₀ c.toRef c.imports
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal)) :
    ∃ (wss : List (List Silmaril.Wasm.Component.Val))
      (dss : List (List (Σ _ : (sigN c.imports.length).Op, Option Payload))) (s₁ : σ),
      p.1 = wss.map (·.map toRefVal) ∧ HostRun g s₀ dss.flatten s₁ ∧
      seqMovesI c calls dss wss ∈ c.toComp.den (impSem P) ∧
      SeqIRObsIS c (c.toComp.den (impSem P)) calls dss wss j vs g s₁ p.2 :=
  Silmaril.Proofs.Wasm.Component.Reference.simpleI_sound_seqS P prof c hc hi hff har g hg s₀ calls
    j vs ht hvs p hp


/-! ## Two components linked -/

/-- **The IR side of two linked components** (proved, every profile): a play of the importer's
core instance whose component import calls are answered by the exporter's specification, with
the exporter's Core store threaded from its instance's store (`Linked2.ExpRun`), is a two-move
play of the linked IR `l.toComp.den (impSem P)`. -/
theorem Linked2.specToIR : Linked2.SpecToIR :=
  Silmaril.Proofs.Wasm.Component.Reference.linked2_specToIR

end Silmaril.Wasm.Component.Reference
