module

public import Silmaril.Wasm.Spec.Embed.Defs
public import Silmaril.Wasm.Spec.Env.Thms
public import Silmaril.Wasm.Spec.Joint.Thms
public import Silmaril.Wasm.Spec.Joint.Wrap.Thms
public import Silmaril.Wasm.Spec.Component.Logic.Thms
public import Silmaril.Wasm.Spec.Component.Async.Thms
public import Silmaril.Wasm.Spec.Multi.Defs
public import Silmaril.Wasm.Institution.CompGraph.Defs

@[expose] public section

/-!
# The Hets logic graph of the specification institutions

`specGraph P C` is a logic graph (`Silmaril.Logic.Institution.LogicGraph`) whose nodes are
(logic, semantics) pairs of `Silmaril.Wasm.Spec`, each read as the institution `inst L S`:

* `mod l s`: a module logic `l : MLogic` (the simple logics, `basic`, `act`, LTL/CTL/TLA,
  export histories) over a module semantics `s : MSem` (`wasmSem P`, the
  divergence-observing `wasmDivSem P`, and programs with environments `(wasmSem P).withEnv`);
* `num l`: a component logic pulled back to numeric Core modules, over `numSem P`;
* `comp l s`: a component logic `l : CLogic` over a component semantics `s : CSem` (wrapped
  modules `wrapSem P`, IR components `irSem C`, joint models `jointSem P C`);
* `syncPull l s`, `async l s`: asynchronous component logics `l : ALogic`, pulled to the
  synchronous events and over the async reading `syncToAsync` of a synchronous semantics.

Comorphism edges (`SEdge`) are the existing translations:

* `mod e s`, `comp e s`, `async e s`: logic maps (`LogicMap.coHom`): each simple logic into
  `act` and `basic`, `neverCall`/`assertNeverFalse` into `callPre`, `act` into LTL/CTL/TLA,
  `retPost` into export histories, the component logics into `act`, `callTyped` into
  `callPre`, `streamSafe` into `act`;
* `env l`: programs with environments to programs (`Semantics.chaosEnv`, `SemMap.coHom`);
* `wrap l`: numeric modules to wrapped modules (`wrapCoHom`, a change of base);
* `jointWrap l`, `jointIR l`: joint models to each kind (`sumInlCoHom`, `sumInrCoHom`);
* `sync l s`: synchronous to asynchronous events (`syncCoHom`).

`SEdge.Expansive` marks the model-expansive edges (all but `env`, `jointWrap`, `jointIR`, whose
model translations are injections, not surjections). `specGraphE` keeps only those, so every
path in it is model-expansive and borrows entailment (`Silmaril.Wasm.Spec.Graph.Thms`).

`Inst.lift`, `Inst.CoHom.lift`, `liftGraph`: the institutions here have signatures in `Type`
(`Inst.{0,0,0,0,0}`), the Wasm logic graph of `Silmaril.Wasm.Institution` has them in `Type 1`;
`ULift` moves a graph up. `fullGraph₃` joins `CompGraph.fullGraph₂` with the lifted
`specGraphE` by `LogicGraph.sum`. It has no cross edges: the nodes of `fullGraph₂` are
observational semantics over other interface categories (`exportIfaces`, `compIfaces`) whose
models are not trace sets.

The harness reduction (`Harness.corridor`) is a corridor between rooms at fixed interfaces, not
an institution comorphism (it is not natural in the program interface), so it is not an edge.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Spec.Graph

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Game
open Silmaril.Wasm.Numerics (Profile)

/-! ## Module logics and semantics -/

/-- Module logics. -/
inductive MLogic where
  | neverCall | callPre | neverCallFrom | retPost | assertNF | basic
  | act | ltlFin | ltlMax | ctl | tla | exportHist
  deriving DecidableEq

/-- The logic of a module-logic node. -/
def MLogic.logic : MLogic → Logic FnType (List Val) (Behaviour Val)
  | .neverCall => Spec.neverCall FnType (List Val) (Behaviour Val)
  | .callPre => Spec.callPre FnType (List Val) (Behaviour Val)
  | .neverCallFrom => Spec.neverCallFrom FnType (List Val) (Behaviour Val)
  | .retPost => Spec.retPost FnType (List Val) (Behaviour Val)
  | .assertNF => Spec.assertNeverFalse FnType (Behaviour Val)
  | .basic => Spec.basic FnType (List Val) (Behaviour Val)
  | .act => Spec.act FnType (List Val) (Behaviour Val)
  | .ltlFin => Spec.ltlFin FnType (List Val) (Behaviour Val)
  | .ltlMax => Spec.ltlMax FnType (List Val) (Behaviour Val)
  | .ctl => Spec.ctl FnType (List Val) (Behaviour Val)
  | .tla => Spec.tla FnType (List Val) (Behaviour Val)
  | .exportHist => Multi.exportHist FnType (List Val) (Behaviour Val)

/-- Module semantics. -/
inductive MSem where
  /-- `wasmSem P`. -/
  | wasm
  /-- `wasmDivSem P`. -/
  | wasmDiv
  /-- `(wasmSem P).withEnv`. -/
  | wasmEnv
  deriving DecidableEq

/-- The semantics of a module-semantics node. -/
noncomputable def MSem.sem (P : Profile) : MSem → Semantics FnType (List Val) (Behaviour Val)
  | .wasm => wasmSem P
  | .wasmDiv => wasmDivSem P
  | .wasmEnv => (wasmSem P).withEnv

/-- The `i`-th injection into `basic`. -/
def basicIn₁ : LogicMap (neverCall FnType (List Val) (Behaviour Val))
    (basic FnType (List Val) (Behaviour Val)) :=
  ((LogicMap.inl _ _).comp (LogicMap.inl _ _)).comp (LogicMap.inl _ _)

/-- The second injection into `basic`. -/
def basicIn₂ : LogicMap (callPre FnType (List Val) (Behaviour Val))
    (basic FnType (List Val) (Behaviour Val)) :=
  ((LogicMap.inr _ _).comp (LogicMap.inl _ _)).comp (LogicMap.inl _ _)

/-- The third injection into `basic`. -/
def basicIn₃ : LogicMap (neverCallFrom FnType (List Val) (Behaviour Val))
    (basic FnType (List Val) (Behaviour Val)) :=
  (LogicMap.inr _ _).comp (LogicMap.inl _ _)

/-- The fourth injection into `basic`. -/
def basicIn₄ : LogicMap (retPost FnType (List Val) (Behaviour Val))
    (basic FnType (List Val) (Behaviour Val)) :=
  LogicMap.inr _ _

/-- Logic-map edges between module logics. -/
inductive MEdge : MLogic → MLogic → Type where
  | ncCp : MEdge .neverCall .callPre
  | anfCp : MEdge .assertNF .callPre
  | ncAct : MEdge .neverCall .act
  | cpAct : MEdge .callPre .act
  | ncfAct : MEdge .neverCallFrom .act
  | rpAct : MEdge .retPost .act
  | anfAct : MEdge .assertNF .act
  | basicAct : MEdge .basic .act
  | ncBasic : MEdge .neverCall .basic
  | cpBasic : MEdge .callPre .basic
  | ncfBasic : MEdge .neverCallFrom .basic
  | rpBasic : MEdge .retPost .basic
  | actFin : MEdge .act .ltlFin
  | actMax : MEdge .act .ltlMax
  | actCtl : MEdge .act .ctl
  | actTla : MEdge .act .tla
  | rpHist : MEdge .retPost .exportHist

/-- The logic map of a module edge. -/
def MEdge.map : {l l' : MLogic} → MEdge l l' → LogicMap l.logic l'.logic
  | _, _, .ncCp => NeverCall.toCallPre _ _ _
  | _, _, .anfCp => AssertNeverFalse.toCallPre _ _
  | _, _, .ncAct => NeverCall.toAct _ _ _
  | _, _, .cpAct => CallPre.toAct _ _ _
  | _, _, .ncfAct => NeverCallFrom.toAct _ _ _
  | _, _, .rpAct => RetPost.toAct _ _ _
  | _, _, .anfAct => AssertNeverFalse.toAct _ _
  | _, _, .basicAct => Basic.toAct _ _ _
  | _, _, .ncBasic => basicIn₁
  | _, _, .cpBasic => basicIn₂
  | _, _, .ncfBasic => basicIn₃
  | _, _, .rpBasic => basicIn₄
  | _, _, .actFin => Act.toLtlFin _ _ _
  | _, _, .actMax => Act.toLtlMax _ _ _
  | _, _, .actCtl => Act.toCtl _ _ _
  | _, _, .actTla => Act.toTla _ _ _
  | _, _, .rpHist => Multi.RetPost.toHist _ _ _

/-! ## Component logics and semantics -/

/-- Synchronous component logics. -/
inductive CLogic where
  | contract | retTyped | callTyped | borrowScoped | noUseAfterDrop | droppedEventually
  | callPre | retPost | act | ltlFin | ltlMax | ctl | tla
  deriving DecidableEq

/-- The logic of a component-logic node. -/
def CLogic.logic : CLogic → Logic CFn (List RVal) Outcome
  | .contract => Spec.contract CFn (List RVal) Outcome
  | .retTyped => Silmaril.Wasm.Spec.Component.retTyped
  | .callTyped => Silmaril.Wasm.Spec.Component.callTyped
  | .borrowScoped => Silmaril.Wasm.Spec.Component.borrowScoped
  | .noUseAfterDrop => Silmaril.Wasm.Spec.Component.noUseAfterDrop
  | .droppedEventually => Silmaril.Wasm.Spec.Component.droppedEventually
  | .callPre => Spec.callPre CFn (List RVal) Outcome
  | .retPost => Spec.retPost CFn (List RVal) Outcome
  | .act => Spec.act CFn (List RVal) Outcome
  | .ltlFin => Spec.ltlFin CFn (List RVal) Outcome
  | .ltlMax => Spec.ltlMax CFn (List RVal) Outcome
  | .ctl => Spec.ctl CFn (List RVal) Outcome
  | .tla => Spec.tla CFn (List RVal) Outcome

/-- Logic-map edges between component logics. -/
inductive CEdge : CLogic → CLogic → Type where
  | contractAct : CEdge .contract .act
  | borrowAct : CEdge .borrowScoped .act
  | dropAct : CEdge .noUseAfterDrop .act
  | typedCp : CEdge .callTyped .callPre
  | cpAct : CEdge .callPre .act
  | rpAct : CEdge .retPost .act
  | actFin : CEdge .act .ltlFin
  | actMax : CEdge .act .ltlMax
  | actCtl : CEdge .act .ctl
  | actTla : CEdge .act .tla

/-- The logic map of a component edge. -/
def CEdge.map : {l l' : CLogic} → CEdge l l' → LogicMap l.logic l'.logic
  | _, _, .contractAct => Contract.toAct _ _ _
  | _, _, .borrowAct => BorrowScoped.toAct
  | _, _, .dropAct => NoUseAfterDrop.toAct
  | _, _, .typedCp => CallTyped.toCallPre
  | _, _, .cpAct => CallPre.toAct _ _ _
  | _, _, .rpAct => RetPost.toAct _ _ _
  | _, _, .actFin => Act.toLtlFin _ _ _
  | _, _, .actMax => Act.toLtlMax _ _ _
  | _, _, .actCtl => Act.toCtl _ _ _
  | _, _, .actTla => Act.toTla _ _ _

/-- Component semantics. -/
inductive CSem where
  /-- Wrapped numeric Core modules, `wrapSem P`. -/
  | wrap
  /-- IR components, `irSem C`. -/
  | ir
  /-- Joint models, `jointSem P C`. -/
  | joint
  deriving DecidableEq

/-- The semantics of a component-semantics node. -/
noncomputable def CSem.sem {M : Type} [Silmaril.Wasm.Component.CoreModule M] (P : Profile)
    (C : Silmaril.Wasm.Component.CoreSem M) : CSem → Semantics CFn (List RVal) Outcome
  | .wrap => wrapSem P
  | .ir => irSem C
  | .joint => jointSem P C

/-- Asynchronous component logics. -/
inductive ALogic where
  | streamSafe | closedOnce | act | ltlMax
  deriving DecidableEq

/-- The logic of an async-logic node. -/
def ALogic.logic : ALogic → Logic CFn AMsg AOut
  | .streamSafe => Silmaril.Wasm.Spec.Component.streamSafe
  | .closedOnce => Silmaril.Wasm.Spec.Component.closedExactlyOnce
  | .act => Spec.act CFn AMsg AOut
  | .ltlMax => Spec.ltlMax CFn AMsg AOut

/-- Logic-map edges between async logics. -/
inductive AEdge : ALogic → ALogic → Type where
  | safeAct : AEdge .streamSafe .act
  | actMax : AEdge .act .ltlMax

/-- The logic map of an async edge. -/
def AEdge.map : {l l' : ALogic} → AEdge l l' → LogicMap l.logic l'.logic
  | _, _, .safeAct => StreamSafe.toAct
  | _, _, .actMax => Act.toLtlMax _ _ _

/-! ## The graph -/

/-- The nodes: (logic, semantics) pairs. -/
inductive SNode where
  | mod (l : MLogic) (s : MSem)
  | num (l : CLogic)
  | comp (l : CLogic) (s : CSem)
  | syncPull (l : ALogic) (s : CSem)
  | async (l : ALogic) (s : CSem)

variable {M : Type} [Silmaril.Wasm.Component.CoreModule M]

/-- The institution of a node. -/
noncomputable def SNode.inst (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) :
    SNode → Inst.{0, 0, 0, 0, 0}
  | .mod l s => Spec.inst l.logic (s.sem P)
  | .num l => Spec.inst (l.logic.pull wrapFn (List.map wrapVal) wrapOut) (numSem P)
  | .comp l s => Spec.inst l.logic (s.sem P C)
  | .syncPull l s => Spec.inst (l.logic.pull id AMsg.args AOut.out) (s.sem P C)
  | .async l s => Spec.inst l.logic (syncToAsync (s.sem P C))

/-- The comorphism edges. -/
inductive SEdge : SNode → SNode → Type where
  /-- A logic map between module logics. -/
  | mod {l l' : MLogic} (e : MEdge l l') (s : MSem) : SEdge (.mod l s) (.mod l' s)
  /-- Programs with environments to programs. -/
  | env (l : MLogic) : SEdge (.mod l .wasmEnv) (.mod l .wasm)
  /-- A logic map between component logics. -/
  | comp {l l' : CLogic} (e : CEdge l l') (s : CSem) : SEdge (.comp l s) (.comp l' s)
  /-- Numeric modules to wrapped modules. -/
  | wrap (l : CLogic) : SEdge (.num l) (.comp l .wrap)
  /-- Joint models to wrapped modules. -/
  | jointWrap (l : CLogic) : SEdge (.comp l .joint) (.comp l .wrap)
  /-- Joint models to IR components. -/
  | jointIR (l : CLogic) : SEdge (.comp l .joint) (.comp l .ir)
  /-- Synchronous to asynchronous events. -/
  | sync (l : ALogic) (s : CSem) : SEdge (.syncPull l s) (.async l s)
  /-- A logic map between async logics. -/
  | async {l l' : ALogic} (e : AEdge l l') (s : CSem) : SEdge (.async l s) (.async l' s)

/-- The comorphism of an edge. -/
noncomputable def SEdge.coHom (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) :
    {a b : SNode} → SEdge a b → Inst.CoHom (a.inst P C) (b.inst P C)
  | _, _, .mod e s => e.map.coHom (s.sem P)
  | _, _, .env l => (wasmSem P).chaosEnv.coHom l.logic
  | _, _, .comp e s => e.map.coHom (s.sem P C)
  | _, _, .wrap l => wrapCoHom l.logic P
  | _, _, .jointWrap l => sumInlCoHom l.logic (wrapSem P) (irSem C)
  | _, _, .jointIR l => sumInrCoHom l.logic (wrapSem P) (irSem C)
  | _, _, .sync l s => syncCoHom l.logic (s.sem P C)
  | _, _, .async e s => e.map.coHom (syncToAsync (s.sem P C))

/-- The model-expansive edges. -/
def SEdge.Expansive : {a b : SNode} → SEdge a b → Prop
  | _, _, .env _ => False
  | _, _, .jointWrap _ => False
  | _, _, .jointIR _ => False
  | _, _, _ => True

/-- **The logic graph of the specification institutions.** -/
noncomputable def specGraph (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) :
    LogicGraph.{0, 0, 0, 0, 0, 0, 0} where
  Logics := SNode
  inst := SNode.inst P C
  Comor := SEdge
  comor e := e.coHom P C
  Mor _ _ := PEmpty
  mor e := e.elim

/-- **The model-expansive part of the graph**: only the expansive edges. -/
noncomputable def specGraphE (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) :
    LogicGraph.{0, 0, 0, 0, 0, 0, 0} where
  Logics := SNode
  inst := SNode.inst P C
  Comor a b := {e : SEdge a b // e.Expansive}
  comor e := e.1.coHom P C
  Mor _ _ := PEmpty
  mor e := e.elim

/-- **The Grothendieck institution of the specification logics.** -/
noncomputable abbrev specFlat (P : Profile) (C : Silmaril.Wasm.Component.CoreSem M) : Inst :=
  (specGraph P C).flatInst

/-! ## Moving up a universe -/

attribute [local instance] uliftCategory

/-- An institution with signatures in `Type` as one with signatures in `Type 1`. -/
@[reducible] def _root_.Silmaril.Logic.Institution.Inst.lift (A : Inst.{0, 0, 0, 0, 0}) :
    Inst.{1, 0, 0, 0, 0} where
  Sign := ULift.{1} A.Sign
  cat := uliftCategory A.Sign
  I := ULift.downFunctor ⋙ A.I

/-- A comorphism, lifted. -/
def _root_.Silmaril.Logic.Institution.Inst.CoHom.lift {A B : Inst.{0, 0, 0, 0, 0}}
    (f : Inst.CoHom A B) : Inst.CoHom A.lift B.lift where
  Φ := (ULift.downFunctor : ULift.{1} A.Sign ⥤ A.Sign) ⋙ f.Φ ⋙
    (ULift.upFunctor : B.Sign ⥤ ULift.{1} B.Sign)
  ρ :=
    { app := fun X => f.ρ.app (ULift.down X)
      naturality := fun X Y g =>
        f.ρ.naturality (X := ULift.down X) (Y := ULift.down Y) g }

/-- A logic graph, lifted. -/
def liftGraph (L : LogicGraph.{0, 0, 0, 0, 0, 0, 0}) : LogicGraph.{0, 0, 1, 0, 0, 0, 0} where
  Logics := L.Logics
  inst a := (L.inst a).lift
  Comor := L.Comor
  comor e := (L.comor e).lift
  Mor _ _ := PEmpty
  mor e := e.elim

/-- **The Wasm logic graph with the specification institutions**: `CompGraph.fullGraph₂` (Core
reduction semantics, games, components) side by side with the model-expansive specification
graph. -/
noncomputable def fullGraph₃ {H : Type} (P : Profile) (host : HostSemantics H)
    (Env : Module → Store H → List ExternAddr → Prop) (C : Silmaril.Wasm.Component.CoreSem M) :
    LogicGraph.{0, 0, 1, 0, 0, 0, 0} :=
  Silmaril.Wasm.Institution.LogicGraph.sum (Silmaril.Wasm.Institution.CompGraph.fullGraph₂ C P host Env)
    (liftGraph (specGraphE P C)) (fun _ _ => PEmpty) (fun e => e.elim)

end Silmaril.Wasm.Spec.Graph
