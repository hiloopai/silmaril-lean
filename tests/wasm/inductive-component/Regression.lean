module

import Silmaril.Wasm.Component.IntrinsicWiring.Lift.Thms
import Silmaril.Wasm.Validation.Intrinsic.ReifyThms
import Silmaril.Wasm.ModuleParts.Thms
import Silmaril.Wasm.Component.Reference.Thms
import Silmaril.Wasm.Component.Reference.Embedding.Thms
import Silmaril.Wasm.Component.Reference.Example.Defs
import Silmaril.Wasm.Component.Reference.DirectLift.Init.Thms
import Silmaril.Wasm.Execution.Core.Entry.Thms
import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
import Silmaril.Wasm.Execution.Core.Exec.ValCheck
import Silmaril.Wasm.Game.Machine.Thms
import Silmaril.Wasm.Game.Strategy.Thms
import Silmaril.Wasm.Institution.DirectLiftTerminal.Thms
import Silmaril.Wasm.SingleThreaded.Exec.CheckedRun
import Silmaril.Wasm.Verify.Kernel.Thms

open Silmaril Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Validation
open Silmaril.Wasm.Component.IntrinsicWiring
open Silmaril.Wasm.Component.Types

private def signature : Wasm.RecType := ⟨[⟨true, [], .func ⟨[], [.i32]⟩⟩]⟩

private def providerParts : ModuleParts Wasm.Func :=
  ⟨{ types := [signature], exports := [⟨"get", .func ⟨0⟩⟩] }, [⟨⟨0⟩, [], [.intConst .i32 42]⟩]⟩

private def consumerParts : ModuleParts Wasm.Func :=
  ⟨{ types := [signature], imports := [⟨"env", "get", .func ⟨0⟩⟩], exports := [⟨"run", .func ⟨1⟩⟩] },
    [⟨⟨0⟩, [], [.call ⟨0⟩]⟩]⟩

private def provider := providerParts.toCore
private def consumer := consumerParts.toCore

private abbrev CorePayload := Σ raw : Wasm.Module, Wasm.Validation.Intrinsic.Reify.Reified raw

private def providerPayload : CorePayload :=
  ⟨provider, (Wasm.Validation.Intrinsic.Reify.reify? provider).get (by decide +kernel)⟩

private def consumerPayload : CorePayload :=
  ⟨consumer, (Wasm.Validation.Intrinsic.Reify.reify? consumer).get (by decide +kernel)⟩

private def bodyErase (payload : CorePayload) : Wasm.Module := payload.2.typed.erase

private def interface? (payload : CorePayload) : Option (CoreModuleType Core3Extern) :=
  core3ModuleType? (bodyErase payload)

private abbrev State := DefState Core3Extern
private abbrev From (before : State) := Σ after, Program .p2 core3Profile interface? before after

private def emitCore {before : State} (payload : CorePayload) : Option (From before) :=
  match checked : interface? payload with
  | none => none
  | some type => some ⟨_, .cons (.core payload type checked) .nil⟩

private def emit {before : State} (cmd : Command) : Option (From before) :=
  match checked : cmd.check .p2 core3Profile before with
  | .error _ => none
  | .ok after => some ⟨after, .cons (.command cmd checked) .nil⟩

private def append {before : State} (part : Option (From before)) (next : ∀ state, Option (From state)) :
    Option (From before) := do
  let ⟨state, left⟩ ← part
  let ⟨after, right⟩ ← next state
  pure ⟨after, left.then right⟩

private def first : Option (From initState) :=
  append (emitCore providerPayload) fun _ => emit (.instance_ (.instantiate 0 []))

private def connect (before : State) (moduleName : String) (instanceIndex : Nat) : Option (From before) :=
  append (emitCore consumerPayload) fun _ => emit (.instance_ (.instantiate 1 [(moduleName, instanceIndex)]))

private def connected := append first fun state => connect state "env" 0

private def finish (before : State) : Option (From before) :=
  append (emit (.alias (.coreExport 1 "run" .func))) fun _ =>
  append (emit (.funcType { params := [], result := some (.prim .u32) })) fun _ =>
  append (emit (.canon (.lift 0 [] 0))) fun _ =>
  emit (.export_ { name := "run" } ⟨.func, 0⟩)

private def linked := (append connected finish).get (by decide +kernel)

example : (append first fun state => connect state "wrong" 0).isSome = false := by decide +kernel
example : (append first fun state => connect state "env" 1).isSome = false := by decide +kernel

private def erased := (linked.2.map (targets := core3ModuleType?) bodyErase (fun checked => checked)).erase

example : erased = Syntax.Component.map bodyErase linked.2.erase :=
  linked.2.erase_map bodyErase (fun checked => checked)

example : bodyErase providerPayload = provider := providerPayload.2.erase_eq
example : bodyErase consumerPayload = consumer := consumerPayload.2.erase_eq

example : (bodyErase consumerPayload).split = consumerParts :=
  (congrArg Wasm.Module.split consumerPayload.2.erase_eq).trans consumerParts.split_toCore

example : erased.coreModules.map (fun mod => mod.exports.map Wasm.Export.name) = [["get"], ["run"]] :=
  by decide +kernel

example : ValidComponentCore3 .p2 erased (componentTypeOfDefs linked.1.ctx) :=
  checkCore3?_sound ((linked.2.map bodyErase (fun checked => checked)).check_closed (by decide +kernel))

example : ((checkCore3? .p2 erased).toOption.map fun typ => typ.exports.map Prod.fst) = some ["run"] :=
  by decide +kernel

private def linkedClosed := (Closed.lift? .p2 core3Profile core3ModuleType? erased).get (by decide +kernel)

private def exposeRun : Exposure linkedClosed.1 "run"
    (.func { params := [], result := some (.prim .u32) }) :=
  ⟨⟨0, by decide +kernel⟩, by with_unfolding_all rfl⟩

example : ∃ typed : Closed .p2 core3Profile core3ModuleType? linkedClosed.1, typed.erase = erased :=
  ⟨linkedClosed.2.val, linkedClosed.2.property⟩

section Runtime

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Entry
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec
open Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Wasm.Verify.Kernel

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private abbrev WireEngine := Engine.core3 neverFail
private abbrev WireHost := CanonHost WireEngine
private abbrev selected := profile neverFail
private abbrev emb := Core3Adder.emb
private abbrev oracle := Core3Adder.first

private def coreProvider (Host : Type) : Execution.Core.Config Host :=
  (instantiateInit? {} provider []).getD ⟨{}, {}, []⟩

private def coreConsumer (Host : Type) : Execution.Core.Config Host :=
  (instantiateInit? (coreProvider Host).store consumer [.func 0]).getD ⟨{}, {}, []⟩

private theorem providerChecked {Host : Type} :
    runChecked? neverFail 10 ({} : Store Host) (bodyErase providerPayload) [] =
      some (coreProvider Host, true, some (.values [])) := by
  rw [show bodyErase providerPayload = provider from providerPayload.2.erase_eq]
  with_unfolding_all rfl

private theorem consumerChecked {Host : Type} :
    runChecked? neverFail 10 (coreProvider Host).store (bodyErase consumerPayload) [.func 0] =
      some (coreConsumer Host, true, some (.values [])) := by
  rw [show bodyErase consumerPayload = consumer from consumerPayload.2.erase_eq]
  with_unfolding_all rfl

private theorem ready_of_checked {Host : Type} {input : ModuleInput Host} {config : Execution.Core.Config Host}
    (ok : StoreOk input.store)
    (checked : runChecked? neverFail 10 input.store input.module_ input.imports =
      some (config, true, some (.values [])))
    (allocation : instantiate? evalConst? input.store input.module_ input.imports = some config) :
    StoreOk config.store ∧ ReadyAfter selected Det.noHost input ⟨config.store, config.frame.module⟩ := by
  obtain ⟨_, typed, terminal⟩ := CheckedRun.runChecked?_sound ok checked
  obtain ⟨_, ⟨storeOk, _⟩, _⟩ := typed
  exact ⟨storeOk, config, config, (instantiate?_iff (CheckedRun.runChecked?_inv checked).1).mp allocation,
    ⟨.refl, terminal _ rfl⟩, rfl⟩

private def providerInput (Host : Type) : ModuleInput Host := ⟨{}, bodyErase providerPayload, []⟩

private def consumerInput (Host : Type) : ModuleInput Host :=
  ⟨(coreProvider Host).store, bodyErase consumerPayload, [.func 0]⟩

private def ready {Host : Type} (config : Execution.Core.Config Host) : Ready Host :=
  ⟨config.store, config.frame.module⟩

private theorem providerReady {Host : Type} :
    StoreOk (coreProvider Host).store ∧ ReadyAfter selected Det.noHost (providerInput Host) (ready (coreProvider Host)) :=
  ready_of_checked (input := providerInput Host) (by constructor <;> intro item member <;> cases member)
    providerChecked (by with_unfolding_all rfl)

private theorem consumerReady {Host : Type} :
    StoreOk (coreConsumer Host).store ∧ ReadyAfter selected Det.noHost (consumerInput Host) (ready (coreConsumer Host)) :=
  ready_of_checked (input := consumerInput Host) providerReady.1 consumerChecked (by with_unfolding_all rfl)

private def refInstantiation :=
  (emb.instantiateRun oracle 100 linkedClosed.2.val.erase [] (Reference.initConfig ())).get (by decide +kernel)

private def refReady := refInstantiation.1.config

private theorem instantiateReference :
    emb.instantiateRun oracle 100 linkedClosed.2.val.erase [] (Reference.initConfig ()) = some refInstantiation :=
  by with_unfolding_all rfl

private def runExport : FuncId := (refInstantiation.2.2.lookup "run").get (by decide +kernel)

private theorem lookupReference : refInstantiation.2.2.lookup "run" = some runExport :=
  by with_unfolding_all rfl

private theorem coreAddress {Host : Type} : Game.Accept.exportFunc? (coreConsumer Host).frame.module "run" = some 1 :=
  by with_unfolding_all rfl

private def liftAddress? : Option Nat :=
  match refReady.store.funcs[runExport.idx]? with
  | some (.lifted address _ _ _) => some address
  | _ => none

private theorem resolvedWire :
    Game.Accept.exportFunc? (coreProvider WireHost).frame.module "get" = some 0 ∧
    (coreConsumer WireHost).frame.module.funcs = [0, 1] ∧ liftAddress? = some 1 := by
  exact ⟨by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

private theorem referenceReadyStore : refReady.store.core = (coreConsumer WireHost).store :=
  by with_unfolding_all rfl

private def refCall := (emb.callTop oracle 100 ⟨0⟩ runExport [] refReady).get (by decide +kernel)

private theorem callReference : emb.callTop oracle 100 ⟨0⟩ runExport [] refReady = some refCall :=
  by with_unfolding_all rfl

private theorem result_is_42 : Component.callOutcome? ⟨0⟩ refCall = some (.resolved (some [.u32 42])) :=
  by with_unfolding_all rfl

private theorem referenceReturns : Outcome.returns (some [.u32 42]) ∈
    exportBehaviours oracle.prof (Host.ofEmbedder emb) () linkedClosed.2.val.erase [] "run" [] :=
  exportBehaviours_of_run emb oracle () instantiateReference lookupReference callReference result_is_42

private def coreTerminal (Host : Type) : Execution.Core.Config Host :=
  ⟨(coreConsumer Host).store, {}, (Result.values [.i32 42]).toAdmin⟩

private theorem executeRun {Host : Type} :
    Finishes selected Det.noHost (invoke (coreConsumer Host).store 1 []) (coreTerminal Host) (.values [.i32 42]) := by
  have admitted : InvokeOk (coreConsumer Host).store 1 [] := invokeOk?_sound (by with_unfolding_all rfl)
  have ran : runInvoke? neverFail 30 (coreConsumer Host).store 1 [] =
      some (coreTerminal Host, true, some (.values [.i32 42])) := by
    rw [← runInvokeK_eq]
    kernel_rfl
  exact ⟨InvokeRun.runInvoke?_steps_noHost consumerReady.1 admitted ran, rfl⟩

private theorem coreNamedEntry {Host : Type} :
    (rawExport selected Det.noHost [(ScalarType.num (.int .i32)).toC]).initial
      ⟨ready (coreConsumer Host), "run", []⟩ (invoke (coreConsumer Host).store 1 []) := ⟨1, coreAddress, rfl⟩

private theorem coreReturnUnique {Host : Type} {terminal : Execution.Core.Config Host} {result : Result}
    (finished : Finishes selected Det.noHost (invoke (coreConsumer Host).store 1 []) terminal result) :
    terminal = coreTerminal Host ∧ result = .values [.i32 42] := finishes_unique finished executeRun

private theorem referenceReturnStore : refCall.config.store.core = (coreTerminal WireHost).store :=
  by with_unfolding_all rfl

private theorem linkedReferenceWitness :
    Instantiates oracle.prof emb.hr emb.dispatch (Reference.initConfig ()) linkedClosed.2.val.erase []
      refReady refInstantiation.2.1 refInstantiation.2.2 ∧
    refInstantiation.2.2.lookup "run" = some runExport ∧
    refReady.store.core = (ready (coreConsumer WireHost)).store ∧
    Calls oracle.prof emb.hr emb.dispatch refReady ⟨0⟩ runExport [] refCall.config (.resolved (some [.u32 42])) ∧
    refCall.config.store.core = (coreTerminal WireHost).store :=
  ⟨emb.instantiateRun_sound oracle instantiateReference, lookupReference, referenceReadyStore,
    emb.callTop_sound oracle callReference result_is_42, referenceReturnStore⟩

private def gameInstance : ScalarInstance := ⟨[], [⟨[], [.num (.int .i32)]⟩], [1], (coreConsumer Nat).store⟩

private def scalarStore? (store : Store WireHost) : Option (Store Nat) := do
  let funcs ← store.funcs.mapM fun fi => match fi.code with
    | .wasm body => some (⟨fi.type, fi.module, .wasm body⟩ : FuncInst Nat)
    | .host _ => none
  return { store with funcs }

private theorem gameStores : scalarStore? refReady.store.core = some gameInstance.store ∧
    scalarStore? refCall.config.store.core = some (coreTerminal Nat).store :=
  ⟨by rw [referenceReadyStore]; with_unfolding_all rfl,
    by rw [referenceReturnStore]; with_unfolding_all rfl⟩

private def question : gameInstance.F.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

private def answer : gameInstance.F.Ar question := .values ⟨[.i32 42], .cons ⟨42, rfl⟩ .nil⟩

private theorem gameActivation : gameInstance.Activation selected gameInstance.store
    [.inr (.ask question), .inr (.ans question answer)] (coreTerminal Nat).store := by
  obtain ⟨store, thread, run, result⟩ := (ret_iff_core (P := selected) (s := gameInstance.store)
    (t := gameInstance.initThread question) (r := .values [.i32 42])).2
      ⟨coreTerminal Nat, (executeRun (Host := Nat)).1, (executeRun (Host := Nat)).2⟩
  have final := (coreReturnUnique ⟨run.steps, result⟩).1
  have sameStore : store = (coreTerminal Nat).store := by
    cases thread <;> exact congrArg Execution.Core.Config.store final
  rw [← sameStore]
  exact .cons (.call _ _) (.cons (.oret run result (Answer.ofResult?_toResult answer)) (.nil _))

private theorem gameObservation : [.inr (.ask question), .inr (.ans question answer)] ∈
    gameInstance.strategy selected gameInstance.store :=
  gameInstance.append_mem_of gameActivation (gameInstance.mem_strategy_iff.2 ⟨_, .nil _⟩)

open DirectLift
open Silmaril.Proofs.Wasm.Component.Reference (D Store.mapH)
open Silmaril.Wasm.Numerics (Profile)

private def wire : DirectWire := ⟨provider, consumer, "env", "run", "run", [], some .u32⟩

private theorem wireErasure : linkedClosed.2.val.erase = wire.component := by with_unfolding_all rfl

private abbrev ProfileHost (P : Profile) := CanonHost (core3P P)

private noncomputable def preparations (P : Profile) :
    wire.Prepared P (coreConsumer (ProfileHost P)).store 1 where
  providerStore := (coreProvider (ProfileHost P)).store
  providerInst := (coreProvider (ProfileHost P)).frame.module
  consumerInst := (coreConsumer (ProfileHost P)).frame.module
  resolvedImports := [.func 0]
  providerImports := by with_unfolding_all rfl
  provide := by with_unfolding_all rfl
  resolve := by with_unfolding_all rfl
  consume := by with_unfolding_all rfl
  lookup := by with_unfolding_all rfl

private theorem wrongWire (P : Profile) :
    Component.Instantiate.coreImportsFor? (preparations P).providerStore consumer [("wrong", 0)]
      (wire.providerFrame (preparations P).providerInst) = none := by with_unfolding_all rfl

private theorem relationalInstantiation (P : Profile) (prof : ProfileKind) :
    Instantiates prof (refHost P).hr (D P) (initConfig ()) linkedClosed.2.val.erase []
      (wire.ready (coreConsumer (ProfileHost P)).store 1) ⟨0⟩ [("run", ⟨0⟩)] := by
  rw [wireErasure]
  exact (wire.instantiates_iff (preparations P)).2 ⟨rfl, rfl, rfl⟩

private def wireExport : SimpleExport := ⟨"run", ⟨[], [.u32]⟩, 0⟩

private theorem boundary (P : Profile) :
    Boundary gameInstance (P := P) (coreConsumer (ProfileHost P)).store wireExport [] question where
  wellFormed := by
    change gameInstance.WellFormed gameInstance.store
    refine ⟨consumerReady.1, rfl, ?_, ?_⟩
    · rintro ⟨idx, bound⟩
      have zero : idx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
      subst idx
      exact ⟨_, by with_unfolding_all rfl, Expand.iff.2 (by with_unfolding_all rfl)⟩
    · intro addr fi host lookup code
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp lookup
      change addr < 2 at bound
      have which : addr = 0 ∨ addr = 1 := by omega
      rcases which with rfl | rfl
      all_goals
        rw [show gameInstance.store.funcs[_]? = some _ by with_unfolding_all rfl] at lookup
        subst fi
        cases code
  noImports := rfl
  signature := rfl
  arguments := rfl
  typed := rfl
  floatFreeParams := rfl
  floatFreeResults := rfl
  flatParams := by decide +kernel
  oneResult := by decide +kernel
  flatResults := by decide +kernel

private theorem linkedForward :
    ∃ final, Calls oracle.prof (refHost selected).hr (D selected)
      (wire.ready (coreConsumer (ProfileHost selected)).store 1) ⟨7⟩ ⟨0⟩ [] final
      (.resolved (some [.u32 42])) ∧
      (coreTerminal Nat).store = Store.mapH (fun _ => 0) final.store.core := by
  have init := relationalInstantiation selected oracle.prof
  rw [wireErasure] at init
  exact (wire.terminalObservationIff (preparations selected) (boundary selected) rfl init (by rfl)).2
    ⟨coreTerminal Nat, .values [.i32 42], executeRun, ⟨[Flat.i32 42], [.u32 42], rfl, rfl, rfl⟩, rfl⟩

private theorem linkedReadback {final : Component.Machine.Config (core3P selected) Unit} {out : CallOutcome}
    (ran : Calls oracle.prof (refHost selected).hr (D selected)
      (wire.ready (coreConsumer (ProfileHost selected)).store 1) ⟨0⟩ ⟨0⟩ [] final out) :
    out = .resolved (some [.u32 42]) ∧
    Store.mapH (fun _ => 0) final.store.core = (coreTerminal Nat).store := by
  have entry := relationalInstantiation selected oracle.prof
  rw [wireErasure] at entry
  obtain ⟨core, result, ans, finished, _, reports, storeEq, _⟩ := wire.terminalReadbackOfInstantiation
    (out := out) (preparations selected) (boundary selected) rfl entry (by rfl) ran
  obtain ⟨rfl, rfl⟩ := coreReturnUnique finished
  refine ⟨?_, storeEq.symm⟩
  cases out with
  | resolved values =>
    cases values with
    | none => exact False.elim reports
    | some values =>
      obtain ⟨flats, lifted, hflats, hlifted, rfl⟩ := reports
      have : flats = [Flat.i32 42] := (Option.some.inj hflats).symm
      subst flats
      have : lifted = [.u32 42] := (Option.some.inj hlifted).symm
      subst lifted
      rfl
  | trap =>
    obtain ⟨flats, hflats, rejects⟩ := reports
    have : flats = [Flat.i32 42] := (Option.some.inj hflats).symm
    subst flats
    cases rejects
  | deadlock => exact False.elim reports

open Silmaril.Wasm.Institution.DirectLiftTerminal

private noncomputable def terminalModel : ComponentModel selected wireExport where
  wire := wire
  shared := (coreConsumer (ProfileHost selected)).store
  entry := gameInstance
  question := question
  args := []
  profile := oracle.prof
  call := 7
  prepared := preparations selected
  boundary := boundary selected
  signature := rfl
  named := rfl

private def returns42 : Sentence := fun out store =>
  out = .resolved (some [.u32 42]) ∧ store = (coreTerminal Nat).store

open CategoryTheory in
example : (institution selected wireExport).Sat (1 : Fin 2) ⟨terminalModel⟩ returns42 := by
  have arrow : (0 : Fin 2) ≤ 1 := by decide
  apply ((institution selected wireExport).satisfaction (homOfLE arrow) ⟨terminalModel⟩ returns42).2
  exact ⟨.resolved (some [.u32 42]), (coreTerminal Nat).store,
    ⟨coreTerminal Nat, .values [.i32 42], executeRun, ⟨[Flat.i32 42], [.u32 42], rfl, rfl, rfl⟩, rfl⟩,
    rfl, rfl⟩

#print axioms consumerReady
#print axioms coreNamedEntry
#print axioms coreReturnUnique
#print axioms linkedReferenceWitness
#print axioms referenceReturns
#print axioms gameStores
#print axioms gameActivation
#print axioms gameObservation
#print axioms DirectWire.instantiates_iff
#print axioms DirectWire.terminalReadbackOfInstantiation
#print axioms Reach.of_steps
#print axioms DirectWire.terminalForwardOfInstantiation
#print axioms DirectWire.terminalObservationIff
#print axioms relationalInstantiation
#print axioms wrongWire
#print axioms linkedForward
#print axioms linkedReadback
#print axioms ComponentModel.reaches_iff
#print axioms institution

end Runtime

#print axioms Program.erase_then
#print axioms Program.erase_map
#print axioms Program.map_then
#print axioms Program.sound
#print axioms checkCore3?_sound
