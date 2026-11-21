module

import Silmaril.Wasm.Execution.Core.Entry.Program.Thms
import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
import Silmaril.Wasm.Execution.Core.Intrinsic.Pure.Thms
import Silmaril.Wasm.Execution.Core.Soundness
import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Wasm.Validation.Intrinsic.Thms

open Silmaril.Semantics.Operational Silmaril.Wasm Silmaril.Wasm.Validation
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Entry Silmaril.Wasm.Execution.Core.Intrinsic
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Wasm.Game Silmaril.Wasm.Component.Reference Silmaril.Wasm.Abstract.InstSession

private def body : Code [.i32, .i32] [] [.i32] :=
  .seq (.localGet .here (by decide)) (.seq (.localGet (.there .here) (by decide))
    (.seq (.intBin (.div .unsigned)) .done))

private def sourceModule : Silmaril.Wasm.Module where
  types := [⟨[⟨true, [], .func ⟨[.i32, .i32], [.i32]⟩⟩]⟩]
  funcs := [⟨⟨0⟩, [], body.erase⟩]
  exports := [⟨"divide", .func ⟨0⟩⟩]

private def interface : CModuleType := (validate? sourceModule).getD ⟨[], []⟩
private theorem validates : validate? sourceModule = some interface := rfl
private theorem moduleOk : ModuleOk sourceModule interface := validate?_sound validates
private def initialStore : Store Nat := {}
private theorem initialStoreOk : StoreOk initialStore := by constructor <;> simp [initialStore]
private abbrev selected := profile neverFail
private def host : HostSemantics Nat := fun _ _ _ result => result = .diverged
private theorem hostOk : HostOk host := by
  intro store entry id args params results _ _ _ _ _
  exact ⟨⟨.diverged, rfl⟩, fun outcome equal => by cases equal; trivial⟩

private def input : ModuleInput Nat := ⟨initialStore, sourceModule, []⟩
private def checkedInput : { raw : ModuleInput Nat // raw.CheckedAt interface } :=
  ⟨input, moduleOk, initialStoreOk, .nil⟩
private def allocated : Config Nat := (instantiate? evalConst? initialStore sourceModule []).getD ⟨{}, {}, []⟩
private theorem initializes : (rawModule selected host).initial input allocated :=
  (instantiate?_iff ⟨interface.exports, [], moduleOk, .nil⟩).mp rfl

private def ready : Ready Nat := ⟨allocated.store, allocated.frame.module⟩

example : ReadyAfter selected host input ready := ⟨allocated, allocated, initializes, ⟨.refl, rfl⟩, rfl⟩

example : (checkedModule selected host interface).May checkedInput (.returned (.ok [])) :=
  ⟨allocated, initializes, allocated, .refl, Instantiate.ok hostOk initialStoreOk initializes, .values [], rfl, rfl⟩

example : ∃ typed : TypedModuleInput Nat interface, typed.erase = input ∧
    (typedModule selected host interface).Equivalent typed (checkedModule selected host interface) checkedInput := by
  obtain ⟨typed, erases⟩ := checkedModule_lift checkedInput.property
  change typed.erase = input at erases
  refine ⟨typed, erases, ?_⟩
  change (typedModule selected host interface).Equivalent typed (rawModule selected host) input
  rw [← erases]
  exact typedModule_equivalent_raw hostOk typed

example : ∃ typed : TypedModuleInput Nat interface, typed.erase = input ∧
    (typedModule selected host interface).May typed (.returned (.ok [])) := by
  obtain ⟨module_, erased⟩ := Validation.Intrinsic.Module.lift_erase moduleOk
  let typed : TypedModuleInput Nat interface := ⟨initialStore, module_, [], initialStoreOk, .nil⟩
  have erasedInput : typed.erase = input := congrArg (fun m => ModuleInput.mk initialStore m []) erased
  have init : (rawModule selected host).initial typed.erase allocated := erasedInput.symm ▸ initializes
  obtain ⟨state, typedInit, erasesTo⟩ := (typedModule_lift hostOk).mp init
  exact ⟨typed, erasedInput, state, typedInit,
    (typedModule_may hostOk state _).mpr ⟨state.val, .values [], ⟨.refl, by rw [erasesTo]; rfl⟩, rfl⟩⟩

private def args (divisor : BitVec 32) : Values [.i32, .i32] := .cons 84 (.cons divisor .nil)

example : (rawExport selected noHost [.i32]).NoEntry ⟨ready, "missing", (args 7).erase⟩ := by
  rintro ⟨_, address, found, _⟩
  change none = some address at found
  cases found

private def type : DefType := (allocTypes sourceModule.types)[0]'(by decide +kernel)
private def frameContext : Context := { types := [type], funcs := [type] }
private def function : FuncInst Nat := ⟨type, ready.instance_, .wasm ⟨⟨0⟩, [], body.erase⟩⟩
private theorem readyStoreOk : StoreOk ready.store := (Instantiate.ok hostOk initialStoreOk initializes).choose_spec.1.1
private theorem readyModuleOk : ModuleInstOk ready.store ready.instance_ frameContext :=
  ModuleInstOk.mk (k := 0) (by
    change ∀ item ∈ [type], TyOk {} item
    simp only [List.mem_singleton, forall_eq]
    exact TyOk.check_sound (by decide +kernel)) .nil .nil
    (.cons (ExternAddrOk.func (fi := function) rfl) .nil) .nil .nil (by simp [show ready.instance_.datas = [] from rfl]) .nil
    (by
      change ∀ item ∈ [⟨"divide", .func 0⟩], ExportInstOk ready.store item
      simp only [List.mem_singleton, forall_eq]
      exact ⟨_, ExternAddrOk.func (fi := function) rfl⟩) (by decide +kernel) (by decide +kernel) (by decide)

private def world : World Nat frameContext := ⟨ready.store, ready.instance_, readyStoreOk, readyModuleOk⟩
private def divide : DirectCall world [.i32, .i32] [.i32] :=
  ⟨⟨0⟩, 0, function, [], ⟨0⟩, body, frameContext, readyModuleOk, rfl, rfl, Expand.iff.mpr rfl, rfl⟩
private def named : ResolvedExport divide := ⟨"divide", rfl⟩

example (divisor : BitVec 32) : named.opSem.Equivalent (args divisor) (rawExport selected noHost [.i32])
    (named.rawInput (args divisor)) := named.equivalent (oracle := neverFail) _

private theorem evaluated (divisor : BitVec 32) :
    divide.runFor (args divisor) (Pure.budget body) = some (Pure.denotes (declared := []) body (args divisor)) :=
  Pure.run_eval ⟨(args divisor).append (Values.zeros divide.declaredLocals)⟩ divide.body .nil

private theorem rawDivision (divisor : BitVec 32) :
    (rawExport selected noHost [.i32]).May (named.rawInput (args divisor))
      (observeResult (invokeResult (Pure.denotes (declared := []) body (args divisor)))) :=
  ⟨_, (named.raw_initial_iff (args divisor) _ (types := [.i32])).mpr rfl,
    (invoke_may_iff divide (args divisor) (evaluated divisor) _).mpr rfl⟩

example : (rawExport selected noHost [.i32]).May (named.rawInput (args 7)) (.returned (.ok [.i32 12])) :=
  rawDivision 7

example : named.opSem.May (args 0) .trap :=
  (named.equivalent (oracle := neverFail) (args 0)).2.2 (rawDivision 0)

example : (rawExport selected noHost [.i32]).semantics.SafeAt (invoke ready.store 0 (args 0).erase) :=
  invoke_noUB divide (args 0)

example : divide.runFor (args 7) 2 = none := rfl
example : divide.runFor (args 7) 3 = some (some (.cons 12 .nil)) := rfl
example : divide.runFor (args 0) 3 = some none := rfl

private def registered : NumInstance :=
  ⟨⟨[], [⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩],
    exportFuncAddrs ready.instance_, ready.store⟩,
    [], [("divide", ⟨[.int .i32, .int .i32], [.int .i32]⟩)], rfl, rfl⟩

private theorem registeredOk : registered.inst.Ok := by
  refine ⟨readyStoreOk, rfl, ?_, ?_⟩
  · intro index
    have first : index = ⟨0, by decide⟩ := Fin.eq_zero (show Fin 1 from index)
    subst index
    exact ⟨function, rfl, Expand.iff.mpr rfl⟩
  · intro address fn external found hostCode
    change [function][address]? = some fn at found
    cases address with
    | zero =>
      have isFunction : function = fn := Option.some.inj found
      subst fn
      cases hostCode
    | succ address => simp at found

private def question (divisor : BitVec 32) : registered.inst.F.Op :=
  ⟨⟨0, by decide⟩, ⟨(args divisor).erase, .cons ⟨84, rfl⟩ (.cons ⟨divisor, rfl⟩ .nil)⟩⟩

example : (scalarInstance neverFail registered.inst [.i32]).initial (ready.store, question 7)
    (invoke ready.store 0 (args 7).erase) := rfl

example : (typedInstance registered.inst divide registeredOk).May (question 7) (.returned (.ok [.i32 12])) :=
  ⟨_, ⟨args 7, rfl, rfl, rfl⟩,
    (typedInstance_may_iff divide registeredOk (args 7) (question 7) rfl rfl (evaluated 7) (oracle := neverFail) _).mpr
      ((invoke_may_iff divide (args 7) (evaluated 7) _).mpr rfl)⟩

example : ([], .ret (.inr ()) ready.store) ∈ instFinS registered.inst selected ready.store (question 0) :=
  (session_finishes_iff divide (args 0) (question := question 0) rfl rfl rfl
    (evaluated 0) (typedAnswer := .trap) rfl [] _).mpr rfl

private def answer : registered.inst.F.Ar (question 7) := .values ⟨[.i32 12], .cons ⟨12, rfl⟩ .nil⟩

example : ([], .ret (sAns (question 7) answer) ready.store) ∈
    instFinS registered.inst selected ready.store (question 7) := by
  have readback : Answer.ofResult? (registered.inst.exports.get (question 7).1)
      (invokeResult (some (.cons (kind := .i32) 12 .nil))) = some answer :=
    Answer.ofResult?_toResult answer
  exact (session_finishes_iff divide (args 7) (question := question 7) rfl rfl rfl
    (evaluated 7) readback [] _).mpr rfl

#print axioms typedModule_lift
#print axioms typedModule_may
#print axioms invoke_noUB
#print axioms invoke_finishes_iff
#print axioms ResolvedExport.may_iff
#print axioms typedModule_equivalent_raw
#print axioms typedModule_equivalent_checked
#print axioms ResolvedExport.equivalent
#print axioms ResolvedExport.equivalent_of_runFor
#print axioms typedInstance_may_iff
#print axioms session_finishes_iff
