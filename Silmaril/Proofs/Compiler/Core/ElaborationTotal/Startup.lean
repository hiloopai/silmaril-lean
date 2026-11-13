module

public import Silmaril.Cerberus.Core.Forced.Thms
public import Silmaril.Compiler.Core.Source.StartupReach.Defs

/-! The no-parameter startup proof follows the imported StartupReach equations,
strengthening each actual next/memory/update request to a forced transition.
The concrete errno allocation/store facts are reused through their header. -/

@[expose] public section
namespace Silmaril.Compiler.Core.ElaborationTotal
open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.StartupReach
open Mem.Concrete (Tags Allocation updateLastAllocation readonlyKind)
open Silmaril.Cerberus.Core

theorem startup_errno_forced (file : Program) (labels : Labels) (control : Control)
    (memory : Mem.Concrete.State) (last : memory.lastAddress = 281474976710655)
    (dead : memory.dead = []) :
    ∃ finish accesses, finish.stdout = memory.stdout ∧
      Forced.Reaches file labels ⟨.startup control, [], memory⟩
        ⟨control, [.annotations accesses], finish⟩ := by
  obtain ⟨bytes, pointers, allocated⟩ := alloc_errno ⟨file.tagDefs, memory.enumTypes⟩ memory last
  let allocation : Allocation := {base := errnoAddr, size := 4, objectType := some intTy}
  let first : Mem.Concrete.State := updateLastAllocation
    {memory with
      bytes := bytes
      pointerBytes := pointers
      nextId := memory.nextId + 1
      lastAddress := errnoAddr
      allocations := memory.allocations.insert memory.nextId allocation
      lastUsed := some memory.nextId}
    fun allocation => {allocation with readonlyKind := readonlyKind (.other "errno")}
  have lookup : first.allocations.lookup memory.nextId = some allocation := by
    simp [first, updateLastAllocation, allocation, readonlyKind]
  have live : memory.nextId ∉ first.dead := by
    simp [first, updateLastAllocation, allocation, dead]
  obtain ⟨second, stored, stdout⟩ := store_errno ∅ first memory.nextId lookup live
  refine ⟨{second with currentLocation := .other "Driver.drive"},
    [⟨none, [], true, errnoAddr, 4⟩], ?_, ?_⟩
  · simp [stdout, first, updateLastAllocation, allocation]
  refine (Forced.memory (name := "Create") (after := first)
    (control := .value (.object (.pointer (.allocated memory.nextId errnoAddr))))
    (frames := [.startupStore control]) (by intro outcome; simp) ?_).trans ?_
  · simp only [request, requestAux, awaitsScheduling, memoryRequest]
    simp only [show Ctype.mk [] (.basic (.integer (.signed .int))) = intTy from rfl,
      integer, allocated]
    simp [bind, Except.bind, pure, Except.pure, first, allocation]
  refine (Forced.memory (name := "Store") (after := second) (control := .value .unit)
    (frames := [.annotations [⟨none, [], true, errnoAddr, 4⟩], .startupEnter control])
    (by intro outcome; simp) ?_).trans ?_
  · simp only [request, requestAux, awaitsScheduling, memoryRequest]
    simp only [show Ctype.mk [] (.basic (.integer (.signed .int))) = intTy from rfl,
      toMemory, objectMemory, Mem.Concrete.unatomic, intType, access_errno ∅ first memory.nextId lookup live]
    simp only [intTy] at stored ⊢
    simp [stored, bind, Except.bind, pure, Except.pure]
  apply Forced.update (by intro outcome; simp)
  simp [request, requestAux, awaitsScheduling]

theorem enter_main_forced (file : Program) (labels : Labels) (arguments : List String)
    (environment : Env) (memory : Mem.Concrete.State) {symbol : Sym} {location : Loc}
    {marker : Option Nat} {type : BaseType} {body : EE}
    (main : file.main = some symbol)
    (declaration : file.funs.lookup symbol = some (.procedure location marker type [] body)) :
    Forced.Reaches file labels ⟨.globals [] arguments environment, [], memory⟩
      ⟨.startup (.effectExpr body environment), [], memory⟩ := by
  refine (Forced.next (c' := .enterMain arguments environment) (k' := [])
    (by intro outcome; simp) ?_).trans ?_
  · simp [request, requestAux, awaitsScheduling]
  apply Forced.next (by intro outcome; simp)
  simp [request, requestAux, awaitsScheduling, main, declaration]

theorem initial_forced_body (file : Program) (enums : Map Sym IntegerType) (arguments : List String)
    {symbol : Sym} {location : Loc} {marker : Option Nat} {type : BaseType} {body : EE}
    (noDefinitions : ∀ entry ∈ file.globs, ∀ base expression, entry.2 ≠ .definition base expression)
    (main : file.main = some symbol)
    (declaration : file.funs.lookup symbol = some (.procedure location marker type [] body)) :
    ∃ start labels memory accesses, initial file enums arguments = .ok (start, labels) ∧
      memory.stdout = "" ∧
      Forced.Reaches file labels start ⟨.effectExpr body ∅, [.annotations accesses], memory⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  obtain ⟨memory, accesses, stdout, started⟩ := startup_errno_forced file labels (.effectExpr body ∅)
    ({enumTypes := enums} : Mem.Concrete.State) rfl rfl
  refine ⟨_, labels, memory, accesses, ?_, by simpa using stdout,
    (enter_main_forced file labels arguments ∅ _ main declaration).trans started⟩
  simp only [initial]
  rw [List.filterMap_eq_nil_iff.mpr]
  · simp [main, declaration, labels]
  · rintro ⟨symbol, _ | _⟩ member
    · exact absurd rfl (noDefinitions _ member _ _)
    · rfl

end Silmaril.Compiler.Core.ElaborationTotal
