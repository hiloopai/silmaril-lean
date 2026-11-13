module

public import Silmaril.Compiler.Native.Optimize.Validation.Effects.Load.Defs
@[expose] public section
namespace Silmaril.Compiler.Native.Optimize.Validation.Effects
open Silmaril.Machine
open Roots
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Actual successful source loading installs the actual memory word at the
real next effect index, then interns that load node and writes its destination.
No total input frame, invented load interpretation or candidate execution. -/
theorem source_load (state : State) (frame : Lir.Frame Nat) (memory : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (loads : LoadsScoped state.nodes state.effects.size)
    (width : Lir.Width) (ext : Lir.Ext) (dest base offset : Nat) (address word : Lir.Word)
    (baseRead : frame.get base = some address)
    (loaded : memory.load width ext (address.toNat + offset) = some word) :
    ∃ newMeaning,
      LoadResult state ((evalOp (.load width ext dest base offset)).run state).2
        (frame.set dest word) meaning newMeaning ∧
      ((evalOp (.load width ext dest base offset)).run state).2.effects =
        state.effects.push (.load width ext ((readReg base).run state).1 offset) ∧
      newMeaning.load state.effects.size = some word ∧
      runEffects newMeaning [.load width ext ((readReg base).run state).1 offset] memory =
        some ([some word], memory) := by
  let read := (readReg base).run state
  let event : Effect := .load width ext read.1 offset
  let recorded := (effect event).run read.2
  obtain ⟨readMeaning, actualRead, readTotal⟩ := Total.readReg_sound state frame meaning rooted total base address baseRead
  let withLoad := setLoad readMeaning read.2.effects.size word
  have readLoads : LoadsScoped read.2.nodes read.2.effects.size := by
    rw [actualRead.effects]
    exact readReg_loadsScoped state base state.effects.size loads
  have recordedActual : recorded = (read.2.effects.size, { read.2 with effects := read.2.effects.push event }) := rfl
  have loadedRooted : Rooted recorded.2 frame withLoad := by
    rw [recordedActual]
    have prior := setLoad_rooted read.2 frame readMeaning actualRead.rooted readLoads word
    exact ⟨prior.wellScoped, prior.coherent, prior.regsBounded, prior.slotsBounded, prior.regs, prior.slots⟩
  have loadedTotal : Total.TotalNodes recorded.2.nodes withLoad :=
    prefix_total read.2.nodes readMeaning withLoad read.2.effects.size readTotal (setLoad_prefix readMeaning _ _ word)
  have oldLoads : LoadsScoped recorded.2.nodes recorded.2.effects.size := by
    rw [recordedActual]
    exact loadsScoped_mono readLoads (by simp)
  have eventBound : recorded.1 < recorded.2.effects.size := by rw [recordedActual]; simp
  have computed : (Expr.load recorded.1).eval withLoad = some word := by
    change withLoad.load recorded.1 = some word
    rw [recordedActual]
    exact setLoad_current readMeaning read.2.effects.size word
  obtain ⟨newMeaning, actualIntern, finalTotal⟩ := Total.intern_sound recorded.2 frame withLoad loadedRooted loadedTotal
    (.load recorded.1) trivial word computed
  have actual : (evalOp (.load width ext dest base offset)).run state =
      (writeReg dest ((intern (.load recorded.1)).run recorded.2).1).run
        ((intern (.load recorded.1)).run recorded.2).2 := rfl
  have recordedNodes : recorded.2.nodes = read.2.nodes := rfl
  have recordedEvents : recorded.2.effects.size = read.2.effects.size + 1 := by rw [recordedActual]; simp
  have initialExtension : PrefixExtends state.nodes.size state.effects.size meaning withLoad :=
    (prefix_of_extends actualRead.extension state.effects.size).trans
      (setLoad_prefix readMeaning read.2.nodes.size read.2.effects.size word) actualRead.grows
      (by rw [actualRead.effects])
  have finalExtension : PrefixExtends state.nodes.size state.effects.size meaning newMeaning :=
    initialExtension.trans (prefix_of_extends actualIntern.extension recorded.2.effects.size) actualRead.grows
      (by rw [recordedEvents, actualRead.effects]; omega)
  have baseBound : read.1 < recorded.2.nodes.size := actualRead.bounded
  have baseSelected : newMeaning.value read.1 = some address :=
    (actualIntern.extension.values read.1 baseBound).trans actualRead.selected
  have internLoads := intern_loadsScoped recorded.2 (.load recorded.1) recorded.2.effects.size oldLoads eventBound
  refine ⟨newMeaning, ?_, ?_, ?_, ?_⟩
  · rw [actual]
    refine ⟨writeReg_rooted _ frame newMeaning actualIntern.rooted dest _ word actualIntern.bounded actualIntern.selected,
      finalTotal, ?_,
      finalExtension, actualRead.grows.trans actualIntern.grows⟩
    change LoadsScoped ((intern (.load recorded.1)).run recorded.2).2.nodes
      ((intern (.load recorded.1)).run recorded.2).2.effects.size
    rw [actualIntern.effects]
    exact internLoads
  · rw [actual]
    change ((intern (.load recorded.1)).run recorded.2).2.effects = _
    rw [actualIntern.effects]
    change read.2.effects.push event = _
    rw [actualRead.effects]
  · rw [← actualRead.effects]
    exact (congrFun actualIntern.extension.load read.2.effects.size).trans
      (setLoad_current readMeaning read.2.effects.size word)
  · change (([event].mapM (concreteEffect newMeaning)).bind fun events => runEvents events memory) = _
    have concrete : concreteEffect newMeaning event = some (.load width ext (address.toNat + offset)) := by
      simp only [event, concreteEffect, baseSelected, Option.map_some]
    simp only [List.mapM_cons, List.mapM_nil, concrete]
    apply runEvents_singleton
    simp only [Event.exec, loaded, Option.map_some]

/-- Inversion of actual Lir.Op.exec supplies every operand and memory result
required by source_load; those are not extra checker assumptions. -/
theorem source_load_exec (state : State) (frame final : Lir.Frame Nat) (memory finalMemory : Lir.Memory)
    (meaning : Interpretation) (rooted : Rooted state frame meaning)
    (total : Total.TotalNodes state.nodes meaning) (loads : LoadsScoped state.nodes state.effects.size)
    (width : Lir.Width) (ext : Lir.Ext) (dest base offset : Nat)
    (executed : (Lir.Op.load width ext dest base offset).exec frame memory = some (final, finalMemory)) :
    finalMemory = memory ∧ ∃ newMeaning,
      LoadResult state ((evalOp (.load width ext dest base offset)).run state).2 final meaning newMeaning ∧
      runEffects newMeaning [.load width ext ((readReg base).run state).1 offset] memory =
        some ([final.get dest], finalMemory) := by
  obtain ⟨address, read, word, loaded, output⟩ :
      ∃ address, frame.get base = some address ∧ ∃ word,
        memory.load width ext (address.toNat + offset) = some word ∧
        (frame.set dest word = final ∧ memory = finalMemory) := by
    simpa only [Lir.Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] using executed
  obtain ⟨newMeaning, actual, events, currentLoad, replay⟩ := source_load state frame memory meaning rooted total loads
    width ext dest base offset address word read loaded
  refine ⟨output.2.symm, newMeaning, output.1 ▸ actual, ?_⟩
  rw [← output.1, ← output.2]
  simpa only [Lir.Frame.get_set, ↓reduceIte] using replay

end Silmaril.Compiler.Native.Optimize.Validation.Effects
