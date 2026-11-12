module

public import Silmaril.Wasm.SpecTec.Sim.Round3.Defs

/-!
# Round 3 integration: the backward conjunct of the target is false

`Step/memory.grow-fail` (rule 27) has no premise: SpecTec lets `(CONST at n) (MEMORY.GROW x)`
step to `CONST at (-1)` for every `x`, including an index the frame's module does not list. Core's
`MemoryStep.growFail` needs `s.mem? f x`. So on the empty store, with the empty module instance,

  `growConfig := [i32.const 0, memory.grow 0]`

is `Typed` in every `simEnv B` (`typed_growConfig`: `Typed` is SpecTec's syntactic typing and does
not check that `0` is a memory index of the module), SpecTec steps (`sstep_growConfig`, for every
`B`), and Core is stuck (`step_stuck`). Hence:

* `not_wholeStepBounded : ¬ Integrate.Task.wholeStepBounded`, at the empty host type, the empty
  host and every profile;
* `not_wholeStepUpTo : ¬ Bwd.Task.wholeStepUpTo` and `not_wholeStep : ¬ Task.wholeStep` (each
  implies the target).

Track bwd-pure-step argued this (with `table.grow-fail`); this file makes it formal. A satisfiable
restatement must constrain the source configuration of the backward conjunct by Core validity
(e.g. `ConfigOk`, or index validity against the frame's module).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round3

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- The administrative instructions of the counterexample: integer constants and
`memory.grow`. -/
def StuckOk : Admin → Bool
  | .plain (.intConst ..) => true
  | .plain (.memoryGrow _) => true
  | _ => false

set_option linter.unusedSimpArgs false in
/-- **Core is stuck** on code made of integer constants and `memory.grow` when the frame's module
lists no memory. -/
theorem step_stuck {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hm : c.frame.module.mems = []) (hall : c.code.all StuckOk = true) :
    False := by
  induction h with
  | parametric h => cases h <;> simp [List.all_append, StuckOk] at hall
  | numeric h => cases h <;> simp [List.all_append, StuckOk] at hall
  | vector h => cases h <;> simp [List.all_append, StuckOk] at hall
  | «variable» h => cases h <;> simp [List.all_append, StuckOk] at hall
  | table h => cases h <;> simp [List.all_append, StuckOk] at hall
  | memory h => cases h <;> simp_all [List.all_append, StuckOk, Store.mem?]
  | reference h => cases h <;> simp [List.all_append, StuckOk] at hall
  | aggregate h => cases h <;> simp [List.all_append, StuckOk] at hall
  | ctxtInstrs _ _ ih =>
    simp only [List.all_append, Bool.and_eq_true] at hall
    exact ih hm hall.1.2
  | _ => simp [List.all_append, StuckOk] at hall

/-- The encoding of the empty host type. -/
def hnE : Empty → String := fun e => e.elim

/-- Memory index `0`. -/
def mem0 : MemIdx := ⟨0⟩

/-- `i32.const 0; memory.grow 0` on the empty store, with the empty module instance. -/
def growConfig : Config Empty :=
  ⟨{}, ⟨[], {}⟩, vals [.num ⟨.int .i32, 0⟩] ++ [.plain (.memoryGrow mem0)]⟩

/-- What SpecTec steps it to: `i32.const -1`. -/
def grownConfig : Config Empty :=
  ⟨{}, ⟨[], {}⟩, [aconst .i32 (BitVec.allOnes _)]⟩

set_option maxRecDepth 100000 in
theorem findTyp_memidx {B : Builtins} :
    (simEnv B).findTyp? "memidx" = some ([], [.instD [] [] (.aliasT (.varT "idx" []))]) := rfl

/-- `memory.grow 0` is a typed `instr`. -/
theorem typedV_memoryGrow (B : Builtins) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.memoryGrow mem0)) :=
  FwdMem.typedV_instrCase rfl rfl
    (Typing.typedV_alias findTyp_memidx (Typing.typedV_idx _) _ ⟨rfl, rfl, rfl⟩)

/-- **The counterexample is `Typed`**, in every `simEnv B`. -/
theorem typed_growConfig (B : Builtins) : Typed (simEnv B) hnE growConfig := by
  have T := Typing.typingFacts_simEnv B hnE
  obtain ⟨hst, hv⟩ := (T.config _).1 (Typing.typed_vals (B := B) hnE [] [.num ⟨.int .i32, 0⟩])
  refine (T.config _).2 ⟨hst, ?_⟩
  show TypedV (simEnv B) instrsT (.list (adminsToV (vals [.num ⟨.int .i32, 0⟩] ++
    [.plain (.memoryGrow mem0)])))
  rw [adminsToV_append]
  exact (T.append _ _).2 ⟨hv, typedV_list_single.2 (typedV_memoryGrow B)⟩

/-- **SpecTec steps from it**, in every `simEnv B` (`Step/memory.grow-fail`). -/
theorem sstep_growConfig (B : Builtins) :
    SStep (simEnv B) (configV hnE growConfig) (configV hnE grownConfig) := by
  have T := Typing.typingFacts_simEnv B hnE
  have hc := typed_growConfig B
  show SStep _ (cfgV _ [adminToV (aconst .i32 0), adminToV (.plain (.memoryGrow mem0))])
    (cfgV _ [adminToV (aconst .i32 (BitVec.allOnes _))])
  rw [State.adminToV_aconst, State.adminToV_aconst]
  exact State.sstep_memoryGrowFail (State.growDefs_simEnv B) (Typing.stateTyping_simEnv B)
    (hasStepRules_simEnv B).memoryGrowFail (State.typedV_state T hc) mem0.value.isLt

/-- **Core is stuck on it.** -/
theorem not_step_growConfig {P : Profile} {host : HostSemantics Empty} {c' : Config Empty} :
    ¬ Step P host growConfig c' := fun h =>
  step_stuck h rfl rfl

/-- **The target is false.** At the empty host type, the empty host and any profile, the backward
conjunct fails for every `B` at `growConfig`. -/
theorem not_wholeStepBounded : ¬ Integrate.Task.wholeStepBounded := fun h => by
  obtain ⟨B, -, hb⟩ := h Empty hnE (fun e => e.elim) Integrate.emptyHost
    Integrate.hostFinite_emptyHost false {}
  obtain ⟨c', -, -, -, hs⟩ := hb growConfig _ (typed_growConfig B) (sstep_growConfig B)
  exact not_step_growConfig hs

/-- The backward track's goal is false too (it implies the target). -/
theorem not_wholeStepUpTo : ¬ Bwd.Task.wholeStepUpTo := fun h =>
  not_wholeStepBounded (Integrate.Task.wholeStepBounded_of_upTo h)

/-- The round-0 goal is false too (it implies the backward track's). -/
theorem not_wholeStep : ¬ Task.wholeStep := fun h => not_wholeStepUpTo (Bwd.wholeStep_upTo h)

end Silmaril.Wasm.SpecTec.Sim.Round3
