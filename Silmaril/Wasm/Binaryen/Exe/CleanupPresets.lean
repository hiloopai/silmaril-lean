module

public import Silmaril.Wasm.Binaryen.Exe.SelectedCleanup

@[expose] public section

/-! # Inspectable restricted Binaryen optimization-level schedules

Source: Binaryen version_133, commit
`fba5005a132d85d578be5bd010e0487ed8e2ce3e`,
`src/passes/pass.cpp` (`addDefault*Optimization*Passes`) and
`src/tools/optimization-options.h` (level settings and ordered requests).

These schedules follow the feature-neutral/no-DWARF default skeleton. GC,
multivalue, string and low-memory-dependent additions are not selected here.
Missing upstream slots are recorded rather than silently identified with a
local pass. Available slots use existing guarded, restricted implementations;
variant substitutions are named explicitly. This is not upstream -O parity.
The expanded list is certified by `SelectedCleanupSound` at every same profile.
-/

namespace Silmaril.Wasm.Binaryen.Exe

inductive CleanupPreset where
  | o0 | o1 | o2 | o3 | o4 | os | oz
  deriving DecidableEq, Repr

def CleanupPreset.name : CleanupPreset → String
  | .o0 => "-O0"
  | .o1 => "-O1"
  | .o2 => "-O2"
  | .o3 => "-O3"
  | .o4 => "-O4"
  | .os => "-Os"
  | .oz => "-Oz"

def CleanupPreset.levels : CleanupPreset → Nat × Nat
  | .o0 => (0, 0)
  | .o1 => (1, 0)
  | .o2 => (2, 0)
  | .o3 => (3, 0)
  | .o4 => (4, 0)
  | .os => (2, 1)
  | .oz => (2, 2)

/-- One upstream slot and its actual local expansion. An empty expansion is an
explicit coverage gap, not a claim to implement the upstream pass. -/
structure PresetSlot where
  upstream : String
  stages : List CleanupStage
  note : String
  deriving Repr

def PresetSlot.omitted (name : String) : PresetSlot :=
  ⟨name, [], "not implemented in this certified preset"⟩

def PresetSlot.restricted (name : String) (stage : FunctionStageId) : PresetSlot :=
  ⟨name, [.function stage], "existing guarded restricted implementation"⟩

def PresetSlot.substituted (name : String) (stage : FunctionStageId) (note : String) : PresetSlot :=
  ⟨name, [.function stage], note⟩

def PresetSlot.rume : PresetSlot :=
  ⟨"remove-unused-module-elements", [.rume], "existing guarded restricted implementation"⟩

/-- Retain the upstream optimizing slot while naming its restricted local run. -/
def PresetSlot.inlining : PresetSlot :=
  ⟨"inlining-optimizing", [.inlining],
    "guarded small/leaf-callee inlining only; upstream optimizing subpipeline is not implemented"⟩

/-- Feature-neutral default order, retaining repeated upstream slots. -/
def CleanupPreset.schedule (preset : CleanupPreset) : List PresetSlot := Id.run do
  if preset == .o0 then return []
  let (opt, shrink) := preset.levels
  let precompute := if opt >= 3 || shrink >= 2 then
      PresetSlot.substituted "precompute-propagate" .precompute
        "restricted precompute only; upstream propagation is not implemented"
    else PresetSlot.restricted "precompute" .precompute
  let globals := if opt >= 2 || shrink >= 2 then
      PresetSlot.substituted "simplify-globals-optimizing" .simplifyGlobals
        "restricted simplify-globals only; optimizing subpipeline is not implemented"
    else PresetSlot.restricted "simplify-globals" .simplifyGlobals
  let mut slots := [PresetSlot.omitted "duplicate-function-elimination"]
  if opt >= 2 then slots := slots ++ [PresetSlot.rume]
  slots := slots ++ [PresetSlot.omitted "memory-packing"]
  if opt >= 2 then slots := slots ++ [PresetSlot.omitted "once-reduction"]
  if opt >= 3 || shrink >= 1 then slots := slots ++ [PresetSlot.omitted "ssa-nomerge"]
  if opt >= 4 then
    slots := slots ++ [PresetSlot.omitted "flatten", PresetSlot.omitted "simplify-locals-notee-nostructure",
      PresetSlot.omitted "local-cse"]
  slots := slots ++ [PresetSlot.restricted "dce" .dce, PresetSlot.restricted "remove-unused-names" .removeUnusedNames,
    PresetSlot.restricted "remove-unused-brs" .removeUnusedBrs, PresetSlot.restricted "remove-unused-names" .removeUnusedNames,
    PresetSlot.restricted "optimize-instructions" .optimizeInstructions]
  if opt >= 2 || shrink >= 2 then slots := slots ++ [PresetSlot.omitted "pick-load-signs"]
  slots := slots ++ [precompute]
  if opt >= 2 || shrink >= 2 then slots := slots ++ [PresetSlot.omitted "code-pushing"]
  slots := slots ++ [PresetSlot.substituted "simplify-locals-nostructure" .simplifyLocals
      "restricted tee/drop cleanup only; no general nostructure local simplifier",
    PresetSlot.restricted "vacuum" .vacuum, PresetSlot.omitted "reorder-locals",
    PresetSlot.restricted "remove-unused-brs" .removeUnusedBrs]
  if opt >= 3 || shrink >= 2 then slots := slots ++ [PresetSlot.omitted "merge-locals"]
  slots := slots ++ [PresetSlot.restricted "coalesce-locals" .coalesceLocals]
  if opt >= 3 || shrink >= 1 then slots := slots ++ [PresetSlot.omitted "local-cse"]
  slots := slots ++ [PresetSlot.restricted "simplify-locals" .simplifyLocals, PresetSlot.restricted "vacuum" .vacuum,
    PresetSlot.omitted "reorder-locals", PresetSlot.restricted "coalesce-locals" .coalesceLocals,
    PresetSlot.omitted "reorder-locals", PresetSlot.restricted "vacuum" .vacuum]
  if opt >= 3 || shrink >= 1 then slots := slots ++ [PresetSlot.restricted "code-folding" .codeFolding]
  slots := slots ++ [PresetSlot.restricted "merge-blocks" .mergeBlocks,
    PresetSlot.restricted "remove-unused-brs" .removeUnusedBrs, PresetSlot.restricted "remove-unused-names" .removeUnusedNames]
  if opt >= 3 || shrink >= 1 then slots := slots ++ [PresetSlot.omitted "constraint-analysis"]
  slots := slots ++ [PresetSlot.restricted "merge-blocks" .mergeBlocks, precompute,
    PresetSlot.restricted "optimize-instructions" .optimizeInstructions]
  if opt >= 2 || shrink >= 1 then slots := slots ++ [PresetSlot.omitted "rse"]
  slots := slots ++ [PresetSlot.restricted "vacuum" .vacuum]
  if opt >= 2 || shrink >= 1 then slots := slots ++ [PresetSlot.omitted "dae-optimizing"]
  if opt >= 2 || shrink >= 2 then slots := slots ++ [PresetSlot.inlining]
  slots := slots ++ [PresetSlot.omitted "duplicate-function-elimination", PresetSlot.omitted "duplicate-import-elimination"]
  if shrink >= 2 then slots := slots ++ [PresetSlot.omitted "merge-similar-functions"]
  slots := slots ++ [globals, PresetSlot.rume]
  if opt >= 2 || shrink >= 1 then slots := slots ++ [PresetSlot.omitted "reorder-globals"]
  return slots ++ [PresetSlot.restricted "directize" .directize]

def CleanupPreset.stages (preset : CleanupPreset) : List CleanupStage :=
  preset.schedule.flatMap (·.stages)

/-- Inspection keeps every unsupported upstream slot and substitution visible. -/
def CleanupPreset.report (preset : CleanupPreset) : String :=
  preset.name ++ " restricted version_133 feature-neutral schedule\n" ++
    String.intercalate "\n" (preset.schedule.map fun slot =>
      slot.upstream ++ " => " ++
      (if slot.stages.isEmpty then "[omitted]" else
        String.intercalate "," (slot.stages.map CleanupStage.name)) ++ " (" ++ slot.note ++ ")")

end Silmaril.Wasm.Binaryen.Exe
