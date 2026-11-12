module

public import Silmaril.Wasm.SpecTec.Defs

/-!
# SpecTec: theorems

Restated from the copies in `Silmaril.Raw.Wasm.SpecTec` (source names in brackets). What they say
and what they do not is in `docs/projects/spectec/README.md`.

* **the stream** — the decoder inverts the printer on every IL definition
  (`decodeDef?_defS`), and as encoding relations the decoder is sound and complete
  (`decodeScript?_sound`, `decodeScript?_complete`);
* **the semantics** — IL evaluation is deterministic (`evalRel_deterministic`);
* **provenance** — the rules the equivalence layer reasons about are the pinned wasm-3.0
  script's rules at the stated indices, checked by `rfl` against the imported stream
  (`hasStepPureRules_wasm30`, `hasStepRules_wasm30`, `hasStepLiftRules_wasm30`);
* **hand-written Core steps are SpecTec derivations** — e.g. `br_if` taken
  (`derives_brIfTrue`), and with silmaril-lean's numerics installed `i32.and` steps the whole
  SpecTec machine at every state (`derives_step_binopAnd_wasmBuiltins`); this is the
  Core-to-SpecTec direction for a fragment, not an equivalence of the two relations;
* **errata** — the four `#650` patches apply to the pinned script (`applyErrata_binary51`);
* **defects the semantics exposes** — the pinned signed-LEB128 grammar `BsN(32)` derives
  nothing from `FF 7E` (`i32.const -129`), even in the corrected script
  (`not_bsn_FF7E_corrected`), so the corrected `Bi32` disagrees with the hand-written signed
  LEB128 grammar (`bi32_corrected_disagrees_with_in`); `Step/table.grow-succeed` cannot fire
  under the IL semantics because its result variable is bound by nothing
  (`not_ruleFires_tableGrowSucceed_pinned`); the interpreter's strict slice bound
  (`il/eval.ml:284`) left a load ending exactly at the end of memory with neither the `-val` nor
  the `-oob` side condition, which the port corrects (upstream item U2): there the access is in
  bounds and has its slice (`boundary_slice`).
-/

public section

namespace Silmaril.SpecTec.Equiv.Execution

/-- **Cross-check against the binary-format bridge.**
`Equiv/BinaryInstr.lean` built, independently and for a different purpose,
a total `Silmaril.SpecTec.Equiv.instrV : Wasm.Instr → Value` covering §5.3's
137 plain opcodes and the index-immediate instructions.  Wherever both are
defined they agree, by `rfl`: eight of `instrV?`'s ten clauses are checked
against the independently written binary-format bridge.  (`intConst` and
`vecConst` are the two `Equiv.instrV` does not reach, because §5.3 gives
them a LEB128 immediate rather than a closed value expression.) -/
theorem instrV?_agrees_binaryInstr (l : Wasm.LabelIdx) (x : Wasm.LocalIdx) :
    instrV? .nop = some (Silmaril.SpecTec.Equiv.instrV .nop) ∧
    instrV? .unreachable = some (Silmaril.SpecTec.Equiv.instrV .unreachable) ∧
    instrV? .drop = some (Silmaril.SpecTec.Equiv.instrV .drop) ∧
    instrV? (.select none) = some (Silmaril.SpecTec.Equiv.instrV (.select none)) ∧
    instrV? (.br l) = some (Silmaril.SpecTec.Equiv.instrV (.br l)) ∧
    instrV? (.brIf l) = some (Silmaril.SpecTec.Equiv.instrV (.brIf l)) ∧
    instrV? (.localSet x) = some (Silmaril.SpecTec.Equiv.instrV (.localSet x)) ∧
    instrV? (.localTee x) = some (Silmaril.SpecTec.Equiv.instrV (.localTee x)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Silmaril.SpecTec.Equiv.Execution

namespace Silmaril.Wasm.SpecTec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- `IL.decodeDef?` inverts the printer `IL.defS` on every definition
[`Silmaril.SpecTec.IL.decodeDef?_defS`]. -/
theorem decodeDef?_defS : ∀ d : Def, decodeDef? (defS d) = some d :=
  Silmaril.SpecTec.IL.decodeDef?_defS

/-- The script decoder is sound for the printer's encoding relation
[`Silmaril.SpecTec.IL.decodeScript?_sound`]. -/
theorem decodeScript?_sound : scriptRel.DecoderSound decodeScript? :=
  Silmaril.SpecTec.IL.decodeScript?_sound

/-- The script decoder is complete for the printer's encoding relation
[`Silmaril.SpecTec.IL.decodeScript?_complete`]. -/
theorem decodeScript?_complete : scriptRel.DecoderComplete decodeScript? :=
  Silmaril.SpecTec.IL.decodeScript?_complete

/-- IL expression evaluation is deterministic [`Silmaril.SpecTec.Sem.evalRel_deterministic`]. -/
theorem evalRel_deterministic (env : Env) (ρ : VarEnv) : (evalRel env ρ).Deterministic :=
  Silmaril.SpecTec.Sem.evalRel_deterministic env ρ

/-- Twenty-three `Step_pure` rules, transcribed, are the pinned script's at their indices
[`Silmaril.SpecTec.Equiv.Execution.hasStepRules_wasm30`]. -/
theorem hasStepPureRules_wasm30 :
    Silmaril.SpecTec.Equiv.Execution.HasStepRules (envOfScript Specs.wasm30) :=
  Silmaril.SpecTec.Equiv.Execution.hasStepRules_wasm30

/-- All thirty-six `Step` rules, transcribed, are the pinned script's at their indices
[`Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30`]. -/
theorem hasStepRules_wasm30 :
    Silmaril.SpecTec.Equiv.ExecStepRules.HasStepRules (envOfScript Specs.wasm30) :=
  Silmaril.SpecTec.Equiv.ExecStepRules.hasStepRules_wasm30

/-- `Step/pure` and `Step/read` are the pinned script's rules 0 and 1
[`Silmaril.SpecTec.Equiv.ExecStep.hasStepLiftRules_wasm30`]. -/
theorem hasStepLiftRules_wasm30 :
    Silmaril.SpecTec.Equiv.ExecStep.HasStepLiftRules (envOfScript Specs.wasm30) :=
  Silmaril.SpecTec.Equiv.ExecStep.hasStepLiftRules_wasm30

/-- The hand-written Core step `i32.const c; br_if l ~> br l` (`c ≠ 0`) is a `Step_pure`
derivation, in every environment holding the transcribed rules
[`Silmaril.SpecTec.Equiv.Execution.derives_brIfTrue`]. -/
theorem derives_brIfTrue {env : Env} (h : Silmaril.SpecTec.Equiv.Execution.HasStepRules env)
    {c : BitVec 32} {l : Silmaril.Wasm.LabelIdx} {v : Value} (hc : c ≠ 0)
    (hv : Silmaril.SpecTec.Equiv.Execution.StepImage
      [Silmaril.Wasm.Execution.Core.constI32 c, .plain (.brIf l)] [.plain (.br l)] v) :
    Derives env "Step_pure" "%~>%" [] v :=
  Silmaril.SpecTec.Equiv.Execution.derives_brIfTrue h hc hv

open Silmaril.SpecTec.Equiv in
/-- With silmaril-lean's numerics installed as the IL's builtins, `i32.and` steps the whole
SpecTec machine (`Step`, through `Step/pure`) at every state `z`
[`Silmaril.SpecTec.Equiv.ExecStep.derives_step_binopAnd_wasmBuiltins`]. -/
theorem derives_step_binopAnd_wasmBuiltins (i₁ i₂ : BitVec 32) (z : Value) :
    Derives ExecBuiltins.wasm30WithWasmNumerics "Step" "%~>%" []
      (.tuple
        [ExecStep.configV z
          [Execution.constV Execution.i32V (bvV i₁),
           Execution.constV Execution.i32V (bvV i₂),
           ExecNumeric.binopV Execution.i32V ExecBuiltins.andV],
         ExecStep.configV z
          [Execution.constV Execution.i32V
            (bvV (Silmaril.Wasm.Numerics.iand_ 32 i₁ i₂))]]) :=
  ExecStep.derives_step_binopAnd_wasmBuiltins i₁ i₂ z

/-- The four `#650` patches apply to the pinned wasm-3.0 script
[`Silmaril.SpecTec.IL.Binary51.applyErrata_binary51`]. -/
theorem applyErrata_binary51 :
    applyErrata Binary51.binary51 Specs.wasm30 = some Binary51.wasm30binary51 :=
  Silmaril.SpecTec.IL.Binary51.applyErrata_binary51

/-- The signed LEB128 grammar `BsN(32)` of the corrected wasm-3.0 script derives no value
from `FF 7E`, the encoding of `-129` (`#803`)
[`Silmaril.SpecTec.Equiv.not_bsn_FF7E_corrected`]. -/
theorem not_bsn_FF7E_corrected (ρ : VarEnv) (v : Value) :
    ¬ gramRelSup Silmaril.SpecTec.Equiv.envCorrected ρ
      (.varG "BsN" [.expA (.numE (.natN 32))]) [0xFF, 0x7E] v :=
  Silmaril.SpecTec.Equiv.not_bsn_FF7E_corrected ρ v

/-- So the corrected `Bi32` is not silmaril-lean's signed LEB128 grammar `IN 32`, read
through the value bridge [`Silmaril.SpecTec.Equiv.bi32_corrected_disagrees_with_in`]. -/
theorem bi32_corrected_disagrees_with_in (ρ : VarEnv) :
    ¬ ∀ (bs : Silmaril.SpecTec.Grammar.Bytes) (v : Value),
        gramRelSup Silmaril.SpecTec.Equiv.envCorrected ρ (.varG "Bi32" []) bs v ↔
          ∃ bv : BitVec 32, Silmaril.Wasm.Binary.IN 32 bs bv ∧
            v = Silmaril.SpecTec.Equiv.iNV bv :=
  Silmaril.SpecTec.Equiv.bi32_corrected_disagrees_with_in ρ

/-- `Step/table.grow-succeed` (rule 15 of `Step`) fires at nothing under the IL semantics
[`Silmaril.SpecTec.Equiv.ExecStepRules.not_ruleFires_tableGrowSucceed_pinned`]. -/
theorem not_ruleFires_tableGrowSucceed_pinned {env : Env} {v : Value} :
    ¬ Silmaril.SpecTec.Equiv.Validation.RuleFires env "%~>%" [] [] v
      Silmaril.SpecTec.Equiv.ExecStepRules.tableGrowSucceedRule :=
  Silmaril.SpecTec.Equiv.ExecStepRules.not_ruleFires_tableGrowSucceed_pinned

/-- A load of `k` bytes at effective address `a` ending exactly at the end of memory fails the
`-oob` guard and meets the `-val` slice condition, with the last `k` bytes, under the corrected
slice bound [`Silmaril.SpecTec.Equiv.ExecReadMemory.boundary_slice`]. The interpreter's original
strict bound is `Silmaril.Wasm.SpecTec.Broken.sliceEvalMl?`. -/
theorem boundary_slice {a k : Nat} {bs : List Value} (h : a + k = bs.length) :
    ¬ bs.length < a + k ∧ Value.slice? (.list bs) a k = some (.list (bs.drop a)) :=
  Silmaril.SpecTec.Equiv.ExecReadMemory.boundary_slice h

end Silmaril.Wasm.SpecTec
