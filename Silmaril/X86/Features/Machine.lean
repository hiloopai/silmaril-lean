module

public import Silmaril.X86.Features.Extension
public import Silmaril.X86.Ext.Machine

/-!
# The feature-parametric x86 machine

`step F exts exit m` is one fetch/decode/execute step of a processor whose
executable feature set is `F`, over the canonical integer machine
`X86.Ext` extended by the instruction families `exts`.

## Decoding

The bytes at RIP are first decoded by the integer decoder (`Ext.fetch`). If it
accepts them, the instruction executes exactly as `Ext.step` does, on the
integer part of the state; the vector, mask, MXCSR and x87 state are unchanged.
Otherwise every extension decoder is tried in list order on the same fetch
window (`extDecode`); the first that accepts the bytes wins, and execute
permission is required on exactly the consumed span. When no extension accepts
them either, the integer machine's classification is kept: a truncated
encoding is a fetch fault and anything else is `undecodable`.

## Features

An extension instruction executes only when every feature in its `requires`
list is in `F`; otherwise the step is `featureUD f` for the first missing
feature `f`. This is what hardware does (#UD, SIGILL at the process level):
for every feature in `Feature`, the SDM specifies #UD when CPUID does not
report it (or XCR0 does not enable its state, which `FeatureSet.ofCpuid`
folds in).

The integer machine contains LZCNT, TZCNT and POPCNT (`Ext.Instr.bitcount`).
POPCNT raises #UD without its feature (`featureUD .popcnt`). LZCNT and TZCNT
do not: on a processor without LZCNT (BMI1), `F3 0F BD` (`F3 0F BC`) executes as
BSR (BSF), whose result differs. The model does not describe BSR/BSF and
reports `featureAlias f`. Both outcomes are *feature faults*
(`Outcome.featureFault?`): the outcome depends on the feature set.

`featureUD` is a defined architectural fault. It is distinct from
`undecodable` and `unmodeled`, which say that the bytes are outside the model,
and allow any continuation at the process level.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory)

/-- The extended state and memory of one user-mode thread. -/
structure MState where
  state : State
  memory : Memory

/-- The integer machine's view. -/
def MState.toBase (m : MState) : X86.MState := ⟨m.state.core, m.memory⟩

/-- The result of one step. Faults change nothing. -/
inductive Outcome where
  /-- The instruction retired with this successor state. -/
  | retired (next : MState)
  /-- A RET popped the designated return address; this is the state after it. -/
  | returned (final : MState)
  /-- #UD because the instruction needs the feature `f`, which is absent. -/
  | featureUD (f : Feature)
  /-- Without feature `f` these bytes are a different instruction, which the
  model does not describe (LZCNT/TZCNT without LZCNT/BMI1 are BSR/BSF). -/
  | featureAlias (f : Feature)
  /-- An architectural fault. -/
  | fault (f : Fault)
  /-- A SETcc, Jcc or CMOVcc whose condition depends on an undefined flag. -/
  | undefinedCondition (c : Ext.Cond)
  /-- The instruction bytes cannot be fetched. -/
  | fetchFault
  /-- The bytes at RIP are outside every decoder (chaos). -/
  | undecodable
  /-- The instruction is decoded but its behaviour is not modelled (chaos). -/
  | unmodeled

/-- The feature an outcome depends on, if it is a feature fault. -/
def Outcome.featureFault? : Outcome → Option Feature
  | .featureUD f | .featureAlias f => some f
  | _ => none

/-- An integer-machine outcome, on the extended state `s`. -/
def Outcome.ofBase (s : State) : Ext.Outcome → Outcome
  | .retired next => .retired ⟨s.setCore next.core, next.memory⟩
  | .returned final => .returned ⟨s.setCore final.core, final.memory⟩
  | .trapped => .fault .invalidOpcode
  | .undefinedCondition c => .undefinedCondition c
  | .divideFault => .fault .divideError
  | .dataFault _ => .fault .dataFault
  | .fetchFault => .fetchFault
  | .undecodable => .undecodable

@[simp] theorem Outcome.featureFault?_ofBase (s : State) (o : Ext.Outcome) :
    (Outcome.ofBase s o).featureFault? = none := by
  cases o <;> rfl

/-! ## Integer instructions that need features -/

/-- The feature an integer instruction needs, and whether its absence makes the
bytes a different instruction (`true`) rather than #UD (`false`). -/
def baseRequirement : Ext.Instr → Option (Feature × Bool)
  | .bitcount .lzcnt .. => some (.lzcnt, true)
  | .bitcount .tzcnt .. => some (.bmi1, true)
  | .bitcount .popcnt .. => some (.popcnt, false)
  | _ => none

/-- The feature fault of an integer instruction on `F`, if any. -/
def baseCheck (F : FeatureSet) (i : Ext.Instr) : Option Outcome :=
  match baseRequirement i with
  | some (f, aliased) =>
    if F.has f then none else some (if aliased then .featureAlias f else .featureUD f)
  | none => none

/-- The integer machine's own feature record of a feature set. -/
def FeatureSet.toCpu (F : FeatureSet) : Ext.CpuFeatures :=
  ⟨F.has .lzcnt, F.has .bmi1, F.has .popcnt⟩

/-- `baseCheck` passes exactly when `Ext.Instr.requires` holds. -/
theorem baseCheck_eq_none_iff (F : FeatureSet) (i : Ext.Instr) :
    baseCheck F i = none ↔ i.requires F.toCpu = true := by
  cases i
  case bitcount op _ _ _ =>
    cases op <;> simp [baseCheck, baseRequirement, Ext.Instr.requires, FeatureSet.toCpu]
  all_goals exact iff_of_true rfl rfl

theorem baseCheck_mono {F G : FeatureSet} (hFG : F ⊆ G) {i : Ext.Instr}
    (h : baseCheck F i = none) : baseCheck G i = none := by
  unfold baseCheck at h ⊢
  split
  · rename_i f aliased hr
    rw [hr] at h
    simp only at h
    split at h
    · rename_i hf
      simp only [show G.has f = true from hFG f hf, ↓reduceIte]
    · cases h
  · rfl

theorem baseCheck_featureFault {F : FeatureSet} {i : Ext.Instr} {o : Outcome}
    (h : baseCheck F i = some o) : o.featureFault?.isSome := by
  unfold baseCheck at h
  split at h
  · split at h
    · cases h
    · cases h; split <;> rfl
  · cases h

/-! ## Extension decoding -/

/-- The first extension that decodes the bytes, with its instruction and length. -/
def extDecode : List Extension → List Byte → Option ((e : Extension) × (e.Syntax × Nat))
  | [], _ => none
  | e :: es, bytes =>
    match e.decoder.decode bytes with
    | some (x, n) => some ⟨e, x, n⟩
    | none => extDecode es bytes

/-- Execute a decoded extension instruction on `F`. -/
def extStep (F : FeatureSet) (e : Extension) (x : e.Syntax) (length : Nat) (m : MState) :
    Outcome :=
  match F.missing (e.requires x) with
  | some f => .featureUD f
  | none =>
    match e.exec x length m.state m.memory with
    | .retired s memory => .retired ⟨s, memory⟩
    | .fault f => .fault f
    | .unmodeled => .unmodeled

/-! ## One step -/

/-- Fetch, decode and execute one instruction on a processor with features `F`. -/
def step (F : FeatureSet) (exts : List Extension) (exit : Word) (m : MState) : Outcome :=
  match Ext.fetch m.memory m.state.core.rip.toNat with
  | .decoded i _ =>
    match baseCheck F i with
    | some o => o
    | none => Outcome.ofBase m.state (Ext.step exit m.toBase)
  | base =>
    match extDecode exts (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) with
    | some ⟨e, x, n⟩ =>
      if m.memory.Permitted .execute m.state.core.rip.toNat n then extStep F e x n m
      else .fetchFault
    | none =>
      match base with
      | .truncated => .fetchFault
      | _ => .undecodable

/-- Retirement only, as a partial transition function. -/
def stepOpt (F : FeatureSet) (exts : List Extension) (exit : Word) (m : MState) : Option MState :=
  match step F exts exit m with
  | .retired next => some next
  | _ => none

/-- `n` retirements from `initial`. -/
def run (F : FeatureSet) (exts : List Extension) (exit : Word) (n : Nat) (initial : MState) :
    Option MState :=
  Machine.Execution.run (stepOpt F exts exit) n initial

/-- A finite run of retirements followed by a return to `exit`. -/
def Returns (F : FeatureSet) (exts : List Extension) (exit : Word) (initial final : MState) :
    Prop :=
  ∃ n mid, run F exts exit n initial = some mid ∧ step F exts exit mid = .returned final

theorem stepOpt_eq_some_iff {F : FeatureSet} {exts : List Extension} {exit : Word}
    {m next : MState} : stepOpt F exts exit m = some next ↔ step F exts exit m = .retired next := by
  unfold stepOpt
  split <;> simp_all

@[simp] theorem run_zero (F : FeatureSet) (exts : List Extension) (exit : Word) (m : MState) :
    run F exts exit 0 m = some m := rfl

theorem run_succ (F : FeatureSet) (exts : List Extension) (exit : Word) (n : Nat) (m : MState) :
    run F exts exit (n + 1) m = (stepOpt F exts exit m).bind (run F exts exit n) := rfl

/-! ## Step equations -/

/-- An integer instruction at RIP. -/
theorem step_of_base {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {i : Ext.Instr} {n : Nat} (h : Ext.fetch m.memory m.state.core.rip.toNat = .decoded i n) :
    step F exts exit m =
      match baseCheck F i with
      | some o => o
      | none => Outcome.ofBase m.state (Ext.step exit m.toBase) := by
  simp only [step, h]

/-- An integer instruction from exactly fetched bytes. -/
theorem step_of_base_fetch {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {bytes : List Byte} {i : Ext.Instr} {n : Nat}
    (fetched : m.memory.fetchBytes m.state.core.rip.toNat n = some bytes)
    (decoded : Ext.decode bytes = some (i, n)) :
    step F exts exit m =
      match baseCheck F i with
      | some o => o
      | none => Outcome.ofBase m.state (Ext.step exit m.toBase) :=
  step_of_base (Ext.fetch_eq_decoded_iff.mpr ⟨bytes, fetched, decoded⟩)

/-- Bytes the integer decoder rejects, decoded by an extension. -/
theorem step_of_ext {F : FeatureSet} {exts : List Extension} {exit : Word} {m : MState}
    {e : Extension} {x : e.Syntax} {n : Nat}
    (hbase : Ext.decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = none)
    (hext : extDecode exts (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) =
      some ⟨e, x, n⟩)
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F exts exit m = extStep F e x n m := by
  have hf : ∀ i k, Ext.fetch m.memory m.state.core.rip.toNat ≠ .decoded i k := by
    intro i k h
    obtain ⟨bytes, fetched, decoded⟩ := Ext.fetch_eq_decoded_iff.mp h
    obtain ⟨more, hmore⟩ := X86.fetchBytes_prefix_fetchWindow fetched
      (limit := maxInstrLength) (Ext.decode_length decoded).2.2.1
    have := Ext.decode_append more decoded
    rw [hmore, hbase] at this
    cases this
  unfold step
  split
  · rename_i i k h; exact absurd h (hf i k)
  · rw [hext]; simp only [hperm, ite_true]

/-! ## Feature-set facts about one step -/

/-- A feature fault names a feature outside `F`. -/
theorem step_featureFault_not_mem {F : FeatureSet} {exts : List Extension} {exit : Word}
    {m : MState} {f : Feature} (h : (step F exts exit m).featureFault? = some f) : f ∉ F := by
  unfold step at h
  split at h
  · split at h
    · rename_i o hb
      unfold baseCheck at hb
      split at hb
      · split at hb
        · cases hb
        · rename_i hf; cases hb; split at h <;> (cases h; exact hf)
      · cases hb
    · simp at h
  · split at h
    · split at h
      · unfold extStep at h
        split at h
        · rename_i hm; cases h; exact (FeatureSet.missing_not_mem hm).2
        · split at h <;> cases h
      · cases h
    · split at h <;> cases h

/-- With no extensions and no feature fault, the machine is the integer machine. -/
theorem step_nil_eq_ofBase {F : FeatureSet} {exit : Word} {m : MState}
    (h : (step F [] exit m).featureFault? = none) :
    step F [] exit m = Outcome.ofBase m.state (Ext.step exit m.toBase) := by
  unfold step at h ⊢
  split
  · rename_i i n hf
    rw [hf] at h
    simp only at h ⊢
    split
    · rename_i o hb
      rw [hb] at h
      have := baseCheck_featureFault hb
      simp_all
    · rfl
  · rename_i base hd
    simp only [extDecode, Ext.step, MState.toBase]
    cases hb : Ext.fetch m.memory m.state.core.rip.toNat with
    | decoded i n => exact absurd hb (hd i n)
    | truncated => rfl
    | undecodable => rfl

/-- The features the integer machine itself relies on. -/
def baseFeatures : FeatureSet := FeatureSet.ofList [.lzcnt, .bmi1, .popcnt]

theorem baseCheck_of_baseFeatures {F : FeatureSet} (hF : baseFeatures ⊆ F) (i : Ext.Instr) :
    baseCheck F i = none := by
  unfold baseCheck
  split
  · rename_i f aliased hr
    have hf : f ∈ baseFeatures := by
      cases i <;> simp [baseRequirement] at hr
      rename_i op _ _ _
      cases op <;> simp at hr <;> obtain ⟨rfl, rfl⟩ := hr <;> decide
    simp only [show F.has f = true from hF f hf, ↓reduceIte]
  · rfl

/-- On a processor with LZCNT, BMI1 and POPCNT, `step F []` is the integer
machine `Ext.step`, on the integer part of the state. -/
theorem step_nil_of_baseFeatures {F : FeatureSet} (hF : baseFeatures ⊆ F) (exit : Word)
    (m : MState) : step F [] exit m = Outcome.ofBase m.state (Ext.step exit m.toBase) := by
  apply step_nil_eq_ofBase
  unfold step
  split
  · rw [baseCheck_of_baseFeatures hF]; simp
  · simp only [extDecode]; split <;> rfl

end Silmaril.X86.Features
