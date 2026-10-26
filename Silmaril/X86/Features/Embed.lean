module

public import Silmaril.X86.Features.Transport
public import Silmaril.X86.Float.Machine

/-!
# The existing machines inside the feature-parametric one

* The integer machine: `step F []` is `Ext.step` whenever it is not a feature
  fault (`step_nil_eq_ofBase`, in `Machine.lean`), and unconditionally on a
  processor with LZCNT, BMI1 and POPCNT (`step_nil_of_baseFeatures`).
* Scalar SSE: `floatExt` is `X86.Float`'s scalar SSE/SSE2/SSE4.1 subset as an
  `Extension`: its decoder is `Float.byteDecoder`, an instruction requires its
  `Float.Instr.feature`, and it executes `Float.Instr.exec` on the scalar view
  `State.toFloat`, writing the result back as legacy SSE does
  (`State.withFloat`: bits 511:128 kept). `step_floatExt` shows that whenever
  `X86.Float`'s own machine decodes a scalar SSE instruction that the integer
  decoder rejects and its feature is present, both machines take the same
  step.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory)

/-- The CPUID feature of `X86.Float`'s feature names. -/
def _root_.Silmaril.X86.Float.Feature.toFeature : Float.Feature → Feature
  | .sse => .sse
  | .sse2 => .sse2
  | .sse41 => .sse41

/-- A scalar-SSE result on the extended state. -/
def floatResult (s : State) : Float.Result → Result
  | .commit t memory => .retired (s.withFloat t) memory
  | .fault .memory => .fault .dataFault
  | .fault .alignment => .fault .generalProtection
  | .fault .reservedMxcsr => .fault .generalProtection
  | .fault (.simd mxcsr) => .fault (.simdException mxcsr)

/-- `X86.Float`'s scalar SSE/SSE2/SSE4.1 instructions as an extension. -/
def floatExt : Extension where
  name := "X86.Float scalar SSE/SSE2/SSE4.1"
  Syntax := Float.Instr
  decoder := Float.byteDecoder
  requires i := [i.feature.toFeature]
  exec i _ s memory := floatResult s (i.exec s.toFloat memory)

@[simp] theorem floatExt_decode : floatExt.decoder.decode = Float.decode := rfl

theorem floatExt_requires (i : Float.Instr) : floatExt.requires i = [i.feature.toFeature] := rfl

theorem floatExt_exec (i : Float.Instr) (n : Nat) (s : State) (memory : Memory) :
    floatExt.exec i n s memory = floatResult s (i.exec s.toFloat memory) := rfl

/-- A scalar SSE instruction at RIP that the integer decoder rejects. -/
theorem step_floatExt_of_decode {F : FeatureSet} {exit : Word} {m : MState} {i : Float.Instr}
    {n : Nat}
    (hbase : Ext.decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = none)
    (hdec : Float.decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) =
      some (i, n))
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat n) :
    step F [floatExt] exit m = extStep F floatExt i n m :=
  step_of_ext (e := floatExt) (x := i) hbase (by simp [extDecode, hdec]) hperm

/-- `X86.Float` machine outcomes on the extended state. -/
def Outcome.ofFloat (s : State) : Float.Outcome → Outcome
  | .retired next => .retired ⟨s.withFloat next.state, next.memory⟩
  | .returned final => .returned ⟨s.withFloat final.state, final.memory⟩
  | .undecoded => .undecodable
  | .memoryFault _ => .fault .dataFault
  | .generalProtection _ => .fault .generalProtection
  | .simdException _ mxcsr => .fault (.simdException mxcsr)
  | .invalidOpcode => .fault .invalidOpcode
  | .undefinedFlag _ => .unmodeled

private theorem float_decode_of_insn {bytes : List Byte} {i : Float.Instr} {n : Nat}
    (h : Float.Insn.decode bytes = some (.sse i, n)) : Float.decode bytes = some (i, n) := by
  unfold Float.Insn.decode at h
  split at h
  · cases h
  · split at h
    · rename_i j k hj; cases h; exact hj
    · rename_i hn
      cases hc : Float.CtlInstr.decode bytes with
      | none => rw [hc] at h; cases h
      | some r => rw [hc] at h; cases h

/-- Agreement with `X86.Float`'s machine on scalar SSE instructions. -/
theorem step_floatExt {F : FeatureSet} {exit : Word} {m : MState} {i : Float.Instr} {n : Nat}
    (hfetch : Float.fetch m.memory m.state.core.rip.toNat = .decoded (.sse i) n)
    (hbase : Ext.decode (fetchWindow m.memory maxInstrLength m.state.core.rip.toNat) = none)
    (hF : i.feature.toFeature ∈ F) :
    step F [floatExt] exit m =
      Outcome.ofFloat m.state (Float.MState.step exit ⟨m.state.toFloat, m.memory⟩) := by
  have hf := hfetch
  unfold Float.fetch at hf
  split at hf
  · rename_i instr length hd
    split at hf
    · rename_i hperm
      cases hf
      have hdec := float_decode_of_insn hd
      rw [step_of_ext (e := floatExt) (x := i) hbase (by simp [extDecode, hdec]) hperm]
      have hrip : (m.state.toFloat).core.rip = m.state.core.rip := rfl
      simp only [Float.MState.step, hrip, hfetch]
      unfold extStep
      have hmiss : F.missing (floatExt.requires i) = none := by
        have hF' : F.has i.feature.toFeature = true := hF
        simp [floatExt_requires, FeatureSet.missing, hF']
      rw [hmiss]
      simp only [floatExt_exec]
      cases hx : i.exec m.state.toFloat m.memory with
      | commit t memory => rfl
      | fault flt => cases flt <;> rfl
    · cases hf
  · cases hf

end Silmaril.X86.Features
