module

public import Silmaril.Machine.SystemV.Abi.Ffi.Defs

@[expose] public section
namespace Silmaril.Machine.SystemV.Abi.Ffi

/-- A typed native result retains every caller slice outside its write footprint. -/
theorem Result.readBytes {signature : Signature} {value : ResultValue signature.result}
    {writes : Footprint} {call : Call} {final : State}
    (result : Result signature value writes call final) {address length : Nat}
    (disjoint : ∀ offset < length, ¬ writes (address + offset)) :
    final.machine.memory.readBytes address length =
      call.initial.machine.memory.readBytes address length :=
  Silmaril.Process.Memory.WritesWithin.readBytes result.frame disjoint

@[simp] theorem bytesOfNat_length (value offset count : Nat) :
    (bytesOfNat value offset count).length = count := by
  simp [bytesOfNat]

/-- The register observation reads exactly the requested low bytes and therefore
places no constraints on excess high register bits. -/
theorem locationBytes_gp (state : State) (register : Silmaril.X86.Reg)
    (count : Nat) (fits : count ≤ 8) :
    locationBytes state (.gp register) count =
      some (bytesOfNat ((state.machine.core.read register).setWidth (8 * count)).toNat 0 count) := by
  simp [locationBytes, fits]

/-- Values with equal low object-width bits induce exactly the same GP byte
observation, regardless of excess high register bits. -/
theorem locationBytes_gp_eq_of_lowBits (first second : State)
    (register : Silmaril.X86.Reg) (count : Nat)
    (lowBits : (first.machine.core.read register).setWidth (8 * count) =
      (second.machine.core.read register).setWidth (8 * count)) :
    locationBytes first (.gp register) count = locationBytes second (.gp register) count := by
  simp only [locationBytes]
  rw [lowBits]

/-- Changing unobserved padding bytes preserves a register encoding. This also
covers x87 storage padding: only the ten value bytes occur in its return chunk. -/
theorem chunksAt_of_observed_eq {state : State} {first second : Silmaril.Cerberus.NativeTypes.Bytes}
    {chunks : List Chunk} (sameLength : first.length = second.length)
    (observed : ∀ chunk ∈ chunks,
      (first.drop chunk.offset).take chunk.bytes = (second.drop chunk.offset).take chunk.bytes)
    (encoded : ChunksAt state first chunks) : ChunksAt state second chunks := by
  intro chunk member
  obtain ⟨fits, value⟩ := encoded chunk member
  exact ⟨by omega, by rw [← observed chunk member]; exact value⟩

theorem TotalCorrect.realizes {signature : Signature}
    {result : Values signature.arguments → ResultValue signature.result}
    {writes : Values signature.arguments → Footprint}
    {unaliased : Values signature.arguments → Nat → Nat → Prop}
    {domain : Values signature.arguments → Call → Prop} {execute : Call → State → Prop}
    (correct : TotalCorrect signature result writes unaliased domain execute) :
    Realizes signature result writes unaliased domain execute := by
  intro arguments call entry domainAt
  obtain ⟨final, run⟩ := correct.2 arguments call entry domainAt
  exact ⟨final, run, correct.1 arguments call entry domainAt final run⟩

/-- For deterministic executions the earlier returning-run contract also gives
universal partial correctness. Nondeterministic backends need a separate proof. -/
theorem Realizes.partialCorrect_of_deterministic {signature : Signature}
    {result : Values signature.arguments → ResultValue signature.result}
    {writes : Values signature.arguments → Footprint}
    {unaliased : Values signature.arguments → Nat → Nat → Prop}
    {domain : Values signature.arguments → Call → Prop} {execute : Call → State → Prop}
    (correct : Realizes signature result writes unaliased domain execute)
    (deterministic : ∀ call first second, execute call first → execute call second → first = second) :
    PartialCorrect signature result writes unaliased domain execute := by
  intro arguments call entry domainAt final run
  obtain ⟨witness, witnessRun, resultAt⟩ := correct arguments call entry domainAt
  have equal := deterministic call witness final witnessRun run
  exact equal ▸ resultAt

end Silmaril.Machine.SystemV.Abi.Ffi
