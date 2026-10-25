module

public import Silmaril.Wasm.Binaryen.Toolkit.EmptyIdentityMerge
public import Silmaril.Wasm.Binaryen.Toolkit.MergeSound
public import Silmaril.Wasm.Binaryen.Exe.CoreInputCheckSound
public import Silmaril.Wasm.Execution.Core.Exec.Instantiate

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit

open Execution.Core Validation Numerics

def EmptyIdentityInputs (inputs : List (String × Module)) (survivor : String)
    (merged : Module) : Prop :=
  ∃ other, other ≠ survivor ∧
    (inputs = [(other, {}), (survivor, merged)] ∨
      inputs = [(survivor, merged), (other, {})])

theorem validateIdentityPartner_sound {m : Module}
    (accepted : validateIdentityPartner m = .ok ()) : m.imports = [] ∧ ModuleValid m := by
  unfold validateIdentityPartner at accepted
  split at accepted
  · cases accepted
  · rename_i imports
    split at accepted
    · cases accepted
    · rename_i valid
      refine ⟨by simpa using imports, validate?_isSome_iff.mp ?_⟩
      cases checked : validate? m with
      | none => simp [checked] at valid
      | some mt => rfl

/-- The output retains the exact original survivor bytes. All original byte
meanings are kept; the other decoded module is provably empty. -/
theorem mergeEmptyIdentityBytes_sound {inputs : List (String × ByteArray)}
    {a : EmptyIdentityMergedArtifact} (accepted : mergeEmptyIdentityBytes inputs = .ok a) :
    List.Forall₂ (fun input decoded => input.1 = decoded.1 ∧
      Binary.Core.Encodes input.2.data.toList decoded.2) inputs a.inputs ∧
    (a.survivor, a.bytes) ∈ inputs ∧ a.merged.imports = [] ∧
    ModuleValid a.merged ∧ Binary.Core.Encodes a.bytes.data.toList a.merged ∧
    EmptyIdentityInputs a.inputs a.survivor a.merged := by
  unfold mergeEmptyIdentityBytes at accepted
  split at accepted
  · rename_i original leftName leftBytes rightName rightBytes
    split at accepted
    · cases accepted
    · rename_i distinct
      obtain ⟨left, leftDecoded, accepted⟩ := Exe.bind_ok accepted
      obtain ⟨right, rightDecoded, accepted⟩ := Exe.bind_ok accepted
      have leftBytesMeaning := decodeInput_sound leftDecoded
      have rightBytesMeaning := decodeInput_sound rightDecoded
      split at accepted
      · rename_i empty
        obtain ⟨ignored, partner, accepted⟩ := Exe.bind_ok accepted
        cases ignored
        cases Except.ok.inj accepted
        have emptyModule := Exe.canonicalModuleEq_sound empty
        have valid := validateIdentityPartner_sound partner
        refine ⟨.cons ⟨rfl, leftBytesMeaning⟩ (.cons ⟨rfl, rightBytesMeaning⟩ .nil),
          by simp, valid.1, valid.2, rightBytesMeaning, leftName, ?_, .inl ?_⟩
        · simpa using distinct
        · simp [emptyModule]
      · split at accepted
        · rename_i empty
          obtain ⟨ignored, partner, accepted⟩ := Exe.bind_ok accepted
          cases ignored
          cases Except.ok.inj accepted
          have emptyModule := Exe.canonicalModuleEq_sound empty
          have valid := validateIdentityPartner_sound partner
          refine ⟨.cons ⟨rfl, leftBytesMeaning⟩ (.cons ⟨rfl, rightBytesMeaning⟩ .nil),
            by simp, valid.1, valid.2, leftBytesMeaning, rightName, ?_, .inr ?_⟩
          · simpa [ne_comm] using distinct
          · simp [emptyModule]
        · cases accepted
  · cases accepted

/-- Instantiating the empty module preserves every ambient store exactly. -/
theorem emptyModule_ready {H : Type} (P : Profile) (host : HostSemantics H) (s : Store H) :
    Ready P host s {} [] s {} := by
  have evaluator : EvalSound P host (fun _ _ _ => (none : Option (Store H × Val))) := by
    intro s f code final value impossible
    cases impossible
  have computed : instantiate? (fun _ _ _ => (none : Option (Store H × Val))) s {} [] =
      some ⟨s, {}, []⟩ := by rfl
  have valid : ModuleOk ({} : Module) ⟨[], []⟩ := validate?_sound (by rfl)
  exact ⟨_, _, instantiate?_sound evaluator computed ⟨[], [], valid, .nil⟩,
    .refl, rfl, rfl, rfl⟩

/-- Removing an empty left or right partner preserves all behavior of the
retained module in the actual original, separately instantiated program. -/
theorem emptyIdentityInputs_refines_original {H : Type} {inputs : List (String × Module)}
    {survivor : String} {merged : Module} (identity : EmptyIdentityInputs inputs survivor merged)
    (closed : merged.imports = []) (P : Profile) (host : HostSemantics H)
    (x : String) (vs : List Val) :
    (moduleEntryPoints P host closedEnv).beh merged x vs ⊆
      Program.beh P host inputs survivor x vs := by
  obtain ⟨other, distinct, left | right⟩ := identity
  · subst inputs
    rintro behavior ⟨s, imports, final, mi, address, ⟨rfl, rfl⟩, ready, exported, observation⟩
    refine ⟨final, [(survivor, mi), (other, {})], mi, address,
      .cons rfl (emptyModule_ready P host {}) (.cons ?_ ready .nil), ?_, exported, observation⟩
    · simp [closed, resolveImportsBy]
    · simp
  · subst inputs
    rintro behavior ⟨s, imports, final, mi, address, ⟨rfl, rfl⟩, ready, exported, observation⟩
    refine ⟨final, [(other, {}), (survivor, mi)], mi, address,
      .cons ?_ ready (.cons rfl (emptyModule_ready P host final) .nil), ?_, exported, observation⟩
    · simp [closed, resolveImportsBy]
    · have different : (survivor == other) = false := by
        apply Bool.eq_false_iff.mpr
        intro same
        exact distinct (beq_iff_eq.mp same).symm
      simp [List.lookup_cons, different]

theorem mergeEmptyIdentityBytes_refines_original {H : Type}
    {inputs : List (String × ByteArray)} {a : EmptyIdentityMergedArtifact}
    (accepted : mergeEmptyIdentityBytes inputs = .ok a) (P : Profile) (host : HostSemantics H)
    (x : String) (vs : List Val) :
    (moduleEntryPoints P host closedEnv).beh a.merged x vs ⊆
      Program.beh P host a.inputs a.survivor x vs := by
  obtain ⟨_, _, closed, _, _, identity⟩ := mergeEmptyIdentityBytes_sound accepted
  exact emptyIdentityInputs_refines_original identity closed P host x vs

end Silmaril.Wasm.Binaryen.Toolkit
