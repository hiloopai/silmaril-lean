module

public import Silmaril.Wasm.Tools.Component.Validate.Defs
public import Silmaril.Wasm.Component.BinaryP3.Thms
public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Tools.Component.GcAbi.Thms
import Silmaril.Wasm.Component.Reference.Validation.Laws.Thms

/-!
# `wasm-tools validate` for components: specification theorems

* `decode_sound`: a reference decoding is in the binary grammar (`DecodesAs`: the verified
  `BinaryP3` grammar, `BinaryP3.parse_sound`, or wasmparser's reading `BinaryW`); definitions
  for the extended fold are wasmparser's reading or the `BinaryP3` decoding (`DecodesExt`);
* `check_sound`: **an accepted binary is accepted by the specification** (`Accepts`): it
  decodes to `c`, and `c` is `ValidComponentCore3` at `F.feat` with the returned type
  (`checkCore3?_sound`) or the definitions are `GcAbi.GValid` (`GcAbi.check?_sound`: the
  reference's rules, the GC canonical ABI, value exports used), and the extra and gate rules
  find nothing;
* `check_ok_iff`: the executable characterisation of acceptance;
* `check_module_valid`: every core module of a component accepted through the reference path
  is a valid Core 3.0 module;
* `default_le_all`: the default flags are below `--features all`.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Component.Validate

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Validation

/-- The `BinaryP3` path of the decoder is in the grammar. -/
theorem decodeP3_sound {b : ByteArray} {c : RefComponent} (h : decodeP3 b = .ok c) :
    ∃ a, (BinaryP3.componentG (b.size + 1)).G b.data.toList a ∧ toRefP3 a = .ok c := by
  unfold decodeP3 at h
  split at h
  · cases h
  · next a ha => exact ⟨a, BinaryP3.parse_sound ha, h⟩

/-- The `BinaryW` path of the decoder is wasmparser's reading. -/
theorem decodeW_sound {F : CFlags} {b : ByteArray} {e : String} {d : Decoded}
    (h : decodeW F b e = .ok d) :
    ∃ ds, DecodesW F b ds ∧ (d = .ext ds ∨ d = .ref (GcAbi.GDef.toRefs ds)) := by
  unfold decodeW at h
  split at h
  · cases h
  · next a ha =>
    split at h
    · cases h
    · next hn =>
      have hg : F.gc = true ∨ gcOptsUsed a = false := by
        cases hg : F.gc <;> cases hu : gcOptsUsed a <;> simp_all
      split at h
      · cases h
      · next ds hds =>
        split at h
        · cases h; exact ⟨ds, ⟨a, ha, hg, hds⟩, .inl rfl⟩
        · cases h; exact ⟨ds, ⟨a, ha, hg, hds⟩, .inr rfl⟩

theorem decodeW_sound' {F : CFlags} {b : ByteArray} {e : String} {d : Decoded}
    (h : decodeW F b e = .ok d) :
    (∃ c, d = .ref c ∧ DecodesAs F b c) ∨ (∃ ds, d = .ext ds ∧ DecodesExt F b ds) :=
  match decodeW_sound h with
  | ⟨ds, hds, .inl hd⟩ => .inr ⟨ds, hd, .inl hds⟩
  | ⟨ds, hds, .inr hd⟩ => .inl ⟨_, hd, .inr ⟨ds, hds, rfl⟩⟩

/-- **The decoder is sound**: a reference decoding is in the binary grammar (`DecodesAs`);
definitions for the extended fold are wasmparser's reading or the `BinaryP3` decoding. -/
theorem decode_sound {F : CFlags} {b : ByteArray} {d : Decoded} (h : decode F b = .ok d) :
    (∃ c, d = .ref c ∧ DecodesAs F b c) ∨ (∃ ds, d = .ext ds ∧ DecodesExt F b ds) := by
  unfold decode at h
  split at h
  · next c hc =>
    split at h
    · exact decodeW_sound' h
    · next hv =>
      obtain ⟨a, ha, hr⟩ := decodeP3_sound hc
      have hp : DecodesP3 b c := ⟨a, ha, hr, by simpa using hv⟩
      split at h
      · cases h; exact .inr ⟨_, rfl, .inr ⟨c, hp, rfl⟩⟩
      · cases h; exact .inl ⟨c, rfl, .inl hp⟩
  · exact decodeW_sound' h

theorem finish_ok {F : CFlags} {c : RefComponent} {ct ct' : Types.ComponentType Nat Core3Extern}
    (h : finish F c ct = .ok ct') :
    ct' = ct ∧ Extra.extraProblem F.feat.nestedNames c = none ∧ gateAll F c = none := by
  unfold finish at h
  split at h
  · cases h
  · next he =>
    split at h
    · cases h
    · next hg => cases h; exact ⟨rfl, he, hg⟩

/-- **Executable characterisation of acceptance.** -/
theorem check_ok_iff {F : CFlags} {b : ByteArray} {ct : Types.ComponentType Nat Core3Extern} :
    check F b = .ok ct ↔
      ((∃ c, decode F b = .ok (.ref c) ∧ checkCore3? F.feat c = .ok ct ∧ finish F c ct = .ok ct) ∨
        (∃ ds, decode F b = .ok (.ext ds) ∧ GcAbi.check? F.feat ds = .ok ct ∧
          finish F (GcAbi.GDef.toRefs ds) ct = .ok ct)) := by
  unfold check
  constructor
  · intro h
    split at h
    · cases h
    · next c hc =>
      split at h
      · cases h
      · next ct' hct => obtain ⟨rfl, -⟩ := finish_ok h; exact .inl ⟨c, hc, hct, h⟩
    · next ds hds =>
      split at h
      · cases h
      · next ct' hct => obtain ⟨rfl, -⟩ := finish_ok h; exact .inr ⟨ds, hds, hct, h⟩
  · rintro (⟨c, hc, hct, hf⟩ | ⟨ds, hds, hct, hf⟩)
    · rw [hc]; simp only [hct, hf]
    · rw [hds]; simp only [hct, hf]

/-- **Soundness**: an accepted binary is accepted by the specification. -/
theorem check_sound {F : CFlags} {b : ByteArray} {ct : Types.ComponentType Nat Core3Extern}
    (h : check F b = .ok ct) : ∃ c, Accepts F b c ct := by
  rcases check_ok_iff.mp h with ⟨c, hc, hct, hf⟩ | ⟨ds, hds, hct, hf⟩
  · obtain ⟨-, he, hg⟩ := finish_ok hf
    rcases decode_sound hc with ⟨c', hc', hdec⟩ | ⟨_, hbad, _⟩
    · cases hc'; exact ⟨c, .inl ⟨hdec, checkCore3?_sound hct⟩, he, hg⟩
    · cases hbad
  · obtain ⟨-, he, hg⟩ := finish_ok hf
    rcases decode_sound hds with ⟨_, hbad, _⟩ | ⟨ds', hds', hw⟩
    · cases hbad
    · cases hds'
      exact ⟨_, .inr ⟨ds, hw, rfl, GcAbi.check?_sound hct⟩, he, hg⟩

/-- Every core module of a component accepted through the reference path is a valid Core 3.0
module. -/
theorem check_module_valid {F : CFlags} {b : ByteArray} {c : RefComponent}
    {ct : Types.ComponentType Nat Core3Extern} (hd : decode F b = .ok (.ref c))
    (h : check F b = .ok ct) :
    DecodesAs F b c ∧ ∀ m ∈ c.coreModules, Silmaril.Wasm.Validation.ModuleValid m := by
  rcases check_ok_iff.mp h with ⟨c', hc, hct, _⟩ | ⟨_, hds, _⟩
  · rw [hd] at hc
    cases hc
    rcases decode_sound hd with ⟨c'', hc'', hdec⟩ | ⟨_, hbad, _⟩
    · cases hc''; exact ⟨hdec, (checkCore3?_sound hct).2⟩
    · cases hbad
  · rw [hd] at hds; cases hds

/-- A malformed verdict comes from the decoder. -/
theorem check_malformed {F : CFlags} {b : ByteArray} {e : String}
    (h : check F b = .error (.malformed e)) : decode F b = .error e := by
  unfold check at h
  split at h
  · next e' he => cases h; exact he
  · split at h
    · cases h
    · unfold finish at h; split at h <;> (try split at h) <;> cases h
  · split at h
    · cases h
    · unfold finish at h; split at h <;> (try split at h) <;> cases h

/-- The default flags are below `--features all`. -/
theorem default_le_all : CFlags.default.le CFlags.all := by
  refine ⟨?_, fun _ => rfl⟩
  unfold Features.le
  decide

end Silmaril.Wasm.Tools.Component.Validate
