module

public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Sound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSound
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.LinkSoundSeq

/-!
# Soundness of two linked components over `core3R P V IR`

`link2Sound_core3R`, `link2SoundSeq_core3R`: the engine `core3R P V IR` (Core 3.0 with validity
`V` and an internal step `IR` contained in `InternalP P`) has `Link2Sound` and `Link2SoundSeq`;
hence so has every restriction `restrict (core3P P) r` of the Core 3.0 engine
(`link2Sound_restrict_core3P`, `link2SoundSeq_restrict_core3P`), which is `core3R P _ _` by
definition.

The proofs are `linked2_sound` and `linked2_sound_seq` of the `Core3R.Link` copies of the
`Reference` linked-soundness chain, which take `Sub P IR` as an instance `Fact (Sub P IR)`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Numerics (Profile)

/-- **Soundness of two linked components over `core3R P V IR`**, for an internal step
contained in `InternalP P`. -/
theorem link2Sound_core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (hIR : Sub P IR) :
    Link2Sound (core3R P V IR) id P := by
  have : Fact (Sub P IR) := ⟨hIR⟩
  intro prof l hEg hEi hIg hIi har hff hW hN hn hS σ impl h₀ j vs hvs b hb
  have hm : Silmaril.Wasm.Component.Syntax.Component.map (N := (core3R P V IR).Module) id
      l.toRef = l.toRef := Silmaril.Wasm.Component.Syntax.Component.map_id _
  erw [hm, ← linkHost_eq] at hb
  exact linked2_sound P prof l hEg hEi hIg hIi har hff hW hN hn hS impl h₀ j vs hvs b hb

/-- **Soundness of two linked components for sequences of calls over `core3R P V IR`**, for an
internal step contained in `InternalP P`. -/
theorem link2SoundSeq_core3R (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (hIR : Sub P IR) :
    Link2SoundSeq (core3R P V IR) id P := by
  have : Fact (Sub P IR) := ⟨hIR⟩
  intro prof l hEg hEi hIg hIi har hff hW hN hn hS σ impl h₀ calls j vs ht hvs p hp
  have hm : Silmaril.Wasm.Component.Syntax.Component.map (N := (core3R P V IR).Module) id
      l.toRef = l.toRef := Silmaril.Wasm.Component.Syntax.Component.map_id _
  erw [hm, ← linkHost_eq] at hp
  exact linked2_sound_seq P prof l hEg hEi hIg hIi har hff hW hN hn hS impl h₀ calls j vs ht hvs
    p hp

/-- **Every restriction of the Core 3.0 engine has soundness of two linked components.** -/
theorem link2Sound_restrict_core3P (P : Profile) (r : Restriction (core3P P)) :
    Link2Sound (restrict (core3P P) r) id P :=
  link2Sound_core3R P (fun m => (core3P P).Valid m ∧ r.Mod m)
    (fun c c' => (core3P P).Internal c c' ∧ r.Rt c') (sub_restrict P r)

/-- **Every restriction of the Core 3.0 engine has soundness of two linked components for
sequences of calls.** -/
theorem link2SoundSeq_restrict_core3P (P : Profile) (r : Restriction (core3P P)) :
    Link2SoundSeq (restrict (core3P P) r) id P :=
  link2SoundSeq_core3R P (fun m => (core3P P).Valid m ∧ r.Mod m)
    (fun c c' => (core3P P).Internal c c' ∧ r.Rt c') (sub_restrict P r)

end Silmaril.Proofs.Wasm.Component.Param.Core3R
