module

public import Silmaril.Proofs.Wasm.Auto2.Valid.Step
public import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# The kernel validator is `validate?`

`nodupNames_eq`: the byte-list comparison of export names decides their distinctness;
`checkModuleK?_eq`: `checkModuleK? = checkModule?`; `checkersK_sound`: the checkers with the
fragment function checker are sound; `validK?_eq : validK? m = validate? m` (soundness of
`checkModule?` and completeness of `validate?`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Valid

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.Valid

theorem bytesNe_eq : ∀ (a b : List UInt8), bytesNe a b = !decide (a = b)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => by
    rw [bytesNe, bytesNe_eq a b]
    by_cases hxy : x = y
    · subst hxy
      simp [Nat.beq_refl]
    · have hne : x.toNat ≠ y.toNat := fun h => hxy (UInt8.toNat_inj.mp h)
      have hb : Nat.beq x.toNat y.toNat = false := by
        cases hq : Nat.beq x.toNat y.toNat
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) hne
      simp [hb, hxy]

theorem pwB_eq {α : Type} [DecidableEq α] :
    ∀ (l : List α), pwB (fun a b => !decide (a = b)) l = decide l.Nodup
  | [] => by simp [pwB]
  | a :: l => by
    have hall : ∀ l : List α, (l.all fun b => !decide (a = b)) = !decide (a ∈ l) := by
      intro l
      induction l with
      | nil => simp
      | cons b l ih =>
        simp only [List.all_cons, ih, List.mem_cons]
        by_cases h : a = b <;> simp [h]
    rw [pwB, pwB_eq l, hall]
    simp [List.nodup_cons]

theorem nodup_map_of_inj {α β : Type} {g : α → β} (hg : ∀ a b, g a = g b → a = b) :
    ∀ (l : List α), (l.map g).Nodup ↔ l.Nodup
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, nodup_map_of_inj hg l]
    constructor
    · rintro ⟨h, hl⟩
      exact ⟨fun ha => h ⟨a, ha, rfl⟩, hl⟩
    · rintro ⟨h, hl⟩
      refine ⟨?_, hl⟩
      rintro ⟨b, hb, hba⟩
      exact h (hg b a hba ▸ hb)

theorem nodupNames_eq (es : List Export) :
    nodupNames es = decide (es.map Export.name).Nodup := by
  have hf : (fun a b : List UInt8 => bytesNe a b) = fun a b => !decide (a = b) := by
    funext a b
    exact bytesNe_eq a b
  have hm : es.map (fun e => e.name.toByteArray.data.toList) =
      (es.map Export.name).map (fun s => s.toByteArray.data.toList) := by
    simp [Function.comp_def]
  have hinj : ∀ a b : String, a.toByteArray.data.toList = b.toByteArray.data.toList → a = b := by
    intro a b h
    exact String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp h))
  rw [nodupNames, show (bytesNe) = fun a b => !decide (a = b) from hf, pwB_eq, hm]
  simp only [decide_eq_decide]
  exact nodup_map_of_inj hinj _

theorem checkModuleK?_eq (K : ModuleCheckers) (m : Module) : checkModuleK? K m = checkModule? K m := by
  unfold checkModuleK? checkModule?
  simp only [nodupNames_eq, decide_eq_true_eq]

theorem checkersK_sound : checkersK.Sound :=
  { defaultCheckers_sound with
    func := fun {C f d} h => by
      simp only [checkersK, Bool.or_eq_true] at h
      rcases h with h | h
      · exact defaultCheckers_sound.func (funcCheck_of_funcF h)
      · exact defaultCheckers_sound.func h }

/-- **The kernel validator is `validate?`.** -/
theorem validK?_eq (m : Module) : validK? m = validate? m := by
  unfold validK?
  split
  · rename_i mt h
    rw [checkModuleK?_eq] at h
    exact (validate?_complete (checkModule?_sound checkersK_sound h)).symm
  · rfl

/-- The form a certificate uses: `validate?` succeeds when `validK?` does. -/
theorem validate?_isSome_of_validK {m : Module} (h : (validK? m).isSome = true) :
    (validate? m).isSome = true := by
  rwa [← validK?_eq]

end Silmaril.Proofs.Wasm.Auto2.Valid
