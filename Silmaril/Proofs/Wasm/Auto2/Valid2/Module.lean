module

public import Silmaril.Proofs.Wasm.Auto2.Valid2.Step
public import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# The extended kernel validator is `validate?`

`funcCheck_of_funcBodyG`: the fast function checker implies the default one when the type is the
one looked up; `checkersX_sound`; `encB_inj`, `nodupNamesN_eq`: export names compared as numbers;
`checkModuleG?_sound : checkModuleG? m = some mt → checkModule? checkersX m = some mt` (the type
comparison `checkModuleG?` omits holds for the types `checkModule?` looked up, and the
precomputed expansions are those of these types); **`validG?_eq : validG? m = validate? m`**.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Valid2

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.Valid Silmaril.Wasm.Auto2.Valid2
open Silmaril.Proofs.Wasm.Auto2.Valid

/-! ## Functions -/

/-- **The fast function checker implies the default one** (for the looked-up type). -/
theorem funcCheck_of_funcBodyG {C : Context} {f : Func} {d : DefType}
    (hd : C.type? f.type = some d) (h : funcBodyG C f d.expand? = true) :
    defaultCheckers.func C f d = true := by
  show funcCheck tyOkC exprC C f d = true
  unfold funcBodyG at h
  unfold funcCheck
  simp only [hd, ↓reduceIte]
  split at h
  · rename_i ps rs hx
    rw [hx]
    split at h
    · rename_i lts hl
      simp only [hl]
      exact exprC_of_exprG h
    · cases h
  · cases h

theorem checkersX_sound : checkersX.Sound :=
  { defaultCheckers_sound with
    func := fun {C f d} h => by
      simp only [checkersX, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hd, h⟩ | h
      · exact defaultCheckers_sound.func (funcCheck_of_funcBodyG hd h)
      · exact defaultCheckers_sound.func h }

/-- `allPairs` is monotone along a relation the two lists satisfy pointwise. -/
theorem allPairs_mono {α β : Type} {R : α → β → Prop} {p q : α → β → Bool}
    (hpq : ∀ a b, R a b → p a b = true → q a b = true) :
    ∀ {as : List α} {bs : List β}, List.Forall₂ R as bs → allPairs p as bs = true →
      allPairs q as bs = true
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, .cons hr hrs, h => by
    simp only [allPairs, Bool.and_eq_true] at h ⊢
    exact ⟨hpq _ _ hr h.1, allPairs_mono hpq hrs h.2⟩

/-- The fast function check of a module function implies `checkersX`'s, for the types and
expansions `checkModuleG?` computed. -/
theorem funcG_imp {dts : List DefType} {C : Context} (hC : C.types = dts) {f : Func}
    {d : DefType} (hf : ({ types := dts } : Context).type? f.type = some d)
    (h : funcG (dts.map DefType.expand?) C f d = true) : checkersX.func C f d = true := by
  have hd : C.type? f.type = some d := by
    simp only [Context.type?, hC] at hf ⊢
    exact hf
  have hx : ((dts.map DefType.expand?)[f.type.toNat]?).join = d.expand? := by
    simp only [Context.type?] at hf
    simp [List.getElem?_map, hf]
  simp only [funcG, hx] at h
  simp only [checkersX, hd, decide_true, Bool.true_and]
  exact h

/-! ## Export names -/

theorem encB_inj : ∀ {a b : List UInt8}, encB a = encB b → a = b
  | [], [], _ => rfl
  | [], y :: r, h => by simp only [encB] at h; omega
  | x :: l, [], h => by simp only [encB] at h; omega
  | x :: l, y :: r, h => by
    simp only [encB] at h
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    have hxy : x.toNat = y.toNat := by omega
    have hlr : encB l = encB r := by omega
    rw [UInt8.toNat_inj.mp hxy, encB_inj hlr]

theorem nodupNamesN_eq (es : List Export) :
    nodupNamesN es = decide (es.map Export.name).Nodup := by
  have hf : (fun a b : Nat => !Nat.beq a b) = fun a b => !decide (a = b) := by
    funext a b
    by_cases h : a = b
    · subst h
      simp [Nat.beq_refl]
    · have hb : Nat.beq a b = false := by
        cases hq : Nat.beq a b
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) h
      simp [hb, h]
  have hm : es.map (fun e => encB e.name.toByteArray.data.toList) =
      (es.map Export.name).map (fun s => encB s.toByteArray.data.toList) := by
    simp [Function.comp_def]
  have hinj : ∀ a b : String,
      encB a.toByteArray.data.toList = encB b.toByteArray.data.toList → a = b := by
    intro a b h
    exact String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp (encB_inj h)))
  rw [nodupNamesN, hf, pwB_eq, hm]
  simp only [decide_eq_decide]
  exact nodup_map_of_inj hinj _

/-! ## The module -/

/-- **`checkModuleG?` gives what `checkModule? checkersX` gives.** -/
theorem checkModuleG?_sound {m : Module} {mt : CModuleType} (h : checkModuleG? m = some mt) :
    checkModule? checkersX m = some mt := by
  unfold checkModuleG? at h
  unfold checkModule?
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨dts, hdts, xtI, hxtI, fdts, hfdts, jts, hjts, gts, hgts, tts, htts, h⟩ := h
  refine ⟨dts, hdts, xtI, hxtI, fdts, hfdts, jts, hjts, gts, hgts, tts, htts, ?_⟩
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hmem, hfun⟩, hdat⟩, hel⟩, hst⟩ := hc
    have hfa := List.mapM_some_forall₂ (R := fun f d => ({ types := dts } : Context).type? f.type =
      some d) id hfdts
    have hfun' := allPairs_mono (fun f d hr hp => funcG_imp rfl hr hp) hfa hfun
    simp only [hmem, hfun', hdat, hel, hst, Bool.and_self, ↓reduceIte]
    simp only [Option.bind_eq_some_iff] at h ⊢
    obtain ⟨xtE, hx, h⟩ := h
    refine ⟨xtE, hx, ?_⟩
    rw [nodupNamesN_eq] at h
    simpa using h
  · cases h

/-- **The extended kernel validator is `validate?`.** -/
theorem validG?_eq (m : Module) : validG? m = validate? m := by
  unfold validG?
  split
  · rename_i mt h
    exact (validate?_complete (checkModule?_sound checkersX_sound (checkModuleG?_sound h))).symm
  · rfl

/-- The form a certificate uses: `validate?` succeeds when `validG?` does. -/
theorem validate?_isSome_of_validG {m : Module} (h : (validG? m).isSome = true) :
    (validate? m).isSome = true := by
  rwa [← validG?_eq]

end Silmaril.Proofs.Wasm.Auto2.Valid2
