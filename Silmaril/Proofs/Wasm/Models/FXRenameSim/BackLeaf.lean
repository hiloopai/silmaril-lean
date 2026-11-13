module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.Inv

/-!
# Exception renaming, backward: the variable and reference families

A step of a leaf family from the renamed configuration `⟨t, rnFrame n f, rnAdmins n L⟩` is the
renamed image of a step of the same rule from `⟨s, f, L⟩` (`BackOf`).

Each case analysis is stated over a configuration `c` together with the equation
`⟨t, rnFrame n f, rnAdmins n L⟩ = c` (`…_rn_back_of`), so that `cases` on the step leaves the
equation for `rn_inv` to read back. A store lookup of the target is pulled back to the source as
an equation `rnX n x₀ = x` that is rewritten in the goal, not substituted.

Refined from the earlier `Silmaril.Raw.Wasm.Models.FXRenameSim.BackLeaf`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename

variable {H : Type} {P : Profile} {n : Nat} {s t : Store H} {f : Frame} {L : List Admin}

/-- The conclusion of a backward leaf lemma: a step of `R` from `⟨s, f, L⟩` whose renamed
successor, over an `ExnRen n` store, is `d`. -/
def BackOf (R : Config H → Config H → Prop) (n : Nat) (s : Store H) (f : Frame) (L : List Admin)
    (d : Config H) : Prop :=
  ∃ (s' : Store H) (f' : Frame) (L' : List Admin) (t' : Store H),
    R ⟨s, f, L⟩ ⟨s', f', L'⟩ ∧ d = ⟨t', rnFrame n f', rnAdmins n L'⟩ ∧ ExnRen n s' t'

theorem backOf_intro {R : Config H → Config H → Prop} {s' t' : Store H} {f' : Frame}
    {L' : List Admin} {d : Config H} (hR : R ⟨s, f, L⟩ ⟨s', f', L'⟩)
    (hd : d = ⟨t', rnFrame n f', rnAdmins n L'⟩) (h' : ExnRen n s' t') : BackOf R n s f L d :=
  ⟨s', f', L', t', hR, hd, h'⟩

/-- Close the configuration equation of a backward step. -/
macro "rn_fin" : tactic => `(tactic| first | rfl | (rn_simp; done) |
  simp [rnGlobal, rnTable, rnElem, rnStruct, rnArray, rnExn])

theorem rnRef_ne_null_back {r : Ref} (h : rnRef n r ≠ .null) : r ≠ .null :=
  fun h' => h (by rw [h']; rfl)

/-! ## Variables -/

section Variable

variable (h : ExnRen n s t)
include h

theorem localGet_rn_back {x : LocalIdx} {v : Val}
    (hl : (rnFrame n f).local? x = some (some v)) :
    BackOf VariableStep n s f [.plain (.localGet x)] ⟨t, rnFrame n f, [v.toAdmin]⟩ := by
  obtain ⟨v₀, hv₀, hv⟩ := local_rn_back hl
  have hd : (⟨t, rnFrame n f, [v.toAdmin]⟩ : Config H) =
      ⟨t, rnFrame n f, rnAdmins n [v₀.toAdmin]⟩ := by
    rw [← hv]; rn_fin
  exact backOf_intro (.localGet hv₀) hd h

theorem globalGet_rn_back {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hl : t.global? (rnFrame n f) x = some (a, g)) :
    BackOf VariableStep n s f [.plain (.globalGet x)] ⟨t, rnFrame n f, [g.value.toAdmin]⟩ := by
  obtain ⟨g₀, hg₀, hg⟩ := global_rn_back h hl
  have hd : (⟨t, rnFrame n f, [g.value.toAdmin]⟩ : Config H) =
      ⟨t, rnFrame n f, rnAdmins n [g₀.value.toAdmin]⟩ := by
    rw [← hg]; rn_fin
  exact backOf_intro (.globalGet hg₀) hd h

end Variable

theorem variable_rn_back_of (h : ExnRen n s t) {c d : Config H} (step : VariableStep c d)
    (hc : (⟨t, rnFrame n f, rnAdmins n L⟩ : Config H) = c) : BackOf VariableStep n s f L d := by
  cases step with
  | localGet hl => rn_inv hc; exact localGet_rn_back h hl
  | localSet hx =>
    rn_inv hc
    refine backOf_intro (.localSet (by rwa [rnFrame_locals_length] at hx)) ?_ h
    rw [rnFrame_setLocal]; rn_fin
  | localTee => rn_inv hc; exact backOf_intro .localTee (by rn_fin) h
  | globalGet hl => rn_inv hc; exact globalGet_rn_back h hl
  | globalSet hl =>
    rn_inv hc
    obtain ⟨g₀, hg₀, -⟩ := global_rn_back h hl
    exact backOf_intro (.globalSet hg₀) (by rn_fin) (setGlobal_rn h _ _)

theorem variable_rn_back (h : ExnRen n s t) {d : Config H}
    (step : VariableStep ⟨t, rnFrame n f, rnAdmins n L⟩ d) : BackOf VariableStep n s f L d :=
  variable_rn_back_of h step rfl

/-! ## References -/

theorem eqTrue_rn_back (h : ExnRen n s t) {r₁ r₂ : Ref} (hn : rnRef n r₁ ≠ .null)
    (he : rnRef n r₂ = rnRef n r₁) :
    BackOf RefStep n s f [.ref r₁, .ref r₂, .plain .refEq] ⟨t, rnFrame n f, [constI32 1]⟩ := by
  have hr : r₂ = r₁ := rnRef_injective n he
  rw [hr]
  exact backOf_intro (.eqTrue (rnRef_ne_null_back hn)) (by rn_fin) h

theorem reference_rn_back_of (h : ExnRen n s t) {c d : Config H} (step : RefStep c d)
    (hc : (⟨t, rnFrame n f, rnAdmins n L⟩ : Config H) = c) : BackOf RefStep n s f L d := by
  cases step with
  | refNull ht => rn_inv hc; exact backOf_intro (.refNull ht) (by rn_fin) h
  | refFunc hf => rn_inv hc; exact backOf_intro (.refFunc hf) (by rn_fin) h
  | refI31 i => rn_inv hc; exact backOf_intro (.refI31 i) (by rn_fin) h
  | isNullTrue => rn_inv hc; exact backOf_intro .isNullTrue (by rn_fin) h
  | isNullFalse hn =>
    rn_inv hc; exact backOf_intro (.isNullFalse (rnRef_ne_null_back hn)) (by rn_fin) h
  | asNonNullNull => rn_inv hc; exact backOf_intro .asNonNullNull (by rn_fin) h
  | asNonNullAddr hn =>
    rn_inv hc; exact backOf_intro (.asNonNullAddr (rnRef_ne_null_back hn)) (by rn_fin) h
  | eqNull => rn_inv hc; exact backOf_intro .eqNull (by rn_fin) h
  | eqTrue hn =>
    rn_inv hc
    exact eqTrue_rn_back h hn (by assumption)
  | eqFalse hn =>
    rn_inv hc
    exact backOf_intro (.eqFalse (fun he => hn (by rw [he]))) (by rn_fin) h
  | testTrue hv => rn_inv hc; exact backOf_intro (.testTrue (refOk_rn_back h hv)) (by rn_fin) h
  | testFalse hv =>
    rn_inv hc; exact backOf_intro (.testFalse (fun hv' => hv (refOk_rn h hv'))) (by rn_fin) h
  | castSucceed hv =>
    rn_inv hc; exact backOf_intro (.castSucceed (refOk_rn_back h hv)) (by rn_fin) h
  | castFail hv =>
    rn_inv hc; exact backOf_intro (.castFail (fun hv' => hv (refOk_rn h hv'))) (by rn_fin) h
  | i31GetNull sx => rn_inv hc; exact backOf_intro (.i31GetNull sx) (by rn_fin) h
  | i31GetNum sx i => rn_inv hc; exact backOf_intro (.i31GetNum sx i) (by rn_fin) h
  | externConvertNull => rn_inv hc; exact backOf_intro .externConvertNull (by rn_fin) h
  | externConvertAddr hn =>
    rn_inv hc; exact backOf_intro (.externConvertAddr (rnRef_ne_null_back hn)) (by rn_fin) h
  | anyConvertNull => rn_inv hc; exact backOf_intro .anyConvertNull (by rn_fin) h
  | anyConvertAddr r => rn_inv hc; exact backOf_intro (.anyConvertAddr _) (by rn_fin) h

theorem reference_rn_back (h : ExnRen n s t) {d : Config H}
    (step : RefStep ⟨t, rnFrame n f, rnAdmins n L⟩ d) : BackOf RefStep n s f L d :=
  reference_rn_back_of h step rfl

end Silmaril.Proofs.Wasm.Models.FXRenameSim
