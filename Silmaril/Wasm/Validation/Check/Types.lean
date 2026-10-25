module

public import Silmaril.Wasm.Validation.Modules

@[expose] public section

/-! # Checker for the module type section (`Types_ok`)

`typesCheck? recOk C rts` follows the `TypesOk.cons` recursion, parametrised over
a group checker `recOk` for `Rectype_ok: C ⊢ rectype : OK(x)`.
-/

namespace Silmaril.Wasm.Validation

/-- Computable `Types_ok`, parametric in a `Rectype_ok` checker. -/
def typesCheck? (recOk : Context → List SubType → Nat → Bool) :
    Context → List RecType → Option (List DefType)
  | _, [] => some []
  | C, rt :: rts =>
    let C' : Context := { C with types := C.types ++ C.rollGroup rt }
    if recOk C' rt.types C.types.length then
      (typesCheck? recOk C' rts).map (C.rollGroup rt ++ ·)
    else none

theorem typesCheck?_sound {recOk : Context → List SubType → Nat → Bool}
    (hrec : ∀ C sts x, recOk C sts x = true → RecTypeOkAt C sts x) :
    ∀ {C : Context} {rts : List RecType} {dts : List DefType},
      typesCheck? recOk C rts = some dts → TypesOk C rts dts
  | C, [], dts, h => by
    simp only [typesCheck?, Option.some.injEq] at h
    subst h; exact .nil
  | C, rt :: rts, dts, h => by
    simp only [typesCheck?] at h
    split at h
    · rename_i hok
      cases hr : typesCheck? recOk { C with types := C.types ++ C.rollGroup rt } rts with
      | none => simp [hr] at h
      | some ds =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        exact .cons (hrec _ _ _ hok) (typesCheck?_sound hrec hr)
    · exact absurd h (by simp)

theorem typesCheck?_complete {recOk : Context → List SubType → Nat → Bool}
    (hrec : ∀ C sts x, RecTypeOkAt C sts x → recOk C sts x = true)
    {C : Context} {rts : List RecType} {dts : List DefType}
    (h : TypesOk C rts dts) : typesCheck? recOk C rts = some dts := by
  induction h with
  | nil => rfl
  | cons hok _ ih =>
    simp only [typesCheck?, hrec _ _ _ hok, ite_true, ih, Option.map_some]

/-- Soundness and completeness together. -/
theorem typesCheck?_iff {recOk : Context → List SubType → Nat → Bool}
    (hrec : ∀ C sts x, recOk C sts x = true ↔ RecTypeOkAt C sts x)
    {C : Context} {rts : List RecType} {dts : List DefType} :
    typesCheck? recOk C rts = some dts ↔ TypesOk C rts dts :=
  ⟨typesCheck?_sound (fun C s x => (hrec C s x).1),
   typesCheck?_complete (fun C s x => (hrec C s x).2)⟩

/-- `typesCheck?` from the empty context on a module's type section. -/
def typesCheckEmpty? (recOk : Context → List SubType → Nat → Bool) (m : Module) :
    Option (List DefType) :=
  typesCheck? recOk {} m.types

theorem typesCheckEmpty?_sound {recOk : Context → List SubType → Nat → Bool}
    (hrec : ∀ C sts x, recOk C sts x = true → RecTypeOkAt C sts x)
    {m : Module} {dts : List DefType} (h : typesCheckEmpty? recOk m = some dts) :
    TypesOk {} m.types dts :=
  typesCheck?_sound hrec h

theorem typesCheckEmpty?_complete {recOk : Context → List SubType → Nat → Bool}
    (hrec : ∀ C sts x, RecTypeOkAt C sts x → recOk C sts x = true)
    {m : Module} {dts : List DefType} (h : TypesOk {} m.types dts) :
    typesCheckEmpty? recOk m = some dts :=
  typesCheck?_complete hrec h

/-- Completeness in existential form: if some `dts` validates, the checker finds it
(and by `TypesOk.det` it is the unique one). -/
theorem typesCheck?_isSome_iff {recOk : Context → List SubType → Nat → Bool}
    (hrec : ∀ C sts x, recOk C sts x = true ↔ RecTypeOkAt C sts x)
    {C : Context} {rts : List RecType} :
    (typesCheck? recOk C rts).isSome ↔ ∃ dts, TypesOk C rts dts := by
  constructor
  · intro h
    obtain ⟨dts, hd⟩ := Option.isSome_iff_exists.1 h
    exact ⟨dts, (typesCheck?_iff hrec).1 hd⟩
  · rintro ⟨dts, hd⟩
    rw [(typesCheck?_iff hrec).2 hd]; rfl

end Silmaril.Wasm.Validation
