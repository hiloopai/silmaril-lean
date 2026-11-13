module

public import Silmaril.Cerberus.GeneralizedTypes.Defs
public import Silmaril.Cerberus.Target.Thms

@[expose] public section
namespace Silmaril.Cerberus.GeneralizedTypes
open Silmaril.Cerberus
open Target

/-- Successful literal selection returns an actual candidate whose target range
contains the value, including both signed endpoints. -/
theorem firstRepresentable_sound (config : Config) (env : Environment) (loc : Loc)
    (value : Int) (candidates : List IntegerType) (type : IntegerType)
    (accepted : firstRepresentable config env loc value candidates = .ok type) :
    type ∈ candidates ∧ ∃ range,
      integerRange config env type = .ok range ∧ range.lower ≤ value ∧ value ≤ range.upper := by
  induction candidates with
  | nil =>
      have impossible : (Except.error (.untypableIntegerConstant loc value) :
          Except Error IntegerType) = .ok type := accepted
      cases impossible
  | cons candidate rest ih =>
      show type ∈ candidate :: rest ∧ ∃ range,
        integerRange config env type = .ok range ∧ range.lower ≤ value ∧ value ≤ range.upper
      cases hr : integerRange config env candidate with
      | error error =>
          simp only [firstRepresentable, hr] at accepted
          change Except.error error = Except.ok type at accepted
          cases accepted
      | ok range =>
          show type ∈ candidate :: rest ∧ ∃ range,
            integerRange config env type = .ok range ∧ range.lower ≤ value ∧ value ≤ range.upper
          simp only [firstRepresentable, hr] at accepted
          change (if range.contains value then Except.ok candidate
            else firstRepresentable config env loc value rest) = .ok type at accepted
          by_cases contains : range.contains value = true
          · have selected : (Except.ok candidate : Except Error IntegerType) = .ok type := by
              simpa only [ite_eq_left contains] using accepted
            have same : candidate = type := Except.ok.inj selected
            have bounds : integerRange config env type = .ok range := same ▸ hr
            exact ⟨List.mem_cons.mpr (.inl same.symm), range, bounds,
              (contains_eq_true range value).mp contains⟩
          · have tail : firstRepresentable config env loc value rest = .ok type := by
              simpa only [ite_eq_right contains] using accepted
            obtain ⟨member, found, bounds, lower, upper⟩ := ih tail
            exact ⟨List.mem_cons_of_mem candidate member, found, bounds, lower, upper⟩

theorem typeOfConstant_representable (config : Config) (env : Environment) (loc : Loc)
    (value : Int) (basis : Ail.Basis) (suffix : Option Ail.IntegerSuffix) (type : IntegerType)
    (accepted : typeOfConstant config env loc (.iconstant value basis suffix) = .ok type) :
    type ∈ constantCandidates basis suffix ∧ ∃ range,
      integerRange config env type = .ok range ∧ range.lower ≤ value ∧ value ≤ range.upper :=
  firstRepresentable_sound config env loc value (constantCandidates basis suffix) type accepted

/-- Input order matters: the earliest representable type is selected. -/
theorem firstRepresentable_head (config : Config) (env : Environment) (loc : Loc)
    (value : Int) (type : IntegerType) (rest : List IntegerType) (range : IntegerRange)
    (bounds : integerRange config env type = .ok range)
    (contains : range.lower ≤ value ∧ value ≤ range.upper) :
    firstRepresentable config env loc value (type :: rest) = .ok type := by
  have hc : range.contains value = true := (contains_eq_true range value).mpr contains
  simp only [firstRepresentable, bounds]
  change (if range.contains value then Except.ok type
    else firstRepresentable config env loc value rest) = .ok type
  rw [ite_eq_left hc]

/-- Interpretation retains an existing lvalue type and its register flag. -/
theorem interpretCategory_lvalue (config : Config) (env : Environment) (loc : Loc)
    (qs : Qualifiers) (type : Ctype) (register : Bool) :
    interpretCategory config env loc (.lvalue qs type register) =
      .ok (.lvalue qs type register) := rfl

/-- CHERI promotions cannot accidentally use the default conversion algorithm. -/
theorem promote_rejects_cheri (config : Config) (env : Environment) (type : IntegerType)
    (cheri : config.cheri = true) : promote config env type = .error .unsupportedCheri := by
  simp [promote, cheri]
  rfl

theorem usualInteger_rejects_cheri (config : Config) (env : Environment)
    (first second : IntegerType) (cheri : config.cheri = true) :
    usualInteger config env first second = .error .unsupportedCheri := by
  simp [usualInteger, cheri]
  rfl

end Silmaril.Cerberus.GeneralizedTypes
