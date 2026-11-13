module

public import Silmaril.Wasm.Wasmi.Observed.Defs
public import Silmaril.Wasm.Wasmi.Thms
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# The constant-expression gap (proofs)

`gapMod` (`global.wast:373`) validates with no imports and allocates, with every global `0`
(kernel evaluations of silmaril-lean's validator and `prepare?`), so Core 3.0 instantiates it at
every profile and host (`Silmaril.Proofs.Wasm.Wasmi.instantiate_of`, through the header
`Silmaril.Wasm.Wasmi.Thms`); it is not `ConstOk`, so wasmi's `instantiate?` refuses it. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Wasmi.Observed

theorem gap_checks :
    ((Validation.validate? gapMod).map fun mt => mt.imports.isEmpty) = some true ∧
      ((prepare? evalConst? ({} : Store Empty) gapMod []).map fun p =>
        (p.2.isNone, decide (∀ g ∈ p.1.store.globals, g.value = Val.i32 0))) =
        some (true, true) ∧
      ConstOk gapMod = false := by
  decide +kernel

/-- **Core 3.0 instantiates `gapMod`**, at every profile and host, with every global `0`. -/
theorem gap_core (P : Profile) (host : HostSemantics Empty) :
    ∃ c : Config Empty, Instantiate P host ({} : Store Empty) gapMod [] c ∧
      ∀ g ∈ c.store.globals, g.value = Val.i32 0 := by
  obtain ⟨hv, hp, -⟩ := gap_checks
  rcases h : prepare? evalConst? ({} : Store Empty) gapMod [] with _ | p
  · rw [h] at hp
    cases hp
  · rw [h] at hp
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨hst, hg⟩ := hp
    exact ⟨p.1, Silmaril.Proofs.Wasm.Wasmi.instantiate_of hv h (Option.isNone_iff_eq_none.mp hst)
      P host, of_decide_eq_true hg⟩

/-- **wasmi refuses `gapMod`.** -/
theorem gap_wasmi : Silmaril.Wasm.Wasmi.Observed.instantiate? ({} : Store Empty) gapMod = none := by
  simp [Silmaril.Wasm.Wasmi.Observed.instantiate?, gap_checks.2.2]

end Silmaril.Proofs.Wasm.Wasmi.Observed
