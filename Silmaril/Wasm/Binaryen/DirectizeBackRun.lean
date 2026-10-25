module

public import Silmaril.Wasm.Binaryen.DirectizeBackStep
public import Silmaril.Wasm.Binaryen.DirectizeRun

@[expose] public section

/-! # Directize: backward runs for arbitrary numerical profiles

Each actual target step has a positive source match, including numerical and
growth choices. Stable terminal configurations already have identical results.
-/

namespace Silmaril.Wasm.Binaryen.DirSim.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {ok : SiteOk} {mi : ModuleInst} {P : Numerics.Profile}

/-- Every chosen finite target run has an original run with related final state. -/
theorem run_sim {c d d' : Config H} (hd : Steps P closedHost d d')
    (hinvs : ∀ x, Steps P closedHost c x → DInv ok mi x.store)
    (hMR : MR ok mi c d) (hSR : SR ok mi c.store d.store) :
    ∃ c', Steps P closedHost c c' ∧ MR ok mi c' d' ∧ SR ok mi c'.store d'.store := by
  induction hd with
  | refl => exact ⟨c, .refl, hMR, hSR⟩
  | @tail x x' hx hs ih =>
    obtain ⟨cx, hc, hMRx, hSRx⟩ := ih
    obtain ⟨cx', hp, hMR', hSR'⟩ := sim (sizeOf x.code + 1) x x' cx
      (by omega) hs hMRx hSRx (hinvs cx hc)
    exact ⟨cx', hc.trans (steps_of_tg hp closedHost), hMR', hSR'⟩

/-- Stable original code has exactly the selected terminal target result. -/
theorem terminal_code {c d : Config H} {r : Result} (hMR : MR ok mi c d)
    (hr : d.code = r.toAdmin) : c.code = r.toAdmin := by
  have hrel := hMR.2
  rw [hr] at hrel
  cases r with
  | values vs => exact GL.values_back hrel
  | trap => exact GL.abrupt_back (r := .trap) (by intro _ h; cases h) hrel
  | throw a => exact GL.abrupt_back (r := .throw a) (by intro _ h; cases h) hrel

/-- A selected infinite target execution gives an infinite original execution. -/
theorem div_sim {c d : Config H} (hd : Diverges P closedHost d)
    (hinvs : ∀ x, Steps P closedHost c x → DInv ok mi x.store)
    (hMR : MR ok mi c d) (hSR : SR ok mi c.store d.store) : Diverges P closedHost c := by
  refine InfiniteTrace.coinduct
    (fun y => ∃ x z, Steps P closedHost c z ∧ Diverges P closedHost x ∧ MR ok mi z x ∧
      SR ok mi z.store x.store ∧ Steps P closedHost y z) ?_
    ⟨d, c, .refl, hd, hMR, hSR, .refl⟩
  rintro y ⟨x, z, hz, hdx, hMRz, hSRz, hyz⟩
  rcases Relation.ReflTransGen.cases_head hyz with rfl | ⟨y₁, h₁, h₂⟩
  · obtain ⟨x₁, hs, hdx₁⟩ := InfiniteTrace.unfold hdx
    obtain ⟨z', hp, hMR', hSR'⟩ := sim (sizeOf x.code + 1) x x₁ y
      (by omega) hs hMRz hSRz (hinvs y hz)
    obtain ⟨z₁, h₁, h₂⟩ := Relation.TransGen.head'_iff.mp hp
    exact ⟨z₁, Step.of_noHost closedHost h₁, x₁, z',
      hz.trans (steps_of_tg hp closedHost), hdx₁, hMR', hSR',
      h₂.lift id (fun _ _ h => Step.of_noHost closedHost h)⟩
  · exact ⟨y₁, h₁, x, z, hz, hdx, hMRz, hSRz, h₂⟩

end Silmaril.Wasm.Binaryen.DirSim.Back
