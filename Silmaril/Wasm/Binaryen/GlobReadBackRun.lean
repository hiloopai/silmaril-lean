module

public import Silmaril.Wasm.Binaryen.GlobReadBackStep
public import Silmaril.Wasm.Binaryen.GlobReadRun

@[expose] public section

/-! # Immutable-global substitution: backward runs for arbitrary numerical profiles

Every selected step, including its numerical or growth choice, has a positive
original simulation. Terminal literal results may need a final finite sequence of
original immutable-global reads. These give both terminating and infinite backward
simulation without deterministic reduction, confluence, or a fixed growth oracle.
-/

namespace Silmaril.Wasm.Binaryen.GlobRead.Back

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.Binaryen.InlR Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- Every chosen finite literal-side run has an original run with related final state. -/
theorem run_sim (hok : PrmOk p) {c d d' : Config H} (hd : Steps P closedHost d d')
    (hinvs : ∀ x, Steps P closedHost c x → GInv p.lk p.mi x.store)
    (hMR : MR p c d) (hSR : SR p c.store d.store) :
    ∃ c', Steps P closedHost c c' ∧ MR p c' d' ∧ SR p c'.store d'.store := by
  induction hd with
  | refl => exact ⟨c, .refl, hMR, hSR⟩
  | @tail x x' hx hs ih =>
    obtain ⟨cx, hc, hMRx, hSRx⟩ := ih
    obtain ⟨cx', hp, hMR', hSR'⟩ := sim hok (sizeOf x.code + 1) x x' cx
      (by omega) hs hMRx hSRx (hinvs cx hc)
    exact ⟨cx', hc.trans (steps_of_tg hp closedHost), hMR', hSR'⟩

/-- Completing the source's pending immutable reads preserves its store and frame. -/
theorem terminal {c d : Config H} {r : Result} (hinv : GInv p.lk p.mi c.store)
    (hMR : MR p c d) (hr : d.code = r.toAdmin) :
    ∃ c', Steps P closedHost c c' ∧ c'.code = r.toAdmin ∧ c'.store = c.store := by
  have hrel := hMR.2
  rw [hr] at hrel
  cases r with
  | values vs =>
    have hp := GL.prepare_values (P := P) hinv hrel
    exact ⟨⟨c.store, c.frame, vals vs⟩,
      hp.lift id (fun _ _ h => Step.of_noHost closedHost h), rfl, rfl⟩
  | trap =>
    have he := GL.abrupt_back (r := .trap) (by intro _ h; cases h) hrel
    exact ⟨c, .refl, he, rfl⟩
  | throw a =>
    have he := GL.abrupt_back (r := .throw a) (by intro _ h; cases h) hrel
    exact ⟨c, .refl, he, rfl⟩

/-- A selected infinite literal-side execution gives an infinite original execution. -/
theorem div_sim (hok : PrmOk p) {c d : Config H} (hd : Diverges P closedHost d)
    (hinvs : ∀ x, Steps P closedHost c x → GInv p.lk p.mi x.store)
    (hMR : MR p c d) (hSR : SR p c.store d.store) : Diverges P closedHost c := by
  refine InfiniteTrace.coinduct
    (fun y => ∃ x z, Steps P closedHost c z ∧ Diverges P closedHost x ∧ MR p z x ∧
      SR p z.store x.store ∧ Steps P closedHost y z) ?_
    ⟨d, c, .refl, hd, hMR, hSR, .refl⟩
  rintro y ⟨x, z, hz, hdx, hMRz, hSRz, hyz⟩
  rcases Relation.ReflTransGen.cases_head hyz with rfl | ⟨y₁, h₁, h₂⟩
  · obtain ⟨x₁, hs, hdx₁⟩ := InfiniteTrace.unfold hdx
    obtain ⟨z', hp, hMR', hSR'⟩ := sim hok (sizeOf x.code + 1) x x₁ y
      (by omega) hs hMRz hSRz (hinvs y hz)
    obtain ⟨z₁, h₁, h₂⟩ := Relation.TransGen.head'_iff.mp hp
    exact ⟨z₁, Step.of_noHost closedHost h₁, x₁, z',
      hz.trans (steps_of_tg hp closedHost), hdx₁, hMR', hSR',
      h₂.lift id (fun _ _ h => Step.of_noHost closedHost h)⟩
  · exact ⟨y₁, h₁, x, z, hz, hdx, hMRz, hSRz, h₂⟩

end Silmaril.Wasm.Binaryen.GlobRead.Back
