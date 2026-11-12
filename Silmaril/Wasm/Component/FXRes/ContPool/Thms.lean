module

public import Silmaril.Wasm.Component.FXRes.ContPool.Defs
public import Silmaril.Proofs.Wasm.Component.FXRes.ContPool.Move

/-!
# Continuations in the table or in a store, never both: results

Proofs in `Silmaril.Proofs.Wasm.Component.FXRes.ContPool.{Live,Step,Move}`, for every profile `P`
and every host-code type.

* `gstep_inv`: every step with its identity update keeps `GInv`; `pstep_lift`, `gstep_proj`:
  the pool steps are exactly the projections of the steps with identities;
* **`pool_identities`**: every run of the pool from an engine store with an empty table and no
  threads has its tracked identities (the run with identity updates, `GSteps`), and at its end
  distinct live locations have distinct identities;
* **`never_both`**: so no continuation identity is at the same time in the store of a thread
  and in the table, nor in two stores, nor in two table entries;
* `new_moves`, `take_moves`: `new` moves the identity of the store entry to the table entry it
  fills and kills the store entry; `take` moves the identity of the table entry to the new
  store entry and kills the table entry.

What is not claimed: the pool is an abstraction of the component machine's use of engine
threads; no theorem here is about runs of `Silmaril.Wasm.Component.Machine`. Its justification
is that the machine reaches the engine store only through the engine interface, whose
operations other than `Internal` keep the table (`ContEngine.prepareC_tab`, `allocHostC_tab`,
`memWriteC_tab`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContPool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (ContFX AdminFX)
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Component.FXRes Silmaril.Wasm.Component.FXRes.ContEngine
open Silmaril.Wasm.Component.Runtime (Table)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- Runs with identity updates keep the invariant. -/
theorem gsteps_inv {x y : Pool H × Ghost} (h : GSteps P x y) (hI : GInv x.1 x.2) : GInv y.1 y.2 := by
  induction h with
  | refl => exact hI
  | tail _ hs ih => exact gstep_inv hs ih

/-- Every run of the pool has its identity updates. -/
theorem psteps_lift {p p' : Pool H} (h : PSteps P p p') (g : Ghost) :
    ∃ g', GSteps P (p, g) (p', g') := by
  induction h with
  | refl => exact ⟨g, .refl⟩
  | tail _ hs ih =>
    obtain ⟨g₁, h₁⟩ := ih
    obtain ⟨g₂, h₂⟩ := pstep_lift hs g₁
    exact ⟨g₂, .tail h₁ h₂⟩

/-- **Tracked identities along every pool run.** -/
theorem pool_identities {c : Store (FXCode (CH H))} {p : Pool H} (h : PSteps P (Pool.init c) p) :
    ∃ g, GSteps P (Pool.init c, Ghost.init) (p, g) ∧ GInv p g := by
  obtain ⟨g, hg⟩ := psteps_lift h Ghost.init
  exact ⟨g, hg, gsteps_inv hg (ginv_init c)⟩

/-- **A continuation is in the table or in a store, never both.** -/
theorem never_both {p : Pool H} {g : Ghost} (hI : GInv p g) {i j n : ℕ}
    (hs : Live p (.store i j)) (ht : Live p (.tab n)) : g.id (.store i j) ≠ g.id (.tab n) :=
  fun he => Loc.noConfusion (hI.inj _ _ hs ht he)

/-- `new` moves the identity into the table and kills the store entry. -/
theorem new_moves {s : EStore H} {ts : List (Option (ThreadV (CH H)))} {g : Ghost} {i k n : ℕ}
    {t : ThreadV (CH H)} {K : KStore} {f : Frame} {code : List AdminFX}
    (hi : ts[i]? = some (some t)) :
    (g.move (.store i k) (.tab n)).id (.tab n) = g.id (.store i k) ∧
      ¬ Live ⟨s, ts.set i (some (.fx (K.set k none) f code))⟩ (.store i k) :=
  ⟨Function.update_self _ _ _, dead_after_new hi⟩

/-- `take` moves the identity into the store and kills the table entry. -/
theorem take_moves {s : Store (FXCode (CH H))} {tb tb' : Table ContFX}
    {ts : List (Option (ThreadV (CH H)))} {g : Ghost} {i N : ℕ} {K : KStore} {C : ContFX}
    (ht : tb.remove? N = some (C, tb')) (hwf : Silmaril.Wasm.Resource.FreeOK tb) :
    (g.move (.tab N) (.store i K.length)).id (.store i K.length) = g.id (.tab N) ∧
      ¬ Live ⟨⟨s, tb'⟩, ts⟩ (.tab N) :=
  ⟨Function.update_self _ _ _, dead_after_take ht hwf⟩

/-- info: 'Silmaril.Wasm.Component.FXRes.ContPool.pool_identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pool_identities

end Silmaril.Wasm.Component.FXRes.ContPool
