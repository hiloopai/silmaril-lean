module

public import Silmaril.Machine.Abi.Conformance.Lens.Defs
public import Silmaril.Proofs.Machine.Abi.Conformance.Basic

/-! # The machine lens: proofs for `Conformance.Lens.Thms` -/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.Lens

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Lens
open Silmaril.Proofs.Machine.Abi.Conformance
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (State MState Word)
open Silmaril.X86.FnContract (RunsIn)

/-! ## No laundering -/

/-- The entry state of the laundering test: `blank` with the direction flag set. -/
def sUp : Ffi.State := { blank with direction := true }

/-- A different integer state: `rip = 1`. -/
def yOne : MState := ⟨{ blank.machine.core with rip := 1 }, blank.machine.memory⟩

theorem yOne_ne : yOne ≠ sUp.machine := fun h => by
  have := congrArg (fun m : MState => m.core.rip) h
  exact absurd this (by decide)

theorem launder_of_ne {s : Ffi.State} {y : MState} (h : y ≠ s.machine) :
    launder s y = { s with machine := y, direction := false, x87Mode := true } := by
  unfold launder; simp [h]

theorem launder_self (s : Ffi.State) : launder s s.machine = s := by
  unfold launder; simp

theorem launder_direction : (launder sUp yOne).direction ≠ sUp.direction := by
  rw [launder_of_ne yOne_ne]
  decide

/-- **The laundering store is the store of no machine**, through any map of integer states
into the machine's states: it violates put-put (`Mach.store_store`). -/
theorem launder_not_store (M : Mach) (e : MState → M.σ) :
    ¬ ∀ s y, M.store s (e y) = launder s y := by
  intro h
  have h1 := Mach.store_store M sUp (e yOne) (e sUp.machine)
  rw [h, h, h, launder_self, launder_of_ne yOne_ne,
    launder_of_ne (s := { sUp with machine := yOne, direction := false, x87Mode := true })
      (y := sUp.machine) (fun h => yOne_ne h.symm)] at h1
  have := congrArg Ffi.State.direction h1
  exact absurd this (by decide)

theorem agree_euclid {f : FfiField} {u s s' : Ffi.State} (h : f.Agree u s) (h' : f.Agree u s') :
    f.Agree s s' := by
  cases f <;> exact h.symm.trans h'

/-- Every field but `.machine` varies independently of `.machine`. -/
theorem split (f : FfiField) (hf : f ≠ .machine) :
    ∃ s s' : Ffi.State, s.machine = s'.machine ∧ ¬ f.Agree s s' := by
  cases f with
  | machine => exact absurd rfl hf
  | vectors =>
    exact ⟨blank, { blank with vectors := fun _ => 1 }, rfl, fun h => by
      have := congrArg (fun v : BitVec 512 => v.getLsbD 0)
        (congrFun (show blank.vectors = fun _ => 1 from h) 0)
      simp [blank] at this⟩
  | x87 =>
    exact ⟨blank, { blank with x87 := fun _ => 1 }, rfl, fun h =>
      absurd (congrFun (show blank.x87 = fun _ => 1 from h) 0) (by decide)⟩
  | direction =>
    exact ⟨blank, { blank with direction := true }, rfl, fun h =>
      absurd (show blank.direction = true from h) (by decide)⟩
  | x87Mode =>
    exact ⟨blank, { blank with x87Mode := false }, rfl, fun h =>
      absurd (show blank.x87Mode = false from h) (by decide)⟩
  | mxcsr =>
    exact ⟨blank, { blank with mxcsr := 1 }, rfl, fun h =>
      absurd (show blank.mxcsr = 1 from h) (by decide)⟩
  | x87Control =>
    exact ⟨blank, { blank with x87Control := 1 }, rfl, fun h =>
      absurd (show blank.x87Control = 1 from h) (by decide)⟩
  | fsBase =>
    exact ⟨blank, { blank with fsBase := 1 }, rfl, fun h =>
      absurd (show blank.fsBase = 1 from h) (by decide)⟩

/-- **A machine whose state is fixed by its core and memory models only `.machine`**: every
FFI state has a completion that agrees with it on the modelled fields, and such a machine's
completion is fixed by `s.machine`. -/
theorem models_eq_machine (M : Mach)
    (hdet : ∀ x x', M.isa.core x = M.isa.core x' → M.isa.mem x = M.isa.mem x' → x = x')
    {f : FfiField} (hf : M.models f = true) : f = .machine := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨s, s', hm, hn⟩ := split f hne
  obtain ⟨x, hx⟩ := M.fills_total s
  obtain ⟨x', hx'⟩ := M.fills_total s'
  have e : x = x' := hdet _ _
    (by rw [Mach.fills_core hx, Mach.fills_core hx', hm])
    (by rw [Mach.fills_mem hx, Mach.fills_mem hx', hm])
  subst e
  exact hn (agree_euclid (M.fills_agree hx f hf) (M.fills_agree hx' f hf))

/-- On such a machine, `store` carries every field but `.machine`. -/
theorem store_carried_of_determined (M : Mach)
    (hdet : ∀ x x', M.isa.core x = M.isa.core x' → M.isa.mem x = M.isa.mem x' → x = x')
    {f : FfiField} (hf : f ≠ .machine) (s : Ffi.State) (y : M.σ) : f.Agree (M.store s y) s := by
  refine Mach.store_carried ?_ s y
  cases h : M.models f
  · rfl
  · exact absurd (models_eq_machine M hdet h) hf

/-! ## A machine with hidden state -/

theorem tscStep_eq {x x' : MState × Word} :
    tscStep x = some x' ↔ x.1.core.rip = 0 ∧ x' = (⟨tscCore x.1.core x.2, x.1.memory⟩, x.2) := by
  unfold tscStep
  by_cases h : x.1.core.rip = 0
  · simp only [h, ↓reduceIte, Option.some.injEq, true_and]
    exact ⟨fun e => e.symm, fun e => e.symm⟩
  · simp only [h, ↓reduceIte, reduceCtorEq, false_and]

theorem tscStep_after {x x' : MState × Word} (h : tscStep x = some x') : tscStep x' = none := by
  obtain ⟨-, rfl⟩ := tscStep_eq.1 h
  unfold tscStep tscCore
  simp

/-- From a state that has stepped, `tsc` is stuck. -/
theorem runs_stuck {P : MState × Word → Prop} {x y : MState × Word} (hx : tscStep x = none)
    (r : RunsIn tscIsa P x y) : y = x := by
  cases r with
  | refl => rfl
  | step _ hs _ => exact absurd (hx.symm.trans hs) (by simp)

/-- A run of `tsc` to a state that steps is empty. -/
theorem runs_tsc {P : MState × Word → Prop} {x y : MState × Word} (r : RunsIn tscIsa P x y)
    (hs : (tscStep y).isSome) : y = x := by
  cases r with
  | refl => rfl
  | step _ h r =>
    have := runs_stuck (tscStep_after h) r
    subst this
    rw [tscStep_after h] at hs
    cases hs

/-- **The hidden value is read**: two completions of `blank` step to different FFI states. -/
theorem tsc_reads_hidden : ∃ s x x', tsc.Fills s x ∧ tsc.Fills s x' ∧ ∃ y y',
    tsc.isa.step x = some y ∧ tsc.isa.step x' = some y' ∧ tsc.store s y ≠ tsc.store s y' := by
  refine ⟨blank, (blank.machine, 0), (blank.machine, 1), rfl, rfl, _, _,
    (tscStep_eq (x := (blank.machine, 0))).2 ⟨rfl, rfl⟩,
    (tscStep_eq (x := (blank.machine, 1))).2 ⟨rfl, rfl⟩, fun h => ?_⟩
  have := congrArg (fun t : Ffi.State => t.machine.core.regs .rax) h
  simp [Mach.store, overwrite, tsc, tscCore] at this

/-- **No deterministic reference is faithful to `tsc`**: two completions of one FFI state
step to different FFI states. -/
theorem tsc_not_faithful_ofFun (r : Ffi.State → Option Ffi.State) :
    ¬ Faithful (Ref.ofFun r) tsc := by
  intro hf
  obtain ⟨s, x, x', hx, hx', y, y', hy, hy', hne⟩ := tsc_reads_hidden
  have e1 : r (tsc.store s x) = some (tsc.store s y) := hf.fwd s x hx x y (.refl _) hy
  have e2 : r (tsc.store s x') = some (tsc.store s y') := hf.fwd s x' hx' x' y' (.refl _) hy'
  rw [Mach.store_fills hx] at e1
  rw [Mach.store_fills hx'] at e2
  exact hne (Option.some.inj (e1.symm.trans e2))

/-- **`tsc` is faithful to `tscRef`**: a step reading hidden state does not make faithfulness
unsatisfiable. -/
theorem tsc_faithful : Faithful tscRef tsc := by
  refine ⟨fun s x _ y y' _ hs => ?_, fun Q s x y hx hr hsome t ht => ?_⟩
  · obtain ⟨h0, rfl⟩ := tscStep_eq.1 hs
    exact ⟨h0, y.2, rfl⟩
  · have e := runs_tsc hr hsome
    subst e
    obtain ⟨h0, v, rfl⟩ := ht
    refine ⟨(y.1, v), (y.1, v), (⟨tscCore y.1.core v, y.1.memory⟩, v), hx, .refl _, rfl,
      tscStep_eq.2 ⟨h0, rfl⟩, rfl⟩

end Silmaril.Proofs.Machine.Abi.Conformance.Lens

end
