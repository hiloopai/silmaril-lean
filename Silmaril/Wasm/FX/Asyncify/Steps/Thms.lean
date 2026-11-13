module

public import Silmaril.Wasm.FX.Asyncify.Steps.Defs
public import Silmaril.Wasm.FX.Asyncify.Selective.Thms

/-!
# Step counts of asyncify strategies and optimizations: results

The header of `Defs` (`NoSlower`, `SameSteps`).

**General.**

* `noSlower_of_rsim`: a relational stuttering simulation (`RelSim.RSim`, every step of `s`
  matched by at least one step of `t`) makes `s` never slower than `t`;
  `noSlower_of_simRel`, `noSlower_of_simStep`: the same for the family's `SimRel` and for
  `FXAsync`'s functional `SimStep`.
* `runN_map`, `sameSteps_of_map`, `beh_eq_of_map`: a map `g` with `s (g y) = (t y).map g`
  (a functional lock step) gives equal runs step by step, hence the same step counts and
  behaviours.
* `NoSlower.trans`, `noSlower_refl`.

**Optimizations.**

* **`selective_no_slower`**: for every target program `Q` and certificate `SafeProg S Q`,
  selective instrumentation (`optP S Q`) is never slower than full instrumentation (`Q`), from
  any code; **`analyze_no_slower`**: for the computed analysis and every kernel program, no
  hypothesis (`compSel (analyze (compP P) n) P` against `compP P`).

**Strategies.**

* `kernel_no_slower`: the kernel is never slower than its unwinding lowering (`tstep (compP P)`).
* `unwind_dispatch_same`: the unwinding machine and the first-order dispatch machine take the same
  number of steps (`FXAsyncPC`'s lock step); `kernel_no_slower_dispatch`.

These are upper bounds (never slower), not strict gains; strict gains are on examples
(`Selective.twice_tgt_slower`, and `SM.fwd_sm_faster` for the state machine).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Steps

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.FX.Asyncify.RelSim (RSim RRes)
open Silmaril.Wasm.FX.Asyncify.Selective (SafeProg optP opt compSel selInit analyze)
open Silmaril.Wasm.Models.FXAsyncPC (fstep annP bodies fInit rootCode)

variable {C D E V : Type}

/-! ## General -/

theorem noSlower_refl (s : C → Res C V) (x : C) : NoSlower s s x x := fun _ _ h => h

theorem NoSlower.trans {s : C → Res C V} {t : D → Res D V} {u : E → Res E V} {x : C} {y : D}
    {z : E} (h₁ : NoSlower s t x y) (h₂ : NoSlower t u y z) : NoSlower s u x z :=
  fun m o h => h₁ m o (h₂ m o h)

/-- **A stuttering simulation bounds the steps.** -/
theorem noSlower_of_rsim {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V}
    (h : RSim R s t) {x : C} {y : D} (hxy : R x y) : NoSlower s t x y :=
  fun _ _ hm => Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.rsim_stop_back h hxy hm

theorem rres_of_resRel {R : C → D → Prop} {a : Res C V} {b : Res D V}
    (h : Silmaril.Wasm.FX.Asyncify.ResRel R a b) : RRes R a b := by
  cases a with
  | next c =>
    cases b with
    | next d => exact .next h
    | stop _ => exact h.elim
  | stop o =>
    cases b with
    | next _ => exact h.elim
    | stop o' =>
      have ho : o = o' := h
      rw [ho]
      exact .stop o'

theorem noSlower_of_simRel {R : C → D → Prop} {s : C → Res C V} {t : D → Res D V}
    (h : Silmaril.Wasm.FX.Asyncify.SimRel s t R) {x : C} {y : D} (hxy : R x y) :
    NoSlower s t x y := by
  refine noSlower_of_rsim (R := R) ?_ hxy
  intro x y hxy
  obtain ⟨n, hn, hr⟩ := h x y hxy
  exact ⟨n, hn, rres_of_resRel hr⟩

theorem noSlower_of_simStep {s : C → Res C V} {t : D → Res D V} {g : C → D}
    (h : Silmaril.Proofs.Wasm.Models.FXAsync.SimStep s t g) (x : C) : NoSlower s t x (g x) := by
  refine noSlower_of_rsim (R := fun x y => y = g x) ?_ rfl
  rintro x y rfl
  obtain ⟨n, hn, hr⟩ := h x
  refine ⟨n, hn, ?_⟩
  rw [hr]
  cases s x with
  | next c => exact .next rfl
  | stop o => exact .stop o

/-- **A functional lock step gives equal runs.** -/
theorem runN_map {s : C → Res C V} {t : D → Res D V} {g : D → C}
    (h : ∀ y, s (g y) = (t y).map g) (n : Nat) (y : D) :
    runN s n (g y) = (runN t n y).map g := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    have hy : s (g y) = (t y).map g := h y
    cases ht : t y with
    | next y' =>
      have hs : s (g y) = .next (g y') := by rw [hy, ht]; rfl
      simp only [runN, hs, ht, ih]
    | stop o =>
      have hs : s (g y) = .stop o := by rw [hy, ht]; rfl
      simp only [runN, hs, ht, Res.map]

theorem map_eq_stop {g : D → C} {r : Res D V} {o : Outcome V} (h : r.map g = .stop o) :
    r = .stop o := by
  cases r with
  | next _ => cases h
  | stop o' =>
    have ho : o' = o := by simpa only [Res.map, Res.stop.injEq] using h
    rw [ho]

theorem sameSteps_of_map {s : C → Res C V} {t : D → Res D V} {g : D → C}
    (h : ∀ y, s (g y) = (t y).map g) (y : D) : SameSteps s t (g y) y := by
  constructor
  · intro m o hm
    rw [runN_map h, hm]
    rfl
  · intro m o hm
    rw [runN_map h] at hm
    exact map_eq_stop hm

/-- A functional lock step gives equal behaviours. -/
theorem beh_eq_of_map {s : C → Res C V} {t : D → Res D V} {g : D → C}
    (h : ∀ y, s (g y) = (t y).map g) (y : D) : beh s (g y) = beh t y := by
  refine Silmaril.Wasm.FX.Asyncify.RelSim.beh_eq_of_lock (R := fun x y => x = g y) ?_ rfl
  rintro x y rfl
  rw [h y]
  cases t y with
  | next y' => exact .next rfl
  | stop o => exact .stop o

/-! ## Optimizations -/

/-- **Selective instrumentation is never slower than full instrumentation.** -/
theorem selective_no_slower {S : Nat → Bool} {Q : Prog (TIns V)} (hQ : SafeProg S Q)
    (test : V → Bool) (c : List (TIns V)) (ops : List (SV V)) :
    NoSlower (tstep (optP S Q) test) (tstep Q test) ⟨[], .normal, [⟨opt S false c, ops⟩]⟩
      ⟨[], .normal, [⟨c, ops⟩]⟩ :=
  noSlower_of_rsim (Silmaril.Wasm.FX.Asyncify.Selective.selective_sim hQ test)
    ⟨.nil, trivial, ⟨rfl, rfl⟩, .nil _⟩

/-- **With the computed analysis, for every kernel program**: the selectively instrumented
lowering is never slower than the fully instrumented one. -/
theorem analyze_no_slower (P : Prog (Ins V)) (n : Nat) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    NoSlower (tstep (compSel (analyze (compP P) n) P) test) (tstep (compP P) test)
      (selInit (analyze (compP P) n) f args) (tInit f args) :=
  selective_no_slower (Silmaril.Proofs.Wasm.FX.Asyncify.Selective.analyze_safe (compP P) n) test _
    args

/-! ## Strategies -/

/-- The kernel is never slower than its unwinding lowering. -/
theorem kernel_no_slower (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    NoSlower (sstep P test) (tstep (compP P) test) (sInit f args) (tInit f args) :=
  noSlower_of_simStep (sim_step P test) (sInit f args)

theorem rres_of_pc {R : C → D → Prop} {a : Res C V} {b : Res D V}
    (h : Silmaril.Proofs.Wasm.Models.FXAsyncPC.ResRel R a b) : RRes R a b := by
  cases h with
  | next h => exact .next h
  | stop o => exact .stop o

theorem rres_flip {R : C → D → Prop} {a : Res C V} {b : Res D V} (h : RRes R a b) :
    RRes (fun d c => R c d) b a := by
  cases h with
  | next h => exact .next h
  | stop o => exact .stop o

/-- The unwinding machine and the first-order dispatch machine take the same steps. -/
theorem unwind_dispatch_same (Q : Prog (TIns V)) (R : List (TIns V)) (test : V → Bool)
    {x : TCfg V} {y : Silmaril.Wasm.Models.FXAsyncPC.FCfg V}
    (hxy : Silmaril.Proofs.Wasm.Models.FXAsyncPC.RCfg (bodies Q R) x y) :
    SameSteps (tstep Q test) (fstep (annP Q) (bodies Q R) test) x y := by
  have hl : Silmaril.Wasm.FX.Asyncify.RelSim.LockStep
      (Silmaril.Proofs.Wasm.Models.FXAsyncPC.RCfg (bodies Q R)) (tstep Q test)
      (fstep (annP Q) (bodies Q R) test) :=
    fun x y h => rres_of_pc (Silmaril.Proofs.Wasm.Models.FXAsyncPC.lock_step test x y h)
  have hl' : Silmaril.Wasm.FX.Asyncify.RelSim.LockStep
      (fun y x => Silmaril.Proofs.Wasm.Models.FXAsyncPC.RCfg (bodies Q R) x y)
      (fstep (annP Q) (bodies Q R) test) (tstep Q test) :=
    fun y x h => rres_flip (hl x y h)
  exact ⟨noSlower_of_rsim (Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.rsim_of_lock hl) hxy,
    noSlower_of_rsim (Silmaril.Proofs.Wasm.FX.Asyncify.RelSim.rsim_of_lock hl') hxy⟩

/-- The kernel is never slower than the first-order dispatch machine. -/
theorem kernel_no_slower_dispatch (P : Prog (Ins V)) (test : V → Bool) (f : Nat)
    (args : List (SV V)) :
    NoSlower (sstep P test) (fstep (annP (compP P)) (bodies (compP P) (rootCode f)) test)
      (sInit f args) (fInit f args) :=
  (kernel_no_slower P test f args).trans
    (unwind_dispatch_same (compP P) (rootCode f) test
      (Silmaril.Wasm.Models.FXAsyncPC.init_related (compP P) f args)).1

end Silmaril.Wasm.FX.Asyncify.Steps