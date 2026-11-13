module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Bounded.Basic
public import Silmaril.Wasm.FX.Asyncify.Tool.Thms

/-!
# The asyncify tool with a bounded memory: results

The header of `Defs`. `tgtStepB cap` is the target system whose machine traps at an `i32.load`
or `i32.store` ending past `cap` bytes (`cap = capOf pages` for the declared memory).

* **`bounded_eq_of_safe`**: if no reachable state of the unbounded target accesses memory past
  `cap`, the bounded and unbounded targets have the same behaviours.
* **`overflow_traps`**: otherwise the bounded target **traps** at the first state that does, with
  the host state of that point: its only behaviour is that trap.
* `bounded_sub`: in every case the bounded target's behaviours are among the unbounded
  target's and traps.
* **`asyncify_beh_bounded`**: with `asyncify_beh`, for a well-formed program under
  `DepthBound`, every behaviour of the bounded target is a behaviour of the source or a trap;
  `asyncify_beh_safe`: equal behaviours when the target stays in bounds.
* **`asyncify_beh_fits`**: equal behaviours when every source state fits its frames into the
  memory, **conditional on the frozen open target `Task.fits`** (not proved).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Bounded

variable {σ : Type}

/-- **No out-of-bounds access reachable: the bounded target behaves as the unbounded one.** -/
theorem bounded_eq_of_safe (cap : Nat) (E : Env) (H : Host σ) {t : TSt σ}
    (hs : Safe (tgtStep E H) (fun t => OOB cap t.cfg) t) :
    beh (tgtStepB cap E H) t = beh (tgtStep E H) t :=
  beh_eq_of_safe (fun x hx => tgtStepB_good x hx) hs

/-- **An overflow traps**: the bounded target's only behaviour is a trap at the first state of the
unbounded run that accesses memory past `cap`. -/
theorem overflow_traps (cap : Nat) (E : Env) (H : Host σ) {t : TSt σ}
    (hns : ¬ Safe (tgtStep E H) (fun t => OOB cap t.cfg) t) :
    ∃ n y, runN (tgtStep E H) n t = .next y ∧ OOB cap y.cfg ∧
      beh (tgtStepB cap E H) t = {.trap y.host} :=
  beh_eq_of_bad (o := fun y => .trap y.host) (fun x hx => tgtStepB_good x hx)
    (fun x hx => tgtStepB_bad x hx) hns

/-- The bounded target's behaviours are the unbounded target's or traps. -/
theorem bounded_sub (cap : Nat) (E : Env) (H : Host σ) (t : TSt σ) :
    beh (tgtStepB cap E H) t ⊆ beh (tgtStep E H) t ∪ {b | ∃ h, b = .trap h} := by
  intro b hb
  rcases beh_sub (o := fun y : TSt σ => (.trap y.host : Obs σ)) (fun x hx => tgtStepB_good x hx)
    (fun x hx => tgtStepB_bad x hx) t hb with h | ⟨y, -, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨y.host, rfl⟩

/-- **The pass with a bounded memory**: every behaviour of the bounded target is a source
behaviour or a trap. -/
theorem asyncify_beh_bounded (P : Prog) (hP : P.WF) (H : Host σ) (cap : Nat) {e : Nat}
    {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams)
    (s : σ) (hbound : DepthBound P H (srcCfg e fn args, s)) :
    beh (tgtStepB cap (asyncifyProg P) H) (tgtSt P e fn args s) ⊆
      beh (srcStep P.env H) (srcCfg e fn args, s) ∪ {b | ∃ h, b = .trap h} := by
  rw [asyncify_beh P hP H hfn args hargs s hbound]
  exact bounded_sub cap _ H _

/-- **In bounds, the same behaviours as the source.** -/
theorem asyncify_beh_safe (P : Prog) (hP : P.WF) (H : Host σ) (cap : Nat) {e : Nat}
    {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W) (hargs : args.length = fn.nparams)
    (s : σ) (hbound : DepthBound P H (srcCfg e fn args, s))
    (hs : Safe (tgtStep (asyncifyProg P) H) (fun t => OOB cap t.cfg) (tgtSt P e fn args s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStepB cap (asyncifyProg P) H) (tgtSt P e fn args s) := by
  rw [bounded_eq_of_safe cap _ H hs]
  exact asyncify_beh P hP H hfn args hargs s hbound

/-- **Conditional on `Task.fits`**: when every source state fits its frames in `cap` bytes, the
bounded target has the source's behaviours. -/
theorem asyncify_beh_fits (ht : Task.fits) (P : Prog) (hP : P.WF) (H : Host σ) (cap : Nat)
    {e : Nat} {fn : FnSrc} (hfn : P.fnAt e = some fn) (args : List W)
    (hargs : args.length = fn.nparams) (s : σ) (hbound : DepthBound P H (srcCfg e fn args, s))
    (hfit : FitsIn cap P H (srcCfg e fn args, s)) :
    beh (srcStep P.env H) (srcCfg e fn args, s) =
      beh (tgtStepB cap (asyncifyProg P) H) (tgtSt P e fn args s) := by
  have hge := Prog.fnAt_ge hfn
  have hget : P.fns[e - P.imps.length]? = some fn := by
    unfold Prog.fnAt at hfn
    simpa [hge] using hfn
  exact asyncify_beh_safe P hP H cap hfn args hargs s hbound
    (ht P hP H cap e fn args s hge hget hargs hfit)

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.asyncify_beh_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asyncify_beh_bounded

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.overflow_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms overflow_traps

end Silmaril.Wasm.FX.Asyncify.Tool
