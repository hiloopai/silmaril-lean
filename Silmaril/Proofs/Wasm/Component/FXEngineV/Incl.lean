module

public import Silmaril.Wasm.Component.FXEngineV.Defs
public import Silmaril.Wasm.Component.FXEngine.Thms
public import Silmaril.Wasm.Models.FXV.Thms
public import Silmaril.Proofs.Wasm.Component.FXEngineV.Vals
public import Silmaril.Proofs.Wasm.Component.FXEngineV.Lawful

/-!
# The engine with suspension simulates the WasmFX engine

On the same instance, every play of `fxE P` is a play of `fxEV P`.

* `ιT`: a thread of `fxE P` as a thread of `fxEV P` (the context of a parked thread by
  `Ctx.toV`);
* `internal_incl`: an internal step of `fxE P` is one of `fxEV P` (`stepFX_incl`, and
  `E.toV.plug = E.plug` for parking);
* `status_incl`: a returned or callout status of `fxE P` is the status in `fxEV P`. The only
  non-trivial case is an FX thread that has returned: its code is Core code (values, a trap or
  a thrown exception), on which `StepFX'` has the steps of `StepFX` (`stepFX'_iff_allCore`) and
  every parking context with FX values is a parking context of `fxE P` (`ctx_of_allCore`);
* `resume_incl`: resumption commutes with `ιT`;
* `sim`: the transition system of an `fxE P` instance is simulated by that of the same instance
  of `fxEV P`, so `engineStrategy_le`.

The converse fails on FX code (a branch with a continuation operand steps only in `fxEV P`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXEngineV

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Execution.Core (Store Frame Val Admin vals)
open Silmaril.Wasm.SingleThreaded (Thread)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)
open Silmaril.Wasm.Models.FX (AdminFX ContFX Ctx StepFX cvals cthrowing)
open Silmaril.Wasm.Models.FXV (StepFX' CtxV FVal fvals liftV)
open Silmaril.Proofs.Wasm.Models.FX (isCore)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-! ## Contexts -/

theorem toV_plug (E : Ctx) (c : List AdminFX) : E.toV.plug c = E.plug c := by
  induction E with
  | hole => rfl
  | seq vs E rest ih =>
    simp only [Ctx.toV, CtxV.plug, Ctx.plug, Silmaril.Wasm.Models.FXV.fvals_liftV, ih]
  | label n k E ih => simp only [Ctx.toV, CtxV.plug, Ctx.plug, ih]
  | frame n f E ih => simp only [Ctx.toV, CtxV.plug, Ctx.plug, ih]
  | handler hs E ih => simp only [Ctx.toV, CtxV.plug, Ctx.plug, ih]

theorem fvals_allCore (vs : List FVal) (h : (fvals vs).all isCore = true) :
    ∃ ws, vs = liftV ws := by
  induction vs with
  | nil => exact ⟨[], rfl⟩
  | cons v vs ih =>
    simp only [fvals, List.map_cons, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ws, hws⟩ := ih h.2
    cases v with
    | val w => exact ⟨w :: ws, by rw [hws]; rfl⟩
    | cont k => simp [FVal.toAdmin, isCore] at h

/-- **A parking context in Core code is a context of `fxE P`.** -/
theorem ctx_of_allCore : ∀ (E : CtxV) (c : List AdminFX), (E.plug c).all isCore = true →
    ∃ E' : Ctx, E'.plug c = E.plug c
  | .hole, _, _ => ⟨.hole, rfl⟩
  | .seq vs E rest, c, h => by
      simp only [CtxV.plug, List.all_append, Bool.and_eq_true] at h
      obtain ⟨ws, rfl⟩ := fvals_allCore vs h.1.1
      obtain ⟨E', hE'⟩ := ctx_of_allCore E c h.1.2
      exact ⟨.seq ws E' rest, by
        simp only [Ctx.plug, CtxV.plug, Silmaril.Wasm.Models.FXV.fvals_liftV, hE']⟩
  | .label _ _ _, _, h => by simp [CtxV.plug, isCore] at h
  | .frame _ _ _, _, h => by simp [CtxV.plug, isCore] at h
  | .handler _ _, _, h => by simp [CtxV.plug, isCore] at h

/-! ## Threads -/

/-- A thread of `fxE P` as a thread of `fxEV P`. -/
def ιT : ThreadFX H → ThreadV H
  | .core t => .core t
  | .fx K f code => .fx K f code
  | .parked K f E Ec h args => .parked K f E.toV Ec h args

/-- **An internal step of `fxE P` is one of `fxEV P`.** -/
theorem internal_incl {x y : Store (FXCode H) × ThreadFX H} (h : InternalFX P x y) :
    InternalV P (x.1, ιT x.2) (y.1, ιT y.2) := by
  rcases x with ⟨s, t⟩
  rcases y with ⟨s', t'⟩
  cases t with
  | core t₀ =>
    rcases h with ⟨t₁, rfl, h⟩ | ⟨hc, K, f, code, rfl, h⟩
    · exact Or.inl ⟨t₁, rfl, h⟩
    · exact Or.inr ⟨hc, K, f, code, rfl, Silmaril.Wasm.Models.FXV.stepFX_incl h⟩
  | fx K f code =>
    rcases h with ⟨K', f', code', rfl, h⟩ | ⟨hs, E, cs, Ec, a, hh, args, hc, hd, rfl⟩
    · exact Or.inl ⟨K', f', code', rfl, Silmaril.Wasm.Models.FXV.stepFX_incl h⟩
    · exact Or.inr ⟨hs, E.toV, cs, Ec, a, hh, args, by rw [toV_plug]; exact hc, hd, rfl⟩
  | parked => exact h.elim

/-- Runs of `fxE P` are runs of `fxEV P`. -/
theorem steps_incl {s s' : Store (FXCode H)} {t t' : ThreadFX H}
    (h : Steps (fxE P) (s, t) (s', t')) : Steps (fxEV P) (s, ιT t) (s', ιT t') :=
  Relation.ReflTransGen.lift (p := (fxEV P).Internal)
    (fun x : Store (FXCode H) × ThreadFX H => (x.1, ιT x.2))
    (fun _ _ h => internal_incl h) (s, t) (s', t') h

/-- Code whose `fxE P` result is `returned` is Core code. -/
theorem allCore_of_fxResult {code : List AdminFX} {r : Silmaril.Wasm.Component.Engine.CallResult}
    (h : (fxResult code : Silmaril.Wasm.Component.Engine.Status H) = .returned r) :
    code.all isCore = true := by
  unfold fxResult at h
  split_ifs at h with h1 h2 h3
  · obtain ⟨vs, rfl⟩ := h1
    exact Silmaril.Proofs.Wasm.Models.FX.all_isCore_cvals vs
  · rw [h2]
    rfl
  · obtain ⟨a, rfl⟩ := h3
    exact Silmaril.Proofs.Wasm.Models.FX.all_isCore_cthrowing a

/-- An FX thread with Core code that takes no `fxE P` step takes no `fxEV P` step. -/
theorem no_internalV_of_allCore {s : Store (FXCode H)} {K : List (Option ContFX)} {f : Frame}
    {code : List AdminFX} (hc : code.all isCore = true)
    (hn : ¬ ∃ y, InternalFX P (s, ThreadFX.fx K f code) y) :
    ¬ ∃ y, InternalV P (s, ThreadV.fx K f code) y := by
  rintro ⟨⟨s', t'⟩, ⟨K', f', code', -, hs⟩ | ⟨-, E, cs, Ec, a, h, args, hp, hd, -⟩⟩
  · exact hn ⟨(s', .fx K' f' code'), Or.inl ⟨K', f', code', rfl,
      (Silmaril.Wasm.Models.FXV.stepFX'_iff_allCore (x := ⟨s, K, f, code⟩)
        (y := ⟨s', K', f', code'⟩) hc).mp hs⟩⟩
  · obtain ⟨E', hE'⟩ := ctx_of_allCore E _ (hp ▸ hc)
    exact hn ⟨(s, .parked K f E' Ec h args), Or.inr ⟨rfl, E', cs, Ec, a, h, args,
      hp.trans hE'.symm, hd, rfl⟩⟩

/-- **A returned status of `fxE P` is the status in `fxEV P`.** -/
theorem status_incl_returned {s : Store (FXCode H)} {t : ThreadFX H}
    {r : Silmaril.Wasm.Component.Engine.CallResult} (h : statusFX P s t = .returned r) :
    statusV P s (ιT t) = .returned r := by
  cases t with
  | core t₀ => exact h
  | fx K f code =>
    simp only [statusFX] at h
    split_ifs at h with hex
    show statusV P s (.fx K f code) = _
    simp only [statusV]
    exact (ite_eq_right (no_internalV_of_allCore (allCore_of_fxResult h) hex)).trans h
  | parked => exact h

/-- **A callout status of `fxE P` is the status in `fxEV P`.** -/
theorem status_incl_callout {s : Store (FXCode H)} {t : ThreadFX H} {hc : H}
    {args : List Silmaril.Wasm.Component.Engine.FlatValue}
    (h : statusFX P s t = .callout hc args) : statusV P s (ιT t) = .callout hc args := by
  cases t with
  | core t₀ => exact h
  | fx K f code =>
    simp only [statusFX] at h
    split_ifs at h
    exact absurd h (Silmaril.Proofs.Wasm.Component.FXEngineV.fxResult_ne_callout code hc args)
  | parked => exact h

/-- Resumption commutes with `ιT`. -/
theorem resume_incl (s : Store (FXCode H)) (t : ThreadFX H)
    (r : Silmaril.Wasm.Component.Engine.CallResult) :
    resumeV s (ιT t) r = ιT (resumeFX s t r) := by
  cases t with
  | core t₀ => rfl
  | fx K f code => rfl
  | parked K f E Ec h args =>
    show ThreadV.fx K f (E.toV.plug _) = ThreadV.fx K f (E.plug _)
    rw [toV_plug]

/-! ## The simulation -/

/-- A hidden state of an `fxE P` instance as one of `fxEV P`. -/
def mapE {n k : Nat} : EState (fxE P) n k → EState (fxEV P) n k
  | .idle s => .idle s
  | .running q s t => .running q s (ιT t)
  | .waiting q s t e => .waiting q s (ιT t) e
  | .refusing q s => .refusing q s

/-- **Every move of `fxE P` is a move of `fxEV P`.** -/
theorem etrans_mapE {addrs : List Nat} {imps exps : CoreIface}
    {x x' : EState (fxE P) imps.length exps.length} {m : Move (sigN imps.length) (sigN exps.length)}
    (h : ETrans (fxE P) addrs imps exps x m x') :
    ETrans (fxEV P) addrs imps exps (mapE x) m (mapE x') := by
  cases h with
  | call hc => exact .call hc
  | refuse hc => exact .refuse hc
  | refused => exact .refused
  | ucall run hco hh => exact .ucall (steps_incl run) (status_incl_callout hco) hh
  | @uret q s t e r =>
    have h := ETrans.uret (E := fxEV P) (addrs := addrs) (imps := imps) (exps := exps) (q := q)
      (s := s) (t := ιT t) (e := e) r
    have e' := resume_incl s t (resultOf imps[e.1].2.results r)
    show ETrans (fxEV P) addrs imps exps (EState.waiting q s (ιT t) e) _
      (EState.running q s (ιT (resumeFX s t _)))
    exact e' ▸ h
  | oret run hf => exact .oret (steps_incl run) (status_incl_returned hf)
  | otrap run hf => exact .otrap (steps_incl run) (status_incl_returned hf)

/-- The `fxE P` instance is simulated by the same `fxEV P` instance. -/
def sim (I : EInstance (fxE P)) (imps exps : CoreIface) :
    (engineLTS (fxE P) I imps exps).Simulation
      (engineLTS (fxEV P) ⟨I.store, I.addrs⟩ imps exps) where
  R x y := y = mapE x
  init := rfl
  step := by
    rintro x x' y l rfl ⟨m, rfl, h⟩
    exact ⟨mapE x', .vis ⟨m, rfl, etrans_mapE h⟩ (.nil _), rfl⟩

/-- **The strategy of an `fxE P` instance is below that of the same `fxEV P` instance.** -/
theorem engineStrategy_le (I : EInstance (fxE P)) (imps exps : CoreIface) :
    engineStrategy (fxE P) I imps exps ≤ engineStrategy (fxEV P) ⟨I.store, I.addrs⟩ imps exps :=
  (sim I imps exps).ofLTS_le

end Silmaril.Proofs.Wasm.Component.FXEngineV
