module

public import Silmaril.Wasm.Component.FXInv.Defs
public import Silmaril.Wasm.Component.FXEngine.Thms
import Silmaril.Proofs.Wasm.Component.FXInv.Step
import Silmaril.Proofs.Wasm.Component.FXInv.Vals

/-!
# Inversion of `StepFX` at host calls

The FX engine `fxE P` (`Silmaril.Wasm.Component.FXEngine`) parks an FX thread at a call of a
component host function by an explicit internal step. Its laws were proved without knowing
whether such a thread has other steps. This module proves that it has none, and what that means
for the game semantics of modules with FX functions.

* **`stepFX_atHost`** (inversion): FX code at a call of a component host function
  (`AtHost s code h args`) takes no `StepFX` step with no host. Proof: the Core erasure of the
  code has the host call as its `decompose?` redex (`decompose?_erase_plug`), while the left-hand
  side of every host-free `StepFX` step has none (`stepFX_noHostRedex`, by induction on the step).
* **`atHost_unique`**: the host function and the arguments of the call are determined by the
  code (the FX context and Core context of the redex need not be: `Ctx.seq` nests).
* **Engine level.** `internalFX_atHost`: every internal step of an FX thread at a host call is a
  parking step, keeps the store and parks at that call; `internalFX_atHost_exists`: one exists;
  `stepsFX_atHost`: a run from such a thread is empty or that one parking step;
  `statusFX_parked_atHost`: the parked thread asks exactly that call.
* **Values.** `stepFX_vals`: FX code that is a sequence of values takes no `StepFX` step (any
  host, any FX table); `internalFX_vals`: an FX thread at values takes no internal step; hence
  `statusFX_vals`: it has returned those values (or is `stuck` when one is not flat).
* **Game level** (`fxXG P`, modules with FX functions). `etrans_atHost`: in the transition
  system of any instance of the FX engine, a running export call whose thread is an FX thread at
  a call of import `h` has exactly one kind of move, the import question `h` with the call's
  arguments (as flat values), into the waiting state with the parked thread; there is no answer
  move and no other question. `engineLTS_atHost` restates it for `engineLTS`, whose strategy is
  the game semantics `(fxXG P).sem` of a module.

See `docs/projects/wasm-components.md` (section "Stretch, fxcomp").

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXInv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (AdminFX StepFX ConfigFX ContFX)
open Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Proofs.Wasm.Component.FXInv
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- **Inversion of `StepFX` at host calls**: FX code at a call of a component host function
takes no host-free `StepFX` step. -/
theorem stepFX_atHost (P : Profile) {s : Store (FXCode H)} {K : List (Option ContFX)}
    {f : Frame} {code : List AdminFX} {h : H} {args : List Execution.Core.Val}
    (hat : AtHost s code h args) {y : ConfigFX (FXCode H)} :
    ¬ StepFX P (noHostFX H) fxOf ⟨s, K, f, code⟩ y := by
  intro hs
  obtain ⟨E, cs, Ec, a, rfl, hd⟩ := hat
  obtain ⟨Ec', he⟩ := decompose?_erase_plug hd E
  exact NoHostRedex.hostFree (stepFX_noHostRedex hs) _ _ _ _ he

/-- **The host call of FX code is unique**: its host function and arguments. -/
theorem atHost_unique {s : Store (FXCode H)} {code : List AdminFX} {h h' : H}
    {args args' : List Execution.Core.Val} (h₁ : AtHost s code h args)
    (h₂ : AtHost s code h' args') : h = h' ∧ args = args' := by
  obtain ⟨E, cs, Ec, a, rfl, hd⟩ := h₁
  obtain ⟨E₂, cs₂, Ec₂, a₂, he₂, hd₂⟩ := h₂
  obtain ⟨_, e₁⟩ := decompose?_erase_plug hd E
  obtain ⟨_, e₂⟩ := decompose?_erase_plug hd₂ E₂
  rw [← he₂, e₁] at e₂
  simp only [Option.some.injEq, Prod.mk.injEq, FXCode.host.injEq] at e₂
  exact ⟨e₂.2.2.1, e₂.2.2.2⟩

/-- **Every internal step of an FX thread at a host call parks it at that call.** -/
theorem internalFX_atHost (P : Profile) {s : Store (FXCode H)} {K : List (Option ContFX)}
    {f : Frame} {code : List AdminFX} {h : H} {args : List Execution.Core.Val}
    (hat : AtHost s code h args) {y : Store (FXCode H) × ThreadFX H}
    (hy : InternalFX P (s, .fx K f code) y) :
    y.1 = s ∧ ∃ E Ec, y.2 = .parked K f E Ec h args := by
  rcases hy with ⟨K', f', code', -, hs⟩ | ⟨hy₁, E, cs, Ec, a, h', args', hc, hd, hy₂⟩
  · exact absurd hs (stepFX_atHost P hat)
  · obtain ⟨rfl, rfl⟩ := atHost_unique ⟨E, cs, Ec, a, hc, hd⟩ hat
    exact ⟨hy₁, E, Ec, hy₂⟩

/-- An FX thread at a host call can park. -/
theorem internalFX_atHost_exists (P : Profile) {s : Store (FXCode H)}
    {K : List (Option ContFX)} {f : Frame} {code : List AdminFX} {h : H}
    {args : List Execution.Core.Val} (hat : AtHost s code h args) :
    ∃ E Ec, InternalFX P (s, .fx K f code) (s, .parked K f E Ec h args) := by
  obtain ⟨E, cs, Ec, a, hc, hd⟩ := hat
  exact ⟨E, Ec, Or.inr ⟨rfl, E, cs, Ec, a, h, args, hc, hd, rfl⟩⟩

/-- An FX thread at a host call is running (its parking step is pending). -/
theorem statusFX_atHost (P : Profile) {s : Store (FXCode H)} {K : List (Option ContFX)}
    {f : Frame} {code : List AdminFX} {h : H} {args : List Execution.Core.Val}
    (hat : AtHost s code h args) : statusFX P s (.fx K f code) = .running := by
  obtain ⟨E, Ec, hi⟩ := internalFX_atHost_exists P (K := K) (f := f) hat
  exact ite_eq_left ⟨_, hi⟩

/-- **Runs from an FX thread at a host call**: none, or the parking step (a parked thread takes
no step). -/
theorem stepsFX_atHost (P : Profile) {s s' : Store (FXCode H)} {K : List (Option ContFX)}
    {f : Frame} {code : List AdminFX} {h : H} {args : List Execution.Core.Val}
    (hat : AtHost s code h args) {t' : ThreadFX H}
    (run : Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxE P)
      (s, ThreadFX.fx K f code) (s', t')) :
    (s' = s ∧ t' = .fx K f code) ∨ (s' = s ∧ ∃ E Ec, t' = .parked K f E Ec h args) := by
  rcases Relation.ReflTransGen.cases_head run with e | ⟨y, hy, run'⟩
  · obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
    exact Or.inl ⟨e₁.symm, e₂.symm⟩
  · obtain ⟨hy₁, E, Ec, hy₂⟩ := internalFX_atHost P hat hy
    have hy' : y = (s, ThreadFX.parked K f E Ec h args) := Prod.ext hy₁ hy₂
    subst hy'
    rcases Relation.ReflTransGen.cases_head run' with e | ⟨z, hz, -⟩
    · obtain ⟨e₁, e₂⟩ := Prod.mk.inj e
      exact Or.inr ⟨e₁.symm, E, Ec, e₂.symm⟩
    · exact hz.elim

/-- The parked thread asks exactly its call (or is stuck, when an argument is not flat). -/
theorem statusFX_parked (P : Profile) (s : Store (FXCode H)) (K : List (Option ContFX))
    (f : Frame) (E : Silmaril.Wasm.Models.FX.Ctx) (Ec : Silmaril.Wasm.SingleThreaded.Ctx) (h : H)
    (args : List Execution.Core.Val) :
    statusFX P s (.parked K f E Ec h args) =
      match args.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | some fargs => .callout h fargs
      | none => .stuck := rfl

/-! ## Values -/

/-- **FX values take no `StepFX` step.** -/
theorem stepFX_vals (P : Profile) {host : HostSemantics H}
    {fx : H → Option Silmaril.Wasm.Models.FX.FuncFX} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} (vs : List Execution.Core.Val) {y : ConfigFX H} :
    ¬ StepFX P host fx ⟨s, K, f, Silmaril.Wasm.Models.FX.cvals vs⟩ y := fun hs =>
  stepFX_not_allVals hs (by simpa using allVals_vals vs)

/-- **An FX thread at values takes no internal step** (neither a `StepFX` step nor parking). -/
theorem internalFX_vals (P : Profile) (s : Store (FXCode H)) (K : List (Option ContFX))
    (f : Frame) (vs : List Execution.Core.Val) :
    ¬ ∃ y, InternalFX P (s, ThreadFX.fx K f (Silmaril.Wasm.Models.FX.cvals vs)) y := by
  rintro ⟨y, ⟨K', f', code', -, hs⟩ | ⟨-, E, cs, Ec, a, h, args, hc, hd, -⟩⟩
  · exact stepFX_vals P vs hs
  · obtain ⟨Ec', he⟩ := decompose?_erase_plug hd E
    have hn : Silmaril.Wasm.SingleThreaded.decompose? s
        (eraseL (Silmaril.Wasm.Models.FX.cvals vs)) = none := by
      simpa using Silmaril.Wasm.SingleThreaded.decompose?_vals_nil
    rw [hc] at hn
    exact absurd (hn.symm.trans he) (fun e => by cases e)

/-- **The status of an FX thread at values**: it returned them (as flat values). -/
theorem statusFX_vals (P : Profile) (s : Store (FXCode H)) (K : List (Option ContFX))
    (f : Frame) (vs : List Execution.Core.Val) :
    statusFX P s (.fx K f (Silmaril.Wasm.Models.FX.cvals vs)) =
      match vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | some fvs => .returned (.values fvs)
      | none => .stuck := by
  refine (ite_eq_right (internalFX_vals P s K f vs)).trans ?_
  have hex : ∃ ws, Silmaril.Wasm.Models.FX.cvals vs = Silmaril.Wasm.Models.FX.cvals ws := ⟨vs, rfl⟩
  refine (dite_eq_left hex).trans ?_
  rw [← cvals_injective hex.choose_spec]
  cases vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? <;> rfl

/-! ## Game level -/

theorem fxE_status (P : Profile) {H : Type} (s : (fxE P).Store H) (t : (fxE P).Thread H) :
    (fxE P).status s t = statusFX P s t := rfl

/-- A run from an FX thread at a host call to a callout ends at the parking of that call. -/
theorem callout_of_run_atHost (P : Profile) {s s' : Store (FXCode H)}
    {K : List (Option ContFX)} {f : Frame} {code : List AdminFX} {h h' : H}
    {args : List Execution.Core.Val} {fargs : List Flat} (hat : AtHost s code h args)
    {t' : ThreadFX H}
    (run : Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxE P)
      (s, ThreadFX.fx K f code) (s', t'))
    (hc : (fxE P).status s' t' = .callout h' fargs) :
    s' = s ∧ h' = h ∧ args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some fargs ∧
      ∃ E Ec, t' = .parked K f E Ec h args := by
  rcases stepsFX_atHost P hat run with ⟨rfl, rfl⟩ | ⟨rfl, E, Ec, rfl⟩
  · exact absurd ((statusFX_atHost P hat).symm.trans hc) (fun e => by cases e)
  · have hp : (match args.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
        | some fargs => Silmaril.Wasm.Component.Engine.Status.callout h fargs
        | none => .stuck) = .callout h' fargs := hc
    split at hp
    · rename_i hf
      cases hp
      exact ⟨rfl, rfl, hf, E, Ec, rfl⟩
    · cases hp

/-- A run from an FX thread at a host call never returns. -/
theorem not_returned_of_run_atHost (P : Profile) {s s' : Store (FXCode H)}
    {K : List (Option ContFX)} {f : Frame} {code : List AdminFX} {h : H}
    {args : List Execution.Core.Val} (hat : AtHost s code h args) {t' : ThreadFX H}
    (run : Silmaril.Wasm.Component.Engine.CoreEngine.Steps (fxE P)
      (s, ThreadFX.fx K f code) (s', t'))
    (r : Silmaril.Wasm.Component.Engine.CallResult) : (fxE P).status s' t' ≠ .returned r := by
  intro hr
  rcases stepsFX_atHost P hat run with ⟨rfl, rfl⟩ | ⟨rfl, E, Ec, rfl⟩
  · exact absurd ((statusFX_atHost P hat).symm.trans hr) (fun e => by cases e)
  · have hp : (match args.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
        | some fargs => Silmaril.Wasm.Component.Engine.Status.callout h fargs
        | none => .stuck) = .returned r := hr
    split at hp <;> cases hp

/-- **The moves of an FX instance at a host call** (game semantics of modules with FX
functions): in the transition system of an instance of `fxE P`, a running export call whose
thread is an FX thread at a call of import `h` with arguments `args` has a move only if the
arguments are flat values `fargs`, and then every move is the import question `(h, fargs)` into
the waiting state with the parked thread and the same store. -/
theorem etrans_atHost (P : Profile) {addrs : List Nat} {imps exps : CoreIface}
    {q : (sigN exps.length).Op} {s : Store (FXCode Nat)} {K : List (Option ContFX)} {f : Frame}
    {code : List AdminFX} {h : Nat} {args : List Execution.Core.Val}
    (hat : AtHost s code h args) {m : Silmaril.Games.Move (sigN imps.length) (sigN exps.length)}
    {y : EState (fxE P) imps.length exps.length}
    (ht : ETrans (fxE P) addrs imps exps (.running q s (ThreadFX.fx K f code)) m y) :
    ∃ (hh : h < imps.length) (fargs : List Flat) (E : Silmaril.Wasm.Models.FX.Ctx)
      (Ec : Silmaril.Wasm.SingleThreaded.Ctx),
      args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some fargs ∧
      m = .inl (.ask (⟨h, hh⟩, .flat fargs)) ∧
      y = .waiting q s (ThreadFX.parked K f E Ec h args) (⟨h, hh⟩, .flat fargs) := by
  cases ht with
  | ucall run callout hh =>
    obtain ⟨rfl, rfl, hf, E, Ec, rfl⟩ := callout_of_run_atHost P hat run callout
    exact ⟨hh, _, E, Ec, hf, rfl, rfl⟩
  | oret run final => exact absurd final (not_returned_of_run_atHost P hat run _)
  | otrap run final => exact absurd final (not_returned_of_run_atHost P hat run _)

/-- `etrans_atHost` for the transition system `engineLTS` of an instance, whose strategy is the
game semantics of a module over `fxXG P`. -/
theorem engineLTS_atHost (P : Profile) (I : EInstance (fxXG P).E) {imps exps : CoreIface}
    {q : (sigN exps.length).Op} {s : Store (FXCode Nat)} {K : List (Option ContFX)} {f : Frame}
    {code : List AdminFX} {h : Nat} {args : List Execution.Core.Val}
    (hat : AtHost s code h args) {l} {y : (engineLTS (fxXG P).E I imps exps).State}
    (ht : (engineLTS (fxXG P).E I imps exps).step (.running q s (ThreadFX.fx K f code)) l y) :
    ∃ (hh : h < imps.length) (fargs : List Flat) (E : Silmaril.Wasm.Models.FX.Ctx)
      (Ec : Silmaril.Wasm.SingleThreaded.Ctx),
      args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some fargs ∧
      l = some (.inl (.ask (⟨h, hh⟩, .flat fargs))) ∧
      y = .waiting q s (ThreadFX.parked K f E Ec h args) (⟨h, hh⟩, .flat fargs) := by
  obtain ⟨m, rfl, hm⟩ := ht
  obtain ⟨hh, fargs, E, Ec, hf, rfl, rfl⟩ := etrans_atHost P hat hm
  exact ⟨hh, fargs, E, Ec, hf, rfl, rfl⟩

end Silmaril.Wasm.Component.FXInv
