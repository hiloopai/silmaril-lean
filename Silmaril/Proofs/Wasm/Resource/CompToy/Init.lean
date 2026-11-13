module

public import Silmaril.Wasm.Resource.CompToy.Defs
public import Silmaril.Wasm.Component.Reference.Silent.Thms
public import Silmaril.Wasm.Resource.Table.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# The toy resource component: instantiation at every profile

* `kernel_rfl` (now in `Silmaril.Wasm.Verify.Kernel.Defs`): closes an equation `lhs = rhs` by the
  kernel's definitional check alone, after reverting the local context (as `decide +kernel`
  does for decidable propositions, which refuses free variables). The kernel evaluates the
  toy's instantiation program over `core3P P` with `P` free in about a second; the elaborator's
  `rfl` does not finish;
* `silentRun_detRunL`: a successful `silentRun` is an unlocked deterministic machine run
  (`DetRunL`) of quiet labels in any context, as `SRuns.detRunL`;
* `silentRun_toyInst` (kernel evaluation): the toy's instantiation program runs silently to
  `toyInst P`, observing instance `0` and the exports `toyEs`;
* **`toy_instBehaviours`**: at every profile `P`, choice profile and host, the only result of
  instantiating the toy is the instance at `toyInst P` with exports `toyEs` (no trap, no
  divergence);
* `toyCtrP_toyCfg`: the counter of `toyCfg P c ι G` is `c` (for `c < 2^32`);
* **`toyR_init`**: hence the reachability invariant `toyR` holds after every instantiation
  (`CtrVCOn.init` for `toyProgP P`), with counter `0`, an empty instance and no leftovers.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs

/-! ## Silent evaluation is a deterministic run -/

section Silent

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- **A successful silent evaluation is an unlocked deterministic run**, in any context, whose
labels are `tau` or observations and whose observations are those of the evaluation. -/
theorem silentRun_detRunL {α : Type} (p : Canon.P E σ α) :
    ∀ {m m' : Machine.Config E σ} {os : List HostObs} {a : α},
      silentRun p m = some (os, a, m') → m.store.lockdown = false →
      ∀ (th : Option ThreadId) (f : α → Canon.P E σ (Ret E)) (segs : List (Seg E σ))
        (rest : List (Activation E σ)),
        ∃ tr, SRuns.Quiet tr ∧ traceObs tr = os ∧ DetRunL prof hr dispatch
          { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
          { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } := by
  induction p with
  | pure b =>
    intro m m' os a h hl th f segs rest
    obtain ⟨rfl, rfl, rfl⟩ : [] = os ∧ b = a ∧ m = m' := by
      simpa only [silentRun, Option.some.injEq, Prod.mk.injEq] using h
    refine ⟨[], ?_, rfl, DetRunL.refl hl⟩
    intro _ h'
    cases h'
  | op o k ih =>
    intro m m' os a h hl th f segs rest
    cases o with
    | get =>
      obtain ⟨tr, hq, ho, d⟩ := ih m.store h hl th f segs rest
      exact ⟨_, hq.cons (.inl rfl), ho,
        .cons hl (.of_prog rfl (fun _ _ e => by cases e) (.get rfl)) d⟩
    | modify g =>
      have hg : (g m.store).lockdown = m.store.lockdown := by
        by_contra hne
        simp only [silentRun, hne, ite_false, reduceCtorEq] at h
      have h' : silentRun (k ()) { m with store := g m.store } = some (os, a, m') := by
        simpa only [silentRun, hg, ite_true] using h
      obtain ⟨tr, hq, ho, d⟩ := ih () h' (hg.trans hl) th f segs rest
      exact ⟨_, hq.cons (.inl rfl), ho,
        .cons hl (.of_prog rfl (fun _ _ e => by cases e) (.modify rfl)) d⟩
    | emit o =>
      obtain ⟨⟨os', a', m''⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, rfl, rfl⟩ : o :: os' = os ∧ a' = a ∧ m'' = m' := by
        simpa only [Prod.mk.injEq] using h₂
      have hl' : (observe m o).store.lockdown = false :=
        (congrArg CStore.lockdown (observe_store m o)).trans hl
      obtain ⟨tr, hq, ho, d⟩ := ih () h₁ hl' th f segs rest
      refine ⟨_, hq.cons (.inr ⟨o, rfl⟩), ?_, .cons hl (SRuns.emit_step th o k f segs rest m) d⟩
      rw [← ho]
      rfl
    | _ => simp only [silentRun, reduceCtorEq] at h

end Silent

/-! ## The toy's instantiation -/

variable (P : Silmaril.Wasm.Numerics.Profile)

/-- **The toy's instantiation program runs silently** to `toyInst P` (kernel evaluation, `P`
free). -/
theorem silentRun_toyInst :
    silentRun (instantiateProg (E := core3P P) (σ := Unit) toyComp []) (initConfig ()) =
      some ([instantiatedObs ⟨0⟩ toyEs], .unit, toyInst P) := by
  kernel_rfl

theorem toyInst_ctl : (toyInst P).ctl = [] := by kernel_rfl

theorem toyInst_lockdown : (toyInst P).store.lockdown = false := by kernel_rfl

/-- `toyInst P` is the configuration between calls with counter `0`, the initial instance and
no leftovers. -/
theorem toyInst_eq : toyInst P = toyCfg P 0 {} (ToyGarb.empty P) := by kernel_rfl

theorem toyInst_globals_length : (toyInst P).store.core.globals.length = 1 := by kernel_rfl

/-- The counter of `toyCfg P c ι G` is `c`. -/
theorem toyCtrP_toyCfg {c : ℕ} (ι : InstState) (G : ToyGarb P) (hc : c < 2 ^ 32) :
    toyCtrP P (toyCfg P c ι G) = c := by
  obtain ⟨g, hg⟩ := List.length_eq_one_iff.mp (toyInst_globals_length P)
  have hgl : (toyCfg P c ι G).store.core.globals =
      [{ g with value := .i32 (BitVec.ofNat 32 c) }] := by
    show ((toyInst P).store.core.globals.modify 0 _) = _
    rw [hg]
    rfl
  show (match ((toyCfg P c ι G).store.core.globals[0]?).map
      Silmaril.Wasm.Execution.Core.GlobalInst.value with
    | some (Silmaril.Wasm.Execution.Core.Val.num v) => v.bits.toNat
    | _ => 0) = c
  rw [hgl]
  show (BitVec.ofNat 32 c).toNat = c
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hc

/-- The configuration after the instantiation host event. -/
noncomputable def toyStart : Machine.Config (core3P P) Unit :=
  { (initConfig () : Machine.Config (core3P P) Unit) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg toyComp []))] }

variable {P}

/-- **The instantiation is one deterministic run** from the host event to `toyInst P`. -/
theorem toyInst_detRunL {prof : ProfileKind} {hr : HostReady Unit}
    {D : Call (core3P P) → Canon.P (core3P P) Unit (Ret (core3P P))} :
    ∃ tr, SRuns.Quiet tr ∧ traceObs tr = [instantiatedObs ⟨0⟩ toyEs] ∧
      DetRunL prof hr D (toyStart P) tr (toyInst P) := by
  obtain ⟨tr, hq, ho, d⟩ := silentRun_detRunL (prof := prof) (hr := hr) (dispatch := D) _
    (silentRun_toyInst P) rfl none (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { toyInst P with ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      { toyInst P with ctl := [] } :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  have e : ({ toyInst P with ctl := [] } : Machine.Config (core3P P) Unit) = toyInst P := by
    kernel_rfl
  refine ⟨tr ++ [.tau], fun l hl => ?_, ?_, ?_⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hq l hl
    · exact .inl (List.mem_singleton.1 hl)
  · rw [traceObs_append, ho]
    rfl
  · rw [← e]
    exact d.trans (.cons (toyInst_lockdown P) s (.refl (toyInst_lockdown P)))

/-- **The results of instantiating the toy**, at every profile, choice profile and host: the
only one is the instance at `toyInst P` with root instance `0` and exports `toyEs`. -/
theorem toy_instBehaviours (prof : ProfileKind) (h : Host (core3P P) Unit) :
    ∀ r ∈ instBehaviours prof h (initConfig ()) (toyProgP P).comp (toyProgP P).args,
      r = .instance (toyInst P) ⟨0⟩ toyEs := by
  obtain ⟨trD, hq, ho, d⟩ := toyInst_detRunL (P := P) (prof := prof) (hr := h.hr)
    (D := h.dispatch)
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn, hc, -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = toyStart P := hostRun_inv s₁
    obtain ⟨htr, hm⟩ := detRunL_end d hq (toyInst_ctl P) (he ▸ hs₁) hn (.inl hc)
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, toyEs) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), toyEs) := Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = toyStart P := hostRun_inv s₁
    obtain ⟨-, rfl⟩ := detRunL_end d hq (toyInst_ctl P) (he ▸ hs₁) hn (.inr ht)
    have hl : (toyInst P).store.lockdown = true := ht
    rw [toyInst_lockdown] at hl
    cases hl
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = toyStart P := hostRun_inv s₁
    exact absurd (d.toDetRun.diverges (he ▸ dv)) (not_diverges_of_ctl_nil (toyInst_ctl P))

/-- **`toyR` holds after every instantiation** (`CtrVCOn.init` for `toyProgP P`), with the
counter at `0`. -/
theorem toyR_init (prof : ProfileKind) (h : Host (core3P P) Unit) :
    ∀ m₀ inst es, InstResult.instance m₀ inst es ∈
        instBehaviours prof h (initConfig ()) (toyProgP P).comp (toyProgP P).args →
      toyR P es m₀ ∧ m₀ = toyCfg P 0 {} (ToyGarb.empty P) := by
  intro m₀ inst es hi
  have he := toy_instBehaviours prof h _ hi
  injection he with hm _ hes
  subst hm hes
  exact ⟨⟨rfl, 0, {}, ToyGarb.empty P, toyInst_eq P, by decide, rfl, .inl rfl,
    ⟨freeOK_empty, by decide⟩, fun _ hx => (nomatch hx), fun _ hx => (nomatch hx)⟩, toyInst_eq P⟩

end Silmaril.Wasm.Resource.CompToy
