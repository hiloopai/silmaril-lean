module

public import Silmaril.Wasm.Det.Shared.Defs
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.Det.NoMem.Thms

/-!
# Determinism under store-writing hosts: runs and sufficient conditions

* `RunsS.steps`, `RunsS.snoc`: extending a run by host-free steps and by an answered call;
* `Runs.toS`, `DetCfgS.detCfg`: the store-free oracle is the special case where the returned store
  is the store at the call, so `DetCfgS` gives `DetCfg` when `A` is reflexive;
* `detCfgS_of_closed`: an invariant closed under steps and under resumption in admissible stores,
  with unique non-trapping stops of host-free runs, gives `DetCfgS` (as
  `Silmaril.Wasm.Det.Core.detCfg_of_closed`);
* `closedS_noMem`: the invariant of the memory-free subset depends on the store only through its
  function instances, so it is closed under resumption in every store keeping them
  (`KeepFuncs`), hence `detModuleS_of_storeB`/`detModuleS_of_closB`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Shared

open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Shared
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {A : Store Nat → Store Nat → Prop} {Inv : Config Nat → Prop}

theorem resumeIn_self (d : Config Nat) (E : Ctx) (r : Result) :
    resumeIn d E r d.store = resumeAt d E r := rfl

/-- Extend a run by host-free steps. -/
theorem runsS_steps {c d d' : Config Nat} {tr : List SCall} (hr : RunsS P A c tr d)
    (hs : Steps P Det.noHost d d') : RunsS P A c tr d' := by
  induction hr with
  | stop h => exact .stop (h.trans hs)
  | call h hd hA _ ih => exact .call h hd hA (ih hs)

/-- Extend a run by an answered import call. -/
theorem runsS_snoc {c d : Config Nat} {tr : List SCall} {E : Ctx} {a h : Nat} {args : List Val}
    (hr : RunsS P A c tr d) (hd : decompose? d.store d.code = some (E, a, h, args)) (r : Result)
    {s' : Store Nat} (hA : A d.store s') :
    RunsS P A c (tr ++ [⟨h, args, r, s'⟩]) (resumeIn d E r s') := by
  induction hr with
  | stop hs => exact .call hs hd hA (.stop .refl)
  | call hs hd' hA' _ ih => exact .call hs hd' hA' (ih hd hA)

/-- The store-free trace of a run, read with returned stores equal to the stores at the calls. -/
theorem Runs.toS (hA : ∀ s, A s s) {c d : Config Nat} {tr : List Call} (hr : Runs P c tr d) :
    ∃ tr', RunsS P A c tr' d := by
  induction hr with
  | stop hs => exact ⟨[], .stop hs⟩
  | call hs hd _ ih =>
    obtain ⟨tr', hk⟩ := ih
    exact ⟨_, .call hs hd (hA _) (resumeIn_self _ _ _ ▸ hk)⟩

/-- Lock-step reading of two store-free runs after a common store-writing prefix. -/
theorem detCfg_aux (hA : ∀ s, A s s) {c : Config Nat} (hD : DetCfgS P A c) {o₁ o₂ : Out} :
    ∀ (tr : List Call) (pre : List SCall) (y₁ y₂ d₁ d₂ : Config Nat), RunsS P A c pre y₁ →
      RunsS P A c pre y₂ → Runs P y₁ tr d₁ → Runs P y₂ tr d₂ → OutAt d₁ o₁ → OutAt d₂ o₂ →
      o₁ = o₂ ∧ d₁.store = d₂.store
  | [], pre, y₁, y₂, d₁, d₂, g₁, g₂, h₁, h₂, ho₁, ho₂ => by
    cases h₁ with
    | stop hs₁ =>
      cases h₂ with
      | stop hs₂ => exact hD pre d₁ d₂ o₁ o₂ (runsS_steps g₁ hs₁) (runsS_steps g₂ hs₂) ho₁ ho₂
  | x :: q, pre, y₁, y₂, d₁, d₂, g₁, g₂, h₁, h₂, ho₁, ho₂ => by
    cases h₁ with
    | @call _ e₁ _ E₁ a₁ _ _ r _ hs₁ hd₁ hk₁ =>
      cases h₂ with
      | @call _ e₂ _ E₂ a₂ _ _ _ _ hs₂ hd₂ hk₂ =>
        have hst : e₁.store = e₂.store :=
          (hD pre e₁ e₂ _ _ (runsS_steps g₁ hs₁) (runsS_steps g₂ hs₂) (.call hd₁) (.call hd₂)).2
        have r₁ := runsS_snoc (runsS_steps g₁ hs₁) hd₁ r (hA e₁.store)
        have r₂ := runsS_snoc (runsS_steps g₂ hs₂) hd₂ r (hA e₂.store)
        rw [← hst] at r₂
        rw [resumeIn_self] at r₁
        have e : resumeIn e₂ E₂ r e₁.store = resumeAt e₂ E₂ r := by rw [hst]; rfl
        rw [e] at r₂
        exact detCfg_aux hA hD q _ _ _ _ _ r₁ r₂ hk₁ hk₂ ho₁ ho₂

/-- **The store-free oracle is a special case**: with `A` reflexive, `DetCfgS` gives `DetCfg`. -/
theorem DetCfgS.detCfg (hA : ∀ s, A s s) {c : Config Nat} (hD : DetCfgS P A c) : DetCfg P c :=
  fun tr d₁ d₂ _ _ h₁ h₂ ho₁ ho₂ =>
    detCfg_aux hA hD tr [] c c d₁ d₂ (.stop .refl) (.stop .refl) h₁ h₂ ho₁ ho₂

/-! ## Sufficient conditions -/

/-- Runs from an invariant configuration reach at most one non-trapping stop. -/
theorem runsS_unique (hI : ClosedS P A Inv) (hS : ∀ c, Inv c → SegDet P c) :
    ∀ (tr : List SCall) (c d₁ d₂ : Config Nat), Inv c → RunsS P A c tr d₁ → RunsS P A c tr d₂ →
      Stop d₁ → Stop d₂ → d₁ = d₂
  | [], c, d₁, d₂, hc, h₁, h₂, hs₁, hs₂ => by
    cases h₁ with
    | stop hs₁' =>
      cases h₂ with
      | stop hs₂' => exact hS c hc d₁ d₂ hs₁' hs₂' hs₁ hs₂
  | x :: q, c, d₁, d₂, hc, h₁, h₂, hs₁, hs₂ => by
    cases h₁ with
    | @call _ e₁ _ E₁ a₁ _ _ _ _ _ hs₁' hd₁ hA₁ hk₁ =>
      cases h₂ with
      | @call _ e₂ _ E₂ a₂ _ _ _ _ _ hs₂' hd₂ hA₂ hk₂ =>
        have he : e₁ = e₂ :=
          hS c hc e₁ e₂ hs₁' hs₂' (Silmaril.Proofs.Wasm.Det.Core.stop_of_decompose hd₁)
            (Silmaril.Proofs.Wasm.Det.Core.stop_of_decompose hd₂)
        subst he
        have hE : E₁ = E₂ := by
          rw [hd₁] at hd₂
          cases hd₂
          rfl
        subst hE
        have he₁ : Inv e₁ := Silmaril.Proofs.Wasm.Det.Core.inv_steps hI.step hs₁' hc
        exact runsS_unique hI hS q _ d₁ d₂ (hI.resume _ _ _ _ _ _ _ he₁ hd₁ hA₁) hk₁ hk₂ hs₁ hs₂

/-- **Determinism under store-writing hosts from an invariant.** -/
theorem detCfgS_of_closed (hI : ClosedS P A Inv) (hS : ∀ c, Inv c → SegDet P c) {c : Config Nat}
    (hc : Inv c) : DetCfgS P A c := by
  intro tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂
  have he : d₁ = d₂ := runsS_unique hI hS tr c d₁ d₂ hc h₁ h₂ ⟨_, ho₁⟩ ⟨_, ho₂⟩
  subst he
  exact ⟨OutAt.unique ho₁ ho₂, rfl⟩

/-! ## The memory-free subset -/

open Silmaril.Wasm.Det.NoMem in
/-- The invariant of the memory-free subset is closed under resumption in every store keeping
the function instances. -/
theorem closedS_noMem {q : Nat → Bool} {ind : Bool} (P : Profile) :
    ClosedS P KeepFuncs (Silmaril.Wasm.Det.NoMem.Inv q ind) where
  step := (inv_closed P).step
  resume c E a h args r s' hc hd hk := by
    obtain ⟨hM, hN, hF⟩ := (inv_closed P).resume c E a h args r hc hd
    refine ⟨hM, hN, ?_⟩
    show FunOk q ind s'.funcs
    rw [hk]
    exact hF

open Silmaril.Wasm.Det.NoMem in
theorem detCfgS_noMem {q : Nat → Bool} {ind : Bool} {c : Config Nat} (hc : Silmaril.Wasm.Det.NoMem.Inv q ind c) :
    DetCfgS P KeepFuncs c :=
  detCfgS_of_closed (closedS_noMem P)
    (fun _ h => segDet_of_detUpTo (inv_closed P).step (fun _ h' => inv_detUpTo neverFail h') h) hc

open Silmaril.Wasm.Det.NoMem in
/-- **Full mode**: at every store passing `storeB`, every function is deterministic under every
host keeping the function instances. -/
theorem detModuleS_of_storeB (Entry : Nat → Prop) :
    DetModuleS P KeepFuncs (fun s => storeB s = true) Entry := fun _ hs a _ vs =>
  detCfgS_noMem (Silmaril.Proofs.Wasm.Det.NoMem.inv_invoke (a := a) vs
    Silmaril.Proofs.Wasm.Det.NoMem.mode_full (Silmaril.Proofs.Wasm.Det.NoMem.funOk_of_storeB hs) rfl)

open Silmaril.Wasm.Det.NoMem in
/-- **Direct mode**: at every store with the functions of a store passing `closB s₀ A`, the
functions of `A` are deterministic under every host keeping the function instances. -/
theorem detModuleS_of_closB {s₀ : Store Nat} {L : List Nat} (h : closB s₀ L = true) :
    DetModuleS P KeepFuncs (fun s => s.funcs = s₀.funcs) (· ∈ L) := fun s hs a ha vs => by
  have h' : closB s L = true := (closB_congr hs L).trans h
  exact detCfgS_noMem (Silmaril.Proofs.Wasm.Det.NoMem.inv_invoke vs
    (Silmaril.Proofs.Wasm.Det.NoMem.mode_direct _) (Silmaril.Proofs.Wasm.Det.NoMem.funOk_of_closB h')
    (List.contains_iff_mem.mpr ha))

end Silmaril.Proofs.Wasm.Det.Shared
