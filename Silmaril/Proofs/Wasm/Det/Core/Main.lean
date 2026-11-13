module

public import Silmaril.Proofs.Wasm.Det.Core.Basic

/-!
# Determinism and statelessness modulo traps and imports: main results

* the oracle consequences: two Core runs against the same `oracleHost F` that both return
  without trapping saw the same import calls and answers (`traces_eq`), hence return the same
  result (`obsAgree_oracle`) and, for `DetCfg`, in the same store (`detCfg_oracle`);
* sufficient conditions: `detCfg_of_closed` (an invariant closed under steps and resumptions on
  which host-free runs have at most one non-trapping stop), `segDet_of_stepDet` (steps are
  equal up to `Doomed` ones, the shape of `Choice.soft_join`), `segDet_of_detUpTo` (steps are
  steps of a deterministic profile up to `Doomed` ones, through silmaril-lean's uniqueness of
  normal forms `reach_normal_unique`), `Doomed.detCfg`;
* monotonicity in the profile.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## The oracle consequences -/

/-- Answers of a tail. -/
theorem Answers.tail {F : Nat → List Val → Result} {x : Call} {tr : List Call}
    (h : Answers F (x :: tr)) : Answers F tr :=
  fun y hy => h y (List.mem_cons_of_mem x hy)

/-- A returning run does not agree with a run stopped at an import call. -/
theorem ret_ne_call {P : Profile} {c₁ c₂ d₁ e₂ : Config Nat} (h : ObsAgree P c₁ c₂)
    {r : Result} (h₁ : Runs P c₁ [] d₁) (ho : OutAt d₁ (.ret r))
    (hs : Steps P Det.noHost c₂ e₂) {E : Ctx} {a hh : Nat} {args : List Val}
    (hd : decompose? e₂.store e₂.code = some (E, a, hh, args)) : False := by
  have he : Out.ret r = Out.call hh args := h [] d₁ e₂ _ _ h₁ (.stop hs) ho (.call hd)
  cases he

/-- **Agreeing configurations run against the same oracle make the same import calls**: two
Core runs against `oracleHost F` from output-agreeing configurations that both return without
trapping have the same history of calls and answers. -/
theorem traces_eq {P : Profile} {F : Nat → List Val → Result} :
    ∀ (tr₁ tr₂ : List Call) (c₁ c₂ d₁ d₂ : Config Nat) (r₁ r₂ : Result),
      ObsAgree P c₁ c₂ → Runs P c₁ tr₁ d₁ → Runs P c₂ tr₂ d₂ → Answers F tr₁ → Answers F tr₂ →
      OutAt d₁ (.ret r₁) → OutAt d₂ (.ret r₂) → tr₁ = tr₂ := by
  intro tr₁ tr₂ c₁ c₂ d₁ d₂ r₁ r₂ hA h₁ h₂ hF₁ hF₂ ho₁ ho₂
  induction tr₁ generalizing tr₂ c₁ c₂ with
  | nil =>
    cases h₂ with
    | stop _ => rfl
    | call hs hd _ => exact (ret_ne_call hA h₁ ho₁ hs hd).elim
  | cons x q₁ ih =>
    show x :: q₁ = tr₂
    cases h₁ with
    | call hs₁ hd₁ hk₁ =>
      show _ :: q₁ = tr₂
      cases h₂ with
      | stop hs₂ =>
        exact (ret_ne_call (fun tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂ =>
          (hA tr d₂ d₁ o₂ o₁ h₂ h₁ ho₂ ho₁).symm) (.stop hs₂) ho₂ hs₁ hd₁).elim
      | call hs₂ hd₂ hk₂ =>
        show _ :: q₁ = _ :: _
        rename_i e₁ E₁ a₁ h₁' args₁ ans₁ e₂ E₂ a₂ h₂' args₂ ans₂ q₂
        have hcall : Out.call h₁' args₁ = Out.call h₂' args₂ :=
          hA [] e₁ e₂ _ _ (.stop hs₁) (.stop hs₂) (.call hd₁) (.call hd₂)
        have hh : h₁' = h₂' ∧ args₁ = args₂ := by
          cases hcall
          exact ⟨rfl, rfl⟩
        obtain ⟨rfl, rfl⟩ := hh
        have ha₁ : ans₁ = F h₁' args₁ := hF₁ _ List.mem_cons_self
        have ha₂ : ans₂ = F h₁' args₁ := hF₂ _ List.mem_cons_self
        have hans : ans₁ = ans₂ := ha₁.trans ha₂.symm
        subst hans
        have hA' : ObsAgree P (resumeAt e₁ E₁ ans₁) (resumeAt e₂ E₂ ans₁) :=
          ObsAgree.resume hA ans₁ hs₁ hd₁ hs₂ hd₂
        have hq : q₁ = q₂ := ih q₂ _ _ hA' hk₁ hk₂ (Answers.tail hF₁) (Answers.tail hF₂)
        rw [hq]

/-- **Output agreement against an oracle**: Core runs against `oracleHost F` from two
output-agreeing configurations that both return without trapping return the same result, and
saw the same import calls and answers. -/
theorem obsAgree_oracle {P : Profile} {F : Nat → List Val → Result} {c₁ c₂ d₁ d₂ : Config Nat}
    (hA : ObsAgree P c₁ c₂) (h₁ : Steps P (oracleHost F) c₁ d₁)
    (h₂ : Steps P (oracleHost F) c₂ d₂) {r₁ r₂ : Result} (hr₁ : r₁ ≠ .trap) (hr₂ : r₂ ≠ .trap)
    (hd₁ : d₁.code = r₁.toAdmin) (hd₂ : d₂.code = r₂.toAdmin) :
    r₁ = r₂ ∧ ∃ tr, Runs P c₁ tr d₁ ∧ Runs P c₂ tr d₂ := by
  obtain ⟨tr₁, hR₁, hF₁⟩ := Runs.of_steps h₁
  obtain ⟨tr₂, hR₂, hF₂⟩ := Runs.of_steps h₂
  have ho₁ : OutAt d₁ (.ret r₁) := .ret hr₁ hd₁
  have ho₂ : OutAt d₂ (.ret r₂) := .ret hr₂ hd₂
  have htr : tr₁ = tr₂ := traces_eq tr₁ tr₂ c₁ c₂ d₁ d₂ r₁ r₂ hA hR₁ hR₂ hF₁ hF₂ ho₁ ho₂
  subst htr
  have he : Out.ret r₁ = Out.ret r₂ := hA tr₁ d₁ d₂ _ _ hR₁ hR₂ ho₁ ho₂
  cases he
  exact ⟨rfl, tr₁, hR₁, hR₂⟩

/-- **Determinism against an oracle**: two Core runs from `c` against `oracleHost F` that both
return without trapping return the same result in the same store. -/
theorem detCfg_oracle {P : Profile} {F : Nat → List Val → Result} {c d₁ d₂ : Config Nat}
    (hD : DetCfg P c) (h₁ : Steps P (oracleHost F) c d₁) (h₂ : Steps P (oracleHost F) c d₂)
    {r₁ r₂ : Result} (hr₁ : r₁ ≠ .trap) (hr₂ : r₂ ≠ .trap) (hd₁ : d₁.code = r₁.toAdmin)
    (hd₂ : d₂.code = r₂.toAdmin) : r₁ = r₂ ∧ d₁.store = d₂.store := by
  obtain ⟨hr, tr, hR₁, hR₂⟩ := obsAgree_oracle (DetCfg.obsAgree hD) h₁ h₂ hr₁ hr₂ hd₁ hd₂
  exact ⟨hr, (hD tr d₁ d₂ _ _ hR₁ hR₂ (.ret hr₁ hd₁) (.ret hr₂ hd₂)).2⟩

/-! ## Sufficient conditions -/

/-- Closure of an invariant under host-free runs. -/
theorem inv_steps {P : Profile} {Inv : Config Nat → Prop}
    (hstep : ∀ c d, Inv c → Step P Det.noHost c d → Inv d) {c d : Config Nat}
    (h : Steps P Det.noHost c d) (hc : Inv c) : Inv d := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact hstep _ _ ih hs

/-- Runs from an invariant configuration reach at most one non-trapping stop, as a
configuration. -/
theorem runs_unique {P : Profile} {Inv : Config Nat → Prop} (hI : Closed P Inv)
    (hS : ∀ c, Inv c → SegDet P c) :
    ∀ (tr : List Call) (c d₁ d₂ : Config Nat), Inv c → Runs P c tr d₁ → Runs P c tr d₂ →
      Stop d₁ → Stop d₂ → d₁ = d₂ := by
  intro tr c d₁ d₂ hc h₁ h₂ hs₁ hs₂
  induction tr generalizing c with
  | nil =>
    cases h₁ with
    | stop hs₁' =>
      cases h₂ with
      | stop hs₂' => exact hS c hc d₁ d₂ hs₁' hs₂' hs₁ hs₂
  | cons x q ih =>
    show d₁ = d₂
    cases h₁ with
    | call hs₁' hd₁ hk₁ =>
      show d₁ = d₂
      cases h₂ with
      | call hs₂' hd₂ hk₂ =>
        show d₁ = d₂
        rename_i e₁ E₁ a₁ hh args r e₂ E₂ a₂
        have he : e₁ = e₂ :=
          hS c hc e₁ e₂ hs₁' hs₂' (stop_of_decompose hd₁) (stop_of_decompose hd₂)
        subst he
        have hE : E₁ = E₂ := by
          rw [hd₁] at hd₂
          cases hd₂
          rfl
        subst hE
        have he₁ : Inv e₁ := inv_steps hI.step hs₁' hc
        have hres : Inv (resumeAt e₁ E₁ r) := hI.resume _ _ _ _ _ r he₁ hd₁
        exact ih _ hres hk₁ hk₂

/-- **Determinism from an invariant**: if `Inv` is closed under host-free steps and resumptions
and host-free runs from every `Inv` configuration reach at most one non-trapping stop, every
`Inv` configuration is deterministic modulo traps and imports. -/
theorem detCfg_of_closed {P : Profile} {Inv : Config Nat → Prop} (hI : Closed P Inv)
    (hS : ∀ c, Inv c → SegDet P c) {c : Config Nat} (hc : Inv c) : DetCfg P c := by
  intro tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂
  have he : d₁ = d₂ := runs_unique hI hS tr c d₁ d₂ hc h₁ h₂ ⟨_, ho₁⟩ ⟨_, ho₂⟩
  subst he
  exact ⟨OutAt.unique ho₁ ho₂, rfl⟩

/-- **Steps equal up to doomed ones give unique stops.** -/
theorem segDet_of_stepDet {P : Profile} {Inv : Config Nat → Prop}
    (hstep : ∀ c d, Inv c → Step P Det.noHost c d → Inv d)
    (hD : ∀ c, Inv c → StepDetAt P c) {c : Config Nat} (hc : Inv c) : SegDet P c := by
  intro d₁ d₂ h₁ h₂ hs₁ hs₂
  revert hc d₂
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ d₂ h₂ hs₂ => (Stop.steps_eq hs₁ h₂).symm
  | @head x e₁ hx₁ he₁ ih =>
    intro hx d₂ h₂ hs₂
    rcases Relation.ReflTransGen.cases_head h₂ with rfl | ⟨e₂, hx₂, he₂⟩
    · exact absurd hx₁ (Stop.no_step hs₂)
    · rcases hD x hx e₁ e₂ hx₁ hx₂ with rfl | hdoom | hdoom
      · exact ih (hstep _ _ hx hx₁) d₂ he₂ hs₂
      · exact absurd hs₁ (hdoom d₁ he₁)
      · exact absurd hs₂ (hdoom d₂ he₂)

/-- Runs to a non-trapping stop under `DetUpTo` are runs at the deterministic profile. -/
theorem steps_det_of_detUpTo {P : Profile} {o : GrowOracle} {Inv : Config Nat → Prop}
    (hstep : ∀ c d, Inv c → Step P Det.noHost c d → Inv d)
    (hU : ∀ c, Inv c → DetUpTo P o c) {c d : Config Nat} (h : Steps P Det.noHost c d)
    (hd : Stop d) : Inv c → Steps (profile o) Det.noHost c d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ => .refl
  | @head x e hxe hed ih =>
    intro hx
    rcases hU x hx e hxe with hD | hdoom
    · exact Relation.ReflTransGen.head hD (ih (hstep _ _ hx hxe))
    · exact absurd hd (hdoom d hed)

/-- Host-free Core runs are runs of the machine. -/
theorem reach_of_steps {P : Profile} {c d : Config Nat} (h : Steps P Det.noHost c d) :
    Silmaril.Wasm.Game.Reach P (thr c) (thr d) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (internal_of_step hs)

/-- The thread of a configuration determines it. -/
theorem thr_injective {c d : Config Nat} (h : thr c = thr d) : c = d := by
  rcases c with ⟨s, f, code⟩
  rcases d with ⟨s', f', code'⟩
  have h₁ : s = s' ∧ Thread.active f code = Thread.active f' code' := Prod.mk.inj h
  have h₂ : f = f' ∧ code = code' := Thread.active.inj h₁.2
  rw [h₁.1, h₂.1, h₂.2]

/-- A non-trapping stop is a normal form of the machine. -/
theorem Stop.normal {P : Profile} {d : Config Nat} (hd : Stop d) :
    ∀ z, ¬ Silmaril.Wasm.Game.InternalP P (thr d) z := by
  rintro z ⟨f', code', -, hz⟩
  exact Stop.no_step (e := ⟨z.1, f', code'⟩) hd hz

/-- **Steps of a deterministic profile up to doomed ones give unique stops** (silmaril-lean's
uniqueness of normal forms at `profile o`, `reach_normal_unique`). -/
theorem segDet_of_detUpTo {P : Profile} {o : GrowOracle} {Inv : Config Nat → Prop}
    (hstep : ∀ c d, Inv c → Step P Det.noHost c d → Inv d)
    (hU : ∀ c, Inv c → DetUpTo P o c) {c : Config Nat} (hc : Inv c) : SegDet P c := by
  intro d₁ d₂ h₁ h₂ hs₁ hs₂
  have hD₁ : Steps (profile o) Det.noHost c d₁ := steps_det_of_detUpTo hstep hU h₁ hs₁ hc
  have hD₂ : Steps (profile o) Det.noHost c d₂ := steps_det_of_detUpTo hstep hU h₂ hs₂ hc
  have ht : thr d₁ = thr d₂ :=
    Silmaril.Wasm.Game.reach_normal_unique (reach_of_steps hD₁) (reach_of_steps hD₂)
      (Stop.normal hs₁) (Stop.normal hs₂)
  exact thr_injective ht

/-- **Doomed configurations are deterministic** (they have no non-trapping stop). -/
theorem Doomed.detCfg {P : Profile} {c : Config Nat} (h : Doomed P c) : DetCfg P c := by
  intro tr d₁ d₂ o₁ o₂ h₁ _ ho₁ _
  cases h₁ with
  | stop hs => exact absurd ⟨_, ho₁⟩ (h d₁ hs)
  | call hs hd _ => exact absurd (stop_of_decompose hd) (h _ hs)

/-- Doomed configurations agree with every configuration. -/
theorem Doomed.obsAgree {P : Profile} {c₁ : Config Nat} (h : Doomed P c₁) (c₂ : Config Nat) :
    ObsAgree P c₁ c₂ := by
  intro tr d₁ d₂ o₁ o₂ h₁ _ ho₁ _
  cases h₁ with
  | stop hs => exact absurd ⟨_, ho₁⟩ (h d₁ hs)
  | call hs hd _ => exact absurd (stop_of_decompose hd) (h _ hs)

/-! ## Lock-step relations -/

/-- Host-free runs from lock-step related configurations to non-trapping stops end in related
stops. -/
theorem lockStep_seg {P : Profile} {R : Config Nat → Config Nat → Prop} (hL : LockStep P R)
    {x sx : Config Nat} (hx : Steps P Det.noHost x sx) (hsx : Stop sx) :
    ∀ y sy, R x y → Steps P Det.noHost y sy → Stop sy → R sx sy := by
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro y sy hxy hy hsy
    have hy' : Stop y := hL.stop_left _ _ hxy hsx
    have he : sy = y := Stop.steps_eq hy' hy
    rw [he]
    exact hxy
  | @head x x' hxx' hx'sx ih =>
    intro y sy hxy hy hsy
    show R sx sy
    rcases Relation.ReflTransGen.cases_head hy with rfl | ⟨y', hyy', hy'sy⟩
    · have hx : Stop x := hL.stop_right _ _ hxy hsy
      exact absurd hxx' (Stop.no_step hx)
    · rcases hL.step x y x' y' hxy hxx' hyy' with hR | hd | hd
      · exact ih y' sy hR hy'sy hsy
      · exact absurd hsx (hd sx hx'sx)
      · exact absurd hsy (hd sy hy'sy)

/-- Runs with the same calls from lock-step related configurations to non-trapping stops end in
related stops. -/
theorem lockStep_runs {P : Profile} {R : Config Nat → Config Nat → Prop} (hL : LockStep P R) :
    ∀ (tr : List Call) (c₁ c₂ d₁ d₂ : Config Nat), R c₁ c₂ → Runs P c₁ tr d₁ →
      Runs P c₂ tr d₂ → Stop d₁ → Stop d₂ → R d₁ d₂ := by
  intro tr c₁ c₂ d₁ d₂ hR h₁ h₂ hs₁ hs₂
  induction tr generalizing c₁ c₂ with
  | nil =>
    cases h₁ with
    | stop hs₁' =>
      cases h₂ with
      | stop hs₂' => exact lockStep_seg hL hs₁' hs₁ c₂ d₂ hR hs₂' hs₂
  | cons x q ih =>
    show R d₁ d₂
    cases h₁ with
    | call hs₁' hd₁ hk₁ =>
      show R d₁ d₂
      cases h₂ with
      | call hs₂' hd₂ hk₂ =>
        show R d₁ d₂
        rename_i e₁ E₁ a₁ hh args r e₂ E₂ a₂
        have he : R e₁ e₂ :=
          lockStep_seg hL hs₁' (stop_of_decompose hd₁) _ _ hR hs₂' (stop_of_decompose hd₂)
        have hres : R (resumeAt e₁ E₁ r) (resumeAt e₂ E₂ r) :=
          hL.resume e₁ e₂ E₁ E₂ a₁ a₂ hh args r he hd₁ hd₂
        exact ih _ _ hres hk₁ hk₂

/-- **Lock-step related configurations agree on their non-trapping outputs.** -/
theorem obsAgree_of_lockStep {P : Profile} {R : Config Nat → Config Nat → Prop}
    (hL : LockStep P R) {c₁ c₂ : Config Nat} (h : R c₁ c₂) : ObsAgree P c₁ c₂ := by
  intro tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂
  have hR : R d₁ d₂ := lockStep_runs hL tr c₁ c₂ d₁ d₂ h h₁ h₂ ⟨_, ho₁⟩ ⟨_, ho₂⟩
  exact hL.out d₁ d₂ o₁ o₂ hR ho₁ ho₂

/-! ## Monotonicity in the profile -/

theorem DetCfg.mono {P' P : Profile} (hP : ProfileLE P' P) {c : Config Nat} (h : DetCfg P c) :
    DetCfg P' c :=
  fun tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂ =>
    h tr d₁ d₂ o₁ o₂ (Runs.mono hP h₁) (Runs.mono hP h₂) ho₁ ho₂

theorem ObsAgree.mono {P' P : Profile} (hP : ProfileLE P' P) {c₁ c₂ : Config Nat}
    (h : ObsAgree P c₁ c₂) : ObsAgree P' c₁ c₂ :=
  fun tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂ =>
    h tr d₁ d₂ o₁ o₂ (Runs.mono hP h₁) (Runs.mono hP h₂) ho₁ ho₂

theorem CallReach.mono {P' P : Profile} (hP : ProfileLE P' P) {Entry : Nat → Prop}
    {s₀ s : Store Nat} (h : CallReach P' Entry s₀ s) : CallReach P Entry s₀ s := by
  induction h with
  | init => exact .init
  | call _ ha hok hr hd ih => exact .call ih ha hok (Runs.mono hP hr) hd

end Silmaril.Proofs.Wasm.Det.Core
