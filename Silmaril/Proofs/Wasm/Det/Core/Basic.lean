module

public import Silmaril.Wasm.Det.Core.Defs
public import Silmaril.Wasm.Game.Machine.Thms
public import Silmaril.Wasm.SingleThreaded.Locality

/-!
# Determinism and statelessness modulo traps and imports: basic facts

* outputs: `OutAt.unique` (a configuration has at most one output), `Stop.no_step` (a
  non-trapping stop has no host-free step at any profile);
* function instances never change: `steps_funcs_eq`, `Runs.funcs_eq`, `CallReach.funcs_eq`;
* runs: `Runs.head`, `Runs.append_stop`, `Runs.mono` (profile refinement), `Runs.of_steps`
  (a Core run against `oracleHost F` is a run whose answers are `F`'s);
* propagation of `ObsAgree`/`DetCfg` through a shared import call (`ObsAgree.resume`,
  `DetCfg.resume`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

/-! ## Outputs -/

theorem val_toAdmin_injective : Function.Injective Val.toAdmin := by
  intro v w h
  have h' : v.toAdmin.val? = w.toAdmin.val? := congrArg Admin.val? h
  simpa only [Admin.val?_toAdmin, Option.some.injEq] using h'

/-- The values of a list never end with `THROW_REF`. -/
theorem vals_ne_throwing (vs : List Val) (a : Nat) : vals vs ≠ throwing a := by
  intro h
  have h' : (vals vs).map Admin.val? = (throwing a).map Admin.val? := congrArg _ h
  have hl : (vals vs).map Admin.val? = vs.map some := by
    simp only [vals, List.map_map, Function.comp_def, Admin.val?_toAdmin]
  have hr : (throwing a).map Admin.val? = [some (.ref (.exn a)), none] := rfl
  rw [hl, hr] at h'
  have hn : none ∈ vs.map some := by rw [h']; simp
  simp at hn

/-- Non-trapping results are determined by their code. -/
theorem toAdmin_inj {r₁ r₂ : Result} (h₁ : r₁ ≠ .trap) (h₂ : r₂ ≠ .trap)
    (h : r₁.toAdmin = r₂.toAdmin) : r₁ = r₂ := by
  cases r₁ with
  | values vs =>
    cases r₂ with
    | values ws => exact congrArg Result.values (vals_injective h)
    | throw b => exact absurd h (vals_ne_throwing vs b)
    | trap => exact absurd rfl h₂
  | throw a =>
    cases r₂ with
    | values ws => exact absurd h.symm (vals_ne_throwing ws a)
    | throw b =>
      have hb : (Admin.ref (.exn a)) = .ref (.exn b) := (List.cons.inj h).1
      cases hb
      rfl
    | trap => exact absurd rfl h₂
  | trap => exact absurd rfl h₁

/-- A non-trapping result is not an import call. -/
theorem decompose?_toAdmin {s : Store Nat} {r : Result} (hr : r ≠ .trap) :
    decompose? s r.toAdmin = none := by
  cases r with
  | values vs => exact decompose?_vals_nil
  | throw a =>
    exact decompose?_vals_cons_none (vs := [.ref (.exn a)]) (d := .plain .throwRef) (r := [])
      rfl (fun _ _ => decompHead_plain rfl)
  | trap => exact absurd rfl hr

/-- **A configuration has at most one output.** -/
theorem OutAt.unique {c : Config Nat} {o₁ o₂ : Out} (h₁ : OutAt c o₁) (h₂ : OutAt c o₂) :
    o₁ = o₂ := by
  cases h₁ with
  | ret hr hc =>
    cases h₂ with
    | ret hr' hc' => exact congrArg Out.ret (toAdmin_inj hr hr' (hc.symm.trans hc'))
    | call hd =>
      have hn : decompose? c.store c.code = none := by rw [hc]; exact decompose?_toAdmin hr
      rw [hn] at hd
      cases hd
  | call hd =>
    cases h₂ with
    | ret hr hc =>
      have hn : decompose? c.store c.code = none := by rw [hc]; exact decompose?_toAdmin hr
      rw [hn] at hd
      cases hd
    | call hd' =>
      rw [hd] at hd'
      cases hd'
      rfl

/-- The thread of a configuration. -/
def thr (c : Config Nat) : Store Nat × Thread := (c.store, .active c.frame c.code)

/-- A host-free Core step is an internal step of the machine. -/
theorem internal_of_step {P : Profile} {c e : Config Nat} (h : Step P Det.noHost c e) :
    Silmaril.Wasm.Game.InternalP P (thr c) (thr e) :=
  ⟨e.frame, e.code, rfl, h⟩

/-- **A non-trapping stop has no host-free step**, at any profile. -/
theorem Stop.no_step {P : Profile} {c e : Config Nat} (hc : Stop c) :
    ¬ Step P Det.noHost c e := by
  intro h
  obtain ⟨o, ho⟩ := hc
  cases ho with
  | ret _ hc' =>
    exact Silmaril.Wasm.Game.resultAt_no_internal (t := .active c.frame c.code) hc' _
      (internal_of_step h)
  | call hd =>
    exact Silmaril.Wasm.Game.calloutAt_no_internal (t := .active c.frame c.code) ⟨_, _, hd⟩ _
      (internal_of_step h)

/-- A host-free run from a non-trapping stop stays there. -/
theorem Stop.steps_eq {P : Profile} {c d : Config Nat} (hc : Stop c)
    (h : Steps P Det.noHost c d) : d = c := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨e, he, -⟩
  · rfl
  · exact absurd he (Stop.no_step hc)

/-- An import call is a non-trapping stop. -/
theorem stop_of_decompose {d : Config Nat} {E : Ctx} {a h : Nat} {args : List Val}
    (hd : decompose? d.store d.code = some (E, a, h, args)) : Stop d :=
  ⟨_, .call hd⟩

/-! ## Runs -/

/-- Prepend a host-free step to a run. -/
theorem Runs.head {P : Profile} {c c' d : Config Nat} {tr : List Call}
    (h : Step P Det.noHost c c') (hr : Runs P c' tr d) : Runs P c tr d := by
  cases hr with
  | stop hs => exact .stop (Relation.ReflTransGen.head h hs)
  | call hs hd hk => exact .call (Relation.ReflTransGen.head h hs) hd hk

/-- Prepend a host-free run to a run. -/
theorem Runs.steps_head {P : Profile} {c c' d : Config Nat} {tr : List Call}
    (h : Steps P Det.noHost c c') (hr : Runs P c' tr d) : Runs P c tr d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hr
  | head hs _ ih => exact Runs.head hs ih

/-- Runs at a refining profile are runs. -/
theorem steps_mono {P' P : Profile} (hP : ProfileLE P' P) {c d : Config Nat}
    (h : Steps P' Det.noHost c d) : Steps P Det.noHost c d :=
  Relation.ReflTransGen.mono (fun x y hxy => hP x y hxy) _ _ h

/-- **Runs at a refining profile are runs.** -/
theorem Runs.mono {P' P : Profile} (hP : ProfileLE P' P) {c d : Config Nat} {tr : List Call}
    (h : Runs P' c tr d) : Runs P c tr d := by
  induction h with
  | stop hs => exact .stop (steps_mono hP hs)
  | call hs hd _ ih => exact .call (steps_mono hP hs) hd ih

/-- A step against `oracleHost F` is a host-free step, or the resumption of an import call
with `F`'s answer. -/
theorem step_oracle_cases {P : Profile} {F : Nat → List Val → Result} {c c' : Config Nat}
    (h : Step P (oracleHost F) c c') :
    Step P Det.noHost c c' ∨ ∃ E a hh args, decompose? c.store c.code = some (E, a, hh, args) ∧
      c' = resumeAt c E (F hh args) := by
  rcases Step.split_host h with h' | ⟨E, a, hh, args, hd, hres⟩
  · exact .inl h'
  · rcases hres with ⟨s', r, hhost, rfl⟩ | ⟨hdiv, -⟩
    · have he : Execution.Host.Outcome.returned s' r = .returned c.store (F hh args) := hhost
      cases he
      exact .inr ⟨E, a, hh, args, hd, rfl⟩
    · cases hdiv

/-- **A Core run against `oracleHost F` is a run whose answers are `F`'s.** -/
theorem Runs.of_steps {P : Profile} {F : Nat → List Val → Result} {c d : Config Nat}
    (h : Steps P (oracleHost F) c d) : ∃ tr, Runs P c tr d ∧ Answers F tr := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .stop .refl, fun _ hx => by cases hx⟩
  | head hs _ ih =>
    obtain ⟨tr, hr, hF⟩ := ih
    rcases step_oracle_cases hs with h' | ⟨E, a, hh, args, hd, rfl⟩
    · exact ⟨tr, Runs.head h' hr, hF⟩
    · refine ⟨⟨hh, args, F hh args⟩ :: tr, .call .refl hd hr, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · rfl
      · exact hF x hx'

/-! ## Function instances never change -/

/-- Host-free runs keep the function instances (silmaril-lean's `Step.framesLocal`). -/
theorem steps_funcs_eq {P : Profile} {c d : Config Nat} (h : Steps P Det.noHost c d) :
    d.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hst ih => exact (Step.framesLocal hst).1.trans ih

/-- **Runs keep the function instances** (answers do not write the store). -/
theorem Runs.funcs_eq {P : Profile} {c d : Config Nat} {tr : List Call} (h : Runs P c tr d) :
    d.store.funcs = c.store.funcs := by
  induction h with
  | stop hs => exact steps_funcs_eq hs
  | call hs _ _ ih =>
    have h' := steps_funcs_eq hs
    exact ih.trans h'

/-- **The call states of a module have the function instances of the initial store.** -/
theorem CallReach.funcs_eq {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (h : CallReach P Entry s₀ s) : s.funcs = s₀.funcs := by
  induction h with
  | init => rfl
  | call _ _ _ hr _ ih => exact (Runs.funcs_eq hr).trans ih

/-! ## Propagation through a shared import call -/

/-- Output agreement propagates through an import call both sides make with the same answer. -/
theorem ObsAgree.resume {P : Profile} {c₁ c₂ e₁ e₂ : Config Nat} (h : ObsAgree P c₁ c₂)
    {E₁ E₂ : Ctx} {a₁ a₂ hh : Nat} {args : List Val} (r : Result)
    (hs₁ : Steps P Det.noHost c₁ e₁) (hd₁ : decompose? e₁.store e₁.code = some (E₁, a₁, hh, args))
    (hs₂ : Steps P Det.noHost c₂ e₂) (hd₂ : decompose? e₂.store e₂.code = some (E₂, a₂, hh, args)) :
    ObsAgree P (resumeAt e₁ E₁ r) (resumeAt e₂ E₂ r) :=
  fun tr d₁ d₂ o₁ o₂ hr₁ hr₂ ho₁ ho₂ =>
    h (⟨hh, args, r⟩ :: tr) d₁ d₂ o₁ o₂ (.call hs₁ hd₁ hr₁) (.call hs₂ hd₂ hr₂) ho₁ ho₂

/-- Determinism of the continuation after an import call. -/
theorem DetCfg.resume {P : Profile} {c e : Config Nat} (h : DetCfg P c) {E : Ctx}
    {a hh : Nat} {args : List Val} (r : Result) (hs : Steps P Det.noHost c e)
    (hd : decompose? e.store e.code = some (E, a, hh, args)) : DetCfg P (resumeAt e E r) :=
  fun tr d₁ d₂ o₁ o₂ hr₁ hr₂ ho₁ ho₂ =>
    h (⟨hh, args, r⟩ :: tr) d₁ d₂ o₁ o₂ (.call hs hd hr₁) (.call hs hd hr₂) ho₁ ho₂

/-- Determinism gives output agreement of a configuration with itself. -/
theorem DetCfg.obsAgree {P : Profile} {c : Config Nat} (h : DetCfg P c) : ObsAgree P c c :=
  fun tr d₁ d₂ o₁ o₂ hr₁ hr₂ ho₁ ho₂ => (h tr d₁ d₂ o₁ o₂ hr₁ hr₂ ho₁ ho₂).1

end Silmaril.Proofs.Wasm.Det.Core
