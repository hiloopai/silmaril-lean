module

public import Silmaril.Wasm.Det.Core.Defs
public import Silmaril.Proofs.Wasm.Det.Core.Main

/-!
# Determinism and statelessness modulo traps and imports (Core 3.0): theorems

Every statement holds at an **arbitrary** profile `P`.

**Headline consequences** (imports answered by an oracle host `oracleHost F`; the general,
history-dependent form is the definition itself, over `Runs` with a shared call list):

* `detCfg_oracle`, `DetFn.oracle`, `DetModule.oracle`: given the same call state (a store
  reachable by the module) and the same import answers, two Core runs of an export call that
  both return without trapping return the same result in the same store;
* `obsAgree_oracle`, `StatelessFn.oracle`, `StatelessModule.history`: for a stateless function,
  two such runs from *different* call states return the same result; for a stateless module,
  the result of a call after any history of calls is the result of the same call in the initial
  store;
* `traces_eq`: the two runs also made the same import calls with the same arguments.

**Sufficient conditions** (for the subset strands):

* `detCfg_of_closed`: an invariant `Inv` closed under host-free steps and resumptions
  (`Closed P Inv`) on which host-free runs reach at most one non-trapping stop (`SegDet`);
* `segDet_of_stepDet`: two host-free steps from an `Inv` configuration are equal or one is
  `Doomed` (`StepDetAt`). `Silmaril.Proofs.Wasm.Game.Choice.soft_join` (two host-free steps are
  equal or both `Soft`) gives `StepDetAt P c` as soon as every `Soft` step from `c` is
  `Doomed`; the bridge is a three-line proof, not stated here because `Soft` has no header;
* `segDet_of_detUpTo`: every host-free step from an `Inv` configuration at `P` is a step at a
  deterministic profile `profile o`, or `Doomed` (`DetUpTo`); uniqueness of normal forms at
  `profile o` (silmaril-lean, `reach_normal_unique`) does the rest, including bubbling;
* `obsAgree_of_lockStep`, `statelessFn_of_lockStep`: a lock-step relation (`LockStep`) between
  the configurations of two runs gives output agreement; this is the entry point for
  determinism up to NaN payloads and for statelessness (two call states related by what the
  code may read);
* `Doomed.detCfg`, `Doomed.obsAgree`.

**Combinators**: `DetCfg.obsAgree`, `DetCfg.resume`, `ObsAgree.resume` (through a shared import
call), monotonicity in the profile (`DetCfg.mono`, `ObsAgree.mono`, `DetFn.mono`,
`DetModule.mono`, `StatelessFn.mono`, `StatelessModule.mono`, `CallReach.mono`),
`StatelessFn.anti` (fewer call states), `StatelessFn.detOut`, `Runs.funcs_eq` and
`CallReach.funcs_eq` (function instances never change), (a stateless function has
deterministic outputs), `OutAt.unique`, `Stop.no_step`, `Runs.of_steps`, `Runs.mono`.

Proofs: `Silmaril.Proofs.Wasm.Det.Core.{Basic,Main}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## Basic facts -/

/-- A configuration has at most one output. -/
theorem OutAt.unique {c : Config Nat} {o₁ o₂ : Out} (h₁ : OutAt c o₁) (h₂ : OutAt c o₂) :
    o₁ = o₂ :=
  Silmaril.Proofs.Wasm.Det.Core.OutAt.unique h₁ h₂

/-- A non-trapping stop has no host-free step, at any profile. -/
theorem Stop.no_step {P : Profile} {c e : Config Nat} (hc : Stop c) :
    ¬ Step P Det.noHost c e :=
  Silmaril.Proofs.Wasm.Det.Core.Stop.no_step hc

/-- A Core run against `oracleHost F` is a run whose answers are `F`'s. -/
theorem Runs.of_steps {P : Profile} {F : Nat → List Val → Result} {c d : Config Nat}
    (h : Steps P (oracleHost F) c d) : ∃ tr, Runs P c tr d ∧ Answers F tr :=
  Silmaril.Proofs.Wasm.Det.Core.Runs.of_steps h

/-- Runs at a refining profile are runs. -/
theorem Runs.mono {P' P : Profile} (hP : ProfileLE P' P) {c d : Config Nat} {tr : List Call}
    (h : Runs P' c tr d) : Runs P c tr d :=
  Silmaril.Proofs.Wasm.Det.Core.Runs.mono hP h

/-- Runs keep the function instances. -/
theorem Runs.funcs_eq {P : Profile} {c d : Config Nat} {tr : List Call} (h : Runs P c tr d) :
    d.store.funcs = c.store.funcs :=
  Silmaril.Proofs.Wasm.Det.Core.Runs.funcs_eq h

/-- The call states of a module have the function instances of the initial store. -/
theorem CallReach.funcs_eq {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (h : CallReach P Entry s₀ s) : s.funcs = s₀.funcs :=
  Silmaril.Proofs.Wasm.Det.Core.CallReach.funcs_eq h

/-- Determinism gives output agreement of a configuration with itself. -/
theorem DetCfg.obsAgree {P : Profile} {c : Config Nat} (h : DetCfg P c) : ObsAgree P c c :=
  Silmaril.Proofs.Wasm.Det.Core.DetCfg.obsAgree h

/-- Determinism of the continuation after an import call. -/
theorem DetCfg.resume {P : Profile} {c e : Config Nat} (h : DetCfg P c) {E : Ctx}
    {a hh : Nat} {args : List Val} (r : Result) (hs : Steps P Det.noHost c e)
    (hd : decompose? e.store e.code = some (E, a, hh, args)) : DetCfg P (resumeAt e E r) :=
  Silmaril.Proofs.Wasm.Det.Core.DetCfg.resume h r hs hd

/-- Output agreement propagates through an import call both sides make with the same answer. -/
theorem ObsAgree.resume {P : Profile} {c₁ c₂ e₁ e₂ : Config Nat} (h : ObsAgree P c₁ c₂)
    {E₁ E₂ : Ctx} {a₁ a₂ hh : Nat} {args : List Val} (r : Result)
    (hs₁ : Steps P Det.noHost c₁ e₁) (hd₁ : decompose? e₁.store e₁.code = some (E₁, a₁, hh, args))
    (hs₂ : Steps P Det.noHost c₂ e₂) (hd₂ : decompose? e₂.store e₂.code = some (E₂, a₂, hh, args)) :
    ObsAgree P (resumeAt e₁ E₁ r) (resumeAt e₂ E₂ r) :=
  Silmaril.Proofs.Wasm.Det.Core.ObsAgree.resume h r hs₁ hd₁ hs₂ hd₂

/-! ## The headline consequences -/

/-- **Same calls**: Core runs against `oracleHost F` from output-agreeing configurations that
both return without trapping made the same import calls with the same arguments and answers. -/
theorem traces_eq {P : Profile} {F : Nat → List Val → Result} (tr₁ tr₂ : List Call)
    (c₁ c₂ d₁ d₂ : Config Nat) (r₁ r₂ : Result) (hA : ObsAgree P c₁ c₂)
    (h₁ : Runs P c₁ tr₁ d₁) (h₂ : Runs P c₂ tr₂ d₂) (hF₁ : Answers F tr₁) (hF₂ : Answers F tr₂)
    (ho₁ : OutAt d₁ (.ret r₁)) (ho₂ : OutAt d₂ (.ret r₂)) : tr₁ = tr₂ :=
  Silmaril.Proofs.Wasm.Det.Core.traces_eq tr₁ tr₂ c₁ c₂ d₁ d₂ r₁ r₂ hA h₁ h₂ hF₁ hF₂ ho₁ ho₂

/-- **Output agreement against an oracle**: Core runs against `oracleHost F` from two
output-agreeing configurations that both return without trapping return the same result. -/
theorem obsAgree_oracle {P : Profile} {F : Nat → List Val → Result} {c₁ c₂ d₁ d₂ : Config Nat}
    (hA : ObsAgree P c₁ c₂) (h₁ : Steps P (oracleHost F) c₁ d₁)
    (h₂ : Steps P (oracleHost F) c₂ d₂) {r₁ r₂ : Result} (hr₁ : r₁ ≠ .trap) (hr₂ : r₂ ≠ .trap)
    (hd₁ : d₁.code = r₁.toAdmin) (hd₂ : d₂.code = r₂.toAdmin) :
    r₁ = r₂ ∧ ∃ tr, Runs P c₁ tr d₁ ∧ Runs P c₂ tr d₂ :=
  Silmaril.Proofs.Wasm.Det.Core.obsAgree_oracle hA h₁ h₂ hr₁ hr₂ hd₁ hd₂

/-- **Determinism against an oracle**: two Core runs from `c` against `oracleHost F` that both
return without trapping return the same result in the same store. -/
theorem detCfg_oracle {P : Profile} {F : Nat → List Val → Result} {c d₁ d₂ : Config Nat}
    (hD : DetCfg P c) (h₁ : Steps P (oracleHost F) c d₁) (h₂ : Steps P (oracleHost F) c d₂)
    {r₁ r₂ : Result} (hr₁ : r₁ ≠ .trap) (hr₂ : r₂ ≠ .trap) (hd₁ : d₁.code = r₁.toAdmin)
    (hd₂ : d₂.code = r₂.toAdmin) : r₁ = r₂ ∧ d₁.store = d₂.store :=
  Silmaril.Proofs.Wasm.Det.Core.detCfg_oracle hD h₁ h₂ hr₁ hr₂ hd₁ hd₂

/-- **Per function**: two Core runs of the same typed invocation against the same oracle that
both return without trapping return the same result in the same store. -/
theorem DetFn.oracle {P : Profile} {s : Store Nat} {a : Nat} (hD : DetFn P s a) {vs : List Val}
    (hok : InvokeOk s a vs) {F : Nat → List Val → Result} {d₁ d₂ : Config Nat}
    (h₁ : Steps P (oracleHost F) (invoke s a vs) d₁)
    (h₂ : Steps P (oracleHost F) (invoke s a vs) d₂)
    {r₁ r₂ : Result} (hr₁ : r₁ ≠ .trap) (hr₂ : r₂ ≠ .trap) (hd₁ : d₁.code = r₁.toAdmin)
    (hd₂ : d₂.code = r₂.toAdmin) : r₁ = r₂ ∧ d₁.store = d₂.store :=
  detCfg_oracle (hD vs hok) h₁ h₂ hr₁ hr₂ hd₁ hd₂

/-- **Per module: the same call state gives the same non-trapping result.** At a call state `s`
reachable by the module, two Core runs of an entry call against the same oracle that both
return without trapping return the same result in the same store. -/
theorem DetModule.oracle {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (hD : DetModule P Entry s₀) (hs : CallReach P Entry s₀ s) {a : Nat} (ha : Entry a)
    {vs : List Val} (hok : InvokeOk s a vs) {F : Nat → List Val → Result} {d₁ d₂ : Config Nat}
    (h₁ : Steps P (oracleHost F) (invoke s a vs) d₁)
    (h₂ : Steps P (oracleHost F) (invoke s a vs) d₂)
    {r₁ r₂ : Result} (hr₁ : r₁ ≠ .trap) (hr₂ : r₂ ≠ .trap) (hd₁ : d₁.code = r₁.toAdmin)
    (hd₂ : d₂.code = r₂.toAdmin) : r₁ = r₂ ∧ d₁.store = d₂.store :=
  DetFn.oracle (hD s hs a ha) hok h₁ h₂ hr₁ hr₂ hd₁ hd₂

/-- **Per function, statelessness: non-trapping results do not depend on the call state.** -/
theorem StatelessFn.oracle {P : Profile} {S : Store Nat → Prop} {a : Nat}
    (hS : StatelessFn P S a) {s₁ s₂ : Store Nat} (hs₁ : S s₁) (hs₂ : S s₂) {vs : List Val}
    (hok₁ : InvokeOk s₁ a vs) (hok₂ : InvokeOk s₂ a vs) {F : Nat → List Val → Result}
    {d₁ d₂ : Config Nat} (h₁ : Steps P (oracleHost F) (invoke s₁ a vs) d₁)
    (h₂ : Steps P (oracleHost F) (invoke s₂ a vs) d₂) {r₁ r₂ : Result} (hr₁ : r₁ ≠ .trap)
    (hr₂ : r₂ ≠ .trap) (hd₁ : d₁.code = r₁.toAdmin) (hd₂ : d₂.code = r₂.toAdmin) : r₁ = r₂ :=
  (obsAgree_oracle (hS s₁ s₂ vs hs₁ hs₂ hok₁ hok₂) h₁ h₂ hr₁ hr₂ hd₁ hd₂).1

/-- **Per module, statelessness: earlier calls do not affect later non-trapping results.** A
call at any reachable call state returns, when it does not trap, what the same call returns in
the initial store. -/
theorem StatelessModule.history {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (hS : StatelessModule P Entry s₀) (hs : CallReach P Entry s₀ s) {a : Nat} (ha : Entry a)
    {vs : List Val} (hok₀ : InvokeOk s₀ a vs) (hok : InvokeOk s a vs)
    {F : Nat → List Val → Result} {d₀ d : Config Nat}
    (h₀ : Steps P (oracleHost F) (invoke s₀ a vs) d₀)
    (h : Steps P (oracleHost F) (invoke s a vs) d)
    {r₀ r : Result} (hr₀ : r₀ ≠ .trap) (hr : r ≠ .trap) (hd₀ : d₀.code = r₀.toAdmin)
    (hd : d.code = r.toAdmin) : r = r₀ :=
  StatelessFn.oracle (hS a ha) hs .init hok hok₀ h h₀ hr hr₀ hd hd₀

/-! ## Sufficient conditions -/

/-- **Determinism from an invariant**: if `Inv` is closed under host-free steps and resumptions
and host-free runs from every `Inv` configuration reach at most one non-trapping stop, every
`Inv` configuration is deterministic modulo traps and imports. -/
theorem detCfg_of_closed {P : Profile} {Inv : Config Nat → Prop} (hI : Closed P Inv)
    (hS : ∀ c, Inv c → SegDet P c) {c : Config Nat} (hc : Inv c) : DetCfg P c :=
  Silmaril.Proofs.Wasm.Det.Core.detCfg_of_closed hI hS hc

/-- **Steps equal up to doomed ones give unique stops.** -/
theorem segDet_of_stepDet {P : Profile} {Inv : Config Nat → Prop}
    (hstep : ∀ c d, Inv c → Step P Det.noHost c d → Inv d)
    (hD : ∀ c, Inv c → StepDetAt P c) {c : Config Nat} (hc : Inv c) : SegDet P c :=
  Silmaril.Proofs.Wasm.Det.Core.segDet_of_stepDet hstep hD hc

/-- **Steps of a deterministic profile up to doomed ones give unique stops.** -/
theorem segDet_of_detUpTo {P : Profile} {o : GrowOracle} {Inv : Config Nat → Prop}
    (hstep : ∀ c d, Inv c → Step P Det.noHost c d → Inv d)
    (hU : ∀ c, Inv c → DetUpTo P o c) {c : Config Nat} (hc : Inv c) : SegDet P c :=
  Silmaril.Proofs.Wasm.Det.Core.segDet_of_detUpTo hstep hU hc

/-- Determinism from an invariant on which steps are equal up to doomed ones. -/
theorem detCfg_of_stepDet {P : Profile} {Inv : Config Nat → Prop} (hI : Closed P Inv)
    (hD : ∀ c, Inv c → StepDetAt P c) {c : Config Nat} (hc : Inv c) : DetCfg P c :=
  detCfg_of_closed hI (fun _ h => segDet_of_stepDet hI.step hD h) hc

/-- Determinism from an invariant on which steps are deterministic-profile steps up to doomed
ones. -/
theorem detCfg_of_detUpTo {P : Profile} {o : GrowOracle} {Inv : Config Nat → Prop}
    (hI : Closed P Inv) (hU : ∀ c, Inv c → DetUpTo P o c) {c : Config Nat} (hc : Inv c) :
    DetCfg P c :=
  detCfg_of_closed hI (fun _ h => segDet_of_detUpTo hI.step hU h) hc

/-- **Lock-step related configurations agree on their non-trapping outputs** (output
determinism up to a relation, e.g. NaN payloads; statelessness for related call states). -/
theorem obsAgree_of_lockStep {P : Profile} {R : Config Nat → Config Nat → Prop}
    (hL : LockStep P R) {c₁ c₂ : Config Nat} (h : R c₁ c₂) : ObsAgree P c₁ c₂ :=
  Silmaril.Proofs.Wasm.Det.Core.obsAgree_of_lockStep hL h

/-- Statelessness from a lock-step relation relating the invocations in any two call states. -/
theorem statelessFn_of_lockStep {P : Profile} {S : Store Nat → Prop} {a : Nat}
    {R : Config Nat → Config Nat → Prop} (hL : LockStep P R)
    (h : ∀ s₁ s₂ vs, S s₁ → S s₂ → InvokeOk s₁ a vs → InvokeOk s₂ a vs →
      R (invoke s₁ a vs) (invoke s₂ a vs)) : StatelessFn P S a :=
  fun s₁ s₂ vs h₁ h₂ hok₁ hok₂ => obsAgree_of_lockStep hL (h s₁ s₂ vs h₁ h₂ hok₁ hok₂)

/-- Doomed configurations are deterministic. -/
theorem Doomed.detCfg {P : Profile} {c : Config Nat} (h : Doomed P c) : DetCfg P c :=
  Silmaril.Proofs.Wasm.Det.Core.Doomed.detCfg h

/-- Doomed configurations agree with every configuration. -/
theorem Doomed.obsAgree {P : Profile} {c₁ : Config Nat} (h : Doomed P c₁) (c₂ : Config Nat) :
    ObsAgree P c₁ c₂ :=
  Silmaril.Proofs.Wasm.Det.Core.Doomed.obsAgree h c₂

/-! ## Combinators -/

theorem DetCfg.mono {P' P : Profile} (hP : ProfileLE P' P) {c : Config Nat} (h : DetCfg P c) :
    DetCfg P' c :=
  Silmaril.Proofs.Wasm.Det.Core.DetCfg.mono hP h

theorem ObsAgree.mono {P' P : Profile} (hP : ProfileLE P' P) {c₁ c₂ : Config Nat}
    (h : ObsAgree P c₁ c₂) : ObsAgree P' c₁ c₂ :=
  Silmaril.Proofs.Wasm.Det.Core.ObsAgree.mono hP h

theorem CallReach.mono {P' P : Profile} (hP : ProfileLE P' P) {Entry : Nat → Prop}
    {s₀ s : Store Nat} (h : CallReach P' Entry s₀ s) : CallReach P Entry s₀ s :=
  Silmaril.Proofs.Wasm.Det.Core.CallReach.mono hP h

theorem DetFn.mono {P' P : Profile} (hP : ProfileLE P' P) {s : Store Nat} {a : Nat}
    (h : DetFn P s a) : DetFn P' s a :=
  fun vs hok => DetCfg.mono hP (h vs hok)

/-- A module deterministic at `P` is deterministic at every refinement of `P`. -/
theorem DetModule.mono {P' P : Profile} (hP : ProfileLE P' P) {Entry : Nat → Prop}
    {s₀ : Store Nat} (h : DetModule P Entry s₀) : DetModule P' Entry s₀ :=
  fun s hs a ha => DetFn.mono hP (h s (CallReach.mono hP hs) a ha)

theorem StatelessFn.mono {P' P : Profile} (hP : ProfileLE P' P) {S : Store Nat → Prop}
    {a : Nat} (h : StatelessFn P S a) : StatelessFn P' S a :=
  fun s₁ s₂ vs h₁ h₂ hok₁ hok₂ => ObsAgree.mono hP (h s₁ s₂ vs h₁ h₂ hok₁ hok₂)

/-- Statelessness over a smaller set of call states. -/
theorem StatelessFn.anti {P : Profile} {S S' : Store Nat → Prop} (hSS : ∀ s, S' s → S s)
    {a : Nat} (h : StatelessFn P S a) : StatelessFn P S' a :=
  fun s₁ s₂ vs h₁ h₂ hok₁ hok₂ => h s₁ s₂ vs (hSS _ h₁) (hSS _ h₂) hok₁ hok₂

/-- A module stateless at `P` is stateless at every refinement of `P`. -/
theorem StatelessModule.mono {P' P : Profile} (hP : ProfileLE P' P) {Entry : Nat → Prop}
    {s₀ : Store Nat} (h : StatelessModule P Entry s₀) : StatelessModule P' Entry s₀ :=
  fun a ha => StatelessFn.mono hP (StatelessFn.anti (fun _ hs => CallReach.mono hP hs) (h a ha))

/-- A stateless function has deterministic outputs at every call state it covers. -/
theorem StatelessFn.detOut {P : Profile} {S : Store Nat → Prop} {a : Nat}
    (h : StatelessFn P S a) {s : Store Nat} (hs : S s) {vs : List Val} (hok : InvokeOk s a vs) :
    ObsAgree P (invoke s a vs) (invoke s a vs) :=
  h s s vs hs hs hok hok

/-- An instance deterministic with its instantiation phase is a deterministic module from every
store at which instantiation finishes without trapping. -/
theorem DetInst.module {P : Profile} {c₀ : Config Nat} {Entry : Nat → Prop}
    (h : DetInst P c₀ Entry) {tr : List Call} {d : Config Nat} {r : Result}
    (hr : Runs P c₀ tr d) (hd : d.code = r.toAdmin) (hnt : r ≠ .trap) :
    DetModule P Entry d.store :=
  h.2 tr d r hr hd hnt

end Silmaril.Wasm.Det.Core
