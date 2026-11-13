module

public import Silmaril.Wasm.Game.ULink.Runs.Thms
public import Silmaril.Wasm.Det.Shared.Thms
public import Silmaril.Wasm.Det.Link.Shared.Defs
public import Silmaril.Proofs.Wasm.Det.Link.Store
public import Silmaril.Proofs.Wasm.Det.Game.Trapped

/-!
# Determinism of the shared store from the parts (step B, store-writing route)

The shared world `S.sc` of a static link (provider and consumer instantiated into one store) is
the semantic link `S.toULink` of `Silmaril.Wasm.Game.ULink`: its stubbed store is the consumer
store `S.scs`. A host-free run of an export invocation in a store with the shared functions
splits (`ULink.linked_oruns`) into a run of the consumer invocation in the stubbed store, whose
stub calls are answered by host-free runs of the provider's invocations **in the real store at
the call** (`ULink.provAns`); the returned store is the stubbed final store, so these are
answers of a host that writes the store and keeps the functions (`KeepFuncs`).

* `oruns_det` (generic): if the consumer is `DetCfgS` against `KeepFuncs`-hosts and the answers
  are deterministic modulo traps (two non-trapping answers to the same call in the same store
  are equal, with equal returned stores), two such runs reaching non-trapping results have the
  same result and the same store. The traces are compared at their first difference: before it
  the consumer is at the same call in the same store (`DetCfgS` on the common prefix); a trap
  answer cannot be followed by a non-trapping result (`step_trapped`); two non-trapping answers
  agree.
* `shared_detCall`: hence every export invocation is `DetCfg` in every store with the shared
  functions, from `DetModuleS` of the consumer (stores with the functions of `S.scs`) and
  `DetCfg` of the provider's invocations (stores with the functions of `S.sc`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Link.Shared

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Shared
  Silmaril.Wasm.Det.Game Silmaril.Proofs.Wasm.Det.Link.Store Silmaril.Proofs.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {Ans : Store Nat → Nat → List Val → Result → Store Nat → Prop}

/-! ### Runs against a call-dependent oracle -/

/-- The store-writing call of an answered call. -/
def toSCall (x : OCall) : SCall := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩

/-- A run against a call-dependent oracle is a run against any store relation containing it. -/
theorem ORuns.toS {A : Store Nat → Store Nat → Prop}
    (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ') {c d : Config Nat} {tr : List OCall}
    (hr : ORuns P Ans c tr d) : RunsS P A c (tr.map toSCall) d := by
  induction hr with
  | stop hs => exact .stop hs
  | call hs hd hA' _ ih => exact .call hs hd (hA _ _ _ _ _ hA') ih

/-- Answers that keep the functions: the stores at the calls keep the initial functions. -/
theorem ORuns.keep (hK : ∀ σ h args r σ', Ans σ h args r σ' → σ'.funcs = σ.funcs)
    {F : List (FuncInst Nat)} {c d : Config Nat} {tr : List OCall} (hr : ORuns P Ans c tr d)
    (hc : c.store.funcs = F) :
    ORuns P (fun σ h args r σ' => Ans σ h args r σ' ∧ σ.funcs = F) c tr d := by
  induction hr with
  | stop hs => exact .stop hs
  | call hs hd hA _ ih =>
    have hf : _ = F := (Runs.funcs_eq (Runs.stop (P := P) hs)).trans hc
    exact .call hs hd ⟨hA, hf⟩ (ih ((hK _ _ _ _ _ hA).trans hf))

/-- Split a run after a prefix of its trace. -/
theorem ORuns.split : ∀ {c d : Config Nat} {p q : List OCall}, ORuns P Ans c (p ++ q) d →
    ∃ e, (∀ e', Steps P Det.noHost e e' → ORuns P Ans c p e') ∧ ORuns P Ans e q d
  | c, _, [], _, hr => ⟨c, fun _ h => .stop h, hr⟩
  | _, _, _ :: _, _, hr => by
    cases hr with
    | call hs hd hA hk =>
      obtain ⟨e, he, hq⟩ := ORuns.split hk
      exact ⟨e, fun e' h => .call hs hd hA (he e' h), hq⟩

/-- The configuration of a run at a call of its trace. -/
theorem ORuns.at {c d : Config Nat} {p q : List OCall} {x : OCall}
    (hr : ORuns P Ans c (p ++ x :: q) d) :
    ∃ g E a, ORuns P Ans c p g ∧ decompose? g.store g.code = some (E, a, x.1, x.2.1) ∧
      Ans g.store x.1 x.2.1 x.2.2.1 x.2.2.2 ∧
      ORuns P Ans ⟨x.2.2.2, g.frame, E.fill x.2.2.1.toAdmin⟩ q d := by
  obtain ⟨e, he, hq⟩ := ORuns.split hr
  cases hq with
  | call hs hd hA hk => exact ⟨_, _, _, he _ hs, hd, hA, hk⟩

/-! ### Trapped answers -/

/-- Host-free runs from trapped code stay trapped. -/
theorem steps_trapped {s : Store Nat} {F : Frame} {E : Ctx} {d : Config Nat}
    (h : Steps P Det.noHost ⟨s, F, E.fill [.trap]⟩ d) : ∃ E' : Ctx, d.code = E'.fill [.trap] := by
  induction h with
  | refl => exact ⟨E, rfl⟩
  | @tail y z _ hst ih =>
    obtain ⟨E', hE'⟩ := ih
    have hst' : Step P Det.noHost ⟨y.store, y.frame, E'.fill [.trap]⟩ z := by
      rw [← hE']
      exact hst
    exact step_trapped E' _ _ _ hst'

/-- **After a trap answer no run reaches a non-trapping result.** -/
theorem ORuns.trapped {s : Store Nat} {F : Frame} {E : Ctx} {q : List OCall} {d : Config Nat}
    {r : Result} (hr : ORuns P Ans ⟨s, F, E.fill [.trap]⟩ q d) (ho : OutAt d (.ret r)) : False := by
  cases hr with
  | stop hs =>
    obtain ⟨E', hE'⟩ := steps_trapped hs
    cases ho with
    | ret hne hc => exact hne (fill_trap_toAdmin (hE'.symm.trans hc))
  | call hs hd _ _ =>
    obtain ⟨E', hE'⟩ := steps_trapped hs
    rw [hE', Ctx.decompose?_fill_trap] at hd
    cases hd

/-! ### Twin runs -/

section Twin

variable {A : Store Nat → Store Nat → Prop} {c : Config Nat}

/-- A run ending in a result and a run continuing at a call cannot have the same trace up to
the call. -/
theorem no_ret_call (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ') (hD : DetCfgS P A c)
    {p q : List OCall} {x : OCall} {d₁ d₂ : Config Nat} {r : Result}
    (h₁ : ORuns P Ans c p d₁) (ho : OutAt d₁ (.ret r)) (h₂ : ORuns P Ans c (p ++ x :: q) d₂) :
    False := by
  obtain ⟨g, E, a, hg, hd, -, -⟩ := ORuns.at h₂
  have := (hD _ _ _ _ _ (ORuns.toS hA h₁) (ORuns.toS hA hg) ho (.call hd)).1
  cases this

/-- Answers deterministic modulo traps. -/
def AnsDet (Ans : Store Nat → Nat → List Val → Result → Store Nat → Prop) : Prop :=
  ∀ σ h args r₁ r₂ σ₁ σ₂, Ans σ h args r₁ σ₁ → Ans σ h args r₂ σ₂ → r₁ ≠ .trap → r₂ ≠ .trap →
    r₁ = r₂ ∧ σ₁ = σ₂

/-- A run continuing after a call to a non-trapping result had a non-trapping answer. -/
theorem ans_ne_trap {σ : Store Nat} {F : Frame} {E : Ctx} {r r' : Result} {q : List OCall}
    {d : Config Nat} (hk : ORuns P Ans ⟨σ, F, E.fill r.toAdmin⟩ q d) (ho : OutAt d (.ret r')) :
    r ≠ .trap := by
  rintro rfl
  exact ORuns.trapped hk ho

/-- At the first call after a common prefix, the two runs make the same call with the same
answer. -/
theorem head_eq (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ') (hD : DetCfgS P A c)
    (hAns : AnsDet Ans) {p q₁ q₂ : List OCall} {x₁ x₂ : OCall} {d₁ d₂ : Config Nat}
    {r₁ r₂ : Result} (h₁ : ORuns P Ans c (p ++ x₁ :: q₁) d₁)
    (h₂ : ORuns P Ans c (p ++ x₂ :: q₂) d₂) (ho₁ : OutAt d₁ (.ret r₁))
    (ho₂ : OutAt d₂ (.ret r₂)) : x₁ = x₂ := by
  obtain ⟨g₁, E₁, a₁, hg₁, hd₁, hA₁, hk₁⟩ := ORuns.at h₁
  obtain ⟨g₂, E₂, a₂, hg₂, hd₂, hA₂, hk₂⟩ := ORuns.at h₂
  obtain ⟨ho, hst⟩ := hD _ _ _ _ _ (ORuns.toS hA hg₁) (ORuns.toS hA hg₂) (.call hd₁) (.call hd₂)
  obtain ⟨hh, hargs⟩ : x₁.1 = x₂.1 ∧ x₁.2.1 = x₂.2.1 := Out.call.inj ho
  have hA₂' : Ans g₁.store x₁.1 x₁.2.1 x₂.2.2.1 x₂.2.2.2 := by
    rw [hst, hh, hargs]
    exact hA₂
  obtain ⟨hr, hσ⟩ := hAns _ _ _ _ _ _ _ hA₁ hA₂' (ans_ne_trap hk₁ ho₁) (ans_ne_trap hk₂ ho₂)
  exact Prod.ext hh (Prod.ext hargs (Prod.ext hr hσ))

/-- **Two runs to non-trapping results have the same trace.** -/
theorem trace_eq (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ') (hD : DetCfgS P A c)
    (hAns : AnsDet Ans) :
    ∀ (tr₁ p tr₂ : List OCall) {d₁ d₂ : Config Nat} {r₁ r₂ : Result},
      ORuns P Ans c (p ++ tr₁) d₁ → ORuns P Ans c (p ++ tr₂) d₂ → OutAt d₁ (.ret r₁) →
      OutAt d₂ (.ret r₂) → tr₁ = tr₂
  | [], _, [], _, _, _, _, _, _, _, _ => rfl
  | [], p, _ :: _, _, _, _, _, h₁, h₂, ho₁, _ =>
    (no_ret_call hA hD (List.append_nil p ▸ h₁) ho₁ h₂).elim
  | _ :: _, p, [], _, _, _, _, h₁, h₂, _, ho₂ =>
    (no_ret_call hA hD (List.append_nil p ▸ h₂) ho₂ h₁).elim
  | x₁ :: q₁, p, x₂ :: q₂, _, _, _, _, h₁, h₂, ho₁, ho₂ => by
    have hx : x₁ = x₂ := head_eq hA hD hAns h₁ h₂ ho₁ ho₂
    have e₁ : p ++ x₁ :: q₁ = (p ++ [x₁]) ++ q₁ := by simp
    have e₂ : p ++ x₂ :: q₂ = (p ++ [x₁]) ++ q₂ := by simp [hx]
    have hq : q₁ = q₂ := trace_eq hA hD hAns q₁ (p ++ [x₁]) q₂ (e₁ ▸ h₁) (e₂ ▸ h₂) ho₁ ho₂
    rw [hx, hq]

/-- **Twin runs**: two runs against deterministic answers from a `DetCfgS` configuration that
reach non-trapping results have the same result and the same store. -/
theorem oruns_det (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ') (hD : DetCfgS P A c)
    (hAns : AnsDet Ans) {tr₁ tr₂ : List OCall} {d₁ d₂ : Config Nat} {r₁ r₂ : Result}
    (h₁ : ORuns P Ans c tr₁ d₁) (h₂ : ORuns P Ans c tr₂ d₂) (ho₁ : OutAt d₁ (.ret r₁))
    (ho₂ : OutAt d₂ (.ret r₂)) : r₁ = r₂ ∧ d₁.store = d₂.store := by
  have htr : tr₁ = tr₂ := trace_eq hA hD hAns tr₁ [] tr₂ h₁ h₂ ho₁ ho₂
  subst htr
  obtain ⟨ho, hst⟩ := hD _ _ _ _ _ (ORuns.toS hA h₁) (ORuns.toS hA h₂) ho₁ ho₂
  exact ⟨Out.ret.inj ho, hst⟩

end Twin

/-! ### Twin runs from two call states -/

section TwinW

variable {A : Store Nat → Store Nat → Prop} {c₁ c₂ : Config Nat}

/-- The call and answer of an answered call. -/
def strip (x : OCall) : Nat × List Val × Result := (x.1, x.2.1, x.2.2.1)

theorem map_strip (tr : List OCall) : (tr.map toSCall).map SCall.call = tr.map strip := by
  rw [List.map_map]
  rfl

theorem ObsAgreeW.symm (h : ObsAgreeW P A c₁ c₂) : ObsAgreeW P A c₂ c₁ :=
  fun tr₁ tr₂ d₁ d₂ o₁ o₂ he h₁ h₂ ho₁ ho₂ => (h tr₂ tr₁ d₂ d₁ o₂ o₁ he.symm h₂ h₁ ho₂ ho₁).symm

/-- Answers agreeing modulo traps, whatever the stores at the calls. -/
def AnsAgree (Ans : Store Nat → Nat → List Val → Result → Store Nat → Prop) : Prop :=
  ∀ σ₁ σ₂ h args r₁ r₂ σ₁' σ₂', Ans σ₁ h args r₁ σ₁' → Ans σ₂ h args r₂ σ₂' → r₁ ≠ .trap →
    r₂ ≠ .trap → r₁ = r₂

theorem no_ret_callW (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ')
    (hD : ObsAgreeW P A c₁ c₂) {p₁ p₂ q : List OCall} {x : OCall} {d₁ d₂ : Config Nat}
    {r : Result} (hp : p₁.map strip = p₂.map strip) (h₁ : ORuns P Ans c₁ p₁ d₁)
    (ho : OutAt d₁ (.ret r)) (h₂ : ORuns P Ans c₂ (p₂ ++ x :: q) d₂) : False := by
  obtain ⟨g, E, a, hg, hd, -, -⟩ := ORuns.at h₂
  have he : (p₁.map toSCall).map SCall.call = (p₂.map toSCall).map SCall.call := by
    rw [map_strip, map_strip, hp]
  have := hD _ _ _ _ _ _ he (ORuns.toS hA h₁) (ORuns.toS hA hg) ho (.call hd)
  cases this

theorem head_eqW (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ')
    (hD : ObsAgreeW P A c₁ c₂) (hAns : AnsAgree Ans) {p₁ p₂ q₁ q₂ : List OCall} {x₁ x₂ : OCall}
    {d₁ d₂ : Config Nat} {r₁ r₂ : Result} (hp : p₁.map strip = p₂.map strip)
    (h₁ : ORuns P Ans c₁ (p₁ ++ x₁ :: q₁) d₁) (h₂ : ORuns P Ans c₂ (p₂ ++ x₂ :: q₂) d₂)
    (ho₁ : OutAt d₁ (.ret r₁)) (ho₂ : OutAt d₂ (.ret r₂)) : strip x₁ = strip x₂ := by
  obtain ⟨g₁, E₁, a₁, hg₁, hd₁, hA₁, hk₁⟩ := ORuns.at h₁
  obtain ⟨g₂, E₂, a₂, hg₂, hd₂, hA₂, hk₂⟩ := ORuns.at h₂
  have he : (p₁.map toSCall).map SCall.call = (p₂.map toSCall).map SCall.call := by
    rw [map_strip, map_strip, hp]
  have ho := hD _ _ _ _ _ _ he (ORuns.toS hA hg₁) (ORuns.toS hA hg₂) (.call hd₁) (.call hd₂)
  obtain ⟨hh, hargs⟩ : x₁.1 = x₂.1 ∧ x₁.2.1 = x₂.2.1 := Out.call.inj ho
  have hA₂' : Ans g₂.store x₁.1 x₁.2.1 x₂.2.2.1 x₂.2.2.2 := by
    rw [hh, hargs]
    exact hA₂
  have hr := hAns _ _ _ _ _ _ _ _ hA₁ hA₂' (ans_ne_trap hk₁ ho₁) (ans_ne_trap hk₂ ho₂)
  exact Prod.ext hh (Prod.ext hargs hr)

/-- **Two runs from agreeing call states make the same calls with the same answers.** -/
theorem trace_eqW (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ')
    (hD : ObsAgreeW P A c₁ c₂) (hAns : AnsAgree Ans) :
    ∀ (tr₁ p₁ p₂ tr₂ : List OCall) {d₁ d₂ : Config Nat} {r₁ r₂ : Result},
      p₁.map strip = p₂.map strip → ORuns P Ans c₁ (p₁ ++ tr₁) d₁ →
      ORuns P Ans c₂ (p₂ ++ tr₂) d₂ → OutAt d₁ (.ret r₁) → OutAt d₂ (.ret r₂) →
      tr₁.map strip = tr₂.map strip
  | [], _, _, [], _, _, _, _, _, _, _, _, _ => rfl
  | [], p₁, _, _ :: _, _, _, _, _, hp, h₁, h₂, ho₁, _ =>
    (no_ret_callW hA hD hp (List.append_nil p₁ ▸ h₁) ho₁ h₂).elim
  | _ :: _, _, p₂, [], _, _, _, _, hp, h₁, h₂, _, ho₂ =>
    (no_ret_callW hA (ObsAgreeW.symm hD) hp.symm (List.append_nil p₂ ▸ h₂) ho₂ h₁).elim
  | x₁ :: q₁, p₁, p₂, x₂ :: q₂, _, _, _, _, hp, h₁, h₂, ho₁, ho₂ => by
    have hx : strip x₁ = strip x₂ := head_eqW hA hD hAns hp h₁ h₂ ho₁ ho₂
    have hp' : (p₁ ++ [x₁]).map strip = (p₂ ++ [x₂]).map strip := by
      rw [List.map_append, List.map_append, hp, List.map_singleton, List.map_singleton, hx]
    have e₁ : p₁ ++ x₁ :: q₁ = (p₁ ++ [x₁]) ++ q₁ := by simp
    have e₂ : p₂ ++ x₂ :: q₂ = (p₂ ++ [x₂]) ++ q₂ := by simp
    have hq := trace_eqW hA hD hAns q₁ (p₁ ++ [x₁]) (p₂ ++ [x₂]) q₂ hp' (e₁ ▸ h₁) (e₂ ▸ h₂) ho₁ ho₂
    rw [List.map_cons, List.map_cons, hx, hq]

/-- **Twin runs from two call states**: against answers agreeing modulo traps, two runs from
`ObsAgreeW` configurations reaching non-trapping results have the same result. -/
theorem oruns_agree (hA : ∀ σ h args r σ', Ans σ h args r σ' → A σ σ')
    (hD : ObsAgreeW P A c₁ c₂) (hAns : AnsAgree Ans) {tr₁ tr₂ : List OCall} {d₁ d₂ : Config Nat}
    {r₁ r₂ : Result} (h₁ : ORuns P Ans c₁ tr₁ d₁) (h₂ : ORuns P Ans c₂ tr₂ d₂)
    (ho₁ : OutAt d₁ (.ret r₁)) (ho₂ : OutAt d₂ (.ret r₂)) : r₁ = r₂ := by
  have htr : tr₁.map strip = tr₂.map strip := trace_eqW hA hD hAns tr₁ [] [] tr₂ rfl h₁ h₂ ho₁ ho₂
  have he : (tr₁.map toSCall).map SCall.call = (tr₂.map toSCall).map SCall.call := by
    rw [map_strip, map_strip, htr]
  exact Out.ret.inj (hD _ _ _ _ _ _ he (ORuns.toS hA h₁) (ORuns.toS hA h₂) ho₁ ho₂)

end TwinW

/-! ### The shared world of a static link -/

section Setup

variable (S : Setup)

/-- The oracle of the shared world: provider answers, asked in stores with the consumer's
functions. -/
abbrev SAns (S : Setup) (P : Profile) : Store Nat → Nat → List Val → Result → Store Nat → Prop :=
  fun σ h args r σ' => S.toULink.provAns P σ h args r σ' ∧ σ.funcs = S.scs.funcs

theorem layout_of_sc (hS : S.Scalar) {s : Store Nat} (hs : s.funcs = S.sc.funcs) :
    S.toULink.Layout s :=
  ULink.layout_of_funcs (Setup.toULink_layout S hS) hs

theorem stubS_funcs {s : Store Nat} (hs : s.funcs = S.sc.funcs) :
    (S.toULink.stubS s).funcs = S.scs.funcs := by
  show s.funcs.mapIdx S.toULink.stubFI = _
  rw [hs, ← Setup.toULink_stubS S]
  rfl

/-- Provider answers keep the functions. -/
theorem provAns_funcs {σ σ' : Store Nat} {h : Nat} {args : List Val} {r : Result}
    (hA : S.toULink.provAns P σ h args r σ') : σ'.funcs = σ.funcs := by
  obtain ⟨s₀, a, s', rfl, -, -, hrun, rfl⟩ := hA
  have hf : s'.funcs = s₀.funcs := Runs.funcs_eq (Runs.stop (P := P) hrun)
  show s'.funcs.mapIdx S.toULink.stubFI = s₀.funcs.mapIdx S.toULink.stubFI
  rw [hf]

/-- The real store of a stubbed store with the consumer's functions has the shared functions. -/
theorem real_funcs (hS : S.Scalar) {σ s₀ : Store Nat} (hσ : σ.funcs = S.scs.funcs)
    (he : σ = S.toULink.stubS s₀) (hl : S.toULink.Layout s₀) : s₀.funcs = S.sc.funcs := by
  have h₁ : (S.toULink.unstubS (S.toULink.stubS s₀)).funcs = s₀.funcs :=
    congrArg Store.funcs (ULink.unstub_stub hl)
  have h₂ : (S.toULink.unstubS (S.toULink.stubS S.sc)).funcs = S.sc.funcs :=
    congrArg Store.funcs (ULink.unstub_stub (Setup.toULink_layout S hS))
  have h₃ : (S.toULink.stubS s₀).funcs = (S.toULink.stubS S.sc).funcs := by
    rw [← he, hσ, Setup.toULink_stubS]
  have h₄ : (S.toULink.unstubS (S.toULink.stubS s₀)).funcs =
      (S.toULink.unstubS (S.toULink.stubS S.sc)).funcs := by
    show (S.toULink.stubS s₀).funcs.mapIdx S.toULink.unstubFI =
      (S.toULink.stubS S.sc).funcs.mapIdx S.toULink.unstubFI
    rw [h₃]
  exact h₁.symm.trans (h₄.trans h₂)

/-- Stub targets are provider exports. -/
theorem entry_of_target (hS : S.Scalar) {k a : Nat} (ht : S.toULink.target k = some a) :
    entry S.providerI a := by
  obtain ⟨hk, ha⟩ := Setup.ulinkTarget_eq_some ht
  have hlen : (S.stubs.map (S.base.funcs.length + ·)).length = S.stubTypes.length :=
    hS.provider.addrs_length
  have hk' : k < S.stubTypes.length := by
    rw [← hlen, List.length_map]
    exact hk
  refine ⟨⟨k, hk'⟩, ?_⟩
  show (S.stubs.map (S.base.funcs.length + ·)).getD k 0 = a
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  exact ha

/-- **Provider answers are deterministic modulo traps**, when the provider's invocations are. -/
theorem sAns_det (hS : S.Scalar)
    (hp : ∀ s, s.funcs = S.sc.funcs → ∀ a, entry S.providerI a → ∀ vs, DetCfg P (invoke s a vs)) :
    AnsDet (SAns S P) := by
  rintro σ h args r₁ r₂ σ₁ σ₂ ⟨⟨s₁, a₁, s₁', he₁, hl₁, ht₁, hrun₁, rfl⟩, hσ⟩
    ⟨⟨s₂, a₂, s₂', he₂, hl₂, ht₂, hrun₂, rfl⟩, -⟩ hr₁ hr₂
  have hs : s₁ = s₂ := by
    rw [← ULink.unstub_stub hl₁, ← he₁, he₂, ULink.unstub_stub hl₂]
  have ha : a₁ = a₂ := Option.some.inj (ht₁.symm.trans ht₂)
  subst hs ha
  have hD := hp s₁ (real_funcs S hS hσ he₁ hl₁) a₁ (entry_of_target S hS ht₁) args
  obtain ⟨ho, hst⟩ := hD [] _ _ _ _ (.stop hrun₁) (.stop hrun₂) (.ret hr₁ rfl) (.ret hr₂ rfl)
  exact ⟨Out.ret.inj ho, congrArg S.toULink.stubS hst⟩

/-- An export run in a store with the shared functions, read as a consumer run. -/
theorem shared_split (hS : S.Scalar) {s : Store Nat} (hs : s.funcs = S.sc.funcs) {a : Nat}
    {vs : List Val} {d : Config Nat} {r : Result} (h : Steps P Det.noHost (invoke s a vs) d)
    (hfin : d.code = r.toAdmin) :
    ∃ tr, ORuns P (SAns S P) (invoke (S.toULink.stubS s) a vs) tr
      ⟨S.toULink.stubS d.store, d.frame, d.code⟩ := by
  obtain ⟨tr, hr⟩ := ULink.linked_oruns (layout_of_sc S hS hs) h hfin
  refine ⟨tr, ?_⟩
  rw [ULink.invoke_stubS]
  exact ORuns.keep (fun _ _ _ _ _ hA => provAns_funcs S hA) hr (stubS_funcs S hs)

theorem stubS_inj (hS : S.Scalar) {s₁ s₂ : Store Nat} (h₁ : s₁.funcs = S.sc.funcs)
    (h₂ : s₂.funcs = S.sc.funcs) (h : S.toULink.stubS s₁ = S.toULink.stubS s₂) : s₁ = s₂ := by
  rw [← ULink.unstub_stub (layout_of_sc S hS h₁), h, ULink.unstub_stub (layout_of_sc S hS h₂)]

/-- **Step B, store level**: every export invocation in a store with the shared functions is
deterministic modulo traps (outputs and stores), from `DetModuleS` of the consumer against
`KeepFuncs`-hosts and `DetCfg` of the provider's invocations. -/
theorem shared_detCall (hS : S.Scalar)
    (hp : ∀ s, s.funcs = S.sc.funcs → ∀ a, entry S.providerI a → ∀ vs, DetCfg P (invoke s a vs))
    (hc : DetModuleS P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI))
    {s : Store Nat} (hs : s.funcs = S.sc.funcs) {a : Nat} (ha : entry S.sharedI a)
    (vs : List Val) : DetCfg P (invoke s a vs) := by
  intro tr d₁ d₂ o₁ o₂ r₁ r₂ ho₁ ho₂
  have hn : NoHostFn s := NoHostFn.of_funcs hs (NoHostFn.of_wellFormed rfl hS.shared)
  obtain ⟨rfl, run₁⟩ := runs_noHost hn r₁
  obtain ⟨-, run₂⟩ := runs_noHost hn r₂
  have hf₁ : d₁.store.funcs = S.sc.funcs := (Runs.funcs_eq r₁).trans hs
  have hf₂ : d₂.store.funcs = S.sc.funcs := (Runs.funcs_eq r₂).trans hs
  obtain ⟨q₁, rfl, hq₁, hc₁⟩ := outAt_noHost (hn.of_funcs (Runs.funcs_eq r₁)) ho₁
  obtain ⟨q₂, rfl, hq₂, hc₂⟩ := outAt_noHost (hn.of_funcs (Runs.funcs_eq r₂)) ho₂
  obtain ⟨tr₁, h₁⟩ := shared_split S hS hs run₁ hc₁
  obtain ⟨tr₂, h₂⟩ := shared_split S hS hs run₂ hc₂
  obtain ⟨hq, hst⟩ := oruns_det (A := KeepFuncs) (fun _ _ _ _ _ hA => provAns_funcs S hA.1)
    (hc _ (stubS_funcs S hs) a ha vs) (sAns_det S hS hp) h₁ h₂ (.ret hq₁ hc₁) (.ret hq₂ hc₂)
  exact ⟨congrArg Out.ret hq, stubS_inj S hS hf₁ hf₂ hst⟩

/-- **Step B**: `DetModule` of the shared store from the parts. -/
theorem shared_detModule_of_parts (hS : S.Scalar)
    (hp : ∀ s, s.funcs = S.sc.funcs → ∀ a, entry S.providerI a → ∀ vs, DetCfg P (invoke s a vs))
    (hc : DetModuleS P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI)) :
    DetModule P (entry S.sharedI) S.sc :=
  fun _ hs _ ha vs _ => shared_detCall S hS hp hc (CallReach.funcs_eq hs) ha vs

/-- **Provider answers agree modulo traps across call states**, when the provider's exports are
stateless against hosts whose returned stores may differ. -/
theorem sAns_agree (hS : S.Scalar)
    (hp : StatelessModuleW P KeepFuncs (fun s => s.funcs = S.sc.funcs) (entry S.providerI)) :
    AnsAgree (SAns S P) := by
  rintro σ₁ σ₂ h args r₁ r₂ σ₁' σ₂' ⟨⟨s₁, a₁, s₁', he₁, hl₁, ht₁, hrun₁, rfl⟩, hσ₁⟩
    ⟨⟨s₂, a₂, s₂', he₂, hl₂, ht₂, hrun₂, rfl⟩, hσ₂⟩ hr₁ hr₂
  have ha : a₁ = a₂ := Option.some.inj (ht₁.symm.trans ht₂)
  subst ha
  have hD := hp a₁ (entry_of_target S hS ht₁) s₁ s₂ args (real_funcs S hS hσ₁ he₁ hl₁)
    (real_funcs S hS hσ₂ he₂ hl₂)
  exact Out.ret.inj (hD [] [] _ _ _ _ rfl (.stop hrun₁) (.stop hrun₂) (.ret hr₁ rfl) (.ret hr₂ rfl))

/-- **Step B, statelessness, per invocation**: two export invocations on the same arguments in
any two stores with the shared functions agree on non-trapping outputs. -/
theorem shared_obsAgree (hS : S.Scalar)
    (hp : StatelessModuleW P KeepFuncs (fun s => s.funcs = S.sc.funcs) (entry S.providerI))
    (hc : StatelessModuleW P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI))
    {s₁ s₂ : Store Nat} (hs₁ : s₁.funcs = S.sc.funcs) (hs₂ : s₂.funcs = S.sc.funcs) {a : Nat}
    (ha : entry S.sharedI a) (vs : List Val) : ObsAgree P (invoke s₁ a vs) (invoke s₂ a vs) := by
  intro tr d₁ d₂ o₁ o₂ r₁ r₂ ho₁ ho₂
  have hn₁ : NoHostFn s₁ := NoHostFn.of_funcs hs₁ (NoHostFn.of_wellFormed rfl hS.shared)
  have hn₂ : NoHostFn s₂ := NoHostFn.of_funcs hs₂ (NoHostFn.of_wellFormed rfl hS.shared)
  obtain ⟨rfl, run₁⟩ := runs_noHost hn₁ r₁
  obtain ⟨-, run₂⟩ := runs_noHost hn₂ r₂
  obtain ⟨q₁, rfl, hq₁, hc₁⟩ := outAt_noHost (hn₁.of_funcs (Runs.funcs_eq r₁)) ho₁
  obtain ⟨q₂, rfl, hq₂, hc₂⟩ := outAt_noHost (hn₂.of_funcs (Runs.funcs_eq r₂)) ho₂
  obtain ⟨tr₁, h₁⟩ := shared_split S hS hs₁ run₁ hc₁
  obtain ⟨tr₂, h₂⟩ := shared_split S hS hs₂ run₂ hc₂
  have hD := hc a ha _ _ vs (stubS_funcs S hs₁) (stubS_funcs S hs₂)
  exact congrArg Out.ret (oruns_agree (A := KeepFuncs) (fun _ _ _ _ _ hA => provAns_funcs S hA.1)
    hD (sAns_agree S hS hp) h₁ h₂ (.ret hq₁ hc₁) (.ret hq₂ hc₂))

/-- **Step B, statelessness**: `StatelessModule` of the shared store from the parts. -/
theorem shared_statelessModule_of_parts (hS : S.Scalar)
    (hp : StatelessModuleW P KeepFuncs (fun s => s.funcs = S.sc.funcs) (entry S.providerI))
    (hc : StatelessModuleW P KeepFuncs (fun κ => κ.funcs = S.scs.funcs) (entry S.consumerI)) :
    StatelessModule P (entry S.sharedI) S.sc :=
  fun _ ha _ _ vs h₁ h₂ _ _ =>
    shared_obsAgree S hS hp hc (CallReach.funcs_eq h₁) (CallReach.funcs_eq h₂) ha vs

end Setup

end Silmaril.Proofs.Wasm.Det.Link.Shared
