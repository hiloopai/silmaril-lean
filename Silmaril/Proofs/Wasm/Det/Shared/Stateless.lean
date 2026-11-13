module

public import Silmaril.Proofs.Wasm.Det.Shared.Basic
public import Silmaril.Wasm.Det.Shared.Stateless.Defs
public import Silmaril.Wasm.Det.Stateless.Thms

/-!
# Statelessness under store-writing hosts: proofs

* `DetCfgS.obsAgreeS`: determinism gives output agreement with itself.
* The stateless subset (`Silmaril.Wasm.Det.Stateless`): its invariant is closed under resumption in
  every store keeping the function instances (`closedS_sl`); runs in two stores agreeing on the
  functions and the read globals, with the same returned stores, stay in agreeing stores
  (`runsS_swap`: after an answer both runs continue in the same returned store); hence
  `obsAgreeS_of_agree`, `statelessFnS_of_good`, `statelessModuleS_of_good`.

New proofs (the structure follows `Silmaril.Proofs.Wasm.Det.Stateless.Runs`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Shared.Stateless

open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Shared Silmaril.Wasm.Det.Stateless
  Silmaril.Proofs.Wasm.Det.Stateless Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-- Determinism gives output agreement of a configuration with itself. -/
theorem DetCfgS.obsAgreeS {A : Store Nat → Store Nat → Prop} {c : Config Nat}
    (h : DetCfgS P A c) : ObsAgreeS P A c c :=
  fun tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂ => (h tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂).1

variable {A R W : Nat → Bool}

/-- The invariant of the stateless subset after an answer in a store with the same functions. -/
theorem inv_resumeIn {c : Config Nat} {E : Ctx} {a h : Nat} {args : List Val} (r : Result)
    {s' : Store Nat} (hc : Inv A R W c) (hd : decompose? c.store c.code = some (E, a, h, args))
    (hA : KeepFuncs c.store s') : Inv A R W (resumeIn c E r s') := by
  obtain ⟨-, hok, hp⟩ := inv_resume r hc hd
  have hg : GoodFuns A R W s'.funcs := by
    rw [show s'.funcs = c.store.funcs from hA]
    exact hc.1
  exact ⟨hg, hok, hp⟩

/-- The invariant of the stateless subset is closed under store-writing answers keeping the
function instances. -/
theorem closedS_sl (P : Profile) : ClosedS P KeepFuncs (Inv A R W) :=
  ⟨fun _ _ hc h => (inv_step hc h).1, fun _ _ _ _ _ r _ hc hd hA => inv_resumeIn r hc hd hA⟩

/-- **Subset code is deterministic against every host keeping the function instances.** -/
theorem detCfgS_sl {c : Config Nat} (hc : Inv A R W c) : DetCfgS P KeepFuncs c :=
  Silmaril.Proofs.Wasm.Det.Shared.detCfgS_of_closed (closedS_sl P)
    (fun _ h => segDet_of_detUpTo (o := anyOracle) (closedS_sl P).step
      (fun _ hd _ he => .inl (Silmaril.Proofs.Wasm.Det.Stateless.step_profile hd he)) h) hc

/-- Runs in agreeing stores against the same store-writing answers. -/
theorem runsS_swap {c d : Config Nat} {tr : List SCall} (h : RunsS P KeepFuncs c tr d)
    (hc : Inv A R W c) {t : Store Nat} (ht : Agree R t c.store) :
    ∃ dt, RunsS P KeepFuncs (swapStore t c) tr (swapStore dt d) ∧ Agree R dt d.store := by
  induction h generalizing t with
  | stop hs =>
    obtain ⟨dt, hst, hag, -⟩ := steps_swap hs hc ht
    exact ⟨dt, .stop hst, hag⟩
  | @call c d e E a hh args r s' tr hs hd hA hk ih =>
    obtain ⟨dt, hst, hag, hinv⟩ := steps_swap hs hc ht
    have hd' : decompose? (swapStore dt d).store (swapStore dt d).code = some (E, a, hh, args) :=
      (decompose?_congr hag.1 d.code).trans hd
    have hA' : KeepFuncs (swapStore dt d).store s' := by
      show s'.funcs = dt.funcs
      rw [show s'.funcs = d.store.funcs from hA, hag.1]
    obtain ⟨et, hk', hag'⟩ := ih (inv_resumeIn r hinv hd hA) (t := s') (Agree.refl R s')
    exact ⟨et, .call hst hd' hA' hk', hag'⟩

/-- **Statelessness for agreeing stores, under store-writing hosts.** -/
theorem obsAgreeS_of_agree {c₁ c₂ : Config Nat} (hc : Inv A R W c₁)
    (hag : Agree R c₁.store c₂.store) (hf : c₁.frame = c₂.frame) (hcode : c₁.code = c₂.code) :
    ObsAgreeS P KeepFuncs c₁ c₂ := by
  intro tr d₁ d₂ o₁ o₂ h₁ h₂ ho₁ ho₂
  have hc₂ : Inv A R W c₂ := ⟨hag.1 ▸ hc.1, hf ▸ hcode ▸ hc.2.1, hcode ▸ hc.2.2⟩
  obtain ⟨dt, hrun, hag'⟩ := runsS_swap h₂ hc₂ hag
  have hc₁ : swapStore c₁.store c₂ = c₁ := by
    simp only [swapStore, ← hf, ← hcode]
  have ho : OutAt (swapStore dt d₂) o₂ := outAt_swap ho₂ hag'.1
  exact (detCfgS_sl hc tr d₁ _ o₁ o₂ h₁ (hc₁ ▸ hrun) ho₁ ho).1

/-- **Statelessness of subset functions under store-writing hosts** over the stores agreeing
with `s₀` on the functions and the globals of `R`. -/
theorem statelessFnS_of_good {s₀ : Store Nat} {a : Nat} (hg : GoodFuns A R W s₀.funcs)
    (ha : A a = true) : StatelessFnS P KeepFuncs (fun s => Agree R s s₀) a := by
  intro s₁ s₂ vs h₁ h₂ _ _
  have hag : Agree R s₁ s₂ := Agree.trans h₁ (Agree.symm h₂)
  exact obsAgreeS_of_agree (Silmaril.Proofs.Wasm.Det.Stateless.inv_invoke vs (h₁.1 ▸ hg) ha) hag rfl (invoke_code_eq hag.1 a vs)

/-- **A module of subset functions is stateless under store-writing hosts** over the stores
agreeing with `s₀` on the functions and the globals of `R`. -/
theorem statelessModuleS_of_good {Entry : Nat → Prop} {s₀ : Store Nat}
    (hm : GoodFuns A R W s₀.funcs) (hE : ∀ a, Entry a → A a = true) :
    StatelessModuleS P KeepFuncs (fun s => Agree R s s₀) Entry :=
  fun a ha => statelessFnS_of_good hm (hE a ha)

/-- **Stateless check ⇒ statelessness under store-writing hosts.** -/
theorem statelessFnS_of_check {s : Store Nat} {a : Nat} (h : statelessCheck s a = true) :
    StatelessFnS P KeepFuncs (fun t => Agree (readsOf s (closure s [a])).contains t s) a :=
  statelessFnS_of_good (statelessCheck_spec h).2 (statelessCheck_spec h).1

end Silmaril.Proofs.Wasm.Det.Shared.Stateless
