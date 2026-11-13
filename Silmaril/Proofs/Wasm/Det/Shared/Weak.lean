module

public import Silmaril.Proofs.Wasm.Det.Shared.Stateless
public import Silmaril.Wasm.Det.Link.Shared.Defs

/-!
# Statelessness against hosts whose returned stores differ: the stateless subset

Code of the stateless subset that reads **no global** (`R` empty) reads the store only through
its function instances. So two of its runs from stores with the same functions, whose traces
agree on calls and answers, are runs of the same configuration up to the stores, whatever stores
the hosts return as long as they keep the functions (`runsS_swapW`, from
`Silmaril.Proofs.Wasm.Det.Stateless.steps_swap`). Determinism against store-writing hosts
(`detCfgS_sl`) then gives `ObsAgreeW` (`obsAgreeW_sl`, `statelessModuleW_of_good`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Shared.Weak

open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Shared Silmaril.Wasm.Det.Stateless
  Silmaril.Proofs.Wasm.Det.Stateless Silmaril.Proofs.Wasm.Det.Shared.Stateless
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {A W : Nat → Bool}

/-- No global is read. -/
abbrev noR : Nat → Bool := fun _ => false

theorem agree_noR {t s : Store Nat} (h : t.funcs = s.funcs) : Agree noR t s :=
  ⟨h, fun _ h => by cases h⟩

/-- The returned stores of a run against hosts keeping the functions have the initial
functions. -/
theorem runsS_stores {c d : Config Nat} {tr : List SCall} (h : RunsS P KeepFuncs c tr d) :
    ∀ x ∈ tr, x.store.funcs = c.store.funcs := by
  induction h with
  | stop _ => exact fun x hx => absurd hx List.not_mem_nil
  | call hs _ hA _ ih =>
    intro x hx
    have hf : _ = _ := Runs.funcs_eq (Runs.stop (P := P) hs)
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hA.trans hf
    · exact (ih x hx).trans (hA.trans hf)

/-- One answered call of the swapped run, in the returned store of the other trace. -/
theorem swapW_call {c d e : Config Nat} {E : Ctx} {a hh : Nat} {args : List Val} {r : Result}
    {s' xs : Store Nat} {tr₁ : List SCall} (hs : Steps P Det.noHost c d)
    (hd : decompose? d.store d.code = some (E, a, hh, args)) (hA : KeepFuncs d.store s')
    (hc : Inv A noR W c) {t : Store Nat} (ht : t.funcs = c.store.funcs)
    (hxs : xs.funcs = c.store.funcs)
    (ih : Inv A noR W (resumeIn d E r s') → xs.funcs = s'.funcs →
      ∃ dt, RunsS P KeepFuncs (swapStore xs (resumeIn d E r s')) tr₁ (swapStore dt e) ∧
        dt.funcs = e.store.funcs) :
    ∃ dt, RunsS P KeepFuncs (swapStore t c) (⟨hh, args, r, xs⟩ :: tr₁) (swapStore dt e) ∧
      dt.funcs = e.store.funcs := by
  obtain ⟨dt, hsw, hag, hinv⟩ := steps_swap hs hc (agree_noR ht)
  have hfd : d.store.funcs = c.store.funcs := Runs.funcs_eq (Runs.stop (P := P) hs)
  have hd' : decompose? (swapStore dt d).store (swapStore dt d).code = some (E, a, hh, args) :=
    (decompose?_congr hag.1 d.code).trans hd
  have hA' : KeepFuncs (swapStore dt d).store xs := hxs.trans (hfd.symm.trans hag.1.symm)
  have hxs' : xs.funcs = s'.funcs := hxs.trans (hfd.symm.trans hA.symm)
  obtain ⟨et, hk', hag'⟩ := ih (inv_resumeIn r hinv hd hA) hxs'
  exact ⟨et, .call hsw hd' hA' hk', hag'⟩

/-- **Swapping a run into the returned stores of another trace** with the same calls and
answers. -/
theorem runsS_swapW {c d : Config Nat} {tr₂ : List SCall} (h : RunsS P KeepFuncs c tr₂ d)
    (hc : Inv A noR W c) {t : Store Nat} (ht : t.funcs = c.store.funcs) :
    ∀ tr₁ : List SCall, tr₁.map SCall.call = tr₂.map SCall.call →
      (∀ x ∈ tr₁, x.store.funcs = c.store.funcs) →
      ∃ dt, RunsS P KeepFuncs (swapStore t c) tr₁ (swapStore dt d) ∧ dt.funcs = d.store.funcs := by
  induction h generalizing t with
  | stop hs =>
    rintro (_ | _) htr -
    · obtain ⟨dt, hst, hag, -⟩ := steps_swap hs hc (agree_noR ht)
      exact ⟨dt, .stop hst, hag.1⟩
    · cases htr
  | call hs hd hA _ ih =>
    rintro (_ | ⟨⟨xh, xargs, xr, xs⟩, tr₁⟩) htr hst
    · cases htr
    · obtain ⟨hx, htr'⟩ := List.cons.inj htr
      obtain ⟨rfl, rfl, rfl⟩ : xh = _ ∧ xargs = _ ∧ xr = _ := by
        simpa [SCall.call] using hx
      have hxs : xs.funcs = _ := hst _ List.mem_cons_self
      refine swapW_call hs hd hA hc ht hxs fun hinv hxs' => ih hinv hxs' tr₁ htr' fun y hy => ?_
      exact (hst y (List.mem_cons_of_mem _ hy)).trans (hxs.symm.trans hxs')

/-- **Output agreement against hosts whose returned stores differ**, for subset code reading
no global, from configurations equal up to stores with the same functions. -/
theorem obsAgreeW_sl {c₁ c₂ : Config Nat} (hc : Inv A noR W c₁)
    (hf : c₁.store.funcs = c₂.store.funcs) (hfr : c₁.frame = c₂.frame) (hcode : c₁.code = c₂.code) :
    ObsAgreeW P KeepFuncs c₁ c₂ := by
  intro tr₁ tr₂ d₁ d₂ o₁ o₂ htr h₁ h₂ ho₁ ho₂
  have hc₂ : Inv A noR W c₂ := ⟨hf ▸ hc.1, hfr ▸ hcode ▸ hc.2.1, hcode ▸ hc.2.2⟩
  have hst : ∀ x ∈ tr₁, x.store.funcs = c₂.store.funcs :=
    fun x hx => (runsS_stores h₁ x hx).trans hf
  obtain ⟨dt, hrun, hag⟩ := runsS_swapW h₂ hc₂ (t := c₁.store) hf tr₁ htr hst
  have hc₁ : swapStore c₁.store c₂ = c₁ := by
    simp only [swapStore, ← hfr, ← hcode]
  have ho : OutAt (swapStore dt d₂) o₂ := outAt_swap ho₂ hag
  exact (detCfgS_sl hc tr₁ d₁ _ o₁ o₂ h₁ (hc₁ ▸ hrun) ho₁ ho).1

/-- **A module of subset functions reading no global is stateless against hosts whose returned
stores differ**, over the stores with the functions of `s₀`. -/
theorem statelessModuleW_of_good {Entry : Nat → Prop} {s₀ : Store Nat}
    (hm : GoodFuns A noR W s₀.funcs) (hE : ∀ a, Entry a → A a = true) :
    StatelessModuleW P KeepFuncs (fun s => s.funcs = s₀.funcs) Entry := by
  intro a ha s₁ s₂ vs h₁ h₂
  have hg : GoodFuns A noR W s₁.funcs := by
    rw [h₁]
    exact hm
  exact obsAgreeW_sl (Silmaril.Wasm.Det.Stateless.inv_invoke vs hg (hE a ha)) (h₁.trans h₂.symm) rfl
    (invoke_code_eq (h₁.trans h₂.symm) a vs)

end Silmaril.Proofs.Wasm.Det.Shared.Weak
