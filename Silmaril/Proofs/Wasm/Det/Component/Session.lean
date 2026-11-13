module

public import Silmaril.Wasm.Det.Component.Defs
public import Silmaril.Wasm.Det.Core.Thms

/-!
# Sessions of canonical-ABI exports: proofs

* unwinding: `sReach_obs`, `sStatelessAt_of_obs` (confinement and observation give
  statelessness);
* invariants over Core runs: `steps_inv`, `runs_inv`, `steps_obs`, `runs_obs` (per-step
  confinement);
* the canonical-ABI phases: `abiCall_obs`/`abi_confined` (confinement from `ConfVC`),
  `lower_rel`, `abiCall_out_eq`/`abi_obsDetermines` (observation from `ReallocVC`, `WriteVC`,
  `CoreVC`);
* function instances: `memWrite_funcs`, `confVC_funcs`, `sReach_funcs`, `confined_funcsAt`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Component

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Component

variable {P : Profile}

/-! ## Unwinding -/

/-- Under confinement, every call state is `Obs`-related to the initial one. -/
theorem sReach_obs {ι α β : Type} {C : ι → CallSem α β} {s₀ : Store Nat}
    {Obs : Store Nat → Store Nat → Prop} (hP : IsPER Obs) (h₀ : Obs s₀ s₀)
    (hC : Confined C s₀ Obs) {s : Store Nat} (hs : SReach C s₀ s) : Obs s₀ s := by
  induction hs with
  | init => exact h₀
  | call hs hc ih => exact hP.trans ih (hC _ _ _ _ _ _ hs hc)

/-- **Unwinding**: confinement and observation give statelessness. -/
theorem sStatelessAt_of_obs {ι α β : Type} {C : ι → CallSem α β} {s₀ : Store Nat}
    {Obs : Store Nat → Store Nat → Prop} (hP : IsPER Obs) (h₀ : Obs s₀ s₀)
    (hC : Confined C s₀ Obs) {i : ι} (hO : ObsDetermines C Obs i) : SStatelessAt C s₀ i :=
  fun s₁ s₂ h₁ h₂ v tr t₁ t₂ w₁ w₂ c₁ c₂ =>
    hO s₁ s₂ (hP.trans (hP.symm (sReach_obs hP h₀ hC h₁)) (sReach_obs hP h₀ hC h₂))
      v tr t₁ t₂ w₁ w₂ c₁ c₂

/-! ## Invariants over Core runs -/

/-- A `Closed` invariant holds along host-free runs. -/
theorem steps_inv {J : Config Nat → Prop} (hJ : Closed P J) {c d : Config Nat} (hc : J c)
    (h : Steps P Det.noHost c d) : J d := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact hJ.step _ _ ih hs

/-- A `Closed` invariant holds along runs with import calls. -/
theorem runs_inv {J : Config Nat → Prop} (hJ : Closed P J) {c d : Config Nat} {tr : List Call}
    (hc : J c) (h : Runs P c tr d) : J d := by
  induction h with
  | stop hs => exact steps_inv hJ hc hs
  | call hs hd _ ih => exact ih (hJ.resume _ _ _ _ _ _ (steps_inv hJ hc hs) hd)

/-- Per-step confinement along host-free runs. -/
theorem steps_obs {Obs : Store Nat → Store Nat → Prop} {J : Config Nat → Prop}
    (hS : StepConfined P Obs J) (hP : IsPER Obs) (hr : ∀ s, Obs s s) {c d : Config Nat}
    (hc : J c) (h : Steps P Det.noHost c d) : Obs c.store d.store := by
  induction h with
  | refl => exact hr _
  | tail h₁ hs ih => exact hP.trans ih (hS.step _ _ (steps_inv hS.closed hc h₁) hs)

/-- **Per-step confinement along runs** (import answers keep the store). -/
theorem runs_obs {Obs : Store Nat → Store Nat → Prop} {J : Config Nat → Prop}
    (hS : StepConfined P Obs J) (hP : IsPER Obs) (hr : ∀ s, Obs s s) {c d : Config Nat}
    {tr : List Call} (hc : J c) (h : Runs P c tr d) : Obs c.store d.store := by
  induction h with
  | stop hs => exact steps_obs hS hP hr hc hs
  | call hs hd _ ih =>
    exact hP.trans (steps_obs hS hP hr hc hs)
      (ih (hS.closed.resume _ _ _ _ _ _ (steps_inv hS.closed hc hs) hd))

/-! ## Confinement of the canonical-ABI phases -/

section Conf

variable {Obs : Store Nat → Store Nat → Prop} {x : AbiFn}

theorem lower_obs (hP : IsPER Obs) (hr : ∀ s, Obs s s) (hV : ConfVC P Obs x) {s s₁ : Store Nat}
    {v : AVal} {args : List Val} (h : Lower P x s v s₁ args) : Obs s s₁ := by
  cases h with
  | flat _ => exact hr _
  | buf hx hs hd hw =>
    exact hP.trans (hV.realloc _ _ hx _ _ _ hs) (hV.write _ _ hx _ _ _ _ _ _ hs hd hw)

theorem lowerFails_obs (hV : ConfVC P Obs x) {s s' : Store Nat} {v : AVal}
    (h : LowerFails P x s v s') : Obs s s' := by
  cases h with
  | realloc hx hs _ _ => exact hV.realloc _ _ hx _ _ _ hs
  | write hx hs _ _ => exact hV.realloc _ _ hx _ _ _ hs

theorem postRet_obs (hr : ∀ s, Obs s s) (hV : ConfVC P Obs x) {s s' : Store Nat} {ws : List Val}
    {ok : Bool} (h : PostRet P x s ws s' ok) : Obs s s' := by
  cases h with
  | none _ => exact hr _
  | run hx hs _ => exact hV.post _ hx _ _ _ hs

/-- Every canonical-ABI call ends in an `Obs`-related store. -/
theorem abiCall_obs (hP : IsPER Obs) (hr : ∀ s, Obs s s) (hV : ConfVC P Obs x)
    {s s' : Store Nat} {v : AVal} {tr : List Call} {o : Option AVal}
    (h : AbiCall P x s v tr s' o) : Obs s s' := by
  cases h with
  | lowerFails h => exact lowerFails_obs hV h
  | coreFails hl hr' _ _ => exact hP.trans (lower_obs hP hr hV hl) (hV.core _ _ _ _ hr')
  | ret hl hr' _ hp =>
    exact hP.trans (hP.trans (lower_obs hP hr hV hl) (hV.core _ _ _ _ hr')) (postRet_obs hr hV hp)

/-- **Confinement of a canonical-ABI session** from the per-export `ConfVC`s. -/
theorem abi_confined {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat} (hP : IsPER Obs)
    (hr : ∀ s, Obs s s) (hV : ∀ i, ConfVC P Obs (X i)) : Confined (abiSem P X) s₀ Obs :=
  fun _ i _ _ _ _ _ h => abiCall_obs hP hr (hV i) h

end Conf

/-! ## Observation through the canonical-ABI phases -/

section Obs

variable {Obs Mid Arg : Store Nat → Store Nat → Prop} {x : AbiFn}

/-- Lowered arguments are numbers. -/
theorem lower_nums {s s₁ : Store Nat} {v : AVal} {args : List Val} (h : Lower P x s v s₁ args) :
    Nums args := by
  cases h with
  | flat _ =>
    intro a ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
    exact ⟨_, rfl⟩
  | buf _ _ _ _ =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨_, rfl⟩
    · rcases List.mem_singleton.mp ha' with rfl
      exact ⟨_, rfl⟩

/-- `Val.i32` is injective. -/
theorem i32_inj {a b : BitVec 32} (h : Val.i32 a = Val.i32 b) : a = b := by
  injection h with h₁
  injection h₁

/-- **Lowering from `Obs`-related stores**: the same flat arguments, `Arg`-related stores. -/
theorem lower_rel (hflat : x.argBuf = none → ∀ s₁ s₂, Obs s₁ s₂ → Arg s₁ s₂)
    (hbuf : ∀ ra m, x.argBuf = some (ra, m) → ReallocVC P Obs Mid ra ∧ WriteVC Mid Arg m)
    {s₁ s₂ t₁ t₂ : Store Nat} {v : AVal} {a₁ a₂ : List Val} (ho : Obs s₁ s₂)
    (h₁ : Lower P x s₁ v t₁ a₁) (h₂ : Lower P x s₂ v t₂ a₂) : a₁ = a₂ ∧ Arg t₁ t₂ := by
  cases h₁ with
  | flat hx =>
    cases h₂ with
    | flat _ => exact ⟨rfl, hflat hx _ _ ho⟩
  | buf hx hs hd hw =>
    cases h₂ with
    | buf hx' hs' hd' hw' =>
      show _ ∧ Arg t₁ t₂
      obtain ⟨hra, hm⟩ := Prod.mk.inj (Option.some.inj (hx.symm.trans hx'))
      have hs'' := hra ▸ hs'
      obtain ⟨hp, hmid⟩ := (hbuf _ _ hx).1 _ _ _ _ _ _ _ ho hs hs'' hd hd'
      have hw'' := hm ▸ hp ▸ hw'
      exact ⟨by rw [hp], (hbuf _ _ hx).2 _ _ _ _ _ _ hmid hw hw''⟩

/-- An `if` with a `some` result. -/
theorem ite_some {α : Type} {b : Bool} {a : Option α} {w : α}
    (h : (if b then a else none) = some w) : b = true ∧ a = some w := by
  cases b with
  | false => cases h
  | true => exact ⟨rfl, h⟩

/-- **Two canonical-ABI calls from `Obs`-related stores**: equal non-trapping outputs. -/
theorem abiCall_out_eq (hflat : x.argBuf = none → ∀ s₁ s₂, Obs s₁ s₂ → Arg s₁ s₂)
    (hbuf : ∀ ra m, x.argBuf = some (ra, m) → ReallocVC P Obs Mid ra ∧ WriteVC Mid Arg m)
    (hC : CoreVC P Arg x) {s₁ s₂ t₁ t₂ : Store Nat} {v : AVal} {tr : List Call}
    {o₁ o₂ : Option AVal} {w₁ w₂ : AVal} (ho : Obs s₁ s₂) (h₁ : AbiCall P x s₁ v tr t₁ o₁)
    (h₂ : AbiCall P x s₂ v tr t₂ o₂) (e₁ : o₁ = some w₁) (e₂ : o₂ = some w₂) : w₁ = w₂ := by
  cases h₁ with
  | lowerFails _ => cases e₁
  | coreFails _ _ _ _ => cases e₁
  | ret hl₁ hr₁ hd₁ _ =>
    cases h₂ with
    | lowerFails _ => cases e₂
    | coreFails _ _ _ _ => cases e₂
    | ret hl₂ hr₂ hd₂ _ =>
      show w₁ = w₂
      obtain ⟨ha, harg⟩ := lower_rel hflat hbuf ho hl₁ hl₂
      have hr₂' := ha ▸ hr₂
      obtain ⟨-, hlift⟩ := hC _ _ _ _ _ _ _ _ harg (lower_nums hl₁) hr₁ hr₂' hd₁ hd₂
      have hs : some w₁ = some w₂ := (ite_some e₁).2.symm.trans (hlift.trans (ite_some e₂).2)
      exact Option.some.inj hs

/-- **Observation for a canonical-ABI export** from the phase VCs. -/
theorem abi_obsDetermines {ι : Type} (X : ι → AbiFn) (i : ι)
    (hflat : (X i).argBuf = none → ∀ s₁ s₂, Obs s₁ s₂ → Arg s₁ s₂)
    (hbuf : ∀ ra m, (X i).argBuf = some (ra, m) → ReallocVC P Obs Mid ra ∧ WriteVC Mid Arg m)
    (hC : CoreVC P Arg (X i)) : ObsDetermines (abiSem P X) Obs i :=
  fun _ _ ho _ _ _ _ _ _ h₁ h₂ => abiCall_out_eq hflat hbuf hC ho h₁ h₂ rfl rfl

end Obs

/-! ## Function instances -/

/-- Writing memory keeps the function instances. -/
theorem memWrite_funcs {s t : Store Nat} {m p : Nat} {bs : List UInt8}
    (h : memWrite s m p bs = some t) : t.funcs = s.funcs := by
  unfold memWrite at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

/-- Runs keep the function instances of the invoked store. -/
theorem runs_invoke_funcs {s : Store Nat} {a : Nat} {vs : List Val} {tr : List Call}
    {d : Config Nat} (h : Runs P (invoke s a vs) tr d) : s.funcs = d.store.funcs :=
  (Runs.funcs_eq h).symm

/-- Every canonical-ABI export is confined with respect to its function instances. -/
theorem confVC_funcs (x : AbiFn) : ConfVC P FuncsEq x where
  realloc _ _ _ _ _ _ hs := runs_invoke_funcs (.stop hs)
  write _ _ _ _ _ _ _ _ _ _ _ hw := (memWrite_funcs hw).symm
  core _ _ _ _ hr := runs_invoke_funcs hr
  post _ _ _ _ _ hs := runs_invoke_funcs (.stop hs)

theorem isPER_funcsEq : IsPER FuncsEq where
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

theorem isPER_funcsAt (F : List (FuncInst Nat)) : IsPER (FuncsAt F) where
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨h₁.1, h₂.2⟩

/-- Call states of a canonical-ABI session hold the initial function instances. -/
theorem sReach_funcs {ι : Type} {X : ι → AbiFn} {s₀ s : Store Nat}
    (hs : SReach (abiSem P X) s₀ s) : s.funcs = s₀.funcs :=
  (sReach_obs isPER_funcsEq rfl (abi_confined isPER_funcsEq (fun _ => rfl)
    (fun i => confVC_funcs (X i))) hs).symm

/-- A canonical-ABI session is confined with respect to its initial function instances. -/
theorem confined_funcsAt {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat} :
    Confined (abiSem P X) s₀ (FuncsAt s₀.funcs) :=
  fun _ i _ _ _ _ hs h =>
    ⟨sReach_funcs hs, (abiCall_obs isPER_funcsEq (fun _ => rfl) (confVC_funcs (X i)) h).symm.trans
      (sReach_funcs hs)⟩

end Silmaril.Proofs.Wasm.Det.Component
