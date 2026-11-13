module

public import Silmaril.Proofs.Wasm.Det.NoMem.Transfer
public import Silmaril.Proofs.Wasm.Det.NoMem.Step
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.SingleThreaded.Locality

/-!
# The memory-free, float-free subset: determinism at every profile

* `inv_closed`: the invariant `Inv q ind` is closed under host-free steps (`step_seq`, and
  silmaril-lean's `Step.framesLocal`: function instances never change) and under resuming an
  import call with any answer (`seq_fill`: the answer replaces the call redex `decompose?`
  found, through `decompose?_sound`);
* `inv_detUpTo`: every host-free step from an `Inv` configuration at a profile `P` is a step at
  the deterministic profile `profile o` (`step_transfer`), for every grow oracle `o`;
* `detCfg_of_inv`: hence every `Inv` configuration is deterministic modulo traps and imports at
  every profile (`Silmaril.Wasm.Det.Core.detCfg_of_detUpTo`);
* soundness of the executable checks `storeB`, `closB`, `detFnB` and the per-function,
  per-module and per-instance consequences.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.NoMem

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.NoMem
  Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)

variable {q : Nat → Bool} {ind : Bool}

/-! ## Resumption -/

/-- Replacing a call redex that does not end with an `InS` element by code of the subset keeps
the subset, in every evaluation context. -/
theorem seq_fill {X Y : List Admin} (hX : ∀ p, ¬ lastS q p X)
    (hY : ∀ fs p, Seq q ind fs p Y) :
    ∀ (E : Ctx) (fs : List Nat) (p : Prop), Seq q ind fs p (E.fill X) → Seq q ind fs p (E.fill Y)
  | .top pre rest, fs, p, h => by
    simp only [Ctx.fill] at h ⊢
    rw [seq_append3] at h ⊢
    have hr : lastS q (lastS q p (vals pre)) X = False := propext ⟨hX _, False.elim⟩
    rw [hr] at h
    exact ⟨h.1, hY _ _, seq_mono False.elim h.2.2⟩
  | .label pre n cont E rest, fs, p, h => by
    simp only [Ctx.fill] at h ⊢
    rw [seq_append3] at h ⊢
    obtain ⟨h₁, ⟨hc, ⟨hcont, hb⟩, -⟩, h₃⟩ := h
    exact ⟨h₁, ⟨hc, ⟨hcont, seq_fill hX hY E fs False hb⟩, trivial⟩, h₃⟩
  | .handler pre n cs E rest, fs, p, h => by
    simp only [Ctx.fill] at h ⊢
    rw [seq_append3] at h ⊢
    obtain ⟨h₁, ⟨hc, hb, -⟩, h₃⟩ := h
    exact ⟨h₁, ⟨hc, seq_fill hX hY E fs False hb, trivial⟩, h₃⟩
  | .frame pre n f E rest, fs, p, h => by
    simp only [Ctx.fill] at h ⊢
    rw [seq_append3] at h ⊢
    obtain ⟨h₁, ⟨hc, hb, -⟩, h₃⟩ := h
    exact ⟨h₁, ⟨hc, seq_fill hX hY E f.module.funcs False hb, trivial⟩, h₃⟩

/-- The call redex of an import call does not end with an `InS` element. -/
theorem not_lastS_redex {args : List Val} {a : Nat} {yy : Admin} (hy : yy.IsCallRef) (p : Prop) :
    ¬ lastS q p (vals args ++ [.ref (.func a), yy]) := by
  rw [lastS_append]
  exact not_inS_callRef hy

/-! ## The invariant is closed -/

/-- **Closure** of the invariant under host-free steps and resumptions, at every profile. -/
theorem inv_closed (P : Profile) : Closed P (Inv q ind) where
  step c d hc hs := by
    obtain ⟨hM, hS, hF⟩ := hc
    obtain ⟨h₁, h₂⟩ := step_seq hM hs hF hS
    refine ⟨hM, h₂ ▸ h₁, ?_⟩
    have hfun : d.store.funcs = c.store.funcs := (Step.framesLocal hs).1
    unfold FunOk at hF ⊢
    rw [hfun]
    exact hF
  resume c E a h args r hc hd := by
    obtain ⟨hM, hS, hF⟩ := hc
    obtain ⟨_, yy, _, _, _, _, hy, _, _, hcode⟩ := decompose?_sound hd
    refine ⟨hM, ?_, hF⟩
    rw [hcode] at hS
    exact seq_fill (not_lastS_redex hy) (fun _ _ => seq_toAdmin r) E _ False hS

/-- Every host-free step from an `Inv` configuration is a step of every deterministic
profile. -/
theorem inv_detUpTo {P : Profile} (o : GrowOracle) {c : Config Nat} (hc : Inv q ind c) :
    DetUpTo P o c :=
  fun _ he => Or.inl (step_transfer he hc.2.1)

/-- **Determinism of subset configurations**, at every profile. -/
theorem detCfg_of_inv {P : Profile} {c : Config Nat} (hc : Inv q ind c) : DetCfg P c :=
  detCfg_of_detUpTo (o := fun _ _ _ _ => false) (inv_closed P) (fun _ h => inv_detUpTo _ h) hc

/-! ## Invocations -/

/-- The invocation of a function that may be entered satisfies the invariant. -/
theorem inv_invoke {s : Store Nat} {a : Nat} (vs : List Val) (hM : Mode q ind)
    (hF : FunOk q ind s.funcs) (ha : q a = true) : Inv q ind (invoke s a vs) := by
  refine ⟨hM, ?_, hF⟩
  show Seq q ind [] False (vals vs ++ _)
  rw [seq_vals_append]
  exact ⟨fun h => absurd h isCRT_ref, trivial, fun _ b hb => by cases hb; exact ha,
    trivial, trivial⟩

/-! ## The executable checks -/

theorem funOk_of_funcB {H : Type} {F : List (FuncInst H)}
    (h : ∀ b fi, q b = true → F[b]? = some fi → funcB q ind fi = true) : FunOk q ind F := by
  intro b fi fn hb hf hc
  have := h b fi hb hf
  simpa [funcB, hc] using this

theorem funOk_of_storeB {s : Store Nat} (h : storeB s = true) :
    FunOk (fun _ => true) true s.funcs :=
  funOk_of_funcB fun _ _ _ hf => List.all_eq_true.mp h _ (List.mem_of_getElem? hf)

theorem funOk_of_closB {s : Store Nat} {A : List Nat} (h : closB s A = true) :
    FunOk (fun x => A.contains x) false s.funcs := by
  refine funOk_of_funcB fun b fi hb hf => ?_
  have := List.all_eq_true.mp h b (by simpa using hb)
  simpa [hf] using this

theorem mode_full : Mode (fun _ => true) true := fun _ _ => rfl

theorem mode_direct (q : Nat → Bool) : Mode q false := fun h => absurd h Bool.false_ne_true

/-- **Full mode**: every function of a store passing `storeB` is deterministic. -/
theorem detFn_of_storeB {P : Profile} {s : Store Nat} (h : storeB s = true) (a : Nat) :
    DetFn P s a :=
  fun vs _ => detCfg_of_inv (inv_invoke vs mode_full (funOk_of_storeB h) rfl)

/-- **Direct mode**: every function of `A` is deterministic when `A` passes `closB`. -/
theorem detFn_of_closB {P : Profile} {s : Store Nat} {A : List Nat} (h : closB s A = true)
    {a : Nat} (ha : a ∈ A) : DetFn P s a :=
  fun vs _ => detCfg_of_inv
    (inv_invoke vs (mode_direct _) (funOk_of_closB h) (List.contains_iff_mem.mpr ha))

/-- **The per-function check**. -/
theorem detFn_of_detFnB {P : Profile} {s : Store Nat} {a : Nat} (h : detFnB s a = true) :
    DetFn P s a := by
  simp only [detFnB, Bool.and_eq_true] at h
  exact detFn_of_closB h.2 (List.contains_iff_mem.mp h.1)

theorem storeB_congr {s t : Store Nat} (h : s.funcs = t.funcs) : storeB s = storeB t := by
  simp only [storeB, h]

theorem closB_congr {s t : Store Nat} (h : s.funcs = t.funcs) (A : List Nat) :
    closB s A = closB t A := by
  simp only [closB, h]

/-- **Per module, full mode**: a store passing `storeB` is a deterministic module for every set
of entries. -/
theorem detModule_of_storeB {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (h : storeB s₀ = true) : DetModule P Entry s₀ :=
  fun _ hs a _ => detFn_of_storeB ((storeB_congr (CallReach.funcs_eq hs)).trans h) a

/-- **Per module, direct mode**: with the entries `A`, a store passing `closB s₀ A` is a
deterministic module. -/
theorem detModule_of_closB {P : Profile} {s₀ : Store Nat} {A : List Nat}
    (h : closB s₀ A = true) : DetModule P (· ∈ A) s₀ :=
  fun _ hs _ ha => detFn_of_closB ((closB_congr (CallReach.funcs_eq hs) A).trans h) ha

/-- **Per instance**: an instantiation configuration of the subset over a store passing
`storeB` is a deterministic instance (the instantiation phase and every later call). -/
theorem detInst_of_storeB {P : Profile} {c₀ : Config Nat} {Entry : Nat → Prop}
    (h : storeB c₀.store = true) (hc : Seq (fun _ => true) true c₀.frame.module.funcs False c₀.code) :
    DetInst P c₀ Entry := by
  refine ⟨detCfg_of_inv ⟨mode_full, hc, funOk_of_storeB h⟩, fun tr d r hr _ _ => ?_⟩
  exact detModule_of_storeB ((storeB_congr (Runs.funcs_eq hr)).trans h)

end Silmaril.Proofs.Wasm.Det.NoMem
