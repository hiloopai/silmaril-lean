module

public import Silmaril.Proofs.Wasm.Det.GrowTrap.Closure
public import Silmaril.Proofs.Wasm.Det.GrowTrap.Transfer

/-!
# Subset 2 (allocation failure traps): determinism modulo traps and imports

* `inv_closed`: `Inv G` is closed under host-free steps (`step_inv`, the module of the frame and
  the function instances never change) and under resuming an import call with any answer
  (`post_fill`: the host-call redex `E.fill (vals args ++ [REF.FUNC_ADDR a, CALL_REF])` becomes
  `E.fill r.toAdmin`);
* `inv_detUpTo`: every host-free step from an `Inv G` configuration at an arbitrary profile is
  a step of `profile neverFail` or leads to `Dm` code, which is `Doomed` (`dm_doomed`);
* `detCfg_of_inv`: hence (silmaril-lean's unique normal forms at deterministic profiles, through
  `Silmaril.Wasm.Det.Core.detCfg_of_detUpTo`) every `Inv G` configuration is deterministic modulo
  traps and imports, at every profile;
* `inv_invoke`, `detCall_of_funcsOk`, `detFn_of_funcsOk`, `detModule_of_funcsOk`: invocations
  of functions in `G` (and modules whose entries are in such sets);
* `funcsOk_of_checkG`, `mem_reachOf`, `detFn_of_check`, `detModule_of_check`: the executable
  check is sound.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.GrowTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Det.GrowTrap Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Verify (instrCalls exprCalls)
open Silmaril.Wasm.Numerics (Profile)

variable {G : Nat → Prop}

/-! ## Resumption -/

/-- Replacing a segment `A` by flat code `B` without `memory.grow` and `CALL_REF dt`, when `A`
ends with an element that may not precede `CALL_REF dt`. -/
theorem post_mid {fs : List Nat} {pre : List Val} {A B rest K : List Admin} {p : Option Admin}
    (hA : GAs G fs (vals pre ++ A ++ rest)) (hG : GrowSeq (vals pre ++ A ++ rest) K)
    (hP : PairSeq G p (vals pre ++ A ++ rest)) (hB : GAs G fs B)
    (hBg : ∀ x ∈ B, isGrowA x = false) (hBc : ∀ x ∈ B, isCRT x = false)
    (hend : ¬ EndOpt G (lastP p (vals pre ++ A))) : Post G fs K p (vals pre ++ B ++ rest) := by
  have hA' : (GAs G fs (vals pre) ∧ GAs G fs A) ∧ GAs G fs rest := by simpa using hA
  have hGr : GrowSeq rest K := (growSeq_append.mp hG).2
  have hPr : PairSeq G (lastP p (vals pre ++ A)) rest := (pairSeq_append.mp hP).2
  have hnoG : ∀ x ∈ vals pre ++ B, isGrowA x = false := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      exact isGrowA_toAdmin v
    · exact hBg x hx
  have hnoC : ∀ x ∈ vals pre ++ B, isCRT x = false := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      exact isCRT_toAdmin v
    · exact hBc x hx
  exact ⟨by simp [hB, hA'.2], growSeq_append.mpr ⟨growSeq_of_noGrow hnoG _, hGr⟩,
    pairSeq_append.mpr ⟨pairSeq_of_noCRT hnoC _, PairSeq.congr hPr fun h => (hend h).elim⟩⟩

theorem lastP_label_not_end {p : Option Admin} {pre : List Val} {x : Admin}
    (hx : ¬ EndOk G x) : ¬ EndOpt G (lastP p (vals pre ++ [x])) := by
  rw [lastP_append_of_ne (by simp)]
  rintro ⟨y, hy, hyE⟩
  have hxy : x = y := by simpa using hy
  exact hx (hxy ▸ hyE)

theorem toAdmin_noGrow (r : Result) : ∀ x ∈ r.toAdmin, isGrowA x = false := by
  rcases r with vs | a | _
  · intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    exact isGrowA_toAdmin v
  · simp [Result.toAdmin, isGrow]
  · simp [Result.toAdmin]

theorem toAdmin_noCRT (r : Result) : ∀ x ∈ r.toAdmin, isCRT x = false := by
  rcases r with vs | a | _
  · intro x hx
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    exact isCRT_toAdmin v
  · simp [Result.toAdmin]
  · simp [Result.toAdmin]

theorem gAs_toAdmin (fs : List Nat) (r : Result) : GAs G fs r.toAdmin := by
  rcases r with vs | a | _
  · exact gAs_vals vs
  · simp [Result.toAdmin, GA, instrOk, flatOk, CallsIn, instrCalls]
  · simp [Result.toAdmin, GA]

theorem gA_label_of {fs : List Nat} {n : Nat} {cont : List Instr} {b b' : List Admin}
    (hl : GA G fs (.label n cont b)) (ih : Post G fs [] none b') : GA G fs (.label n cont b') := by
  simp only [GA]
  exact ⟨hl.1, hl.2.1, ih.1, ih.2.1, ih.2.2⟩

theorem gA_frame_of {fs : List Nat} {n : Nat} {f : Frame} {b' : List Admin}
    (ih : Post G f.module.funcs [] none b') : GA G fs (.frame n f b') := by
  simp only [GA]
  exact ⟨ih.1, ih.2.1, ih.2.2⟩

/-- **Resuming a host call keeps the code invariant.** -/
theorem post_fill {args : List Val} {a : Nat} {yy : Admin} (hyy : yy.IsCallRef) (r : Result) :
    ∀ (E : Ctx) (fs : List Nat) (K : List Admin) (p : Option Admin),
      GAs G fs (E.fill (vals args ++ [.ref (.func a), yy])) →
      GrowSeq (E.fill (vals args ++ [.ref (.func a), yy])) K →
      PairSeq G p (E.fill (vals args ++ [.ref (.func a), yy])) → Post G fs K p (E.fill r.toAdmin)
  | .top pre rest, fs, K, p, hA, hG, hP => by
    have hend : ¬ EndOpt G (lastP p (vals pre ++ (vals args ++ [.ref (.func a), yy]))) := by
      have e : vals pre ++ (vals args ++ [.ref (.func a), yy]) =
          (vals pre ++ vals args ++ [.ref (.func a)]) ++ [yy] := by simp
      rw [e, lastP_append_of_ne (by simp)]
      rintro ⟨y, hy, hyE⟩
      have hxy : yy = y := by simpa using hy
      exact isCallRef_not_end hyy (hxy ▸ hyE)
    exact post_mid hA hG hP (gAs_toAdmin fs r) (toAdmin_noGrow r) (toAdmin_noCRT r) hend
  | .label pre n cont E rest, fs, K, p, hA, hG, hP => by
    show Post G fs K p (vals pre ++ [.label n cont (E.fill r.toAdmin)] ++ rest)
    have hl : GA G fs (.label n cont (E.fill (vals args ++ [.ref (.func a), yy]))) :=
      gA_of_mem hA (by simp [Ctx.fill])
    have ih : Post G fs [] none (E.fill r.toAdmin) :=
      post_fill hyy r E fs [] none hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2
    exact post_mid (A := [.label n cont _]) hA hG hP ⟨gA_label_of hl ih, trivial⟩
      (by simp) (by simp) (lastP_label_not_end (by simp [EndOk]))
  | .handler pre n cs E rest, fs, K, p, hA, hG, hP => by
    have hl : GA G fs (.handler n cs (E.fill (vals args ++ [.ref (.func a), yy]))) :=
      gA_of_mem hA (by simp [Ctx.fill])
    exact absurd hl (by simp [GA])
  | .frame pre n f E rest, fs, K, p, hA, hG, hP => by
    show Post G fs K p (vals pre ++ [.frame n f (E.fill r.toAdmin)] ++ rest)
    have hl : GA G fs (.frame n f (E.fill (vals args ++ [.ref (.func a), yy]))) :=
      gA_of_mem hA (by simp [Ctx.fill])
    have ih : Post G f.module.funcs [] none (E.fill r.toAdmin) :=
      post_fill hyy r E f.module.funcs [] none hl.1 hl.2.1 hl.2.2
    exact post_mid (A := [.frame n f _]) hA hG hP ⟨gA_frame_of ih, trivial⟩
      (by simp) (by simp) (lastP_label_not_end (by simp [EndOk]))

/-! ## Closure and determinism -/

/-- **`Inv G` is closed** under host-free steps (every profile) and resumptions. -/
theorem inv_closed (P : Profile) : Closed P (Inv G) where
  step c d hc hs := by
    have hpost : Post G c.frame.module.funcs [] none d.code :=
      step_inv hs hc.2.2.2 [] none hc.1 hc.2.1 hc.2.2.1
    have hm : d.frame.module = c.frame.module := step_module hs
    have hfs : d.store.funcs = c.store.funcs := (Step.framesLocal hs).1
    exact ⟨by rw [hm]; exact hpost.1, hpost.2.1, hpost.2.2, by rw [hfs]; exact hc.2.2.2⟩
  resume c E a h args r hc hd := by
    obtain ⟨fi, yy, ps, rs, -, -, hyy, -, -, hcode⟩ := decompose?_sound hd
    have hpost := post_fill hyy r E c.frame.module.funcs [] none (hcode ▸ hc.1) (hcode ▸ hc.2.1)
      (hcode ▸ hc.2.2.1)
    exact ⟨hpost.1, hpost.2.1, hpost.2.2, hc.2.2.2⟩

/-- **Every step from `Inv G` is a step of `profile neverFail`, or doomed.** -/
theorem inv_detUpTo {P : Profile} {c : Config Nat} (hc : Inv G c) : DetUpTo P neverFail c := by
  intro e he
  rcases step_transfer (G := G) he [] hc.1 hc.2.1 with h | hD
  · exact .inl h
  · exact .inr (dm_doomed (by simpa using hD))

/-- **Determinism modulo traps and imports of the subset**, at every profile. -/
theorem detCfg_of_inv {P : Profile} {c : Config Nat} (hc : Inv G c) : DetCfg P c :=
  detCfg_of_detUpTo (o := neverFail) (inv_closed P) (fun _ h => inv_detUpTo h) hc

/-- The invocation of a function in `G` satisfies the invariant. -/
theorem inv_invoke {s : Store Nat} {a : Nat} (ha : G a) (hF : FuncsOk G s.funcs)
    (vs : List Val) : Inv G (invoke s a vs) := by
  refine ⟨by simp [invoke, GA], ?_, ?_, hF⟩
  · show GrowSeq (vals vs ++ [.ref (.func a), .callRefType _]) []
    exact growSeq_append.mpr ⟨growSeq_vals _ _, growSeq_of_noGrow (by simp) _⟩
  show PairSeq G none (vals vs ++ [.ref (.func a), .callRefType _])
  refine pairSeq_append.mpr ⟨pairSeq_vals _ _, ?_⟩
  exact ⟨by simp, fun _ => ⟨_, rfl, ha⟩, trivial⟩

theorem detCall_of_funcsOk {P : Profile} {s : Store Nat} {a : Nat} (ha : G a)
    (hF : FuncsOk G s.funcs) (vs : List Val) : DetCall P s a vs :=
  detCfg_of_inv (inv_invoke ha hF vs)

theorem detFn_of_funcsOk {P : Profile} {s : Store Nat} {a : Nat} (ha : G a)
    (hF : FuncsOk G s.funcs) : DetFn P s a :=
  fun vs _ => detCall_of_funcsOk ha hF vs

theorem detModule_of_funcsOk {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (hE : ∀ a, Entry a → G a) (hF : FuncsOk G s₀.funcs) : DetModule P Entry s₀ := by
  intro s hs a ha
  have hfs : s.funcs = s₀.funcs := CallReach.funcs_eq hs
  exact detFn_of_funcsOk (hE a ha) (hfs ▸ hF)

/-! ## The executable check -/

theorem funcsOk_of_checkG {F : List (FuncInst Nat)} {L : List Nat} (h : checkG F L = true) :
    FuncsOk (· ∈ L) F := by
  intro a fi fn ha hf hcode
  have hb : funcOkB F L a = true := List.all_eq_true.mp h a ha
  simp only [funcOkB, hf, hcode, Bool.and_eq_true, List.all_eq_true] at hb
  refine ⟨hb.1, fun i hi x hx b hxb => ?_⟩
  have hc := hb.2 x (mem_exprCalls hi hx)
  rw [hxb] at hc
  simpa using hc

theorem mem_iterate_reachStep (F : List (FuncInst Nat)) (a : Nat) :
    ∀ n (L : List Nat), a ∈ L → a ∈ (reachStep F)^[n] L
  | 0, _, h => h
  | n + 1, L, h => by
    rw [Function.iterate_succ_apply]
    exact mem_iterate_reachStep F a n _ (List.mem_append_left _ h)

theorem mem_reachOf (F : List (FuncInst Nat)) (a : Nat) : a ∈ reachOf F a :=
  mem_iterate_reachStep F a _ [a] (by simp)

/-- **Soundness of the check**: a function passing `check` is deterministic modulo traps and
imports, at every profile. -/
theorem detFn_of_check {P : Profile} {s : Store Nat} {a : Nat} (h : check s a = true) :
    DetFn P s a :=
  detFn_of_funcsOk (G := (· ∈ reachOf s.funcs a)) (mem_reachOf _ a) (funcsOk_of_checkG h)

/-- A module whose entries all pass `check` is deterministic modulo traps and imports, at every
profile. -/
theorem detModule_of_check {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (h : ∀ a, Entry a → check s₀ a = true) : DetModule P Entry s₀ := by
  intro s hs a ha
  have hfs : s.funcs = s₀.funcs := CallReach.funcs_eq hs
  have hc : check s a = true := by simpa [check, hfs] using h a ha
  exact detFn_of_check hc

end Silmaril.Proofs.Wasm.Det.GrowTrap
