module

public import Silmaril.Proofs.Wasm.Models.FXAsyncFX.Step

/-!
# Behaviours: the kernel's are `StepFX'` behaviours of the encoding

* `infinite_of_plus`: a predicate from which a positive run always reaches the predicate again
  gives an infinite trace;
* `supported_next`: the fragment holds along the rest of a run;
* `stop_in_fx`: a kernel run that stops (in the fragment) is a `StepFX'` run to a result of the
  same behaviour; `div_in_fx`: a diverging kernel run gives an infinite `StepFX'` trace;
* **`beh_in_fx`**: from related configurations, with the fragment along the kernel run, every
  kernel behaviour (as `obsB`) is a `StepFX'` behaviour; `trap_not_beh`: and the kernel does not
  trap;
* `rel_init`: the kernel's call of `f` and the FX call `fxInit` are related.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX

variable {H : Type} (S : Setup H) {W : Prog (Ins Val)}

theorem infinite_of_plus {A : Type} {R : A → A → Prop} (Q : A → Prop)
    (h : ∀ a, Q a → ∃ b, Relation.TransGen R a b ∧ Q b) {a : A} (ha : Q a) :
    Silmaril.InfiniteTrace R a := by
  refine Silmaril.InfiniteTrace.coinduct (fun a => ∃ b, Relation.TransGen R a b ∧ Q b)
    (fun a ⟨b, hab, hb⟩ => ?_) (h a ha)
  obtain ⟨a', h₁, h₂⟩ := Relation.TransGen.head'_iff.mp hab
  refine ⟨a', h₁, ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h₂ with rfl | h₃
  · exact h b hb
  · exact ⟨b, h₃, hb⟩

theorem runN_succ_next {x x' : SCfg Val} (h : sstep W i32Test x = .next x') (n : Nat) :
    runN (sstep W i32Test) (n + 1) x = runN (sstep W i32Test) n x' := by
  simp only [runN, h]

theorem supported_next {x x' : SCfg Val} (hsup : Supported W x)
    (h : sstep W i32Test x = .next x') : Supported W x' :=
  fun n y hy => hsup (n + 1) y (by rw [runN_succ_next h]; exact hy)

theorem fine_of_supported {x : SCfg Val} (hsup : Supported W x) : fine W x = true :=
  hsup 0 x rfl

/-- A kernel run that stops is matched by a `StepFX'` run to a result. -/
theorem stop_in_fx (hok : Ok S W) : ∀ (n : Nat) {x : SCfg Val} {c : ConfigFX H} {o : Outcome Val},
    Rel S W x c → Supported W x → runN (sstep W i32Test) n x = .stop o →
      o ≠ .trap ∧ ∃ (d : ConfigFX H) (r : Result), StepsFX' S.P S.host S.fx c d ∧
        d.code = r.toAdmin.map .core ∧ r.toBehaviour = obsB o.toObs
  | 0, _, _, _, _, _, h => nomatch h
  | n + 1, x, c, o, hR, hsup, h => by
    have hm : Matched S W c (sstep W i32Test x) := sim_step S hok hR (fine_of_supported hsup)
    cases hx : sstep W i32Test x with
    | next x' =>
      rw [hx] at hm
      obtain ⟨c', hcc', hR'⟩ := hm
      have hrun : runN (sstep W i32Test) n x' = .stop o := by rw [← runN_succ_next hx]; exact h
      obtain ⟨hne, d, r, hd, hcode, hb⟩ :=
        stop_in_fx hok n hR' (supported_next hsup hx) hrun
      exact ⟨hne, d, r, hcc'.to_reflTransGen.trans hd, hcode, hb⟩
    | stop o' =>
      have ho : o' = o := by simpa only [runN, hx, Res.stop.injEq] using h
      rw [hx, ho] at hm
      obtain ⟨hne, r, hcode, hb⟩ := hm
      exact ⟨hne, c, r, .refl, hcode, hb⟩

/-- A diverging kernel run gives an infinite `StepFX'` trace. -/
theorem div_in_fx (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : Supported W x) (hdiv : ∀ n, ∃ y, runN (sstep W i32Test) n x = .next y) :
    Silmaril.InfiniteTrace (StepFX' S.P S.host S.fx) c := by
  refine infinite_of_plus (fun c => ∃ x, Rel S W x c ∧ Supported W x ∧
    ∀ n, ∃ y, runN (sstep W i32Test) n x = .next y) (fun c ⟨x, hR, hsup, hdiv⟩ => ?_)
    ⟨x, hR, hsup, hdiv⟩
  have hm : Matched S W c (sstep W i32Test x) := sim_step S hok hR (fine_of_supported hsup)
  obtain ⟨x', hx⟩ : ∃ x', sstep W i32Test x = .next x' := by
    obtain ⟨y, hy⟩ := hdiv 1
    cases hx : sstep W i32Test x with
    | next x' => exact ⟨x', rfl⟩
    | stop o => simp only [runN, hx, reduceCtorEq] at hy
  rw [hx] at hm
  obtain ⟨c', hcc', hR'⟩ := hm
  refine ⟨c', hcc', x', hR', supported_next hsup hx, fun n => ?_⟩
  obtain ⟨y, hy⟩ := hdiv (n + 1)
  exact ⟨y, by rw [← runN_succ_next hx]; exact hy⟩

/-- **Every kernel behaviour is a `StepFX'` behaviour of the encoding.** -/
theorem beh_in_fx (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : Supported W x) :
    ∀ b ∈ beh (sstep W i32Test) x, obsB b ∈ behavioursFX' S.P S.host S.fx c := by
  rintro b (⟨n, o, hrun, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨-, d, r, hd, hcode, hb⟩ := stop_in_fx S hok n hR hsup hrun
    exact Or.inl ⟨d, r, hd, hcode, hb.symm⟩
  · exact Or.inr ⟨rfl, div_in_fx S hok hR hsup hdiv⟩

/-- In the fragment the kernel does not trap. -/
theorem trap_not_beh (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : Supported W x) : Obs.trap ∉ beh (sstep W i32Test) x := by
  rintro (⟨n, o, hrun, ho⟩ | ⟨h, -⟩)
  · obtain ⟨hne, -⟩ := stop_in_fx S hok n hR hsup hrun
    cases o with
    | done vs => exact nomatch ho
    | trap => exact hne rfl
  · exact nomatch h

/-- The root annotation of a call of `f`. -/
def rootAnn (S : Setup H) (f : Nat) : Ann := ⟨.root, .call none, [.core (.call (S.xf f))]⟩

/-- **The initial configurations are related.** -/
theorem rel_init (f : Nat) (args : List Val) :
    Rel S W (sInit f (args.map .val)) (fxInit S f args) := by
  let p : SFrame Val × Ann := (⟨[.call f], args.map .val, none⟩, rootAnn S f)
  have hfr : FrOk S W p := ⟨.call .nil, fun _ h => Kind.noConfusion h⟩
  have hframes : ∀ q ∈ [p], FrOk S W q := by
    intro q hq
    rw [List.mem_singleton.mp hq]
    exact hfr
  have hmain : MainOk S W [p] :=
    ⟨hframes, fun _ h => absurd h List.not_mem_nil, [], p, rfl, rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  refine ⟨rfl, rfl, .nil, [p], rfl, hmain, ?_⟩
  simp only [fxInit, stkCtx, lowsCtx, plug_comp, topCtx_plug, p, rootAnn, kindCtx, CtxV.plug,
    opsF_vals, fvals_vals_map, cvals, adm, List.map_cons, List.map_nil, InstrFX.toAdmin,
    List.append_nil]

end Silmaril.Proofs.Wasm.Models.FXAsyncFX
