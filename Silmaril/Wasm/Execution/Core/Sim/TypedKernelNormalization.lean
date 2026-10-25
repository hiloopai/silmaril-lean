module

public import Silmaril.Wasm.Execution.Core.Sim.TypedNormalization

@[expose] public section

/-! # Typed normalization with kernel-prefix discard

Branches and returns preserve their operand prefix. Traps and thrown exceptions
may discard it when crossing runtime contexts. This additive facts interface
records that distinction; the stronger existing typed facts adapt directly.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics

variable {H : Type}

local notation "noHost" => (fun _ _ _ _ => False)

/-- Typed base normalization that preserves exit prefixes except for trap and
exception kernels, whose administrative rules may discard values. -/
structure TypedKernelFacts (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) : Prop where
  src : ∀ {x y : List Instr}, BI x y → B (expression x) (expression y)
  exit : ∀ {s t : Store H} {f : Frame} {vs us : List Val} {x y k j : List Admin},
    StoreRel F s t → B x y → ContextTyped ⟨t, f, vals vs ++ y⟩ →
    Exit k → vals vs ++ x = vals us ++ k ++ j →
    ∃ (t' : Store H) (ws : List Val) (j' : List Admin),
      Steps P noHost ⟨t, f, vals vs ++ y⟩ ⟨t', f, vals ws ++ k ++ j'⟩ ∧ StoreRel F s t' ∧
        (ws = us ∨ k = [.trap] ∨ ∃ a, k = throwing a)
  values : ∀ {s t : Store H} {f : Frame} {vs us : List Val} {x y : List Admin},
    StoreRel F s t → B x y → ContextTyped ⟨t, f, vals vs ++ y⟩ → x = vals us →
    ∃ t' : Store H, Steps P noHost ⟨t, f, vals vs ++ y⟩ ⟨t', f, vals vs ++ vals us⟩ ∧
      StoreRel F s t'

/-- Every existing exact-prefix typed facts witness remains usable. -/
theorem TypedBaseFacts.toTypedKernelFacts {P : Profile} {F : FuncInst H → FuncInst H → Prop}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    (facts : TypedBaseFacts P F BI B) : TypedKernelFacts P F BI B where
  src := facts.src
  values := facts.values
  exit := by
    intro s t f vs us x y k j stores related typed exit shape
    obtain ⟨t', j', run, stores'⟩ := facts.exit stores related typed exit shape
    exact ⟨t', us, j', run, stores', Or.inl rfl⟩

variable {P : Profile} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

namespace Closure

/-- A values-only source normalizes its related target using the target's
ambient typing witness; the surrounding values remain explicit. -/
theorem kernel_run_vals (hB : TypedKernelFacts P F BI B) :
    ∀ {x y : List Admin}, Segs BI (WithCuts B) x y → x.all Admin.isVal = true →
    ∀ {s t : Store H} {f : Frame} (W : List Val), StoreRel F s t →
    ContextTyped ⟨t, f, vals W ++ y⟩ →
    ∃ t', Steps P noHost ⟨t, f, vals W ++ y⟩ ⟨t', f, vals W ++ x⟩ ∧ StoreRel F s t' := by
  intro x y h
  induction h with
  | nil => intro _ s t f W hst _; exact ⟨t, .refl, hst⟩
  | @cons xs ys xr yr hs _ ih =>
    intro hall s t f W hst htyped
    rw [List.all_append, Bool.and_eq_true] at hall
    obtain ⟨hxs, hxr⟩ := hall
    obtain ⟨u, hu⟩ := exists_vals_of_all hxs
    have htHead : ContextTyped ⟨t, f, vals W ++ ys⟩ := by
      apply ContextTyped.suffix (rest := yr)
      simpa only [List.append_assoc] using htyped
    obtain ⟨t₁, h₁, hst₁⟩ : ∃ t₁, Steps P noHost ⟨t, f, vals W ++ ys⟩
        ⟨t₁, f, vals W ++ xs⟩ ∧ StoreRel F s t₁ := by
      cases hs with
      | @one a b hab =>
        obtain ⟨v, hv⟩ : ∃ v, a.val? = some v := by
          cases ha : a.val? with
          | none => simp [List.all_cons, Admin.isVal, ha] at hxs
          | some v => exact ⟨v, rfl⟩
        obtain rfl := hab.eq_of_val hv
        exact ⟨t, .refl, hst⟩
      | base hb =>
        rcases hb with hb | hcut
        · subst hu
          exact hB.values hst hb htHead rfl
        · exact absurd (exitCut_not_all hcut) (by simp [hxs])
    subst hu
    have h₁' := Steps.append_right h₁ yr
    dsimp only at h₁'
    have htTail : ContextTyped ⟨t₁, f, vals (W ++ u) ++ yr⟩ := by
      have ht := htyped.steps (steps_congr h₁' (by simp) rfl)
      simpa only [vals_append, List.append_assoc] using ht
    obtain ⟨t₂, h₂, hst₂⟩ := ih hxr (f := f) (W ++ u) hst₁ htTail
    refine ⟨t₂, ?_, hst₂⟩
    exact Relation.ReflTransGen.trans (b := ⟨t₁, f, vals (W ++ u) ++ yr⟩)
      (steps_congr h₁' (by simp) (by simp)) (steps_congr h₂ rfl (by simp))

/-- Locate the first computational source segment after normalizing the
target's values-only prefix with its preserved typing witness. -/
theorem kernel_split_active (hB : TypedKernelFacts P F BI B) :
    ∀ {x y : List Admin}, Segs BI (WithCuts B) x y → x.all Admin.isVal = false →
    ∀ {s t : Store H} {f : Frame} (W : List Val), StoreRel F s t →
    ContextTyped ⟨t, f, vals W ++ y⟩ →
    ∃ (V : List Val) (xs ys xr yr : List Admin) (t' : Store H),
      x = vals V ++ xs ++ xr ∧ Seg BI (WithCuts B) xs ys ∧ xs.all Admin.isVal = false ∧
      Segs BI (WithCuts B) xr yr ∧
      Steps P noHost ⟨t, f, vals W ++ y⟩ ⟨t', f, vals W ++ vals V ++ ys ++ yr⟩ ∧
      StoreRel F s t' := by
  intro x y h
  induction h with
  | nil => intro h; simp at h
  | @cons xs ys xr yr hs hr ih =>
    intro hall s t f W hst htyped
    by_cases hxs : xs.all Admin.isVal = true
    · have hxr : xr.all Admin.isVal = false := by
        simpa [List.all_append, hxs] using hall
      have htHead : ContextTyped ⟨t, f, vals W ++ ys⟩ := by
        apply ContextTyped.suffix (rest := yr)
        simpa only [List.append_assoc] using htyped
      obtain ⟨t₁, h₁, hst₁⟩ := kernel_run_vals hB (Segs.single hs) hxs W hst htHead
      obtain ⟨u, rfl⟩ := exists_vals_of_all hxs
      have h₁' := Steps.append_right h₁ yr
      dsimp only at h₁'
      have htTail : ContextTyped ⟨t₁, f, vals (W ++ u) ++ yr⟩ := by
        have ht := htyped.steps (steps_congr h₁' (by simp) rfl)
        simpa only [vals_append, List.append_assoc] using ht
      obtain ⟨V, xs', ys', xr', yr', t₂, rfl, hseg, hact, hr', h₂, hst₂⟩ :=
        ih hxr (f := f) (W ++ u) hst₁ htTail
      refine ⟨u ++ V, xs', ys', xr', yr', t₂, by simp, hseg, hact, hr', ?_, hst₂⟩
      exact Relation.ReflTransGen.trans (b := ⟨t₁, f, vals (W ++ u) ++ yr⟩)
        (steps_congr h₁' (by simp) (by simp)) (steps_congr h₂ rfl (by simp))
    · refine ⟨[], xs, ys, xr, yr, t, by simp, hs, by simpa using hxs, hr, ?_, hst⟩
      exact steps_congr .refl rfl (by simp)

/-- Typed exit transport through the full sequence closure, retaining the
related final store and the actual target frame. -/
theorem kernel_exit_lift (hB : TypedKernelFacts P F BI B) {x y : List Admin}
    (hxy : Segs BI (WithCuts B) x y) {s t : Store H} {f : Frame} (hst : StoreRel F s t)
    (W : List Val) (htyped : ContextTyped ⟨t, f, vals W ++ y⟩) {us : List Val} {k j : List Admin} (hk : Exit k) (hx : x = vals us ++ k ++ j) :
    ∃ (t' : Store H) (us' : List Val) (j' : List Admin),
      Steps P noHost ⟨t, f, vals W ++ y⟩ ⟨t', f, vals us' ++ k ++ j'⟩ ∧
      StoreRel F s t' ∧ (us' = W ++ us ∨ k = [.trap] ∨ ∃ a, k = throwing a) := by
  obtain ⟨pre, e, he, hke⟩ := hk.eq_vals_append
  have hx' : x = vals (us ++ pre) ++ e :: j := by rw [hx, hke]; simp
  have hna : x.all Admin.isVal = false := by
    rw [hx']; simp [List.all_append, Admin.isVal, he]
  obtain ⟨V, xs, ys, xr, yr, t₁, hxV, hseg, hact, hr, hrun, hst₁⟩ :=
    kernel_split_active hB hxy hna W hst htyped
  have htBase : ContextTyped ⟨t₁, f, vals (W ++ V) ++ ys⟩ := by
    have ht := ContextTyped.suffix (rest := yr) (htyped.steps hrun)
    simpa only [vals_append, List.append_assoc] using ht
  obtain ⟨hflat, hctx⟩ := hk.head_flat (BI := BI) hke
  cases hseg with
  | @one a b hab =>
    have ha : a.val? = none := by simpa [Admin.isVal] using hact
    have hj : vals V ++ a :: xr = vals (us ++ pre) ++ e :: j := by rw [← hx', hxV]; simp
    obtain ⟨hV, rfl, rfl⟩ := vals_append_cons_inj ha he hj
    obtain rfl := hab.eq_of_flat hflat hctx
    exact ⟨t₁, W ++ us, yr, steps_congr hrun rfl (by rw [hV, hke]; simp), hst₁, Or.inl rfl⟩
  | base hb =>
    obtain ⟨u₁, e', xs₁, he', rfl⟩ := exists_head_of_not_all hact
    have hj : vals (V ++ u₁) ++ e' :: (xs₁ ++ xr) = vals (us ++ pre) ++ e :: j := by
      rw [← hx', hxV]; simp
    obtain ⟨hVu, he'e, -⟩ := vals_append_cons_inj he' he hj
    subst e'
    rcases hb with hb | ⟨cu, cw, ck, cx, cy, hck, hcx, rfl⟩
    · have heq : vals (W ++ V) ++ (vals u₁ ++ e :: xs₁) = vals (W ++ us) ++ k ++ xs₁ := by
        rw [hke, show vals (W ++ V) ++ (vals u₁ ++ e :: xs₁) =
          vals W ++ vals (V ++ u₁) ++ e :: xs₁ by simp, hVu]
        simp
      obtain ⟨t₂, actual, j', h₂, hst₂, samePrefix⟩ := hB.exit (f := f) hst₁ hb htBase hk heq
      have h₂' := Steps.append_right h₂ yr
      dsimp only at h₂'
      exact ⟨t₂, actual, j' ++ yr, Relation.ReflTransGen.trans hrun
        (steps_congr h₂' (by simp) (by simp)), hst₂, samePrefix⟩
    · obtain ⟨htrap, hthrow⟩ := hk.eq_of_head hke
      rcases hck with rfl | ⟨a', rfl⟩
      · have hc' : vals u₁ ++ e :: xs₁ = vals cu ++ Admin.trap :: cx := by rw [hcx]; simp
        obtain ⟨-, rfl, -⟩ := vals_append_cons_inj he val?_trap hc'
        have hk' := htrap rfl
        refine ⟨t₁, W ++ V ++ cw, cy ++ yr, steps_congr hrun rfl (by rw [hk']; simp), hst₁,
          Or.inr (Or.inl hk')⟩
      · have hc' : vals u₁ ++ e :: xs₁ = vals (cu ++ [.ref (.exn a')]) ++
            Admin.plain .throwRef :: cx := by
          rw [hcx]; simp [vals, throwing, Val.toAdmin]
        obtain ⟨hu₁, rfl, -⟩ := vals_append_cons_inj he val?_throwRef hc'
        obtain ⟨a, rfl, rfl⟩ := hthrow rfl
        have hVu' : us ++ [.ref (.exn a)] = (V ++ cu) ++ [.ref (.exn a')] := by
          rw [← hVu, hu₁]; simp
        have ha' : a = a' := by simpa using (List.append_inj' hVu' rfl).2
        subst ha'
        exact ⟨t₁, W ++ V ++ cw, cy ++ yr, steps_congr hrun rfl (by simp), hst₁,
          Or.inr (Or.inr ⟨a, rfl⟩)⟩

end Closure

/-- Typed value normalization through the recursive runtime-code closure. -/
theorem AdminsRel.kernel_values_lift (hB : TypedKernelFacts P F BI B)
    {s t : Store H} {f : Frame} {vs us : List Val} {x y : List Admin}
    (hst : StoreRel F s t) (related : AdminsRel BI (WithCuts B) x y)
    (typed : ContextTyped ⟨t, f, Core.vals vs ++ y⟩) (values : x = Core.vals us) :
    ∃ t', Steps P noHost ⟨t, f, Core.vals vs ++ y⟩ ⟨t', f, Core.vals vs ++ Core.vals us⟩ ∧ StoreRel F s t' := by
  subst x
  exact Closure.kernel_run_vals hB
    (related.segs (fun _ _ h => Or.inl (hB.src h))) (by simp) vs hst typed

/-- Typed exit transport after an arbitrary value prefix. -/
theorem AdminsRel.kernel_exit_lift (hB : TypedKernelFacts P F BI B)
    {s t : Store H} {f : Frame} {vs us : List Val} {x y k j : List Admin}
    (hst : StoreRel F s t) (related : AdminsRel BI (WithCuts B) x y)
    (typed : ContextTyped ⟨t, f, Core.vals vs ++ y⟩)
    (exit : Exit k) (shape : Core.vals vs ++ x = Core.vals us ++ k ++ j) :
    ∃ (t' : Store H) (ws : List Val) (j' : List Admin),
      Steps P noHost ⟨t, f, Core.vals vs ++ y⟩ ⟨t', f, Core.vals ws ++ k ++ j'⟩ ∧ StoreRel F s t' ∧
      (ws = us ∨ k = [.trap] ∨ ∃ a, k = throwing a) := by
  have hrel := (AdminsRel.vals vs).append related
  obtain ⟨t', ws, j', run, stores, same⟩ := Closure.kernel_exit_lift hB
    (hrel.segs (fun _ _ h => Or.inl (hB.src h))) hst [] (by simpa using typed) exit shape
  exact ⟨t', ws, j', by simpa using run, stores, same⟩

/-- Terminal source code normalizes its typed target to the exact same
result, preserving the complete related store. -/
theorem AdminsRel.kernel_result_lift (hB : TypedKernelFacts P F BI B)
    {s t : Store H} {f : Frame} {x y : List Admin} {r : Result}
    (hst : StoreRel F s t) (related : AdminsRel BI (WithCuts B) x y)
    (typed : ContextTyped ⟨t, f, y⟩) (terminal : x = r.toAdmin) :
    ∃ t', Steps P noHost ⟨t, f, y⟩ ⟨t', f, r.toAdmin⟩ ∧ StoreRel F s t' := by
  cases r with
  | values vs =>
    simpa only [Result.toAdmin, vals_nil', List.nil_append] using
      related.kernel_values_lift hB (vs := []) hst (by simpa using typed) terminal
  | trap =>
    obtain ⟨t', ws, j', run, stores, _⟩ := related.kernel_exit_lift hB (vs := []) (us := [])
      (j := []) hst (by simpa using typed) Exit.trap (by simpa [Result.toAdmin] using terminal)
    refine ⟨t', ?_, stores⟩
    have run' : Steps P noHost ⟨t, f, y⟩ ⟨t', f, Core.vals ws ++ [.trap] ++ j'⟩ := by
      simpa using run
    exact run'.trans (Closure.steps_kernel (Or.inl rfl) ws j')
  | throw a =>
    obtain ⟨t', ws, j', run, stores, _⟩ := related.kernel_exit_lift hB (vs := []) (us := [])
      (j := []) hst (by simpa using typed) (Exit.throw a) (by simpa [Result.toAdmin] using terminal)
    refine ⟨t', ?_, stores⟩
    have run' : Steps P noHost ⟨t, f, y⟩ ⟨t', f, Core.vals ws ++ throwing a ++ j'⟩ := by
      simpa using run
    exact run'.trans (Closure.steps_kernel (Or.inr ⟨a, rfl⟩) ws j')

end Silmaril.Wasm.Execution.Core.Sim
