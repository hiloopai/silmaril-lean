module

public import Silmaril.Proofs.Wasm.Models.FXBindT.Runs

/-!
# Partial application under `StepFX'` and `StepFXT`: behaviours

**Under `StepFX'`** (continuation values, untyped `cont.bind`), the pass-1 results for `StepFX`
hold unchanged:

* `bind_rot_sound'`, `bind_sound'` (any host, any FX table), from `behavioursFX_incl`;
* `bind_complete'` (no host calls, no FX functions): every behaviour is a Core behaviour of a
  call on `X₁ ++ U₂ ++ X₂` for a split `vs₂ ++ vs₁ = X₁ ++ X₂ ++ U₂`;
* **`bind_eq_rot'`** (arity of `a` matched): exactly the behaviours of the rotations;
* **`bind_ne_target'`**: the intended equality with `tgtCall` still fails.

The last configurations have no continuations, so `behavioursFX'_noK` hands them to `StepFX`.

**Under `StepFXT`** (typed `cont.bind`):

* `bindT_sound` (any host, no FX functions): when `cont.bind $ct $ct'` binds `|vs₁|` values,
  every Core behaviour of the intended target `vs₁ vs₂ ref.func a call_ref` is a behaviour of
  the source;
* `bindT_complete` (no host calls, no FX functions, arity of `a` matched): every behaviour of the
  source is one of the intended target: the typed `cont.bind` keeps only the split `U₂ = vs₁`,
  and `resume` must pass all of `vs₂` (`underHW_short_empty`);
* **`bindT_eq`**: the source's behaviours **are** the target's.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBindT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXBind
open Silmaril.Wasm.Models.FXLower (tgtCall)
open Silmaril.Proofs.Wasm.Models.FXBind (kRes)
open Silmaril.Proofs.Wasm.Models.FXLower (underH underHW behaviours_underHW behaviours_handler_sub
  withVals_tgtCall)
open Silmaril.Proofs.Wasm.Models.FXBind (BindTargets RotTargets bind_resume_sub underHW_short_empty
  firstS firstD firstS_func first_runs first_returns_only)
open Silmaril.Proofs.Wasm.Models.FXVRuns (behavioursFX'_sub_of_succ not_result_of_mem noKs_underHW
  behavioursFX'_noK)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-! ## `StepFX'` -/

/-- **Every rotation is a `StepFX'` behaviour of the source** (any host, any FX table). -/
theorem bind_rot_sound' {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ X₂ U₂ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs')
    (hS : vs₂ ++ vs₁ = X₂ ++ U₂) :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩ ⊆
      behavioursFX' P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  (Silmaril.Wasm.Models.FXBind.bind_rot_sound hf hr hS).trans (behavioursFX_incl _)

/-- **Soundness of the partial-application lowering under `StepFX'`.** -/
theorem bind_sound' {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursOf P (blockFX host fx) ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ ⊆
      behavioursFX' P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ :=
  bind_rot_sound' hf hr rfl

/-- The source is not a result. -/
theorem srcBind_not_result {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {ct ct' : TypeIdx} {hs : List OnClause} {vs₂ vs₁ : List Val} (r : Result) :
    (⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ : ConfigFX H).code ≠ r.toAdmin.map .core :=
  not_result_of_mem (a := .fx (.contNew ct)) (by simp [srcBind])
    (by simp [Silmaril.Proofs.Wasm.Models.FX.isCore]) r

theorem bsrc₁_not_result {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : DefType} {ct ct' : TypeIdx} {hs : List OnClause} {S : List Val} (r : Result) :
    (Silmaril.Proofs.Wasm.Models.FXBind.bsrc₁ s K f a d ct ct' hs S).code ≠
      r.toAdmin.map .core :=
  not_result_of_mem (a := .contRef K.length) (by simp [Silmaril.Proofs.Wasm.Models.FXBind.bsrc₁])
    (by simp [Silmaril.Proofs.Wasm.Models.FX.isCore]) r

theorem bsrc₂_not_result {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : DefType} {ct' : TypeIdx} {hs : List OnClause} {U₁ U₂ : List Val} (r : Result) :
    (Silmaril.Proofs.Wasm.Models.FXBind.bsrc₂ s K f a d ct' hs U₁ U₂).code ≠
      r.toAdmin.map .core :=
  not_result_of_mem (a := .contRef (K.length + 1))
    (by simp [Silmaril.Proofs.Wasm.Models.FXBind.bsrc₂])
    (by simp [Silmaril.Proofs.Wasm.Models.FX.isCore]) r

/-- **Completeness up to the untyped splits under `StepFX'`.** -/
theorem bind_complete' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) :
    behavioursFX' P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ ⊆
      BindTargets (P := P) s f a fi.type (vs₂ ++ vs₁) := by
  refine behavioursFX'_sub_of_succ srcBind_not_result fun y hy => ?_
  rw [bsrc_succ₁' hf hy]
  refine behavioursFX'_sub_of_succ bsrc₁_not_result fun z hz => ?_
  obtain ⟨U₁, U₂, hS, rfl⟩ := bsrc_succ₂' hz
  refine behavioursFX'_sub_of_succ bsrc₂_not_result fun w hw => ?_
  obtain ⟨hs', X₁, X₂, rfl, rfl⟩ := bsrc_succ₃' hw
  rw [behavioursFX'_noK (noKs_underHW _ _ _ _)]
  intro b hb
  refine ⟨X₁, X₂, U₂, by rw [hS], ?_⟩
  have h := behaviours_underHW (P := P) _ hs' X₁ ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩ hb
  rwa [withVals_tgtCall, ← List.append_assoc] at h

/-- **Under `StepFX'` the source has exactly the behaviours of the rotations** (arity
matched). -/
theorem bind_eq_rot' {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : (vs₂ ++ vs₁).length = ps.length)
    (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFX' P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ =
      RotTargets (P := P) s f a fi.type (vs₂ ++ vs₁) := by
  refine Set.Subset.antisymm ?_ ?_
  · refine behavioursFX'_sub_of_succ srcBind_not_result fun y hy => ?_
    rw [bsrc_succ₁' hf hy]
    refine behavioursFX'_sub_of_succ bsrc₁_not_result fun z hz => ?_
    obtain ⟨U₁, U₂, hS, rfl⟩ := bsrc_succ₂' hz
    refine behavioursFX'_sub_of_succ bsrc₂_not_result fun w hw => ?_
    obtain ⟨hs'', X₁, X₂, rfl, rfl⟩ := bsrc_succ₃' hw
    rw [behavioursFX'_noK (noKs_underHW _ _ _ _)]
    exact bind_resume_sub hf he hn hS
  · rw [← Silmaril.Wasm.Models.FXBind.bind_eq_rot (K := K) (ct := ct) (ct' := ct') hf he hn hr]
    exact behavioursFX_incl _

/-- **Refutation under `StepFX'`**: the intended lowering still fails for the untyped
`cont.bind`; the source returns `[x]`, the call `first y x` only `[y]`. -/
theorem bind_ne_target' (o : Silmaril.Wasm.Numerics.GrowKind → Nat → Nat → Nat → Bool)
    {x y : Val} (hxy : x ≠ y) (K : List (Option ContFX)) (f : Frame) (ct ct' : TypeIdx) :
    behavioursFX' (Profile.deterministic o) noHost noFX
        ⟨firstS (H := H), K, f, srcBind 0 ct ct' [] [x] [y]⟩ ≠
      behavioursOf (Profile.deterministic o) noHost
        ⟨firstS (H := H), f, tgtCall 0 firstD ([y] ++ [x])⟩ := by
  intro heq
  have h := bind_rot_sound' (P := Profile.deterministic o) (host := noHost) (fx := noFX)
    (K := K) (f := f) (ct := ct) (ct' := ct') (hs := []) (hs' := []) (vs₂ := [x]) (vs₁ := [y])
    (X₂ := [x, y]) (U₂ := []) (firstS_func (H := H)) rfl rfl
  rw [blockFX_noFX] at h
  have hsrc := h (Or.inl ⟨_, .values [x], first_runs f x y, rfl, rfl⟩)
  rw [heq] at hsrc
  have := first_returns_only o f hsrc
  simp only [List.cons.injEq, and_true] at this
  exact hxy this

/-! ## `StepFXT` -/

/-- Behaviours of a configuration from those of its successors (`StepFXT`). -/
theorem behavioursFXT_sub_of_succ {host : HostSemantics H} {fx : H → Option FuncFX}
    {x : ConfigFX H} {B : Set (Behaviour Val)} (hnr : ∀ r : Result, x.code ≠ r.toAdmin.map .core)
    (h : ∀ y, StepFXT P host fx x y → behavioursFXT P host fx y ⊆ B) :
    behavioursFXT P host fx x ⊆ B := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · rcases Relation.ReflTransGen.cases_head hrun with rfl | ⟨y, hy, hrest⟩
    · exact absurd hd (hnr r)
    · exact h y hy (Or.inl ⟨d, r, hrest, hd, rfl⟩)
  · obtain ⟨y, hy, htr⟩ := hdiv.unfold
    exact h y hy (Or.inr ⟨rfl, htr⟩)

/-- Behaviours after a run are behaviours (`StepFXT`). -/
theorem behavioursFXT_of_steps {host : HostSemantics H} {fx : H → Option FuncFX}
    {x y : ConfigFX H} (h : StepsFXT P host fx x y) :
    behavioursFXT P host fx y ⊆ behavioursFXT P host fx x := by
  rintro b (⟨d, r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, h.trans hrun, hcode, rfl⟩
  · exact Or.inr ⟨rfl, Silmaril.InfiniteTrace.of_steps h hdiv⟩

/-- The typed arity is unique. -/
theorem bindArity_unique {m : ModuleInst} {ct ct' : TypeIdx} {n n' : Nat}
    (h : BindArity m ct ct' n) (h' : BindArity m ct ct' n') : n = n' := by
  obtain ⟨ps, ps', h1, h2, h3⟩ := h
  obtain ⟨qs, qs', g1, g2, g3⟩ := h'
  rw [h1, Option.some.injEq] at g1
  rw [h2, Option.some.injEq] at g2
  subst g1 g2
  omega

/-- **Soundness of the typed lowering** (any host, no FX functions). -/
theorem bindT_sound {host : HostSemantics H} {s : Store H} {K : List (Option ContFX)}
    {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi)
    (hr : hs.mapM (resolve s f) = some hs') (hA : BindArity f.module ct ct' vs₁.length) :
    behavioursOf P host ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ ⊆
      behavioursFXT P host noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ := by
  have h := behaviours_handler_sub (P := P) (host := host) (fx := noFX) (kRes K a fi.type vs₁)
    hs' ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩
  have hk : Silmaril.Proofs.Wasm.Models.FXVRuns.NoKs
      (underH (kRes K a fi.type vs₁) hs' ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩).code :=
    noKs_underHW _ _ [] _
  rw [blockFX_noFX, ← behavioursFXT_noK hk] at h
  exact h.trans (behavioursFXT_of_steps (bsrc_runsT hf hr hA))

/-- After `cont.bind` bound `vs₁`, every run reaches the intended call (arity matched). -/
theorem bindT_resume_sub {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {hs' : List HClause} {vs₂ vs₁ X₁ X₂ : List Val}
    (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : (vs₂ ++ vs₁).length = ps.length) (hX : vs₂ = X₁ ++ X₂) :
    behavioursFXT P noHost noFX
        (underHW (kRes K a fi.type vs₁) hs' X₁ ⟨s, f, tgtCall a fi.type (vs₁ ++ X₂)⟩) ⊆
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ := by
  rw [behavioursFXT_noK (noKs_underHW _ _ _ _)]
  rcases List.eq_nil_or_concat X₁ with rfl | ⟨L, v, rfl⟩
  · rw [hX, List.nil_append]
    exact behaviours_underHW (P := P) _ hs' [] ⟨s, f, tgtCall a fi.type (vs₁ ++ X₂)⟩
  · have hV : (vs₁ ++ X₂).length < ps.length := by
      rw [← hn, hX]
      simp
      omega
    rw [underHW_short_empty hf he hV]
    exact Set.empty_subset _

/-- **Completeness of the typed lowering** (no host calls, no FX functions, arity matched). -/
theorem bindT_complete {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {ct ct' : TypeIdx} {hs : List OnClause}
    {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : (vs₂ ++ vs₁).length = ps.length) (hA : BindArity f.module ct ct' vs₁.length) :
    behavioursFXT P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ ⊆
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ := by
  refine behavioursFXT_sub_of_succ srcBind_not_result fun y hy => ?_
  rw [bsrc_succ₁T hf hy]
  refine behavioursFXT_sub_of_succ bsrc₁_not_result fun z hz => ?_
  obtain ⟨U₁, U₂, hS, hA', rfl⟩ := bsrc_succ₂T hz
  obtain ⟨rfl, rfl⟩ := List.append_inj' hS (bindArity_unique hA hA')
  refine behavioursFXT_sub_of_succ bsrc₂_not_result fun w hw => ?_
  obtain ⟨hs', X₁, X₂, hX, rfl⟩ := bsrc_succ₃T hw
  exact bindT_resume_sub hf he hn hX

/-- **The typed partial-application lowering is correct**: the source's `StepFXT` behaviours
are exactly the Core behaviours of the intended target (no host calls, no FX functions, the
arities of `cont.bind` and of `a` matched). -/
theorem bindT_eq {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {ct ct' : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {vs₂ vs₁ : List Val} (hf : s.funcs[a]? = some fi)
    (he : Expand fi.type (.func ps rs)) (hn : (vs₂ ++ vs₁).length = ps.length)
    (hA : BindArity f.module ct ct' vs₁.length) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFXT P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ =
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type (vs₁ ++ vs₂)⟩ :=
  Set.Subset.antisymm (bindT_complete hf he hn hA) (bindT_sound hf hr hA)

end Silmaril.Proofs.Wasm.Models.FXBindT
