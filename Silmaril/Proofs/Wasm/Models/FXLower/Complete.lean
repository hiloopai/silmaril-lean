module

public import Silmaril.Proofs.Wasm.Models.FXLower.Prefix

/-!
# Lowering `resume (cont.new (ref.func a))` to `call_ref`: completeness

At the host `noHost` and without FX functions, every CoreFX behaviour of the source
`vs; ref.func a; cont.new; resume` is a Core behaviour of the target `vs; ref.func a; call_ref`.

The source has more than one run: `resume` is untyped, so it may pass any suffix `W₂` of
`vs = W₁ ++ W₂` to the continuation and leave `W₁` outside its handler frame. Each such run is
`underHW … W₁ (vs₂; ref.func a; call_ref)`, whose behaviours are Core behaviours of
`W₁; W₂; ref.func a; call_ref` (`behaviours_underHW`), which is the target. So no arity check
is needed for the equality.

* `behavioursFX_sub_of_succ`: the behaviours of a configuration that is not a result are
  behaviours of its successors;
* `src_succ₁`, `src_succ₂`: the successors of the source and of its first step;
* **`lower_complete`**: the converse of `lower_sound`;
* **`lower_correct`**: so the source and the target have equal behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Proofs.Wasm.Models.FX (isCore)
open Silmaril.Wasm.SingleThreaded.Det (noHost append_singleton_inj)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **Behaviours through a non-result**: they are behaviours of its successors. -/
theorem behavioursFX_sub_of_succ {host : HostSemantics H} {fx : H → Option FuncFX}
    {x : ConfigFX H} {B : Set (Behaviour Val)}
    (hnr : ∀ r : Result, x.code ≠ r.toAdmin.map .core)
    (h : ∀ y, StepFX P host fx x y → behavioursFX P host fx y ⊆ B) :
    behavioursFX P host fx x ⊆ B := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · rcases Relation.ReflTransGen.cases_head hrun with rfl | ⟨y, hy, hrest⟩
    · exact absurd hd (hnr r)
    · exact h y hy (Or.inl ⟨d, r, hrest, hd, rfl⟩)
  · obtain ⟨y, hy, htr⟩ := hdiv.unfold
    exact h y hy (Or.inr ⟨rfl, htr⟩)

/-- Code with a non-Core instruction after values is not a result. -/
theorem cons_not_result {W : List Val} {e : AdminFX} {T : List AdminFX}
    (he : isCore e = false) (r : Result) : cvals W ++ e :: T ≠ r.toAdmin.map .core :=
  fun h => core_ne_cvals_cons he h.symm

/-- The source after `cont.new`. -/
def src₁ (s : Store H) (K : List (Option ContFX)) (f : Frame) (a : Nat) (d : Validation.DefType)
    (ct : TypeIdx) (hs : List OnClause) (vs : List Val) : ConfigFX H :=
  ⟨s, K ++ [some (contOf a d)], f, cvals vs ++ .contRef K.length :: [.fx (.resume ct hs)]⟩

/-- The source code at its first non-value. -/
theorem srcResume_eq (a : Nat) (ct : TypeIdx) (hs : List OnClause) (vs : List Val) :
    srcResume a ct hs vs = cvals (vs ++ [.ref (.func a)]) ++ .fx (.contNew ct) :: [.fx (.resume ct hs)] := by
  simp only [srcResume, cvals_append, List.append_assoc]
  rfl

/-- **The only successor of the source is `src₁`.** -/
theorem src_succ₁ {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) {y : ConfigFX H}
    (h : StepFX P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ y) :
    y = src₁ s K f a fi.type ct hs vs := by
  obtain ⟨W₀, r, hW, hy⟩ := step_contNew h _ ct _ (srcResume_eq a ct hs vs)
  obtain ⟨rfl, hr⟩ := append_singleton_inj.mp hW
  have hr' : r = .func a := by simpa using hr.symm
  rcases hy with ⟨a', fi', ha, hf', rfl⟩ | ⟨hn, -⟩
  · have ha' : a' = a := by simpa [hr'] using ha.symm
    have hfi : fi' = fi := by rw [ha'] at hf'; exact Option.some.inj (hf'.symm.trans hf)
    rw [ha', hfi]
    rfl
  · exact absurd (hr'.symm.trans hn) (by simp)

/-- The continuation `src₁` resumes. -/
theorem src₁_cont (K : List (Option ContFX)) (a : Nat) (d : Validation.DefType) :
    (K ++ [some (contOf a d)])[K.length]? = some (some (contOf a d)) := by
  simp

/-- **The successors of `src₁`: the target under a handler frame, after any prefix of `vs`.** -/
theorem src_succ₂ {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : Validation.DefType} {ct : TypeIdx} {hs : List OnClause} {vs : List Val}
    {y : ConfigFX H} (h : StepFX P noHost noFX (src₁ s K f a d ct hs vs) y) :
    ∃ hs' W₁ W₂, vs = W₁ ++ W₂ ∧ y = underHW (kAfter K a d) hs' W₁ ⟨s, f, tgtCall a d W₂⟩ := by
  obtain ⟨T', hT, W₁, W₂, rfl, hy⟩ := step_resume h vs K.length ct hs _ (Or.inr rfl) rfl
  have hT' : T' = [] := (List.cons.inj hT).2.symm
  subst hT'
  rcases hy with ⟨C, hs', hk, -, rfl⟩ | ⟨hk, -⟩
  · have hC : C = contOf a d := by
      have h1 := (src₁_cont K a d).symm.trans hk
      simpa using h1.symm
    subst hC
    refine ⟨hs', W₁, W₂, rfl, ?_⟩
    show _ = (⟨s, kAfter K a d, f, cvals W₁ ++ [.handler hs' ((tgtCall a d W₂).map .core)]⟩ :
      ConfigFX H)
    rw [← plug_contOf]
    rfl
  · exact absurd ((src₁_cont K a d).symm.trans hk) (by simp)

/-- `vals W₁` in front of the target is the target on `W₁ ++ W₂`. -/
theorem withVals_tgtCall (W₁ W₂ : List Val) (s : Store H) (f : Frame) (a : Nat)
    (d : Validation.DefType) :
    withVals W₁ (⟨s, f, tgtCall a d W₂⟩ : Config H) = ⟨s, f, tgtCall a d (W₁ ++ W₂)⟩ := by
  simp [withVals, tgtCall]

/-- **Completeness of the lowering** (no host calls, no FX functions): every CoreFX behaviour of
the source is a Core behaviour of the target. -/
theorem lower_complete {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) :
    behavioursFX P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ ⊆
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ := by
  refine behavioursFX_sub_of_succ (fun r => by
    rw [show (⟨s, K, f, srcResume a ct hs vs⟩ : ConfigFX H).code = _ from srcResume_eq a ct hs vs]
    exact cons_not_result rfl r) fun y hy => ?_
  rw [src_succ₁ hf hy]
  refine behavioursFX_sub_of_succ (cons_not_result rfl) fun z hz => ?_
  obtain ⟨hs', W₁, W₂, rfl, rfl⟩ := src_succ₂ hz
  rw [← withVals_tgtCall]
  exact behaviours_underHW _ _ _ _

/-- **Correctness of the lowering** (no host calls, no FX functions): the source and the target
have the same behaviours. -/
theorem lower_correct {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct : TypeIdx} {hs : List OnClause} {hs' : List HClause} {vs : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs') :
    behavioursFX P noHost noFX ⟨s, K, f, srcResume a ct hs vs⟩ =
      behavioursOf P noHost ⟨s, f, tgtCall a fi.type vs⟩ := by
  have h := lower_sound (P := P) (host := noHost) (fx := noFX) (K := K) (ct := ct) (vs := vs) hf hr
  rw [blockFX_noFX] at h
  exact Set.Subset.antisymm (lower_complete hf) h

end Silmaril.Proofs.Wasm.Models.FXLower
