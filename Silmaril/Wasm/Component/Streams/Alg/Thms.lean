module

public import Silmaril.Wasm.Component.Streams.Alg.Defs
public import Silmaril.Wasm.Component.Algebra.Ops.Thms
public import Silmaril.Wasm.Component.Streams.Laws.Thms
public import Silmaril.Proofs.Wasm.Component.Streams.Alg

/-!
# Stream pipelines in the component algebra: laws

* `stage_equiv`: codes with the same whole output give **equivalent stage components**
  (`CompEquiv batchSem`); `stage_equivF`: in particular `Tr.EquivF`-equivalent transformers.
* **`pipe_congr`** (by `seq_congr`): replacing every stage of a pipeline by an equivalent one gives
  an equivalent pipeline: *the composition of equivalent components is equivalent*.
* `pipe_cons_denU` (by `denU_seq`): the strategy of a pipeline is the composition of the strategies
  of its stages; `pipe_assoc` (by `seq_assoc`): a pipeline of pipelines is the flat pipeline.
* Stage laws from the transformer laws (`Silmaril.Wasm.Component.Streams.Laws`): map fusion
  (`stage_map_map`), `filter` fusion, `map`/`filter` commutation, take after map, `take_take`; and
  the substitution of any stage in any pipeline by a law-equivalent one (`pipe_subst`).
* **Stage fusion** (`stage_fusion`, proved in `Silmaril.Proofs.Wasm.Component.Streams.Alg` by computing
  the strategy of a stage, `denU_stage`): two plugged stages are the stage of the composite code.
  So a pipeline is its fused stage (`pipe_fuse`), and **two pipelines are equivalent as soon as
  their composite transformers have the same whole output** (`pipe_equiv_of_run`), whatever the
  number of components: e.g. `pipe_map_map` (two map components are one), `pipe_map_filter`,
  `pipe_map_take`, `pipe_lines_rechunk` style laws follow from the transformer laws.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Alg

open Silmaril.Games
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Algebra
open Silmaril.Wasm.Component.Streams
open scoped Silmaril.Wasm.Component.Streams.Tr

theorem denU_stage_of_sem {C : CoreSem TCode} {a b : TCode} (h : C.sem a = C.sem b) :
    (stage a).denU C = (stage b).denU C := by
  simp only [stage, Comp.denU, denNodes, Node.den, coreNode, h]
  rfl

/-- **Codes with the same whole output give equivalent stages.** -/
theorem stage_equiv {a b : TCode} (h : a.run = b.run) : CompEquiv batchSem (stage a) (stage b) := by
  refine ⟨⟨rfl, rfl⟩, denU_stage_of_sem ?_⟩
  simp only [batchSem, h]
  rfl

/-- The whole output of the composite code is that of the composite transformer. -/
theorem run_comp_code (a b : TCode) (xs : List Val) : (TCode.comp a b).run xs = b.run (a.run xs) :=
  rfl

theorem sizes_pipe : ∀ as : List TCode,
    (pipe as).imports.length = 1 ∧ (pipe as).exports.length = 1
  | [] => ⟨rfl, rfl⟩
  | [_] => ⟨rfl, rfl⟩
  | _ :: b :: bs => ⟨rfl, by
      show (seq _ (pipe (b :: bs))).exports.length = 1
      rw [(sizes_seq _ _).2]
      exact (sizes_pipe (b :: bs)).2⟩

/-- **Pipelines of equivalent stages are equivalent** (`seq_congr`). -/
theorem pipe_congr : ∀ {as bs : List TCode}, List.Forall₂ (fun a b => a.run = b.run) as bs →
    CompEquiv batchSem (pipe as) (pipe bs)
  | [], [], .nil => CompEquiv.refl _ _
  | [_], [_], .cons h .nil => stage_equiv h
  | _ :: a₂ :: as, _ :: b₂ :: bs, .cons h hs => by
    show CompEquiv batchSem (seq _ (pipe (a₂ :: as))) (seq _ (pipe (b₂ :: bs)))
    exact seq_congr (stage_equiv h) (pipe_congr hs)
  | [_], _ :: _ :: _, .cons _ hs => by cases hs
  | _ :: _ :: _, [_], .cons _ hs => by cases hs

/-- **The strategy of a pipeline is the composition of those of its stages** (`denU_seq`). -/
theorem pipe_cons_denU (C : CoreSem TCode) (a b : TCode) (bs : List TCode) :
    (pipe (a :: b :: bs)).denU C = ((stage a).denU C).comp ((pipe (b :: bs)).denU C) :=
  denU_seq C _ _

/-- A pipeline followed by a pipeline is the concatenated pipeline (`seq_assoc`). -/
theorem pipe_assoc (C : CoreSem TCode) : ∀ (as bs : List TCode), as ≠ [] → bs ≠ [] →
    CompEquiv C (seq (pipe as) (pipe bs)) (pipe (as ++ bs))
  | [], _, h, _ => absurd rfl h
  | [a], b :: bs, _, _ => CompEquiv.refl _ _
  | a :: a₂ :: as, b :: bs, _, _ => by
    show CompEquiv C (seq (seq (stage a) (pipe (a₂ :: as))) (pipe (b :: bs)))
      (seq (stage a) (pipe (a₂ :: as ++ b :: bs)))
    refine (seq_assoc C _ _ _).trans (seq_congr (CompEquiv.refl _ _) ?_)
    exact pipe_assoc C (a₂ :: as) (b :: bs) (by simp) (by simp)
  | _ :: _, [], _, h => absurd rfl h

/-- `Tr.EquivF`-equivalent transformers give equivalent stages. -/
theorem stage_equivF {a b : TCode} (h : ∀ xs, a.run xs = b.run xs) :
    CompEquiv batchSem (stage a) (stage b) :=
  stage_equiv (funext h)

/-! ## Stage laws -/

/-- **Map fusion.** -/
theorem stage_map_map (f g : Val → Val) :
    CompEquiv batchSem (stage (.comp (.map f) (.map g))) (stage (.map (g ∘ f))) :=
  stage_equivF fun xs => by simp [TCode.run, Tr.run_map]

/-- **Filter fusion.** -/
theorem stage_filter_filter (p q : Val → Bool) :
    CompEquiv batchSem (stage (.comp (.filter p) (.filter q))) (stage (.filter fun x => p x && q x)) :=
  stage_equivF fun xs => by simp [TCode.run, Tr.run_filter, List.filter_filter, Bool.and_comm]

/-- **Map then filter is filter (through the map) then map.** -/
theorem stage_map_filter (f : Val → Val) (p : Val → Bool) :
    CompEquiv batchSem (stage (.comp (.map f) (.filter p))) (stage (.comp (.filter (p ∘ f)) (.map f))) :=
  stage_equivF fun xs => by simp [TCode.run, Tr.run_map, Tr.run_filter, List.filter_map]

/-- **Take after map is map after take.** -/
theorem stage_map_take (f : Val → Val) (n : Nat) :
    CompEquiv batchSem (stage (.comp (.map f) (.take n))) (stage (.comp (.take n) (.map f))) :=
  stage_equivF fun xs => by simp [TCode.run, Tr.run_map, Tr.run_take, List.map_take]

/-- **Take of take.** -/
theorem stage_take_take (m n : Nat) :
    CompEquiv batchSem (stage (.comp (.take m) (.take n))) (stage (.take (min m n))) :=
  stage_equivF fun xs => by simp [TCode.run, Tr.run_take, List.take_take, Nat.min_comm]

theorem forall₂_refl : ∀ bs : List TCode, List.Forall₂ (fun a b => a.run = b.run) bs bs
  | [] => .nil
  | _ :: bs => .cons rfl (forall₂_refl bs)

/-- **Substitution in a pipeline**: replacing one stage by a code with the same whole output (e.g.
by one of the laws above) gives an equivalent pipeline. -/
theorem pipe_subst (as bs : List TCode) {a b : TCode} (h : a.run = b.run) :
    CompEquiv batchSem (pipe (as ++ a :: bs)) (pipe (as ++ b :: bs)) := by
  apply pipe_congr
  induction as with
  | nil => exact .cons h (forall₂_refl bs)
  | cons c cs ih => exact .cons rfl ih

/-! ## Fusion -/

/-- **Stage fusion.** -/
theorem stage_fusion (a b : TCode) :
    CompEquiv batchSem (seq (stage a) (stage b)) (stage (.comp a b)) :=
  Silmaril.Proofs.Wasm.Component.Streams.Alg.stage_fusion a b

theorem run_fuse : ∀ (a : TCode) (as : List TCode) (xs : List Val),
    (fuse (a :: as)).run xs = as.foldl (fun ys b => b.run ys) (a.run xs)
  | _, [], _ => rfl
  | a, b :: bs, xs => by
    show (fuse (b :: bs)).run (a.run xs) = _
    rw [run_fuse b bs]
    rfl

/-- **A pipeline is its fused stage.** -/
theorem pipe_fuse : ∀ (as : List TCode), as ≠ [] → CompEquiv batchSem (pipe as) (stage (fuse as))
  | [], h => absurd rfl h
  | [_], _ => CompEquiv.refl _ _
  | a :: b :: bs, _ => by
    show CompEquiv batchSem (seq (stage a) (pipe (b :: bs))) (stage (.comp a (fuse (b :: bs))))
    exact (seq_congr (CompEquiv.refl _ _) (pipe_fuse (b :: bs) (by simp))).trans (stage_fusion _ _)

/-- **Pipelines with the same composite whole output are equivalent**, whatever their numbers of
components. -/
theorem pipe_equiv_of_run {as bs : List TCode} (ha : as ≠ []) (hb : bs ≠ [])
    (h : (fuse as).run = (fuse bs).run) : CompEquiv batchSem (pipe as) (pipe bs) :=
  (pipe_fuse as ha).trans ((stage_equiv h).trans (pipe_fuse bs hb).symm)

/-- **Two map components are one.** -/
theorem pipe_map_map (f g : Val → Val) :
    CompEquiv batchSem (pipe [.map f, .map g]) (pipe [.map (g ∘ f)]) :=
  pipe_equiv_of_run (by simp) (by simp) (funext fun xs => by simp [fuse, TCode.run, Tr.run_map])

/-- **A map component then a filter component is a filter (through the map) then a map.** -/
theorem pipe_map_filter (f : Val → Val) (p : Val → Bool) :
    CompEquiv batchSem (pipe [.map f, .filter p]) (pipe [.filter (p ∘ f), .map f]) :=
  pipe_equiv_of_run (by simp) (by simp)
    (funext fun xs => by simp [fuse, TCode.run, Tr.run_map, Tr.run_filter, List.filter_map])

/-- **Take after map, as components.** -/
theorem pipe_map_take (f : Val → Val) (n : Nat) :
    CompEquiv batchSem (pipe [.map f, .take n]) (pipe [.take n, .map f]) :=
  pipe_equiv_of_run (by simp) (by simp)
    (funext fun xs => by simp [fuse, TCode.run, Tr.run_map, Tr.run_take, List.map_take])

/-- **Three components fused into one.** -/
theorem pipe_filter_filter_map (p q : Val → Bool) (f : Val → Val) :
    CompEquiv batchSem (pipe [.filter p, .filter q, .map f])
      (pipe [.comp (.filter fun x => p x && q x) (.map f)]) :=
  pipe_equiv_of_run (by simp) (by simp) (funext fun xs => by
    simp [fuse, TCode.run, Tr.run_map, Tr.run_filter, List.filter_filter, Bool.and_comm])

end Silmaril.Wasm.Component.Streams.Alg
