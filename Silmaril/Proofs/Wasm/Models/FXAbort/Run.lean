module

public import Silmaril.Wasm.Models.FXAbort.Defs
public import Silmaril.Wasm.Models.FXV.Thms

/-!
# The abortive fragment: both sides reach the join

* **`src_runs`** (`StepFX'`): `suspend` captures the empty context and branches with the
  continuation (`suspend`, then `brLabelZero` with the continuation among the values, which
  `StepFX` cannot do), and the handler code drops it (`dropCont`). The source reaches
  `abortJoin W ks` with the same Core store and one more (dead) continuation.
* **`tgt_runs`** (Core): `throw` allocates the exception `⟨ta, W⟩`, the handler catches it and
  branches to the label with the payload. The target reaches `abortJoin W ks` with the store
  `s.addExn ⟨ta, W⟩`.
* `src_behaviours_sup`, `tgt_behaviours_sup`: hence each side has the Core behaviours of the
  join, the source at `s` (no FX functions) and the target at `s.addExn ⟨ta, W⟩`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAbort

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAbort
open Silmaril.Proofs.Wasm.Models.FXLower (ofCoreK)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

theorem toAdmin_core_map (ks : List Instr) :
    (ks.map InstrFX.core).map InstrFX.toAdmin = (expression ks).map AdminFX.core := by
  simp only [expression, List.map_map]
  rfl

theorem toAdmin_comp_core :
    (InstrFX.toAdmin ∘ InstrFX.core) = (AdminFX.core ∘ Admin.plain) := funext fun _ => rfl

/-- The continuation store after the suspension. -/
def kAbort (K : List (Option ContFX)) : List (Option ContFX) := K ++ [some ⟨CtxV.hole.plug⟩]

/-- `suspend` branches to the label with the continuation. -/
theorem src_suspend {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    StepFX' P host fx ⟨s, K, f, abortSrc hs W x ks⟩
      ⟨s, kAbort K, f, [.label (W.length + 1) (.core .drop :: ks.map .core)
        (fvals (liftV W ++ [.cont K.length]) ++ [.core (.plain (.br l))])]⟩ := by
  have h := StepFX'.ctxLabel (P := P) (host := host) (fx := fx) (n := W.length + 1)
    (k := .core .drop :: ks.map .core)
    (StepFX'.suspend (s := s) (K := K) (f := f) (hs := hs) (E := .hole) (vs := liftV W)
      (x := x) ht (by simp [CtxV.Handles]) hc)
  simpa [CtxV.plug, abortSrc, kAbort, FVal.toAdmin] using h

/-- The branch carries the continuation out of the label. -/
theorem src_branch {s : Store H} {K : List (Option ContFX)} {f : Frame} {W : List Val}
    {ks : List Instr} {j : Nat} {l : LabelIdx} (hl : l.toNat = 0) :
    StepFX' P host fx ⟨s, K, f, [.label (W.length + 1) (.core .drop :: ks.map .core)
        (fvals (liftV W ++ [.cont j]) ++ [.core (.plain (.br l))])]⟩
      ⟨s, K, f, cvals W ++ [.contRef j, .core (.plain .drop)] ++
        (expression ks).map AdminFX.core⟩ := by
  have h := StepFX'.brLabelZero (P := P) (host := host) (fx := fx) (s := s) (K := K) (f := f)
    (n := W.length + 1) (k := .core .drop :: ks.map .core) (vs' := [])
    (vs := liftV W ++ [.cont j]) (rest := []) hl (by simp [liftV])
  simpa [expression, List.map_map, toAdmin_comp_core, InstrFX.toAdmin, FVal.toAdmin] using h

/-- The handler code drops the continuation. -/
theorem src_drop {s : Store H} {K : List (Option ContFX)} {f : Frame} {W : List Val}
    {ks : List Instr} {j : Nat} :
    StepFX' P host fx
      ⟨s, K, f, cvals W ++ [.contRef j, .core (.plain .drop)] ++ (expression ks).map .core⟩
      (ofCoreK K ⟨s, f, abortJoin W ks⟩) := by
  have hj : (ofCoreK K ⟨s, f, abortJoin W ks⟩ : ConfigFX H) =
      ⟨s, K, f, cvals W ++ [] ++ (expression ks).map AdminFX.core⟩ := by
    simp [ofCoreK, abortJoin, cvals]
  rw [hj]
  by_cases hne : W ≠ [] ∨ ks ≠ []
  · rw [← fvals_liftV]
    refine StepFX'.seq StepFX'.dropCont ?_
    rcases hne with hW | hk
    · exact Or.inl (by simpa [liftV] using hW)
    · exact Or.inr (by simpa [expression] using hk)
  · obtain ⟨rfl, rfl⟩ : W = [] ∧ ks = [] := by simpa [not_or] using hne
    exact StepFX'.dropCont

/-- **The source reaches the join** (`StepFX'`), keeping the Core store. -/
theorem src_runs {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    StepsFX' P host fx ⟨s, K, f, abortSrc hs W x ks⟩
      (ofCoreK (kAbort K) ⟨s, f, abortJoin W ks⟩) :=
  ((Relation.ReflTransGen.single (src_suspend ht hc)).tail (src_branch hl)).tail src_drop

/-- The tag index of a resolved tag. -/
theorem tag?_module {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    (ht : s.tag? f x = some (ta, ti)) : f.module.tags[x.toNat]? = some ta := by
  unfold Store.tag? at ht
  cases h : f.module.tags[x.toNat]? with
  | none => simp [h] at ht
  | some a =>
    cases h' : s.tags[a]? with
    | none => simp [h, h'] at ht
    | some t =>
      simp only [h, h', Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at ht
      rw [ht.1]

/-- **The target reaches the join** (Core), with one more exception in the store. -/
theorem tgt_runs {host : HostSemantics H} {s : Store H} {f : Frame} {W : List Val} {x : TagIdx}
    {ks : List Instr} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length) (hl : l.toNat = 0) :
    Steps P host ⟨s, f, abortTgt W x l ks⟩ ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ := by
  have h₁ : Step P host ⟨s, f, abortTgt W x l ks⟩
      ⟨s.addExn ⟨ta, W⟩, f, [.label W.length ks
        [.handler W.length [.catch_ x l] (throwing s.exns.length)]]⟩ :=
    Step.ctxtLabel (Step.ctxtHandler (Step.throw ht he hn))
  have hex : (s.addExn ⟨ta, W⟩).exns[s.exns.length]? = some ⟨ta, W⟩ := by
    simp [Store.addExn]
  have h₂ : Step P host
      ⟨s.addExn ⟨ta, W⟩, f, [.label W.length ks
        [.handler W.length [.catch_ x l] (throwing s.exns.length)]]⟩
      ⟨s.addExn ⟨ta, W⟩, f, [.label W.length ks (vals W ++ [.plain (.br l)])]⟩ :=
    Step.ctxtLabel (Step.throwRefHandlerCatch (cs := []) hex (tag?_module ht))
  have h₃ : Step P host
      ⟨s.addExn ⟨ta, W⟩, f, [.label W.length ks (vals W ++ [.plain (.br l)])]⟩
      ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ := by
    have h := Step.brLabelZero (P := P) (host := host) (s := s.addExn ⟨ta, W⟩) (f := f)
      (n := W.length) (cont := ks) (vs' := []) (vs := W) (rest := []) hl rfl
    simpa [vals, abortJoin] using h
  exact ((Relation.ReflTransGen.single h₁).tail h₂).tail h₃

/-- Behaviours of a successor are behaviours (`StepFX'`). -/
theorem behavioursFX'_of_steps {x y : ConfigFX H} (h : StepsFX' P host fx x y) :
    behavioursFX' P host fx y ⊆ behavioursFX' P host fx x := by
  rintro b (⟨d, r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d, r, h.trans hrun, hd, rfl⟩
  · exact Or.inr ⟨rfl, Silmaril.InfiniteTrace.of_steps h hdiv⟩

/-- Behaviours of a successor are behaviours (Core). -/
theorem behavioursOf_of_steps {c d : Config H} (h : Steps P host c d) :
    behavioursOf P host d ⊆ behavioursOf P host c := by
  rintro b (⟨d', r, hrun, hd, rfl⟩ | ⟨rfl, hdiv⟩)
  · exact Or.inl ⟨d', r, h.trans hrun, hd, rfl⟩
  · exact Or.inr ⟨rfl, Silmaril.InfiniteTrace.of_steps h hdiv⟩

/-- **The source has the join's Core behaviours at `s`** (no FX functions). -/
theorem src_behaviours_sup {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {W : List Val} {x : TagIdx} {ks : List Instr} {ta : Nat} {ti : TagInst}
    {l : LabelIdx} (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    behavioursOf P host ⟨s, f, abortJoin W ks⟩ ⊆
      behavioursFX' P host noFX ⟨s, K, f, abortSrc hs W x ks⟩ := by
  rw [← Silmaril.Wasm.Models.FXV.behavioursFX'_ofCoreK (kAbort K)]
  exact behavioursFX'_of_steps (src_runs ht hc hl)

/-- **The target has the join's Core behaviours at `s.addExn ⟨ta, W⟩`.** -/
theorem tgt_behaviours_sup {s : Store H} {f : Frame} {W : List Val} {x : TagIdx}
    {ks : List Instr} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length) (hl : l.toNat = 0) :
    behavioursOf P host ⟨s.addExn ⟨ta, W⟩, f, abortJoin W ks⟩ ⊆
      behavioursOf P host ⟨s, f, abortTgt W x l ks⟩ :=
  behavioursOf_of_steps (tgt_runs ht he hn hl)

/-- Values return themselves. -/
theorem returns_mem (s : Store H) (f : Frame) (W : List Val) :
    Behaviour.returns W ∈ behavioursOf P host ⟨s, f, abortJoin W []⟩ :=
  Or.inl ⟨⟨s, f, abortJoin W []⟩, .values W, .refl, by simp [abortJoin, expression,
    Result.toAdmin], rfl⟩

/-- **With nothing after the block, both sides return the payload.** -/
theorem abort_returns {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {W : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
    (hn : W.length = ts.length)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) (hl : l.toNat = 0) :
    Behaviour.returns W ∈ behavioursFX' P host noFX ⟨s, K, f, abortSrc hs W x []⟩ ∧
      Behaviour.returns W ∈ behavioursOf P host ⟨s, f, abortTgt W x l []⟩ :=
  ⟨src_behaviours_sup ht hc hl (returns_mem s f W),
    tgt_behaviours_sup ht he hn hl (returns_mem _ f W)⟩

end Silmaril.Proofs.Wasm.Models.FXAbort
