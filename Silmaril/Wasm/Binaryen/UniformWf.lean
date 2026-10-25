module

public import Silmaril.Wasm.Binaryen.InlineTyping
public import Silmaril.Wasm.Binaryen.Uniform

@[expose] public section

/-! # Body transformations at well-formed contexts

Module validity supplies well-formed body contexts. The lemmas originally
used by `CleanupVacuum` apply to any body transformation, including one with
a syntactic precondition on the bodies of the input module.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

namespace BodyTransform

/-- `f'` is `f` with a body typed wherever `f`'s is, in well-formed contexts. -/
def FuncRel (f f' : BFunc) : Prop :=
  f'.type = f.type ∧ f'.locals = f.locals ∧
    ∀ C ts, C.Wf → ExprOk C (BExpr.lowerList f.body) ts → ExprOk C (BExpr.lowerList f'.body) ts

/-- The body context of a function of a well-formed module context is well formed. -/
theorem funcBody_wf {C : Context} (hC : C.Wf) {f : Func} {d : DefType}
    {ps rs : Ty (.list .val)} {lts : List LocalType}
    (hd : C.type? f.type = some d) (he : Expand d (.func ps rs))
    (hl : List.Forall₂ (LocalOk C) f.locals lts) :
    (C.funcBody ps.toList rs.toList lts).Wf := by
  have hps := Expand.func_ok (hC.type hd) he
  refine Context.Wf.funcBody hC hps.1 hps.2 (fun lt hlt => ?_)
  obtain ⟨t, -, hlt'⟩ := ModuleWf.forall₂_mem_right hl lt hlt
  cases hlt' with
  | set h _ => exact h
  | unset h _ => exact h

theorem funcOk_of_rel {C : Context} (hC : C.Wf) {f f' : BFunc} {d : DefType}
    (h : FuncOk C (Declaration.Func.mapBody BExpr.lowerList f) d) (hr : FuncRel f f') :
    FuncOk C (Declaration.Func.mapBody BExpr.lowerList f') d := by
  obtain ⟨ht, hl, hb⟩ := hr
  cases h with
  | mk hd he hl' hb' =>
    have hW := funcBody_wf hC hd he hl'
    refine FuncOk.mk (f := Declaration.Func.mapBody BExpr.lowerList f') ?_ he ?_ (hb _ _ hW hb')
    · simpa [Declaration.Func.mapBody, ht] using hd
    · simpa [Declaration.Func.mapBody, hl] using hl'

theorem lower_eq_of_base {m m' : BModule} (hbase : m'.base = m.base) :
    m'.lower = { m.lower with funcs := m'.lower.funcs } := by
  unfold BModule.lower
  rw [hbase]

/-- Replacing function bodies by bodies typed wherever the old ones are (in
well-formed contexts) preserves module validity. -/
theorem ok_of_rel {m m' : BModule} (hm : m.Ok) (hbase : m'.base = m.base)
    (hlen : m'.funcs.length = m.funcs.length)
    (hrel : ∀ i (h : i < m.funcs.length) (h' : i < m'.funcs.length),
      FuncRel m.funcs[i] m'.funcs[i]) :
    m'.Ok := by
  obtain ⟨t, h⟩ := hm
  obtain ⟨dts, xtI, fdts, C, -, hW, -, -, -, -, hfuncs, hrebuild⟩ :=
    InlineTy.ModuleOk.funcs_part h
  refine ⟨t, ?_⟩
  rw [lower_eq_of_base hbase]
  apply hrebuild
  rw [List.forall₂_iff_get] at hfuncs ⊢
  obtain ⟨hl, hg⟩ := hfuncs
  refine ⟨?_, fun i h₁ h₂ => ?_⟩
  · simpa [BModule.lower, hlen] using hl
  · have h₁' : i < m.funcs.length := by simpa [BModule.lower, hlen] using h₁
    have := hg i (by simpa [BModule.lower] using h₁') h₂
    simp only [BModule.lower, List.get_eq_getElem, List.getElem_map] at this ⊢
    exact funcOk_of_rel hW this (hrel i h₁' (by simpa [hlen] using h₁'))

/-- Every defined body of a valid module is typed in some well-formed context. -/
theorem body_typed {m : BModule} (hm : m.Ok) {g : Nat} (hg : g < m.funcs.length) :
    ∃ C ts, C.Wf ∧ ExprOk C (BExpr.lowerList m.funcs[g].body) ts := by
  obtain ⟨t, h⟩ := hm
  obtain ⟨dts, xtI, fdts, C, -, hW, -, -, -, -, hfuncs, -⟩ := InlineTy.ModuleOk.funcs_part h
  rw [List.forall₂_iff_get] at hfuncs
  obtain ⟨hl, hget⟩ := hfuncs
  have hg' : g < m.lower.funcs.length := by simpa [BModule.lower] using hg
  have := hget g hg' (by rw [← hl]; exact hg')
  simp only [BModule.lower, List.get_eq_getElem, List.getElem_map] at this
  cases this with
  | mk hd he hl' hb => exact ⟨_, _, funcBody_wf hW hd he hl', hb⟩

/-- Restoring the input bodies after transforming them restores the module. -/
theorem replace_restore (m : BModule) (T : List BExpr → List BExpr) :
    (m.mapBodies T).replace (List.range m.funcs.length)
      (fun g => (m.body? g).getD []) = m := by
  obtain ⟨b, fs⟩ := m
  simp only [BModule.replace, BModule.mapBodies, BModule.mk.injEq, true_and]
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [BModule.body?, h₂]

/-- Whole-module lifting needs equivalence only at well-formed contexts and
only for bodies of the input module. In particular a local syntactic guard need
not hold for unrelated sequences or already transformed bodies. -/
theorem mapBodies_exportEquiv {o : GrowKind → Nat → Nat → Nat → Bool}
    {T : List BExpr → List BExpr} {m : BModule} (hm : m.Ok)
    (hT : ∀ f ∈ m.funcs, ∀ C it, C.Wf → SeqOk C f.body it →
      SeqEquiv (· = ·) (Profile.deterministic o) C it (T f.body) f.body)
    {H : Type} (host : HostSemantics H) (hhost : HostRespectsCode host) :
    ExportEquiv (· = ·) (Profile.deterministic o) host (m.mapBodies T).lower m.lower := by
  have hs : ∀ g (hg : g < m.funcs.length), (m.body? g).getD [] = m.funcs[g].body := by
    intro g hg
    simp [BModule.body?, hg]
  constructor
  · have key := replaceBodies (R := (· = ·)) (P := Profile.deterministic o) (fun _ => rfl)
      (fun _ _ _ h h' => h.trans h') m (List.range m.funcs.length)
      (fun g => T ((m.body? g).getD [])) ?h ?hok host hhost
    · rw [BodyReplacement.replace_range] at key
      exact key
    case h =>
      intro g hg
      have hg' := List.mem_range.mp hg
      obtain ⟨C, ts, hC, hb⟩ := body_typed hm hg'
      refine ⟨C, .plain [] ts, m.funcs[g].body, by simp [BModule.body?, hg'], ?_⟩
      rw [hs g hg']
      exact (hT _ (List.getElem_mem hg') _ _ hC hb).1
    case hok =>
      intro D' _
      refine ok_of_rel hm rfl (by simp [BModule.replace]) fun i hi _ => ?_
      simp only [BModule.replace, List.getElem_mapIdx]
      split
      · exact ⟨rfl, rfl, fun C ts hC hb => by
          rw [hs i hi]
          exact (hT _ (List.getElem_mem hi) C (.plain [] ts) hC hb).1.1⟩
      · exact ⟨rfl, rfl, fun _ _ _ hb => hb⟩
  · have key := replaceBodies (R := fun b b' : Behaviour Val => b' = b)
      (P := Profile.deterministic o) (fun _ => rfl)
      (fun _ _ _ h h' => h'.trans h) (m.mapBodies T) (List.range m.funcs.length)
      (fun g => (m.body? g).getD []) ?h ?hok host hhost
    · rw [replace_restore] at key
      exact key
    case h =>
      intro g hg
      have hg' := List.mem_range.mp hg
      obtain ⟨C, ts, hC, hb⟩ := body_typed hm hg'
      refine ⟨C, .plain [] ts, T m.funcs[g].body, ?_, ?_⟩
      · simp [BModule.body?, BModule.mapBodies, hg']
      · rw [hs g hg']
        exact (hT _ (List.getElem_mem hg') _ _ hC hb).2
    case hok =>
      intro D' _
      refine ok_of_rel hm rfl (by simp [BModule.replace, BModule.mapBodies]) fun i hi _ => ?_
      simp only [BModule.replace, BModule.mapBodies, List.getElem_mapIdx, List.getElem_map]
      split
      · exact ⟨rfl, rfl, fun C ts _ hb => by rw [hs i hi]; exact hb⟩
      · exact ⟨rfl, rfl, fun C ts hC hb =>
          (hT _ (List.getElem_mem hi) C (.plain [] ts) hC hb).1.1⟩

end BodyTransform

end Silmaril.Wasm.Binaryen

#print axioms Silmaril.Wasm.Binaryen.BodyTransform.mapBodies_exportEquiv
