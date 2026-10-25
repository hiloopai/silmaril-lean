module

public import Silmaril.Wasm.Binaryen.UniformWf
public import Silmaril.Wasm.Binaryen.EquivH

@[expose] public section

/-! # Body transformations over a chosen class of hosts

`BodyTransform.mapBodies_exportEquiv` with the host class as a parameter, and with
the per-body equivalence needed only at the initialization-free body types `.plain`
(a function body is validated at `.plain [] ts`, `ExprOk`). The latter matters for
widened DCE, whose cuts preserve typing only at `.plain` types
(`dce_typed_inits_false`).
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

/-- **Replacing bodies** (`replaceBodies`) over the hosts of a class `Q`. -/
theorem replaceBodiesH {Q : HostClass} {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    (hR : ∀ b, R b b) (hRt : ∀ x y z, R x y → R y z → R x z)
    (m : BModule) (D : List Nat) (spec : Nat → List BExpr)
    (h : ∀ g ∈ D, ∃ C it b, m.body? g = some b ∧ SeqRefinesH Q R P C it (spec g) b)
    (hok : ∀ D', D' ⊆ D → (m.replace D' spec).Ok)
    {H : Type} (host : HostSemantics H) (hhost : Q H host) :
    ExportRefines R P host (m.replace D spec).lower m.lower := by
  revert h hok
  induction D with
  | nil =>
    intro _ _
    simpa only [BodyReplacement.replace_nil] using
      (ExportRefines.refl hR m.lower : ExportRefines R P host m.lower m.lower)
  | cons g D ih =>
    intro h hok
    have hd := ih (fun j hj => h j (List.mem_cons_of_mem g hj))
      (fun D' hD' => hok D' (fun j hj => List.mem_cons_of_mem g (hD' hj)))
    by_cases hg : g ∈ D
    · simpa [BodyReplacement.replace_cons_of_mem m hg] using hd
    · obtain ⟨C, it, b, hb, hs⟩ := h g List.mem_cons_self
      have hold : (m.replace D spec).body? g = some b := by
        rw [BodyReplacement.body?_replace m hg, hb]
      have he := BodyReplacement.withBody_self hold
      have hv := hok D (fun j hj => List.mem_cons_of_mem g hj)
      have hv' := hok (g :: D) (fun _ hj => hj)
      rw [BodyReplacement.replace_cons] at hv' ⊢
      have step := hs.2.2 host (m.replace D spec) g .hole hhost
        (by simpa [BCtx.plug] using hv') (by simpa [BCtx.plug, he] using hv)
      have hs' : ExportRefines R P host ((m.replace D spec).withBody g (spec g)).lower
          (m.replace D spec).lower := by simpa [BCtx.plug, he] using step
      exact hs'.trans hRt hd

namespace BodyTransform

/-- **Module equivalence from per-body equivalences at body types**, for the hosts
of `Q`. -/
theorem mapBodies_exportEquivH {Q : HostClass} {P : Profile}
    {T : List BExpr → List BExpr} {m : BModule} (hm : m.Ok)
    (hT : ∀ f ∈ m.funcs, ∀ C ts, C.Wf → SeqOk C f.body (.plain [] ts) →
      SeqEquivH Q (· = ·) P C (.plain [] ts) (T f.body) f.body)
    {H : Type} (host : HostSemantics H) (hhost : Q H host) :
    ExportEquiv (· = ·) P host (m.mapBodies T).lower m.lower := by
  have hs : ∀ g (hg : g < m.funcs.length), (m.body? g).getD [] = m.funcs[g].body := by
    intro g hg
    simp [BModule.body?, hg]
  constructor
  · have key := replaceBodiesH (Q := Q) (R := (· = ·)) (P := P) (fun _ => rfl)
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
      exact (hT _ (List.getElem_mem hg') _ ts hC hb).1
    case hok =>
      intro D' _
      refine ok_of_rel hm rfl (by simp [BModule.replace]) fun i hi _ => ?_
      simp only [BModule.replace, List.getElem_mapIdx]
      split
      · exact ⟨rfl, rfl, fun C ts hC hb => by
          rw [hs i hi]
          exact (hT _ (List.getElem_mem hi) C ts hC hb).1.1⟩
      · exact ⟨rfl, rfl, fun _ _ _ hb => hb⟩
  · have key := replaceBodiesH (Q := Q) (R := fun b b' : Behaviour Val => b' = b)
      (P := P) (fun _ => rfl)
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
        exact (hT _ (List.getElem_mem hg') _ ts hC hb).2
    case hok =>
      intro D' _
      refine ok_of_rel hm rfl (by simp [BModule.replace, BModule.mapBodies]) fun i hi _ => ?_
      simp only [BModule.replace, BModule.mapBodies, List.getElem_mapIdx, List.getElem_map]
      split
      · exact ⟨rfl, rfl, fun C ts _ hb => by rw [hs i hi]; exact hb⟩
      · exact ⟨rfl, rfl, fun C ts hC hb =>
          (hT _ (List.getElem_mem hi) C ts hC hb).1.1⟩

end BodyTransform

end Silmaril.Wasm.Binaryen
