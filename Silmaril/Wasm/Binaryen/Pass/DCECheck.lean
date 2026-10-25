module

public import Silmaril.Wasm.Binaryen.Pass.DCE

@[expose] public section

/-! # Checked DCE: an executable cut checker

`Pass/DCE.lean` proves the widened DCE sound on bodies satisfying `DceSafeW`, a
proposition. This file gives a Boolean checker `dceSafeWB` with
`dceSafeW_of_check : dceSafeWB es = true → DceSafeW es`, and the per-function checked
pass `dceChecked`: each body is rewritten to `dceL body` when the checker accepts it,
and kept otherwise. `dceChecked_ok` and `dceChecked_sound` are its validity and
export equivalence for every code-parametric host (in particular `closedHost`), as the
executable pipeline (`Exe/Pipeline.lean`, `Exe/PipelineSound.lean`) requires.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation Numerics

/-- Boolean form of `EndsInBot`: the last instruction is stack polymorphic. -/
def endsInBotB (X : List Instr) : Bool :=
  match X.getLast? with
  | some i => botInstr i
  | none => false

theorem endsInBot_of_check {X : List Instr} (h : endsInBotB X = true) : EndsInBot X := by
  unfold endsInBotB at h
  split at h
  · rename_i i hi
    obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hi
    exact ⟨pre, i, rfl, h⟩
  · simp at h

mutual
/-- Boolean checker for `DceSafeWE`. -/
def dceSafeWEB : BExpr → Bool
  | .op _ args => dceSafeWB args &&
      (!BExpr.listBot (dceL args) || endsInBotB (BExpr.lowerList (dceL args)))
  | .block _ b => dceSafeWB b
  | .loop _ b => dceSafeWB b
  | .tryTable _ _ b => dceSafeWB b
  | .if_ _ c t e => dceSafeWB c &&
      (if BExpr.listBot (dceL c) then endsInBotB (BExpr.lowerList (dceL c))
       else dceSafeWB t && dceSafeWB e)
/-- Boolean checker for `DceSafeW`. -/
def dceSafeWB : List BExpr → Bool
  | [] => true
  | e :: es => dceSafeWEB e &&
      (if BExpr.listBot (dceE e) then es.isEmpty || endsInBotB (BExpr.lowerList (dceE e))
       else dceSafeWB es)
end

mutual
theorem dceSafeWE_of_check : ∀ e : BExpr, dceSafeWEB e = true → DceSafeWE e
  | .op _ args, h => by
      simp only [dceSafeWEB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
      refine ⟨dceSafeW_of_check args h.1, fun hb => ?_⟩
      rcases h.2 with h' | h'
      · simp [hb] at h'
      · exact endsInBot_of_check h'
  | .block _ b, h => dceSafeW_of_check b h
  | .loop _ b, h => dceSafeW_of_check b h
  | .tryTable _ _ b, h => dceSafeW_of_check b h
  | .if_ _ c t e, h => by
      simp only [dceSafeWEB, Bool.and_eq_true] at h
      refine ⟨dceSafeW_of_check c h.1, ?_⟩
      have h2 := h.2
      by_cases hb : BExpr.listBot (dceL c) = true
      · simp only [hb, ite_true] at h2 ⊢
        exact endsInBot_of_check h2
      · simp only [hb, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h2 ⊢
        exact ⟨dceSafeW_of_check t h2.1, dceSafeW_of_check e h2.2⟩
theorem dceSafeW_of_check : ∀ es : List BExpr, dceSafeWB es = true → DceSafeW es
  | [], _ => trivial
  | e :: es, h => by
      simp only [dceSafeWB, Bool.and_eq_true] at h
      refine ⟨dceSafeWE_of_check e h.1, ?_⟩
      have h2 := h.2
      by_cases hb : BExpr.listBot (dceE e) = true
      · simp only [hb, ite_true, Bool.or_eq_true, List.isEmpty_iff] at h2 ⊢
        rcases h2 with h' | h'
        · exact Or.inl h'
        · exact Or.inr (endsInBot_of_check h')
      · simp only [hb, Bool.false_eq_true, ite_false] at h2 ⊢
        exact dceSafeW_of_check es h2
end

/-- DCE on one body, run only where the checker accepts it. -/
def dceBodyChecked (b : List BExpr) : List BExpr := if dceSafeWB b then dceL b else b

/-- **Checked DCE on modules**: per function, DCE where `dceSafeWB` accepts. -/
def dceChecked (m : BModule) : BModule := m.mapBodies dceBodyChecked

/-- Checked DCE preserves module validity. -/
theorem dceChecked_ok {m : BModule} (hm : m.Ok) : (dceChecked m).Ok :=
  BodyTransform.ok_of_rel hm rfl (by simp [dceChecked, BModule.mapBodies]) fun i hi _ => by
    simp only [dceChecked, BModule.mapBodies, List.getElem_map]
    refine ⟨rfl, rfl, fun C ts hC hb => ?_⟩
    simp only [dceBodyChecked]
    split
    · next hc => exact dce_typed_body hC (dceSafeW_of_check _ hc) hb
    · exact hb

/-- **Checked DCE is export-equivalent**, for every code-parametric host. -/
theorem dceChecked_sound {P : Profile} {m : BModule} (hm : m.Ok)
    {H : Type} (host : HostSemantics H) (hhost : Sim.HostParametric host) :
    ExportEquiv (· = ·) P host (dceChecked m).lower m.lower :=
  BodyTransform.mapBodies_exportEquivH (Q := HostsP) hm
    (fun f _ _ _ hC hb => by
      simp only [dceBodyChecked]
      split
      · next hc => exact dce_sound_body hC (dceSafeW_of_check _ hc) hb
      · exact ⟨SeqRefinesH.refl (fun _ => rfl) hb,
          SeqRefinesH.refl (R := fun b b' => b' = b) (fun _ => rfl) hb⟩)
    host hhost

/-- Checked DCE under the closed host, at every host-state type. -/
theorem dceChecked_sound_closed {P : Profile} {m : BModule} (hm : m.Ok) {H : Type} :
    ExportEquiv (· = ·) P (closedHost (H := H)) (dceChecked m).lower m.lower :=
  dceChecked_sound hm closedHost closedHost_codeParametric

end Silmaril.Wasm.Binaryen

#print axioms Silmaril.Wasm.Binaryen.dceChecked_ok
#print axioms Silmaril.Wasm.Binaryen.dceChecked_sound
