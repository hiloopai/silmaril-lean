module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeBase

/-!
# Nesting at `simEnv20V`: the vector redexes under every evaluation context

Round 6's `Whole.fwd_nest20` closes a base fragment under V2's three evaluation contexts in
`simEnv20S`. This is the same argument in the corrected vector script `simEnv20V B`, with the
invariant `TypV B hn` (state and code typed there):

* `FwdBaseV B hn R`: every `R` step from a `TypV` configuration is a `Step` of `simEnv20V B`
  between the images, with a `TypV` successor. It is closed under union (`FwdBaseV.or`), so
  further base fragments proved at `simEnv20V` plug in.
* **`fwd_nestV`**: from `FwdBaseV`, every `Whole.Nest20 R` step (any number of `ctxt-instrs`,
  `ctxt-label` and `ctxt-frame` around an `R` step) from a `TypV` configuration is a `Step` of
  `simEnv20V B`, and the successor is `TypV`. Subject reduction is carried through each context
  by the inversions of `VecWholeCtx`.
* **`fwd_vecNest`**: at `vecNB P`, for the covered vector redexes (`VecBase P`).
  `runV_vecNest`: the same for runs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (SStep cfgV TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy valsTy)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Nest20)

variable {H : Type} {hn : H → String} {B : Builtins}

/-- **What a base fragment provides at `simEnv20V B`.** -/
def FwdBaseV (B : Builtins) (hn : H → String) (R : Config H → Config H → Prop) : Prop :=
  ∀ c c', R c c' → TypV B hn c →
    TypV B hn c' ∧ SStep (simEnv20V B) (configV hn c) (configV hn c')

/-- Base fragments combine. -/
theorem FwdBaseV.or {R₁ R₂ : Config H → Config H → Prop} (h₁ : FwdBaseV B hn R₁)
    (h₂ : FwdBaseV B hn R₂) : FwdBaseV B hn (fun c c' => R₁ c c' ∨ R₂ c c') :=
  fun c c' h ht => h.elim (fun h => h₁ c c' h ht) (fun h => h₂ c c' h ht)

theorem ffT_vals : VecAgree.ffT valsTy := by
  simp [VecAgree.ffT, Sim.Round7.Script.evTyp, Sim.Round7.Script.evArgs, Sim.Round7.Script.evIter,
    ElseAgree.GoodT, ElseAgree.tyEvB, VecAgree.fams]

/-- The value prefix of a context is a typed `val*` of `simEnv20V`. -/
theorem typedV_valsV (vs : List Val) :
    TypedV (simEnv20V B) valsTy (.list (adminsToV (vals vs))) :=
  VecAgree.typedV_TtoV ffT_vals (VecAgree.vOk_adminsToV _) (StoreGood.typedV_valsTy20T vs)

/-- `ctxt-instrs`, one level. -/
theorem fwdV_ctx {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (ht : TypV B hn ⟨s, f, vals vs ++ is ++ rest⟩)
    (ih : TypV B hn ⟨s, f, is⟩ → TypV B hn ⟨s', f', is'⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypV B hn ⟨s', f', vals vs ++ is' ++ rest⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, vals vs ++ is ++ rest⟩)
        (configV hn ⟨s', f', vals vs ++ is' ++ rest⟩) := by
  obtain ⟨hvi, hrest⟩ := typedV_adminsV_append_iff.1 ht.code
  obtain ⟨hvals, his⟩ := typedV_adminsV_append_iff.1 hvi
  obtain ⟨ht', hst⟩ := ih ⟨ht.state, his⟩
  refine ⟨⟨ht'.state, typedV_adminsV_append_iff.2
    ⟨typedV_adminsV_append_iff.2 ⟨hvals, ht'.code⟩, hrest⟩⟩, ?_⟩
  have hne' : adminsToV (vals vs) ≠ [] ∨ adminsToV rest ≠ [] := by
    simpa [Pure.adminsToV_eq_map, vals] using hne
  have h := sstepV_ctxtInstrs ht.state ht'.state (typedV_valsV vs) his ht'.code hrest hne' hst
  simpa only [configV, Pure.adminsToV_append] using h

/-- `ctxt-label`, one level. -/
theorem fwdV_label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List V2.Instr}
    {is is' : List Admin} (ht : TypV B hn ⟨s, f, [.label n cont is]⟩)
    (ih : TypV B hn ⟨s, f, is⟩ → TypV B hn ⟨s', f', is'⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s', f', is'⟩)) :
    TypV B hn ⟨s', f', [.label n cont is']⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, [.label n cont is]⟩)
        (configV hn ⟨s', f', [.label n cont is']⟩) := by
  obtain ⟨hn', hcont, his⟩ :=
    typedV_adminLabelV_iff.1 (typedV_adminsV_single_iff.1 ht.code)
  obtain ⟨ht', hst⟩ := ih ⟨ht.state, his⟩
  refine ⟨⟨ht'.state, typedV_adminsV_single_iff.2
    (typedV_adminLabelV_iff.2 ⟨hn', hcont, ht'.code⟩)⟩, ?_⟩
  have h := sstepV_ctxtLabel ht.state ht'.state hn' hcont his ht'.code hst
  simpa only [configV, adminsToV, adminToV] using h

/-- `ctxt-frame`, one level. -/
theorem fwdV_frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ht : TypV B hn ⟨s, f, [.frame n fi is]⟩)
    (ih : TypV B hn ⟨s, fi, is⟩ → TypV B hn ⟨s', fi', is'⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, fi, is⟩) (configV hn ⟨s', fi', is'⟩)) :
    TypV B hn ⟨s', f, [.frame n fi' is']⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, [.frame n fi is]⟩)
        (configV hn ⟨s', f, [.frame n fi' is']⟩) := by
  obtain ⟨hn', hfi, his⟩ :=
    typedV_adminFrameV_iff.1 (typedV_adminsV_single_iff.1 ht.code)
  obtain ⟨hst, hf⟩ := typedV_stateVV_iff.1 ht.state
  obtain ⟨ht', hstep⟩ := ih ⟨typedV_stateVV_iff.2 ⟨hst, hfi⟩, his⟩
  obtain ⟨hst', hfi'⟩ := typedV_stateVV_iff.1 ht'.state
  refine ⟨⟨typedV_stateVV_iff.2 ⟨hst', hf⟩, typedV_adminsV_single_iff.2
    (typedV_adminFrameV_iff.2 ⟨hn', hfi', ht'.code⟩)⟩, ?_⟩
  have h := sstepV_ctxtFrame hst hst' hf hfi hfi' hn' his ht'.code hstep
  simpa only [configV, stateV, adminsToV, adminToV] using h

/-- **Every nested step of a base fragment, from a configuration typed in `simEnv20V B`, is a
`Step` of `simEnv20V B` between the images**, and the successor is typed there. -/
theorem fwd_nestV {R : Config H → Config H → Prop} (hR : FwdBaseV B hn R) {c c' : Config H}
    (h : Nest20 R c c') (ht : TypV B hn c) :
    TypV B hn c' ∧ SStep (simEnv20V B) (configV hn c) (configV hn c') := by
  induction h with
  | base h => exact hR _ _ h ht
  | ctx _ hne ih => exact fwdV_ctx hne ht ih
  | label _ ih => exact fwdV_label ht ih
  | frame _ ih => exact fwdV_frame ht ih

/-- The covered vector redexes are a base fragment at `vecNB P`. -/
theorem fwdBaseV_vec (P : Profile) : FwdBaseV (vecNB P) hn (VecBase (H := H) P) :=
  fun _ _ h ht => fwd_vecBase h ht

/-- **The covered vector redexes under every evaluation context, forward at `vecNB P`.** -/
theorem fwd_vecNest {P : Profile} {c c' : Config H} (h : Nest20 (VecBase P) c c')
    (ht : TypV (vecNB P) hn c) :
    TypV (vecNB P) hn c' ∧ SStep (simEnv20V (vecNB P)) (configV hn c) (configV hn c') :=
  fwd_nestV (fwdBaseV_vec P) h ht

/-- **Runs of nested vector steps are runs of the corrected script**, between the images. -/
theorem runV_vecNest {P : Profile} {c c' : Config H}
    (h : Relation.ReflTransGen (Nest20 (VecBase P)) c c') (ht : TypV (vecNB P) hn c) :
    TypV (vecNB P) hn c' ∧
      Relation.ReflTransGen (SStep (simEnv20V (vecNB P))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact ⟨ht, .refl⟩
  | tail _ h₂ ih =>
    obtain ⟨ht₁, hr⟩ := ih
    obtain ⟨ht₂, hs⟩ := fwd_vecNest h₂ ht₁
    exact ⟨ht₂, hr.tail hs⟩

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
