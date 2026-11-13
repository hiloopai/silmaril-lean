module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTreeCover

/-!
# A whole-step forward theorem for vector trees at `simEnv20V (vecNB P)`

* **`fwdBaseV_exit`**: every exit step (`VecTree.ExitBase`) from a configuration typed in
  `simEnv20V B` is a `Step` of `simEnv20V B` between the images, at every `B`, and the successor
  is typed there. The quantifiers come from the typed code: the label's `n` and continuation and
  the frame's `n` and frame from the inversions `VecWhole.typedV_adminLabelV_iff`,
  `typedV_adminFrameV_iff`, the suffix of `trap-vals` as `instr*` by `typedV_instrsV_of_vecOk`.
* `fwdBaseV_tree`: with round 8's vector redexes (`VecWhole.fwdBaseV_vec`), the base steps of a
  vector tree are a base fragment at `vecNB P`.
* **`wholeStepTree`**: every V2 step from a vector tree whose code is `Whole.Plain20` and whose
  image is typed in `simEnv20V (vecNB P)` is a `Step` of that script between the images, and the
  successor keeps all three properties. **`wholeRunTree`**: the same for runs.
* `wholeRunTree_expr`: the entry point from straight-line vector code `expression is`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTree

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (SStep)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB)
open Silmaril.Wasm.SpecTec.Sim20.VecWhole (TypV FwdBaseV typedV_adminsV_single_iff
  typedV_adminsV_append_iff typedV_adminLabelV_iff typedV_adminFrameV_iff)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Nest20 Plain20)

variable {H : Type} {hn : H → String} {B : Builtins}

/-! ## The exits, forward -/

/-- A pure step between typed codes, at a typed state, as a whole step. -/
theorem fwdV_pure {s : Store H} {f : Frame} {is is' : List Admin} (ht : TypV B hn ⟨s, f, is⟩)
    (ht' : Sim.TypedV (simEnv20V B) StepFix.adminsTy (.list (adminsToV is')))
    (hp : Sim.SPure (simEnv20V B) (adminsToV is) (adminsToV is')) :
    TypV B hn ⟨s, f, is'⟩ ∧ SStep (simEnv20V B) (configV hn ⟨s, f, is⟩) (configV hn ⟨s, f, is'⟩) :=
  ⟨⟨ht.state, ht'⟩, VecAgree.sstepV_pure ht.state ht.code ht' hp⟩

theorem fwdV_labelVals {s : Store H} {f : Frame} {n : Nat} {cont : List V2.Instr} {vs : List Val}
    (ht : TypV B hn ⟨s, f, [.label n cont (vals vs)]⟩) :
    TypV B hn ⟨s, f, vals vs⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, [.label n cont (vals vs)]⟩)
        (configV hn ⟨s, f, vals vs⟩) := by
  obtain ⟨hn', hc, hb⟩ := typedV_adminLabelV_iff.1 (typedV_adminsV_single_iff.1 ht.code)
  exact fwdV_pure ht hb (spureV_labelVals hn' hc)

theorem fwdV_frameVals {s : Store H} {f fr : Frame} {vs : List Val}
    (ht : TypV B hn ⟨s, f, [.frame vs.length fr (vals vs)]⟩) :
    TypV B hn ⟨s, f, vals vs⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, [.frame vs.length fr (vals vs)]⟩)
        (configV hn ⟨s, f, vals vs⟩) := by
  obtain ⟨hn', hfr, hb⟩ := typedV_adminFrameV_iff.1 (typedV_adminsV_single_iff.1 ht.code)
  exact fwdV_pure ht hb (spureV_frameVals hn' hfr)

theorem fwdV_trapVals {s : Store H} {f : Frame} {vs : List Val} {is : List V2.Instr}
    (hne : vs ≠ [] ∨ expression is ≠ []) (hok : is.all VecWhole.vecOkI = true)
    (ht : TypV B hn ⟨s, f, vals vs ++ [.trap] ++ expression is⟩) :
    TypV B hn ⟨s, f, [.trap]⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, vals vs ++ [.trap] ++ expression is⟩)
        (configV hn ⟨s, f, [.trap]⟩) := by
  obtain ⟨hvt, hr⟩ := typedV_adminsV_append_iff.1 ht.code
  obtain ⟨-, htr⟩ := typedV_adminsV_append_iff.1 hvt
  exact fwdV_pure ht htr (spureV_trapVals hne (typedV_instrsV_of_vecOk hok hr))

theorem fwdV_trapLabel {s : Store H} {f : Frame} {n : Nat} {cont : List V2.Instr}
    (ht : TypV B hn ⟨s, f, [.label n cont [.trap]]⟩) :
    TypV B hn ⟨s, f, [.trap]⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, [.label n cont [.trap]]⟩)
        (configV hn ⟨s, f, [.trap]⟩) := by
  obtain ⟨hn', hc, hb⟩ := typedV_adminLabelV_iff.1 (typedV_adminsV_single_iff.1 ht.code)
  exact fwdV_pure ht hb (spureV_trapLabel hn' hc)

theorem fwdV_trapFrame {s : Store H} {f fr : Frame} {n : Nat}
    (ht : TypV B hn ⟨s, f, [.frame n fr [.trap]]⟩) :
    TypV B hn ⟨s, f, [.trap]⟩ ∧
      SStep (simEnv20V B) (configV hn ⟨s, f, [.frame n fr [.trap]]⟩)
        (configV hn ⟨s, f, [.trap]⟩) := by
  obtain ⟨hn', hfr, hb⟩ := typedV_adminFrameV_iff.1 (typedV_adminsV_single_iff.1 ht.code)
  exact fwdV_pure ht hb (spureV_trapFrame hn' hfr)

/-- **The exits are a base fragment at every `B`.** -/
theorem fwdBaseV_exit : FwdBaseV B hn (ExitBase (H := H)) := by
  intro c c' h ht
  cases h with
  | labelVals => exact fwdV_labelVals ht
  | frameVals => exact fwdV_frameVals ht
  | trapVals hne hok => exact fwdV_trapVals hne hok ht
  | trapLabel => exact fwdV_trapLabel ht
  | trapFrame => exact fwdV_trapFrame ht

/-- **The base steps of a vector tree are a base fragment at `vecNB P`.** -/
theorem fwdBaseV_tree (P : Profile) : FwdBaseV (vecNB P) hn (TreeBase (H := H) P) := by
  intro c c' h ht
  cases h with
  | vec h => exact VecWhole.fwdBaseV_vec P c c' h ht
  | exit h => exact fwdBaseV_exit c c' h ht

/-! ## The whole step -/

/-- **Every V2 step from a vector tree with `Plain20` code and an image typed in
`simEnv20V (vecNB P)` is a `Step` of `simEnv20V (vecNB P)` between the images**; the successor
keeps the three properties. -/
theorem wholeStepTree {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : VecCode c.code) (hp : Plain20 c.store c.frame c.code)
    (ht : TypV (vecNB P) hn c) :
    VecCode c'.code ∧ Plain20 c'.store c'.frame c'.code ∧ TypV (vecNB P) hn c' ∧
      SStep (simEnv20V (vecNB P)) (configV hn c) (configV hn c') := by
  have hN := cover_tree h hok hp.tail
  exact ⟨vecCode_nest hN hok, Whole.plain20_step h hp, VecWhole.fwd_nestV (fwdBaseV_tree P) hN ht⟩

/-- **Every V2 run from such a configuration is a run of `simEnv20V (vecNB P)` between the
images.** -/
theorem wholeRunTree {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hok : VecCode c.code) (hp : Plain20 c.store c.frame c.code)
    (ht : TypV (vecNB P) hn c) :
    VecCode c'.code ∧ Plain20 c'.store c'.frame c'.code ∧ TypV (vecNB P) hn c' ∧
      Relation.ReflTransGen (SStep (simEnv20V (vecNB P))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact ⟨hok, hp, ht, .refl⟩
  | tail _ h₂ ih =>
    obtain ⟨hok₁, hp₁, ht₁, hr⟩ := ih
    obtain ⟨hok₂, hp₂, ht₂, hs⟩ := wholeStepTree h₂ hok₁ hp₁ ht₁
    exact ⟨hok₂, hp₂, ht₂, hr.tail hs⟩

/-- **The entry point**: a run from straight-line vector code `expression is` with a typed
image. -/
theorem wholeRunTree_expr {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {is : List V2.Instr} {c' : Config H} (h : Steps P host ⟨s, f, expression is⟩ c')
    (hok : is.all VecWhole.vecOkI = true) (ht : TypV (vecNB P) hn ⟨s, f, expression is⟩) :
    VecCode c'.code ∧ TypV (vecNB P) hn c' ∧
      Relation.ReflTransGen (SStep (simEnv20V (vecNB P)))
        (configV hn ⟨s, f, expression is⟩) (configV hn c') := by
  obtain ⟨h₁, -, h₃, h₄⟩ :=
    wholeRunTree h (vecCode_expression.2 hok) (Whole.plain20_expression is) ht
  exact ⟨h₁, h₃, h₄⟩

end Silmaril.Wasm.SpecTec.Sim20.VecTree
