module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecWholeNest

/-!
# A whole-step forward theorem for straight-line vector code at `simEnv20V (vecNB P)`

`vecOkA` is the straight-line vector code this module covers: values, and the valid vector
instructions whose redexes `VecSrc` lists (the six operator families, and `extract_lane` with
the sign V2's validation demands). Integer operators must be valid at their shape
(`V2.Instr.immediatesValid`), as must the sign of `extract_lane`.

* **`cover_vec`**: every V2 step from `vecOkA` code is a `Nest20 (VecBase P)` step. No other V2
  rule applies: every other pure, read or store rule needs an instruction outside `vecOkA`, and
  the label and frame contexts need a label or a frame.
* `vecOk_step`: the successor's code is `vecOkA` again.
* **`wholeStepVec`**: every V2 step from a configuration with `vecOkA` code whose image is typed
  in `simEnv20V (vecNB P)` is a `Step` of `simEnv20V (vecNB P)` between the images, and the
  successor keeps both properties. **`wholeRunVec`**: the same for runs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecWhole

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (SStep)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V numShape)
open Silmaril.Wasm.SpecTec.Sim20.VecLane (Packed packShape fshapeOf)
open Silmaril.Wasm.SpecTec.Sim20.VecNum (vecNB)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Nest20)

variable {H : Type} {hn : H → String}

/-! ## The code -/

/-- **The instructions of straight-line vector code**: constants, and the valid covered vector
instructions. -/
def vecOkI : V2.Instr → Bool
  | .intConst _ _ | .floatConst _ _ | .vecConst _ | .refNull _ => true
  | .vecFloatUnOp _ _ | .vecFloatBinOp _ _ | .vecFloatRelOp _ _ => true
  | .vecIntUnOp s op => op.valid s
  | .vecIntBinOp s op => op.valid s
  | .vecIntRelOp s op => op.validShape s
  | .vecExtractLane sh sx _ => sx.isSome == decide (sh.laneWidth < 32)
  | _ => false

/-- **Straight-line vector code**, one administrative instruction. -/
def vecOkA : Admin → Bool
  | .plain i => vecOkI i
  | .refFuncAddr _ | .refHostAddr _ => true
  | _ => false

@[simp] theorem vecOkA_toAdmin (v : Val) : vecOkA v.toAdmin = true := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> rfl

@[simp] theorem all_vecOkA_vals (vs : List Val) : (vals vs).all vecOkA = true := by
  simp [vals]

/-- A valid `extract_lane` is one of the covered redexes. -/
theorem vecSrc_extract {sh : Shape} {sx : Option Signedness} {i : LaneIdx} (c : BitVec 128)
    (h : (sx.isSome == decide (sh.laneWidth < 32)) = true) :
    VecSrc [vconst c, .plain (.vecExtractLane sh sx i)] := by
  rcases sh with (_ | _ | _ | _) | (_ | _) <;> rcases sx with _ | s <;>
    simp [Shape.laneWidth, IntShape.laneWidth, FloatShape.laneWidth] at h
  · exact .extractPack (sz := .i8) (.inl rfl) s c i
  · exact .extractPack (sz := .i16) (.inr rfl) s c i
  · exact .extractNum .i32 c i
  · exact .extractNum .i64 c i
  · exact .extractF .f32 c i
  · exact .extractF .f64 c i

/-! ## Coverage -/

/-- **The pure steps from straight-line vector code start at a covered redex.** -/
theorem vecSrc_of_pureStep {P : Profile} {is is' : List Admin} (hp : PureStep P is is')
    (hok : is.all vecOkA = true) : VecSrc is := by
  cases hp <;> simp_all [vecOkA, vecOkI, vals, Val.toAdmin]
  all_goals first
    | exact .funop _ _ _ | exact .fbinop _ _ _ _ | exact .frelop _ _ _ _
    | exact .iunop _ _ _ | exact .ibinop _ _ _ _ | exact .irelop _ _ _ _
    | exact vecSrc_extract _ (by simpa using hok)

/-- No read step starts in straight-line vector code. -/
theorem not_readStep_vecOk {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') (hok : is.all vecOkA = true) : False := by
  cases hr <;> simp_all [vecOkA, vecOkI, vals, Val.toAdmin]

/-- **Every V2 step from straight-line vector code is a nested covered vector step.** -/
theorem cover_vec {P : Profile} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (hok : c.code.all vecOkA = true) : Nest20 (VecBase P) c c' := by
  induction h with
  | pure hp => exact .base (.mk (vecSrc_of_pureStep hp hok) hp)
  | read hr => exact (not_readStep_vecOk hr hok).elim
  | ctxtInstrs _ hne ih =>
    simp only [List.all_append, Bool.and_eq_true] at hok
    exact .ctx (ih hok.1.2) hne
  | ctxtLabel => simp [vecOkA] at hok
  | ctxtFrame => simp [vecOkA] at hok
  | _ => simp_all [vecOkA, vecOkI, vals, Val.toAdmin]

/-! ## The code stays straight-line -/

/-- A covered redex steps to one value. -/
theorem val_of_vecSrc {P : Profile} {is is' : List Admin} (hs : VecSrc is)
    (hp : PureStep P is is') : ∃ v : Val, is' = [v.toAdmin] := by
  cases hs with
  | funop =>
    obtain ⟨r, -, rfl⟩ := VecLane.pureStep_vecFloatUnOp_inv hp
    exact ⟨.vec r, rfl⟩
  | fbinop =>
    obtain ⟨r, -, rfl⟩ := VecLane.pureStep_vecFloatBinOp_inv hp
    exact ⟨.vec r, rfl⟩
  | frelop => exact ⟨.vec _, VecLane.pureStep_vecFloatRelOp_inv hp⟩
  | iunop =>
    obtain ⟨r, -, rfl⟩ := VecTyp.pureStep_vecIntUnOp_inv hp
    exact ⟨.vec r, rfl⟩
  | ibinop =>
    obtain ⟨r, -, rfl⟩ := VecTyp.pureStep_vecIntBinOp_inv hp
    exact ⟨.vec r, rfl⟩
  | irelop => exact ⟨.vec _, VecTyp.pureStep_vecIntRelOp_inv hp⟩
  | extractNum => exact ⟨_, (VecFix.pureStep_extract_inv hp).2⟩
  | extractPack => exact ⟨_, (VecLane.pureStep_extractSx_inv hp).2⟩
  | extractF => exact ⟨_, (VecFix.pureStep_extract_inv hp).2⟩

/-- **Nested covered steps keep the code straight-line.** -/
theorem vecOk_nest {P : Profile} {c c' : Config H} (h : Nest20 (VecBase P) c c')
    (hok : c.code.all vecOkA = true) : c'.code.all vecOkA = true := by
  induction h with
  | base h =>
    obtain ⟨hs, hp⟩ := h
    obtain ⟨v, rfl⟩ := val_of_vecSrc hs hp
    simp
  | ctx _ _ ih =>
    simp only [List.all_append, Bool.and_eq_true] at hok ⊢
    exact ⟨⟨hok.1.1, ih hok.1.2⟩, hok.2⟩
  | label => simp [vecOkA] at hok
  | frame => simp [vecOkA] at hok

/-! ## The whole step -/

/-- **Every V2 step from straight-line vector code, at a configuration whose image is typed in
`simEnv20V (vecNB P)`, is a `Step` of `simEnv20V (vecNB P)` between the images**; the successor
is straight-line vector code with a typed image. -/
theorem wholeStepVec {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : c.code.all vecOkA = true) (ht : TypV (vecNB P) hn c) :
    c'.code.all vecOkA = true ∧ TypV (vecNB P) hn c' ∧
      SStep (simEnv20V (vecNB P)) (configV hn c) (configV hn c') := by
  have hN := cover_vec h hok
  exact ⟨vecOk_nest hN hok, fwd_vecNest hN ht⟩

/-- **Every V2 run from straight-line vector code with a typed image is a run of
`simEnv20V (vecNB P)` between the images.** -/
theorem wholeRunVec {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') (hok : c.code.all vecOkA = true) (ht : TypV (vecNB P) hn c) :
    c'.code.all vecOkA = true ∧ TypV (vecNB P) hn c' ∧
      Relation.ReflTransGen (SStep (simEnv20V (vecNB P))) (configV hn c) (configV hn c') := by
  induction h with
  | refl => exact ⟨hok, ht, .refl⟩
  | tail _ h₂ ih =>
    obtain ⟨hok₁, ht₁, hr⟩ := ih
    obtain ⟨hok₂, ht₂, hs⟩ := wholeStepVec h₂ hok₁ ht₁
    exact ⟨hok₂, ht₂, hr.tail hs⟩

end Silmaril.Wasm.SpecTec.Sim20.VecWhole
