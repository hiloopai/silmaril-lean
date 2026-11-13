module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecLaneStep

/-!
# Builtins answering `$lanes_` at float shapes and `$inv_lanes_`

`Whole.storeB P` answers `$lanes_` at the four integer shapes only, and `$inv_lanes_` nowhere.
`vecB P` adds:

* `$lanes_(Fnn X M, c)` at `F32 X 4` and `F64 X 2`: the lanes of `c` as floats (`lanesFV`, with
  round 3's float encoding `Sim.floatV`);
* `$inv_lanes_(sh, lanes)`: the vector whose lanes at `sh` are `lanes`, at every shape whose lanes
  `vecB P` gives (integer shapes through `lanesV20`, float shapes through `lanesFV`). It answers V2's
  `Numerics.invLanes`: the answer at `$lanes_(sh, c)` is `c` (`invLanes_lanes` is the round trip).

**`laneCalls20_vecB`**, **`floatB_vecB`**: `vecB P` still answers the integer lanes, `$ibytes_` and
every float primitive as `storeB P` does. **`vecB_lanesF`**, **`vecB_invLanes`**,
**`vecB_invLanesF`**: the new answers.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecLane

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim20.Whole (shapeV20 lanesV20 jnnV20 storeB LaneCalls20)

/-- The float shape of a float type. -/
def fshapeOf : FloatType → FloatShape
  | .f32 => .f32x4
  | .f64 => .f64x2

/-- The shape `Fnn X M` of a float type. -/
def fshapeV (t : FloatType) : Value := shapeV (.float (fshapeOf t))

/-- The lanes of `c` at the shape of `t`, as floats. -/
def lanesFV (t : FloatType) (c : BitVec 128) : List Value :=
  (Numerics.lanes t.width (128 / t.width) c).map (Sim.floatV t)

open Classical in
/-- `$lanes_(Fnn X M, c)`. -/
noncomputable def lanesFCall20 (ws : List ArgV) : Option Value :=
  if h : ∃ p : FloatType × BitVec 128, ws = [.val (fshapeV p.1), .val (pctV p.2.toNat)] then
    some (.list (lanesFV h.choose.1 h.choose.2))
  else none

open Classical in
/-- `$inv_lanes_(sh, lanes)`, at the shapes and lanes `vecB` gives. -/
noncomputable def invLanesCall20 (ws : List ArgV) : Option Value :=
  if h : ∃ p : PackSize × BitVec 128, ws = [.val (shapeV20 p.1), .val (.list (lanesV20 p.1 p.2))] then
    some (pctV h.choose.2.toNat)
  else if h' : ∃ p : FloatType × BitVec 128,
      ws = [.val (fshapeV p.1), .val (.list (lanesFV p.1 p.2))] then
    some (pctV h'.choose.2.toNat)
  else none

/-- **`storeB P` with `$lanes_` at float shapes and `$inv_lanes_`.** -/
noncomputable def vecB (P : Profile) : Builtins :=
  ⟨fun x ws => if x = "inv_lanes_" then invLanesCall20 ws
    else if x = "lanes_" then (lanesFCall20 ws).or ((storeB P).call x ws)
    else (storeB P).call x ws⟩

/-! ## Injectivity -/

theorem width_mul (sz : PackSize) : sz.width * (128 / sz.width) = 128 := by cases sz <;> rfl

theorem widthF_mul (t : FloatType) : t.width * (128 / t.width) = 128 := by cases t <;> rfl

theorem lanesV20_inj {sz : PackSize} {c c' : BitVec 128} (h : lanesV20 sz c = lanesV20 sz c') :
    c = c' := by
  have hl : Numerics.lanes sz.width (128 / sz.width) c = Numerics.lanes sz.width (128 / sz.width) c' :=
    List.map_injective_iff.2 (fun a b hab => BitVec.eq_of_toNat_eq (Whole.pctV_injective hab)) h
  rw [← Numerics.invLanes_lanes _ _ (width_mul sz) c, hl, Numerics.invLanes_lanes _ _ (width_mul sz)]

theorem lanesFV_inj {t : FloatType} {c c' : BitVec 128} (h : lanesFV t c = lanesFV t c') : c = c' := by
  have hl : Numerics.lanes t.width (128 / t.width) c = Numerics.lanes t.width (128 / t.width) c' :=
    List.map_injective_iff.2 (fun _ _ hab => Sim.Typing.floatV_injective t hab) h
  rw [← Numerics.invLanes_lanes _ _ (widthF_mul t) c, hl, Numerics.invLanes_lanes _ _ (widthF_mul t)]

theorem fshapeV_inj {t t' : FloatType} (h : fshapeV t = fshapeV t') : t = t' := by
  cases t <;> cases t' <;> simp_all [fshapeV, fshapeOf, shapeV, fnnV, caseNilV]

theorem shapeV20_ne_fshapeV (sz : PackSize) (t : FloatType) : shapeV20 sz ≠ fshapeV t := by
  cases sz <;> cases t <;> simp [shapeV20, jnnV20, fshapeV, fshapeOf, shapeV, fnnV, caseNilV]

/-! ## The answers -/

theorem vecB_call_of_ne {P : Profile} {x : IL.Id} (h₁ : x ≠ "inv_lanes_") (h₂ : x ≠ "lanes_")
    (ws : List ArgV) : (vecB P).call x ws = (storeB P).call x ws := by
  simp [vecB, h₁, h₂]

theorem lanesFCall20_int (sz : PackSize) (c : BitVec 128) :
    lanesFCall20 [.val (shapeV20 sz), .val (pctV c.toNat)] = none := by
  have hn : ¬ ∃ p : FloatType × BitVec 128,
      [ArgV.val (shapeV20 sz), .val (pctV c.toNat)] = [.val (fshapeV p.1), .val (pctV p.2.toNat)] := by
    rintro ⟨p, hp⟩
    exact shapeV20_ne_fshapeV sz p.1 (ArgV.val.inj (List.cons.inj hp).1)
  simp only [lanesFCall20, hn, ↓reduceDIte]

/-- **`vecB P` answers the integer lanes and `$ibytes_` as `storeB P`.** -/
theorem laneCalls20_vecB (P : Profile) : LaneCalls20 (vecB P) where
  lanes sz c := by
    simp only [vecB, show ("lanes_" : String) ≠ "inv_lanes_" by decide, ↓reduceIte,
      lanesFCall20_int, Option.none_or]
    exact (Whole.laneCalls20_storeB P).lanes sz c
  ibytes N k := by
    rw [vecB_call_of_ne (by decide) (by decide)]
    exact (Whole.laneCalls20_storeB P).ibytes N k

/-- **`vecB P` answers every float primitive as `P` does.** -/
theorem floatB_vecB (P : Profile) : Sim.Floats.FloatB P (vecB P) := by
  intro x ws v h
  by_cases h₁ : x = "inv_lanes_"
  · subst h₁; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  by_cases h₂ : x = "lanes_"
  · subst h₂; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  rw [vecB_call_of_ne h₁ h₂]
  exact Whole.floatB_storeB P x ws v h

/-- **`$lanes_` at float shapes.** -/
theorem vecB_lanesF (P : Profile) (t : FloatType) (c : BitVec 128) :
    (vecB P).call "lanes_" [.val (fshapeV t), .val (pctV c.toNat)] = some (.list (lanesFV t c)) := by
  have h : ∃ p : FloatType × BitVec 128, [ArgV.val (fshapeV t), .val (pctV c.toNat)] =
      [.val (fshapeV p.1), .val (pctV p.2.toNat)] := ⟨(t, c), rfl⟩
  have e : h.choose = (t, c) := by
    obtain ⟨a, b⟩ := List.cons.inj h.choose_spec
    obtain ⟨b, -⟩ := List.cons.inj b
    exact Prod.ext (fshapeV_inj (ArgV.val.inj a)).symm
      (BitVec.eq_of_toNat_eq (Whole.pctV_injective (ArgV.val.inj b)).symm)
  simp only [vecB, show ("lanes_" : String) ≠ "inv_lanes_" by decide, ↓reduceIte, lanesFCall20, h,
    ↓reduceDIte, e, Option.some_or]

/-- **`$inv_lanes_` at an integer shape is V2's `invLanes`**: it inverts `$lanes_`. -/
theorem vecB_invLanes (P : Profile) (sz : PackSize) (c : BitVec 128) :
    (vecB P).call "inv_lanes_" [.val (shapeV20 sz), .val (.list (lanesV20 sz c))] =
      some (pctV c.toNat) := by
  have h : ∃ p : PackSize × BitVec 128, [ArgV.val (shapeV20 sz), .val (.list (lanesV20 sz c))] =
      [.val (shapeV20 p.1), .val (.list (lanesV20 p.1 p.2))] := ⟨(sz, c), rfl⟩
  have e₁ : h.choose.1 = sz :=
    (Whole.shapeV20_injective (ArgV.val.inj (List.cons.inj h.choose_spec).1)).symm
  have e₂ : h.choose.2 = c := by
    have hb := ArgV.val.inj (List.cons.inj (List.cons.inj h.choose_spec).2).1
    simp only [Value.list.injEq] at hb
    rw [e₁] at hb
    exact (lanesV20_inj hb).symm
  simp only [vecB, ↓reduceIte, invLanesCall20, h, ↓reduceDIte, e₂]

/-- **`$inv_lanes_` at a float shape inverts `$lanes_`.** -/
theorem vecB_invLanesF (P : Profile) (t : FloatType) (c : BitVec 128) :
    (vecB P).call "inv_lanes_" [.val (fshapeV t), .val (.list (lanesFV t c))] =
      some (pctV c.toNat) := by
  have hn : ¬ ∃ p : PackSize × BitVec 128, [ArgV.val (fshapeV t), .val (.list (lanesFV t c))] =
      [.val (shapeV20 p.1), .val (.list (lanesV20 p.1 p.2))] := by
    rintro ⟨p, hp⟩
    exact shapeV20_ne_fshapeV p.1 t (ArgV.val.inj (List.cons.inj hp).1).symm
  have h : ∃ p : FloatType × BitVec 128, [ArgV.val (fshapeV t), .val (.list (lanesFV t c))] =
      [.val (fshapeV p.1), .val (.list (lanesFV p.1 p.2))] := ⟨(t, c), rfl⟩
  have e₁ : h.choose.1 = t := (fshapeV_inj (ArgV.val.inj (List.cons.inj h.choose_spec).1)).symm
  have e₂ : h.choose.2 = c := by
    have hb := ArgV.val.inj (List.cons.inj (List.cons.inj h.choose_spec).2).1
    simp only [Value.list.injEq] at hb
    rw [e₁] at hb
    exact (lanesFV_inj hb).symm
  simp only [vecB, ↓reduceIte, invLanesCall20, hn, h, ↓reduceDIte, e₂]

end Silmaril.Wasm.SpecTec.Sim20.VecLane
