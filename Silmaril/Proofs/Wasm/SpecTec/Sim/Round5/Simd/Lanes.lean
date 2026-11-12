module

public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim.R4Fwd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Refute

/-!
# Round 5: `$lanes_` and `$inv_lanes_` at the concrete builtins

`Prims.builtins` answers `$lanes_` by `Round5.Simd.lanesCall` and `$inv_lanes_` by
`Round5.Simd.invLanesCall`. On images they are Core's `Shape.lanesOf` and `Shape.invLanes`:

* `applies_lanes`: `$lanes_(sh, a)` is `lanesV sh a`;
* `applies_invLanes`: `$inv_lanes_(sh, lanesV sh a)` is `a`;
* `lanesV_injective`, `shapeV_injective`, `vecV_injective`: the decodings are unique.

From them, `extractNum` and `extractPack`, the `$lanes_` fields of family V's `VecAgree`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (bvV natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

variable {H : Type}

/-! ## Injectivity of the encodings -/

/-- `shapeV` is injective. -/
theorem shapeV_injective : Function.Injective Vec.shapeV := by
  intro s t h
  rcases s with s | s <;> rcases t with t | t <;> cases s <;> cases t <;>
    simp_all [Vec.shapeV, Vec.ishV, Vec.fshV, Vec.intLaneV, Vec.floatLaneV, caseNilV, pctV,
      IntShape.lanes, FloatShape.lanes]

/-- `vecV` is injective. -/
theorem vecV_injective : Function.Injective Vec.vecV := by
  intro a b h
  simp only [Vec.vecV, pctV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
    Num.natN.injEq, and_true, true_and] at h
  exact BitVec.eq_of_toNat_eq h

/-- `laneV sh` is injective. -/
theorem laneV_injective (sh : Shape) : Function.Injective (laneV sh) := by
  intro x y h
  rcases sh with s | s
  · simp only [laneV, pctV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
      Num.natN.injEq, and_true, true_and] at h
    exact BitVec.eq_of_toNat_eq h
  · cases s
    · exact Typing.floatV_injective .f32 h
    · exact Typing.floatV_injective .f64 h

/-- **`lanesV sh` is injective**: the lanes of a 128-bit pattern determine it. -/
theorem lanesV_injective (sh : Shape) : Function.Injective (lanesV sh) := by
  intro a b h
  have hm : sh.lanesOf a = sh.lanesOf b :=
    List.map_injective_iff.2 (laneV_injective sh) h
  exact lanesW_injective sh.size hm

/-! ## The two calls -/

/-- `Prims.builtins` answers `$lanes_` by `lanesCall`. -/
theorem call_lanes (P : Profile) (hn : H → String) (host : HostSemantics H) (sv v : Value) :
    (BI P hn host).call "lanes_" [.val sv, .val v] = lanesCall sv v := by
  simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- `Prims.builtins` answers `$inv_lanes_` by `invLanesCall`. -/
theorem call_invLanes (P : Profile) (hn : H → String) (host : HostSemantics H) (sv lv : Value) :
    (BI P hn host).call "inv_lanes_" [.val sv, .val lv] = invLanesCall sv lv := by
  simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- `lanesCall` on images. -/
theorem lanesCall_eq (sh : Shape) (a : V128) :
    lanesCall (Vec.shapeV sh) (Vec.vecV a) = some (.list (lanesV sh a)) := by
  unfold lanesCall
  split
  · next hex =>
    obtain ⟨h₁, h₂⟩ := hex.choose_spec
    rw [← shapeV_injective h₁, ← vecV_injective h₂]
  · next hne => exact absurd ⟨(sh, a), rfl, rfl⟩ hne

/-- The pattern `invLanesCall` chooses is the one whose lanes it was given. -/
theorem invLanesCall_choose (sh : Shape) (a : V128)
    (hex : ∃ p : Shape × V128, Vec.shapeV sh = Vec.shapeV p.1 ∧
      Value.list (lanesV sh a) = .list (lanesV p.1 p.2)) :
    some (Vec.vecV hex.choose.2) = some (Vec.vecV a) := by
  obtain ⟨h₁, h₂⟩ := hex.choose_spec
  have e₁ : sh = hex.choose.1 := shapeV_injective h₁
  generalize hex.choose = p at e₁ h₂
  obtain ⟨sh', a'⟩ := p
  simp only at e₁ h₂ ⊢
  subst e₁
  rw [lanesV_injective sh (Value.list.inj h₂)]

/-- `invLanesCall` on images. -/
theorem invLanesCall_eq (sh : Shape) (a : V128) :
    invLanesCall (Vec.shapeV sh) (.list (lanesV sh a)) = some (Vec.vecV a) := by
  unfold invLanesCall
  split
  · next hex => exact invLanesCall_choose sh a hex
  · next hne => exact absurd ⟨(sh, a), rfl, rfl⟩ hne

/-- **`$lanes_(sh, a)` denotes Core's lanes of `a`**, as SpecTec values. -/
theorem applies_lanes (P : Profile) (hn : H → String) (host : HostSemantics H) (sh : Shape)
    (a : V128) :
    Applies (simEnv (BI P hn host)) "lanes_" [.val (Vec.shapeV sh), .val (Vec.vecV a)]
      (.list (lanesV sh a)) :=
  Prims.applies_of_noClause (findDef_lanes _) ((call_lanes P hn host _ _).trans (lanesCall_eq sh a))

/-- **`$inv_lanes_(sh, lanesV sh a)` denotes `a`.** -/
theorem applies_invLanes (P : Profile) (hn : H → String) (host : HostSemantics H) (sh : Shape)
    (a : V128) :
    Applies (simEnv (BI P hn host)) "inv_lanes_" [.val (Vec.shapeV sh), .val (.list (lanesV sh a))]
      (Vec.vecV a) :=
  Prims.applies_of_noClause (findDef_invLanes _)
    ((call_invLanes P hn host _ _).trans (invLanesCall_eq sh a))

/-! ## Reading one lane -/

/-- The `k`-th element of `lanesV sh a`. -/
theorem getElem?_lanesV (sh : Shape) (a : V128) {k : Nat} (hk : k < sh.lanes) :
    (lanesV sh a)[k]? = some (laneV sh ((sh.lanesOf a).getD k 0)) := by
  have hl : k < (sh.lanesOf a).length := by simpa [Shape.lanesOf] using hk
  simp [lanesV, List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]

/-- At an unpacked shape the lane image is Core's extracted numeral. -/
theorem laneV_eq_numV (sh : Shape) (a : V128) (k : Nat) (hw : 32 ≤ sh.laneWidth) :
    laneV sh ((sh.lanesOf a).getD k 0) = numV ⟨sh.unpacked, vecExtractLane sh none k a⟩ := by
  rcases sh with s | s <;> cases s
  · simp [Shape.laneWidth, IntShape.laneWidth] at hw
  · simp [Shape.laneWidth, IntShape.laneWidth] at hw
  · simp only [vecExtractLane, vextractLane]
    show pctV _ = pctV _
    congr 1
  · simp only [vecExtractLane, vextractLane]
    show pctV _ = pctV _
    congr 1
  · simp only [vecExtractLane, vextractLane]
    show floatV .f32 _ = floatV .f32 _
    congr 1
  · simp only [vecExtractLane, vextractLane]
    show floatV .f64 _ = floatV .f64 _
    congr 1

/-- **`VecAgree.extractNum`** at the concrete builtins. -/
theorem extractNum (P : Profile) (hn : H → String) (host : HostSemantics H) :
    ∀ (sh : Shape) (a : V128) (k : Nat), k < sh.lanes → 32 ≤ sh.laneWidth →
      ∃ ls, Applies (simEnv (BI P hn host)) "lanes_" [.val (Vec.shapeV sh), .val (Vec.vecV a)]
        (.list ls) ∧ ls[k]? = some (numV ⟨sh.unpacked, vecExtractLane sh none k a⟩) := by
  intro sh a k hk hw
  refine ⟨lanesV sh a, applies_lanes P hn host sh a, ?_⟩
  rw [getElem?_lanesV sh a hk, laneV_eq_numV sh a k hw]

/-- **`VecAgree.extractPack`** at the concrete builtins. -/
theorem extractPack (P : Profile) (hn : H → String) (host : HostSemantics H) :
    ∀ (sh : IntShape) (sx : Signedness) (a : V128) (k : Nat), k < sh.lanes → sh.laneWidth < 32 →
      ∃ ls l n, Applies (simEnv (BI P hn host)) "lanes_" [.val (Vec.ishV sh), .val (Vec.vecV a)]
          (.list ls) ∧ ls[k]? = some l ∧
        Applies (simEnv (BI P hn host)) "psize" [.val (Vec.intLaneV sh)] n ∧
        Applies (simEnv (BI P hn host)) "extend__"
          [.val n, .val (.num (.natN 32)), .val (Vec.sxV sx), .val l]
          (numV ⟨(Shape.int sh).unpacked, vecExtractLane (.int sh) (some sx) k a⟩) := by
  intro sh sx a k hk hw
  have hF := Prims.floatB_builtins (prof := P) hn host
  have hsx : Vec.sxV sx = Equiv.sxV sx := by cases sx <;> rfl
  rcases sh
  · refine ⟨lanesV (.int .i8x16) a, _, _, applies_lanes P hn host (.int .i8x16) a,
      getElem?_lanesV (.int .i8x16) a hk, R4Fwd.applies_psize .i8, ?_⟩
    rw [hsx]
    have := R4Fwd.applies_extend hF 8 sx (((Shape.int .i8x16).lanesOf a).getD k 0)
    cases sx <;> exact this
  · refine ⟨lanesV (.int .i16x8) a, _, _, applies_lanes P hn host (.int .i16x8) a,
      getElem?_lanesV (.int .i16x8) a hk, R4Fwd.applies_psize .i16, ?_⟩
    rw [hsx]
    have := R4Fwd.applies_extend hF 16 sx (((Shape.int .i16x8).lanesOf a).getD k 0)
    cases sx <;> exact this
  · simp [IntShape.laneWidth] at hw
  · simp [IntShape.laneWidth] at hw

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
