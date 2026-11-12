module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Floats.Common
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Typing.Inj

/-!
# Float track: the primitives on encoded arguments

`floatCall P` reads its arguments back through the decoders `decNum`, `decNumType`, which are
exact on encodings (`decNum_numV`, `decNumType_numTypeV`, by injectivity of the encodings), so on
encoded arguments each primitive returns the profile's results. The enumeration `bitsWhere`
contains exactly the patterns satisfying its predicate (`mem_bitsWhere`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV bvV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

/-! ## Enumerations -/

theorem mem_allBits {n : Nat} (b : BitVec n) : b ∈ allBits n :=
  List.mem_map.2 ⟨b.toNat, List.mem_range.2 b.isLt, by simp⟩

theorem mem_bitsWhere {n : Nat} {R : BitVec n → Prop} {b : BitVec n} :
    b ∈ bitsWhere n R ↔ R b := by
  classical
  simp only [bitsWhere, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_allBits b, h⟩⟩

/-- Membership in an encoded enumeration. -/
theorem mem_map_bitsWhere {n : Nat} {R : BitVec n → Prop} {f : BitVec n → Value} {c : Value} :
    c ∈ (bitsWhere n R).map f ↔ ∃ z, R z ∧ c = f z := by
  simp only [List.mem_map, mem_bitsWhere]
  exact ⟨fun ⟨z, hz, he⟩ => ⟨z, hz, he.symm⟩, fun ⟨z, hz, he⟩ => ⟨z, hz, he.symm⟩⟩

/-! ## Decoders -/

/-- `numV` is injective at each number type. -/
theorem numV_injective (t : NumType) :
    Function.Injective (fun b : BitVec t.width => numV ⟨t, b⟩) := by
  rcases t with i | f
  · intro a b h
    exact BitVec.eq_of_toNat_eq (by simpa [numV, Equiv.Execution.pctV] using h)
  · exact Typing.floatV_injective f

theorem decNum_numV (t : NumType) (b : BitVec t.width) : decNum t (numV ⟨t, b⟩) = some b := by
  have h : ∃ b' : BitVec t.width, numV ⟨t, b'⟩ = numV ⟨t, b⟩ := ⟨b, rfl⟩
  unfold decNum
  split
  · rename_i h'
    exact congrArg some (numV_injective t (Classical.choose_spec h'))
  · exact absurd h ‹_›

theorem decNum_floatV (t : FloatType) (b : BitVec t.width) :
    decNum (.float t) (floatV t b) = some b := decNum_numV (.float t) b

theorem decNum_pctV (t : IntType) (b : BitVec t.width) :
    decNum (.int t) (Equiv.Execution.pctV b.toNat) = some b := decNum_numV (.int t) b

theorem numTypeV_injective : Function.Injective Vec.numTypeV := by
  intro a b h
  rcases a with a | a <;> cases a <;> rcases b with b | b <;> cases b <;>
    first | rfl | exact absurd h (by simp [Vec.numTypeV, Equiv.Execution.caseNilV])

theorem decNumType_numTypeV (t : NumType) : decNumType (Vec.numTypeV t) = some t := by
  have h : ∃ t', Vec.numTypeV t' = Vec.numTypeV t := ⟨t, rfl⟩
  unfold decNumType
  split
  · rename_i h'
    exact congrArg some (numTypeV_injective (Classical.choose_spec h'))
  · exact absurd h ‹_›

theorem floatOfWidth_width (t : FloatType) : floatOfWidth t.width = some t := by cases t <;> rfl

theorem intOfWidth_width (t : IntType) : intOfWidth t.width = some t := by cases t <;> rfl

theorem asSx?_sxV (s : Signedness) : IntNumeric.asSx? (sxV s) = some s := by cases s <;> rfl

/-! ## The primitives on encoded arguments -/

/-- The name of a float unary primitive. -/
def unName : FloatUnOp → IL.Id
  | .abs => "fabs_" | .neg => "fneg_" | .sqrt => "fsqrt_" | .ceil => "fceil_"
  | .floor => "ffloor_" | .trunc => "ftrunc_" | .nearest => "fnearest_"

/-- The name of a float binary primitive. -/
def binName : FloatBinOp → IL.Id
  | .add => "fadd_" | .sub => "fsub_" | .mul => "fmul_" | .div => "fdiv_"
  | .min => "fmin_" | .max => "fmax_" | .copysign => "fcopysign_"

/-- The name of a float comparison primitive. -/
def relName : FloatRelOp → IL.Id
  | .eq => "feq_" | .ne => "fne_" | .lt => "flt_" | .gt => "fgt_" | .le => "fle_" | .ge => "fge_"

/-- The unary results, encoded. -/
noncomputable def unRes (P : Profile) (t : FloatType) (op : FloatUnOp) (x : BitVec t.width) :
    Value := .list ((bitsWhere t.width (floatUnOpP P t op x)).map (floatV t))

/-- The binary results, encoded. -/
noncomputable def binRes (P : Profile) (t : FloatType) (op : FloatBinOp) (x y : BitVec t.width) :
    Value := .list ((bitsWhere t.width (floatBinOpP P t op x y)).map (floatV t))

theorem fUn_floatV (P : Profile) (t : FloatType) (op : FloatUnOp) (x : BitVec t.width) :
    fUn P op t.width (floatV t x) = some (unRes P t op x) := by
  simp only [fUn, floatOfWidth_width, Option.bind_eq_bind, Option.bind_some, decNum_floatV]
  rfl

theorem fBin_floatV (P : Profile) (t : FloatType) (op : FloatBinOp) (x y : BitVec t.width) :
    fBin P op t.width (floatV t x) (floatV t y) = some (binRes P t op x y) := by
  simp only [fBin, floatOfWidth_width, Option.bind_eq_bind, Option.bind_some, decNum_floatV]
  rfl

theorem fRel_floatV (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width) :
    fRel op t.width (floatV t x) (floatV t y) = some (Vec.i32NV (floatRelOp t op x y)) := by
  simp only [fRel, floatOfWidth_width, Option.bind_eq_bind, Option.bind_some, decNum_floatV]
  rfl

theorem floatCall_eq {P : Profile} {x : IL.Id} (hx : x ∈ floatNames) (ws : List ArgV) :
    floatCall P x ws = floatCall' P x ws := by
  simp only [floatCall, hx, ↓reduceIte]

theorem floatCall_un (P : Profile) (t : FloatType) (op : FloatUnOp) (x : BitVec t.width) :
    floatCall P (unName op) [.val (natV t.width), .val (floatV t x)] = some (unRes P t op x) := by
  cases op <;> (rw [floatCall_eq (by simp [floatNames, unName])]; exact fUn_floatV P t _ x)

theorem floatCall_bin (P : Profile) (t : FloatType) (op : FloatBinOp) (x y : BitVec t.width) :
    floatCall P (binName op) [.val (natV t.width), .val (floatV t x), .val (floatV t y)] =
      some (binRes P t op x y) := by
  cases op <;> (rw [floatCall_eq (by simp [floatNames, binName])]; exact fBin_floatV P t _ x y)

theorem floatCall_rel (P : Profile) (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width) :
    floatCall P (relName op) [.val (natV t.width), .val (floatV t x), .val (floatV t y)] =
      some (Vec.i32NV (floatRelOp t op x y)) := by
  cases op <;> (rw [floatCall_eq (by simp [floatNames, relName])]; exact fRel_floatV t _ x y)

end Silmaril.Wasm.SpecTec.Sim.Floats
