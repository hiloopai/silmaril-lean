module

public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Computable interpreter: the vector family

`vectorStep?` computes the `VectorStep` head step of the single-threaded
(deterministic) profile. Under `Profile.deterministic o` every vector result
relation is the graph of a (partial) function (`Determinism/FamDetVector.lean`):

* float unary / ternary operators are total functions, so their `-trap` rules
  never fire;
* float binary operators are partial (`vbinopFloat … = some r`), and `-trap`
  fires exactly when the function returns `none`;
* extended binary and conversion operators are partial with no trap rule, so the
  interpreter is stuck (`none`) when the function returns `none`.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

namespace Vec

/-- `$vextbinop__` as a partial function. -/
def extBin (P : Profile) (sh₁ sh₂ : IntShape) (op : VecExtBinOp) (a b : V128) : Option V128 :=
  match op with
  | .relaxedDotS => some (vrelaxedDot P.nd P.relaxed a b)
  | op => vextbinop sh₁ sh₂ op a b

theorem extBin_iff {P : Profile} {sh₁ sh₂ : IntShape} {op : VecExtBinOp} {a b r : V128} :
    VecExtBinOpRel P sh₁ sh₂ op a b r ↔ extBin P sh₁ sh₂ op a b = some r := by
  cases op <;> simp [VecExtBinOpRel, extBin, eq_comm]

/-- Deterministic `relaxed_trunc` (`$ND = false`): the saturating truncation. -/
def relaxedTruncDet (sx : Signedness) : FloatShape → V128 → V128
  | .f32x4, a => invLanesW 32 ((FloatShape.f32x4.lanesOf a).map (truncSatFloat .f32 .i32 sx))
  | .f64x2, a => IntShape.i32x4.invLanes
      ((FloatShape.f64x2.lanesOf a).map (truncSatFloat .f64 .i32 sx) ++ [0, 0])

theorem forall₂_graph {α β : Type} {R : α → β → Prop} {g : α → β}
    (hR : ∀ x y, R x y ↔ y = g x) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys ↔ ys = xs.map g
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
    rw [List.forall₂_cons, hR, forall₂_graph hR]; simp

theorem relaxedTrunc_iff {sx : Signedness} {fs : FloatShape} {a r : V128} :
    vrelaxedTruncRel false {} sx fs a r ↔ r = relaxedTruncDet sx fs a := by
  have hR : ∀ t x y, relaxedTrunc false {} t sx x y ↔ y = truncSatFloat t .i32 sx x :=
    fun t x y => relaxedTrunc_false_iff _ t sx x y
  cases fs with
  | f32x4 =>
    unfold vrelaxedTruncRel invLanesSet relaxedTruncDet
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [(forall₂_graph (R := relaxedTrunc false {} .f32 sx) (hR _)).mp hc]
      rfl
    · rintro rfl
      exact ⟨_, (forall₂_graph (R := relaxedTrunc false {} .f32 sx) (hR _)).mpr rfl, rfl⟩
  | f64x2 =>
    unfold vrelaxedTruncRel relaxedTruncDet
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [(forall₂_graph (R := relaxedTrunc false {} .f64 sx) (hR _)).mp hc]
    · rintro rfl
      exact ⟨_, (forall₂_graph (R := relaxedTrunc false {} .f64 sx) (hR _)).mpr rfl, rfl⟩

/-- `$vcvtop__` in the deterministic profile, as a partial function. -/
def cvt (src tgt : Shape) (op : VecConvertOp) (a : V128) : Option V128 :=
  match op with
  | .relaxedTrunc sx _ =>
    match src with
    | .float fs => if tgt = .int .i32x4 then some (relaxedTruncDet sx fs a) else none
    | .int _ => none
  | op => vcvtop op src tgt a

theorem cvt_iff {o : GrowOracle} {src tgt : Shape} {op : VecConvertOp} {a r : V128} :
    VecConvertRel (Profile.deterministic o) src tgt op a r ↔ cvt src tgt op a = some r := by
  cases op with
  | relaxedTrunc sx z =>
    cases src with
    | float fs =>
      simp only [VecConvertRel, cvt, Profile.deterministic]
      rw [relaxedTrunc_iff]
      by_cases ht : tgt = .int .i32x4 <;> simp [ht, eq_comm]
    | int _ => simp [VecConvertRel, cvt]
  | extend => exact Iff.rfl
  | convert => exact Iff.rfl
  | truncSat => exact Iff.rfl
  | demoteZero => exact Iff.rfl
  | promoteLow => exact Iff.rfl

/-- `$vshufflop_` with its partial indexing: `none` on an index `≥ 32`. -/
@[irreducible] def shuffle? (idx : List LaneIdx) (a b : V128) : Option V128 :=
  if ∀ j ∈ idx, j.val < 32 then some (vecShuffle idx a b) else none

theorem shuffle?_eq {idx : List LaneIdx} {a b r : V128} :
    shuffle? idx a b = some r ↔ (∀ j ∈ idx, j.val < 32) ∧ r = vecShuffle idx a b := by
  unfold shuffle?; split <;> simp_all [eq_comm]

theorem shuffle?_of {idx : List LaneIdx} {a b : V128} (h : ∀ j ∈ idx, j.val < 32) :
    shuffle? idx a b = some (vecShuffle idx a b) :=
  shuffle?_eq.mpr ⟨h, rfl⟩

/-- Lane-bound guard of `vextract_lane`/`vreplace_lane` (`$lanes_(sh, c)[i]` is partial). -/
@[irreducible] def inLane? (sh : Shape) (i : LaneIdx) : Option Unit :=
  if i.val < sh.lanes then some () else none

theorem inLane?_eq {sh : Shape} {i : LaneIdx} {u : Unit} :
    inLane? sh i = some u ↔ i.val < sh.lanes := by
  unfold inLane?; split <;> simp_all

theorem inLane?_of_lt {sh : Shape} {i : LaneIdx} (h : i.val < sh.lanes) : inLane? sh i = some () :=
  inLane?_eq.mpr h

/-- The pure vector step on the reversed (top-first) value stack. -/
def pure? (P : Profile) : Instr → List Val → Option (Nat × List Admin)
  | .vecUnOp op, .vec a :: _ => some (1, [vconst (vvunop op a)])
  | .vecBinOp op, .vec b :: .vec a :: _ => some (2, [vconst (vvbinop op a b)])
  | .vecTernOp op, .vec c :: .vec b :: .vec a :: _ => some (3, [vconst (vvternop op a b c)])
  | .vecTestOp op, .vec a :: _ => some (1, [constI32 (vvtestop op a)])
  | .vecIntUnOp sh op, .vec a :: _ => some (1, [vconst (vecIntUnOp sh op a)])
  | .vecFloatUnOp sh op, .vec a :: _ => some (1, [vconst (vunopFloat sh op a)])
  | .vecIntBinOp sh op, .vec b :: .vec a :: _ => some (2, [vconst (vecIntBinOp P sh op a b)])
  | .vecFloatBinOp sh op, .vec b :: .vec a :: _ =>
    match vbinopFloat sh (canonBinOp op) a b with
    | some r => some (2, [vconst r])
    | none => some (2, [.trap])
  | .vecIntTernOp sh op, .vec c :: .vec b :: .vec a :: _ =>
    some (3, [vconst (vecIntTernOp P sh op a b c)])
  | .vecFloatTernOp sh op, .vec c :: .vec b :: .vec a :: _ =>
    some (3, [vconst (sh.invLanes (List.zipWith3 (fmaddCanon sh.floatType op)
      (sh.lanesOf a) (sh.lanesOf b) (sh.lanesOf c)))])
  | .vecAllTrue sh, .vec a :: _ => some (1, [constI32 (vecAllTrue sh a)])
  | .vecIntRelOp sh op, .vec b :: .vec a :: _ => some (2, [vconst (vecIntRelOp sh op a b)])
  | .vecFloatRelOp sh op, .vec b :: .vec a :: _ => some (2, [vconst (vecFloatRelOp sh op a b)])
  | .vecShiftOp sh op, .num ⟨.int .i32, n⟩ :: .vec a :: _ =>
    some (2, [vconst (vecShiftOp sh op a n)])
  | .vecBitmask sh, .vec a :: _ => some (1, [constI32 (vecBitmask sh a)])
  | .vecSwizzle .swizzle, .vec s :: .vec a :: _ => some (2, [vconst (vecSwizzle a s)])
  | .vecSwizzle .relaxedSwizzle, .vec s :: .vec a :: _ =>
    some (2, [vconst (vecRelaxedSwizzle P a s)])
  | .vecShuffle idx, .vec b :: .vec a :: _ =>
    (shuffle? idx a b).map fun r => (2, [vconst r])
  | .vecSplat sh, .num ⟨t, x⟩ :: _ =>
    if h : t = sh.unpacked then some (1, [vconst (vecSplat sh (h ▸ x))]) else none
  | .vecExtractLane sh sx i, .vec a :: _ =>
    (inLane? sh i).map fun _ =>
      (1, [(Val.num ⟨sh.unpacked, vecExtractLane sh sx i.val a⟩).toAdmin])
  | .vecReplaceLane sh i, .num ⟨t, x⟩ :: .vec a :: _ =>
    if h : t = sh.unpacked then
      (inLane? sh i).map fun _ => (2, [vconst (vecReplaceLane sh i.val a (h ▸ x))])
    else none
  | .vecExtUnOp sh₁ sh₂ op, .vec a :: _ => some (1, [vconst (vextunop sh₁ sh₂ op a)])
  | .vecExtBinOp sh₁ sh₂ op, .vec b :: .vec a :: _ =>
    (extBin P sh₁ sh₂ op a b).map fun r => (2, [vconst r])
  | .vecExtTernOp _ _ _, .vec c :: .vec b :: .vec a :: _ =>
    some (3, [vconst (vrelaxedDotAdd P.nd P.relaxed a b c)])
  | .vecNarrow sh₁ sh₂ sx, .vec b :: .vec a :: _ => some (2, [vconst (vnarrow sh₁ sh₂ sx a b)])
  | .vecConvert src tgt op, .vec a :: _ => (cvt src tgt op a).map fun r => (1, [vconst r])
  | _, _ => none

end Vec

/-- The vector-family head step of the single-threaded profile. -/
def vectorStep? (o : GrowOracle) (s : Store H) (f : Frame) (vs : List Val) (e : Admin) :
    Option (Nat × Config H) :=
  match e with
  | .plain i => (Vec.pure? (profile o) i vs.reverse).map fun p => (p.1, ⟨s, f, p.2⟩)
  | _ => none

namespace Vec

theorem pure?_sound {o : GrowOracle} {i : Instr} {rv : List Val} {k : Nat} {out : List Admin}
    (h : pure? (Profile.deterministic o) i rv = some (k, out)) :
    k ≤ rv.length ∧
      VectorStep (Profile.deterministic o) (vals (rv.take k).reverse ++ [.plain i]) out := by
  unfold pure? at h
  split at h
  all_goals (try split at h)
  all_goals (try simp only [Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h)
  all_goals (try obtain ⟨rfl, rfl⟩ := h)
  all_goals (try obtain ⟨r, hr, rfl, rfl⟩ := h)
  all_goals (try subst_vars)
  all_goals refine ⟨by simp, ?_⟩
  all_goals simp only [List.take_succ_cons, List.take_zero, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, vals_cons, vals_nil]
  all_goals first
    | (obtain ⟨hb, rfl⟩ := shuffle?_eq.mp hr; exact .vecShuffle _ _ _ hb)
    | exact .vecFloatBinOpTrap (fun r hr => by rw [VecFloatBinOpRel_det] at hr; simp_all)
    | (constructor <;> (first | rfl | exact extBin_iff.mpr ‹_› | exact cvt_iff.mpr ‹_› | exact VecFloatBinOpRel_det.mpr ‹_› | exact inLane?_eq.mp hr))

theorem pure?_complete {o : GrowOracle} {args : List Val} {e : Admin} {is' : List Admin}
    (h : VectorStep (Profile.deterministic o) (vals args ++ [e]) is') :
    ∃ i, e = .plain i ∧ ∀ q, pure? (Profile.deterministic o) i (args.reverse ++ q) =
      some (args.length, is') := by
  generalize hl : vals args ++ [e] = l at h
  cases h
  all_goals
    have hl' := congrArg List.reverse hl
    simp [List.reverse_append, vals, List.map_eq_cons_iff, toAdmin_eq_iff] at hl'
  all_goals obtain ⟨rfl, rfl⟩ := hl'
  all_goals refine ⟨_, rfl, fun q => ?_⟩
  all_goals (try (rename_i h; simp only [VecFloatUnOpRel_det, VecFloatBinOpRel_det,
    VecFloatTernOpRel_det, extBin_iff, cvt_iff, VecExtUnOpRel, VecExtTernOpRel,
    VecNarrowRel] at h))
  all_goals (try subst_vars)
  all_goals first
    | (rename_i hb; simp [pure?, shuffle?_of hb])
    | (rename_i hb; simp [pure?, inLane?_of_lt hb])
    | simp at h
    | simp [pure?, Option.eq_none_iff_forall_ne_some.mpr h]
    | simp [pure?, h]
    | simp [pure?, Val.i32]

end Vec

theorem vectorStep?_sound {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} {e : Admin}
    {k : Nat} {c : Config H} (h : vectorStep? o s f vs e = some (k, c)) :
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c := by
  cases e with
  | plain i =>
    simp only [vectorStep?, Option.map_eq_some_iff] at h
    obtain ⟨⟨k', out⟩, hp, hk⟩ := h
    simp only [Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨hk, hs⟩ := Vec.pure?_sound hp
    rw [List.length_reverse] at hk
    rw [List.take_reverse, List.reverse_reverse] at hs
    exact ⟨hk, Head.vector hs⟩
  | _ => simp [vectorStep?] at h

theorem vectorStep?_complete {o : GrowOracle} {s : Store H} {f : Frame} {vs args : List Val}
    {e : Admin} {c : Config H} (h : Head (profile o) s f args e c) (hk : famOf e = .vector)
    (hvs : ∃ q, vs = q ++ args) : vectorStep? o s f vs e = some (args.length, c) := by
  have hf := h.fam_inv (by rw [hk]; decide)
  rw [hk] at hf
  obtain ⟨is', hstep, rfl⟩ := hf
  obtain ⟨i, rfl, hp⟩ := Vec.pure?_complete hstep
  obtain ⟨q, rfl⟩ := hvs
  simp only [vectorStep?, List.reverse_append]
  rw [show profile o = Profile.deterministic o from rfl, hp]
  rfl

end Silmaril.Wasm.SingleThreaded.Exec
