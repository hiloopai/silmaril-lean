module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Simd.Prod
public import Silmaril.Wasm.SpecTec.Sim.FwdSimdAgg.Thms

/-!
# Round 5: `vtestop`'s `allTrue` agrees at the concrete builtins

`$jsizenn(Jnn)` is the lane width (`applies_jsizenn`, through `$lsize`, `$size`, `$psize`),
`$inez_` of each lane is its non-zero test (`Equiv.callDef_inez`), and `$prod` of those tests is
Core's `all_true` (`prod_inez`): the `allTrue` field of family V's `VecAgree`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil bvV natV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round4Int (BI)

attribute [local simp] Silmaril.SpecTec.Equiv.Execution.findVal?_empty
  Silmaril.SpecTec.Equiv.Execution.findVal?_bindVal_lit

variable {H : Type} {B : Builtins}

/-! ## `$jsizenn` -/

set_option maxRecDepth 100000 in
theorem findDef_jsizenn (B : Builtins) : ∃ ps t, (simEnv B).findDef? "jsizenn" = some (ps, t,
    [.defD [.expP "Jnn" (.varT "Jnn" [])] [.expA (.varE "Jnn")]
      (.callE "lsize" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))]) []]) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_lsize (B : Builtins) : ∃ ps t, (simEnv B).findDef? "lsize" = some (ps, t,
    [.defD [.expP "numtype" (.varT "numtype" [])] [.expA numtypePatL]
      (.callE "size" [.expA (.varE "numtype")]) [],
     .defD [.expP "packtype" (.varT "packtype" [])] [.expA packtypePatL]
      (.callE "psize" [.expA (.varE "packtype")]) []]) := ⟨_, _, rfl⟩

/-- `$size(I64) = 64`. -/
theorem applies_size_i64 : Applies (simEnv B) "size" [.val (caseNilV "I64")] (natV 64) := by
  obtain ⟨ps, t, hd⟩ := findDef_size' B
  exact ⟨ps, t, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
    (matchExp_caseE_undef (by decide)))) (tryClauses_hit (matchArgs_cons (matchArg_expA
      (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil) premsHold_nil RefsGC.evalExp_num'))⟩

set_option maxRecDepth 100000 in
/-- `$lsize(nt) = $size(nt)` at `I32`, `I64`. -/
theorem applies_lsize_num (t : IntType) :
    Applies (simEnv B) "lsize" [.val (Vec.numTypeV (.int t))] (natV t.width) := by
  obtain ⟨ps, ty, hd⟩ := findDef_lsize B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil) premsHold_nil
    (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var (v := Vec.numTypeV (.int t)) (by simp))
      evalArgs_nil) ?_))⟩
  · cases t <;> rfl
  · cases t
    · exact applies_size_i32
    · exact applies_size_i64

set_option maxRecDepth 100000 in
/-- `$lsize(pt) = $psize(pt)` at `I8`, `I16`. -/
theorem applies_lsize_pack (p : PackType) :
    Applies (simEnv B) "lsize" [.val (tyV (Ty.pack p : CStorageType))] (natV p.width) := by
  obtain ⟨ps, ty, hd⟩ := findDef_lsize B
  refine ⟨ps, ty, _, hd, Or.inl (tryClauses_skip_match (matchArgs_cons_undef
    (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub ?_)) (tryClauses_hit (matchArgs_cons
      (matchArg_expA (Prims.matchExp_subE (matchExp_varE (by simp))) ?_) matchArgs_nil)
      premsHold_nil (Vec.evalExp_call rfl (evalArgs_cons (evalExp_var (by simp)) evalArgs_nil)
        (R4Fwd.applies_psize p))))⟩ <;>
    cases p <;> rfl

/-- `$lsize` of an integer lane type is its width. -/
theorem applies_lsize (s : IntShape) :
    Applies (simEnv B) "lsize" [.val (Vec.intLaneV s)] (natV s.laneWidth) := by
  cases s
  · exact applies_lsize_pack .i8
  · exact applies_lsize_pack .i16
  · exact applies_lsize_num .i32
  · exact applies_lsize_num .i64

set_option maxRecDepth 100000 in
/-- **`$jsizenn(Jnn)` is the lane width.** -/
theorem applies_jsizenn (s : IntShape) :
    Applies (simEnv B) "jsizenn" [.val (Vec.intLaneV s)] (natV s.laneWidth) := by
  obtain ⟨ps, ty, hd⟩ := findDef_jsizenn B
  exact ⟨ps, ty, _, hd, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_varE (by simp))) matchArgs_nil) premsHold_nil (Vec.evalExp_call rfl
      (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var (by simp))) evalArgs_nil)
      (applies_lsize s)))⟩

/-! ## `$inez_` and `$prod` -/

/-- **`$inez_(N, i)`** at every width, for every `B`. -/
theorem applies_inezN (N : Nat) (x : BitVec N) :
    Applies (simEnv B) "inez_" [.val (natV N), .val (pctV x.toNat)] (pctV (inez_ N x).toNat) := by
  have hargs : EvalArgs (simEnv B) VarEnv.empty [.expA (.numE (.natN N)),
      .expA (.caseE "%" (.tupE [.numE (.natN x.toNat)]))] [.val (natV N), .val (bvV x)] :=
    evalArgs_cons evalExp_num (evalArgs_cons (evalExp_caseE_iff.2 ⟨_, evalExp_tupE_iff.2 ⟨[_],
      evalExps_cons evalExp_num evalExps_nil, rfl⟩, rfl⟩) evalArgs_nil)
  exact (Equiv.ExecNumeric.applies_iff_callDef rfl hargs).2
    (Equiv.callDef_inez (IntNumeric.numEnv_simEnv B) rfl hargs)

/-- The non-zero tests of a list multiply to its `all`-non-zero test. -/
theorem prod_inez {N : Nat} : ∀ xs : List (BitVec N),
    (xs.map fun x => (inez_ N x).toNat).prod = (bool32 (xs.all fun x => x != 0)).toNat
  | [] => rfl
  | x :: xs => by
    have ih := prod_inez xs
    by_cases hx : x = 0
    · subst hx
      simp [inez_, u32OfBool, bool_, bool32]
    · have hx' : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
      have h1 : (inez_ N x).toNat = 1 := by simp [inez_, u32OfBool, bool_, hx']
      have h2 : (x != 0) = true := bne_iff_ne.2 hx
      rw [List.map_cons, List.prod_cons, List.all_cons, ih, h1, h2, Bool.true_and, Nat.one_mul]

/-- Two lists related pointwise through a common source list. -/
theorem forall₂_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (∀ x ∈ l, R (f x) (g x)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | _ :: _, h => .cons (h _ List.mem_cons_self)
      (forall₂_map fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- **`VecAgree.allTrue`** at the concrete builtins. -/
theorem allTrue (P : Profile) (hn : H → String) (host : HostSemantics H) :
    ∀ (sh : IntShape) (a : V128), ∃ ls jsz bs,
      Applies (simEnv (BI P hn host)) "lanes_" [.val (Vec.ishV sh), .val (Vec.vecV a)]
        (.list ls) ∧
      Applies (simEnv (BI P hn host)) "jsizenn" [.val (Vec.intLaneV sh)] jsz ∧
      List.Forall₂ (fun l b => Applies (simEnv (BI P hn host)) "inez_" [.val jsz, .val l]
        (pctV b)) ls bs ∧
      Applies (simEnv (BI P hn host)) "prod" [.val (.list (bs.map fun b => .num (.natN b)))]
        (.num (.natN (vecAllTrue sh a).toNat)) := by
  intro sh a
  refine ⟨lanesV (.int sh) a, natV sh.laneWidth,
    (sh.lanesOf a).map fun x => (inez_ sh.laneWidth x).toNat,
    applies_lanes P hn host (.int sh) a, applies_jsizenn sh,
    forall₂_map fun x _ => applies_inezN sh.laneWidth x, ?_⟩
  have hp := applies_prod (B := BI P hn host) ((sh.lanesOf a).map fun x => (inez_ sh.laneWidth x).toNat)
  rw [prod_inez] at hp
  exact hp

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
