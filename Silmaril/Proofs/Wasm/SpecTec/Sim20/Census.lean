module

public import Silmaril.Wasm.SpecTec.Sim20.Census.Defs

/-!
# The reduction-rule census, proved

`ruleEqB_iff` and `census_same` say what a `same` verdict means: the two rules are equal as IL
terms. The six `census_*` theorems are the census itself, computed by the kernel
(`decide +kernel`, kernel reduction, no native code): for each of `Step_pure`, `Step_read` and `Step`, the
wasm-1.0 rules against wasm-2.0 and the wasm-2.0 rules against wasm-3.0, all on the fixed
scripts. The table in `docs/projects/spectec/README.md` is printed from these lists.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Census

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec

set_option maxRecDepth 100000

/-- The `--ast` rendering of rules is injective, since that of definitions is
(`IL.defS_injective`). -/
theorem ruleS_injective : Function.Injective ruleS := by
  intro r r' h
  have hd : defS (.relD "" [] "" .boolT [r]) = defS (.relD "" [] "" .boolT [r']) := by
    simp [defS, rulesS, h]
  have e := defS_injective hd
  simpa using e

/-- `ruleEqB` decides equality of rules. -/
theorem ruleEqB_iff {r r' : Rule} : ruleEqB r r' = true ↔ r = r' := by
  simp only [ruleEqB, beq_iff_eq]
  exact ruleS_injective.eq_iff

/-- A `same j` verdict names an equal rule at index `j`. -/
theorem verdict_same {b : List Rule} {r : Rule} {j : Nat} (h : verdict b r = .same j) :
    b[j]? = some r := by
  unfold verdict at h
  split at h
  · rename_i k _
    split at h
    · rename_i r' hr'
      by_cases h₁ : ruleEqB r r' = true
      · simp only [h₁, ↓reduceIte, Verdict.same.injEq] at h
        subst h
        rw [hr', ruleEqB_iff.1 h₁]
      · simp only [h₁, Bool.false_eq_true, ↓reduceIte] at h
        split at h <;> cases h
    · cases h
  · split at h <;> cases h

/-- **What `same` means**: if the census lists rule `i` of `rel` in `a` as `same j`, then rule
`i` of `rel` in `a` and rule `j` of `rel` in `b` are one and the same IL rule. -/
theorem census_same {a b : Script} {rel : IL.Id} {i j : Nat} {x : IL.Id}
    (h : (i, x, Verdict.same j) ∈ census a b rel) : SameAt a b rel i j := by
  obtain ⟨⟨r, k⟩, hk, he⟩ := List.mem_map.1 h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, -, hv⟩ := he
  exact ⟨r, List.mem_zipIdx_iff_getElem?.1 hk, verdict_same hv⟩

/-! ## The census -/

/-- The census of `Step_pure`, wasm-1.0 against wasm-2.0 (tally: 13 same, 0 up to
`admininstr`, 16 changed, 0 renamed, 0 absent). -/
theorem census_pure_10_20 :
    census Scripts.Wasm10.fixed Scripts.Wasm20.fixed "Step_pure" =
  [(0, "unreachable", .same 0),
  (1, "nop", .same 1),
  (2, "drop", .same 2),
  (3, "select-true", .changed 3),
  (4, "select-false", .changed 4),
  (5, "if-true", .changed 5),
  (6, "if-false", .changed 6),
  (7, "label-vals", .same 7),
  (8, "br-zero", .same 8),
  (9, "br-succ", .same 9),
  (10, "br_if-true", .changed 10),
  (11, "br_if-false", .changed 11),
  (12, "br_table-lt", .changed 12),
  (13, "br_table-ge", .changed 13),
  (14, "frame-vals", .same 14),
  (15, "return-frame", .same 15),
  (16, "return-label", .same 16),
  (17, "trap-vals", .same 17),
  (18, "trap-label", .same 18),
  (19, "trap-frame", .same 19),
  (20, "unop-val", .changed 20),
  (21, "unop-trap", .changed 21),
  (22, "binop-val", .changed 22),
  (23, "binop-trap", .changed 23),
  (24, "testop", .changed 24),
  (25, "relop", .changed 25),
  (26, "cvtop-val", .changed 26),
  (27, "cvtop-trap", .changed 27),
  (28, "local.tee", .same 55)] := by
  decide +kernel

/-- The tally of `census_pure_10_20`. -/
theorem tally_pure_10_20 : tally (census Scripts.Wasm10.fixed Scripts.Wasm20.fixed "Step_pure") = (13, 0, 16, 0, 0) := by
  rw [census_pure_10_20]; rfl

/-- The census of `Step_pure`, wasm-2.0 against wasm-3.0 (tally: 19 same, 7 up to
`admininstr`, 20 changed, 1 renamed, 9 absent). -/
theorem census_pure_20_30 :
    census Scripts.Wasm20.fixed Scripts.Wasm30.fixed "Step_pure" =
  [(0, "unreachable", .same 0),
  (1, "nop", .same 1),
  (2, "drop", .admOnly 2),
  (3, "select-true", .admOnly 3),
  (4, "select-false", .admOnly 4),
  (5, "if-true", .same 5),
  (6, "if-false", .same 6),
  (7, "label-vals", .admOnly 7),
  (8, "br-zero", .absent),
  (9, "br-succ", .absent),
  (10, "br_if-true", .same 11),
  (11, "br_if-false", .same 12),
  (12, "br_table-lt", .same 13),
  (13, "br_table-ge", .same 14),
  (14, "frame-vals", .admOnly 21),
  (15, "return-frame", .changed 22),
  (16, "return-label", .changed 23),
  (17, "trap-vals", .absent),
  (18, "trap-label", .same 27),
  (19, "trap-frame", .same 29),
  (20, "unop-val", .same 46),
  (21, "unop-trap", .same 47),
  (22, "binop-val", .same 48),
  (23, "binop-trap", .same 49),
  (24, "testop", .same 50),
  (25, "relop", .same 51),
  (26, "cvtop-val", .changed 52),
  (27, "cvtop-trap", .changed 53),
  (28, "ref.is_null-true", .changed 32),
  (29, "ref.is_null-false", .admOnly 33),
  (30, "vvunop", .changed 54),
  (31, "vvbinop", .changed 55),
  (32, "vvternop", .changed 56),
  (33, "vvtestop", .changed 57),
  (34, "vunop", .renamed 58 "vunop-val"),
  (35, "vunop-trap", .same 59),
  (36, "vbinop-val", .same 60),
  (37, "vbinop-trap", .same 61),
  (38, "vtestop-true", .absent),
  (39, "vtestop-false", .absent),
  (40, "vrelop", .changed 65),
  (41, "vshiftop", .changed 66),
  (42, "vbitmask", .changed 67),
  (43, "vswizzle", .absent),
  (44, "vshuffle", .changed 69),
  (45, "vsplat", .changed 70),
  (46, "vextract_lane-num", .changed 71),
  (47, "vextract_lane-pack", .changed 72),
  (48, "vreplace_lane", .changed 73),
  (49, "vextunop", .changed 74),
  (50, "vextbinop", .changed 75),
  (51, "vnarrow", .changed 77),
  (52, "vcvtop-full", .absent),
  (53, "vcvtop-half", .absent),
  (54, "vcvtop-zero", .absent),
  (55, "local.tee", .admOnly 30)] := by
  decide +kernel

/-- The tally of `census_pure_20_30`. -/
theorem tally_pure_20_30 : tally (census Scripts.Wasm20.fixed Scripts.Wasm30.fixed "Step_pure") = (19, 7, 20, 1, 9) := by
  rw [census_pure_20_30]; rfl

/-! ## Rules shared between wasm-2.0 and wasm-3.0 used by the rule-level work -/

/-- `if-true`, `if-false` are rules 5 and 6 of `Step_pure` in both wasm-2.0 and wasm-3.0. -/
theorem sameAt_if_20_30 :
    SameAt Scripts.Wasm20.fixed Scripts.Wasm30.fixed "Step_pure" 5 5 ∧
      SameAt Scripts.Wasm20.fixed Scripts.Wasm30.fixed "Step_pure" 6 6 := by
  constructor <;> refine census_same (x := ?_) ?_ <;> [exact "if-true"; skip; exact "if-false"; skip] <;>
    rw [census_pure_20_30] <;> simp

end Silmaril.Wasm.SpecTec.Sim20.Census
