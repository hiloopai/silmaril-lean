module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecRead
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecReadControl
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecReadTable
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Unbind
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The aggregate (`struct` / `array`) rules of `Step_read`, characterised

`Equiv/ExecRead.lean` transcribes all 103 rules of `Step_read` and pins them
to `Silmaril.SpecTec.Specs.wasm30`.  Thirty-four of those act on the GC
aggregates — `struct.*` and `array.*`.  This file settles **all thirty-four**:

* **twenty-four exact characterisations**, each an iff saying precisely when
  `RuleFires` holds — the eight `-null` rules, `array.len-array`, the four
  `-zero` rules, the eight `-oob` rules (`array.new_elem-oob`,
  `array.get-oob`, `array.fill-oob`, `array.copy-oob1`/`-oob2`,
  `array.init_elem-oob1`/`-oob2`, `array.init_data-oob1`), the two `-succ`
  rules `array.fill-succ` and `array.init_elem-succ`, and
  `array.new_elem-alloc`;
* **ten rules that fire on nothing at all** — `array.get-array`,
  `array.new_data-oob`, `array.init_data-oob2`, `struct.new_default`,
  `struct.get-struct`, `array.new_default`, `array.new_data-num`,
  `array.copy-le`, `array.copy-gt` and `array.init_data-num`.  Each names a
  `mut?`/`zt` pair that only its `Expand` premise could bind, and in this
  semantics neither a `CallE` in the conclusion nor a `RulePr` can bind
  anything: both *evaluate*.  See the three sections at the end.

That the GC rules are a third of `Step_read` and nearly half of its unfireable
ones is not an accident of the transcription: every aggregate rule that has to
look at a storage type reaches it through `Expand`, and `Expand` is a `RulePr`.

The state stays abstract throughout.  `$arrayinst`, `$elem` and `$type` are
never unfolded: each is stated with `ExecNumeric.Applies`, which says what the
rule *derives* without saying what the accessor computes.  The runtime bridge
is the other end of that, and it is a separate workstream.

Two findings worth naming up front.  The `-zero` rules' `else` is **vacuous**
here, so each of them overlaps its `-oob` sibling:
`arrayFill_zero_oob_overlap` exhibits a configuration that both traps and
succeeds.  And `array.new_elem` had a *gap* rather than an overlap: with
`eval.ml:284`'s strict slice bound, at `i + n = |$elem(z, y).REFS|` neither
`-alloc` nor `-oob` fired.  With the corrected bound (upstream item U2)
`-alloc` fires there — `arrayNewElem_boundary_alloc`.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.ExecReadAggregate

open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation
  (RuleFires HasRuleAt MatchExps derives_of_ruleAt ruleFires_nil_iff)
open Silmaril.SpecTec.Equiv.Execution
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.SpecTec.Equiv.Unbind

attribute [local simp] Execution.findVal?_empty Execution.findVal?_bindVal_lit

/-! ## Pattern lists of five and six

The aggregate rules read up to six operands off the stack, two more than
`Equiv/Execution.lean`'s `matchExps_four_iff` reaches. -/

/-- A five-element pattern list. -/
theorem matchExps_five_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ e₃ e₄ e₅ : Exp}
    {vs : List Value} :
    MatchExps env ρ [e₁, e₂, e₃, e₄, e₅] vs ρ' ↔
      ∃ a b c d e σ τ υ φ, vs = [a, b, c, d, e] ∧ MatchExp env ρ e₁ a σ ∧
        MatchExp env σ e₂ b τ ∧ MatchExp env τ e₃ c υ ∧ MatchExp env υ e₄ d φ ∧
        MatchExp env φ e₅ e ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, c, d, e, τ, υ, φ, rfl, hb, hc, hd, he⟩ := matchExps_four_iff.1 h₂
    exact ⟨w, b, c, d, e, σ, τ, υ, φ, rfl, h₁, hb, hc, hd, he⟩
  · rintro ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨a, [b, c, d, e], σ, rfl, h₁,
      matchExps_four_iff.2 ⟨b, c, d, e, τ, υ, φ, rfl, h₂, h₃, h₄, h₅⟩⟩

/-- A six-element pattern list. -/
theorem matchExps_six_iff {env : Env} {ρ ρ' : VarEnv} {e₁ e₂ e₃ e₄ e₅ e₆ : Exp}
    {vs : List Value} :
    MatchExps env ρ [e₁, e₂, e₃, e₄, e₅, e₆] vs ρ' ↔
      ∃ a b c d e g σ τ υ φ χ, vs = [a, b, c, d, e, g] ∧ MatchExp env ρ e₁ a σ ∧
        MatchExp env σ e₂ b τ ∧ MatchExp env τ e₃ c υ ∧ MatchExp env υ e₄ d φ ∧
        MatchExp env φ e₅ e χ ∧ MatchExp env χ e₆ g ρ' := by
  rw [Validation.matchExps_cons_iff]
  constructor
  · rintro ⟨w, ws, σ, rfl, h₁, h₂⟩
    obtain ⟨b, c, d, e, g, τ, υ, φ, χ, rfl, hb, hc, hd, he, hg⟩ := matchExps_five_iff.1 h₂
    exact ⟨w, b, c, d, e, g, σ, τ, υ, φ, χ, rfl, h₁, hb, hc, hd, he, hg⟩
  · rintro ⟨a, b, c, d, e, g, σ, τ, υ, φ, χ, rfl, h₁, h₂, h₃, h₄, h₅, h₆⟩
    exact ⟨a, [b, c, d, e, g], σ, rfl, h₁,
      matchExps_five_iff.2 ⟨b, c, d, e, g, τ, υ, φ, χ, rfl, h₂, h₃, h₄, h₅, h₆⟩⟩

/-! ## The operand patterns the family shares -/

/-- `(CONST I32 i)` with a fresh `i`: the payload is bound whole, unexamined.
Every aggregate rule that reads an index off the stack uses it. -/
theorem matchExp_constI32Var_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v : Value}
    (hx : ρ.findVal? x = none) :
    MatchExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE x])) v ρ' ↔
      ∃ c, v = Execution.constV Execution.i32V c ∧ ρ' = ρ.bindVal x c := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨nt, c, σ, rfl, hnt, hc⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    rw [matchExp_freshVar_iff hx] at hc
    exact ⟨c, rfl, hc⟩
  · rintro ⟨c, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_freshVar_iff hx).2 rfl⟩⟩⟩

/-- `(CONST I32 %(n))` with a fresh `n`: one more `%` wrapper than
`matchExp_constI32Var_iff`, and still no constraint on what is inside. -/
theorem matchExp_constI32Pct_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {v : Value}
    (hx : ρ.findVal? x = none) :
    MatchExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
        .caseE "%" (.tupE [.varE x])])) v ρ' ↔
      ∃ n, v = Execution.constV Execution.i32V (.case "%" (.tuple [n])) ∧
        ρ' = ρ.bindVal x n := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨nt, c, σ, rfl, hnt, hc⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    obtain ⟨u, rfl, hu⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨us, rfl, hus⟩ := Validation.matchExp_tup_iff.1 hu
    obtain ⟨n, rfl, hn⟩ := matchExps_one_iff.1 hus
    rw [matchExp_freshVar_iff hx] at hn
    exact ⟨n, rfl, hn⟩
  · rintro ⟨n, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl, (matchExp_freshVar_iff hx).2 rfl⟩⟩⟩⟩⟩⟩

/-- `sx?`, the optional sign extension `struct.get` and `array.get` carry.  The
`.opt` iteration matches any option and binds the *whole* option to `sx?`; the
per-round binding of `sx` is discarded, so the pattern constrains nothing. -/
theorem matchExp_optVar_iff {env : Env} {ρ ρ' : VarEnv} {x y : IL.Id} {v : Value}
    (hx : ρ.findVal? x = none) (hy : ρ.findVal? y = none) (hne : x ≠ "_") :
    MatchExp env ρ (.iterE (.varE x) (.mk .opt [.mk x (.varE y)])) v ρ' ↔
      ∃ o : Option Value, v = .opt o ∧ ρ' = ρ.bindVal y (.opt o) := by
  rw [Execution.matchExp_iterE_opt_iff]
  constructor
  · rintro (⟨rfl, hv⟩ | ⟨w, σ, u, rfl, hw, hu, hv⟩)
    · rw [matchExp_freshVar_iff hy] at hv
      exact ⟨none, rfl, hv⟩
    · rw [matchExp_freshVar_iff hx] at hw
      subst hw
      rw [Execution.findVal?_bindVal_lit hne] at hu
      simp only [reduceIte, Option.some.injEq] at hu
      subst hu
      rw [matchExp_freshVar_iff hy] at hv
      exact ⟨some w, rfl, hv⟩
  · rintro ⟨o, rfl, rfl⟩
    cases o with
    | none => exact Or.inl ⟨rfl, (matchExp_freshVar_iff hy).2 rfl⟩
    | some w =>
        refine Or.inr ⟨w, ρ.bindVal x w, w, rfl, (matchExp_freshVar_iff hx).2 rfl, ?_,
          (matchExp_freshVar_iff hy).2 rfl⟩
        rw [Execution.findVal?_bindVal_lit hne]
        simp

/-- A `sub` around a fresh variable: it binds anything. -/
theorem matchExp_subVar_iff {env : Env} {ρ ρ' : VarEnv} {x : IL.Id} {t₁ t₂ : Typ}
    {v : Value} (hx : ρ.findVal? x = none) :
    MatchExp env ρ (.subE (.varE x) t₁ t₂) v ρ' ↔ ρ' = ρ.bindVal x v := by
  rw [Validation.matchExp_sub_iff, matchExp_freshVar_iff hx]

/-- A one-argument injection around a fresh variable, e.g. `(ARRAY.FILL x)`. -/
theorem matchExp_caseVar_iff {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {x : IL.Id}
    {v : Value} (hx : ρ.findVal? x = none) :
    MatchExp env ρ (.caseE op (.varE x)) v ρ' ↔
      ∃ w, v = .case op w ∧ ρ' = ρ.bindVal x w := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    rw [matchExp_freshVar_iff hx] at hw
    exact ⟨w, rfl, hw⟩
  · rintro ⟨w, rfl, rfl⟩
    exact ⟨w, rfl, (matchExp_freshVar_iff hx).2 rfl⟩

/-- A two-argument injection around two fresh variables, e.g.
`(ARRAY.COPY x_1 x_2)`. -/
theorem matchExp_caseVar2_iff {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {x y : IL.Id}
    {v : Value} (hx : ρ.findVal? x = none) (hy : ρ.findVal? y = none) (hne : x ≠ y)
    (hw : x ≠ "_") :
    MatchExp env ρ (.caseE op (.tupE [.varE x, .varE y])) v ρ' ↔
      ∃ a b, v = .case op (.tuple [a, b]) ∧ ρ' = (ρ.bindVal x a).bindVal y b := by
  have hy' : ∀ a : Value, (ρ.bindVal x a).findVal? y = none := by
    intro a
    rw [Execution.findVal?_bindVal_lit hw]
    simp [hne, hy]
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw'⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw'
    obtain ⟨a, b, σ, rfl, ha, hb⟩ := matchExps_two_iff.1 hws
    rw [matchExp_freshVar_iff hx] at ha
    subst ha
    rw [matchExp_freshVar_iff (hy' a)] at hb
    exact ⟨a, b, rfl, hb⟩
  · rintro ⟨a, b, rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, (matchExp_freshVar_iff hx).2 rfl,
        (matchExp_freshVar_iff (hy' a)).2 rfl⟩⟩⟩

/-! ## The trapping conclusion

Eight of the thirty-five rules are the `-null` rules: each matches a null
reference somewhere on the stack and steps to `TRAP`, with **no premises at
all**.  They differ only in the pattern list of operands, so one lemma for the
conclusion shape serves all eight. -/

/-- The conclusion shape `(z; instr*) ~> [TRAP]`, matched from the empty
scope.  The state variable `z` is fresh and never inspected. -/
theorem matchExp_trapConcl_iff {env : Env} {ρ' : VarEnv} {es : List Exp} {v : Value} :
    MatchExp env VarEnv.empty
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]),
              .listE [.caseE "TRAP" (.tupE [])]]) v ρ' ↔
      ∃ z instrs, v = .tuple [ExecStep.configV z instrs, .list [Execution.trapV]] ∧
        MatchExps env (VarEnv.empty.bindVal "z" z) es instrs ρ' := by
  rw [matchExp_concl_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, hl, hr⟩
    obtain ⟨zs, rfl, hzs⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hzs
    obtain ⟨z, isv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨instrs, rfl, hinstrs⟩ := Validation.matchExp_list_iff.1 hi
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨t, rfl, ht⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_caseNil_iff] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨z, instrs, rfl, hinstrs⟩
  · rintro ⟨z, instrs, rfl, hinstrs⟩
    exact ⟨_, _, _, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl, hinstrs⟩⟩⟩⟩,
      Validation.matchExp_list_iff.2 ⟨_, rfl,
        matchExps_one_iff.2 ⟨_, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩

/-- `(REF.NULL_ADDR)`, the value every `-null` rule matches. -/
abbrev refNullV : Value := Execution.caseNilV "REF.NULL_ADDR"

/-! ## The eight `-null` rules

Each has an empty premise list, so it fires on exactly the configurations its
conclusion matches — and nothing about the state, the indices, the counts or
the operand values is constrained.  In particular the counts are *not*
required to be numbers: `%(n)` binds whatever is inside the `%`. -/

/-- **`Step_read/array.len-null`, characterised exactly.**  The simplest rule
of the family: no operands beyond the null reference, no premises. -/
theorem ruleFires_arrayLenNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayLenNullRule ↔
      ∃ z, v = .tuple [ExecStep.configV z [refNullV, Execution.caseNilV "ARRAY.LEN"],
        .list [Execution.trapV]] := by
  unfold arrayLenNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, σ, rfl, ha, hb⟩ := matchExps_two_iff.1 hms
    rw [matchExp_caseNil_iff] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [matchExp_caseNil_iff] at hb
    obtain ⟨rfl, -⟩ := hb
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/struct.get-null`, characterised exactly.**  The field index
`i` and the type index `x` are bound and never looked at, and `sx?` matches
any option. -/
theorem ruleFires_structGetNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v structGetNullRule ↔
      ∃ (z : Value) (sx : Option Value) (x i : Value),
        v = .tuple [ExecStep.configV z
          [refNullV, .case "STRUCT.GET" (.tuple [.opt sx, x, i])],
          .list [Execution.trapV]] := by
  unfold structGetNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, σ, rfl, ha, hb⟩ := matchExps_two_iff.1 hms
    rw [matchExp_caseNil_iff] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨w, rfl, hw⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨o, xv, iv, τ, υ, rfl, ho, hx, hi⟩ := matchExps_three_iff.1 hws
    rw [matchExp_optVar_iff (by simp) (by simp) (by simp)] at ho
    obtain ⟨sx, rfl, rfl⟩ := ho
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    exact ⟨z, sx, xv, iv, rfl⟩
  · rintro ⟨z, sx, x, i, rfl⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
              (matchExp_optVar_iff (by simp) (by simp) (by simp)).2 ⟨sx, rfl, rfl⟩,
              (matchExp_freshVar_iff (by simp)).2 rfl,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/array.get-null`, characterised exactly.** -/
theorem ruleFires_arrayGetNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayGetNullRule ↔
      ∃ (z i : Value) (sx : Option Value) (x : Value),
        v = .tuple [ExecStep.configV z
          [refNullV, Execution.constV Execution.i32V i,
           .case "ARRAY.GET" (.tuple [.opt sx, x])],
          .list [Execution.trapV]] := by
  unfold arrayGetNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, σ, τ, rfl, ha, hb, hc⟩ := matchExps_three_iff.1 hms
    rw [matchExp_caseNil_iff] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    obtain ⟨w, rfl, hw⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨o, xv, υ, rfl, ho, hx⟩ := matchExps_two_iff.1 hws
    rw [matchExp_optVar_iff (by simp) (by simp) (by simp)] at ho
    obtain ⟨sx, rfl, rfl⟩ := ho
    exact ⟨z, i, sx, xv, rfl⟩
  · rintro ⟨z, i, sx, x, rfl⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_three_iff.2 ⟨_, _, _, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i, rfl, rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              (matchExp_optVar_iff (by simp) (by simp) (by simp)).2 ⟨sx, rfl, rfl⟩,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/array.fill-null`, characterised exactly.**  The value `val`
being written is bound by a `sub` pattern, so it is entirely unconstrained. -/
theorem ruleFires_arrayFillNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayFillNullRule ↔
      ∃ z i val n x,
        v = .tuple [ExecStep.configV z
          [refNullV, Execution.constV Execution.i32V i, val,
           Execution.constV Execution.i32V (.case "%" (.tuple [n])),
           .case "ARRAY.FILL" x],
          .list [Execution.trapV]] := by
  unfold arrayFillNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseNil_iff] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_subVar_iff (by simp)] at hc
    subst hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar_iff (by simp)] at he
    obtain ⟨x, rfl, -⟩ := he
    exact ⟨z, i, c, n, x, rfl⟩
  · rintro ⟨z, i, val, n, x, rfl⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i, rfl, rfl⟩,
        (matchExp_subVar_iff (by simp)).2 rfl,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨n, rfl, rfl⟩,
        (matchExp_caseVar_iff (by simp)).2 ⟨x, rfl, rfl⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/array.copy-null1`, characterised exactly.**  The *destination*
reference is null; the source reference `ref` is bound and unconstrained. -/
theorem ruleFires_arrayCopyNull1_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayCopyNull1Rule ↔
      ∃ z i₁ ref i₂ n x₁ x₂,
        v = .tuple [ExecStep.configV z
          [refNullV, Execution.constV Execution.i32V i₁, ref,
           Execution.constV Execution.i32V i₂,
           Execution.constV Execution.i32V (.case "%" (.tuple [n])),
           .case "ARRAY.COPY" (.tuple [x₁, x₂])],
          .list [Execution.trapV]] := by
  unfold arrayCopyNull1Rule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, g, σ, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he, hg⟩ :=
      matchExps_six_iff.1 hms
    rw [matchExp_caseNil_iff] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i₁, rfl, rfl⟩ := hb
    rw [matchExp_subVar_iff (by simp)] at hc
    subst hc
    rw [matchExp_constI32Var_iff (by simp)] at hd
    obtain ⟨i₂, rfl, rfl⟩ := hd
    rw [matchExp_constI32Pct_iff (by simp)] at he
    obtain ⟨n, rfl, rfl⟩ := he
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at hg
    obtain ⟨x₁, x₂, rfl, -⟩ := hg
    exact ⟨z, i₁, c, i₂, n, x₁, x₂, rfl⟩
  · rintro ⟨z, i₁, ref, i₂, n, x₁, x₂, rfl⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_six_iff.2 ⟨_, _, _, _, _, _, _, _, _, _, _, rfl,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i₁, rfl, rfl⟩,
        (matchExp_subVar_iff (by simp)).2 rfl,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i₂, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨n, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨x₁, x₂, rfl, rfl⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/array.copy-null2`, characterised exactly.**  The mirror image:
the *source* reference is null and the destination is unconstrained. -/
theorem ruleFires_arrayCopyNull2_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayCopyNull2Rule ↔
      ∃ z ref i₁ i₂ n x₁ x₂,
        v = .tuple [ExecStep.configV z
          [ref, Execution.constV Execution.i32V i₁, refNullV,
           Execution.constV Execution.i32V i₂,
           Execution.constV Execution.i32V (.case "%" (.tuple [n])),
           .case "ARRAY.COPY" (.tuple [x₁, x₂])],
          .list [Execution.trapV]] := by
  unfold arrayCopyNull2Rule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, g, σ, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he, hg⟩ :=
      matchExps_six_iff.1 hms
    rw [matchExp_subVar_iff (by simp)] at ha
    subst ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i₁, rfl, rfl⟩ := hb
    rw [matchExp_caseNil_iff] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [matchExp_constI32Var_iff (by simp)] at hd
    obtain ⟨i₂, rfl, rfl⟩ := hd
    rw [matchExp_constI32Pct_iff (by simp)] at he
    obtain ⟨n, rfl, rfl⟩ := he
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at hg
    obtain ⟨x₁, x₂, rfl, -⟩ := hg
    exact ⟨z, a, i₁, i₂, n, x₁, x₂, rfl⟩
  · rintro ⟨z, ref, i₁, i₂, n, x₁, x₂, rfl⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_six_iff.2 ⟨_, _, _, _, _, _, _, _, _, _, _, rfl,
        (matchExp_subVar_iff (by simp)).2 rfl,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i₁, rfl, rfl⟩,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i₂, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨n, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨x₁, x₂, rfl, rfl⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/array.init_elem-null`, characterised exactly.** -/
theorem ruleFires_arrayInitElemNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayInitElemNullRule ↔
      ∃ z i j n x y,
        v = .tuple [ExecStep.configV z
          [refNullV, Execution.constV Execution.i32V i,
           Execution.constV Execution.i32V j,
           Execution.constV Execution.i32V (.case "%" (.tuple [n])),
           .case "ARRAY.INIT_ELEM" (.tuple [x, y])],
          .list [Execution.trapV]] := by
  unfold arrayInitElemNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseNil_iff] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_constI32Var_iff (by simp)] at hc
    obtain ⟨j, rfl, rfl⟩ := hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at he
    obtain ⟨x, y, rfl, -⟩ := he
    exact ⟨z, i, j, n, x, y, rfl⟩
  · rintro ⟨z, i, j, n, x, y, rfl⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨j, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨n, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨x, y, rfl, rfl⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-- **`Step_read/array.init_data-null`, characterised exactly.**  Identical in
shape to `array.init_elem-null`, with a different injection. -/
theorem ruleFires_arrayInitDataNull_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayInitDataNullRule ↔
      ∃ z i j n x y,
        v = .tuple [ExecStep.configV z
          [refNullV, Execution.constV Execution.i32V i,
           Execution.constV Execution.i32V j,
           Execution.constV Execution.i32V (.case "%" (.tuple [n])),
           .case "ARRAY.INIT_DATA" (.tuple [x, y])],
          .list [Execution.trapV]] := by
  unfold arrayInitDataNullRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseNil_iff] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_constI32Var_iff (by simp)] at hc
    obtain ⟨j, rfl, rfl⟩ := hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at he
    obtain ⟨x, y, rfl, -⟩ := he
    exact ⟨z, i, j, n, x, y, rfl⟩
  · rintro ⟨z, i, j, n, x, y, rfl⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨j, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨n, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨x, y, rfl, rfl⟩⟩⟩,
      Validation.premsHold_nil_iff.2 rfl⟩

/-! ## Reading the state

The rules below are the first of the family whose *conclusion* reads the
store: `array.len-array` returns `|$arrayinst(z)[a].FIELDS|`.  `matchExp` has
no syntactic case for `LenE`, `IdxE`, `DotE` or `CallE`, so each falls through
to `matchDefault`, which **evaluates** the pattern and compares — which is why
these conclusions constrain the state at all.

`$arrayinst` stays abstract: `ArrayFields` says the array instance at an
address has a given field list, with `ExecNumeric.Applies` carrying the
accessor.  Nothing here unfolds it into `Silmaril.Wasm.Execution`. -/

/-- The general `Step_read` conclusion `(z; instr*) ~> rhs`, matched from the
empty scope: the state variable is fresh and never inspected. -/
theorem matchExp_readConcl_iff {env : Env} {ρ' : VarEnv} {es : List Exp} {er : Exp}
    {v : Value} :
    MatchExp env VarEnv.empty
      (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE es]), er]) v ρ' ↔
      ∃ z instrs rhs σ, v = .tuple [ExecStep.configV z instrs, rhs] ∧
        MatchExps env (VarEnv.empty.bindVal "z" z) es instrs σ ∧
        MatchExp env σ er rhs ρ' := by
  rw [matchExp_concl_iff]
  constructor
  · rintro ⟨a, b, σ, rfl, hl, hr⟩
    obtain ⟨zs, rfl, hzs⟩ := Validation.matchExp_case_iff.1 hl
    obtain ⟨avs, rfl, havs⟩ := Validation.matchExp_tup_iff.1 hzs
    obtain ⟨z, isv, τ, rfl, hz, hi⟩ := matchExps_two_iff.1 havs
    rw [matchExp_freshVar_iff (by simp)] at hz
    subst hz
    obtain ⟨instrs, rfl, hinstrs⟩ := Validation.matchExp_list_iff.1 hi
    exact ⟨z, instrs, b, σ, rfl, hinstrs, hr⟩
  · rintro ⟨z, instrs, rhs, σ, rfl, hinstrs, hr⟩
    exact ⟨_, _, σ, rfl,
      Validation.matchExp_case_iff.2 ⟨_, rfl,
        Validation.matchExp_tup_iff.2 ⟨_, rfl,
          matchExps_two_iff.2 ⟨_, _, _, rfl,
            (matchExp_freshVar_iff (by simp)).2 rfl,
            Validation.matchExp_list_iff.2 ⟨_, rfl, hinstrs⟩⟩⟩⟩, hr⟩

/-- `matchExp` at a `LenE` is the default match: evaluate, then compare. -/
theorem matchExp_lenE_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value} :
    MatchExp env ρ (.lenE e) v ρ' ↔ EvalExp env ρ (.lenE e) v ∧ ρ' = ρ := by
  rw [show MatchExp env ρ (.lenE e) v ρ'
        ↔ ∃ n, matchDefault n env ρ (.lenE e) v = .ok ρ' from ?_,
    ExecDefault.matchDefault_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [matchExp] at hn
    | succ m => exact ⟨m, by simpa only [matchExp] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa only [matchExp] using hn⟩

/-- `$arrayinst(z)[k].FIELDS = fields`, with `$arrayinst` left abstract.  This
is the only thing the aggregate rules ever ask of the array half of the
store. -/
def ArrayFields (env : Env) (z : Value) (k : Nat) (fields : List Value) : Prop :=
  ∃ ai inst, ExecNumeric.Applies env "arrayinst" [.val z] ai ∧
    ai.idx? k = some inst ∧ inst.field? "FIELDS" = some (.list fields)

/-- **`Step_read/array.len-array`, characterised exactly.**  Note what the
conclusion alone forces: the address must be a *natural number*, because
`$arrayinst(z)[a]` indexes with it, and the result is the length of the
instance's `FIELDS`.  The rule has no premises; everything it says is in its
conclusion. -/
theorem ruleFires_arrayLenArray_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayLenArrayRule ↔
      ∃ (z : Value) (k : Nat) (fields : List Value),
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" (.num (.natN k)), Execution.caseNilV "ARRAY.LEN"],
          .list [Execution.constV Execution.i32V (Execution.pctV fields.length)]] ∧
        ArrayFields env z k fields := by
  unfold arrayLenArrayRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨a, b, τ, rfl, ha, hb⟩ := matchExps_two_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_caseNil_iff] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    obtain ⟨c, rfl, hc⟩ := matchExps_one_iff.1 hbvs
    obtain ⟨w, rfl, hw⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨nt, pc, υ, rfl, hnt, hpc⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    obtain ⟨u, rfl, hu⟩ := Validation.matchExp_case_iff.1 hpc
    obtain ⟨us, rfl, hus⟩ := Validation.matchExp_tup_iff.1 hu
    obtain ⟨lv, rfl, hlv⟩ := matchExps_one_iff.1 hus
    rw [matchExp_lenE_iff] at hlv
    obtain ⟨hev, -⟩ := hlv
    rw [evalExp_lenE_iff] at hev
    obtain ⟨fields, hfs, rfl⟩ := hev
    obtain ⟨inst, hinst, hfield⟩ := evalExp_dotE_iff.1 hfs
    obtain ⟨ai, k, hai, hk, hidx⟩ := evalExp_idxE_iff.1 hinst
    rw [evalExp_varE_iff] at hk
    simp at hk
    subst hk
    refine ⟨z, k, fields, rfl, ai, inst, ?_, hidx, hfield⟩
    refine (ExecNumeric.applies_iff_callDef
      (ρ := (VarEnv.empty.bindVal "z" z).bindVal "a" (Value.num (.natN k))) rfl ?_).mpr
      (evalExp_callE_iff.1 hai)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil
  · rintro ⟨z, k, fields, rfl, ai, inst, happ, hidx, hfield⟩
    refine ⟨(VarEnv.empty.bindVal "z" z).bindVal "a" (Value.num (.natN k)),
      (VarEnv.empty.bindVal "z" z).bindVal "a" (Value.num (.natN k)),
      matchExp_readConcl_iff.2 ⟨z, _, _,
        (VarEnv.empty.bindVal "z" z).bindVal "a" (Value.num (.natN k)), rfl,
        matchExps_two_iff.2 ⟨_, _, _, rfl,
          (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
          matchExp_caseNil_iff.2 ⟨rfl, rfl⟩⟩, ?_⟩, Validation.premsHold_nil_iff.2 rfl⟩
    refine Validation.matchExp_list_iff.2 ⟨_, rfl,
      matchExps_one_iff.2 ⟨_, rfl,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩,
              Validation.matchExp_case_iff.2 ⟨_, rfl,
                Validation.matchExp_tup_iff.2 ⟨_, rfl,
                  matchExps_one_iff.2 ⟨_, rfl, ?_⟩⟩⟩⟩⟩⟩⟩⟩
    refine matchExp_lenE_iff.2 ⟨evalExp_lenE_iff.2 ⟨fields, ?_, rfl⟩, rfl⟩
    refine evalExp_dotE_iff.2 ⟨inst, ?_, hfield⟩
    refine evalExp_idxE_iff.2 ⟨ai, k, ?_, evalExp_varE_iff.2 (by simp), hidx⟩
    refine evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef
      (ρ := (VarEnv.empty.bindVal "z" z).bindVal "a" (Value.num (.natN k))) rfl ?_).mp happ)
    exact evalArgs_cons (evalExp_varE_iff.2 (by simp)) evalArgs_nil

/-! ## The four `-zero` rules

`array.fill-zero`, `array.copy-zero`, `array.init_elem-zero` and
`array.init_data-zero` each step to the *empty* instruction sequence when the
count is zero.  Their premise list is `else`, then `n = 0`.

The `else` is **vacuous** — `Sem/Eval.lean` sends `.elsePr` to `.ok ρ`
unconditionally and a `RelD` imposes no order on its rules — so the exclusion
the `else` is meant to express is not there.  Each `-zero` rule therefore
fires on configurations its `-oob` sibling also fires on: with `n = 0` and an
out-of-bounds `i`, `array.fill-oob` traps *and* `array.fill-zero` succeeds.
`arrayFill_zero_oob_overlap` exhibits it. -/

/-- The `-zero` rules' premise list: the `else` holds in every scope, and the
`if` forces the count variable to be bound to the literal `0`. -/
theorem premsHold_elseNZero_iff {env : Env} {ρ ρ' : VarEnv} :
    PremsHold env ρ [.elsePr, .ifPr (.cmpE .eqOp .boolT (.varE "n") (.numE (.natN 0)))] ρ' ↔
      ρ' = ρ ∧ ρ.findVal? "n" = some (.num (.natN 0)) := by
  rw [ExecRef.premsHold_elseIf_iff]
  constructor
  · rintro ⟨rfl, hev⟩
    obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff] at h₁
    rw [evalExp_numE_iff] at h₂
    subst h₂
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hc
    exact ⟨rfl, h₁⟩
  · rintro ⟨rfl, hn⟩
    exact ⟨rfl, evalExp_cmpE_iff.2 ⟨_, _, evalExp_varE_iff.2 hn,
      evalExp_numE_iff.2 rfl, ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩

/-- **`Step_read/array.fill-zero`, characterised exactly.** -/
theorem ruleFires_arrayFillZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayFillZeroRule ↔
      ∃ z a i val x,
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" a, Execution.constV Execution.i32V i, val,
           Execution.constV Execution.i32V (Execution.pctV 0),
           .case "ARRAY.FILL" x],
          .list []] := by
  unfold arrayFillZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_subVar_iff (by simp)] at hc
    subst hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar_iff (by simp)] at he
    obtain ⟨x, rfl, rfl⟩ := he
    rw [matchExp_listNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨-, hn⟩ := premsHold_elseNZero_iff.1 hp
    simp at hn
    subst hn
    exact ⟨z, av, i, c, x, rfl⟩
  · rintro ⟨z, a, i, val, x, rfl⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i, rfl, rfl⟩,
        (matchExp_subVar_iff (by simp)).2 rfl,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩⟩,
      matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩,
      premsHold_elseNZero_iff.2 ⟨rfl, ?_⟩⟩
    simp

/-- **`Step_read/array.copy-zero`, characterised exactly.** -/
theorem ruleFires_arrayCopyZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayCopyZeroRule ↔
      ∃ z a₁ i₁ a₂ i₂ x₁ x₂,
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" a₁, Execution.constV Execution.i32V i₁,
           .case "REF.ARRAY_ADDR" a₂, Execution.constV Execution.i32V i₂,
           Execution.constV Execution.i32V (Execution.pctV 0),
           .case "ARRAY.COPY" (.tuple [x₁, x₂])],
          .list []] := by
  unfold arrayCopyZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, g, τ, υ, φ, χ, ψ, rfl, ha, hb, hc, hd, he, hg⟩ :=
      matchExps_six_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨a₁, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i₁, rfl, rfl⟩ := hb
    rw [matchExp_caseVar_iff (by simp)] at hc
    obtain ⟨a₂, rfl, rfl⟩ := hc
    rw [matchExp_constI32Var_iff (by simp)] at hd
    obtain ⟨i₂, rfl, rfl⟩ := hd
    rw [matchExp_constI32Pct_iff (by simp)] at he
    obtain ⟨n, rfl, rfl⟩ := he
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at hg
    obtain ⟨x₁, x₂, rfl, rfl⟩ := hg
    rw [matchExp_listNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨-, hn⟩ := premsHold_elseNZero_iff.1 hp
    simp at hn
    subst hn
    exact ⟨z, a₁, i₁, a₂, i₂, x₁, x₂, rfl⟩
  · rintro ⟨z, a₁, i₁, a₂, i₂, x₁, x₂, rfl⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_six_iff.2 ⟨_, _, _, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i₁, rfl, rfl⟩,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i₂, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩,
      matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩,
      premsHold_elseNZero_iff.2 ⟨rfl, ?_⟩⟩
    simp

/-- **`Step_read/array.init_elem-zero`, characterised exactly.** -/
theorem ruleFires_arrayInitElemZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayInitElemZeroRule ↔
      ∃ z a i j x y,
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" a, Execution.constV Execution.i32V i,
           Execution.constV Execution.i32V j,
           Execution.constV Execution.i32V (Execution.pctV 0),
           .case "ARRAY.INIT_ELEM" (.tuple [x, y])],
          .list []] := by
  unfold arrayInitElemZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_constI32Var_iff (by simp)] at hc
    obtain ⟨j, rfl, rfl⟩ := hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at he
    obtain ⟨x, y, rfl, rfl⟩ := he
    rw [matchExp_listNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨-, hn⟩ := premsHold_elseNZero_iff.1 hp
    simp at hn
    subst hn
    exact ⟨z, av, i, j, x, y, rfl⟩
  · rintro ⟨z, a, i, j, x, y, rfl⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨j, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩,
      matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩,
      premsHold_elseNZero_iff.2 ⟨rfl, ?_⟩⟩
    simp

/-- **`Step_read/array.init_data-zero`, characterised exactly.** -/
theorem ruleFires_arrayInitDataZero_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayInitDataZeroRule ↔
      ∃ z a i j x y,
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" a, Execution.constV Execution.i32V i,
           Execution.constV Execution.i32V j,
           Execution.constV Execution.i32V (Execution.pctV 0),
           .case "ARRAY.INIT_DATA" (.tuple [x, y])],
          .list []] := by
  unfold arrayInitDataZeroRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_constI32Var_iff (by simp)] at hc
    obtain ⟨j, rfl, rfl⟩ := hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at he
    obtain ⟨x, y, rfl, rfl⟩ := he
    rw [matchExp_listNil_iff] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨-, hn⟩ := premsHold_elseNZero_iff.1 hp
    simp at hn
    subst hn
    exact ⟨z, av, i, j, x, y, rfl⟩
  · rintro ⟨z, a, i, j, x, y, rfl⟩
    refine ⟨_, _, matchExp_readConcl_iff.2 ⟨z, _, _, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨i, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨j, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩,
      matchExp_listNil_iff.2 ⟨rfl, rfl⟩⟩,
      premsHold_elseNZero_iff.2 ⟨rfl, ?_⟩⟩
    simp

/-! ## The out-of-bounds premises

Eight more rules trap on an out-of-bounds access.  Each premise compares an
index — or an index plus a count — with the length of a list the state
supplies, and the comparison is what pins the operands down: `Num.cmp` is
defined only on two numerals of the *same* constructor (`Sem/Value.lean`), and
`|…|` always denotes a `nat`.  So the premise, and nothing else in the rule,
forces the index and the count to be naturals. -/

/-- `>` against a `nat` succeeds only on a `nat`. -/
theorem cmpValues_gtNat_true_iff {u : Value} {q : Nat} :
    cmpValues .gtOp u (.num (.natN q)) = .ok (.bool true) ↔
      ∃ p : Nat, u = .num (.natN p) ∧ q < p := by
  constructor
  · intro h
    cases u with
    | num m =>
        cases m with
        | natN p => exact ⟨p, rfl, by simpa [cmpValues, Num.cmp] using h⟩
        | intN a => simp [cmpValues, Num.cmp] at h
        | ratN a => simp [cmpValues, Num.cmp] at h
        | realN a => simp [cmpValues, Num.cmp] at h
    | bool b => simp [cmpValues] at h
    | text t => simp [cmpValues] at h
    | tuple vs => simp [cmpValues] at h
    | case op y => simp [cmpValues] at h
    | struct fs => simp [cmpValues] at h
    | list vs => simp [cmpValues] at h
    | opt o => simp [cmpValues] at h
  · rintro ⟨p, rfl, hlt⟩
    simp [cmpValues, Num.cmp, hlt]

/-- `≥` against a `nat` succeeds only on a `nat`. -/
theorem cmpValues_geNat_true_iff {u : Value} {q : Nat} :
    cmpValues .geOp u (.num (.natN q)) = .ok (.bool true) ↔
      ∃ p : Nat, u = .num (.natN p) ∧ q ≤ p := by
  constructor
  · intro h
    cases u with
    | num m =>
        cases m with
        | natN p => exact ⟨p, rfl, by simpa [cmpValues, Num.cmp] using h⟩
        | intN a => simp [cmpValues, Num.cmp] at h
        | ratN a => simp [cmpValues, Num.cmp] at h
        | realN a => simp [cmpValues, Num.cmp] at h
    | bool b => simp [cmpValues] at h
    | text t => simp [cmpValues] at h
    | tuple vs => simp [cmpValues] at h
    | case op y => simp [cmpValues] at h
    | struct fs => simp [cmpValues] at h
    | list vs => simp [cmpValues] at h
    | opt o => simp [cmpValues] at h
  · rintro ⟨p, rfl, hle⟩
    simp [cmpValues, Num.cmp, hle]

/-- `+` never short-circuits. -/
theorem boolShort_addOp (u : Value) : boolShort .addOp u = none := by
  cases u <;> simp [boolShort]

/-- A sum that denotes a `nat` has two `nat` summands. -/
theorem binValues_addOp_natN {u w : Value} {r : Nat}
    (h : binValues .addOp u w = .ok (.num (.natN r))) :
    ∃ p q : Nat, u = .num (.natN p) ∧ w = .num (.natN q) ∧ r = p + q := by
  cases u with
  | num m =>
      cases w with
      | num m' =>
          cases m with
          | natN p =>
              cases m' with
              | natN q =>
                  exact ⟨p, q, rfl, rfl, by simpa [binValues, Num.bin, eq_comm] using h⟩
              | intN b => simp [binValues, Num.bin] at h
              | ratN b => simp [binValues, Num.bin] at h
              | realN b => simp [binValues, Num.bin] at h
          | intN a => cases m' <;> simp [binValues, Num.bin] at h
          | ratN a => cases m' <;> simp [binValues, Num.bin] at h
          | realN a => cases m' <;> simp [binValues, Num.bin] at h
      | bool b => simp [binValues] at h
      | text t => simp [binValues] at h
      | tuple vs => simp [binValues] at h
      | case op y => simp [binValues] at h
      | struct fs => simp [binValues] at h
      | list vs => simp [binValues] at h
      | opt o => simp [binValues] at h
  | bool b => cases w <;> simp [binValues, boolBin] at h
  | text t => cases w <;> simp [binValues] at h
  | tuple vs => cases w <;> simp [binValues] at h
  | case op y => cases w <;> simp [binValues] at h
  | struct fs => cases w <;> simp [binValues] at h
  | list vs => cases w <;> simp [binValues] at h
  | opt o => cases w <;> simp [binValues] at h

/-- `x.0` where `x` is bound to a `%(…)`: the projection reads the first
component of the injected tuple, and says nothing about the rest of it. -/
theorem evalExp_pctProj_iff {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value} :
    EvalExp env ρ (.projE (.uncaseE (.varE x) "%") 0) v ↔
      ∃ rest : List Value, ρ.findVal? x = some (.case "%" (.tuple (v :: rest))) := by
  rw [evalExp_projE_iff]
  constructor
  · rintro ⟨vs, hvs, -, hidx⟩
    rw [evalExp_uncaseE_iff, evalExp_varE_iff] at hvs
    cases vs with
    | nil => simp at hidx
    | cons w rest =>
        simp only [Int.toNat_zero, List.getElem?_cons_zero, Option.some.injEq] at hidx
        subst hidx
        exact ⟨rest, hvs⟩
  · rintro ⟨rest, h⟩
    exact ⟨v :: rest, evalExp_uncaseE_iff.2 (evalExp_varE_iff.2 h), by omega, by simp⟩

/-- The `-oob` premise with no count: `x.0 >= |…|`. -/
theorem evalExp_projGe_iff {env : Env} {ρ : VarEnv} {x : IL.Id} {e : Exp} :
    EvalExp env ρ
      (.cmpE .geOp (.numT .natT) (.projE (.uncaseE (.varE x) "%") 0) (.lenE e))
      (.bool true) ↔
      ∃ (p : Nat) (rest vs : List Value),
        ρ.findVal? x = some (.case "%" (.tuple (.num (.natN p) :: rest))) ∧
        EvalExp env ρ e (.list vs) ∧ vs.length ≤ p := by
  rw [evalExp_cmpE_iff]
  constructor
  · rintro ⟨v₁, v₂, h₁, h₂, hc⟩
    obtain ⟨vs, hvs, rfl⟩ := evalExp_lenE_iff.1 h₂
    obtain ⟨p, rfl, hle⟩ := cmpValues_geNat_true_iff.1 hc
    obtain ⟨rest, hx⟩ := evalExp_pctProj_iff.1 h₁
    exact ⟨p, rest, vs, hx, hvs, hle⟩
  · rintro ⟨p, rest, vs, hx, hvs, hle⟩
    exact ⟨_, _, evalExp_pctProj_iff.2 ⟨rest, hx⟩,
      evalExp_lenE_iff.2 ⟨vs, hvs, rfl⟩, cmpValues_geNat_true_iff.2 ⟨p, rfl, hle⟩⟩

/-- The `-oob` premise with a count: `x.0 + y > |…|`. -/
theorem evalExp_projAddGt_iff {env : Env} {ρ : VarEnv} {x y : IL.Id} {e : Exp} :
    EvalExp env ρ
      (.cmpE .gtOp (.numT .natT)
        (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE x) "%") 0) (.varE y))
        (.lenE e))
      (.bool true) ↔
      ∃ (p q : Nat) (rest vs : List Value),
        ρ.findVal? x = some (.case "%" (.tuple (.num (.natN p) :: rest))) ∧
        ρ.findVal? y = some (.num (.natN q)) ∧
        EvalExp env ρ e (.list vs) ∧ vs.length < p + q := by
  rw [evalExp_cmpE_iff]
  constructor
  · rintro ⟨v₁, v₂, h₁, h₂, hc⟩
    obtain ⟨vs, hvs, rfl⟩ := evalExp_lenE_iff.1 h₂
    obtain ⟨r, rfl, hlt⟩ := cmpValues_gtNat_true_iff.1 hc
    obtain ⟨w₁, hw₁, hbs⟩ := evalExp_binE_iff.1 h₁
    rcases hbs with hs | ⟨-, w₂, hw₂, hb⟩
    · rw [boolShort_addOp] at hs; exact absurd hs (by simp)
    · obtain ⟨p, q, rfl, rfl, rfl⟩ := binValues_addOp_natN hb
      obtain ⟨rest, hx⟩ := evalExp_pctProj_iff.1 hw₁
      rw [evalExp_varE_iff] at hw₂
      exact ⟨p, q, rest, vs, hx, hw₂, hvs, hlt⟩
  · rintro ⟨p, q, rest, vs, hx, hy, hvs, hlt⟩
    refine ⟨_, _, ?_, evalExp_lenE_iff.2 ⟨vs, hvs, rfl⟩,
      cmpValues_gtNat_true_iff.2 ⟨p + q, rfl, hlt⟩⟩
    exact evalExp_binE_iff.2 ⟨_, evalExp_pctProj_iff.2 ⟨rest, hx⟩,
      Or.inr ⟨boolShort_addOp _, _, evalExp_varE_iff.2 hy, by simp [binValues, Num.bin]⟩⟩

/-- One `if` premise. -/
theorem premsHold_oneIf_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} :
    PremsHold env ρ [.ifPr e] ρ' ↔ ρ' = ρ ∧ EvalExp env ρ e (.bool true) := by
  rw [Validation.premsHold_cons_iff]
  constructor
  · rintro ⟨σ, hpr, hrest⟩
    obtain rfl := Validation.premsHold_nil_iff.1 hrest
    obtain ⟨rfl, hev⟩ := Validation.premHolds_if_iff.1 hpr
    exact ⟨rfl, hev⟩
  · rintro ⟨rfl, hev⟩
    exact ⟨ρ', Validation.premHolds_if_iff.2 ⟨rfl, hev⟩, Validation.premsHold_nil_iff.2 rfl⟩

/-- `$arrayinst(z)[a].FIELDS`, evaluated: the address must denote a `nat`. -/
theorem evalExp_arrayFields_iff {env : Env} {ρ : VarEnv} {zx ax : IL.Id} {z av : Value}
    {vs : List Value} (hz : ρ.findVal? zx = some z) (ha : ρ.findVal? ax = some av)
    (hd : ρ.findDef? "arrayinst" = none) :
    EvalExp env ρ (.dotE (.idxE (.callE "arrayinst" [.expA (.varE zx)]) (.varE ax)) "FIELDS")
      (.list vs) ↔ ∃ k : Nat, av = .num (.natN k) ∧ ArrayFields env z k vs := by
  constructor
  · intro h
    obtain ⟨inst, hinst, hfield⟩ := evalExp_dotE_iff.1 h
    obtain ⟨ai, k, hai, hk, hidx⟩ := evalExp_idxE_iff.1 hinst
    rw [evalExp_varE_iff, ha] at hk
    refine ⟨k, Option.some.inj hk, ai, inst, ?_, hidx, hfield⟩
    exact (ExecNumeric.applies_iff_callDef (ρ := ρ) hd
      (evalArgs_cons (evalExp_varE_iff.2 hz) evalArgs_nil)).mpr (evalExp_callE_iff.1 hai)
  · rintro ⟨k, rfl, ai, inst, happ, hidx, hfield⟩
    refine evalExp_dotE_iff.2 ⟨inst, ?_, hfield⟩
    refine evalExp_idxE_iff.2 ⟨ai, k, ?_, evalExp_varE_iff.2 ha, hidx⟩
    exact evalExp_callE_iff.2 ((ExecNumeric.applies_iff_callDef (ρ := ρ) hd
      (evalArgs_cons (evalExp_varE_iff.2 hz) evalArgs_nil)).mp happ)

/-- `$elem(z, y).REFS = refs`, with `$elem` left abstract. -/
def ElemRefs (env : Env) (z y : Value) (refs : List Value) : Prop :=
  ∃ e, ExecNumeric.Applies env "elem" [.val z, .val y] e ∧ e.field? "REFS" = some (.list refs)

/-- `$elem(z, y).REFS`, evaluated. -/
theorem evalExp_elemRefs_iff {env : Env} {ρ : VarEnv} {zx yx : IL.Id} {z y : Value}
    {vs : List Value} (hz : ρ.findVal? zx = some z) (hy : ρ.findVal? yx = some y)
    (hd : ρ.findDef? "elem" = none) :
    EvalExp env ρ (.dotE (.callE "elem" [.expA (.varE zx), .expA (.varE yx)]) "REFS")
      (.list vs) ↔ ElemRefs env z y vs := by
  have hargs : EvalArgs env ρ [Arg.expA (.varE zx), Arg.expA (.varE yx)]
      [ArgV.val z, ArgV.val y] :=
    evalArgs_cons (evalExp_varE_iff.2 hz) (evalArgs_cons (evalExp_varE_iff.2 hy) evalArgs_nil)
  constructor
  · intro h
    obtain ⟨e, he, hfield⟩ := evalExp_dotE_iff.1 h
    exact ⟨e, (ExecNumeric.applies_iff_callDef (ρ := ρ) hd hargs).mpr
      (evalExp_callE_iff.1 he), hfield⟩
  · rintro ⟨e, happ, hfield⟩
    exact evalExp_dotE_iff.2 ⟨e, evalExp_callE_iff.2
      ((ExecNumeric.applies_iff_callDef (ρ := ρ) hd hargs).mp happ), hfield⟩

/-! ## The eight `-oob` rules -/

/-- **`Step_read/array.get-oob`, characterised exactly.** -/
theorem ruleFires_arrayGetOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayGetOobRule ↔
      ∃ (z : Value) (k p : Nat) (rest : List Value) (sx : Option Value) (x : Value)
        (fields : List Value),
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" (.num (.natN k)),
           Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
           .case "ARRAY.GET" (.tuple [.opt sx, x])],
          .list [Execution.trapV]] ∧
        ArrayFields env z k fields ∧ fields.length ≤ p := by
  unfold arrayGetOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, σ, τ, rfl, ha, hb, hc⟩ := matchExps_three_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    obtain ⟨w, rfl, hw⟩ := Validation.matchExp_case_iff.1 hc
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨o, xv, υ, rfl, ho, hx⟩ := matchExps_two_iff.1 hws
    rw [matchExp_optVar_iff (by simp) (by simp) (by simp)] at ho
    obtain ⟨sx, rfl, rfl⟩ := ho
    rw [matchExp_freshVar_iff (by simp)] at hx
    subst hx
    obtain ⟨-, hev⟩ := premsHold_oneIf_iff.1 hp
    obtain ⟨p, rest, fields, hi, hfs, hle⟩ := evalExp_projGe_iff.1 hev
    simp at hi
    subst hi
    rw [evalExp_arrayFields_iff (zx := "z") (ax := "a") (z := z) (av := av)
      (by simp) (by simp) rfl] at hfs
    obtain ⟨k, rfl, haf⟩ := hfs
    exact ⟨z, k, p, rest, sx, xv, fields, rfl, haf, hle⟩
  · rintro ⟨z, k, p, rest, sx, x, fields, rfl, haf, hle⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_two_iff.2 ⟨_, _, _, rfl,
              (matchExp_optVar_iff (by simp) (by simp) (by simp)).2 ⟨sx, rfl, rfl⟩,
              (matchExp_freshVar_iff (by simp)).2 rfl⟩⟩⟩⟩⟩,
      premsHold_oneIf_iff.2 ⟨rfl, ?_⟩⟩
    refine evalExp_projGe_iff.2 ⟨p, rest, fields, by simp, ?_, hle⟩
    exact (evalExp_arrayFields_iff (zx := "z") (ax := "a") (z := z)
      (av := Value.num (.natN k)) (by simp) (by simp) rfl).2 ⟨k, rfl, haf⟩

/-- **`Step_read/array.fill-oob`, characterised exactly.** -/
theorem ruleFires_arrayFillOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayFillOobRule ↔
      ∃ (z : Value) (k p q : Nat) (rest : List Value) (val x : Value)
        (fields : List Value),
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" (.num (.natN k)),
           Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
           val, Execution.constV Execution.i32V (Execution.pctV q),
           .case "ARRAY.FILL" x],
          .list [Execution.trapV]] ∧
        ArrayFields env z k fields ∧ fields.length < p + q := by
  unfold arrayFillOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_subVar_iff (by simp)] at hc
    subst hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar_iff (by simp)] at he
    obtain ⟨x, rfl, rfl⟩ := he
    obtain ⟨-, hev⟩ := premsHold_oneIf_iff.1 hp
    obtain ⟨p, q, rest, fields, hi, hn, hfs, hlt⟩ := evalExp_projAddGt_iff.1 hev
    simp at hi hn
    subst hi
    subst hn
    rw [evalExp_arrayFields_iff (zx := "z") (ax := "a") (z := z) (av := av)
      (by simp) (by simp) rfl] at hfs
    obtain ⟨k, rfl, haf⟩ := hfs
    exact ⟨z, k, p, q, rest, c, x, fields, rfl, haf, hlt⟩
  · rintro ⟨z, k, p, q, rest, val, x, fields, rfl, haf, hlt⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_subVar_iff (by simp)).2 rfl,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩⟩⟩,
      premsHold_oneIf_iff.2 ⟨rfl, ?_⟩⟩
    refine evalExp_projAddGt_iff.2 ⟨p, q, rest, fields, by simp, by simp, ?_, hlt⟩
    exact (evalExp_arrayFields_iff (zx := "z") (ax := "a") (z := z)
      (av := Value.num (.natN k)) (by simp) (by simp) rfl).2 ⟨k, rfl, haf⟩

/-- **`Step_read/array.copy-oob1`, characterised exactly.**  The bound checked
is the *destination*'s. -/
theorem ruleFires_arrayCopyOob1_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayCopyOob1Rule ↔
      ∃ (z : Value) (k p q : Nat) (rest : List Value) (a₂ i₂ x₁ x₂ : Value)
        (fields : List Value),
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" (.num (.natN k)),
           Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
           .case "REF.ARRAY_ADDR" a₂, Execution.constV Execution.i32V i₂,
           Execution.constV Execution.i32V (Execution.pctV q),
           .case "ARRAY.COPY" (.tuple [x₁, x₂])],
          .list [Execution.trapV]] ∧
        ArrayFields env z k fields ∧ fields.length < p + q := by
  unfold arrayCopyOob1Rule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, g, σ, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he, hg⟩ :=
      matchExps_six_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨a₁, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i₁, rfl, rfl⟩ := hb
    rw [matchExp_caseVar_iff (by simp)] at hc
    obtain ⟨a₂, rfl, rfl⟩ := hc
    rw [matchExp_constI32Var_iff (by simp)] at hd
    obtain ⟨i₂, rfl, rfl⟩ := hd
    rw [matchExp_constI32Pct_iff (by simp)] at he
    obtain ⟨n, rfl, rfl⟩ := he
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at hg
    obtain ⟨x₁, x₂, rfl, rfl⟩ := hg
    obtain ⟨-, hev⟩ := premsHold_oneIf_iff.1 hp
    obtain ⟨p, q, rest, fields, hi, hn, hfs, hlt⟩ := evalExp_projAddGt_iff.1 hev
    simp at hi hn
    subst hi
    subst hn
    rw [evalExp_arrayFields_iff (zx := "z") (ax := "a_1") (z := z) (av := a₁)
      (by simp) (by simp) rfl] at hfs
    obtain ⟨k, rfl, haf⟩ := hfs
    exact ⟨z, k, p, q, rest, a₂, i₂, x₁, x₂, fields, rfl, haf, hlt⟩
  · rintro ⟨z, k, p, q, rest, a₂, i₂, x₁, x₂, fields, rfl, haf, hlt⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_six_iff.2 ⟨_, _, _, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩⟩,
      premsHold_oneIf_iff.2 ⟨rfl, ?_⟩⟩
    refine evalExp_projAddGt_iff.2 ⟨p, q, rest, fields, by simp, by simp, ?_, hlt⟩
    exact (evalExp_arrayFields_iff (zx := "z") (ax := "a_1") (z := z)
      (av := Value.num (.natN k)) (by simp) (by simp) rfl).2 ⟨k, rfl, haf⟩

/-- **`Step_read/array.copy-oob2`, characterised exactly.**  The mirror of
`-oob1`: the *source*'s bound. -/
theorem ruleFires_arrayCopyOob2_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayCopyOob2Rule ↔
      ∃ (z : Value) (k p q : Nat) (rest : List Value) (a₁ i₁ x₁ x₂ : Value)
        (fields : List Value),
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" a₁, Execution.constV Execution.i32V i₁,
           .case "REF.ARRAY_ADDR" (.num (.natN k)),
           Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
           Execution.constV Execution.i32V (Execution.pctV q),
           .case "ARRAY.COPY" (.tuple [x₁, x₂])],
          .list [Execution.trapV]] ∧
        ArrayFields env z k fields ∧ fields.length < p + q := by
  unfold arrayCopyOob2Rule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, g, σ, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he, hg⟩ :=
      matchExps_six_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨a₁, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i₁, rfl, rfl⟩ := hb
    rw [matchExp_caseVar_iff (by simp)] at hc
    obtain ⟨a₂, rfl, rfl⟩ := hc
    rw [matchExp_constI32Var_iff (by simp)] at hd
    obtain ⟨i₂, rfl, rfl⟩ := hd
    rw [matchExp_constI32Pct_iff (by simp)] at he
    obtain ⟨n, rfl, rfl⟩ := he
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at hg
    obtain ⟨x₁, x₂, rfl, rfl⟩ := hg
    obtain ⟨-, hev⟩ := premsHold_oneIf_iff.1 hp
    obtain ⟨p, q, rest, fields, hi, hn, hfs, hlt⟩ := evalExp_projAddGt_iff.1 hev
    simp at hi hn
    subst hi
    subst hn
    rw [evalExp_arrayFields_iff (zx := "z") (ax := "a_2") (z := z) (av := a₂)
      (by simp) (by simp) rfl] at hfs
    obtain ⟨k, rfl, haf⟩ := hfs
    exact ⟨z, k, p, q, rest, a₁, i₁, x₁, x₂, fields, rfl, haf, hlt⟩
  · rintro ⟨z, k, p, q, rest, a₁, i₁, x₁, x₂, fields, rfl, haf, hlt⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_six_iff.2 ⟨_, _, _, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩⟩,
      premsHold_oneIf_iff.2 ⟨rfl, ?_⟩⟩
    refine evalExp_projAddGt_iff.2 ⟨p, q, rest, fields, by simp, by simp, ?_, hlt⟩
    exact (evalExp_arrayFields_iff (zx := "z") (ax := "a_2") (z := z)
      (av := Value.num (.natN k)) (by simp) (by simp) rfl).2 ⟨k, rfl, haf⟩

/-- **`Step_read/array.init_elem-oob1`, characterised exactly.** -/
theorem ruleFires_arrayInitElemOob1_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayInitElemOob1Rule ↔
      ∃ (z : Value) (k p q : Nat) (rest : List Value) (j x y : Value)
        (fields : List Value),
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" (.num (.natN k)),
           Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
           Execution.constV Execution.i32V j,
           Execution.constV Execution.i32V (Execution.pctV q),
           .case "ARRAY.INIT_ELEM" (.tuple [x, y])],
          .list [Execution.trapV]] ∧
        ArrayFields env z k fields ∧ fields.length < p + q := by
  unfold arrayInitElemOob1Rule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_constI32Var_iff (by simp)] at hc
    obtain ⟨j, rfl, rfl⟩ := hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at he
    obtain ⟨x, y, rfl, rfl⟩ := he
    obtain ⟨-, hev⟩ := premsHold_oneIf_iff.1 hp
    obtain ⟨p, q, rest, fields, hi, hn, hfs, hlt⟩ := evalExp_projAddGt_iff.1 hev
    simp at hi hn
    subst hi
    subst hn
    rw [evalExp_arrayFields_iff (zx := "z") (ax := "a") (z := z) (av := av)
      (by simp) (by simp) rfl] at hfs
    obtain ⟨k, rfl, haf⟩ := hfs
    exact ⟨z, k, p, q, rest, j, x, y, fields, rfl, haf, hlt⟩
  · rintro ⟨z, k, p, q, rest, j, x, y, fields, rfl, haf, hlt⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩⟩,
      premsHold_oneIf_iff.2 ⟨rfl, ?_⟩⟩
    refine evalExp_projAddGt_iff.2 ⟨p, q, rest, fields, by simp, by simp, ?_, hlt⟩
    exact (evalExp_arrayFields_iff (zx := "z") (ax := "a") (z := z)
      (av := Value.num (.natN k)) (by simp) (by simp) rfl).2 ⟨k, rfl, haf⟩

/-- **`Step_read/array.init_elem-oob2`, characterised exactly.**  This one
checks the *element segment*, not the array, so it is `$elem` that the
statement names. -/
theorem ruleFires_arrayInitElemOob2_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayInitElemOob2Rule ↔
      ∃ (z : Value) (p q : Nat) (rest : List Value) (a i x y : Value)
        (refs : List Value),
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" a, Execution.constV Execution.i32V i,
           Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
           Execution.constV Execution.i32V (Execution.pctV q),
           .case "ARRAY.INIT_ELEM" (.tuple [x, y])],
          .list [Execution.trapV]] ∧
        ElemRefs env z y refs ∧ refs.length < p + q := by
  unfold arrayInitElemOob2Rule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_constI32Var_iff (by simp)] at hc
    obtain ⟨j, rfl, rfl⟩ := hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at he
    obtain ⟨x, y, rfl, rfl⟩ := he
    obtain ⟨-, hev⟩ := premsHold_oneIf_iff.1 hp
    obtain ⟨p, q, rest, refs, hj, hn, hfs, hlt⟩ := evalExp_projAddGt_iff.1 hev
    simp at hj hn
    subst hj
    subst hn
    rw [evalExp_elemRefs_iff (zx := "z") (yx := "y") (z := z) (y := y)
      (by simp) (by simp) rfl] at hfs
    exact ⟨z, p, q, rest, av, i, x, y, refs, rfl, hfs, hlt⟩
  · rintro ⟨z, p, q, rest, a, i, x, y, refs, rfl, her, hlt⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩⟩,
      premsHold_oneIf_iff.2 ⟨rfl, ?_⟩⟩
    refine evalExp_projAddGt_iff.2 ⟨p, q, rest, refs, by simp, by simp, ?_, hlt⟩
    exact (evalExp_elemRefs_iff (zx := "z") (yx := "y") (z := z) (y := y)
      (by simp) (by simp) rfl).2 her

/-- **`Step_read/array.init_data-oob1`, characterised exactly.**  Identical in
shape to `array.init_elem-oob1`. -/
theorem ruleFires_arrayInitDataOob1_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayInitDataOob1Rule ↔
      ∃ (z : Value) (k p q : Nat) (rest : List Value) (j x y : Value)
        (fields : List Value),
        v = .tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" (.num (.natN k)),
           Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
           Execution.constV Execution.i32V j,
           Execution.constV Execution.i32V (Execution.pctV q),
           .case "ARRAY.INIT_DATA" (.tuple [x, y])],
          .list [Execution.trapV]] ∧
        ArrayFields env z k fields ∧ fields.length < p + q := by
  unfold arrayInitDataOob1Rule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_constI32Var_iff (by simp)] at hc
    obtain ⟨j, rfl, rfl⟩ := hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨n, rfl, rfl⟩ := hd
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at he
    obtain ⟨x, y, rfl, rfl⟩ := he
    obtain ⟨-, hev⟩ := premsHold_oneIf_iff.1 hp
    obtain ⟨p, q, rest, fields, hi, hn, hfs, hlt⟩ := evalExp_projAddGt_iff.1 hev
    simp at hi hn
    subst hi
    subst hn
    rw [evalExp_arrayFields_iff (zx := "z") (ax := "a") (z := z) (av := av)
      (by simp) (by simp) rfl] at hfs
    obtain ⟨k, rfl, haf⟩ := hfs
    exact ⟨z, k, p, q, rest, j, x, y, fields, rfl, haf, hlt⟩
  · rintro ⟨z, k, p, q, rest, j, x, y, fields, rfl, haf, hlt⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩⟩,
      premsHold_oneIf_iff.2 ⟨rfl, ?_⟩⟩
    refine evalExp_projAddGt_iff.2 ⟨p, q, rest, fields, by simp, by simp, ?_, hlt⟩
    exact (evalExp_arrayFields_iff (zx := "z") (ax := "a") (z := z)
      (av := Value.num (.natN k)) (by simp) (by simp) rfl).2 ⟨k, rfl, haf⟩

/-- **`Step_read/array.new_elem-oob`, characterised exactly.**  The only
aggregate `-oob` rule that reads no reference: the bound it checks is the
element segment's. -/
theorem ruleFires_arrayNewElemOob_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayNewElemOobRule ↔
      ∃ (z : Value) (p q : Nat) (rest : List Value) (x y : Value) (refs : List Value),
        v = .tuple [ExecStep.configV z
          [Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
           Execution.constV Execution.i32V (Execution.pctV q),
           .case "ARRAY.NEW_ELEM" (.tuple [x, y])],
          .list [Execution.trapV]] ∧
        ElemRefs env z y refs ∧ refs.length < p + q := by
  unfold arrayNewElemOobRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
    obtain ⟨a, b, c, σ, τ, rfl, ha, hb, hc⟩ := matchExps_three_iff.1 hms
    rw [matchExp_constI32Var_iff (by simp)] at ha
    obtain ⟨i, rfl, rfl⟩ := ha
    rw [matchExp_constI32Pct_iff (by simp)] at hb
    obtain ⟨n, rfl, rfl⟩ := hb
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at hc
    obtain ⟨x, y, rfl, rfl⟩ := hc
    obtain ⟨-, hev⟩ := premsHold_oneIf_iff.1 hp
    obtain ⟨p, q, rest, refs, hi, hn, hfs, hlt⟩ := evalExp_projAddGt_iff.1 hev
    simp at hi hn
    subst hi
    subst hn
    rw [evalExp_elemRefs_iff (zx := "z") (yx := "y") (z := z) (y := y)
      (by simp) (by simp) rfl] at hfs
    exact ⟨z, p, q, rest, x, y, refs, rfl, hfs, hlt⟩
  · rintro ⟨z, p, q, rest, x, y, refs, rfl, her, hlt⟩
    refine ⟨_, _, matchExp_trapConcl_iff.2 ⟨z, _, rfl,
      matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)).2
          ⟨_, _, rfl, rfl⟩⟩⟩,
      premsHold_oneIf_iff.2 ⟨rfl, ?_⟩⟩
    refine evalExp_projAddGt_iff.2 ⟨p, q, rest, refs, by simp, by simp, ?_, hlt⟩
    exact (evalExp_elemRefs_iff (zx := "z") (yx := "y") (z := z) (y := y)
      (by simp) (by simp) rfl).2 her

/-! ## A rule that cannot fire

`array.get-array`'s conclusion is

```
(z; (REF.ARRAY_ADDR a) (CONST I32 i) (ARRAY.GET sx? x))
  ~> ($unpackfield_(zt, sx?, $arrayinst(z)[a].FIELDS[i.0]))
```

and `zt` occurs **only** in the `Expand` premise, `$type(z, x) ~~ ARRAY (mut?
zt)`.  Two things in `Sem/Eval.lean` make that fatal:

* `ruleFires` matches the *whole* conclusion first and runs the premises
  afterwards, in the scope the match built (`Validation.ruleFires_nil_iff`);
* the conclusion's right-hand side is a `CallE`, for which `matchExp` has no
  syntactic case, so it falls through to `matchDefault`, which **evaluates**
  it — and evaluating `$unpackfield_(zt, …)` needs `zt` to be bound.

Nor could the premise supply it: a `RulePr` *evaluates* its argument too
(`Validation.premHolds_rule_iff`), so the `Expand` premise cannot bind `zt`
either.  The rule therefore fires on **no** configuration whatsoever, in any
environment.

The same reading applies to `struct.get-struct` (which needs `zt*`),
`array.copy-le`/`-gt` and `array.init_data-num` (`zt_2`, `zt`, `c`); only
`array.get-array` is proved here, because its unbound occurrence is a bare
`.varE` and the others sit under an iteration whose evaluation needs more
machinery.  This is a finding about the transcription's reading of the IL, not
a claim that the *paper* rule is vacuous: SpecTec's own interpreter solves the
premise first. -/

/-- **`Step_read/array.get-array` fires on nothing.** -/
theorem ruleFires_arrayGetArray_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayGetArrayRule := by
  unfold arrayGetArrayRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, -⟩
  obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
  obtain ⟨a, b, c, τ, υ, rfl, ha, hb, hc⟩ := matchExps_three_iff.1 hms
  rw [matchExp_caseVar_iff (by simp)] at ha
  obtain ⟨av, rfl, rfl⟩ := ha
  rw [matchExp_constI32Var_iff (by simp)] at hb
  obtain ⟨i, rfl, rfl⟩ := hb
  obtain ⟨w, rfl, hw⟩ := Validation.matchExp_case_iff.1 hc
  obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
  obtain ⟨o, xv, φ, rfl, ho, hx⟩ := matchExps_two_iff.1 hws
  rw [matchExp_optVar_iff (by simp) (by simp) (by simp)] at ho
  obtain ⟨sx, rfl, rfl⟩ := ho
  rw [matchExp_freshVar_iff (by simp)] at hx
  subst hx
  obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
  obtain ⟨u, rfl, hu⟩ := matchExps_one_iff.1 hbvs
  rw [Validation.matchExp_sub_iff, ExecDefault.matchExp_callE_iff] at hu
  obtain ⟨hcall, -⟩ := hu
  obtain ⟨ws', ps, t, cs, hargs, -, -⟩ := ExecNumeric.callDef_iff.1 hcall
  obtain ⟨ztv, ws'', -, hzt, -⟩ := evalArgs_expA_cons_iff.1 hargs
  rw [evalExp_varE_iff] at hzt
  simp at hzt

/-! ## The `else` overlap, exhibited -/

/-- **`array.fill-zero` and `array.fill-oob` both fire on the same
configuration.**  A zero-length fill at an index past the end of the array is
*both* a trap (by `-oob`) and a no-op (by `-zero`): the `else` that is meant
to exclude the first case does nothing.  This is the `Step_read` instance of
the overlap `Equiv/ExecRef.lean` found in `Step_pure` and
`Equiv/ExecRead.lean` found in `ref.test`/`ref.cast`. -/
theorem arrayFill_zero_oob_overlap {env : Env} (hr : HasReadRules env)
    (z : Value) (k p : Nat) (val x : Value) (fields : List Value)
    (haf : ArrayFields env z k fields) (hlt : fields.length < p) :
    Derives env "Step_read" "%~>%" []
        (.tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" (.num (.natN k)),
           Execution.constV Execution.i32V (Execution.pctV p), val,
           Execution.constV Execution.i32V (Execution.pctV 0),
           .case "ARRAY.FILL" x],
          .list [Execution.trapV]]) ∧
      Derives env "Step_read" "%~>%" []
        (.tuple [ExecStep.configV z
          [.case "REF.ARRAY_ADDR" (.num (.natN k)),
           Execution.constV Execution.i32V (Execution.pctV p), val,
           Execution.constV Execution.i32V (Execution.pctV 0),
           .case "ARRAY.FILL" x],
          .list []]) :=
  ⟨derives_of_ruleAt hr.arrayFillOob
      (ruleFires_arrayFillOob_iff.2 ⟨z, k, p, 0, [], val, x, fields, rfl, haf, by omega⟩),
   derives_of_ruleAt hr.arrayFillZero
      (ruleFires_arrayFillZero_iff.2
        ⟨z, .num (.natN k), Execution.pctV p, val, x, rfl⟩)⟩

/-! ## Two more rules that cannot fire

`array.new_data-oob` and `array.init_data-oob2` both carry the premise

```
Expand: $type(z, x) ~~ ARRAY (mut? zt)
```

and neither `mut?` nor `zt` occurs anywhere in the rule's *conclusion*.  A
`RulePr` evaluates the expression it asserts (`Validation.premHolds_rule_iff`)
rather than matching it, so the premise cannot introduce them: it needs them
already bound, and the conclusion — which is matched first — never binds
them.  Both rules therefore fire on nothing.

This is cleaner than `array.get-array` above: there the *conclusion* already
fails, here it is the premise, and the conclusions of these two are ordinary
trapping conclusions this file characterises elsewhere. -/

/-- The `Expand … ~~ ARRAY (mut? zt)` premise cannot hold where `zt` is
unbound. -/
theorem premHolds_expandArray_needs_zt {env : Env} {ρ ρ' : VarEnv} {e em : Exp}
    {zt : IL.Id} (hzt : ρ.findVal? zt = none) :
    ¬ PremHolds env ρ (.rulePr "Expand" [] "%~~%"
      (.tupE [e, .caseE "ARRAY" (.caseE "%%" (.tupE [em, .varE zt]))])) ρ' := by
  intro h
  obtain ⟨-, ws, w, -, hw, -⟩ := Validation.premHolds_rule_iff.1 h
  obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨-, qs, -, -, hq⟩ := Validation.evalExps_cons_iff.1 hvs
  obtain ⟨u, -, -, hu, -⟩ := Validation.evalExps_cons_iff.1 hq
  obtain ⟨u₁, hu₁, -⟩ := evalExp_caseE_iff.1 hu
  obtain ⟨u₂, hu₂, -⟩ := evalExp_caseE_iff.1 hu₁
  obtain ⟨vs₂, hvs₂, -⟩ := evalExp_tupE_iff.1 hu₂
  obtain ⟨-, rs, -, -, hr⟩ := Validation.evalExps_cons_iff.1 hvs₂
  obtain ⟨ztv, -, -, hztv, -⟩ := Validation.evalExps_cons_iff.1 hr
  rw [evalExp_varE_iff, hzt] at hztv
  exact absurd hztv (by simp)

/-- **`Step_read/array.new_data-oob` fires on nothing.** -/
theorem ruleFires_arrayNewDataOob_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayNewDataOobRule := by
  unfold arrayNewDataOobRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
  obtain ⟨a, b, c, σ, τ, rfl, ha, hb, hc⟩ := matchExps_three_iff.1 hms
  rw [matchExp_constI32Var_iff (by simp)] at ha
  obtain ⟨i, rfl, rfl⟩ := ha
  rw [matchExp_constI32Pct_iff (by simp)] at hb
  obtain ⟨n, rfl, rfl⟩ := hb
  rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at hc
  obtain ⟨x, y, rfl, rfl⟩ := hc
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  exact premHolds_expandArray_needs_zt (by simp) hpr

/-- **`Step_read/array.init_data-oob2` fires on nothing.** -/
theorem ruleFires_arrayInitDataOob2_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayInitDataOob2Rule := by
  unfold arrayInitDataOob2Rule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨z, instrs, rfl, hms⟩ := matchExp_trapConcl_iff.1 hm
  obtain ⟨a, b, c, d, e, σ, τ, υ, φ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
  rw [matchExp_caseVar_iff (by simp)] at ha
  obtain ⟨av, rfl, rfl⟩ := ha
  rw [matchExp_constI32Var_iff (by simp)] at hb
  obtain ⟨i, rfl, rfl⟩ := hb
  rw [matchExp_constI32Var_iff (by simp)] at hc
  obtain ⟨j, rfl, rfl⟩ := hc
  rw [matchExp_constI32Pct_iff (by simp)] at hd
  obtain ⟨n, rfl, rfl⟩ := hd
  rw [matchExp_caseVar2_iff (by simp) (by simp) (by simp) (by simp)] at he
  obtain ⟨x, y, rfl, rfl⟩ := he
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  exact premHolds_expandArray_needs_zt (by simp) hpr

/-! ## Which variables a conclusion leaves unbound

Seven of the ten rules this file had left open turn out to fire on nothing, and
the argument is always the same one `Equiv/ExecStepRules.lean` makes about
`Step`: a variable the conclusion never *binds* is needed by something that
only *evaluates*.  `Unbinds env e y` says `y` is not among the variables the
pattern `e` binds, and is read off the pattern's shape without unfolding
`matchExp`.

`ExecStepRules` imports this file, so its copy of the predicate cannot be
imported back; it is repeated here.  What is new is the closure under the three
formers the aggregate conclusions add and `Step` did not need: arithmetic
(`BinE`, `CvtE` — both of which `matchExp` only evaluates) and **iteration**
(`matchIterE`, whose per-round scopes are discarded: only the collected
columns, matched against the domain expressions, survive). -/

/-! `Unbinds` and its closure lemmas live in `Equiv/Unbind.lean`, shared with
`Equiv/ExecStepRules.lean`. -/

/-- Arithmetic is not a pattern: `matchExp` evaluates it and compares, so it
binds nothing at all. -/
theorem unbinds_binE {env : Env} {op : BinOp} {t : OpTyp} {e₁ e₂ : Exp} {y : IL.Id} :
    Unbinds env (.binE op t e₁ e₂) y := by
  rintro ρ σ v hy hm
  obtain ⟨-, rfl⟩ := ExecReadTable.matchExp_binE_iff.1 hm
  exact hy

/-- A coercion *is* a pattern, but it only undoes the conversion and matches
underneath. -/
theorem unbinds_cvtE {env : Env} {e : Exp} {t₁ t₂ : NumTyp} {y : IL.Id}
    (h : Unbinds env e y) : Unbinds env (.cvtE e t₁ t₂) y := by
  rintro ρ σ v hy hm
  obtain ⟨m, m', rfl, -, hm'⟩ := ExecReadTable.matchExp_cvtE_iff.1 hm
  exact h _ _ _ hy hm'

/-- `matchIterList` leaves the scope its *domains* leave.  The per-round scopes
are thrown away; only the collected columns, matched against the domain
expressions, reach the result (`Sem/Eval.lean`'s `matchIterList`). -/
theorem matchIterList_scope {env : Env} {ρ ρ' : VarEnv} {e : Exp} {ds : List Dom}
    {ido : Option IL.Id} {vs : List Value} (h : MatchIterList env ρ e ds ido vs ρ') :
    ∃ cols, MatchExps env ρ (ds.map domSrc) cols ρ' := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [matchIterList] at hn
  | succ m =>
      simp only [matchIterList, Res.bind_eq_ok] at hn
      obtain ⟨rows, -, hm⟩ := hn
      exact ⟨_, ⟨m, hm⟩⟩

/-- **An iteration binds only through its domains** — and, for a `^n`
iteration, through its counter.  This is what makes the long right-hand sides
of the aggregate rules tractable: whatever their *bodies* bind per round is
discarded. -/
theorem unbinds_iterE {env : Env} {e : Exp} {it : Iter} {ds : List Dom} {y : IL.Id}
    (hit : ∀ eₙ ido, it = .listN eₙ ido → Unbinds env eₙ y)
    (hd : UnbindsAll env (ds.map domSrc) y) : Unbinds env (.iterE e (.mk it ds)) y := by
  rintro ρ σ v hy ⟨n, hn⟩
  cases n with
  | zero => simp [matchExp] at hn
  | succ m =>
      simp only [matchExp] at hn
      cases m with
      | zero => cases it <;> simp [matchIterE] at hn
      | succ k =>
          cases it with
          | opt =>
              simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
              obtain ⟨o, -, hm⟩ := hn
              cases o with
              | none => exact hd _ _ _ hy ⟨k, hm⟩
              | some w =>
                  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok] at hm
                  obtain ⟨ρ', hρ', ws, hws, hm'⟩ := hm
                  exact hd _ _ _ hy ⟨k, hm'⟩
          | list =>
              simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
              obtain ⟨vs, -, hm⟩ := hn
              obtain ⟨cols, hc⟩ := matchIterList_scope (env := env) (ρ := ρ) ⟨k, hm⟩
              exact hd _ _ _ hy hc
          | list1 =>
              simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok,
                Res.assert_eq_ok] at hn
              obtain ⟨vs, -, -, hm⟩ := hn
              obtain ⟨cols, hc⟩ := matchIterList_scope (env := env) (ρ := ρ) ⟨k, hm⟩
              exact hd _ _ _ hy hc
          | listN eₙ ido =>
              simp only [matchIterE, Res.bind_eq_ok, Res.ofOption_eq_ok] at hn
              obtain ⟨vs, -, ρ₀, h₀, hm⟩ := hn
              have h₁ := hit eₙ ido rfl _ _ _ hy ⟨k, h₀⟩
              obtain ⟨cols, hc⟩ := matchIterList_scope (env := env) (ρ := ρ₀) ⟨k, hm⟩
              exact hd _ _ _ h₁ hc

theorem unbinds_iterE_opt {env : Env} {e : Exp} {ds : List Dom} {y : IL.Id}
    (hd : UnbindsAll env (ds.map domSrc) y) : Unbinds env (.iterE e (.mk .opt ds)) y :=
  unbinds_iterE (by rintro _ _ ⟨⟩) hd

theorem unbinds_iterE_list {env : Env} {e : Exp} {ds : List Dom} {y : IL.Id}
    (hd : UnbindsAll env (ds.map domSrc) y) : Unbinds env (.iterE e (.mk .list ds)) y :=
  unbinds_iterE (by rintro _ _ ⟨⟩) hd

theorem unbinds_iterE_listN {env : Env} {e eₙ : Exp} {ido : Option IL.Id}
    {ds : List Dom} {y : IL.Id} (hn : Unbinds env eₙ y)
    (hd : UnbindsAll env (ds.map domSrc) y) :
    Unbinds env (.iterE e (.mk (.listN eₙ ido) ds)) y :=
  unbinds_iterE (by
    rintro a b h
    injection h with h₁ h₂
    exact h₁ ▸ hn) hd


/-- A `CallE` is not a pattern either: `matchDefault` evaluates it and
compares.  This is the case the whole section turns on. -/
theorem unbinds_callE {env : Env} {f : IL.Id} {args : List Arg} {y : IL.Id} :
    Unbinds env (.callE f args) y := by
  rintro ρ σ v hy hm
  obtain ⟨-, rfl⟩ := ExecDefault.matchExp_callE_iff.1 hm
  exact hy

/-- `e?` over one domain. -/
theorem unbinds_iterE_opt1 {env : Env} {e : Exp} {x d y : IL.Id} (hd : d ≠ "_")
    (hdy : d ≠ y) : Unbinds env (.iterE e (.mk .opt [.mk x (.varE d)])) y := by
  refine unbinds_iterE_opt ?_
  show UnbindsAll env [Exp.varE d] y
  exact unbindsAll_cons (unbinds_varE hd hdy) unbindsAll_nil

/-- `e*` over one domain. -/
theorem unbinds_iterE_list1 {env : Env} {e : Exp} {x d y : IL.Id} (hd : d ≠ "_")
    (hdy : d ≠ y) : Unbinds env (.iterE e (.mk .list [.mk x (.varE d)])) y := by
  refine unbinds_iterE_list ?_
  show UnbindsAll env [Exp.varE d] y
  exact unbindsAll_cons (unbinds_varE hd hdy) unbindsAll_nil

/-- `e^n` with no domain at all — the shape `array.new_default` uses: the
counter is the only thing that can bind. -/
theorem unbinds_iterE_listN0 {env : Env} {e : Exp} {c y : IL.Id} {ido : Option IL.Id}
    (hc : c ≠ "_") (hcy : c ≠ y) :
    Unbinds env (.iterE e (.mk (.listN (.varE c) ido) [])) y :=
  unbinds_iterE_listN (unbinds_varE hc hcy) unbindsAll_nil

/-- `e^n` over one domain. -/
theorem unbinds_iterE_listN1 {env : Env} {e : Exp} {c x d y : IL.Id}
    {ido : Option IL.Id} (hc : c ≠ "_") (hcy : c ≠ y) (hd : d ≠ "_") (hdy : d ≠ y) :
    Unbinds env (.iterE e (.mk (.listN (.varE c) ido) [.mk x (.varE d)])) y := by
  refine unbinds_iterE_listN (unbinds_varE hc hcy) ?_
  show UnbindsAll env [Exp.varE d] y
  exact unbindsAll_cons (unbinds_varE hd hdy) unbindsAll_nil

/-- Discharge `Unbinds` for a conclusion built from the formers the aggregate
rules use.  There is deliberately no case for `DotE`, `IdxE` or `LenE`, and
the `CallE` case *closes* the goal rather than recursing: a variable reachable
only through one of those is never bound. -/
macro "unbindsAgg" : tactic => `(tactic|
  repeat' first
    | exact unbindsAll_nil
    | exact unbinds_varE (by decide) (by decide)
    | exact unbinds_binE
    | exact unbinds_callE
    | exact unbinds_iterE_opt1 (by decide) (by decide)
    | exact unbinds_iterE_list1 (by decide) (by decide)
    | exact unbinds_iterE_listN0 (by decide) (by decide)
    | exact unbinds_iterE_listN1 (by decide) (by decide) (by decide) (by decide)
    | apply unbinds_caseE
    | apply unbinds_tupE
    | apply unbinds_listE
    | apply unbinds_subE
    | apply unbinds_cvtE
    | apply unbinds_catE
    | apply unbindsAll_cons)

/-! ## Seven more rules that cannot fire

`struct.new_default`, `struct.get-struct`, `array.new_default`,
`array.new_data-num`, `array.copy-le`, `array.copy-gt` and
`array.init_data-num` all carry an `Expand` premise naming a `mut?`/`zt` pair,
and in every one of them at least one of the pair is a variable the
*conclusion* never binds.  `scripts/spectec_unbound_vars.py Step_read` lists
them; `unbindsAgg` proves it; and a `RulePr` evaluates the instance it asserts
(`Validation.premHolds_rule_iff`) rather than matching it, so the premise
cannot introduce the missing variable — it needs it already bound.

That settles the last ten of the thirty-four aggregate rules: seven fire on
nothing, and the remaining three (`array.new_elem-alloc`, `array.fill-succ`
and `array.init_elem-succ`) are characterised below.

As with `array.new_data-oob` above, this is a finding about the *pinned IL*,
not about the paper rule: SpecTec's own frontend reduces a rule through
`il2al`, whose `translate.ml` turns such a premise into an assignment.  Of the
103 `Step_read` rules, 21 name a variable nothing binds; 10 of them are
aggregate rules and all 10 are now settled. -/

/-- An `else` on its own holds and changes nothing. -/
theorem premHolds_elsePr_iff {env : Env} {ρ ρ' : VarEnv} :
    PremHolds env ρ .elsePr ρ' ↔ ρ' = ρ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [premHolds] at hn
    | succ n => simp only [premHolds, Except.ok.injEq] at hn; exact hn.symm
  · rintro rfl
    exact ⟨1, by simp [premHolds]⟩

/-- **An iteration whose *leading* domain is unbound has no value.**  The
generalisation of `ExecReadControl.not_evalExp_iterE_of_unbound` the `STRUCT`
expansion needs: it ranges over two domains, `mut?*` and `zt*`. -/
theorem not_evalExp_iterE_of_unboundHead {env : Env} {ρ : VarEnv} {e : Exp} {it : Iter}
    {x y : IL.Id} {ds : List Dom} {v : Value} (hy : ρ.findVal? y = none) :
    ¬ EvalExp env ρ (.iterE e (.mk it (.mk x (.varE y) :: ds))) v := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [evalExp] at hn
  | succ n =>
      simp only [evalExp] at hn
      cases n with
      | zero => cases it <;> simp [evalIterE] at hn
      | succ m =>
          have hd : ∀ xvs, evalDoms m env ρ (.mk x (.varE y) :: ds) ≠ .ok xvs := by
            intro xvs hc
            cases m with
            | zero => simp [evalDoms] at hc
            | succ m' =>
                rw [evalDoms] at hc
                simp only [List.mapM_cons, domVar, domSrc] at hc
                cases hy' : evalExp m' env ρ (.varE y) with
                | ok u => exact Execution.evalExp_varE_ne_ok hy hy'
                | error er =>
                    rw [hy'] at hc
                    simp [Bind.bind, Except.bind, Functor.map, Except.map] at hc
          cases it <;>
            · simp only [evalIterE] at hn
              obtain ⟨xvs, h₁, -⟩ := Res.bind_eq_ok.1 hn
              exact hd xvs h₁

/-- The `Expand … ~~ STRUCT (%((mut? zt)*))` premise cannot hold where the
field iteration's domains are unbound. -/
theorem premHolds_expandStruct_needs_doms {env : Env} {ρ ρ' : VarEnv} {e eb : Exp}
    {x y : IL.Id} {ds : List Dom} (hy : ρ.findVal? y = none) :
    ¬ PremHolds env ρ (.rulePr "Expand" [] "%~~%"
      (.tupE [e, .caseE "STRUCT" (.caseE "%" (.tupE
        [.iterE eb (.mk .list (.mk x (.varE y) :: ds))]))])) ρ' := by
  intro h
  obtain ⟨-, ws, w, -, hw, -⟩ := Validation.premHolds_rule_iff.1 h
  obtain ⟨vs, hvs, -⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨-, qs, -, -, hq⟩ := Validation.evalExps_cons_iff.1 hvs
  obtain ⟨u, -, -, hu, -⟩ := Validation.evalExps_cons_iff.1 hq
  obtain ⟨u₁, hu₁, -⟩ := evalExp_caseE_iff.1 hu
  obtain ⟨u₂, hu₂, -⟩ := evalExp_caseE_iff.1 hu₁
  obtain ⟨vs₂, hvs₂, -⟩ := evalExp_tupE_iff.1 hu₂
  obtain ⟨u₃, -, -, hu₃, -⟩ := Validation.evalExps_cons_iff.1 hvs₂
  exact not_evalExp_iterE_of_unboundHead hy hu₃

/-- **`Step_read/struct.new_default` fires on nothing.**  Its conclusion binds
`z`, `x` and `val*`; the `Expand` premise needs `mut?*` and `zt*`. -/
theorem ruleFires_structNewDefault_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v structNewDefaultRule := by
  unfold structNewDefaultRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hσ : σ.findVal? "mut?*" = none :=
    (show Unbinds env _ "mut?*" by unbindsAgg) _ _ _ (by simp) hl
  have hρ : ρ₁.findVal? "mut?*" = none :=
    (show Unbinds env _ "mut?*" by unbindsAgg) _ _ _ hσ hr
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  exact premHolds_expandStruct_needs_doms hρ hpr

/-- **`Step_read/struct.get-struct` fires on nothing.**  Its right-hand side
is a bare `$unpackfield_(…)`, which binds nothing at all, so neither `mut?*`
nor `zt*` is ever in scope when the `Expand` premise runs. -/
theorem ruleFires_structGetStruct_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v structGetStructRule := by
  unfold structGetStructRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hσ : σ.findVal? "mut?*" = none :=
    (show Unbinds env _ "mut?*" by unbindsAgg) _ _ _ (by simp) hl
  have hρ : ρ₁.findVal? "mut?*" = none :=
    (show Unbinds env _ "mut?*" by unbindsAgg) _ _ _ hσ hr
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  exact premHolds_expandStruct_needs_doms hρ hpr

/-- **`Step_read/array.new_default` fires on nothing.**  Neither `mut?` nor
`zt` occurs in its conclusion: the `val^n` it builds has *no* domain, so the
iteration binds only through its counter. -/
theorem ruleFires_arrayNewDefault_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayNewDefaultRule := by
  unfold arrayNewDefaultRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hσ : σ.findVal? "zt" = none :=
    (show Unbinds env _ "zt" by unbindsAgg) _ _ _ (by simp) hl
  have hρ : ρ₁.findVal? "zt" = none :=
    (show Unbinds env _ "zt" by unbindsAgg) _ _ _ hσ hr
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  exact premHolds_expandArray_needs_zt hρ hpr

/-- **`Step_read/array.new_data-num` fires on nothing.**  `zt` is read by the
`$cunpack`/`$cunpacknum_` calls in the conclusion and by the `Expand` premise,
and bound by neither. -/
theorem ruleFires_arrayNewDataNum_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayNewDataNumRule := by
  unfold arrayNewDataNumRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hσ : σ.findVal? "zt" = none :=
    (show Unbinds env _ "zt" by unbindsAgg) _ _ _ (by simp) hl
  have hρ : ρ₁.findVal? "zt" = none :=
    (show Unbinds env _ "zt" by unbindsAgg) _ _ _ hσ hr
  obtain ⟨κ, hpr, -⟩ := Validation.premsHold_cons_iff.1 hp
  exact premHolds_expandArray_needs_zt hρ hpr

/-- **`Step_read/array.copy-le` fires on nothing.**  Its conclusion is a
perfectly ordinary eleven-instruction right-hand side — the arithmetic and the
`sx?` iteration in it bind nothing beyond what the left-hand side already
bound — and `zt_2` is named only by the `Expand` premise. -/
theorem ruleFires_arrayCopyLe_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayCopyLeRule := by
  unfold arrayCopyLeRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hσ : σ.findVal? "zt_2" = none :=
    (show Unbinds env _ "zt_2" by unbindsAgg) _ _ _ (by simp) hl
  have hρ : ρ₁.findVal? "zt_2" = none :=
    (show Unbinds env _ "zt_2" by unbindsAgg) _ _ _ hσ hr
  obtain ⟨κ, helse, hrest⟩ := Validation.premsHold_cons_iff.1 hp
  obtain rfl := premHolds_elsePr_iff.1 helse
  obtain ⟨κ₂, hpr, -⟩ := Validation.premsHold_cons_iff.1 hrest
  exact premHolds_expandArray_needs_zt hρ hpr

/-- **`Step_read/array.copy-gt` fires on nothing**, for the same reason as
`array.copy-le`. -/
theorem ruleFires_arrayCopyGt_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayCopyGtRule := by
  unfold arrayCopyGtRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hσ : σ.findVal? "zt_2" = none :=
    (show Unbinds env _ "zt_2" by unbindsAgg) _ _ _ (by simp) hl
  have hρ : ρ₁.findVal? "zt_2" = none :=
    (show Unbinds env _ "zt_2" by unbindsAgg) _ _ _ hσ hr
  obtain ⟨κ, helse, hrest⟩ := Validation.premsHold_cons_iff.1 hp
  obtain rfl := premHolds_elsePr_iff.1 helse
  obtain ⟨κ₂, hpr, -⟩ := Validation.premsHold_cons_iff.1 hrest
  exact premHolds_expandArray_needs_zt hρ hpr

/-- **`Step_read/array.init_data-num` fires on nothing.**  `zt` is read by the
`$const($cunpack(zt), …)` its right-hand side pushes and by the `Expand`
premise; nothing binds it. -/
theorem ruleFires_arrayInitDataNum_never {env : Env} {v : Value} :
    ¬ RuleFires env "%~>%" [] [] v arrayInitDataNumRule := by
  unfold arrayInitDataNumRule
  rw [ruleFires_nil_iff]
  rintro ⟨ρ₁, ρ₂, hm, hp⟩
  obtain ⟨a, b, σ, rfl, hl, hr⟩ := matchExp_concl_iff.1 hm
  have hσ : σ.findVal? "zt" = none :=
    (show Unbinds env _ "zt" by unbindsAgg) _ _ _ (by simp) hl
  have hρ : ρ₁.findVal? "zt" = none :=
    (show Unbinds env _ "zt" by unbindsAgg) _ _ _ hσ hr
  obtain ⟨κ, helse, hrest⟩ := Validation.premsHold_cons_iff.1 hp
  obtain rfl := premHolds_elsePr_iff.1 helse
  obtain ⟨κ₂, hpr, -⟩ := Validation.premsHold_cons_iff.1 hrest
  exact premHolds_expandArray_needs_zt hρ hpr

/-! ## The three rules that do fire

`array.fill-succ`, `array.init_elem-succ` and `array.new_elem-alloc` are the
only ones of the ten whose variables are all bound by the conclusion.  Their
right-hand sides compute, so — exactly as in `Equiv/ExecReadTable.lean`'s
`table.fill-succ` — the arithmetic is what constrains the configuration, and
the `else` that looks like a guard constrains nothing. -/

/-- `(CONST I32 e)` for an arbitrary payload pattern `e`. -/
theorem matchExp_constI32E_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} {v : Value} :
    MatchExp env ρ (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []), e])) v ρ' ↔
      ∃ c, v = Execution.constV Execution.i32V c ∧ MatchExp env ρ e c ρ' := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨nt, c, σ, rfl, hnt, hc⟩ := matchExps_two_iff.1 hws
    rw [matchExp_caseNil_iff] at hnt
    obtain ⟨rfl, rfl⟩ := hnt
    exact ⟨c, rfl, hc⟩
  · rintro ⟨c, rfl, hc⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_caseNil_iff.2 ⟨rfl, rfl⟩, hc⟩⟩⟩

/-- A one-argument injection around an already-bound variable: it *tests*. -/
theorem matchExp_caseBound_iff {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {x : IL.Id}
    {v w : Value} (hx : ρ.findVal? x = some w) :
    MatchExp env ρ (.caseE op (.varE x)) v ρ' ↔ v = .case op w ∧ ρ' = ρ := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨u, rfl, hu⟩
    obtain ⟨rfl, rfl⟩ := (matchExp_boundVar_iff hx).1 hu
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩⟩

/-- The scope `array.fill-succ`'s left-hand side builds. -/
def fillSuccScope (z av i val nv x : Value) : VarEnv :=
  ((((((VarEnv.empty.bindVal "z" z).bindVal "a" av).bindVal "i" i).bindVal
    "val" val).bindVal "n" nv).bindVal "x" x)

/-- The nine-instruction right-hand side of `array.fill-succ`.  Nothing in it
binds, so the scope comes out unchanged; the two computed indices are exactly
`ExecReadTable`'s `succPct` and `predPct`. -/
theorem matchExps_arrayFillSuccRhs_iff {env : Env} {ρ ρ' : VarEnv} {tc td : Typ}
    {av i val nv x : Value} {vs : List Value}
    (ha : ρ.findVal? "a" = some av) (hi : ρ.findVal? "i" = some i)
    (hval : ρ.findVal? "val" = some val) (hn : ρ.findVal? "n" = some nv)
    (hx : ρ.findVal? "x" = some x) :
    MatchExps env ρ
      [.caseE "REF.ARRAY_ADDR" (.varE "a"),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]),
       .subE (.varE "val") tc td,
       .caseE "ARRAY.SET" (.varE "x"),
       .caseE "REF.ARRAY_ADDR" (.varE "a"),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
         .caseE "%" (.tupE [.binE .addOp (.numT .natT)
           (.projE (.uncaseE (.varE "i") "%") 0) (.numE (.natN 1))])]),
       .subE (.varE "val") tc td,
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
         .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
           (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
           .intT .natT])]),
       .caseE "ARRAY.FILL" (.varE "x")] vs ρ' ↔
      ∃ k us mn m,
        i = .case "%" (.tuple (.num (.natN k) :: us)) ∧ nv = .num mn ∧
        ExecReadTable.PredPair mn m ∧
        vs = [.case "REF.ARRAY_ADDR" av, Execution.constV Execution.i32V i, val,
              .case "ARRAY.SET" x, .case "REF.ARRAY_ADDR" av,
              Execution.constV Execution.i32V (Execution.pctV (k + 1)), val,
              Execution.constV Execution.i32V (.case "%" (.tuple [.num m])),
              .case "ARRAY.FILL" x] ∧
        ρ' = ρ := by
  constructor
  · intro h
    obtain ⟨w1, ws1, σ1, rfl, h1, t1⟩ := Validation.matchExps_cons_iff.1 h
    rw [matchExp_caseBound_iff ha] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨w2, ws2, σ2, rfl, h2, t2⟩ := Validation.matchExps_cons_iff.1 t1
    obtain ⟨c2, rfl, hc2⟩ := matchExp_constI32E_iff.1 h2
    obtain ⟨rfl, rfl⟩ := (matchExp_boundVar_iff hi).1 hc2
    obtain ⟨w3, ws3, σ3, rfl, h3, t3⟩ := Validation.matchExps_cons_iff.1 t2
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hval] at h3
    obtain ⟨rfl, rfl⟩ := h3
    obtain ⟨w4, ws4, σ4, rfl, h4, t4⟩ := Validation.matchExps_cons_iff.1 t3
    rw [matchExp_caseBound_iff hx] at h4
    obtain ⟨rfl, rfl⟩ := h4
    obtain ⟨w5, ws5, σ5, rfl, h5, t5⟩ := Validation.matchExps_cons_iff.1 t4
    rw [matchExp_caseBound_iff ha] at h5
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨w6, ws6, σ6, rfl, h6, t6⟩ := Validation.matchExps_cons_iff.1 t5
    obtain ⟨c6, rfl, hc6⟩ := matchExp_constI32E_iff.1 h6
    rw [ExecReadTable.matchExp_succPct_iff hi] at hc6
    obtain ⟨k, us, hik, rfl, rfl⟩ := hc6
    obtain ⟨w7, ws7, σ7, rfl, h7, t7⟩ := Validation.matchExps_cons_iff.1 t6
    rw [Validation.matchExp_sub_iff, matchExp_boundVar_iff hval] at h7
    obtain ⟨rfl, rfl⟩ := h7
    obtain ⟨w8, ws8, σ8, rfl, h8, t8⟩ := Validation.matchExps_cons_iff.1 t7
    obtain ⟨c8, rfl, hc8⟩ := matchExp_constI32E_iff.1 h8
    rw [ExecReadTable.matchExp_predPct_iff hn] at hc8
    obtain ⟨mn, m, hnv, rfl, hpred, rfl⟩ := hc8
    obtain ⟨w9, ws9, σ9, rfl, h9, t9⟩ := Validation.matchExps_cons_iff.1 t8
    rw [matchExp_caseBound_iff hx] at h9
    obtain ⟨rfl, rfl⟩ := h9
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 t9
    exact ⟨k, us, mn, m, hik, hnv, hpred, rfl, rfl⟩
  · rintro ⟨k, us, mn, m, hik, hnv, hpred, rfl, rfl⟩
    refine Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ', rfl, ?_,
        Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · exact (matchExp_caseBound_iff ha).2 ⟨rfl, rfl⟩
    · exact matchExp_constI32E_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hi).2 ⟨rfl, rfl⟩⟩
    · exact Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hval).2 ⟨rfl, rfl⟩)
    · exact (matchExp_caseBound_iff hx).2 ⟨rfl, rfl⟩
    · exact (matchExp_caseBound_iff ha).2 ⟨rfl, rfl⟩
    · exact matchExp_constI32E_iff.2 ⟨_, rfl,
        (ExecReadTable.matchExp_succPct_iff hi).2 ⟨k, us, hik, rfl, rfl⟩⟩
    · exact Validation.matchExp_sub_iff.2 ((matchExp_boundVar_iff hval).2 ⟨rfl, rfl⟩)
    · exact matchExp_constI32E_iff.2 ⟨_, rfl,
        (ExecReadTable.matchExp_predPct_iff hn).2 ⟨mn, m, hnv, rfl, hpred, rfl⟩⟩
    · exact (matchExp_caseBound_iff hx).2 ⟨rfl, rfl⟩

/-- **`Step_read/array.fill-succ`, characterised exactly.**

The only premise is `else`, which holds unconditionally, so the `n ≠ 0` guard
the rule appears to carry comes entirely from its right-hand side — and, as in
`table.fill-succ`, that guard is weaker than it looks.  `$(n - 1 : nat)` sits
in a *matched* position, and `matchExp`'s `CvtE` clause only asks that the
residual numeral convert to `n - 1` as an `int`, which is what
`ExecReadTable.PredPair` says.  So `array.fill-succ` fires at `n = 0` too,
with `-1` written as an `int` numeral, and at an `n` that is not a `nat`
numeral at all.

What the conclusion *does* force is the index: `$(i!%.0 + 1)` is evaluated, so
`i` has to be a `%`-injection whose first component is a `nat`.  The address
`a`, the value `val` and the type index `x` stay arbitrary — nothing in the
rule inspects them, and in particular the array at `a` is never read. -/
theorem ruleFires_arrayFillSucc_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayFillSuccRule ↔
      ∃ z av k us val mn m x,
        v = .tuple
          [ExecStep.configV z
             [.case "REF.ARRAY_ADDR" av,
              Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN k) :: us))),
              val,
              Execution.constV Execution.i32V (.case "%" (.tuple [.num mn])),
              .case "ARRAY.FILL" x],
           .list
             [.case "REF.ARRAY_ADDR" av,
              Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN k) :: us))),
              val, .case "ARRAY.SET" x, .case "REF.ARRAY_ADDR" av,
              Execution.constV Execution.i32V (Execution.pctV (k + 1)), val,
              Execution.constV Execution.i32V (.case "%" (.tuple [.num m])),
              .case "ARRAY.FILL" x]] ∧
        ExecReadTable.PredPair mn m := by
  unfold arrayFillSuccRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, -⟩
    obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_subVar_iff (by simp)] at hc
    subst hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨nv, rfl, rfl⟩ := hd
    rw [matchExp_caseVar_iff (by simp)] at he
    obtain ⟨x, rfl, rfl⟩ := he
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    rw [matchExps_arrayFillSuccRhs_iff (av := av) (i := i) (val := c) (nv := nv) (x := x)
      (by simp) (by simp) (by simp) (by simp) (by simp)] at hbvs
    obtain ⟨k, us, mn, m, rfl, rfl, hpred, rfl, rfl⟩ := hbvs
    exact ⟨z, av, k, us, c, mn, m, x, rfl, hpred⟩
  · rintro ⟨z, av, k, us, val, mn, m, x, rfl, hpred⟩
    refine ⟨fillSuccScope z av (.case "%" (.tuple (.num (.natN k) :: us))) val (.num mn) x,
      fillSuccScope z av (.case "%" (.tuple (.num (.natN k) :: us))) val (.num mn) x,
      matchExp_readConcl_iff.2 ⟨z, _, _,
        fillSuccScope z av (.case "%" (.tuple (.num (.natN k) :: us))) val (.num mn) x,
        rfl, ?_, ?_⟩, ExecRef.premsHold_else_iff.2 rfl⟩
    · exact matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_subVar_iff (by simp)).2 rfl,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        (matchExps_arrayFillSuccRhs_iff (by simp [fillSuccScope]) (by simp [fillSuccScope])
          (by simp [fillSuccScope]) (by simp [fillSuccScope])
          (by simp [fillSuccScope])).2 ⟨k, us, mn, m, rfl, rfl, hpred, rfl, rfl⟩⟩

/-- The scope `array.init_elem-succ`'s left-hand side builds. -/
def initElemLhsScope (z av i j nv x y : Value) : VarEnv :=
  (((((((VarEnv.empty.bindVal "z" z).bindVal "a" av).bindVal "i" i).bindVal
    "j" j).bindVal "n" nv).bindVal "x" x).bindVal "y" y)

/-- An index into a value is an index into a *list*. -/
theorem idx?_eq_some_list {w u : Value} {q : Nat} (h : w.idx? q = some u) :
    ∃ refs : List Value, w = .list refs ∧ refs[q]? = some u := by
  cases w with
  | list refs => exact ⟨refs, rfl, h⟩
  | num _ => simp [Value.idx?] at h
  | bool _ => simp [Value.idx?] at h
  | text _ => simp [Value.idx?] at h
  | tuple _ => simp [Value.idx?] at h
  | case _ _ => simp [Value.idx?] at h
  | struct _ => simp [Value.idx?] at h
  | opt _ => simp [Value.idx?] at h

/-- The nine-instruction right-hand side of `array.init_elem-succ`.  Unlike
`array.fill-succ`'s it *binds*: the reference it pushes is a fresh `ref`, which
only the premise then constrains. -/
theorem matchExps_arrayInitElemSuccRhs_iff {env : Env} {ρ ρ' : VarEnv} {tc td : Typ}
    {av i j nv x y : Value} {vs : List Value}
    (ha : ρ.findVal? "a" = some av) (hi : ρ.findVal? "i" = some i)
    (hj : ρ.findVal? "j" = some j) (hn : ρ.findVal? "n" = some nv)
    (hx : ρ.findVal? "x" = some x) (hy : ρ.findVal? "y" = some y)
    (hrf : ρ.findVal? "ref" = none) :
    MatchExps env ρ
      [.caseE "REF.ARRAY_ADDR" (.varE "a"),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []), .varE "i"]),
       .subE (.varE "ref") tc td,
       .caseE "ARRAY.SET" (.varE "x"),
       .caseE "REF.ARRAY_ADDR" (.varE "a"),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
         .caseE "%" (.tupE [.binE .addOp (.numT .natT)
           (.projE (.uncaseE (.varE "i") "%") 0) (.numE (.natN 1))])]),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
         .caseE "%" (.tupE [.binE .addOp (.numT .natT)
           (.projE (.uncaseE (.varE "j") "%") 0) (.numE (.natN 1))])]),
       .caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
         .caseE "%" (.tupE [.cvtE (.binE .subOp (.numT .intT)
           (.cvtE (.varE "n") .natT .intT) (.cvtE (.numE (.natN 1)) .natT .intT))
           .intT .natT])]),
       .caseE "ARRAY.INIT_ELEM" (.tupE [.varE "x", .varE "y"])] vs ρ' ↔
      ∃ ref p us q ws mn m,
        i = .case "%" (.tuple (.num (.natN p) :: us)) ∧
        j = .case "%" (.tuple (.num (.natN q) :: ws)) ∧ nv = .num mn ∧
        ExecReadTable.PredPair mn m ∧
        vs = [.case "REF.ARRAY_ADDR" av, Execution.constV Execution.i32V i, ref,
              .case "ARRAY.SET" x, .case "REF.ARRAY_ADDR" av,
              Execution.constV Execution.i32V (Execution.pctV (p + 1)),
              Execution.constV Execution.i32V (Execution.pctV (q + 1)),
              Execution.constV Execution.i32V (.case "%" (.tuple [.num m])),
              .case "ARRAY.INIT_ELEM" (.tuple [x, y])] ∧
        ρ' = ρ.bindVal "ref" ref := by
  have ha' : ∀ u : Value, (ρ.bindVal "ref" u).findVal? "a" = some av := fun _ => by simp [ha]
  have hi' : ∀ u : Value, (ρ.bindVal "ref" u).findVal? "i" = some i := fun _ => by simp [hi]
  have hj' : ∀ u : Value, (ρ.bindVal "ref" u).findVal? "j" = some j := fun _ => by simp [hj]
  have hn' : ∀ u : Value, (ρ.bindVal "ref" u).findVal? "n" = some nv := fun _ => by simp [hn]
  have hx' : ∀ u : Value, (ρ.bindVal "ref" u).findVal? "x" = some x := fun _ => by simp [hx]
  have hy' : ∀ u : Value, (ρ.bindVal "ref" u).findVal? "y" = some y := fun _ => by simp [hy]
  constructor
  · intro h
    obtain ⟨w1, ws1, σ1, rfl, h1, t1⟩ := Validation.matchExps_cons_iff.1 h
    rw [matchExp_caseBound_iff ha] at h1
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨w2, ws2, σ2, rfl, h2, t2⟩ := Validation.matchExps_cons_iff.1 t1
    obtain ⟨c2, rfl, hc2⟩ := matchExp_constI32E_iff.1 h2
    obtain ⟨rfl, rfl⟩ := (matchExp_boundVar_iff hi).1 hc2
    obtain ⟨w3, ws3, σ3, rfl, h3, t3⟩ := Validation.matchExps_cons_iff.1 t2
    rw [matchExp_subVar_iff hrf] at h3
    subst h3
    obtain ⟨w4, ws4, σ4, rfl, h4, t4⟩ := Validation.matchExps_cons_iff.1 t3
    rw [matchExp_caseBound_iff (hx' _)] at h4
    obtain ⟨rfl, rfl⟩ := h4
    obtain ⟨w5, ws5, σ5, rfl, h5, t5⟩ := Validation.matchExps_cons_iff.1 t4
    rw [matchExp_caseBound_iff (ha' _)] at h5
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨w6, ws6, σ6, rfl, h6, t6⟩ := Validation.matchExps_cons_iff.1 t5
    obtain ⟨c6, rfl, hc6⟩ := matchExp_constI32E_iff.1 h6
    rw [ExecReadTable.matchExp_succPct_iff (hi' _)] at hc6
    obtain ⟨p, us, hip, rfl, rfl⟩ := hc6
    obtain ⟨w7, ws7, σ7, rfl, h7, t7⟩ := Validation.matchExps_cons_iff.1 t6
    obtain ⟨c7, rfl, hc7⟩ := matchExp_constI32E_iff.1 h7
    rw [ExecReadTable.matchExp_succPct_iff (hj' _)] at hc7
    obtain ⟨q, wss, hjq, rfl, rfl⟩ := hc7
    obtain ⟨w8, ws8, σ8, rfl, h8, t8⟩ := Validation.matchExps_cons_iff.1 t7
    obtain ⟨c8, rfl, hc8⟩ := matchExp_constI32E_iff.1 h8
    rw [ExecReadTable.matchExp_predPct_iff (hn' _)] at hc8
    obtain ⟨mn, m, hnv, rfl, hpred, rfl⟩ := hc8
    obtain ⟨w9, ws9, σ9, rfl, h9, t9⟩ := Validation.matchExps_cons_iff.1 t8
    rw [ExecReadTable.matchExp_twoIdxBound_iff (hx' _) (hy' _)] at h9
    obtain ⟨rfl, rfl⟩ := h9
    obtain ⟨rfl, rfl⟩ := Validation.matchExps_nil_iff.1 t9
    exact ⟨w3, p, us, q, wss, mn, m, hip, hjq, hnv, hpred, rfl, rfl⟩
  · rintro ⟨ref, p, us, q, ws, mn, m, hip, hjq, hnv, hpred, rfl, rfl⟩
    refine Validation.matchExps_cons_iff.2 ⟨_, _, ρ, rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ, rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ.bindVal "ref" ref, rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ.bindVal "ref" ref, rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ.bindVal "ref" ref, rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ.bindVal "ref" ref, rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ.bindVal "ref" ref, rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ.bindVal "ref" ref, rfl, ?_,
      Validation.matchExps_cons_iff.2 ⟨_, _, ρ.bindVal "ref" ref, rfl, ?_,
        Validation.matchExps_nil_iff.2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    · exact (matchExp_caseBound_iff ha).2 ⟨rfl, rfl⟩
    · exact matchExp_constI32E_iff.2 ⟨_, rfl, (matchExp_boundVar_iff hi).2 ⟨rfl, rfl⟩⟩
    · exact (matchExp_subVar_iff hrf).2 rfl
    · exact (matchExp_caseBound_iff (hx' ref)).2 ⟨rfl, rfl⟩
    · exact (matchExp_caseBound_iff (ha' ref)).2 ⟨rfl, rfl⟩
    · exact matchExp_constI32E_iff.2 ⟨_, rfl,
        (ExecReadTable.matchExp_succPct_iff (hi' ref)).2 ⟨p, us, hip, rfl, rfl⟩⟩
    · exact matchExp_constI32E_iff.2 ⟨_, rfl,
        (ExecReadTable.matchExp_succPct_iff (hj' ref)).2 ⟨q, ws, hjq, rfl, rfl⟩⟩
    · exact matchExp_constI32E_iff.2 ⟨_, rfl,
        (ExecReadTable.matchExp_predPct_iff (hn' ref)).2 ⟨mn, m, hnv, rfl, hpred, rfl⟩⟩
    · exact (ExecReadTable.matchExp_twoIdxBound_iff (hx' ref) (hy' ref)).2 ⟨rfl, rfl⟩

/-- The premises of `array.init_elem-succ`: a vacuous `else`, and the side
condition `ref = $elem(z, y).REFS[j!%.0]` — which is the *only* thing in the
rule that reads the state. -/
theorem premsHold_initElemSucc_iff {env : Env} {ρ ρ' : VarEnv} {z y j ref : Value}
    (hz : ρ.findVal? "z" = some z) (hy : ρ.findVal? "y" = some y)
    (hj : ρ.findVal? "j" = some j) (hr : ρ.findVal? "ref" = some ref)
    (hd : ρ.findDef? "elem" = none) :
    PremsHold env ρ
      [.elsePr,
       .ifPr (.cmpE .eqOp .boolT (.varE "ref")
         (.idxE (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE "y")]) "REFS")
           (.projE (.uncaseE (.varE "j") "%") 0)))] ρ' ↔
      ρ' = ρ ∧ ∃ (q : Nat) (rest refs : List Value),
        j = .case "%" (.tuple (.num (.natN q) :: rest)) ∧
        ElemRefs env z y refs ∧ refs[q]? = some ref := by
  rw [ExecRef.premsHold_elseIf_iff]
  constructor
  · rintro ⟨rfl, hev⟩
    obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_varE_iff, hr, Option.some.injEq] at h₁
    subst h₁
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hc
    obtain ⟨w, q, hw, hq, hidx⟩ := evalExp_idxE_iff.1 h₂
    obtain ⟨rest, hjj⟩ := evalExp_pctProj_iff.1 hq
    rw [hj, Option.some.injEq] at hjj
    obtain ⟨refs, rfl, hsel⟩ := idx?_eq_some_list hidx
    exact ⟨rfl, q, rest, refs, hjj,
      (evalExp_elemRefs_iff (zx := "z") (yx := "y") hz hy hd).1 hw, hsel⟩
  · rintro ⟨rfl, q, rest, refs, hjj, her, hsel⟩
    refine ⟨rfl, evalExp_cmpE_iff.2 ⟨ref, ref, evalExp_varE_iff.2 hr, ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩
    refine evalExp_idxE_iff.2 ⟨.list refs, q,
      (evalExp_elemRefs_iff (zx := "z") (yx := "y") hz hy hd).2 her, ?_, hsel⟩
    exact evalExp_pctProj_iff.2 ⟨rest, by rw [hj, hjj]⟩

/-- **`Step_read/array.init_elem-succ`, characterised exactly.**

Both index operands are forced to be `%`-injections over a `nat` — `i` by
`$(i!%.0 + 1)` in the right-hand side, `j` by `$(j!%.0 + 1)` there *and* by the
premise's `$elem(z, y).REFS[j!%.0]`.  The count is not: as in `array.fill-succ`
the residual `$(n - 1 : nat)` only has to *convert* to `n - 1` as an `int`, so
the rule fires at `n = 0` as well.

The array address `av` and the type index `x` are never inspected: the rule
reads the *element segment* `y`, not the array.  `ElemRefs` keeps `$elem`
abstract. -/
theorem ruleFires_arrayInitElemSucc_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayInitElemSuccRule ↔
      ∃ z av p us q ws mn m x y refs ref,
        v = .tuple
          [ExecStep.configV z
             [.case "REF.ARRAY_ADDR" av,
              Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: us))),
              Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN q) :: ws))),
              Execution.constV Execution.i32V (.case "%" (.tuple [.num mn])),
              .case "ARRAY.INIT_ELEM" (.tuple [x, y])],
           .list
             [.case "REF.ARRAY_ADDR" av,
              Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: us))),
              ref, .case "ARRAY.SET" x, .case "REF.ARRAY_ADDR" av,
              Execution.constV Execution.i32V (Execution.pctV (p + 1)),
              Execution.constV Execution.i32V (Execution.pctV (q + 1)),
              Execution.constV Execution.i32V (.case "%" (.tuple [.num m])),
              .case "ARRAY.INIT_ELEM" (.tuple [x, y])]] ∧
        ExecReadTable.PredPair mn m ∧ ElemRefs env z y refs ∧ refs[q]? = some ref := by
  unfold arrayInitElemSuccRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨a, b, c, d, e, τ, υ, φ, χ, rfl, ha, hb, hc, hd, he⟩ := matchExps_five_iff.1 hms
    rw [matchExp_caseVar_iff (by simp)] at ha
    obtain ⟨av, rfl, rfl⟩ := ha
    rw [matchExp_constI32Var_iff (by simp)] at hb
    obtain ⟨i, rfl, rfl⟩ := hb
    rw [matchExp_constI32Var_iff (by simp)] at hc
    obtain ⟨j, rfl, rfl⟩ := hc
    rw [matchExp_constI32Pct_iff (by simp)] at hd
    obtain ⟨nv, rfl, rfl⟩ := hd
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by decide) (by decide)] at he
    obtain ⟨x, y, rfl, rfl⟩ := he
    obtain ⟨bvs, rfl, hbvs⟩ := Validation.matchExp_list_iff.1 hr
    rw [matchExps_arrayInitElemSuccRhs_iff (av := av) (i := i) (j := j) (nv := nv)
      (x := x) (y := y) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp)] at hbvs
    obtain ⟨ref, p, us, q, wss, mn, m, rfl, rfl, rfl, hpred, rfl, rfl⟩ := hbvs
    rw [premsHold_initElemSucc_iff (z := z) (y := y) (ref := ref)
      (j := Value.case "%" (Value.tuple (Value.num (Num.natN q) :: wss)))
      (by simp) (by simp) (by simp) (by simp) rfl] at hp
    obtain ⟨-, q', rest, refs, hjj, her, hsel⟩ := hp
    have hqq : q' = q := by
      simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
        Num.natN.injEq, true_and] at hjj
      exact hjj.1.symm
    subst hqq
    exact ⟨z, av, p, us, _, wss, mn, m, x, y, refs, ref, rfl, hpred, her, hsel⟩
  · rintro ⟨z, av, p, us, q, ws, mn, m, x, y, refs, ref, rfl, hpred, her, hsel⟩
    refine ⟨(initElemLhsScope z av (.case "%" (.tuple (.num (.natN p) :: us)))
        (.case "%" (.tuple (.num (.natN q) :: ws))) (.num mn) x y).bindVal "ref" ref,
      (initElemLhsScope z av (.case "%" (.tuple (.num (.natN p) :: us)))
        (.case "%" (.tuple (.num (.natN q) :: ws))) (.num mn) x y).bindVal "ref" ref,
      matchExp_readConcl_iff.2 ⟨z, _, _,
        initElemLhsScope z av (.case "%" (.tuple (.num (.natN p) :: us)))
          (.case "%" (.tuple (.num (.natN q) :: ws))) (.num mn) x y, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExps_five_iff.2 ⟨_, _, _, _, _, _, _, _, _, rfl,
        (matchExp_caseVar_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by decide) (by decide)).2
          ⟨_, _, rfl, rfl⟩⟩
    · exact Validation.matchExp_list_iff.2 ⟨_, rfl,
        (matchExps_arrayInitElemSuccRhs_iff (by simp [initElemLhsScope])
          (by simp [initElemLhsScope]) (by simp [initElemLhsScope])
          (by simp [initElemLhsScope]) (by simp [initElemLhsScope])
          (by simp [initElemLhsScope]) (by simp [initElemLhsScope])).2
        ⟨ref, p, us, q, ws, mn, m, rfl, rfl, rfl, hpred, rfl, rfl⟩⟩
    · exact (premsHold_initElemSucc_iff (z := z) (y := y) (ref := ref)
        (by simp [initElemLhsScope]) (by simp [initElemLhsScope])
        (by simp [initElemLhsScope]) (by simp [initElemLhsScope]) rfl).2
        ⟨rfl, q, ws, refs, rfl, her, hsel⟩

/-! ## `array.new_elem-alloc`

The last of the thirty-four, and the only one whose conclusion *concatenates*.
Its right-hand side is `ref^n (ARRAY.NEW_FIXED x %(n))`: the left operand's
counter `n` is already bound by the left-hand side, so `patLen` computes and
`matchExp` splits without searching — the iteration takes exactly `n` of the
instructions and binds them to `ref*`, and the premise then pins `ref*` to a
slice of `$elem(z, y).REFS`. -/

/-- `e^n` over one domain, with the counter already bound and the body the
domain's own variable under a coercion: it binds the domain to the matched
list and forces the counter to be its length. -/
theorem matchExp_iterNSubVar_iff {env : Env} {ρ ρ' : VarEnv} {x d c : IL.Id}
    {t₁ t₂ : Typ} {nv v : Value} (hx : ρ.findVal? x = none) (hx' : x ≠ "_")
    (hdf : ρ.findVal? d = none) (hc : ρ.findVal? c = some nv) :
    MatchExp env ρ (.iterE (.subE (.varE x) t₁ t₂)
      (.mk (.listN (.varE c) none) [.mk x (.varE d)])) v ρ' ↔
      ∃ vs, v = .list vs ∧ nv = .num (.natN vs.length) ∧
        ρ' = ρ.bindVal d (.list vs) := by
  rw [matchExp_iterE_listN_iff]
  constructor
  · rintro ⟨vs, σ, rfl, hcnt, hiter⟩
    obtain ⟨hnv, rfl⟩ := (matchExp_boundVar_iff hc).1 hcnt
    rw [matchIterList_single_iff (bindsVar_subVar x t₁ t₂) hx hx',
      matchExp_freshVar_iff hdf] at hiter
    exact ⟨vs, rfl, hnv.symm, hiter⟩
  · rintro ⟨vs, rfl, rfl, rfl⟩
    exact ⟨vs, ρ, rfl, (matchExp_boundVar_iff hc).2 ⟨rfl, rfl⟩,
      (matchIterList_single_iff (bindsVar_subVar x t₁ t₂) hx hx').2
        ((matchExp_freshVar_iff hdf).2 rfl)⟩

/-- `(ARRAY.NEW_FIXED x %(n))` with both variables bound: it tests. -/
theorem matchExp_caseVarPct_iff {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {x c : IL.Id}
    {xv nv v : Value} (hx : ρ.findVal? x = some xv) (hc : ρ.findVal? c = some nv) :
    MatchExp env ρ (.caseE op (.tupE [.varE x, .caseE "%" (.tupE [.varE c])])) v ρ' ↔
      v = .case op (.tuple [xv, .case "%" (.tuple [nv])]) ∧ ρ' = ρ := by
  rw [Validation.matchExp_case_iff]
  constructor
  · rintro ⟨w, rfl, hw⟩
    obtain ⟨ws, rfl, hws⟩ := Validation.matchExp_tup_iff.1 hw
    obtain ⟨a, b, σ, rfl, ha, hb⟩ := matchExps_two_iff.1 hws
    obtain ⟨rfl, rfl⟩ := (matchExp_boundVar_iff hx).1 ha
    obtain ⟨c', rfl, hc'⟩ := Validation.matchExp_case_iff.1 hb
    obtain ⟨cs, rfl, hcs⟩ := Validation.matchExp_tup_iff.1 hc'
    obtain ⟨u, rfl, hu⟩ := matchExps_one_iff.1 hcs
    obtain ⟨rfl, rfl⟩ := (matchExp_boundVar_iff hc).1 hu
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, rfl, Validation.matchExp_tup_iff.2 ⟨_, rfl,
      matchExps_two_iff.2 ⟨_, _, ρ', rfl, (matchExp_boundVar_iff hx).2 ⟨rfl, rfl⟩,
        Validation.matchExp_case_iff.2 ⟨_, rfl,
          Validation.matchExp_tup_iff.2 ⟨_, rfl,
            matchExps_one_iff.2 ⟨_, rfl,
              (matchExp_boundVar_iff hc).2 ⟨rfl, rfl⟩⟩⟩⟩⟩⟩⟩

/-- `ref^n` *evaluated*: with the counter bound to the domain's length, the
iteration denotes the domain. -/
theorem evalExp_iterNVar {env : Env} {ρ : VarEnv} {x d c : IL.Id} {ws : List Value}
    (hx : x ≠ "_") (hc : ρ.findVal? c = some (.num (.natN ws.length)))
    (hd : ρ.findVal? d = some (.list ws)) :
    EvalExp env ρ (.iterE (.varE x) (.mk (.listN (.varE c) none) [.mk x (.varE d)]))
      (.list ws) := by
  refine evalExp_iterE_iff.mpr ⟨4, ?_⟩
  have hdoms : evalDoms 3 env ρ [.mk x (.varE d)] = .ok [(x, Value.list ws)] := by
    simp [evalDoms, domVar, domSrc, evalExp, hd]
  have hcount : evalExp 3 env ρ (.varE c) = .ok (.num (.natN ws.length)) := by
    simp [evalExp, hc]
  rw [evalIterE, hdoms]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, hcount]
  refine ⟨_, rfl, _, rfl, ws.length, rfl, ?_⟩
  rw [evalIterList]
  simp only [Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok]
  refine ⟨[(x, ws)], by simp [Value.asList?], by simp, ws, ?_, rfl⟩
  rw [iterRows_singleton, evalRounds]
  clear hdoms hd hcount hc
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.map_cons, List.mapM_cons, Res.bind_eq_ok]
      refine ⟨w, ?_, ws, ih, rfl⟩
      simp [evalExp, VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx]

/-- …and nothing else: `EvalExp` is a function. -/
theorem evalExp_iterNVar_iff {env : Env} {ρ : VarEnv} {x d c : IL.Id} {ws : List Value}
    {w : Value} (hx : x ≠ "_") (hc : ρ.findVal? c = some (.num (.natN ws.length)))
    (hd : ρ.findVal? d = some (.list ws)) :
    EvalExp env ρ (.iterE (.varE x) (.mk (.listN (.varE c) none) [.mk x (.varE d)])) w
      ↔ w = .list ws :=
  ⟨fun h => EvalExp.unique h (evalExp_iterNVar hx hc hd),
   fun h => h ▸ evalExp_iterNVar hx hc hd⟩

/-- A slice of a value is a slice of a *list*, with `Sem/Value.lean`'s
corrected bound `i + n ≤ |l|` (upstream item U2). -/
theorem slice?_eq_some_list {w u : Value} {p k : Nat} (h : w.slice? p k = some u) :
    ∃ l : List Value, w = .list l ∧ p + k ≤ l.length ∧ u = .list ((l.drop p).take k) := by
  cases w with
  | list l =>
      simp only [Value.slice?] at h
      split at h
      · exact ⟨l, rfl, by assumption, (Option.some.inj h).symm⟩
      · exact absurd h (by simp)
  | num _ => simp [Value.slice?] at h
  | bool _ => simp [Value.slice?] at h
  | text _ => simp [Value.slice?] at h
  | tuple _ => simp [Value.slice?] at h
  | case _ _ => simp [Value.slice?] at h
  | struct _ => simp [Value.slice?] at h
  | opt _ => simp [Value.slice?] at h

/-- …and the converse, at a slice that is in bounds. -/
theorem slice?_list {l : List Value} {p k : Nat} (hlt : p + k ≤ l.length) :
    (Value.list l).slice? p k = some (.list ((l.drop p).take k)) := by
  simp only [Value.slice?]
  split
  · rfl
  · exact absurd hlt (by assumption)

/-- The premise of `array.new_elem-alloc`: the `n` references the conclusion
allocated are exactly `$elem(z, y).REFS[i!%.0 : n]`. -/
theorem premsHold_newElemAlloc_iff {env : Env} {ρ ρ' : VarEnv} {z y i : Value}
    {refs : List Value}
    (hz : ρ.findVal? "z" = some z) (hy : ρ.findVal? "y" = some y)
    (hi : ρ.findVal? "i" = some i)
    (hn : ρ.findVal? "n" = some (.num (.natN refs.length)))
    (hr : ρ.findVal? "ref*" = some (.list refs))
    (hdf : ρ.findDef? "elem" = none) :
    PremsHold env ρ
      [.ifPr (.cmpE .eqOp .boolT
        (.iterE (.varE "ref") (.mk (.listN (.varE "n") none) [.mk "ref" (.varE "ref*")]))
        (.sliceE (.dotE (.callE "elem" [.expA (.varE "z"), .expA (.varE "y")]) "REFS")
          (.projE (.uncaseE (.varE "i") "%") 0) (.varE "n")))] ρ' ↔
      ρ' = ρ ∧ ∃ (p : Nat) (rest allrefs : List Value),
        i = .case "%" (.tuple (.num (.natN p) :: rest)) ∧
        ElemRefs env z y allrefs ∧ p + refs.length ≤ allrefs.length ∧
        (allrefs.drop p).take refs.length = refs := by
  rw [premsHold_oneIf_iff]
  constructor
  · rintro ⟨rfl, hev⟩
    obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_cmpE_iff.1 hev
    rw [evalExp_iterNVar_iff (by decide) hn hr] at h₁
    subst h₁
    obtain rfl := ExecNumeric.cmpValues_eq_true_iff.1 hc
    obtain ⟨w, p, kk, hw, hp, hkk, hs⟩ := evalExp_sliceE_iff.1 h₂
    rw [evalExp_varE_iff, hn, Option.some.injEq, Value.num.injEq, Num.natN.injEq] at hkk
    subst hkk
    obtain ⟨rest, hii⟩ := evalExp_pctProj_iff.1 hp
    rw [hi, Option.some.injEq] at hii
    obtain ⟨allrefs, rfl, hlt, hsl⟩ := slice?_eq_some_list hs
    exact ⟨rfl, p, rest, allrefs, hii,
      (evalExp_elemRefs_iff (zx := "z") (yx := "y") hz hy hdf).1 hw, hlt,
      (Value.list.inj hsl).symm⟩
  · rintro ⟨rfl, p, rest, allrefs, hii, her, hlt, hsl⟩
    refine ⟨rfl, evalExp_cmpE_iff.2 ⟨.list refs, .list refs, ?_, ?_,
      ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩⟩
    · exact (evalExp_iterNVar_iff (by decide) hn hr).2 rfl
    · refine evalExp_sliceE_iff.2 ⟨.list allrefs, p, refs.length,
        (evalExp_elemRefs_iff (zx := "z") (yx := "y") hz hy hdf).2 her,
        evalExp_pctProj_iff.2 ⟨rest, by rw [hi, hii]⟩, evalExp_varE_iff.2 hn, ?_⟩
      rw [slice?_list hlt, hsl]

/-- The scope `array.new_elem-alloc`'s left-hand side builds. -/
def newElemLhsScope (z i nv x y : Value) : VarEnv :=
  (((((VarEnv.empty.bindVal "z" z).bindVal "i" i).bindVal "n" nv).bindVal
    "x" x).bindVal "y" y)

/-- **`Step_read/array.new_elem-alloc`, characterised exactly.**

Three things the conclusion alone forces.  The count is *not* a free choice:
the right-hand side's `ref^n` takes exactly `n` instructions and binds them to
`ref*`, and the trailing `ARRAY.NEW_FIXED x %(n)` repeats the same `n`, so the
whole right-hand side is `refs ++ [ARRAY.NEW_FIXED x %(|refs|)]`.  The offset
`i` has to be a `%`-injection over a `nat`, because the premise projects it.
And the array type index `x` is never looked at — the rule reads the *element
segment* `y`.

The premise is where the state comes in: the slice is defined exactly when
`i + n ≤ |$elem(z, y).REFS|`, the complement of `array.new_elem-oob`'s guard
`i + n > |refs|`.  (With `eval.ml:284`'s strict bound, which this port
corrects — upstream item U2 — a copy running exactly to the end of the segment
had no step at all.) -/
theorem ruleFires_arrayNewElemAlloc_iff {env : Env} {v : Value} :
    RuleFires env "%~>%" [] [] v arrayNewElemAllocRule ↔
      ∃ z p rest x y refs allrefs,
        v = .tuple
          [ExecStep.configV z
             [Execution.constV Execution.i32V (.case "%" (.tuple (.num (.natN p) :: rest))),
              Execution.constV Execution.i32V
                (.case "%" (.tuple [.num (.natN refs.length)])),
              .case "ARRAY.NEW_ELEM" (.tuple [x, y])],
           .list (refs ++
             [.case "ARRAY.NEW_FIXED"
               (.tuple [x, .case "%" (.tuple [.num (.natN refs.length)])])])] ∧
        ElemRefs env z y allrefs ∧ p + refs.length ≤ allrefs.length ∧
        (allrefs.drop p).take refs.length = refs := by
  unfold arrayNewElemAllocRule
  rw [ruleFires_nil_iff]
  constructor
  · rintro ⟨ρ₁, ρ₂, hm, hp⟩
    obtain ⟨z, instrs, rhs, σ, rfl, hms, hr⟩ := matchExp_readConcl_iff.1 hm
    obtain ⟨a, b, c, τ, υ, rfl, ha, hb, hc⟩ := matchExps_three_iff.1 hms
    rw [matchExp_constI32Var_iff (by simp)] at ha
    obtain ⟨i, rfl, rfl⟩ := ha
    rw [matchExp_constI32Pct_iff (by simp)] at hb
    obtain ⟨nv, rfl, rfl⟩ := hb
    rw [matchExp_caseVar2_iff (by simp) (by simp) (by decide) (by decide)] at hc
    obtain ⟨x, y, rfl, rfl⟩ := hc
    obtain ⟨vs, k, σ', rfl, hL, hR⟩ := ExecReadControl.matchExp_catE_dest hr
    rw [matchExp_iterNSubVar_iff (nv := nv) (by simp) (by decide) (by simp) (by simp)] at hL
    obtain ⟨refs, hrefs, rfl, rfl⟩ := hL
    obtain rfl : vs.take k = refs := Value.list.inj hrefs
    obtain ⟨bs, hbs, hbvs⟩ := Validation.matchExp_list_iff.1 hR
    obtain ⟨bv, rfl, hbv⟩ := matchExps_one_iff.1 hbvs
    rw [matchExp_caseVarPct_iff (xv := x)
      (nv := Value.num (Num.natN (vs.take k).length)) (by simp) (by simp)] at hbv
    obtain ⟨rfl, rfl⟩ := hbv
    have hvs : vs.take k ++ vs.drop k = vs := List.take_append_drop k vs
    rw [show vs.drop k = _ from Value.list.inj hbs] at hvs
    rw [premsHold_newElemAlloc_iff (z := z) (y := y) (i := i) (refs := vs.take k)
      (by simp) (by simp) (by simp) (by simp) (by simp) rfl] at hp
    obtain ⟨-, p, rest, allrefs, rfl, her, hlt, hsl⟩ := hp
    refine ⟨z, p, rest, x, y, vs.take k, allrefs, ?_, her, hlt, hsl⟩
    rw [hvs]
  · rintro ⟨z, p, rest, x, y, refs, allrefs, rfl, her, hlt, hsl⟩
    have e1 : (refs ++ [Value.case "ARRAY.NEW_FIXED"
        (.tuple [x, .case "%" (.tuple [Value.num (.natN refs.length)])])]).take
          refs.length = refs := by simp
    have e2 : (refs ++ [Value.case "ARRAY.NEW_FIXED"
        (.tuple [x, .case "%" (.tuple [Value.num (.natN refs.length)])])]).drop
          refs.length = [Value.case "ARRAY.NEW_FIXED"
            (.tuple [x, .case "%" (.tuple [Value.num (.natN refs.length)])])] := by simp
    refine ⟨(newElemLhsScope z (.case "%" (.tuple (.num (.natN p) :: rest)))
        (.num (.natN refs.length)) x y).bindVal "ref*" (.list refs),
      (newElemLhsScope z (.case "%" (.tuple (.num (.natN p) :: rest)))
        (.num (.natN refs.length)) x y).bindVal "ref*" (.list refs),
      matchExp_readConcl_iff.2 ⟨z, _, _,
        newElemLhsScope z (.case "%" (.tuple (.num (.natN p) :: rest)))
          (.num (.natN refs.length)) x y, rfl, ?_, ?_⟩, ?_⟩
    · exact matchExps_three_iff.2 ⟨_, _, _, _, _, rfl,
        (matchExp_constI32Var_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_constI32Pct_iff (by simp)).2 ⟨_, rfl, rfl⟩,
        (matchExp_caseVar2_iff (by simp) (by simp) (by decide) (by decide)).2
          ⟨_, _, rfl, rfl⟩⟩
    · refine Execution.matchExp_catE_ofLeft (j := refs.length)
        (σ := (newElemLhsScope z (.case "%" (.tuple (.num (.natN p) :: rest)))
          (.num (.natN refs.length)) x y).bindVal "ref*" (.list refs))
        (patLen_iterE_listN_var (by simp [newElemLhsScope])) (by simp) ?_ ?_
      · rw [e1]
        exact (matchExp_iterNSubVar_iff (nv := .num (.natN refs.length))
          (by simp [newElemLhsScope]) (by decide) (by simp [newElemLhsScope])
          (by simp [newElemLhsScope])).2 ⟨refs, rfl, rfl, rfl⟩
      · rw [e2]
        exact Validation.matchExp_list_iff.2 ⟨_, rfl,
          matchExps_one_iff.2 ⟨_, rfl,
            (matchExp_caseVarPct_iff (xv := x) (nv := .num (.natN refs.length))
              (by simp [newElemLhsScope]) (by simp [newElemLhsScope])).2 ⟨rfl, rfl⟩⟩⟩
    · exact (premsHold_newElemAlloc_iff (z := z) (y := y) (refs := refs)
        (by simp [newElemLhsScope]) (by simp [newElemLhsScope])
        (by simp [newElemLhsScope]) (by simp [newElemLhsScope])
        (by simp [newElemLhsScope]) rfl).2 ⟨rfl, p, rest, allrefs, rfl, her, hlt, hsl⟩

/-- `$elem(z, y).REFS` denotes at most one list: `ExecNumeric.Applies` is a
function and `field?` is one. -/
theorem ElemRefs.unique {env : Env} {z y : Value} {r₁ r₂ : List Value}
    (h₁ : ElemRefs env z y r₁) (h₂ : ElemRefs env z y r₂) : r₁ = r₂ := by
  obtain ⟨e₁, ha₁, hf₁⟩ := h₁
  obtain ⟨e₂, ha₂, hf₂⟩ := h₂
  obtain rfl := ExecNumeric.Applies.unique ha₁ ha₂
  rw [hf₁] at hf₂
  exact Value.list.inj (Option.some.inj hf₂)

/-- **The `array.new_elem` boundary allocates.**  At `i + n = |$elem(z, y).REFS|`
— a copy that runs exactly to the end of the segment, which the W3C rule
allows — `array.new_elem-oob` does not fire, whatever the result, and
`array.new_elem-alloc` fires with the last `n` references.  With
`eval.ml:284`'s strict slice bound neither fired; the port corrects the bound
(upstream item U2). -/
theorem arrayNewElem_boundary_alloc {env : Env} {z x y : Value} {p n : Nat}
    {allrefs : List Value} (her : ElemRefs env z y allrefs)
    (hb : p + n = allrefs.length) :
    (∀ rhs, ¬ RuleFires env "%~>%" [] []
        (.tuple [ExecStep.configV z
          [Execution.constV Execution.i32V (Execution.pctV p),
           Execution.constV Execution.i32V (Execution.pctV n),
           .case "ARRAY.NEW_ELEM" (.tuple [x, y])], rhs]) arrayNewElemOobRule) ∧
      RuleFires env "%~>%" [] []
        (.tuple [ExecStep.configV z
          [Execution.constV Execution.i32V (Execution.pctV p),
           Execution.constV Execution.i32V (Execution.pctV n),
           .case "ARRAY.NEW_ELEM" (.tuple [x, y])],
          .list (allrefs.drop p ++
            [.case "ARRAY.NEW_FIXED" (.tuple [x, Execution.pctV n])])]) arrayNewElemAllocRule := by
  have hlen : (allrefs.drop p).length = n := by simp; omega
  constructor
  · intro rhs
    rw [ruleFires_arrayNewElemOob_iff]
    rintro ⟨z', p', q', rest', x', y', refs', hv, her', hlt⟩
    simp only [ExecStep.configV, Execution.constV, Execution.pctV, Value.tuple.injEq,
      Value.case.injEq, List.cons.injEq, and_true, true_and] at hv
    obtain ⟨⟨rfl, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩⟩, -⟩ := hv
    rw [ElemRefs.unique her' her] at hlt
    omega
  · rw [ruleFires_arrayNewElemAlloc_iff]
    refine ⟨z, p, [], x, y, allrefs.drop p, allrefs, ?_, her, by omega,
      List.take_of_length_le (by omega)⟩
    rw [hlen]
    rfl

end Silmaril.SpecTec.Equiv.ExecReadAggregate
