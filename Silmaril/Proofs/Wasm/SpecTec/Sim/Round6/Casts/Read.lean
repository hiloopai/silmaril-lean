module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Casts.Succ
public import Silmaril.Wasm.SpecTec.Sim.Round5.Read2.Thms

/-!
# Round 6: `Step_read` backward under the new reading, at every configuration

Track reading transfers a `Step_read` rule to the old reading only at a left-hand side whose code
names no cast constructor (`Reading.firesB_read_iff`). Here every left-hand side is covered, by
whether the code is a **cast pair** `[ref r, cast]` (`CastPair`):

* at a cast pair, every rule but the eight cast rules is dead, since each names a constructor that
  neither a reference nor a cast has (`readCheck`, checked over the script, and
  `Reading.deadAt_of_tags`);
* elsewhere, the eight cast rules are dead (their left-hand sides are cast pairs, `pair_of_*`),
  and every other rule is plain for `Expand` (`readCheck`), so every rule fires the same under
  both readings (`Reading.firesB_iff_at`).

So a `Step_read` step of the new reading is a cast step (`castsBwdB_of`, from
`RefOkBB`) or a step of the old reading (`readB`), and the old one is covered by round 5's proved
backward lemmas (`readDecl`, as `backwardUpToNC` without the cast exclusion).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)
open Round5.Read (ReadValidS readDoneK)
open Reading (FiresB RefOkBB DeadAt ClosedAt)
open RefsGC (LhsIn TagsIn)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## Cast pairs -/

/-- **A cast pair**: the code of a cast rule's left-hand side, a reference and a cast. -/
def CastPair (code : List Admin) : Prop :=
  ∃ (r : Ref) (i : Instr), code = [.ref r, .plain i] ∧ Target.castInstr i = true

/-- The constructors of a reference: `Typing.refHead`. -/
def refTags : List MixopS :=
  ["REF.I31_NUM", "REF.NULL_ADDR", "REF.STRUCT_ADDR", "REF.ARRAY_ADDR", "REF.FUNC_ADDR",
    "REF.EXN_ADDR", "REF.HOST_ADDR", "REF.EXTERN"]

/-- The constructors at the top level of a cast pair. -/
def pairTags : List MixopS := refTags ++ Reading.castTags

/-- The four cast instructions. -/
theorem castInstr_cases {i : Instr} (h : Target.castInstr i = true) :
    (∃ rt, i = .refTest rt) ∨ (∃ rt, i = .refCast rt) ∨ (∃ l rt₁ rt₂, i = .brOnCast l rt₁ rt₂) ∨
      ∃ l rt₁ rt₂, i = .brOnCastFail l rt₁ rt₂ := by
  unfold Target.castInstr at h
  split at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, rfl⟩)
  · exact .inr (.inr (.inl ⟨_, _, _, rfl⟩))
  · exact .inr (.inr (.inr ⟨_, _, _, rfl⟩))
  · cases h

/-- A cast's constructor is a cast tag. -/
theorem castHead_mem {i : Instr} (h : Target.castInstr i = true) :
    Typing.adminHead (.plain i) ∈ Reading.castTags := by
  rcases castInstr_cases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    simp [Typing.adminHead, Typing.instrHead, Reading.castTags]

/-- A reference's constructor is a reference tag. -/
theorem refHead_mem (r : Ref) : Typing.adminHead (.ref r) ∈ refTags := by
  cases r <;> simp [Typing.adminHead, Typing.refHead, refTags]

/-- **The left-hand side of a cast pair names only reference and cast constructors.** -/
theorem lhsIn_pair {s : Store H} {f : Frame} {code : List Admin} (hp : CastPair code) :
    LhsIn pairTags (configV hn ⟨s, f, code⟩) := by
  obtain ⟨r, i, rfl, hi⟩ := hp
  refine .inr ⟨stateV hn s f, adminsToV [.ref r, .plain i], rfl, ?_⟩
  intro x hx op w hw
  have hx' : x = adminToV (.ref r) ∨ x = adminToV (.plain i) := by simpa [adminsToV] using hx
  rcases hx' with rfl | rfl
  · rw [Typing.adminToV_case hw]
    exact List.mem_append_left _ (refHead_mem r)
  · rw [Typing.adminToV_case hw]
    exact List.mem_append_right _ (castHead_mem hi)

/-- The code of a cast rule's left-hand side, read back, is a cast pair. -/
theorem pair_of_cfg {B : Builtins} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {is : List Admin} {S F R W : Value} {op : MixopS}
    (hR : HasTyp (simEnv B) (VarEnv.empty.bindVals σ) (.varT "ref" []) R)
    (hop : op ∈ Reading.castTags)
    (h : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
      .list [R, .case op W]])) : CastPair is := by
  obtain ⟨-, -, r, a, rfl, -, ha⟩ := Round5.Read.cast_inv hR h
  have hh : Typing.adminHead a = op := (Typing.adminToV_case ha).symm
  simp only [Reading.castTags, List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl
  · obtain ⟨l, rt₁, rt₂, rfl⟩ := Round5.Read.head_brOnCast hh
    exact ⟨r, _, rfl, rfl⟩
  · obtain ⟨l, rt₁, rt₂, rfl⟩ := Round5.Read.head_brOnCastFail hh
    exact ⟨r, _, rfl, rfl⟩
  · obtain ⟨rt, rfl⟩ := Round5.Read.head_refTest hh
    exact ⟨r, _, rfl, rfl⟩
  · obtain ⟨rt, rfl⟩ := Round5.Read.head_refCast hh
    exact ⟨r, _, rfl, rfl⟩

/-! ## The left-hand sides of the eight cast rules -/

section Lhs

variable {B : Builtins} {D : Interp} {els : Prop} {c : Config H} {b : Value}

theorem pair_of_refTest {r : Rule} (hr : r = refTestTrueRule ∨ r = refTestFalseRule)
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" r (.tuple [configV hn c, b])) :
    CastPair c.code := by
  obtain ⟨s, f, is⟩ := c
  rcases hr with rfl | rfl
  all_goals
    obtain ⟨σ, hq, he, -⟩ := ruleBody_scope hb
    obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
    obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
    obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
    obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
    have hl := RefsGC.lhs_of_concl he
    have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
        .list [R, .case "REF.TEST" RT]]) := by
      concl_inv hl
    exact pair_of_cfg hR (by decide) hcw

theorem pair_of_refCast {r : Rule} (hr : r = refCastSucceedRule ∨ r = refCastFailRule)
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" r (.tuple [configV hn c, b])) :
    CastPair c.code := by
  obtain ⟨s, f, is⟩ := c
  rcases hr with rfl | rfl
  all_goals
    obtain ⟨σ, hq, he, -⟩ := ruleBody_scope hb
    obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
    obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
    obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
    obtain ⟨RT, frt, -⟩ := hq "rt" (.varT "reftype" []) (by simp)
    have hl := RefsGC.lhs_of_concl he
    have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
        .list [R, .case "REF.CAST" RT]]) := by
      concl_inv hl
    exact pair_of_cfg hR (by decide) hcw

theorem pair_of_brOnCast {r : Rule} (hr : r = brOnCastSucceedRule ∨ r = brOnCastFailRule)
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" r (.tuple [configV hn c, b])) :
    CastPair c.code := by
  obtain ⟨s, f, is⟩ := c
  rcases hr with rfl | rfl
  all_goals
    obtain ⟨σ, hq, he, -⟩ := ruleBody_scope hb
    obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
    obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
    obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
    obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
    obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
    obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
    have hl := RefsGC.lhs_of_concl he
    have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
        .list [R, .case "BR_ON_CAST" (.tuple [L, RT₁, RT₂])]]) := by
      concl_inv hl
    exact pair_of_cfg hR (by decide) hcw

theorem pair_of_brOnCastFail {r : Rule}
    (hr : r = brOnCastFailSucceedRule ∨ r = brOnCastFailFailRule)
    (hb : RuleBody (simEnv B) D els [] [] "%~>%" r (.tuple [configV hn c, b])) :
    CastPair c.code := by
  obtain ⟨s, f, is⟩ := c
  rcases hr with rfl | rfl
  all_goals
    obtain ⟨σ, hq, he, -⟩ := ruleBody_scope hb
    obtain ⟨S, fs, -⟩ := hq "s" (.varT "store" []) (by simp)
    obtain ⟨F, ff, -⟩ := hq "f" (.varT "frame" []) (by simp)
    obtain ⟨R, fr, hR⟩ := hq "ref" (.varT "ref" []) (by simp)
    obtain ⟨L, fl, -⟩ := hq "l" (.varT "labelidx" []) (by simp)
    obtain ⟨RT₁, frt₁, -⟩ := hq "rt_1" (.varT "reftype" []) (by simp)
    obtain ⟨RT₂, frt₂, -⟩ := hq "rt_2" (.varT "reftype" []) (by simp)
    have hl := RefsGC.lhs_of_concl he
    have hcw : configV hn ⟨s, f, is⟩ = .case "%;%" (.tuple [.case "%;%" (.tuple [S, F]),
        .list [R, .case "BR_ON_CAST_FAIL" (.tuple [L, RT₁, RT₂])]]) := by
      concl_inv hl
    exact pair_of_cfg hR (by decide) hcw

end Lhs

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
