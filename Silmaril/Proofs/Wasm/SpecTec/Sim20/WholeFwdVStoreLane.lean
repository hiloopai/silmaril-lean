module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdVStoreVal
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdPure2

/-!
# `Step` 18 (`vstore_lane-val`) forward, at builtins that answer `$lanes_` and `$ibytes_`

`z; CONST I32 i; VCONST V128 c; VSTORE_LANE V128 N ao j ~>
$with_mem(z, 0, i + ao.OFFSET, N/8, b*); ε` has three premises:

* `N = $jsize(Jnn)`;
* `M.0 = 128 / N`, over the rationals;
* `b* = $ibytes_(N, $lanes_(Jnn X M, c)[j])`.

`Jnn` and `M` are quantified and bound only by these premises. The declarative reading picks
them as the lane type of width `N` and the lane count `128 / N`.

* `laneB P` is `vbytesB P` with `$lanes_` and `$ibytes_` answered as V2 computes them
  (`laneCalls20_laneB`). It keeps the integer, float, growth and `$vbytes_` answers
  (`intB_laneB`, `floatB_laneB`, `growCalls20_laneB`, `vbytes20_laneB`).
* `callDef_jsize20`: `$jsize` at the lane type of each pack size, through `$lsize` and
  `$size`/`$psize`. `typedV_jnn20`, `typedV_dim20`: the two premise-bound quantifiers are typed.
* **`fires_vstoreLaneVal`**: at builtins with `LaneCalls20`, rule 18 fires from the image of
  V2's `vecStoreLaneVal` to the image of its successor, from a typed state.
* `fwdBase20_vstoreLaneVal`, and **`Task.wholeStepFwd20L`** (stated and proved): at `laneB`, the
  nested fragment of pass 1's `FwdStep20` and this pass's `FwdStep20B`, plus `vecStoreVal` and
  `vecStoreLaneVal`, is matched forward.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil natV)
open Silmaril.Wasm.SpecTec.Sim (Fires TypedV ValsOnly stateT QuantsOk evalExp_tup2 evalExp_case)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim.State (iterVar)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (simEnv20S)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## Lane values -/

/-- The integer lane type of a pack size, `Jnn`. -/
def jnnV20 : PackSize → Value
  | .i8 => caseNilV "I8"
  | .i16 => caseNilV "I16"
  | .i32 => caseNilV "I32"
  | .i64 => caseNilV "I64"

/-- The shape `Jnn X M` of a pack size, with `M = 128 / N`. -/
def shapeV20 (sz : PackSize) : Value := .case "%X%" (.tuple [jnnV20 sz, pctV (128 / sz.width)])

/-- The lanes of `c` at the shape of `sz`, encoded. -/
def lanesV20 (sz : PackSize) (c : BitVec 128) : List Value :=
  (Silmaril.Wasm.Numerics.lanes sz.width (128 / sz.width) c).map fun x => pctV x.toNat

theorem shapeV20_injective : Function.Injective shapeV20 := by
  intro a b h
  cases a <;> cases b <;> simp_all [shapeV20, jnnV20, caseNilV]

/-! ## Builtins answering `$lanes_` and `$ibytes_` -/

/-- **`B` answers `$lanes_` and `$ibytes_` as V2 computes them.** -/
structure LaneCalls20 (B : Builtins) : Prop where
  lanes : ∀ (sz : PackSize) (c : BitVec 128),
    B.call "lanes_" [.val (shapeV20 sz), .val (pctV c.toNat)] = some (.list (lanesV20 sz c))
  ibytes : ∀ N k : Nat, B.call "ibytes_" [.val (.num (.natN N)), .val (pctV k)] =
    some (bytesV (ibytes N (BitVec.ofNat N k)))

open Classical in
/-- `$lanes_(Jnn X M, c)`, at the shapes of pack sizes. -/
noncomputable def lanesCall20 (ws : List ArgV) : Option Value :=
  if h : ∃ p : PackSize × BitVec 128, ws = [.val (shapeV20 p.1), .val (pctV p.2.toNat)] then
    some (.list (lanesV20 h.choose.1 h.choose.2))
  else none

/-- `$ibytes_(N, i)`. -/
def ibytesCall20 : List ArgV → Option Value
  | [.val (.num (.natN N)), .val (.case "%" (.tuple [.num (.natN k)]))] =>
      some (bytesV (ibytes N (BitVec.ofNat N k)))
  | _ => none

/-- **`vbytesB P` with `$lanes_` and `$ibytes_` answered as V2 computes them.** -/
noncomputable def laneB (P : Profile) : Builtins :=
  ⟨fun x ws => if x = "lanes_" then lanesCall20 ws else if x = "ibytes_" then ibytesCall20 ws
    else (vbytesB P).call x ws⟩

theorem laneB_call_of_ne {P : Profile} {x : IL.Id} (h₁ : x ≠ "lanes_") (h₂ : x ≠ "ibytes_")
    (ws : List ArgV) : (laneB P).call x ws = (vbytesB P).call x ws := by
  simp [laneB, h₁, h₂]

theorem laneCalls20_laneB (P : Profile) : LaneCalls20 (laneB P) where
  lanes sz c := by
    have h : ∃ p : PackSize × BitVec 128, [ArgV.val (shapeV20 sz), .val (pctV c.toNat)] =
        [.val (shapeV20 p.1), .val (pctV p.2.toNat)] := ⟨(sz, c), rfl⟩
    have e : h.choose = (sz, c) := by
      obtain ⟨a, t⟩ := List.cons.inj h.choose_spec
      obtain ⟨b, -⟩ := List.cons.inj t
      exact Prod.ext (shapeV20_injective (ArgV.val.inj a)).symm
        (BitVec.eq_of_toNat_eq (pctV_injective (ArgV.val.inj b)).symm)
    simp only [laneB, lanesCall20, ↓reduceIte, h, ↓reduceDIte, e]
  ibytes N k := by
    simp [laneB, ibytesCall20, pctV]

theorem intB_laneB (P : Profile) : Sim.IntNumeric.IntB (laneB P) := by
  intro x ws v h
  by_cases h₁ : x = "lanes_"
  · subst h₁; simp [Sim.IntNumeric.intCall] at h
  by_cases h₂ : x = "ibytes_"
  · subst h₂; simp [Sim.IntNumeric.intCall] at h
  rw [laneB_call_of_ne h₁ h₂]
  exact intB_vbytesB P x ws v h

theorem floatB_laneB (P : Profile) : Sim.Floats.FloatB P (laneB P) := by
  intro x ws v h
  by_cases h₁ : x = "lanes_"
  · subst h₁; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  by_cases h₂ : x = "ibytes_"
  · subst h₂; simp [Sim.Floats.floatCall, Sim.Floats.floatNames] at h
  rw [laneB_call_of_ne h₁ h₂]
  exact floatB_vbytesB P x ws v h

theorem growCalls20_laneB (P : Profile) : GrowCalls20 (laneB P) where
  table ti ti' n r h := by
    rw [laneB_call_of_ne (by decide) (by decide)]
    exact (growCalls20_vbytesB P).table ti ti' n r h
  mem mi mi' n h := by
    rw [laneB_call_of_ne (by decide) (by decide)]
    exact (growCalls20_vbytesB P).mem mi mi' n h

theorem vbytes20_laneB (P : Profile) : VBytes20 (laneB P) := by
  intro c
  rw [laneB_call_of_ne (by decide) (by decide)]
  exact vbytes20_vbytesB P c

/-! ## `$jsize` -/

theorem findDef_jsize20 : ∃ ps t, (simEnv20 B).findDef? "jsize" = some (ps, t,
    [.defD [.expP "Jnn" (.varT "Jnn" [])] [.expA (.varE "Jnn")]
      (.callE "lsize" [.expA (.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []))]) []]) :=
  ⟨_, _, rfl⟩

theorem findDef_lsize20 : ∃ ps t, (simEnv20 B).findDef? "lsize" = some (ps, t,
    [.defD [.expP "numtype" (.varT "numtype" [])]
      [.expA (.subE (.varE "numtype") (.varT "numtype" []) (.varT "lanetype" []))]
      (.callE "size" [.expA (.subE (.varE "numtype") (.varT "numtype" []) (.varT "valtype" []))])
      [],
     .defD [.expP "packtype" (.varT "packtype" [])]
      [.expA (.subE (.varE "packtype") (.varT "packtype" []) (.varT "lanetype" []))]
      (.callE "psize" [.expA (.varE "packtype")]) []]) :=
  ⟨_, _, rfl⟩

theorem findDef_psize20 : ∃ ps t, (simEnv20 B).findDef? "psize" = some (ps, t,
    [.defD [] [.expA (.caseE "I8" (.tupE []))] (.numE (.natN 8)) [],
     .defD [] [.expA (.caseE "I16" (.tupE []))] (.numE (.natN 16)) []]) :=
  ⟨_, _, rfl⟩

/-- A subtype pattern matches as its inner pattern. -/
theorem matchExp_subE20 {env : Env} {ρ ρ' : VarEnv} {e : Exp} {t₁ t₂ : Typ} {v : Value}
    (h : MatchExp env ρ e v ρ') : MatchExp env ρ (.subE e t₁ t₂) v ρ' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp [matchExp, h]⟩

/-- `$psize` at `I8` and `I16`. -/
theorem callDef_psize20 {sz : PackSize} (hs : sz = .i8 ∨ sz = .i16) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "psize" = none) (ha : EvalArgs (simEnv20 B) ρ args [.val (jnnV20 sz)]) :
    CallDef (simEnv20 B) ρ "psize" args (natV sz.width) := by
  obtain ⟨ps, t, hd⟩ := findDef_psize20 (B := B)
  refine callDef_of_tryClauses hρ hd ha ?_
  rcases hs with rfl | rfl
  · exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil))
      matchArgs_nil) premsHold_nil evalExp_num
  · exact tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (matchExp_caseE_undef (by decide)))) (tryClauses_hit (matchArgs_cons (matchArg_expA
        (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil) premsHold_nil evalExp_num)

/-- **`$lsize(Jnn)` is the pack size's width.** -/
theorem callDef_lsize20 (sz : PackSize) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "lsize" = none) (ha : EvalArgs (simEnv20 B) ρ args [.val (jnnV20 sz)]) :
    CallDef (simEnv20 B) ρ "lsize" args (natV sz.width) := by
  obtain ⟨ps, t, hd⟩ := findDef_lsize20 (B := B)
  refine callDef_of_tryClauses hρ hd ha ?_
  cases sz
  · exact tryClauses_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub rfl)) (tryClauses_hit (matchArgs_cons
        (matchArg_expA (matchExp_subE20 (matchExp_varE rfl))) matchArgs_nil) premsHold_nil
        (evalExp_callE_iff.2 (callDef_psize20 (.inl rfl) rfl
          (evalArgs_cons (evalExp_var rfl) evalArgs_nil))))
  · exact tryClauses_skip_match (matchArgs_cons_undef
      (Equiv.ExecBuiltins.matchArg_expA_undef_of_sub rfl)) (tryClauses_hit (matchArgs_cons
        (matchArg_expA (matchExp_subE20 (matchExp_varE rfl))) matchArgs_nil) premsHold_nil
        (evalExp_callE_iff.2 (callDef_psize20 (.inr rfl) rfl
          (evalArgs_cons (evalExp_var rfl) evalArgs_nil))))
  · exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_subE20 (matchExp_varE rfl)))
      matchArgs_nil) premsHold_nil (evalExp_callE_iff.2 (Pure.callDef_size20 (.int .i32) rfl
        (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var rfl)) evalArgs_nil)))
  · exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_subE20 (matchExp_varE rfl)))
      matchArgs_nil) premsHold_nil (evalExp_callE_iff.2 (Pure.callDef_size20 (.int .i64) rfl
        (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var rfl)) evalArgs_nil)))

/-- **`$jsize(Jnn)` is the pack size's width.** -/
theorem callDef_jsize20 (sz : PackSize) {ρ : VarEnv} {args : List Arg}
    (hρ : ρ.findDef? "jsize" = none) (ha : EvalArgs (simEnv20 B) ρ args [.val (jnnV20 sz)]) :
    CallDef (simEnv20 B) ρ "jsize" args (natV sz.width) := by
  obtain ⟨ps, t, hd⟩ := findDef_jsize20 (B := B)
  exact callDef_of_tryClauses hρ hd ha (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_varE rfl)) matchArgs_nil) premsHold_nil (evalExp_callE_iff.2 (callDef_lsize20 sz rfl
      (evalArgs_cons (evalExp_subE_iff.2 (evalExp_var rfl)) evalArgs_nil))))


/-! ## The premise-bound quantifiers are typed -/

theorem findTyp_Jnn20 : (simEnv20 B).findTyp? "Jnn" = some ([], [.instD [] [] (.variantT
    [.mk "I32" (.tupT []) [] [], .mk "I64" (.tupT []) [] [], .mk "I8" (.tupT []) [] [],
      .mk "I16" (.tupT []) [] []])]) := rfl

theorem findTyp_M20 : (simEnv20 B).findTyp? "M" =
    some ([], [.instD [] [] (.aliasT (.varT "dim" []))]) := rfl

/-- **The lane type of a pack size is a `Jnn`.** -/
theorem typedV_jnn20 (sz : PackSize) : TypedV (simEnv20 B) (.varT "Jnn" []) (jnnV20 sz) := by
  cases sz <;> exact Pure.typedV_closedCase20 findTyp_Jnn20 rfl hasTyp_tupT_nil

/-- `i = 1 \/ i = 2 \/ i = 4 \/ i = 8 \/ i = 16`, the premise of `dim`. -/
abbrev dimPrem : Exp :=
  .binE .orOp .boolT (.binE .orOp .boolT (.binE .orOp .boolT (.binE .orOp .boolT
    (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 1))) (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 2))))
    (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 4)))) (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 8))))
    (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN 16)))

theorem findTyp_dim20 : (simEnv20 B).findTyp? "dim" = some ([], [.instD [] [] (.variantT
    [.mk "%" (.tupT [.mk "i" (.numT .natT)]) [] [.ifPr dimPrem]])]) := rfl

/-- **The lane count of a pack size is an `M`**: a `dim`, one of `1, 2, 4, 8, 16`. -/
theorem typedV_dim20 (sz : PackSize) :
    TypedV (simEnv20 B) (.varT "M" []) (pctV (128 / sz.width)) := by
  have htup : HasTyp (simEnv20 B) VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN (128 / sz.width))]) :=
    hasTyp_tupT_iff.2 ⟨_, rfl, hasTypTup_cons_iff.2 ⟨_, _, rfl, hasTyp_numT_iff.2 ⟨_, rfl, rfl⟩,
      hasTypTup_nil_iff.2 rfl⟩⟩
  have hp : PremsOk (simEnv20 B) (caseScope VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
      (.tuple [.num (.natN (128 / sz.width))])) [.ifPr dimPrem] := by
    have hi : (caseScope VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
        (.tuple [.num (.natN (128 / sz.width))])).findVal? "i" = some (.num (.natN (128 / sz.width))) :=
      rfl
    have e : ∀ m : Nat, EvalExp (simEnv20 B) (caseScope VarEnv.empty (.tupT [.mk "i" (.numT .natT)])
        (.tuple [.num (.natN (128 / sz.width))])) (.cmpE .eqOp .boolT (.varE "i") (.numE (.natN m)))
        (.bool (decide (Value.num (.natN (128 / sz.width)) = .num (.natN m)))) := fun m =>
      Sim.RefsGC.evalExp_eq (evalExp_var hi) evalExp_num
    refine Sim.IntNumeric.premsOk_if ?_
    have h := Sim.IntNumeric.evalExp_orB (t := .boolT) (Sim.IntNumeric.evalExp_orB (t := .boolT)
      (Sim.IntNumeric.evalExp_orB (t := .boolT) (Sim.IntNumeric.evalExp_orB (t := .boolT) (e 1) (e 2))
        (e 4)) (e 8)) (e 16)
    cases sz <;> simpa [PackSize.width] using h
  exact typedV_aliasG findTyp_M20 (hasTyp_varT_case rfl findTyp_dim20 Equiv.evalArgs_nil
    matchArgs_nil ((hasTypCase_cons_hit_iff rfl).2 ⟨htup, hp⟩))


/-! ## Rule 18 -/

/-- The shape `Jnn X M` in the rule. -/
abbrev shapeE : Exp :=
  .caseE "%X%" (.tupE [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"])

/-- `$ibytes_(N, $lanes_(Jnn X M, c)[j])`. -/
abbrev laneBytesE : Exp :=
  .callE "ibytes_" [.expA (.varE "N"), .expA (.caseE "%" (.tupE [.projE (.uncaseE (.idxE
    (.callE "lanes_" [.expA shapeE, .expA (.varE "c")]) (.projE (.uncaseE (.varE "j") "%") 0))
    "%") 0]))]

/-- `128 / N`, over the rationals. -/
abbrev lanesRatE : Exp :=
  .binE .divOp (.numT .ratT) (.cvtE (.numE (.natN 128)) .natT .ratT) (.cvtE (.varE "N") .natT .ratT)

/-- `Step/vstore_lane-val`, rule 18 of `Step` (verbatim). -/
def vstoreLaneValRule : Rule :=
  .ruleD "vstore_lane-val" [.expP "z" (.varT "state" []), .expP "i" (.varT "num_" [.expA
    (.caseE "I32" (.tupE []))]), .expP "c" (.varT "vec_" [.expA (.caseE "V128" (.tupE []))]),
    .expP "N" (.varT "N" []), .expP "ao" (.varT "memarg" []), .expP "j" (.varT "laneidx" []),
    .expP "b*" (.iterT (.varT "byte" []) .list), .expP "Jnn" (.varT "Jnn" []),
    .expP "M" (.varT "M" [])] "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
      .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]),
      .caseE "VSTORE_LANE" (.tupE [.caseE "V128" (.tupE []), .caseE "%" (.tupE [.varE "N"]),
        .varE "ao", .varE "j"])]]),
      .caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E (.varE "N")), .expA (iterVar "b" "b*")], .listE []])])
    [.ifPr (.cmpE .eqOp .boolT (.varE "N") (.callE "jsize" [.expA (.varE "Jnn")])),
     .ifPr (.cmpE .eqOp .boolT (.cvtE (.projE (.uncaseE (.varE "M") "%") 0) .natT .ratT) lanesRatE),
     .ifPr (.cmpE .eqOp .boolT (iterVar "b" "b*") laneBytesE)]

theorem hasRuleAt_vstoreLaneVal : HasRuleAt (simEnv20 B) "Step" "%~>%" 18 vstoreLaneValRule :=
  ⟨_, _, _, rfl, rfl, rfl⟩


/-- `128 / N` over the rationals is the natural lane count, at every pack size. -/
theorem lanes_rat20 (sz : PackSize) :
    ((128 : ℚ) / (sz.width : ℚ)) = (((128 / sz.width : Nat)) : ℚ) := by
  cases sz <;> norm_num [PackSize.width]

theorem width_cases20 (sz : PackSize) :
    sz.width = 8 ∨ sz.width = 16 ∨ sz.width = 32 ∨ sz.width = 64 ∨ sz.width = 128 := by
  cases sz <;> simp [PackSize.width]

/-- The lane `j` of `c`, encoded. -/
theorem getElem?_lanesV20 (sz : PackSize) (c : BitVec 128) {j : Nat} (hj : j < 128 / sz.width) :
    (lanesV20 sz c)[j]? =
      some (pctV ((Silmaril.Wasm.Numerics.lanes sz.width (128 / sz.width) c).getD j 0).toNat) := by
  have hl : j < (Silmaril.Wasm.Numerics.lanes sz.width (128 / sz.width) c).length := by
    simpa [Silmaril.Wasm.Numerics.lanes] using hj
  simp [lanesV20, List.getElem?_map, List.getElem?_eq_getElem hl]

/-- A builtin with no clauses, called. -/
theorem evalExp_builtin20 {ρ : VarEnv} {x : IL.Id} {args : List Arg} {ws : List ArgV} {v : Value}
    (hd : ∃ ps t, (simEnv20 B).findDef? x = some (ps, t, [])) (hρ : ρ.findDef? x = none)
    (ha : EvalArgs (simEnv20 B) ρ args ws) (hb : B.call x ws = some v) :
    EvalExp (simEnv20 B) ρ (.callE x args) v := by
  obtain ⟨ps, t, hf⟩ := hd
  exact evalExp_callE_iff.2 (Equiv.ExecBuiltins.callDef_of_builtin_nil hρ hf ha
    (by rw [simEnv20, Env.builtins_withBuiltins]; exact hb))

/-- **`Step/vstore_lane-val` fires forward** at the image of V2's `vecStoreLaneVal`, at builtins
answering `$lanes_` and `$ibytes_` as V2 does, from a typed state. -/
theorem fires_vstoreLaneVal (hL : LaneCalls20 B) {s : Store H} {f : Frame} {sz : PackSize}
    {ao : V2.MemArg} {j : LaneIdx} {i : BitVec 32} {c : BitVec 128} {ad : MemAddr}
    {mi mi' : MemInst} (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (ha : f.module.memAddr? memIdx0 = some ad) (hm : s.memInst? ad = some mi)
    (hj : j.val < 128 / sz.width)
    (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
      (ibytes sz.width ((Silmaril.Wasm.Numerics.lanes sz.width (128 / sz.width) c).getD j.val 0))
        = some mi') :
    Fires (simEnv20 B) "Step" 18 (.tuple [
      configV hn ⟨s, f, [constI32 i, vconst c, .plain (.vecStoreLane sz ao j)]⟩,
      configV hn ⟨s.setMemInst ad mi', f, []⟩]) := by
  let x := (Silmaril.Wasm.Numerics.lanes sz.width (128 / sz.width) c).getD j.val 0
  let w := ibytes sz.width x
  let σ : List (IL.Id × Value) := [("z", stateV hn s f), ("i", pctV i.toNat),
    ("c", pctV c.toNat), ("N", .num (.natN sz.width)), ("ao", memargV ao), ("j", pctV j.val),
    ("b*", bytesV w), ("Jnn", jnnV20 sz), ("M", pctV (128 / sz.width))]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := Pure.valsOnly_bindVals σ
  have fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) := rfl
  have fi : (VarEnv.empty.bindVals σ).findVal? "i" = some (pctV i.toNat) := rfl
  have fc : (VarEnv.empty.bindVals σ).findVal? "c" = some (pctV c.toNat) := rfl
  have fN : (VarEnv.empty.bindVals σ).findVal? "N" = some (.num (.natN sz.width)) := rfl
  have fa : (VarEnv.empty.bindVals σ).findVal? "ao" = some (memargV ao) := rfl
  have fj : (VarEnv.empty.bindVals σ).findVal? "j" = some (pctV j.val) := rfl
  have fb : (VarEnv.empty.bindVals σ).findVal? "b*" = some (bytesV w) := rfl
  have fJ : (VarEnv.empty.bindVals σ).findVal? "Jnn" = some (jnnV20 sz) := rfl
  have fM : (VarEnv.empty.bindVals σ).findVal? "M" = some (pctV (128 / sz.width)) := rfl
  have hsz : w.size = sz.width / 8 := ibytes_size _ _
  have hq : QuantsOk (simEnv20 B) (VarEnv.empty.bindVals σ)
      (match vstoreLaneValRule with | .ruleD _ qs _ _ _ => qs) :=
    QuantsOk.cons fz (hz _ hρ) (QuantsOk.cons fi ((Pure.numTyped_simEnv20 B).i32 i _ hρ)
      (QuantsOk.cons fc (typedV_vecV128_20 c _ hρ) (QuantsOk.cons fN (typedV_N20 _ _ hρ)
        (QuantsOk.cons fa (typedV_memarg20 ao _ hρ) (QuantsOk.cons fj (typedV_laneidx20 j _ hρ)
          (QuantsOk.cons fb (typedV_bytes20 w _ hρ) (QuantsOk.cons fJ (typedV_jnn20 sz _ hρ)
            (QuantsOk.cons fM (typedV_dim20 sz _ hρ) QuantsOk.nil))))))))
  have hl : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .listE [constIE,
        .caseE "VCONST" (.tupE [.caseE "V128" (.tupE []), .varE "c"]),
        .caseE "VSTORE_LANE" (.tupE [.caseE "V128" (.tupE []), .caseE "%" (.tupE [.varE "N"]),
          .varE "ao", .varE "j"])]]))
      (configV hn ⟨s, f, [constI32 i, vconst c, .plain (.vecStoreLane sz ao j)]⟩) := by
    refine evalExp_case (evalExp_tup2 (evalExp_var fz) (evalExp_listE_iff.2 ⟨_, evalExps_cons
      (evalExp_constIE fi) (evalExps_cons (evalExp_vconstE fc) (evalExps_cons
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons
          (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) (evalExps_cons
            (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_var fN) evalExps_nil,
              rfl⟩)) (evalExps_cons (evalExp_var fa) (evalExps_cons (evalExp_var fj)
                evalExps_nil))), rfl⟩)) evalExps_nil)), ?_⟩))
    rfl
  have hb : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (iterVar "b" "b*") (bytesV w) :=
    Equiv.Execution.evalExp_iterPat (by decide) fb
  have hmems : f.module.mems[memIdx0.toNat]? = some ad := by
    simpa [ModuleInst.memAddr?] using ha
  have hmi : s.mems[ad]? = some mi := by simpa [Store.memInst?] using hm
  have hw' : mi.writeBytes? (i.toNat + ao.offset.val) w.size w = some mi' := by
    rw [hsz]; exact hw
  have hwm : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "with_mem" [.expA (.varE "z"), .expA (.caseE "%" (.tupE [.numE (.natN 0)])),
        .expA (.binE .addOp (.numT .natT) iPay offE), .expA (div8E (.varE "N")),
        .expA (iterVar "b" "b*")]) (stateV hn (s.setMemInst ad mi') f) :=
    evalExp_withMem20 (x := memIdx0) rfl (evalExp_var fz)
      (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil,
        rfl⟩))
      (evalExp_addNat20 (evalExp_iPay fi) (evalExp_off fa))
      (by rw [hsz]; exact evalExp_div8 (evalExp_var fN) (width_cases20 sz)) hb hmems hmi hw'
  have hr : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.callE "with_mem" [.expA (.varE "z"),
        .expA (.caseE "%" (.tupE [.numE (.natN 0)])), .expA (.binE .addOp (.numT .natT) iPay offE),
        .expA (div8E (.varE "N")), .expA (iterVar "b" "b*")], .listE []]))
      (configV hn ⟨s.setMemInst ad mi', f, []⟩) :=
    evalExp_case (evalExp_tup2 hwm (evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩))
  -- `N = $jsize(Jnn)`
  have p₁ : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cmpE .eqOp .boolT (.varE "N") (.callE "jsize" [.expA (.varE "Jnn")])) (.bool true) :=
    evalExp_eqTrue (evalExp_var fN) (evalExp_callE_iff.2 (callDef_jsize20 sz rfl
      (evalArgs_cons (evalExp_var fJ) evalArgs_nil)))
  -- `M = 128 / N`
  have eM : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.cvtE (.projE (.uncaseE (.varE "M") "%") 0) .natT .ratT)
      (.num (.ratN ((128 / sz.width : Nat) : ℚ))) :=
    evalExp_cvtE_iff.2 ⟨_, _, Sim.RefsGC.evalExp_unpct (evalExp_var fM), rfl, rfl⟩
  have e128 : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.cvtE (.numE (.natN 128)) .natT .ratT)
      (.num (.ratN 128)) := evalExp_cvtE_iff.2 ⟨_, _, evalExp_num, rfl, rfl⟩
  have eN : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) (.cvtE (.varE "N") .natT .ratT)
      (.num (.ratN (sz.width : ℚ))) := evalExp_cvtE_iff.2 ⟨_, _, evalExp_var fN, rfl, rfl⟩
  have hN0 : (sz.width : ℚ) ≠ 0 := by cases sz <;> norm_num [PackSize.width]
  have eDiv : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) lanesRatE
      (.num (.ratN ((128 / sz.width : Nat) : ℚ))) :=
    evalExp_binE_iff.2 ⟨_, e128, .inr ⟨rfl, _, eN, by
      simp only [binValues, Num.bin, hN0, ↓reduceIte, lanes_rat20]; rfl⟩⟩
  have p₂ := evalExp_eqTrue eM eDiv
  -- `b* = $ibytes_(N, $lanes_(Jnn X M, c)[j])`
  have eSh : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) shapeE (shapeV20 sz) :=
    evalExp_case (evalExp_tup2 (evalExp_subE_iff.2 (evalExp_var fJ)) (evalExp_var fM))
  have eLanes : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.callE "lanes_" [.expA shapeE, .expA (.varE "c")]) (.list (lanesV20 sz c)) :=
    evalExp_builtin20 ⟨_, _, rfl⟩ rfl (evalArgs_cons eSh (evalArgs_cons (evalExp_var fc)
      evalArgs_nil)) (hL.lanes sz c)
  have eLane := Sim.RefsGC.evalExp_unpct (Sim.RefsGC.evalExp_idx eLanes
    (Sim.RefsGC.evalExp_unpct (evalExp_var fj)) (getElem?_lanesV20 sz c hj))
  have eArg : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ)
      (.caseE "%" (.tupE [.projE (.uncaseE (.idxE (.callE "lanes_" [.expA shapeE, .expA (.varE "c")])
        (.projE (.uncaseE (.varE "j") "%") 0)) "%") 0])) (pctV x.toNat) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons eLane evalExps_nil, rfl⟩)
  have eBytes : EvalExp (simEnv20 B) (VarEnv.empty.bindVals σ) laneBytesE (bytesV w) := by
    have h := evalExp_builtin20 (x := "ibytes_") ⟨_, _, rfl⟩ rfl
      (evalArgs_cons (evalExp_var fN) (evalArgs_cons eArg evalArgs_nil)) (hL.ibytes _ _)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  have p₃ := evalExp_eqTrue hb eBytes
  refine Pure.fires_of_ruleAt hasRuleAt_vstoreLaneVal σ hq (evalExp_tup2 hl hr) ?_
  intro pr hpr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl | rfl
  · exact .ifPr p₁
  · exact .ifPr p₂
  · exact .ifPr p₃


/-! ## The fragment and the target -/

/-- **V2's `vecStoreLaneVal`.** -/
inductive VStoreLaneValFwd20 : Config H → Config H → Prop where
  | mk {s : Store H} {f : Frame} {sz : PackSize} {ao : V2.MemArg} {j : LaneIdx} {i : BitVec 32}
      {c : BitVec 128} {a : MemAddr} {mi mi' : MemInst}
      (ha : f.module.memAddr? memIdx0 = some a) (hm : s.memInst? a = some mi)
      (hj : j.val < 128 / sz.width)
      (hw : mi.writeBytes? (effAddr i.toNat ao) (sz.width / 8)
        (ibytes sz.width ((Silmaril.Wasm.Numerics.lanes sz.width (128 / sz.width) c).getD j.val 0))
          = some mi') :
      VStoreLaneValFwd20 ⟨s, f, [constI32 i, vconst c, .plain (.vecStoreLane sz ao j)]⟩
        ⟨s.setMemInst a mi', f, []⟩

theorem VStoreLaneValFwd20.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : VStoreLaneValFwd20 c c') : Step P host c c' := by
  cases h with
  | mk ha hm hj hw => exact .vecStoreLaneVal ha hm hj hw

/-- **`vecStoreLaneVal` is a base**, at builtins answering `$lanes_` and `$ibytes_`, at any store
condition. -/
theorem fwdBase20_vstoreLaneVal {W : Store H → Prop} (hL : LaneCalls20 B) :
    FwdBase20 B hn W (VStoreLaneValFwd20 (H := H)) where
  sr c c' hc h := by
    cases h with
    | mk ha hm hj hw =>
      obtain ⟨hs, hf⟩ := typedV_stateV_iff.1 (typed20_iff.1 hc).1
      exact typed20_mk (storeTy20_setMem (typedV_storeV_iff.1 hs) _ _) hf typedV_admins_nil20
  fwd c c' hc _ h := by
    cases h with
    | mk ha hm hj hw =>
      exact sstepB20S_of_fires (stepAgreeS B 18 (by decide) _
        (fires_vstoreLaneVal hL (typedV_state_of_typed20 hc) ha hm hj hw))

/-- The widened base with both vector stores. -/
inductive FwdStep20L (P : Profile) : Config H → Config H → Prop where
  | fwd {c c' : Config H} (h : FwdStep20B P c c') : FwdStep20L P c c'
  | vstore {c c' : Config H} (h : VStoreValFwd20 c c') : FwdStep20L P c c'
  | vstoreLane {c c' : Config H} (h : VStoreLaneValFwd20 c c') : FwdStep20L P c c'

theorem FwdStep20L.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20L P c c') : Step P host c c' := by
  cases h with
  | fwd h => exact h.step
  | vstore h => exact h.step
  | vstoreLane h => exact h.step

theorem fwdBase20_fwdL {P : Profile} (hG : GrowCalls20 B) (A : Pure.NumAgree (simEnv20 B) P)
    (C : Pure.CvtAgree (simEnv20 B) P) (hV : VBytes20 B) (hL : LaneCalls20 B) :
    FwdBase20 B hn WholePages (FwdStep20L (H := H) P) where
  sr c c' hc h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdB hG A C).sr c c' hc h
    | vstore h => exact (fwdBase20_vstoreVal (W := WholePages) hV).sr c c' hc h
    | vstoreLane h => exact (fwdBase20_vstoreLaneVal (W := WholePages) hL).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | fwd h => exact (fwdBase20_fwdB hG A C).fwd c c' hc hw h
    | vstore h => exact (fwdBase20_vstoreVal hV).fwd c c' hc hw h
    | vstoreLane h => exact (fwdBase20_vstoreLaneVal hL).fwd c c' hc hw h

/-- **The forward 2.0 half on the widened nested fragment with both vector stores** (stated and
proved): at `laneB`, every step of `Nest20 (FwdStep20L P)` from a configuration with typed image
and whole pages is a step of the corrected script between the images, with a typed successor
image. -/
def Task.wholeStepFwd20L : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : RelaxedChoice) (c c' : Config H),
    Typed20 (simEnv20 (laneB (Profile.spec nd r))) hn c → WholePages c.store →
    Nest20 (FwdStep20L (Profile.spec nd r)) c c' →
    Typed20 (simEnv20 (laneB (Profile.spec nd r))) hn c' ∧
      SStepB (simEnv20S (laneB (Profile.spec nd r))) (configV hn c) (configV hn c')

/-- **`Task.wholeStepFwd20L` is proved.** -/
theorem wholeStepFwd20L : Task.wholeStepFwd20L := by
  intro H hn nd r c c' hc hw h
  have F := floatB_laneB (Profile.spec nd r)
  exact fwd_nest20 (fwdBase20_fwdL (growCalls20_laneB _)
    (Pure.numAgree_simEnv20 (intB_laneB _) F) (Pure.cvtAgree_simEnv20 F) (vbytes20_laneB _)
    (laneCalls20_laneB _)) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
