module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumCheck

/-!
# `VecNumAgree`: refuted at round 7's builtins, discharged at `vecNB P`

Every clause of `$vunop_`, `$vbinop_` and `$vrelop_` definitely fails (`VecNumCheck`), so a call
denotes exactly what the builtins answer (`applies_vunop`, `applies_vbinop`, `applies_vrelop`).
Hence:

* **`not_vecNumAgree`**: `VecLane.VecNumAgree (simEnv20V B) P` fails for every `B` that does not
  answer `$vunop_`; in particular at round 7's `VecLane.vecB P` (`not_vecNumAgree_vecB`).
* **`vecNumAgree_vecNB`**: it holds at `vecNB P`, all six fields (the 42 float operators and the
  integer ones).
* `vecNB_call_of_ne`: away from the three dispatchers, `vecNB P` answers as `vecB P`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecNum

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V)
open Silmaril.Wasm.SpecTec.Sim20.VecLane (VecNumAgree)

/-! ## Calls denote the builtins' answers -/

/-- Where every clause definitely fails, a call denotes exactly what the builtins answer. -/
theorem applies_iff_of_undef {env : Env} {x : IL.Id} {ws : List ArgV} {v : Value}
    {ps : List Param} {t : Typ} {cs : List Clause} (hd : env.findDef? x = some (ps, t, cs))
    (hu : TryClausesUndef env cs ws) :
    Applies env x ws v ↔ env.builtins.call x ws = some v := by
  constructor
  · rintro ⟨ps', t', cs', hd', hc⟩
    rw [hd] at hd'
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hd'
    rcases hc with hc | ⟨-, hb⟩
    · exact absurd hu (fun h => Equiv.ExecNumeric.not_tryClauses_and_undef hc h)
    · exact hb
  · intro hb
    exact ⟨ps, t, cs, hd, Or.inr ⟨hu, hb⟩⟩

/-- **`$vunop_` denotes exactly what `B` answers**, at every argument list. -/
theorem applies_vunop (B : Builtins) (ws : List ArgV) (v : Value) :
    Applies (simEnv20V B) "vunop_" ws v ↔ B.call "vunop_" ws = some v := by
  obtain ⟨ps, t, hd⟩ := findDef_vunop B
  exact applies_iff_of_undef hd (tryClausesUndef_of_all _ _ _ clauseUnb_vunop)

/-- **`$vbinop_` denotes exactly what `B` answers.** -/
theorem applies_vbinop (B : Builtins) (ws : List ArgV) (v : Value) :
    Applies (simEnv20V B) "vbinop_" ws v ↔ B.call "vbinop_" ws = some v := by
  obtain ⟨ps, t, hd⟩ := findDef_vbinop B
  exact applies_iff_of_undef hd (tryClausesUndef_of_all _ _ _ clauseUnb_vbinop)

/-- **`$vrelop_` denotes exactly what `B` answers.** -/
theorem applies_vrelop (B : Builtins) (ws : List ArgV) (v : Value) :
    Applies (simEnv20V B) "vrelop_" ws v ↔ B.call "vrelop_" ws = some v := by
  obtain ⟨ps, t, hd⟩ := findDef_vrelop B
  exact applies_iff_of_undef hd (tryClausesUndef_of_all _ _ _ clauseUnb_vrelop)

/-! ## The refutation -/

/-- **`VecNumAgree` fails wherever `$vunop_` is not answered**: its float unary field asks for a
value of `$vunop_`, and the clauses give none. -/
theorem not_vecNumAgree {B : Builtins} {P : Profile} (hB : ∀ ws, B.call "vunop_" ws = none) :
    ¬ VecNumAgree (simEnv20V B) P := by
  intro h
  obtain ⟨vs, ha, -⟩ := h.floatUn .f32x4 .abs 0
  rw [applies_vunop, hB] at ha
  cases ha

/-- Round 7's builtins do not answer `$vunop_`. -/
theorem vecB_vunop (P : Profile) (ws : List ArgV) : (VecLane.vecB P).call "vunop_" ws = none := by
  simp [VecLane.vecB, Whole.storeB, Whole.laneB, Whole.vbytesB, Whole.growB, Sim.Floats.floatIntB,
    Sim.Floats.floatNames, Sim.IntNumeric.intCall]

/-- **`VecNumAgree` is false at round 7's builtins `vecB P`.** -/
theorem not_vecNumAgree_vecB (P : Profile) : ¬ VecNumAgree (simEnv20V (VecLane.vecB P)) P :=
  not_vecNumAgree (vecB_vunop P)

/-! ## Decoding -/

theorem dec_enc {α : Type} {enc : α → List ArgV} (hinj : Function.Injective enc) (a : α) :
    dec enc (enc a) = some a := by
  unfold dec
  split
  · rename_i h
    exact congrArg some (hinj (Classical.choose_spec h))
  · rename_i h
    exact absurd ⟨a, rfl⟩ h

theorem dec_none {α : Type} {enc : α → List ArgV} {ws : List ArgV} (h : ∀ a, enc a ≠ ws) :
    dec enc ws = none := by
  unfold dec
  split
  · rename_i h'
    obtain ⟨a, ha⟩ := h'
    exact absurd ha (h a)
  · rfl

theorem pctV_toNat_inj {a b : BitVec 128} (h : pctV a.toNat = pctV b.toNat) : a = b :=
  BitVec.eq_of_toNat_eq (by simpa [pctV] using h)

theorem shapeV_float_inj {s s' : FloatShape} (h : shapeV (.float s) = shapeV (.float s')) :
    s = s' := by
  cases s <;> cases s' <;> simp_all [shapeV, fnnV, caseNilV, dimV, pctV, FloatShape.lanes]

theorem shapeV_int_inj {s s' : IntShape} (h : shapeV (.int s) = shapeV (.int s')) : s = s' := by
  cases s <;> cases s' <;> simp_all [shapeV, ishapeV, jnnV, caseNilV, dimV, pctV, IntShape.lanes]

theorem shapeV_int_ne_float (s : IntShape) (s' : FloatShape) :
    shapeV (.int s) ≠ shapeV (.float s') := by
  cases s <;> cases s' <;> simp [shapeV, ishapeV, jnnV, fnnV, caseNilV]

theorem sxV_inj {a b : Signedness} (h : sxV a = sxV b) : a = b := by
  cases a <;> cases b <;> simp_all [sxV, caseNilV]

theorem floatUnOpV_inj {a b : FloatUnOp} (h : floatUnOpV a = floatUnOpV b) : a = b := by
  cases a <;> cases b <;> simp_all [floatUnOpV, caseNilV]

theorem vecFloatBinOpV_inj {a b : V2.VecFloatBinOp} (h : vecFloatBinOpV a = vecFloatBinOpV b) :
    a = b := by
  cases a <;> cases b <;> simp_all [vecFloatBinOpV, caseNilV]

theorem floatRelOpV_inj {a b : FloatRelOp} (h : floatRelOpV a = floatRelOpV b) : a = b := by
  cases a <;> cases b <;> simp_all [floatRelOpV, caseNilV]

theorem vecIntUnOpV_inj {a b : VecIntUnOp} (h : vecIntUnOpV a = vecIntUnOpV b) : a = b := by
  cases a <;> cases b <;> simp_all [vecIntUnOpV, caseNilV]

theorem vecIntBinOpV_inj {a b : V2.VecIntBinOp} (h : vecIntBinOpV a = vecIntBinOpV b) : a = b := by
  cases a <;> cases b <;> simp [vecIntBinOpV, caseNilV, sxV] at h ⊢ <;>
    exact sxV_inj h

theorem vecIntRelOpV_inj {a b : IntRelOp} (h : vecIntRelOpV a = vecIntRelOpV b) : a = b := by
  cases a <;> cases b <;> simp [vecIntRelOpV, caseNilV, sxV] at h ⊢ <;>
    exact sxV_inj h

theorem encFU_inj : Function.Injective encFU := by
  rintro ⟨s, o, c⟩ ⟨s', o', c'⟩ h
  simp only [encFU, List.cons.injEq, ArgV.val.injEq, and_true] at h
  rw [shapeV_float_inj h.1, floatUnOpV_inj h.2.1, pctV_toNat_inj h.2.2]

theorem encFB_inj : Function.Injective encFB := by
  rintro ⟨s, o, c, d⟩ ⟨s', o', c', d'⟩ h
  simp only [encFB, List.cons.injEq, ArgV.val.injEq, and_true] at h
  rw [shapeV_float_inj h.1, vecFloatBinOpV_inj h.2.1, pctV_toNat_inj h.2.2.1,
    pctV_toNat_inj h.2.2.2]

theorem encFR_inj : Function.Injective encFR := by
  rintro ⟨s, o, c, d⟩ ⟨s', o', c', d'⟩ h
  simp only [encFR, List.cons.injEq, ArgV.val.injEq, and_true] at h
  rw [shapeV_float_inj h.1, floatRelOpV_inj h.2.1, pctV_toNat_inj h.2.2.1, pctV_toNat_inj h.2.2.2]

theorem encIU_inj : Function.Injective encIU := by
  rintro ⟨s, o, c⟩ ⟨s', o', c'⟩ h
  simp only [encIU, List.cons.injEq, ArgV.val.injEq, and_true] at h
  rw [shapeV_int_inj h.1, vecIntUnOpV_inj h.2.1, pctV_toNat_inj h.2.2]

theorem encIB_inj : Function.Injective encIB := by
  rintro ⟨s, o, c, d⟩ ⟨s', o', c', d'⟩ h
  simp only [encIB, List.cons.injEq, ArgV.val.injEq, and_true] at h
  rw [shapeV_int_inj h.1, vecIntBinOpV_inj h.2.1, pctV_toNat_inj h.2.2.1, pctV_toNat_inj h.2.2.2]

theorem encIR_inj : Function.Injective encIR := by
  rintro ⟨s, o, c, d⟩ ⟨s', o', c', d'⟩ h
  simp only [encIR, List.cons.injEq, ArgV.val.injEq, and_true] at h
  rw [shapeV_int_inj h.1, vecIntRelOpV_inj h.2.1, pctV_toNat_inj h.2.2.1, pctV_toNat_inj h.2.2.2]

theorem decFU_encIU (a : IntShape × VecIntUnOp × BitVec 128) : dec encFU (encIU a) = none :=
  dec_none fun b h => shapeV_int_ne_float a.1 b.1
    (by simp only [encFU, encIU, List.cons.injEq, ArgV.val.injEq] at h; exact h.1.symm)

theorem decFB_encIB (a : IntShape × V2.VecIntBinOp × BitVec 128 × BitVec 128) :
    dec encFB (encIB a) = none :=
  dec_none fun b h => shapeV_int_ne_float a.1 b.1
    (by simp only [encFB, encIB, List.cons.injEq, ArgV.val.injEq] at h; exact h.1.symm)

theorem decFR_encIR (a : IntShape × IntRelOp × BitVec 128 × BitVec 128) :
    dec encFR (encIR a) = none :=
  dec_none fun b h => shapeV_int_ne_float a.1 b.1
    (by simp only [encFR, encIR, List.cons.injEq, ArgV.val.injEq] at h; exact h.1.symm)

/-! ## The answers of `vecNB P` -/

theorem mem_bitsWhere {R : BitVec 128 → Prop} {b : BitVec 128} :
    b ∈ Sim.Floats.bitsWhere 128 R ↔ R b := by
  classical
  simp only [Sim.Floats.bitsWhere, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
  exact fun _ => List.mem_map.2 ⟨b.toNat, List.mem_range.2 b.isLt, by simp⟩

theorem mem_resList {R : BitVec 128 → Prop} {w : Value} :
    w ∈ (Sim.Floats.bitsWhere 128 R).map (fun r => pctV r.toNat) ↔ ∃ r, R r ∧ w = pctV r.toNat := by
  simp only [List.mem_map, mem_bitsWhere]
  exact ⟨fun ⟨r, hr, e⟩ => ⟨r, hr, e.symm⟩, fun ⟨r, hr, e⟩ => ⟨r, hr, e.symm⟩⟩

/-- Away from the three dispatchers, `vecNB P` answers as `vecB P`. -/
theorem vecNB_call_of_ne {P : Profile} {x : IL.Id} (h₁ : x ≠ "vunop_") (h₂ : x ≠ "vbinop_")
    (h₃ : x ≠ "vrelop_") (ws : List ArgV) : (vecNB P).call x ws = (VecLane.vecB P).call x ws := by
  simp [vecNB, vecNCall, h₁, h₂, h₃]

theorem vecNB_vunop (P : Profile) (ws : List ArgV) :
    (vecNB P).call "vunop_" ws = (vunopCall P ws).or ((VecLane.vecB P).call "vunop_" ws) := by
  simp [vecNB, vecNCall]

theorem vecNB_vbinop (P : Profile) (ws : List ArgV) :
    (vecNB P).call "vbinop_" ws = (vbinopCall P ws).or ((VecLane.vecB P).call "vbinop_" ws) := by
  simp [vecNB, vecNCall]

theorem vecNB_vrelop (P : Profile) (ws : List ArgV) :
    (vecNB P).call "vrelop_" ws = (vrelopCall ws).or ((VecLane.vecB P).call "vrelop_" ws) := by
  simp [vecNB, vecNCall]

theorem vunopCall_F (P : Profile) (a : FloatShape × FloatUnOp × BitVec 128) :
    vunopCall P (encFU a) = some (resList (VecFloatUnOpResult P a.1 a.2.1 a.2.2)) := by
  simp only [vunopCall, dec_enc encFU_inj a, Option.map_some, Option.some_or]

theorem vunopCall_I (P : Profile) (a : IntShape × VecIntUnOp × BitVec 128) :
    vunopCall P (encIU a) = some (resList (VecIntUnOpResult a.1 a.2.1 a.2.2)) := by
  simp only [vunopCall, decFU_encIU a, dec_enc encIU_inj a, Option.map_some, Option.map_none,
    Option.none_or]

theorem vbinopCall_F (P : Profile) (a : FloatShape × V2.VecFloatBinOp × BitVec 128 × BitVec 128) :
    vbinopCall P (encFB a) = some (resList (VecFloatBinOpResult P a.1 a.2.1 a.2.2.1 a.2.2.2)) := by
  simp only [vbinopCall, dec_enc encFB_inj a, Option.map_some, Option.some_or]

theorem vbinopCall_I (P : Profile) (a : IntShape × V2.VecIntBinOp × BitVec 128 × BitVec 128) :
    vbinopCall P (encIB a) = some (resList (VecIntBinOpResult P a.1 a.2.1 a.2.2.1 a.2.2.2)) := by
  simp only [vbinopCall, decFB_encIB a, dec_enc encIB_inj a, Option.map_some, Option.map_none,
    Option.none_or]

theorem vrelopCall_F (a : FloatShape × FloatRelOp × BitVec 128 × BitVec 128) :
    vrelopCall (encFR a) = some (pctV (VecFloatRelOp a.1 a.2.1 a.2.2.1 a.2.2.2).toNat) := by
  simp only [vrelopCall, dec_enc encFR_inj a, Option.map_some, Option.some_or]

theorem vrelopCall_I (a : IntShape × IntRelOp × BitVec 128 × BitVec 128) :
    vrelopCall (encIR a) = some (pctV (VecIntRelOp a.1 a.2.1 a.2.2.1 a.2.2.2).toNat) := by
  simp only [vrelopCall, decFR_encIR a, dec_enc encIR_inj a, Option.map_some, Option.map_none,
    Option.none_or]

/-- **`VecNumAgree` holds at `vecNB P`**: all six fields, the float operators and the integer
ones. -/
theorem vecNumAgree_vecNB (P : Profile) : VecNumAgree (simEnv20V (vecNB P)) P where
  floatUn s op c := ⟨_, (applies_vunop _ (encFU (s, op, c)) _).2
    (by rw [vecNB_vunop, vunopCall_F]; rfl), fun _ => mem_resList⟩
  floatBin s op c₁ c₂ := ⟨_, (applies_vbinop _ (encFB (s, op, c₁, c₂)) _).2
    (by rw [vecNB_vbinop, vbinopCall_F]; rfl), fun _ => mem_resList⟩
  floatRel s op c₁ c₂ := (applies_vrelop _ (encFR (s, op, c₁, c₂)) _).2
    (by rw [vecNB_vrelop, vrelopCall_F]; rfl)
  intUn s op c := ⟨_, (applies_vunop _ (encIU (s, op, c)) _).2
    (by rw [vecNB_vunop, vunopCall_I]; rfl), fun _ => mem_resList⟩
  intBin s op c₁ c₂ := ⟨_, (applies_vbinop _ (encIB (s, op, c₁, c₂)) _).2
    (by rw [vecNB_vbinop, vbinopCall_I]; rfl), fun _ => mem_resList⟩
  intRel s op c₁ c₂ := (applies_vrelop _ (encIR (s, op, c₁, c₂)) _).2
    (by rw [vecNB_vrelop, vrelopCall_I]; rfl)

end Silmaril.Wasm.SpecTec.Sim20.VecNum
