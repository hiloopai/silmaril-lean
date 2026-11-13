module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Build
public import Silmaril.Proofs.Wasm.SpecTec.Meta.Sound

/-!
# Completeness: what our evaluator computes, their reduction reaches

`strict_red`: in `fixed`, an expression of the fragment whose strict value is `v` (and that
applies no `pow` to two `int`s) reduces, through encoded fragment expressions, to the literal of
`v`; `reduceF_complete` packages this as a `Reduce_exp` derivation for every typed store `S`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim (DDerives DPrem QuantsOk TypedV ValsOnly otherwise)

set_option maxRecDepth 100000

/-- Reduction between encoded fragment expressions. -/
def FRed (S : Value) : FExp → FExp → Prop :=
  Relation.ReflTransGen fun a b => MStep envF S a.enc b.enc

/-! ## `Reduce_exp` from steps -/

theorem reduce_refl_mk {S a : Value} (hS : TypedV envF (.varT "S" []) S)
    (ha : TypedV envF (.varT "exp" []) a) : MReduce envF S a a := by
  let σ : List (IL.Id × Value) := [("S", S), ("e", a)]
  have hρ := valsOnly_inst σ
  refine Sim.DDerives.rule (i := 0) findRel_reduceF (by rw [reduceF_rules]; rfl) rfl
    (σ := σ) ?_ ?_ (fun _ h => by simp at h)
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ha _ hρ) Sim.QuantsOk.nil)
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))

theorem reduce_step_mk {S a b c : Value} (hS : TypedV envF (.varT "S" []) S)
    (ha : TypedV envF (.varT "exp" []) a) (hb : TypedV envF (.varT "exp" []) b)
    (hc : TypedV envF (.varT "exp" []) c) (h₁ : MStep envF S a b) (h₂ : MReduce envF S b c) :
    MReduce envF S a c := by
  let σ : List (IL.Id × Value) := [("S", S), ("e", a), ("e''", c), ("e'", b)]
  have hρ := valsOnly_inst σ
  refine Sim.DDerives.rule (i := 1) findRel_reduceF (by rw [reduceF_rules]; rfl) rfl
    (σ := σ) ?_ ?_ (Sim.prems_two ?_ ?_)
  · exact Sim.QuantsOk.cons rfl (hS _ hρ) (Sim.QuantsOk.cons rfl (ha _ hρ)
      (Sim.QuantsOk.cons rfl (hc _ hρ) (Sim.QuantsOk.cons rfl (hb _ hρ) Sim.QuantsOk.nil)))
  · exact evalExp_tuple (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))
  · exact .rulePr Equiv.evalArgs_nil
      (evalExp_tuple (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))) h₁
  · exact .rulePr Equiv.evalArgs_nil
      (evalExp_tuple (evalExps_three (evalExp_var rfl) (evalExp_var rfl) (evalExp_var rfl))) h₂

theorem reduce_of_fred {S : Value} (hS : TypedV envF (.varT "S" []) S) {a b : FExp}
    (h : FRed S a b) : MReduce envF S a.enc b.enc := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact reduce_refl_mk hS (typedV_enc b)
  | head hab _ ih =>
    exact reduce_step_mk hS (typedV_enc _) (typedV_enc _) (typedV_enc b) hab ih

/-! ## Congruence -/

theorem fred_un {S : Value} (hS : TypedV envF (.varT "S" []) S) (op : UnOp) (t : OpTyp)
    {a a' : FExp} (h : FRed S a a') : FRed S (.un op t a) (.un op t a') :=
  Relation.ReflTransGen.lift (p := fun a b : FExp => MStep envF S a.enc b.enc) (FExp.un op t)
    (fun x y hxy => unCtx_mk hS (typedV_unop op) (typedV_enc x) (typedV_enc y) hxy) _ _ h

theorem fred_bin_l {S : Value} (hS : TypedV envF (.varT "S" []) S) (op : BinOp) (t : OpTyp)
    {a a' : FExp} (b : FExp) (h : FRed S a a') : FRed S (.bin op t a b) (.bin op t a' b) :=
  Relation.ReflTransGen.lift (p := fun a b : FExp => MStep envF S a.enc b.enc) (fun x => FExp.bin op t x b)
    (fun x y hxy => ctx1_mk stepF_3 hS (typedV_binop op) (typedV_enc x) (typedV_enc y) (typedV_enc b) hxy) _ _ h

theorem fred_bin_r {S : Value} (hS : TypedV envF (.varT "S" []) S) (op : BinOp) (t : OpTyp)
    (a : FExp) {b b' : FExp} (h : FRed S b b') : FRed S (.bin op t a b) (.bin op t a b') :=
  Relation.ReflTransGen.lift (p := fun a b : FExp => MStep envF S a.enc b.enc) (fun x => FExp.bin op t a x)
    (fun x y hxy => ctx2_mk stepF_4 hS (typedV_binop op) (typedV_enc a) (typedV_enc x) (typedV_enc y) hxy) _ _ h

theorem fred_cmp_l {S : Value} (hS : TypedV envF (.varT "S" []) S) (op : CmpOp) (t : OpTyp)
    {a a' : FExp} (b : FExp) (h : FRed S a a') : FRed S (.cmp op t a b) (.cmp op t a' b) :=
  Relation.ReflTransGen.lift (p := fun a b : FExp => MStep envF S a.enc b.enc) (fun x => FExp.cmp op t x b)
    (fun x y hxy => ctx1_mk stepF_7 hS (typedV_cmpop op) (typedV_enc x) (typedV_enc y) (typedV_enc b) hxy) _ _ h

theorem fred_cmp_r {S : Value} (hS : TypedV envF (.varT "S" []) S) (op : CmpOp) (t : OpTyp)
    (a : FExp) {b b' : FExp} (h : FRed S b b') : FRed S (.cmp op t a b) (.cmp op t a b') :=
  Relation.ReflTransGen.lift (p := fun a b : FExp => MStep envF S a.enc b.enc) (fun x => FExp.cmp op t a x)
    (fun x y hxy => ctx2_mk stepF_8 hS (typedV_cmpop op) (typedV_enc a) (typedV_enc x) (typedV_enc y) hxy) _ _ h

/-! ## Strict values are literals -/

theorem unValue_lit {op : UnOp} {u v : Value} (hu : IsLitV u)
    (h : FExp.resVal (unValue op u) = some v) : IsLitV v := by
  match u, hu with
  | .bool b, _ =>
    obtain rfl := unValue_bool h
    trivial
  | .num (.natN n), _ =>
    obtain ⟨m', hm, rfl⟩ := unValue_num h
    exact isLitV_num (un_natInt (m := .natN n) trivial hm)
  | .num (.intN i), _ =>
    obtain ⟨m', hm, rfl⟩ := unValue_num h
    exact isLitV_num (un_natInt (m := .intN i) trivial hm)

theorem binValues_lit {op : BinOp} {u w v : Value} (hu : IsLitV u) (hw : IsLitV w)
    (h : FExp.resVal (binValues op u w) = some v) : IsLitV v := by
  match u, w, hu, hw with
  | .bool _, .bool _, _, _ =>
    obtain ⟨b, rfl⟩ := binValues_bool h
    trivial
  | .num (.natN _), .num (.natN _), _, _ | .num (.natN _), .num (.intN _), _, _
  | .num (.intN _), .num (.natN _), _, _ | .num (.intN _), .num (.intN _), _, _ =>
    obtain ⟨m, hm, rfl⟩ := binValues_num h
    exact isLitV_num (bin_natInt (by trivial) (by trivial) hm)
  | .bool _, .num (.natN _), _, _ | .bool _, .num (.intN _), _, _
  | .num (.natN _), .bool _, _, _ | .num (.intN _), .bool _, _, _ =>
    simp [binValues, FExp.resVal] at h

theorem cmpValues_bool {op : CmpOp} {u w v : Value}
    (h : FExp.resVal (cmpValues op u w) = some v) : ∃ b, v = .bool b := by
  unfold cmpValues at h
  split at h
  · exact ⟨_, (by simpa [FExp.resVal] using h.symm)⟩
  · exact ⟨_, (by simpa [FExp.resVal] using h.symm)⟩
  · generalize Num.cmp _ _ _ = o at h
    cases o with
    | none => simp [Res.ofOption, FExp.resVal] at h
    | some b => exact ⟨b, (by simpa [Res.ofOption, FExp.resVal] using h.symm)⟩
  · simp [FExp.resVal] at h

theorem cmpValues_lit {op : CmpOp} {u w v : Value}
    (h : FExp.resVal (cmpValues op u w) = some v) : IsLitV v := by
  obtain ⟨b, rfl⟩ := cmpValues_bool h
  trivial

theorem strict_lit : ∀ {e : FExp} {v : Value}, e.strict = some v → IsLitV v
  | .bool _, _, h => by cases h; trivial
  | .nat _, _, h => by cases h; trivial
  | .int _, _, h => by cases h; trivial
  | .un _ _ a, _, h => by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    exact unValue_lit (strict_lit hu) h
  | .bin _ _ a b, _, h => by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
    exact binValues_lit (strict_lit hu) (strict_lit hw) h
  | .cmp _ _ a b, _, h => by
    obtain ⟨u, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨w, -, h⟩ := Option.bind_eq_some_iff.1 h
    exact cmpValues_lit h

/-! ## The last step: an operator on literals -/

theorem resVal_ok {r : Res Value} {v : Value} (h : FExp.resVal r = some v) : r = .ok v := by
  cases r <;> simp_all [FExp.resVal]

theorem natInt_of_lit {m : Num} (h : IsLitV (.num m)) : NatInt m := by
  cases m <;> simp_all [IsLitV, NatInt]

theorem numunop_typed {op : UnOp} {m m' : Num} (h : Num.un op m = some m') :
    TypedV envF (.varT "numunop" []) (encUnOp op) := by
  cases op
  case notOp => simp [Num.un] at h
  all_goals exact typedV_nullary variant_numunop rfl

theorem boolbinop_typed {op : BinOp} {b₁ b₂ : Bool} {c : Bool} (h : boolBin op b₁ b₂ = some c) :
    TypedV envF (.varT "boolbinop" []) (encBinOp op) := by
  cases op <;> first | exact typedV_nullary variant_boolbinop rfl | simp [boolBin] at h

theorem numbinop_typed {op : BinOp} {a b m : Num} (h : Num.bin op a b = some m) :
    TypedV envF (.varT "numbinop" []) (encBinOp op) := by
  cases op <;> first | exact typedV_nullary variant_numbinop rfl | simp [Num.bin] at h

theorem numcmpop_typed {op : CmpOp} {a b : Num} {c : Bool} (h : Num.cmp op a b = some c) :
    TypedV envF (.varT "numcmpop" []) (encCmpOp op) := by
  cases op <;> first | exact typedV_nullary variant_numcmpop rfl | simp [Num.cmp] at h

theorem unValue_bool_op {op : UnOp} {b : Bool} {v : Value}
    (h : FExp.resVal (unValue op (.bool b)) = some v) : op = .notOp := by
  cases op <;> simp_all [unValue, FExp.resVal]

theorem step_un {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : UnOp} {u v : Value}
    (hu : IsLitV u) (h : FExp.resVal (unValue op u) = some v) :
    MStep envF S (con "UN" [encUnOp op, encVal u]) (encVal v) := by
  match u, hu with
  | .bool b, _ =>
    obtain rfl := unValue_bool h
    obtain rfl := unValue_bool_op h
    exact unBool_mk hS b
  | .num (.natN n), _ =>
    obtain ⟨m', hm', rfl⟩ := unValue_num h
    exact unNum_mk hS (numunop_typed hm') (m := .natN n) trivial hm'
  | .num (.intN i), _ =>
    obtain ⟨m', hm', rfl⟩ := unValue_num h
    exact unNum_mk hS (numunop_typed hm') (m := .intN i) trivial hm'

theorem binValues_boolBin {op : BinOp} {b₁ b₂ c : Bool}
    (h : binValues op (.bool b₁) (.bool b₂) = .ok (.bool c)) : boolBin op b₁ b₂ = some c := by
  cases hb : boolBin op b₁ b₂ <;> simp_all [binValues, Res.ofOption]

theorem step_bin_num {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : BinOp} {m₁ m₂ : Num}
    {v : Value} (hm₁ : NatInt m₁) (hm₂ : NatInt m₂) (hp : ¬ IntPow op m₁ m₂)
    (h : FExp.resVal (binValues op (.num m₁) (.num m₂)) = some v) :
    MStep envF S (con "BIN" [encBinOp op, encNum m₁, encNum m₂]) (encVal v) := by
  obtain ⟨m, hm, rfl⟩ := binValues_num h
  exact binNum_mk hS (numbinop_typed hm) hm₁ hm₂ hp hm

theorem step_bin {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : BinOp} {u w v : Value}
    (hu : IsLitV u) (hw : IsLitV w) (h : FExp.resVal (binValues op u w) = some v)
    (hp : op = .powOp → ∀ i j : Int, u = .num (.intN i) → w = .num (.intN j) → False) :
    MStep envF S (con "BIN" [encBinOp op, encVal u, encVal w]) (encVal v) := by
  have hp' : ∀ m₁ m₂, u = .num m₁ → w = .num m₂ → ¬ IntPow op m₁ m₂ := by
    rintro m₁ m₂ rfl rfl ⟨hop, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
    exact hp hop i j rfl rfl
  match u, w, hu, hw with
  | .bool b₁, .bool b₂, _, _ =>
    obtain ⟨c, rfl⟩ := binValues_bool h
    exact binBool_mk hS (boolbinop_typed (binValues_boolBin (resVal_ok h))) (resVal_ok h)
  | .num (.natN _), .num (.natN _), _, _ =>
    exact step_bin_num hS (by trivial) (by trivial) (hp' _ _ rfl rfl) h
  | .num (.natN _), .num (.intN _), _, _ =>
    exact step_bin_num hS (by trivial) (by trivial) (hp' _ _ rfl rfl) h
  | .num (.intN _), .num (.natN _), _, _ =>
    exact step_bin_num hS (by trivial) (by trivial) (hp' _ _ rfl rfl) h
  | .num (.intN _), .num (.intN _), _, _ =>
    exact step_bin_num hS (by trivial) (by trivial) (hp' _ _ rfl rfl) h
  | .bool _, .num (.natN _), _, _ | .bool _, .num (.intN _), _, _
  | .num (.natN _), .bool _, _, _ | .num (.intN _), .bool _, _, _ =>
    simp [binValues, FExp.resVal] at h

theorem cmpValues_ord {op : CmpOp} (h₁ : op ≠ .eqOp) (h₂ : op ≠ .neOp) {u w v : Value}
    (h : FExp.resVal (cmpValues op u w) = some v) :
    ∃ m₁ m₂ b, u = .num m₁ ∧ w = .num m₂ ∧ Num.cmp op m₁ m₂ = some b ∧ v = .bool b := by
  unfold cmpValues at h
  split at h
  · exact absurd rfl h₁
  · exact absurd rfl h₂
  · rename_i m₁ m₂ _ _
    cases hc : Num.cmp op m₁ m₂ with
    | none => simp [hc, Res.ofOption, FExp.resVal] at h
    | some b => exact ⟨m₁, m₂, b, rfl, rfl, hc,
        (by simpa [hc, Res.ofOption, FExp.resVal] using h.symm)⟩
  · simp [FExp.resVal] at h

theorem step_cmp_eq {S : Value} (hS : TypedV envF (.varT "S" []) S) {u w : Value}
    (hu : IsLitV u) (hw : IsLitV w) :
    MStep envF S (con "CMP" [encCmpOp .eqOp, encVal u, encVal w]) (encVal (.bool (u == w))) := by
  by_cases e : u = w
  · subst e
    rw [beq_self_eq_true u]
    exact cmpVal_mk stepF_9 hS hu hu (by simp [cmpValues])
  · have e' : encVal u ≠ encVal w := fun h' => e (encVal_inj hu hw h')
    have hb : (u == w) = false := by simpa using e
    rw [hb]
    exact cmpVal_mk stepF_10 hS hu hw (by simp [cmpValues, e'])

theorem step_cmp_ne {S : Value} (hS : TypedV envF (.varT "S" []) S) {u w : Value}
    (hu : IsLitV u) (hw : IsLitV w) :
    MStep envF S (con "CMP" [encCmpOp .neOp, encVal u, encVal w])
      (encVal (.bool (!(u == w)))) := by
  by_cases e : u = w
  · subst e
    rw [beq_self_eq_true u]
    exact cmpVal_mk stepF_11 hS hu hu (by simp [cmpValues])
  · have e' : encVal u ≠ encVal w := fun h' => e (encVal_inj hu hw h')
    have hb : (u == w) = false := by simpa using e
    rw [hb]
    exact cmpVal_mk stepF_12 hS hu hw (by simp [cmpValues, e'])

theorem step_cmp {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : CmpOp} {u w v : Value}
    (hu : IsLitV u) (hw : IsLitV w) (h : FExp.resVal (cmpValues op u w) = some v) :
    MStep envF S (con "CMP" [encCmpOp op, encVal u, encVal w]) (encVal v) := by
  by_cases h₁ : op = .eqOp
  · subst h₁
    have hv : v = .bool (u == w) := by simpa [cmpValues, FExp.resVal, eq_comm] using h
    rw [hv]; exact step_cmp_eq hS hu hw
  by_cases h₂ : op = .neOp
  · subst h₂
    have hv : v = .bool (!(u == w)) := by simpa [cmpValues, FExp.resVal, eq_comm] using h
    rw [hv]; exact step_cmp_ne hS hu hw
  obtain ⟨m₁, m₂, b, rfl, rfl, hc, rfl⟩ := cmpValues_ord h₁ h₂ h
  exact cmpNum_mk hS (numcmpop_typed hc) (natInt_of_lit hu) (natInt_of_lit hw) hc

/-! ## Completeness -/

theorem complete_un {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : UnOp} {t : OpTyp}
    {a la : FExp} {u v : Value} (hr : FRed S a la) (hla : la.enc = encVal u) (hu : a.strict = some u)
    (h : FExp.resVal (unValue op u) = some v) :
    ∃ l : FExp, FRed S (.un op t a) l ∧ l.enc = encVal v := by
  obtain ⟨l, -, hl, -⟩ := litOf_spec (unValue_lit (strict_lit hu) h)
  refine ⟨l, (fred_un hS op t hr).tail ?_, hl⟩
  show MStep envF S (con "UN" [encUnOp op, la.enc]) l.enc
  rw [hla, hl]
  exact step_un hS (strict_lit hu) h

theorem complete_bin {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : BinOp} {t : OpTyp}
    {a b la lb : FExp} {u w v : Value} (hra : FRed S a la) (hla : la.enc = encVal u)
    (hrb : FRed S b lb) (hlb : lb.enc = encVal w) (hu : a.strict = some u) (hw : b.strict = some w)
    (h : FExp.resVal (binValues op u w) = some v)
    (hp : op = .powOp → ∀ i j : Int, u = .num (.intN i) → w = .num (.intN j) → False) :
    ∃ l : FExp, FRed S (.bin op t a b) l ∧ l.enc = encVal v := by
  obtain ⟨l, -, hl, -⟩ := litOf_spec (binValues_lit (strict_lit hu) (strict_lit hw) h)
  refine ⟨l, ((fred_bin_l hS op t b hra).trans (fred_bin_r hS op t la hrb)).tail ?_, hl⟩
  show MStep envF S (con "BIN" [encBinOp op, la.enc, lb.enc]) l.enc
  rw [hla, hlb, hl]
  exact step_bin hS (strict_lit hu) (strict_lit hw) h hp

theorem complete_cmp {S : Value} (hS : TypedV envF (.varT "S" []) S) {op : CmpOp} {t : OpTyp}
    {a b la lb : FExp} {u w v : Value} (hra : FRed S a la) (hla : la.enc = encVal u)
    (hrb : FRed S b lb) (hlb : lb.enc = encVal w) (hu : a.strict = some u) (hw : b.strict = some w)
    (h : FExp.resVal (cmpValues op u w) = some v) :
    ∃ l : FExp, FRed S (.cmp op t a b) l ∧ l.enc = encVal v := by
  obtain ⟨l, -, hl, -⟩ := litOf_spec (cmpValues_lit h)
  refine ⟨l, ((fred_cmp_l hS op t b hra).trans (fred_cmp_r hS op t la hrb)).tail ?_, hl⟩
  show MStep envF S (con "CMP" [encCmpOp op, la.enc, lb.enc]) l.enc
  rw [hla, hlb, hl]
  exact step_cmp hS (strict_lit hu) (strict_lit hw) h

/-- **Every strict value is reached.** -/
theorem strict_red {S : Value} (hS : TypedV envF (.varT "S" []) S) :
    ∀ (e : FExp), e.NoIntPow → ∀ v, e.strict = some v →
      ∃ l : FExp, FRed S e l ∧ l.enc = encVal v
  | .bool _, _, _, h => ⟨_, .refl, by cases h; rfl⟩
  | .nat _, _, _, h => ⟨_, .refl, by cases h; rfl⟩
  | .int _, _, _, h => ⟨_, .refl, by cases h; rfl⟩
  | .un _ _ a, hn, _, h => by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨la, hr, hla⟩ := strict_red hS a hn u hu
    exact complete_un hS hr hla hu h
  | .bin _ _ a b, ⟨hna, hnb, hp⟩, _, h => by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨la, hra, hla⟩ := strict_red hS a hna u hu
    obtain ⟨lb, hrb, hlb⟩ := strict_red hS b hnb w hw
    exact complete_bin hS hra hla hrb hlb hu hw h fun hop i j hi hj =>
      hp hop i j (hi ▸ hu) (hj ▸ hw)
  | .cmp _ _ a b, ⟨hna, hnb⟩, _, h => by
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨la, hra, hla⟩ := strict_red hS a hna u hu
    obtain ⟨lb, hrb, hlb⟩ := strict_red hS b hnb w hw
    exact complete_cmp hS hra hla hrb hlb hu hw h

/-- **Their reduction is complete for ours** (fixed script). -/
theorem reduceF_complete {S : Value} (hS : TypedV envF (.varT "S" []) S) {e : FExp}
    (hn : e.NoIntPow) {v : Value} (h : e.strict = some v) : MReduce envF S e.enc (encVal v) := by
  obtain ⟨l, hr, hl⟩ := strict_red hS e hn v h
  have hred := reduce_of_fred hS hr
  rwa [hl] at hred

end Silmaril.Wasm.SpecTec.Meta
