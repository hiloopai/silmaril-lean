module

public import Silmaril.Proofs.Wasm.SSA.Native.FwdBasic

/-! # Native adequacy, forward direction: operators on the stack -/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Native

open Silmaril.Wasm (IntType Instr BlockType)
open Silmaril.Wasm.Binaryen (BExpr evalFlat Flow)
open Silmaril.Wasm.Execution.Core (Val Store Frame)
open Silmaril.Wasm.SSA

/-- The interpreter flow of an operator result. -/
def resFlow : Res → List Val → Flow
  | .val w, stk => .normal (w.toVal :: stk)
  | .trap, _ => .trap

section
variable {H : Type} (s : Store H) (f : Frame) (stk : List Val)

theorem flat_un {t : IntType} {op : Silmaril.Wasm.IntUnOp} {a w : WVal}
    (h : UnOp.eval (.int t op) a = some w) :
    evalFlat s f (a.toVal :: stk) (.intUnOp t op) = some (s, f, .normal (w.toVal :: stk)) := by
  simp only [UnOp.eval, Option.map_eq_some_iff] at h
  obtain ⟨y, hy, rfl⟩ := h
  simp [evalFlat, asInt_toVal, hy, ofInt_toVal]

theorem flat_test {t : IntType} {a w : WVal} (h : UnOp.eval (.test t) a = some w) :
    evalFlat s f (a.toVal :: stk) (.intTestOp t .eqz) = some (s, f, .normal (w.toVal :: stk)) := by
  simp only [UnOp.eval, Option.map_eq_some_iff] at h
  obtain ⟨y, hy, rfl⟩ := h
  simp [evalFlat, asInt_toVal, hy]; rfl

theorem flat_bin {t : IntType} {op : Silmaril.Wasm.IntBinOp} {a b : WVal} {res : Res}
    (h : BinOp.eval (.int t op) a b = some res) :
    evalFlat s f (b.toVal :: a.toVal :: stk) (.intBinOp t op) = some (s, f, resFlow res stk) := by
  simp only [BinOp.eval] at h
  cases ha : a.asInt t <;> cases hb : b.asInt t <;> simp only [ha, hb, reduceCtorEq] at h
  rename_i x y
  simp only [evalFlat, asInt_toVal, ha, hb, Option.bind_eq_bind, Option.bind_some]
  cases hz : Silmaril.Wasm.Numerics.intBinOp t op x y <;> simp only [hz, Option.some.injEq] at h <;>
    subst h <;> simp [resFlow, ofInt_toVal]

theorem flat_rel {t : IntType} {op : Silmaril.Wasm.IntRelOp} {a b : WVal} {res : Res}
    (h : BinOp.eval (.rel t op) a b = some res) :
    evalFlat s f (b.toVal :: a.toVal :: stk) (.intRelOp t op) = some (s, f, resFlow res stk) := by
  simp only [BinOp.eval] at h
  cases ha : a.asInt t <;> cases hb : b.asInt t <;> simp only [ha, hb, reduceCtorEq, Option.some.injEq] at h
  subst h
  simp [evalFlat, asInt_toVal, ha, hb, resFlow]; rfl

theorem flat_select {ty : Option (List Silmaril.Wasm.ValType)} {a b c : WVal} {res : Res}
    (h : Op.eval .select [a, b, c] = some res) :
    evalFlat s f (c.toVal :: b.toVal :: a.toVal :: stk) (.select ty) = some (s, f, resFlow res stk) := by
  simp only [Op.eval, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  cases t <;> simp [evalFlat, resFlow, truthy_toVal, ht]

end

/-- The flat instruction `i` computes the operator `o` on the stack. -/
private def FlatOK {H : Type} (s : Store H) (i : Instr) (o : Op) : Prop :=
  ∀ (vs : List WVal) (res : Res) (f : Frame) (stk : List Val),
    o.eval vs = some res → evalFlat s f (vs.reverse.map WVal.toVal ++ stk) i = some (s, f, resFlow res stk)

/-- The native operators `ofInstr?` recognises, with the instruction of each. -/
private theorem ofInstr?_op_cases {i : Instr} {args args' : List Expr} {o : Op}
    (h : ofInstr? i args = some (.op o args')) (hn : o.native = true) :
    args' = args ∧ (∀ x, i ≠ .call x) ∧
      ((∃ t b, i = .intConst t b ∧ o = .const (.ofInt t b)) ∨
        (∃ t op, i = .intUnOp t op ∧ o = .un (.int t op)) ∨
        (∃ t, i = .intTestOp t .eqz ∧ o = .un (.test t)) ∨
        (∃ t op, i = .intBinOp t op ∧ o = .bin (.int t op)) ∨
        (∃ t op, i = .intRelOp t op ∧ o = .bin (.rel t op)) ∨
        (∃ ty, i = .select ty ∧ o = .select)) := by
  unfold ofInstr? at h
  split at h <;> (try split at h) <;> simp at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · exact ⟨rfl, fun _ h => Instr.noConfusion h, .inl ⟨_, _, rfl, rfl⟩⟩
  all_goals simp_all [Op.native]

section
variable {H : Type} (s : Store H)

private theorem flatOK_const (t : IntType) (b : BitVec t.width) :
    FlatOK s (.intConst t b) (.const (.ofInt t b)) := by
  intro vs res f stk hev
  match vs, hev with
  | [], hev =>
      have hres : res = .val (.ofInt t b) := (Option.some.inj hev).symm
      rw [hres]
      simp [evalFlat, resFlow, ofInt_toVal]

private theorem flatOK_un (t : IntType) (op : Silmaril.Wasm.IntUnOp) :
    FlatOK s (.intUnOp t op) (.un (.int t op)) := by
  intro vs res f stk hev
  match vs, hev with
  | [a], hev =>
      obtain ⟨w, hw, rfl⟩ : ∃ w, UnOp.eval (.int t op) a = some w ∧ Res.val w = res := by
        simpa only [Op.eval, Option.map_eq_some_iff] using hev
      exact flat_un s f stk hw

private theorem flatOK_test (t : IntType) : FlatOK s (.intTestOp t .eqz) (.un (.test t)) := by
  intro vs res f stk hev
  match vs, hev with
  | [a], hev =>
      obtain ⟨w, hw, rfl⟩ : ∃ w, UnOp.eval (.test t) a = some w ∧ Res.val w = res := by
        simpa only [Op.eval, Option.map_eq_some_iff] using hev
      exact flat_test s f stk hw

private theorem flatOK_bin (t : IntType) (op : Silmaril.Wasm.IntBinOp) :
    FlatOK s (.intBinOp t op) (.bin (.int t op)) := by
  intro vs res f stk hev
  match vs, hev with
  | [_, _], hev => exact flat_bin s f stk hev

private theorem flatOK_rel (t : IntType) (op : Silmaril.Wasm.IntRelOp) :
    FlatOK s (.intRelOp t op) (.bin (.rel t op)) := by
  intro vs res f stk hev
  match vs, hev with
  | [_, _], hev => exact flat_rel s f stk hev

private theorem flatOK_select (ty : Option (List Silmaril.Wasm.ValType)) :
    FlatOK s (.select ty) .select := by
  intro vs res f stk hev
  match vs, hev with
  | [_, _, _], hev => exact flat_select s f stk hev

end

theorem flat_op {H : Type} (s : Store H) {i : Instr} {args args' : List Expr} {o : Op}
    (h : ofInstr? i args = some (.op o args')) (hn : o.native = true) :
    args' = args ∧ (∀ x, i ≠ .call x) ∧ ∀ (vs : List WVal) (res : Res) (f : Frame) (stk : List Val),
      o.eval vs = some res → evalFlat s f (vs.reverse.map WVal.toVal ++ stk) i = some (s, f, resFlow res stk) := by
  obtain ⟨hargs, hcall, hcases⟩ := ofInstr?_op_cases h hn
  suffices hflat : FlatOK s i o from ⟨hargs, hcall, hflat⟩
  rcases hcases with ⟨t, b, hi, ho⟩ | ⟨t, op, hi, ho⟩ | ⟨t, hi, ho⟩ | ⟨t, op, hi, ho⟩ |
    ⟨t, op, hi, ho⟩ | ⟨ty, hi, ho⟩
  · exact hi ▸ ho ▸ flatOK_const s t b
  · exact hi ▸ ho ▸ flatOK_un s t op
  · exact hi ▸ ho ▸ flatOK_test s t
  · exact hi ▸ ho ▸ flatOK_bin s t op
  · exact hi ▸ ho ▸ flatOK_rel s t op
  · exact hi ▸ ho ▸ flatOK_select s ty

end Silmaril.Proofs.Wasm.SSA.Native
