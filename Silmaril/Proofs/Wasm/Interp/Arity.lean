module

public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Execution.Core.Typing.Store

@[expose] public section

/-!
# The arity check is sound for native evaluation (proofs)

`flowOk_of_eval`: if a sequence of native trees passes the arity check `chk` from the height of
its stack, in a store whose functions all pass it (`StoreChk`), then a native evaluation
(`Binaryen.Eval`) completes normally at the height the check computes, branches only to
existing labels carrying at least their arity, and returns at least the function's result
arity; it never throws; and it keeps the store's functions, the frame's module and its number
of locals (`EvalInv`). New proofs. Used by `Silmaril.Proofs.Wasm.Interp.Control`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- What the arity check says about a native flow. -/
def FlowOk (labels : List Nat) (ret : Nat) (out : Option Nat) : Binaryen.Flow → Prop
  | .normal vs => out = some vs.length
  | .brk l vs => ∃ n, labels[l]? = some n ∧ n ≤ vs.length
  | .ret vs => ret ≤ vs.length
  | .trap => True
  | .throw _ => False

/-! ## Function-list extension -/

/-- Function-list extension, as in Core's `Extend`: every existing function is
kept, and functions may be appended. -/
abbrev FuncsExt (F F' : List (FuncInst H)) : Prop := ExtendsList ExtendFunc F F'

theorem extendFunc_eq {a b : FuncInst H} (h : ExtendFunc a b) : a = b := by
  obtain ⟨ht, hm, hw, hh⟩ := h
  rcases a with ⟨ta, ma, ca⟩
  rcases b with ⟨tb, mb, cb⟩
  dsimp only at ht hm hw hh
  subst ht hm
  rcases ca with c | k
  · rw [hw c rfl]
  · rw [hh k rfl]

/-- Existing addresses keep their function instances. -/
theorem get_of_funcsExt {F F' : List (FuncInst H)} (h : FuncsExt F F') {i : Nat} {fi : FuncInst H}
    (hi : F[i]? = some fi) : F'[i]? = some fi := by
  obtain ⟨fi', hi', he⟩ := h.2 i fi hi
  rw [hi', extendFunc_eq he]

theorem funcsExt_refl (F : List (FuncInst H)) : FuncsExt F F :=
  ⟨Nat.le_refl _, fun _ x hx => ⟨x, hx, rfl, rfl, fun _ h => h, fun _ h => h⟩⟩

theorem funcsExt_of_eq {F F' : List (FuncInst H)} (h : F' = F) : FuncsExt F F' := h ▸ funcsExt_refl F

theorem FuncsExt.trans {F₁ F₂ F₃ : List (FuncInst H)} (h₁ : FuncsExt F₁ F₂) (h₂ : FuncsExt F₂ F₃) :
    FuncsExt F₁ F₃ := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, fun i x hx => ⟨x, get_of_funcsExt h₂ (get_of_funcsExt h₁ hx), ?_⟩⟩
  exact ⟨rfl, rfl, fun _ h => h, fun _ h => h⟩

/-- The function-list invariant of a native run: extension, keeping the store
check (with the extension `ext`) and the native profile. -/
def FuncsGoodE (ext : ExtArity H) (F F' : List (FuncInst H)) : Prop :=
  FuncsExt F F' ∧ (StoreChkE ext F → StoreChkE ext F') ∧
    (Binaryen.NativeFuncsOk F → Binaryen.NativeFuncsOk F')

/-- The function-list invariant with the native checker. -/
abbrev FuncsGood (F F' : List (FuncInst H)) : Prop := FuncsGoodE noExt F F'

theorem FuncsGoodE.refl {ext : ExtArity H} (F : List (FuncInst H)) : FuncsGoodE ext F F :=
  ⟨funcsExt_refl F, id, id⟩

theorem FuncsGoodE.of_eq {ext : ExtArity H} {F F' : List (FuncInst H)} (h : F' = F) :
    FuncsGoodE ext F F' := h ▸ FuncsGoodE.refl (ext := ext) F

theorem FuncsGoodE.trans {ext : ExtArity H} {F₁ F₂ F₃ : List (FuncInst H)}
    (h₁ : FuncsGoodE ext F₁ F₂) (h₂ : FuncsGoodE ext F₂ F₃) : FuncsGoodE ext F₁ F₃ :=
  ⟨h₁.1.trans h₂.1, h₂.2.1 ∘ h₁.2.1, h₂.2.2 ∘ h₁.2.2⟩

theorem FuncsGood.refl (F : List (FuncInst H)) : FuncsGood F F := FuncsGoodE.refl F

theorem FuncsGood.of_eq {F F' : List (FuncInst H)} (h : F' = F) : FuncsGood F F' :=
  FuncsGoodE.of_eq h

theorem FuncsGood.trans {F₁ F₂ F₃ : List (FuncInst H)} (h₁ : FuncsGood F₁ F₂) (h₂ : FuncsGood F₂ F₃) :
    FuncsGood F₁ F₃ :=
  FuncsGoodE.trans h₁ h₂

@[simp] theorem funcsGoodE_self {ext : ExtArity H} (F : List (FuncInst H)) :
    FuncsGoodE ext F F ↔ True :=
  ⟨fun _ => trivial, fun _ => FuncsGoodE.refl F⟩

theorem funcsGood_self (F : List (FuncInst H)) : FuncsGood F F ↔ True := funcsGoodE_self F

/-- The invariants of a native evaluation: the functions are extended (keeping the
store check with `ext` and the native profile), and the module and number of
locals are kept. -/
def EvalInvE (ext : ExtArity H) (s : Store H) (f : Frame) (r : Store H × Frame × Binaryen.Flow) :
    Prop :=
  FuncsGoodE ext s.funcs r.1.funcs ∧ r.2.1.module = f.module ∧ r.2.1.locals.length = f.locals.length

/-- The invariants of a native evaluation, with the native checker. -/
abbrev EvalInv (s : Store H) (f : Frame) (r : Store H × Frame × Binaryen.Flow) : Prop :=
  EvalInvE noExt s f r

theorem EvalInvE.refl {ext : ExtArity H} (s : Store H) (f : Frame) (fl : Binaryen.Flow) :
    EvalInvE ext s f (s, f, fl) :=
  ⟨FuncsGoodE.refl _, rfl, rfl⟩

theorem EvalInvE.trans {ext : ExtArity H} {s s₁ : Store H} {f f₁ : Frame} {fl : Binaryen.Flow}
    {r : Store H × Frame × Binaryen.Flow} (h₁ : EvalInvE ext s f (s₁, f₁, fl))
    (h₂ : EvalInvE ext s₁ f₁ r) : EvalInvE ext s f r :=
  ⟨h₁.1.trans h₂.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem EvalInv.refl (s : Store H) (f : Frame) (fl : Binaryen.Flow) : EvalInv s f (s, f, fl) :=
  EvalInvE.refl s f fl

theorem EvalInv.trans {s s₁ : Store H} {f f₁ : Frame} {fl : Binaryen.Flow}
    {r : Store H × Frame × Binaryen.Flow} (h₁ : EvalInv s f (s₁, f₁, fl)) (h₂ : EvalInv s₁ f₁ r) :
    EvalInv s f r :=
  EvalInvE.trans h₁ h₂

/-- An abrupt flow's check does not depend on the fall-through height. -/
theorem FlowOk.abrupt {labels : List Nat} {ret : Nat} {o o' : Option Nat} {fl : Binaryen.Flow}
    (h : FlowOk labels ret o fl) (hn : ¬ fl.IsNormal) : FlowOk labels ret o' fl := by
  cases fl <;> first | exact absurd trivial hn | exact h

/-! ## The check, unfolded -/

section UnfoldE

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat} {labels : List Nat}

@[simp] theorem chk_noneE (es : List Binaryen.BExpr) : chkE ext F mi nl ret labels none es = some none := by
  cases es <;> rfl

@[simp] theorem chk_nilE (h : Nat) : chkE ext F mi nl ret labels (some h) [] = some (some h) := rfl

theorem chk_consE {h : Nat} {e : Binaryen.BExpr} {es : List Binaryen.BExpr} {out : Option Nat} :
    chkE ext F mi nl ret labels (some h) (e :: es) = some out ↔
      ∃ o, chk1E ext F mi nl ret labels h e = some o ∧ chkE ext F mi nl ret labels o es = some out := by
  simp only[chkE, Option.bind_eq_some_iff]

theorem chk1_opE {h : Nat} {i : Instr} {args : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk1E ext F mi nl ret labels h (.op i args) = some o) :
    ∃ oa, chkE ext F mi nl ret labels (some h) args = some oa ∧
      ∀ h₁, oa = some h₁ → flatChkE ext F mi nl ret labels h₁ i = some o := by
  simp only[chk1E, Option.bind_eq_some_iff] at hc
  obtain ⟨oa, ha, hb⟩ := hc
  refine ⟨oa, ha, ?_⟩
  rintro h₁ rfl
  exact hb

theorem chk1_blockE {h : Nat} {bt : BlockType} {body : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk1E ext F mi nl ret labels h (.block bt body) = some o) :
    ∃ np nr, blockArity mi bt = some (np, nr) ∧ np ≤ h ∧
      endsAt (chkE ext F mi nl ret (nr :: labels) (some np) body) nr = true ∧
      o = some (h - np + nr) := by
  simp only[chk1E] at hc
  split at hc
  · rename_i np nr ha
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1, hcond.2, (Option.some.inj hc).symm⟩
    · cases hc
  · cases hc

theorem chk1_loopE {h : Nat} {bt : BlockType} {body : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk1E ext F mi nl ret labels h (.loop bt body) = some o) :
    ∃ np nr, blockArity mi bt = some (np, nr) ∧ np ≤ h ∧
      endsAt (chkE ext F mi nl ret (np :: labels) (some np) body) nr = true ∧
      o = some (h - np + nr) := by
  simp only[chk1E] at hc
  split at hc
  · rename_i np nr ha
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1, hcond.2, (Option.some.inj hc).symm⟩
    · cases hc
  · cases hc

theorem chk1_ifE {h : Nat} {bt : BlockType} {c t e : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk1E ext F mi nl ret labels h (.if_ bt c t e) = some o) :
    ∃ oc, chkE ext F mi nl ret labels (some h) c = some oc ∧ ∀ h₁, oc = some h₁ →
      ∃ np nr, blockArity mi bt = some (np, nr) ∧ np + 1 ≤ h₁ ∧
        endsAt (chkE ext F mi nl ret (nr :: labels) (some np) t) nr = true ∧
        endsAt (chkE ext F mi nl ret (nr :: labels) (some np) e) nr = true ∧
        o = some (h₁ - 1 - np + nr) := by
  simp only[chk1E, Option.bind_eq_some_iff] at hc
  obtain ⟨oc, hco, hb⟩ := hc
  refine ⟨oc, hco, ?_⟩
  rintro h₁ rfl
  simp only at hb
  split at hb
  · rename_i np nr ha
    split at hb
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1.1, hcond.1.2, hcond.2, (Option.some.inj hb).symm⟩
    · cases hb
  · cases hb

theorem endsAt_eqE {x : Option (Option Nat)} {n : Nat} (h : endsAt x n = true) :
    ∃ o, x = some o ∧ (o = none ∨ o = some n) := by
  rcases x with _ | _ | k
  · cases h
  · exact ⟨none, rfl, .inl rfl⟩
  · simp only [endsAt, beq_iff_eq] at h
    exact ⟨some k, rfl, .inr (by rw [h])⟩

end UnfoldE

section Unfold

variable {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat} {labels : List Nat}

@[simp] theorem chk_none (es : List Binaryen.BExpr) : chk F mi nl ret labels none es = some none := by
  cases es <;> rfl

@[simp] theorem chk_nil (h : Nat) : chk F mi nl ret labels (some h) [] = some (some h) := rfl

theorem chk_cons {h : Nat} {e : Binaryen.BExpr} {es : List Binaryen.BExpr} {out : Option Nat} :
    chk F mi nl ret labels (some h) (e :: es) = some out ↔
      ∃ o, chk1 F mi nl ret labels h e = some o ∧ chk F mi nl ret labels o es = some out := by
  simp only[chk, chkE, Option.bind_eq_some_iff]

theorem chk1_op {h : Nat} {i : Instr} {args : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk1 F mi nl ret labels h (.op i args) = some o) :
    ∃ oa, chk F mi nl ret labels (some h) args = some oa ∧
      ∀ h₁, oa = some h₁ → flatChk F mi nl ret labels h₁ i = some o := by
  simp only[chk1, chk1E, Option.bind_eq_some_iff] at hc
  obtain ⟨oa, ha, hb⟩ := hc
  refine ⟨oa, ha, ?_⟩
  rintro h₁ rfl
  exact hb

theorem chk1_block {h : Nat} {bt : BlockType} {body : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk1 F mi nl ret labels h (.block bt body) = some o) :
    ∃ np nr, blockArity mi bt = some (np, nr) ∧ np ≤ h ∧
      endsAt (chk F mi nl ret (nr :: labels) (some np) body) nr = true ∧
      o = some (h - np + nr) := by
  simp only[chk1, chk1E] at hc
  split at hc
  · rename_i np nr ha
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1, hcond.2, (Option.some.inj hc).symm⟩
    · cases hc
  · cases hc

theorem chk1_loop {h : Nat} {bt : BlockType} {body : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk1 F mi nl ret labels h (.loop bt body) = some o) :
    ∃ np nr, blockArity mi bt = some (np, nr) ∧ np ≤ h ∧
      endsAt (chk F mi nl ret (np :: labels) (some np) body) nr = true ∧
      o = some (h - np + nr) := by
  simp only[chk1, chk1E] at hc
  split at hc
  · rename_i np nr ha
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1, hcond.2, (Option.some.inj hc).symm⟩
    · cases hc
  · cases hc

theorem chk1_if {h : Nat} {bt : BlockType} {c t e : List Binaryen.BExpr} {o : Option Nat}
    (hc : chk1 F mi nl ret labels h (.if_ bt c t e) = some o) :
    ∃ oc, chk F mi nl ret labels (some h) c = some oc ∧ ∀ h₁, oc = some h₁ →
      ∃ np nr, blockArity mi bt = some (np, nr) ∧ np + 1 ≤ h₁ ∧
        endsAt (chk F mi nl ret (nr :: labels) (some np) t) nr = true ∧
        endsAt (chk F mi nl ret (nr :: labels) (some np) e) nr = true ∧
        o = some (h₁ - 1 - np + nr) := by
  simp only[chk1, chk1E, Option.bind_eq_some_iff] at hc
  obtain ⟨oc, hco, hb⟩ := hc
  refine ⟨oc, hco, ?_⟩
  rintro h₁ rfl
  simp only at hb
  split at hb
  · rename_i np nr ha
    split at hb
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨np, nr, ha, hcond.1.1, hcond.1.2, hcond.2, (Option.some.inj hb).symm⟩
    · cases hb
  · cases hb

theorem endsAt_eq {x : Option (Option Nat)} {n : Nat} (h : endsAt x n = true) :
    ∃ o, x = some o ∧ (o = none ∨ o = some n) := by
  rcases x with _ | _ | k
  · cases h
  · exact ⟨none, rfl, .inl rfl⟩
  · simp only [endsAt, beq_iff_eq] at h
    exact ⟨some k, rfl, .inr (by rw [h])⟩

end Unfold

/-- The native block arity is that of the frame's module. -/
theorem arity_eq (f : Frame) (bt : BlockType) : Binaryen.arity f bt = blockArity f.module bt := by
  cases bt <;> rfl

/-- A normal result of a body whose check ends at `n` has `n` values. -/
theorem length_of_ends {labels : List Nat} {ret n : Nat} {o : Option Nat} {vs : List Val}
    (hok : FlowOk labels ret o (.normal vs)) (he : o = none ∨ o = some n) : vs.length = n := by
  have hv : o = some vs.length := hok
  rcases he with rfl | rfl
  · cases hv
  · exact (Option.some.inj hv).symm

/-- The values a block body hands on are at least the block's arity. -/
theorem blockVals_length {labels : List Nat} {ret n : Nat} {o : Option Nat} {fl : Binaryen.Flow}
    {vs : List Val} (hok : FlowOk (n :: labels) ret o fl) (he : o = none ∨ o = some n)
    (hvs : fl.blockVals = some vs) : n ≤ vs.length := by
  rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | a <;> simp only [Binaryen.Flow.blockVals,
    reduceCtorEq, Option.some.injEq] at hvs
  · subst hvs
    exact (length_of_ends hok he).ge
  · subst hvs
    obtain ⟨m, hm, hle⟩ := hok
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    exact hm ▸ hle

/-- A branch to an outer label loses one label. -/
theorem FlowOk.brk_succ {labels : List Nat} {ret n k : Nat} {o o' : Option Nat} {vs : List Val}
    (h : FlowOk (n :: labels) ret o (.brk (k + 1) vs)) : FlowOk labels ret o' (.brk k vs) := h

/-- An escaping flow passes through a label. -/
theorem FlowOk.escape {labels : List Nat} {ret n : Nat} {o o' : Option Nat} {fl : Binaryen.Flow}
    (h : FlowOk (n :: labels) ret o fl) (he : fl.Escapes) : FlowOk labels ret o' fl := by
  cases fl <;> first | exact absurd he id | exact h

/-! ## The extension parameter is conservative -/

/-- The five call forms an extension may describe. -/
def Instr.IsExtCall : Instr → Prop
  | .callIndirect .. | .callRef _ | .returnCall _ | .returnCallRef _ | .returnCallIndirect .. => True
  | _ => False

/-- **Off the extension's call forms, every extension is the native check.** -/
theorem flatChkE_eq_flatChk (ext : ExtArity H) {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {h : Nat} {i : Instr} (hi : ¬ Instr.IsExtCall i) :
    flatChkE ext F mi nl ret labels h i = flatChk F mi nl ret labels h i := by
  cases i <;> first | rfl | exact absurd trivial hi

/-- The native check rejects the extension's call forms. -/
theorem flatChk_extCall {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {i : Instr} (hi : Instr.IsExtCall i) :
    flatChk F mi nl ret labels h i = none := by
  cases i <;> first | rfl | exact absurd hi id

/-! ## Flat instructions -/

section Flat

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {labels : List Nat}
  {s s' : Store H} {f f' : Frame} {stk stk' : List Val}

/-! ### `select` and `br_table` -/

/-- The native `select`. -/
theorem evalFlat_select {t : Option (List ValType)} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.select t) = some (s', f', fl)) :
    ∃ c b a r bv, stk = c :: b :: a :: r ∧ Binaryen.truthy c = some bv ∧ s' = s ∧ f' = f ∧
      fl = .normal ((if bv then a else b) :: r) := by
  rcases stk with _ | ⟨c, _ | ⟨b, _ | ⟨a, r⟩⟩⟩
  all_goals simp only [Binaryen.evalFlat, reduceCtorEq] at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨bv, hbv, rfl, rfl, rfl⟩ := h
  exact ⟨c, b, a, r, bv, rfl, hbv, rfl, rfl, rfl⟩

/-- The native `br_table`. -/
theorem evalFlat_brTable {ls : List LabelIdx} {d : LabelIdx} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.brTable ls d) = some (s', f', fl)) :
    ∃ (c : Val) (r : List Val) (i : BitVec 32), stk = c :: r ∧ Binaryen.asInt .i32 c = some i ∧ s' = s ∧ f' = f ∧
      fl = .brk ((ls[i.toNat]?).getD d).toNat r := by
  rcases stk with _ | ⟨c, r⟩
  all_goals simp only [Binaryen.evalFlat, reduceCtorEq] at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨i, hi, rfl, rfl, rfl⟩ := h
  exact ⟨c, r, i, rfl, hi, rfl, rfl, rfl⟩

/-- The check of `select`. -/
theorem flatChk_select {h : Nat} {t : Option (List ValType)} {o : Option Nat}
    (hc : flatChk F mi nl ret labels h (.select t) = some o) : 3 ≤ h ∧ o = some (h - 3 + 1) := by
  simp only[flatChk, flatChkE, flatEff] at hc
  split at hc
  · exact ⟨‹_›, (Option.some.inj hc).symm⟩
  · cases hc

/-- The check of `br_table`. -/
theorem flatChk_brTable {h : Nat} {ls : List LabelIdx} {d : LabelIdx} {o : Option Nat}
    (hc : flatChk F mi nl ret labels h (.brTable ls d) = some o) :
    1 ≤ h ∧ tableOk labels (h - 1) (d :: ls) = true ∧ o = none := by
  simp only[flatChk, flatChkE] at hc
  split at hc
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    exact ⟨hcond.1, hcond.2, (Option.some.inj hc).symm⟩
  · cases hc

/-- A target of a checked table exists and finds its arity. -/
theorem tableOk_mem {h : Nat} {ls : List LabelIdx} {l : LabelIdx} (ht : tableOk labels h ls = true)
    (hl : l ∈ ls) : ∃ n, labels[l.toNat]? = some n ∧ n ≤ h := by
  have hl' := List.all_eq_true.mp ht l hl
  revert hl'
  split
  · rename_i n hn
    exact fun hle => ⟨n, hn, of_decide_eq_true hle⟩
  · exact fun hf => absurd hf Bool.false_ne_true

/-- The label a `br_table` takes is in its table. -/
theorem brTable_target_mem (ls : List LabelIdx) (d : LabelIdx) (k : Nat) :
    (ls[k]?).getD d ∈ d :: ls := by
  rcases hk : ls[k]? with _ | l
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_of_getElem? hk)

/-- A checked `br_table` branches to a label it finds the arity of. -/
theorem flowOk_brTable {ls : List LabelIdx} {d : LabelIdx} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.brTable ls d) = some (s', f', fl))
    {o : Option Nat} (hc : flatChk F mi nl ret labels stk.length (.brTable ls d) = some o)
    (o' : Option Nat) : FlowOk labels ret o' fl ∧ EvalInvE ext s f (s', f', fl) := by
  obtain ⟨c, r, i, rfl, -, rfl, rfl, rfl⟩ := evalFlat_brTable h
  obtain ⟨-, ht, -⟩ := flatChk_brTable hc
  have hlen : (c :: r).length - 1 = r.length := by simp
  rw [hlen] at ht
  exact ⟨tableOk_mem ht (brTable_target_mem ls d i.toNat), EvalInvE.refl _ _ _⟩

/-- A checked `select` completes at the checked height. -/
theorem flat_normal_select {t : Option (List ValType)}
    (h : Binaryen.evalFlat s f stk (.select t) = some (s', f', .normal stk'))
    {o : Option Nat} (hc : flatChk F mi nl ret labels stk.length (.select t) = some o) :
    o = some stk'.length ∧ EvalInvE ext s f (s', f', .normal stk') := by
  obtain ⟨c, b, a, r, bv, rfl, -, rfl, rfl, hfl⟩ := evalFlat_select h
  obtain ⟨-, rfl⟩ := flatChk_select hc
  have hs : stk' = (if bv then a else b) :: r := (Binaryen.Flow.normal.inj hfl)
  subst hs
  exact ⟨by simp, EvalInvE.refl _ _ _⟩

/-- A memory load: results and invariants. -/
theorem flat_load {t : IntType} {x : MemIdx} {arg : MemArg} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.intLoad t none x arg) = some (s', f', fl)) :
    s' = s ∧ f' = f ∧ ∃ v r, stk = v :: r ∧ (fl = .trap ∨ ∃ w, fl = .normal (w :: r)) := by
  rcases stk with _ | ⟨v, r⟩
  · simp [Binaryen.evalFlat] at h
  simp only [Binaryen.evalFlat] at h
  rcases ha : Binaryen.addrNat? v with _ | i
  · simp [ha] at h
  rcases hm : s.mem? f x with _ | ⟨ma, mi'⟩
  · simp [ha, hm] at h
  rcases hl : Execution.Memory.load mi'.bytes (effAddr i arg) (t.width / 8) with _ | c
  · simp only [ha, hm, hl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, v, r, rfl, .inl rfl⟩
  · simp only [ha, hm, hl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, v, r, rfl, .inr ⟨_, rfl⟩⟩

/-- A memory store: results and invariants. -/
theorem flat_store {t : IntType} {x : MemIdx} {arg : MemArg} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.intStore t none x arg) = some (s', f', fl)) :
    s'.funcs = s.funcs ∧ f' = f ∧ ∃ w v r, stk = w :: v :: r ∧ (fl = .trap ∨ fl = .normal r) := by
  rcases stk with _ | ⟨w, _ | ⟨v, r⟩⟩
  · simp [Binaryen.evalFlat] at h
  · simp [Binaryen.evalFlat] at h
  simp only [Binaryen.evalFlat] at h
  rcases ha : Binaryen.addrNat? v with _ | i
  · simp [ha] at h
  rcases hw : Binaryen.asInt t w with _ | c
  · simp [ha, hw] at h
  rcases hm : s.mem? f x with _ | ⟨ma, mi'⟩
  · simp [ha, hw, hm] at h
  rcases hs : Execution.Memory.store mi'.bytes (effAddr i arg) (count := t.width / 8)
      (c.setWidth _) with _ | b
  · simp only [ha, hw, hm, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, w, v, r, rfl, .inl rfl⟩
  · simp only [ha, hw, hm, hs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, w, v, r, rfl, .inr rfl⟩

/-- `flat_normal` for instructions other than `select` and `br_table`. -/
theorem flat_normal_plain {i : Instr} (hsel : ¬ ∃ t, i = .select t)
    (hld : ¬ ∃ t x arg, i = .intLoad t none x arg) (hst : ¬ ∃ t x arg, i = .intStore t none x arg)
    (hbt : ¬ ∃ ls d, i = .brTable ls d)
    (h : Binaryen.evalFlat s f stk i = some (s', f', .normal stk'))
    {o : Option Nat} (hc : flatChk F mi nl ret labels stk.length i = some o) :
    o = some stk'.length ∧ EvalInvE ext s f (s', f', .normal stk') := by
  cases i
  all_goals try first | exact absurd ⟨_, rfl⟩ hsel | exact absurd ⟨_, _, rfl⟩ hbt
  case intLoad t p x arg =>
    rcases p with _ | p
    · exact absurd ⟨_, _, _, rfl⟩ hld
    · simp[flatChk, flatChkE, flatEff] at hc
  case intStore t p x arg =>
    rcases p with _ | p
    · exact absurd ⟨_, _, _, rfl⟩ hst
    · simp[flatChk, flatChkE, flatEff] at hc
  all_goals simp only[Binaryen.evalFlat, flatChk, flatChkE, extStep, noExt, flatEff] at h hc
  all_goals (repeat' split at h) <;> (repeat' split at hc)
  all_goals simp_all [EvalInvE, Option.map_eq_some_iff, Option.bind_eq_some_iff, Frame.setLocal,
    Store.setGlobal]
  all_goals (try obtain ⟨_, _, _, _, rfl, rfl, rfl⟩ := h)
  all_goals (try (obtain ⟨_, _, _, _, h⟩ := h; split at h <;>
    simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, Binaryen.Flow.normal.injEq,
      and_false] at h; obtain ⟨rfl, rfl, rfl⟩ := h))
  all_goals (subst_vars)
  all_goals simp_all
  omega

/-- A checked flat instruction completing normally ends at the checked height and keeps the
invariants. -/
theorem flat_normal {i : Instr} (h : Binaryen.evalFlat s f stk i = some (s', f', .normal stk'))
    {o : Option Nat} (hc : flatChk F mi nl ret labels stk.length i = some o) :
    o = some stk'.length ∧ EvalInvE ext s f (s', f', .normal stk') := by
  by_cases hsel : ∃ t, i = .select t
  · obtain ⟨t, rfl⟩ := hsel
    exact flat_normal_select h hc
  by_cases hbt : ∃ ls d, i = .brTable ls d
  · obtain ⟨ls, d, rfl⟩ := hbt
    obtain ⟨_, _, _, -, -, -, -, hfl⟩ := evalFlat_brTable h
    cases hfl
  by_cases hld : ∃ t x arg, i = .intLoad t none x arg
  · obtain ⟨t, x, arg, rfl⟩ := hld
    obtain ⟨rfl, rfl, v, r, rfl, hfl | ⟨w, hfl⟩⟩ := flat_load h
    · cases hfl
    · cases hfl
      simp only[flatChk, flatChkE, flatEff, List.length_cons] at hc
      refine ⟨?_, EvalInvE.refl _ _ _⟩
      split at hc <;> simp_all
  by_cases hst : ∃ t x arg, i = .intStore t none x arg
  · obtain ⟨t, x, arg, rfl⟩ := hst
    obtain ⟨hfs, rfl, w, v, r, rfl, hfl | hfl⟩ := flat_store h
    · cases hfl
    · cases hfl
      simp only[flatChk, flatChkE, flatEff, List.length_cons] at hc
      refine ⟨?_, FuncsGoodE.of_eq hfs, rfl, rfl⟩
      split at hc <;> simp_all
  exact flat_normal_plain hsel hld hst hbt h hc

/-- `flat_abrupt` for instructions other than `select` and `br_table`. -/
theorem flat_abrupt_plain {i : Instr} {fl : Binaryen.Flow} (hsel : ¬ ∃ t, i = .select t)
    (hld : ¬ ∃ t x arg, i = .intLoad t none x arg) (hst : ¬ ∃ t x arg, i = .intStore t none x arg)
    (hbt : ¬ ∃ ls d, i = .brTable ls d)
    (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) (hn : ¬ fl.IsNormal)
    {o : Option Nat} (hc : flatChk F mi nl ret labels stk.length i = some o) (o' : Option Nat) :
    FlowOk labels ret o' fl ∧ EvalInvE ext s f (s', f', fl) := by
  cases i
  all_goals try first | exact absurd ⟨_, rfl⟩ hsel | exact absurd ⟨_, _, rfl⟩ hbt
  case intLoad t p x arg =>
    rcases p with _ | p
    · exact absurd ⟨_, _, _, rfl⟩ hld
    · simp[flatChk, flatChkE, flatEff] at hc
  case intStore t p x arg =>
    rcases p with _ | p
    · exact absurd ⟨_, _, _, rfl⟩ hst
    · simp[flatChk, flatChkE, flatEff] at hc
  all_goals simp only[Binaryen.evalFlat, flatChk, flatChkE, extStep, noExt, flatEff] at h hc
  all_goals (repeat' split at h) <;> (repeat' split at hc)
  all_goals simp_all [EvalInvE, FlowOk, Option.map_eq_some_iff, Option.bind_eq_some_iff,
    Frame.setLocal, Store.setGlobal, Binaryen.Flow.IsNormal]
  all_goals (try obtain ⟨_, _, _, _, rfl, rfl, rfl⟩ := h)
  all_goals (try (obtain ⟨_, _, _, _, h⟩ := h; split at h <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h))
  all_goals (subst_vars)
  all_goals simp_all
  obtain ⟨_, rfl, rfl, rfl⟩ := ‹Binaryen.truthy _ = some true ∧ _›
  exact ⟨_, ‹_›, ‹_›⟩

/-- A checked flat instruction stopping abruptly satisfies the check and keeps the invariants. -/
theorem flat_abrupt {i : Instr} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) (hn : ¬ fl.IsNormal)
    {o : Option Nat} (hc : flatChk F mi nl ret labels stk.length i = some o) (o' : Option Nat) :
    FlowOk labels ret o' fl ∧ EvalInvE ext s f (s', f', fl) := by
  by_cases hsel : ∃ t, i = .select t
  · obtain ⟨t, rfl⟩ := hsel
    obtain ⟨_, _, _, _, _, -, -, -, -, rfl⟩ := evalFlat_select h
    exact absurd trivial hn
  by_cases hbt : ∃ ls d, i = .brTable ls d
  · obtain ⟨ls, d, rfl⟩ := hbt
    exact flowOk_brTable h hc o'
  by_cases hld : ∃ t x arg, i = .intLoad t none x arg
  · obtain ⟨t, x, arg, rfl⟩ := hld
    obtain ⟨rfl, rfl, v, r, rfl, rfl | ⟨w, rfl⟩⟩ := flat_load h
    · exact ⟨trivial, EvalInvE.refl _ _ _⟩
    · exact absurd trivial hn
  by_cases hst : ∃ t x arg, i = .intStore t none x arg
  · obtain ⟨t, x, arg, rfl⟩ := hst
    obtain ⟨hfs, rfl, w, v, r, rfl, rfl | rfl⟩ := flat_store h
    · exact ⟨trivial, FuncsGoodE.of_eq hfs, rfl, rfl⟩
    · exact absurd trivial hn
  exact flat_abrupt_plain hsel hld hst hbt h hn hc o'

/-- The check of a direct call. -/
theorem flatChk_call {h : Nat} {x : FuncIdx} {o : Option Nat}
    (hc : flatChk F mi nl ret labels h (.call x) = some o) :
    ∃ p q, callArity F mi x = some (p, q) ∧ p ≤ h ∧ o = some (h - p + q) := by
  simp only[flatChk, flatChkE, flatEff] at hc
  split at hc
  · rename_i p q hpq
    split at hc
    · exact ⟨p, q, hpq, ‹_›, (Option.some.inj hc).symm⟩
    · cases hc
  · cases hc

end Flat

/-- The arity of a called function is that of its type. -/
theorem callArity_eq {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    {ps rs : List Validation.CValType} (hfi : s.func? f x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    callArity s.funcs f.module x = some (ps.length, rs.length) := by
  simp only [Store.func?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hfi
  obtain ⟨a', ha, fi', hfi', h⟩ := hfi
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp [callArity, ha, hfi', hty]

/-- The called function, as an element of the store. -/
theorem funcs_of_func? {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hfi : s.func? f x = some (a, fi)) : s.funcs[a]? = some fi := by
  simp only [Store.func?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hfi
  obtain ⟨a', -, fi', hfi', h⟩ := hfi
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact hfi'

section Transfer

variable {H' : Type}

variable {F₁ : List (FuncInst H)} {F₂ : List (FuncInst H')} {mi₁ mi₂ : ModuleInst} {nl ret : Nat}

/-- Every arity known to the first store and instance is known to the second. -/
structure Arities (F₁ : List (FuncInst H)) (mi₁ : ModuleInst) (F₂ : List (FuncInst H'))
    (mi₂ : ModuleInst) : Prop where
  call : ∀ x p, callArity F₁ mi₁ x = some p → callArity F₂ mi₂ x = some p
  block : ∀ bt p, blockArity mi₁ bt = some p → blockArity mi₂ bt = some p

theorem flatChk_transfer (hA : Arities F₁ mi₁ F₂ mi₂) {labels : List Nat} {h : Nat} {i : Instr}
    {o : Option Nat} (hc : flatChk F₁ mi₁ nl ret labels h i = some o) :
    flatChk F₂ mi₂ nl ret labels h i = some o := by
  cases i
  case call x =>
    simp only[flatChk, flatChkE, flatEff] at hc ⊢
    split at hc
    · rename_i p q hpq
      rw [hA.call x (p, q) hpq]
      exact hc
    · cases hc
  case intLoad t p x arg => rcases p with _ | p <;> exact hc
  case intStore t p x arg => rcases p with _ | p <;> exact hc
  all_goals exact hc

theorem endsAt_transfer {x y : Option (Option Nat)} {n : Nat}
    (hxy : ∀ o, x = some o → y = some o) (h : endsAt x n = true) : endsAt y n = true := by
  obtain ⟨o, hx, -⟩ := endsAt_eq h
  rw [hxy o hx, ← hx]
  exact h

mutual
/-- **A passing check transfers** to a store and instance with the same arities. -/
theorem chk_transfer (hA : Arities F₁ mi₁ F₂ mi₂) {labels : List Nat} :
    ∀ (oh : Option Nat) (es : List Binaryen.BExpr) {o : Option Nat},
      chk F₁ mi₁ nl ret labels oh es = some o → chk F₂ mi₂ nl ret labels oh es = some o
  | none, es, o, hc => by
    rw [chk_none] at hc ⊢
    exact hc
  | some h, [], o, hc => hc
  | some h, e :: es, o, hc => by
    obtain ⟨o₁, h1, h2⟩ := chk_cons.mp hc
    exact chk_cons.mpr ⟨o₁, chk1_transfer hA h e h1, chk_transfer hA o₁ es h2⟩

/-- `chk_transfer` for one tree. -/
theorem chk1_transfer (hA : Arities F₁ mi₁ F₂ mi₂) {labels : List Nat} :
    ∀ (h : Nat) (e : Binaryen.BExpr) {o : Option Nat},
      chk1 F₁ mi₁ nl ret labels h e = some o → chk1 F₂ mi₂ nl ret labels h e = some o
  | h, .op i args, o, hc => by
    simp only[chk1, chk1E, Option.bind_eq_some_iff] at hc ⊢
    obtain ⟨oa, ha, hk⟩ := hc
    refine ⟨oa, chk_transfer hA (some h) args ha, ?_⟩
    rcases oa with _ | h₁
    · exact hk
    · exact flatChk_transfer hA hk
  | h, .block bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_block hc
    simp only[chk1, chk1E, hA.block bt _ hbt, hle, decide_true, Bool.true_and, endsAt_transfer (fun _ => chk_transfer hA (some np) body) hends, ite_true]
  | h, .loop bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_loop hc
    simp only[chk1, chk1E, hA.block bt _ hbt, hle, decide_true, Bool.true_and, endsAt_transfer (fun _ => chk_transfer hA (some np) body) hends, ite_true]
  | h, .if_ bt c t el, o, hc => by
    obtain ⟨oc, hco, hk⟩ := chk1_if hc
    simp only[chk1, chk1E, Option.bind_eq_some_iff]
    refine ⟨oc, chk_transfer hA (some h) c hco, ?_⟩
    rcases oc with _ | h₁
    · simp only[chk1, chk1E, Option.bind_eq_some_iff, hco] at hc
      obtain ⟨_, hx, hy⟩ := hc
      cases hx
      exact hy
    · obtain ⟨np, nr, hbt, hle, ht, he, rfl⟩ := hk h₁ rfl
      simp only [hA.block bt _ hbt, hle, decide_true,
        endsAt_transfer (fun _ => chk_transfer hA (some np) t) ht,
        endsAt_transfer (fun _ => chk_transfer hA (some np) el) he, Bool.and_self, ite_true]
  | h, .tryTable .., o, hc => by simp[chk1, chk1E] at hc
end

end Transfer

/-! ## Extensions stable under function extension -/

/-- An extension whose answers survive a function-list extension. -/
class ExtStable (ext : ExtArity H) : Prop where
  stable : ∀ {F F' : List (FuncInst H)} {mi : ModuleInst} {i : Instr} {e : ExtEff},
    FuncsExt F F' → ext F mi i = some e → ext F' mi i = some e

instance : ExtStable (noExt (H := H)) := ⟨fun _ h => by simp [noExt] at h⟩

section TransferE

variable {ext : ExtArity H} [hext : ExtStable ext] {F F' : List (FuncInst H)} {mi : ModuleInst}
  {nl ret : Nat}

theorem callArity_ext (h : FuncsExt F F') {x : FuncIdx} {p : Nat × Nat}
    (hp : callArity F mi x = some p) : callArity F' mi x = some p := by
  unfold callArity at hp ⊢
  rcases ha : mi.funcs[x.toNat]? with _ | a
  · simp [ha] at hp
  · rcases hf : F[a]? with _ | fi
    · simp [ha, hf] at hp
    · simp only [ha, hf, Option.bind_eq_bind, Option.bind_some] at hp
      simp only [Option.bind_eq_bind, Option.bind_some, get_of_funcsExt h hf]
      exact hp

theorem extStep_ext (h : FuncsExt F F') {i : Instr} {o : Option Nat} {k : Nat}
    (hc : extStep (ext F mi i) ret k = some o) : extStep (ext F' mi i) ret k = some o := by
  rcases he : ext F mi i with _ | e
  · rw [he] at hc
    simp [extStep] at hc
  · rw [he] at hc
    rw [hext.stable h he]
    exact hc

theorem flatChkE_ext (h : FuncsExt F F') {labels : List Nat} {k : Nat} {i : Instr}
    {o : Option Nat} (hc : flatChkE ext F mi nl ret labels k i = some o) :
    flatChkE ext F' mi nl ret labels k i = some o := by
  cases i
  case call x =>
    simp only [flatChkE, flatEff] at hc ⊢
    split at hc
    · rename_i p q hpq
      rw [callArity_ext h hpq]
      exact hc
    · cases hc
  case callIndirect x y => exact extStep_ext h hc
  case callRef y => exact extStep_ext h hc
  case returnCall x => exact extStep_ext h hc
  case returnCallRef y => exact extStep_ext h hc
  case returnCallIndirect x y => exact extStep_ext h hc
  case intLoad t p x arg => rcases p with _ | p <;> exact hc
  case intStore t p x arg => rcases p with _ | p <;> exact hc
  all_goals exact hc

set_option linter.unusedSectionVars false in
mutual
/-- **A passing extended check still passes after a function extension.** -/
theorem chkE_ext (h : FuncsExt F F') {labels : List Nat} :
    ∀ (oh : Option Nat) (es : List Binaryen.BExpr) {o : Option Nat},
      chkE ext F mi nl ret labels oh es = some o → chkE ext F' mi nl ret labels oh es = some o
  | none, es, o, hc => by
    rw [chk_noneE] at hc ⊢
    exact hc
  | some k, [], o, hc => hc
  | some k, e :: es, o, hc => by
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    exact chk_consE.mpr ⟨o₁, chk1E_ext h k e h1, chkE_ext h o₁ es h2⟩

theorem chk1E_ext (h : FuncsExt F F') {labels : List Nat} :
    ∀ (k : Nat) (e : Binaryen.BExpr) {o : Option Nat},
      chk1E ext F mi nl ret labels k e = some o → chk1E ext F' mi nl ret labels k e = some o
  | k, .op i args, o, hc => by
    simp only [chk1E, Option.bind_eq_some_iff] at hc ⊢
    obtain ⟨oa, ha, hk⟩ := hc
    refine ⟨oa, chkE_ext h (some k) args ha, ?_⟩
    rcases oa with _ | h₁
    · exact hk
    · exact flatChkE_ext h hk
  | k, .block bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_blockE hc
    simp only [chk1E, hbt, hle, decide_true, Bool.true_and,
      endsAt_transfer (fun _ => chkE_ext h (some np) body) hends, ite_true]
  | k, .loop bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_loopE hc
    simp only [chk1E, hbt, hle, decide_true, Bool.true_and,
      endsAt_transfer (fun _ => chkE_ext h (some np) body) hends, ite_true]
  | k, .if_ bt c t el, o, hc => by
    obtain ⟨oc, hco, hk⟩ := chk1_ifE hc
    simp only [chk1E, Option.bind_eq_some_iff]
    refine ⟨oc, chkE_ext h (some k) c hco, ?_⟩
    rcases oc with _ | h₁
    · simp only [chk1E, Option.bind_eq_some_iff, hco] at hc
      obtain ⟨_, hx, hy⟩ := hc
      cases hx
      exact hy
    · obtain ⟨np, nr, hbt, hle, ht, he, rfl⟩ := hk h₁ rfl
      simp only [hbt, hle, decide_true,
        endsAt_transfer (fun _ => chkE_ext h (some np) t) ht,
        endsAt_transfer (fun _ => chkE_ext h (some np) el) he, Bool.and_self, ite_true]
  | k, .tryTable .., o, hc => by simp [chk1E] at hc
end

end TransferE

section Conserv

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}

theorem flatChkE_of_flatChk {labels : List Nat} {k : Nat} {i : Instr} {o : Option Nat}
    (hc : flatChk F mi nl ret labels k i = some o) : flatChkE ext F mi nl ret labels k i = some o := by
  by_cases hi : Instr.IsExtCall i
  · rw [flatChk_extCall hi] at hc
    cases hc
  · rwa [flatChkE_eq_flatChk ext hi]

set_option linter.unusedSectionVars false in
mutual
/-- **The native check implies every extended check** (conservativity). -/
theorem chkE_of_chk {labels : List Nat} :
    ∀ (oh : Option Nat) (es : List Binaryen.BExpr) {o : Option Nat},
      chk F mi nl ret labels oh es = some o → chkE ext F mi nl ret labels oh es = some o
  | none, es, o, hc => by
    rw [chk_none] at hc
    rw [chk_noneE]
    exact hc
  | some k, [], o, hc => hc
  | some k, e :: es, o, hc => by
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    exact chk_consE.mpr ⟨o₁, chk1E_of_chk1 k e h1, chkE_of_chk o₁ es h2⟩

theorem chk1E_of_chk1 {labels : List Nat} :
    ∀ (k : Nat) (e : Binaryen.BExpr) {o : Option Nat},
      chk1 F mi nl ret labels k e = some o → chk1E ext F mi nl ret labels k e = some o
  | k, .op i args, o, hc => by
    simp only [chk1E, Option.bind_eq_some_iff] at hc ⊢
    obtain ⟨oa, ha, hk⟩ := hc
    refine ⟨oa, chkE_of_chk (some k) args ha, ?_⟩
    rcases oa with _ | h₁
    · exact hk
    · exact flatChkE_of_flatChk hk
  | k, .block bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_blockE hc
    simp only [chk1E, hbt, hle, decide_true, Bool.true_and,
      endsAt_transfer (fun _ => chkE_of_chk (some np) body) hends, ite_true]
  | k, .loop bt body, o, hc => by
    obtain ⟨np, nr, hbt, hle, hends, rfl⟩ := chk1_loopE hc
    simp only [chk1E, hbt, hle, decide_true, Bool.true_and,
      endsAt_transfer (fun _ => chkE_of_chk (some np) body) hends, ite_true]
  | k, .if_ bt c t el, o, hc => by
    obtain ⟨oc, hco, hk⟩ := chk1_ifE hc
    simp only [chk1E, Option.bind_eq_some_iff]
    refine ⟨oc, chkE_of_chk (some k) c hco, ?_⟩
    rcases oc with _ | h₁
    · simp only [chk1E, Option.bind_eq_some_iff, hco] at hc
      obtain ⟨_, hx, hy⟩ := hc
      cases hx
      exact hy
    · obtain ⟨np, nr, hbt, hle, ht, he, rfl⟩ := hk h₁ rfl
      simp only [hbt, hle, decide_true,
        endsAt_transfer (fun _ => chkE_of_chk (some np) t) ht,
        endsAt_transfer (fun _ => chkE_of_chk (some np) el) he, Bool.and_self, ite_true]
  | k, .tryTable .., o, hc => by simp [chk1E] at hc
end

/-- **A natively checked store passes every extended check** (`chkE_of_chk`). -/
theorem storeChkE_of_storeChk {F : List (FuncInst H)} (hS : StoreChk F) : StoreChkE ext F :=
  fun a fi fn ps rs ha hc ht =>
    endsAt_transfer (fun _ ho => chkE_of_chk _ _ ho) (hS a fi fn ps rs ha hc ht)

end Conserv

theorem arities_of_funcsExt {F F' : List (FuncInst H)} (h : FuncsExt F F') (mi : ModuleInst) :
    Arities F mi F' mi where
  call x p hp := by
    unfold callArity at hp ⊢
    rcases ha : mi.funcs[x.toNat]? with _ | a
    · simp [ha] at hp
    · rcases hf : F[a]? with _ | fi
      · simp [ha, hf] at hp
      · simp only [ha, hf, Option.bind_eq_bind, Option.bind_some] at hp
        simp only [Option.bind_eq_bind, Option.bind_some, get_of_funcsExt h hf]
        exact hp
  block _ _ hp := hp

/-! ## Soundness of the check -/

/-- The statement of `flowOk_of_eval` for one evaluation. -/
def ArityGoodE (ext : ExtArity H) (s : Store H) (f : Frame) (stk : List Val)
    (es : List Binaryen.BExpr) (r : Store H × Frame × Binaryen.Flow) : Prop :=
  ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChkE ext s.funcs →
    chkE ext s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    FlowOk labels ret out r.2.2 ∧ EvalInvE ext s f r

/-- What the native arity check says about a native run. -/
abbrev ArityGood (s : Store H) (f : Frame) (stk : List Val) (es : List Binaryen.BExpr)
    (r : Store H × Frame × Binaryen.Flow) : Prop :=
  ArityGoodE noExt s f stk es r

section Cases

theorem storeChk_inv {ext : ExtArity H} {s s₁ : Store H} {f f₁ : Frame} {fl : Binaryen.Flow}
    (h : EvalInvE ext s f (s₁, f₁, fl)) (hS : StoreChkE ext s.funcs) : StoreChkE ext s₁.funcs :=
  h.1.2.1 hS

theorem nativeFuncsOk_inv {ext : ExtArity H} {s s₁ : Store H} {f f₁ : Frame} {fl : Binaryen.Flow}
    (h : EvalInvE ext s f (s₁, f₁, fl)) (hF : Binaryen.NativeFuncsOk s.funcs) :
    Binaryen.NativeFuncsOk s₁.funcs := h.1.2.2 hF

set_option linter.unusedSectionVars false

variable {ext : ExtArity H} [ExtStable ext]

variable {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl : Binaryen.Flow}
  {r : Store H × Frame × Binaryen.Flow}

theorem not_extCall_of_evalFlat {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr}
    {fl : Binaryen.Flow} (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) :
    ¬ Instr.IsExtCall i := by
  cases i <;> simp_all [Binaryen.evalFlat, Instr.IsExtCall]

theorem flatChk_of_evalFlat {s' : Store H} {f' : Frame} {stk' : List Val} {i : Instr}
    {fl : Binaryen.Flow} {ret : Nat} {labels : List Nat} {k : Nat} {o : Option Nat}
    (h : Binaryen.evalFlat s₁ f₁ stk' i = some (s', f', fl))
    (hc : flatChkE ext s₁.funcs f₁.module f₁.locals.length ret labels k i = some o) :
    flatChk s₁.funcs f₁.module f₁.locals.length ret labels k i = some o := by
  rwa [flatChkE_eq_flatChk ext (not_extCall_of_evalFlat h)] at hc

theorem flatChkE_call {x : FuncIdx} {ret : Nat} {labels : List Nat} {k : Nat} {o : Option Nat}
    (hc : flatChkE ext s₁.funcs f₁.module f₁.locals.length ret labels k (.call x) = some o) :
    flatChk s₁.funcs f₁.module f₁.locals.length ret labels k (.call x) = some o := by
  rwa [flatChkE_eq_flatChk ext (by simp [Instr.IsExtCall])] at hc

/-- A passing check still passes after a run (functions extended, module and
locals kept). -/
theorem chk_inv (h : EvalInvE ext s f (s₁, f₁, fl)) {ret : Nat} {labels : List Nat} {oh : Option Nat}
    {es : List Binaryen.BExpr} {o : Option Nat}
    (hc : chkE ext s.funcs f.module f.locals.length ret labels oh es = some o) :
    chkE ext s₁.funcs f₁.module f₁.locals.length ret labels oh es = some o := by
  rw [h.2.1, h.2.2]
  exact chkE_ext h.1.1 oh es hc

theorem chk_inv_endsAt (h : EvalInvE ext s f (s₁, f₁, fl)) {ret : Nat} {labels : List Nat}
    {oh : Option Nat} {es : List Binaryen.BExpr} {n : Nat}
    (hc : endsAt (chkE ext s.funcs f.module f.locals.length ret labels oh es) n = true) :
    endsAt (chkE ext s₁.funcs f₁.module f₁.locals.length ret labels oh es) n = true :=
  endsAt_transfer (fun _ => chk_inv h) hc

theorem flatChk_inv (h : EvalInvE ext s f (s₁, f₁, fl)) {ret : Nat} {labels : List Nat} {k : Nat}
    {i : Instr} {o : Option Nat}
    (hc : flatChkE ext s.funcs f.module f.locals.length ret labels k i = some o) :
    flatChkE ext s₁.funcs f₁.module f₁.locals.length ret labels k i = some o := by
  rw [h.2.1, h.2.2]
  exact flatChkE_ext h.1.1 hc



theorem arity_nil : ArityGoodE ext s f stk [] (s, f, .normal stk) := by
  intro labels ret out _ hc
  rw [chk_nilE] at hc
  exact ⟨(Option.some.inj hc).symm, EvalInvE.refl _ _ _⟩

theorem arity_argsAbort (iha : ArityGoodE ext s f stk args (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
    ArityGoodE ext s f stk (.op i args :: es) (s₁, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  obtain ⟨hok, hinv⟩ := iha hS ha
  exact ⟨hok.abrupt hfl, hinv⟩

/-- Checked arguments evaluated normally reach the checked height of the operator. -/
theorem arity_args {labels : List Nat} {ret : Nat} {o : Option Nat}
    (hS : StoreChkE ext s.funcs) (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁))
    (hc : chk1E ext s.funcs f.module f.locals.length ret labels stk.length (.op i args) = some o) :
    flatChkE ext s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o ∧
      EvalInvE ext s f (s₁, f₁, .normal stk₁) := by
  obtain ⟨oa, ha, hf⟩ := chk1_opE hc
  obtain ⟨hoa, hinv⟩ := iha hS ha
  have hfc : flatChkE ext s.funcs f.module f.locals.length ret labels stk₁.length i = some o :=
    hf _ hoa
  exact ⟨flatChk_inv hinv hfc, hinv⟩

theorem arity_opOk (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁))
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ihk : ArityGoodE ext s₂ f₂ stk₂ es r) : ArityGoodE ext s f stk (.op i args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  obtain ⟨ho, inv2⟩ := flat_normal hflat (flatChk_of_evalFlat hflat hf)
  have inv12 : EvalInvE ext s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
  have h2' : chkE ext s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
      some out := by
    rw [← ho]
    exact chk_inv inv12 h2
  obtain ⟨hok, inv3⟩ := ihk (storeChk_inv inv12 hS) h2'
  exact ⟨hok, inv12.trans inv3⟩

theorem arity_opStop (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁))
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
    ArityGoodE ext s f stk (.op i args :: es) (s₂, f₂, fl) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  obtain ⟨hok, inv2⟩ := flat_abrupt hflat hfl (flatChk_of_evalFlat hflat hf) out
  exact ⟨hok, inv1.trans inv2⟩

/-! ### Calls -/

/-- The values a callee hands back are at least its result arity. -/
theorem retVals_length {n : Nat} {ob : Option Nat} (hok : FlowOk [n] n ob fl)
    (hob : ob = none ∨ ob = some n) (hvs : fl.retVals = some vs) : n ≤ vs.length := by
  rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | a <;> simp only [Binaryen.Flow.retVals,
    reduceCtorEq, Option.some.injEq] at hvs
  · subst hvs
    exact (length_of_ends hok hob).ge
  · subst hvs
    obtain ⟨m, hm, hle⟩ := hok
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    exact hm ▸ hle
  · subst hvs
    exact hok

/-- The locals of a callee frame. -/
theorem forCall_length (mi : ModuleInst) {args : List Val} (ls : List ValType) {n : Nat}
    (hn : args.length = n) : (Frame.forCall mi args ls).locals.length = n + ls.length := by
  simp [Frame.forCall, hn]

/-- The check of a callee body, in the callee's frame. -/
theorem callee_chk {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hS1 : StoreChkE ext s₁.funcs)
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk₁.length) :
    ∃ ob, (ob = none ∨ ob = some rs.length) ∧
      chkE ext s₁.funcs (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals).module
        (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals).locals.length
        rs.length [rs.length] (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) =
        some ob := by
  have hend := hS1 a fi fn ps rs (funcs_of_func? hfi) hcode hty
  obtain ⟨ob, hb, hob⟩ := endsAt_eq hend
  have hlen : (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals).locals.length =
      ps.length + fn.locals.length :=
    forCall_length _ _ (by simp only [List.length_reverse, List.length_take]; omega)
  refine ⟨ob, hob, ?_⟩
  rw [hlen]
  exact hb

/-- A checked callee body satisfies the check at its own label and result arity. -/
theorem arity_callee {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hS : StoreChkE ext s.funcs)
    (inv1 : EvalInvE ext s f (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : ps.length ≤ stk₁.length)
    (ihb : ArityGoodE ext s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₂, f₂, fl)) :
    ∃ ob, (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob fl ∧
      FuncsGoodE ext s₁.funcs s₂.funcs := by
  have hS1 : StoreChkE ext s₁.funcs := storeChk_inv inv1 hS
  obtain ⟨ob, hob, hb'⟩ := callee_chk (ext := ext) hS1 hfi hcode hty hp
  obtain ⟨hok, hinv⟩ := ihb hS1 hb'
  exact ⟨ob, hob, hok, hinv.1⟩

/-- What the check of a call says before the callee runs. -/
theorem arity_call_pre {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    {labels : List Nat} {ret : Nat} {out : Option Nat} (hS : StoreChkE ext s.funcs)
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hc : chkE ext s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op (.call x) args :: es) = some out) :
    EvalInvE ext s f (s₁, f₁, .normal stk₁) ∧ ps.length ≤ stk₁.length ∧
      chkE ext s.funcs f.module f.locals.length ret labels
        (some (stk₁.length - ps.length + rs.length)) es = some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS iha h1
  obtain ⟨p, q, hpq, hp, ho⟩ := flatChk_call (flatChkE_call hf)
  have hca : callArity s₁.funcs f₁.module x = some (ps.length, rs.length) := callArity_eq hfi hty
  obtain ⟨rfl, rfl⟩ : p = ps.length ∧ q = rs.length := by
    rw [hca, Option.some.injEq, Prod.mk.injEq] at hpq
    exact ⟨hpq.1.symm, hpq.2.symm⟩
  exact ⟨inv1, hp, ho ▸ h2⟩

theorem arity_callOk {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType}
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (ihb : ArityGoodE ext s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₂, f₂, fl)) (hvs : fl.retVals = some vs)
    (ihk : ArityGoodE ext s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    ArityGoodE ext s f stk (.op (.call x) args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS iha hfi hty hc
  obtain ⟨ob, hob, hok, hfuncs⟩ := arity_callee hS inv1 hfi hcode hty hp ihb
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have inv2 : EvalInvE ext s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE ext s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [hlen]
    exact chk_inv inv2 h2
  obtain ⟨hok', inv3⟩ := ihk (storeChk_inv inv2 hS) h2'
  exact ⟨hok', inv2.trans inv3⟩

theorem arity_callTrap {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType}
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (ihb : ArityGoodE ext s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₂, f₂, .trap)) :
    ArityGoodE ext s f stk (.op (.call x) args :: es) (s₂, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS iha hfi hty hc
  obtain ⟨-, -, -, hfuncs⟩ := arity_callee hS inv1 hfi hcode hty hp ihb
  exact ⟨trivial, inv1.1.trans hfuncs, inv1.2.1, inv1.2.2⟩

theorem arity_callThrow {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {t : Nat}
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁)) (hfi : s₁.func? f₁ x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (ihb : ArityGoodE ext s₁ (Frame.forCall fi.module (stk₁.take ps.length).reverse fn.locals) []
      (Binaryen.liftInstrs fn.body) (s₂, f₂, .throw t)) :
    ArityGoodE ext s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, -⟩ := arity_call_pre hS iha hfi hty hc
  obtain ⟨_, _, hok, _⟩ := arity_callee hS inv1 hfi hcode hty hp ihb
  exact absurd hok id

/-! ### Blocks, loops and conditionals -/

/-- A checked body satisfies the check. -/
theorem arity_body {L : List Nat} {ret n₀ nr : Nat} {stk₀ : List Val} (hS : StoreChkE ext s.funcs)
    (hb : endsAt (chkE ext s.funcs f.module f.locals.length ret L (some n₀) body) nr = true)
    (hlen : stk₀.length = n₀) (ihb : ArityGoodE ext s f stk₀ body (s₁, f₁, fl)) :
    ∃ ob, (ob = none ∨ ob = some nr) ∧ FlowOk L ret ob fl ∧ EvalInvE ext s f (s₁, f₁, fl) := by
  obtain ⟨ob, hb', hob⟩ := endsAt_eq hb
  obtain ⟨hok, hinv⟩ := ihb hS (hlen ▸ hb')
  exact ⟨ob, hob, hok, hinv⟩

/-- Continuing after a block whose body handed on `vs`. -/
theorem arity_after {labels : List Nat} {ret np nr : Nat} {out : Option Nat}
    (hS : StoreChkE ext s.funcs) (inv1 : EvalInvE ext s f (s₁, f₁, fl)) (hnp : np ≤ stk.length)
    (hnr : nr ≤ vs.length)
    (h2 : chkE ext s.funcs f.module f.locals.length ret labels (some (stk.length - np + nr)) es =
      some out)
    (ihk : ArityGoodE ext s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    FlowOk labels ret out r.2.2 ∧ EvalInvE ext s f r := by
  have hlen : (vs.take nr ++ stk.drop np).length = stk.length - np + nr := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chkE ext s₁.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take nr ++ stk.drop np).length) es = some out := by
    rw [hlen]
    exact chk_inv inv1 h2
  obtain ⟨hok, inv2⟩ := ihk (storeChk_inv inv1 hS) h2'
  exact ⟨hok, inv1.trans inv2⟩

/-- What the check of a block says. -/
theorem arity_block_pre {bt : BlockType} {np nr : Nat} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (har : Binaryen.arity f bt = some (np, nr))
    (hc : chkE ext s.funcs f.module f.locals.length ret labels (some stk.length)
      (.block bt body :: es) = some out) :
    np ≤ stk.length ∧
      endsAt (chkE ext s.funcs f.module f.locals.length ret (nr :: labels) (some np) body) nr = true ∧
      chkE ext s.funcs f.module f.locals.length ret labels (some (stk.length - np + nr)) es =
        some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨np', nr', ha, hp, hb, ho⟩ := chk1_blockE h1
  rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact ⟨hp, hb, ho ▸ h2⟩

/-- What the check of a loop says. -/
theorem arity_loop_pre {bt : BlockType} {np nr : Nat} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (har : Binaryen.arity f bt = some (np, nr))
    (hc : chkE ext s.funcs f.module f.locals.length ret labels (some stk.length)
      (.loop bt body :: es) = some out) :
    np ≤ stk.length ∧
      endsAt (chkE ext s.funcs f.module f.locals.length ret (np :: labels) (some np) body) nr = true ∧
      chkE ext s.funcs f.module f.locals.length ret labels (some (stk.length - np + nr)) es =
        some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨np', nr', ha, hp, hb, ho⟩ := chk1_loopE h1
  rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact ⟨hp, hb, ho ▸ h2⟩

theorem take_length_of_le {np : Nat} (h : np ≤ stk.length) : (stk.take np).length = np := by
  simp only [List.length_take]
  omega

theorem arity_blockOk {bt : BlockType} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, fl)) (hvs : fl.blockVals = some vs)
    (ihk : ArityGoodE ext s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    ArityGoodE ext s f stk (.block bt body :: es) r := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_block_pre har hc
  obtain ⟨ob, hob, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact arity_after hS inv1 hp (blockVals_length hok hob hvs) h2 ihk

theorem arity_blockBrk {bt : BlockType} {np nr k : Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
    ArityGoodE ext s f stk (.block bt body :: es) (s₁, f₁, .brk k vs) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨_, _, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.brk_succ, inv1⟩

theorem arity_blockEsc {bt : BlockType} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, fl)) (hfl : fl.Escapes) :
    ArityGoodE ext s f stk (.block bt body :: es) (s₁, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨_, _, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.escape hfl, inv1⟩

theorem arity_loopOk {bt : BlockType} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, .normal vs))
    (ihk : ArityGoodE ext s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    ArityGoodE ext s f stk (.loop bt body :: es) r := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_loop_pre har hc
  obtain ⟨ob, hob, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact arity_after hS inv1 hp (length_of_ends hok hob).ge h2 ihk

theorem arity_loopBack {bt : BlockType} {np nr : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, .brk 0 vs))
    (ihk : ArityGoodE ext s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
    ArityGoodE ext s f stk (.loop bt body :: es) r := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  obtain ⟨m, hm, hle⟩ := hok
  have hnp : np ≤ vs.length := by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    exact hm ▸ hle
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have hc' : chkE ext s₁.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
    rw [hlen]
    exact chk_inv inv1 hc
  obtain ⟨hok', inv2⟩ := ihk (storeChk_inv inv1 hS) hc'
  exact ⟨hok', inv1.trans inv2⟩

theorem arity_loopBrk {bt : BlockType} {np nr k : Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs)) :
    ArityGoodE ext s f stk (.loop bt body :: es) (s₁, f₁, .brk k vs) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.brk_succ, inv1⟩

theorem arity_loopEsc {bt : BlockType} {np nr : Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE ext s f (stk.take np) body (s₁, f₁, fl)) (hfl : fl.Escapes) :
    ArityGoodE ext s f stk (.loop bt body :: es) (s₁, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.escape hfl, inv1⟩

/-- What the check of an `if` says once its condition has run. -/
theorem arity_if_pre {bt : BlockType} {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    {np nr : Nat} {labels : List Nat} {ret : Nat} {out : Option Nat} (hS : StoreChkE ext s.funcs)
    (ihc : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (har : Binaryen.arity f₁ bt = some (np, nr))
    (hc : chkE ext s.funcs f.module f.locals.length ret labels (some stk.length)
      (.if_ bt c t el :: es) = some out) :
    EvalInvE ext s f (s₁, f₁, .normal (cv :: stk₁)) ∧ np ≤ stk₁.length ∧
      endsAt (chkE ext s.funcs f.module f.locals.length ret (nr :: labels) (some np)
        (if b then t else el)) nr = true ∧
      chkE ext s.funcs f.module f.locals.length ret labels (some (stk₁.length - np + nr)) es =
        some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := chk1_ifE h1
  obtain ⟨hoc, inv1⟩ := ihc hS hco
  obtain ⟨np', nr', ha, hp, ht, he, ho⟩ := hk1 _ hoc
  rw [← inv1.2.1, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  have hlen : (cv :: stk₁).length - 1 - np + nr = stk₁.length - np + nr := by
    simp only [List.length_cons]
    omega
  refine ⟨inv1, by simp only [List.length_cons] at hp; omega, ?_, by rw [← hlen, ← ho]; exact h2⟩
  cases b
  · exact he
  · exact ht

theorem arity_ifOk {bt : BlockType} {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    {np nr : Nat} (ihc : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : ArityGoodE ext s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (hvs : fl.blockVals = some vs) (ihk : ArityGoodE ext s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
    ArityGoodE ext s f stk (.if_ bt c t el :: es) r := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hb, h2⟩ := arity_if_pre (b := b) hS ihc har hc
  replace hb := chk_inv_endsAt inv1 hb
  replace h2 := chk_inv inv1 h2
  obtain ⟨ob, hob, hok, inv2⟩ :=
    arity_body (storeChk_inv inv1 hS) hb (take_length_of_le hp) iharm
  obtain ⟨hok', inv3⟩ := arity_after (storeChk_inv inv1 hS) inv2 hp
    (blockVals_length hok hob hvs) h2 ihk
  exact ⟨hok', inv1.trans inv3⟩

theorem arity_ifBrk {bt : BlockType} {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    {np nr k : Nat} (ihc : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : ArityGoodE ext s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, .brk (k + 1) vs)) :
    ArityGoodE ext s f stk (.if_ bt c t el :: es) (s₂, f₂, .brk k vs) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hb, -⟩ := arity_if_pre (b := b) hS ihc har hc
  replace hb := chk_inv_endsAt inv1 hb
  obtain ⟨_, _, hok, inv2⟩ := arity_body (storeChk_inv inv1 hS) hb (take_length_of_le hp) iharm
  exact ⟨hok.brk_succ, inv1.trans inv2⟩

theorem arity_ifEsc {bt : BlockType} {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    {np nr : Nat} (ihc : ArityGoodE ext s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (har : Binaryen.arity f₁ bt = some (np, nr))
    (iharm : ArityGoodE ext s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (hfl : fl.Escapes) :
    ArityGoodE ext s f stk (.if_ bt c t el :: es) (s₂, f₂, fl) := by
  intro labels ret out hS hc
  obtain ⟨inv1, hp, hb, -⟩ := arity_if_pre (b := b) hS ihc har hc
  replace hb := chk_inv_endsAt inv1 hb
  obtain ⟨_, _, hok, inv2⟩ := arity_body (storeChk_inv inv1 hS) hb (take_length_of_le hp) iharm
  exact ⟨hok.escape hfl, inv1.trans inv2⟩

theorem arity_ifAbort {bt : BlockType} {c t el : List Binaryen.BExpr}
    (ihc : ArityGoodE ext s f stk c (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
    ArityGoodE ext s f stk (.if_ bt c t el :: es) (s₁, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_ifE h1
  obtain ⟨hok, inv1⟩ := ihc hS hco
  exact ⟨hok.abrupt hfl, inv1⟩

end Cases

/-- **Soundness of the arity check for native evaluation.** -/
theorem flowOk_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : Binaryen.Eval s f stk es r) :
    ArityGood s f stk es r := by
  induction h with
  | nil => exact arity_nil
  | argsAbort _ hfl iha => exact arity_argsAbort iha hfl
  | callOk _ hfi hcode hty _ hvs _ iha ihb ihk => exact arity_callOk iha hfi hcode hty ihb hvs ihk
  | callTrap _ hfi hcode hty _ iha ihb => exact arity_callTrap iha hfi hcode hty ihb
  | callThrow _ hfi hcode hty _ iha ihb => exact arity_callThrow iha hfi hcode hty ihb
  | opOk _ _ hflat _ iha ihk => exact arity_opOk iha hflat ihk
  | opStop _ _ hflat hfl iha => exact arity_opStop iha hflat hfl
  | blockOk har _ hvs _ ihb ihk => exact arity_blockOk har ihb hvs ihk
  | blockBrk har _ ihb => exact arity_blockBrk har ihb
  | blockEsc har _ hfl ihb => exact arity_blockEsc har ihb hfl
  | loopOk har _ _ ihb ihk => exact arity_loopOk har ihb ihk
  | loopBack har _ _ ihb ihk => exact arity_loopBack har ihb ihk
  | loopBrk har _ ihb => exact arity_loopBrk har ihb
  | loopEsc har _ hfl ihb => exact arity_loopEsc har ihb hfl
  | ifOk _ _ har _ hvs _ ihc iharm ihk => exact arity_ifOk ihc har iharm hvs ihk
  | ifBrk _ _ har _ ihc iharm => exact arity_ifBrk ihc har iharm
  | ifEsc _ _ har _ hfl ihc iharm => exact arity_ifEsc ihc har iharm hfl
  | ifAbort _ hfl ihc => exact arity_ifAbort ihc hfl

end Silmaril.Wasm.Interp
