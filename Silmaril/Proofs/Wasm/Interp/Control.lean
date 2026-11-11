module

public import Silmaril.Proofs.Wasm.Interp.Arity
public import Silmaril.Proofs.Wasm.Interp.Trap

@[expose] public section

/-!
# Native evaluation with structured control and calls is a Core 3.0 run (proofs)

`wp_of_eval`: a native evaluation (`Binaryen.Eval`) of arity-checked trees (`chk`, `StoreChk`)
— straight-line integer operators, `unreachable`, blocks, loops, `if`, `br`, `br_if`,
`return` and direct calls — is matched by a Core 3.0 run of the lowering, at every profile and
host: `Silmaril.Wasm.Logic.Core.WP` with the postcondition `Match` (same store and frame; normal
results equal; branches and returns to the same target with the native values on top; traps).
Uses `flowOk_of_eval` (`Silmaril.Proofs.Wasm.Interp.Arity`) for the heights at which blocks and
calls hand on their values, where the interpreter truncates with `take` and Core does not.
New proofs. Summary in `Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Outcomes and runs -/

section Runs

variable {s s' : Store H} {f f' : Frame}

/-- The lowering of a sequence, element by element. -/
theorem code_cons (e : Binaryen.BExpr) (es : List Binaryen.BExpr) :
    expression (Binaryen.BExpr.lowerList (e :: es)) =
      expression e.lower ++ expression (Binaryen.BExpr.lowerList es) := by
  simp [expression]

/-- A run reaching a matched outcome. -/
theorem run_of_wp {c : List Admin} {r : Store H × Frame × Binaryen.Flow}
    (h : WP P host s f c (Match r)) :
    ∃ c' o, Steps P host ⟨s, f, c⟩ ⟨r.1, r.2.1, c'⟩ ∧ o.Ends c' ∧ FlowMatch r.2.2 o := by
  obtain ⟨s', f', c', o, hs, he, rfl, rfl, hm⟩ := h
  exact ⟨c', o, hs, he, hm⟩

/-- The final form of a normal outcome. -/
theorem ends_normal {vs : List Val} {o : Outcome} {c' : List Admin}
    (hm : FlowMatch (.normal vs) o) (he : o.Ends c') : c' = vals vs.reverse := by
  rcases o with ws | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
  subst hm
  exact he

theorem wp_abrupt_br {c' : List Admin} {o : Outcome} {l : Nat} {vs : List Val} (he : o.Ends c')
    (hm : FlowMatch (.brk l vs) o) (pre : List Val) (rest : List Admin) :
    WP P host s f (vals pre ++ c' ++ rest) (Match (s, f, .brk l vs)) := by
  rcases o with _ | ⟨l', ws⟩ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
  obtain ⟨rfl, junk, rfl⟩ := hm
  obtain ⟨x, rest', hx, rfl⟩ := he
  have e : vals pre ++ (vals (junk ++ vs.reverse) ++ .plain (.br x) :: rest') ++ rest =
      vals (pre ++ junk ++ vs.reverse) ++ .plain (.br x) :: (rest' ++ rest) := by simp
  rw [e]
  exact wp_br ⟨rfl, rfl, hx, pre ++ junk, by simp⟩

theorem wp_abrupt_ret {c' : List Admin} {o : Outcome} {vs : List Val} (he : o.Ends c')
    (hm : FlowMatch (.ret vs) o) (pre : List Val) (rest : List Admin) :
    WP P host s f (vals pre ++ c' ++ rest) (Match (s, f, .ret vs)) := by
  rcases o with _ | _ | ws | _ | _ | _ <;> simp only [FlowMatch] at hm
  obtain ⟨junk, rfl⟩ := hm
  obtain ⟨rest', rfl⟩ := he
  have e : vals pre ++ (vals (junk ++ vs.reverse) ++ .plain .return_ :: rest') ++ rest =
      vals (pre ++ junk ++ vs.reverse) ++ .plain .return_ :: (rest' ++ rest) := by simp
  rw [e]
  exact wp_return ⟨rfl, rfl, pre ++ junk, by simp⟩

theorem wp_abrupt_trap {c' : List Admin} {o : Outcome} (he : o.Ends c')
    (hm : FlowMatch .trap o) (pre : List Val) (rest : List Admin) :
    WP P host s f (vals pre ++ c' ++ rest) (Match (s, f, .trap)) := by
  rcases o with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
  have hc : c' = [.trap] := he
  subst hc
  simpa using (wp_trap (P := P) (host := host) (s := s) (f := f) (vs := pre) (rest := rest)
    (Q := Match (s, f, .trap)) ⟨rfl, rfl, trivial⟩)

/-- An abrupt final form, in a value prefix and before more code, is a final form. -/
theorem wp_abrupt {c' : List Admin} {o : Outcome} {fl : Binaryen.Flow} (he : o.Ends c')
    (hm : FlowMatch fl o) (hn : ¬ fl.IsNormal) (pre : List Val) (rest : List Admin) :
    WP P host s f (vals pre ++ c' ++ rest) (Match (s, f, fl)) := by
  rcases fl with vs | ⟨l, vs⟩ | vs | _ | a
  · exact absurd trivial hn
  · exact wp_abrupt_br he hm pre rest
  · exact wp_abrupt_ret he hm pre rest
  · exact wp_abrupt_trap he hm pre rest
  · rcases o <;> simp only [FlowMatch] at hm

/-- A sequence whose first part ends abruptly. -/
theorem wp_append_abrupt' {c rest : List Admin} {s₁ : Store H} {f₁ : Frame} {fl : Binaryen.Flow}
    (h : WP P host s f c (Match (s₁, f₁, fl))) (hn : ¬ fl.IsNormal) :
    WP P host s f (c ++ rest) (Match (s₁, f₁, fl)) := by
  obtain ⟨c', o, hst, he, hm⟩ := run_of_wp h
  have h2 : WP P host s₁ f₁ (vals [] ++ c' ++ rest) (Match (s₁, f₁, fl)) :=
    wp_abrupt he hm hn [] rest
  exact WP.steps (Steps.append rest hst) (by simpa [vals] using h2)

/-- A sequence whose first part completes normally. -/
theorem wp_append_normal {c rest : List Admin} {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val}
    {Q : Post H} (h : WP P host s f c (Match (s₁, f₁, .normal stk₁)))
    (hk : WP P host s₁ f₁ (vals stk₁.reverse ++ rest) Q) : WP P host s f (c ++ rest) Q := by
  obtain ⟨c', o, hst, he, hm⟩ := run_of_wp h
  have hc : c' = vals stk₁.reverse := ends_normal hm he
  subst hc
  exact WP.steps (Steps.append rest hst) hk

end Runs

/-! ## Flat instructions -/

section Flat

variable {s s' : Store H} {f f' : Frame} {stk stk' : List Val}
  {F : List (FuncInst H)} {mi : ModuleInst} {ret : Nat} {labels : List Nat}

/-- A native condition is an `i32`. -/
theorem truthy_eq {v : Val} {b : Bool} (h : Binaryen.truthy v = some b) :
    ∃ c : BitVec 32, v = Val.i32 c ∧ b = (c != 0) := by
  simp only [Binaryen.truthy, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, eq_ofInt_of_asInt hc, rfl⟩

/-- A checked flat instruction completing normally, other than `br_if`, `select` and
`call`, is a straight-line one. -/
theorem straight_of_flatChk {nl : Nat} {h₀ : Nat} {o : Option Nat} {i : Instr}
    (hi : ∀ x, i ≠ .call x) (hb : ∀ l, i ≠ .brIf l) (hsel : ∀ t, i ≠ .select t)
    (hc : flatChk F mi nl ret labels h₀ i = some o)
    (h : Binaryen.evalFlat s f stk i = some (s', f', .normal stk')) :
    Instr.straight i = true ∧ Instr.setsBelow nl i = true := by
  by_cases hbt : ∃ ls d, i = .brTable ls d
  · obtain ⟨ls, d, rfl⟩ := hbt
    obtain ⟨_, _, _, -, -, -, -, hfl⟩ := evalFlat_brTable h
    cases hfl
  cases i
  all_goals try first | exact absurd rfl (hsel _) | exact absurd ⟨_, _, rfl⟩ hbt
  all_goals simp only [flatChk, flatEff] at hc
  all_goals (repeat' split at hc) <;> simp_all [Instr.straight, Instr.setsBelow, Instr.setIdx?,
    Binaryen.evalFlat]

/-- `select`. -/
theorem steps_select {t : Option (List ValType)}
    (h : Binaryen.evalFlat s f stk (.select t) = some (s', f', .normal stk')) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain (.select t) :: rest⟩
      ⟨s', f', vals stk'.reverse ++ rest⟩ := by
  obtain ⟨c, b, a, r, bv, rfl, hbv, rfl, rfl, hfl⟩ := evalFlat_select h
  have hs : stk' = (if bv then a else b) :: r := Binaryen.Flow.normal.inj hfl
  subst hs
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hbv
  have e : vals (Val.i32 c₀ :: b :: a :: r).reverse ++ .plain (.select t) :: rest =
      vals r.reverse ++ [a.toAdmin, b.toAdmin, constI32 c₀, .plain (.select t)] ++ rest := by
    simp [vals, constI32]
  rw [e]
  by_cases h0 : c₀ = 0
  · have hv : (if (c₀ != 0) = true then a else b) = b := by simp [h0]
    have e2 : vals ((if (c₀ != 0) = true then a else b) :: r).reverse ++ rest =
        vals r.reverse ++ [b.toAdmin] ++ rest := by rw [hv]; simp [vals]
    rw [e2]
    subst h0
    exact .single (Step.ctx r.reverse rest (.parametric (.selectFalse a b t)))
  · have h1 : (c₀ != 0) = true := by simpa using h0
    have hv : (if (c₀ != 0) = true then a else b) = a := by rw [h1]; rfl
    have e2 : vals ((if (c₀ != 0) = true then a else b) :: r).reverse ++ rest =
        vals r.reverse ++ [a.toAdmin] ++ rest := by rw [hv]; simp [vals]
    rw [e2]
    exact .single (Step.ctx r.reverse rest (.parametric (.selectTrue h0)))

/-- `br_if` not taken. -/
theorem steps_brIf_false {l : LabelIdx}
    (h : Binaryen.evalFlat s f stk (.brIf l) = some (s', f', .normal stk')) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain (.brIf l) :: rest⟩
      ⟨s', f', vals stk'.reverse ++ rest⟩ := by
  rcases stk with _ | ⟨c, r⟩
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, hr⟩ := h
    obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
    by_cases h0 : c₀ = 0
    · subst h0
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, Prod.mk.injEq,
        Binaryen.Flow.normal.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      have e : vals (Val.i32 0 :: r).reverse ++ .plain (.brIf l) :: rest =
          vals r.reverse ++ [constI32 0, .plain (.brIf l)] ++ rest := by simp [vals, constI32]
      rw [e]
      simpa using (Steps.ctx (P := P) (host := host) r.reverse rest
        (.single (Step.brIfFalse (s := s) (f := f) (l := l))))
    · have h1 : (c₀ != 0) = true := by simpa using h0
      simp only [h1, ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_false] at hr

/-- A checked flat instruction completing normally is a Core run. -/
theorem steps_flat_normal {h₀ : Nat} {o : Option Nat} {i : Instr} (hi : ∀ x, i ≠ .call x)
    (hc : flatChk F mi f.locals.length ret labels h₀ i = some o)
    (h : Binaryen.evalFlat s f stk i = some (s', f', .normal stk')) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩
      ⟨s', f', vals stk'.reverse ++ rest⟩ := by
  by_cases hb : ∃ l, i = .brIf l
  · obtain ⟨l, rfl⟩ := hb
    exact steps_brIf_false h rest
  by_cases hsel : ∃ t, i = .select t
  · obtain ⟨t, rfl⟩ := hsel
    exact steps_select h rest
  · have hb' : ∀ l, i ≠ .brIf l := fun l hl => hb ⟨l, hl⟩
    have hsel' : ∀ t, i ≠ .select t := fun t ht => hsel ⟨t, ht⟩
    obtain ⟨hs, hsb⟩ := straight_of_flatChk hi hb' hsel' hc h
    have e1 : exec1 s f stk i = some (s', f', stk') := (exec1_of_evalFlat hs hsb h).1
    have e2 : exec s f stk [i] = some (s', f', stk') := by
      rw [exec_cons_of_some e1]
      rfl
    simpa [expression] using exec_sound (P := P) (host := host) rest e2

/-- A native binary operator stops only by trapping. -/
theorem binop_abrupt {t : IntType} {op : IntBinOp} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.intBinOp t op) = some (s', f', fl)) (hn : ¬ fl.IsNormal) :
    fl = .trap := by
  rcases stk with _ | ⟨y, _ | ⟨x, r⟩⟩
  · simp [Binaryen.evalFlat] at h
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat] at h
    cases hx : Binaryen.asInt t x <;> cases hy : Binaryen.asInt t y <;> simp [hx, hy] at h
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨-, -, rfl⟩ := h
    · exact absurd trivial hn
    · rfl

theorem wp_flat_unreachable (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain .unreachable :: rest) (Match (s, f, .trap)) := by
  have st : Step P host ⟨s, f, vals stk.reverse ++ [.plain .unreachable] ++ rest⟩
      ⟨s, f, vals stk.reverse ++ [.trap] ++ rest⟩ :=
    Step.ctx stk.reverse rest (.parametric .unreachable)
  have hw : WP P host s f (vals stk.reverse ++ .trap :: rest) (Match (s, f, .trap)) :=
    wp_trap ⟨rfl, rfl, trivial⟩
  simpa using WP.step st (by simpa using hw)

theorem wp_flat_brIf {l : LabelIdx} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.brIf l) = some (s', f', fl)) (hn : ¬ fl.IsNormal)
    (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain (.brIf l) :: rest) (Match (s', f', fl)) := by
  rcases stk with _ | ⟨c, r⟩
  · simp [Binaryen.evalFlat] at h
  · simp only [Binaryen.evalFlat, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, hr⟩ := h
    obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
    by_cases h0 : c₀ = 0
    · subst h0
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      exact absurd trivial hn
    · have h1 : (c₀ != 0) = true := by simpa using h0
      simp only [h1, ↓reduceIte, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      have e : vals (Val.i32 c₀ :: r).reverse = vals (r.reverse ++ [Val.i32 c₀]) := by simp
      rw [e]
      exact wp_brIf_true h0 ⟨rfl, rfl, rfl, [], by simp⟩

theorem wp_flat_br {l : LabelIdx} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.br l) = some (s', f', fl)) (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain (.br l) :: rest) (Match (s', f', fl)) := by
  simp only [Binaryen.evalFlat, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact wp_br ⟨rfl, rfl, rfl, [], by simp⟩

theorem wp_flat_return {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk .return_ = some (s', f', fl)) (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain .return_ :: rest) (Match (s', f', fl)) := by
  simp only [Binaryen.evalFlat, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact wp_return ⟨rfl, rfl, [], by simp⟩

theorem wp_flat_unreachable' {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk .unreachable = some (s', f', fl)) (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain .unreachable :: rest) (Match (s', f', fl)) := by
  simp only [Binaryen.evalFlat, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact wp_flat_unreachable rest

theorem wp_flat_binop {t : IntType} {op : IntBinOp} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.intBinOp t op) = some (s', f', fl)) (hn : ¬ fl.IsNormal)
    (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain (.intBinOp t op) :: rest) (Match (s', f', fl)) := by
  obtain rfl : fl = .trap := binop_abrupt h hn
  have st := steps_binop_trap (P := P) (host := host) h rest
  exact ⟨s', f', [.trap], .trap, by simpa using st, rfl, rfl, rfl, trivial⟩

theorem wp_flat_brTable {ls : List LabelIdx} {d : LabelIdx} {fl : Binaryen.Flow}
    (h : Binaryen.evalFlat s f stk (.brTable ls d) = some (s', f', fl)) (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain (.brTable ls d) :: rest) (Match (s', f', fl)) := by
  obtain ⟨c, r, i, rfl, hi, rfl, rfl, rfl⟩ := evalFlat_brTable h
  have hc : c = Val.i32 i := eq_ofInt_of_asInt hi
  subst hc
  have e : vals (Val.i32 i :: r).reverse = vals (r.reverse ++ [Val.i32 i]) := by simp
  rw [e]
  rcases hl : ls[i.toNat]? with _ | l
  · have hge : ls.length ≤ i.toNat := List.getElem?_eq_none_iff.mp hl
    exact wp_brTable_ge hge ⟨rfl, rfl, by simp, [], by simp⟩
  · exact wp_brTable_lt hl ⟨rfl, rfl, by simp, [], by simp⟩

/-- A checked flat instruction stopping abruptly reaches a matching final form. -/
theorem wp_flat_abrupt {h₀ : Nat} {o : Option Nat} {i : Instr} {fl : Binaryen.Flow}
    (hc : flatChk F mi f.locals.length ret labels h₀ i = some o)
    (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) (hn : ¬ fl.IsNormal)
    (rest : List Admin) :
    WP P host s f (vals stk.reverse ++ .plain i :: rest) (Match (s', f', fl)) := by
  by_cases hs : Instr.straight i = true
  · rcases flat_flow hs h with hnorm | ⟨t, op, rfl⟩
    · exact absurd hnorm hn
    · exact wp_flat_binop h hn rest
  · cases i
    all_goals try first | exact absurd rfl hs
    case unreachable => exact wp_flat_unreachable' h rest
    case br l => exact wp_flat_br h rest
    case brIf l => exact wp_flat_brIf h hn rest
    case brTable ls d => exact wp_flat_brTable h rest
    case select t =>
      obtain ⟨_, _, _, _, _, -, -, -, -, rfl⟩ := evalFlat_select h
      exact absurd trivial hn
    case return_ => exact wp_flat_return h rest
    all_goals exfalso
    all_goals first | (simp [flatChk, flatEff] at hc; done) | simp [Binaryen.evalFlat] at h

end Flat

/-! ## Leaving a label -/

section Label

variable {s₁ : Store H} {f₁ : Frame} {n : Nat} {cont : List Instr} {c' : List Admin}
  {o : Outcome} {vs : List Val}

/-- Splitting the top `n` values off a reversed stack. -/
theorem rev_split (junk vs : List Val) (n : Nat) :
    junk ++ vs.reverse = (junk ++ (vs.drop n).reverse) ++ (vs.take n).reverse := by
  conv_lhs => rw [← List.take_append_drop n vs]
  simp

/-- A body that completed normally leaves its label with its values. -/
theorem exit_normal (he : o.Ends c') (hm : FlowMatch (.normal vs) o) (pre : List Val)
    (rest : List Admin) :
    Steps P host ⟨s₁, f₁, vals pre ++ [.label n cont c'] ++ rest⟩
      ⟨s₁, f₁, vals (pre ++ vs.reverse) ++ rest⟩ := by
  have hc : c' = vals vs.reverse := ends_normal hm he
  subst hc
  simpa using Steps.ctx (P := P) (host := host) pre rest
    (.single (Step.labelVals (s := s₁) (f := f₁) (n := n) (cont := cont)))

/-- A branch to the label continues with its continuation on the top `n` values. -/
theorem exit_br0 (he : o.Ends c') (hm : FlowMatch (.brk 0 vs) o) (hn : n ≤ vs.length)
    (pre : List Val) (rest : List Admin) :
    Steps P host ⟨s₁, f₁, vals pre ++ [.label n cont c'] ++ rest⟩
      ⟨s₁, f₁, vals (pre ++ (vs.take n).reverse) ++ expression cont ++ rest⟩ := by
  rcases o with _ | ⟨l', ws⟩ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
  obtain ⟨rfl, junk, rfl⟩ := hm
  obtain ⟨x, rest', hx, rfl⟩ := he
  have hlen : (vs.take n).reverse.length = n := by
    simp only [List.length_reverse, List.length_take]
    omega
  have e : vals (junk ++ vs.reverse) ++ .plain (.br x) :: rest' =
      vals (junk ++ (vs.drop n).reverse) ++ vals (vs.take n).reverse ++ [.plain (.br x)] ++
        rest' := by
    rw [rev_split junk vs n]
    simp
  have st : Step P host ⟨s₁, f₁, [.label n cont (vals (junk ++ vs.reverse) ++
      .plain (.br x) :: rest')]⟩ ⟨s₁, f₁, vals (vs.take n).reverse ++ expression cont⟩ := by
    rw [e]
    exact Step.brLabelZero hx hlen
  simpa using Steps.ctx pre rest (.single st)

theorem label_step_brk {k : Nat} (he : o.Ends c') (hm : FlowMatch (.brk (k + 1) vs) o) :
    ∃ c'' o', Step P host ⟨s₁, f₁, [.label n cont c']⟩ ⟨s₁, f₁, c''⟩ ∧ o'.Ends c'' ∧
      FlowMatch (.brk k vs) o' := by
  rcases o with _ | ⟨l', ws⟩ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
  obtain ⟨rfl, junk, rfl⟩ := hm
  obtain ⟨x, rest', hx, rfl⟩ := he
  have hl : (labelPred x).toNat = k := by
    show x.toNat - 1 = k
    omega
  refine ⟨vals (junk ++ vs.reverse) ++ [.plain (.br (labelPred x))], .br k (junk ++ vs.reverse),
    ?_, ⟨labelPred x, [], hl, rfl⟩, rfl, junk, rfl⟩
  simpa only [List.append_assoc, List.singleton_append] using
    Step.brLabelSucc (P := P) (host := host) (s := s₁) (f := f₁) (n := n) (cont := cont)
      (vs := junk ++ vs.reverse) (l := x) (rest := rest') (by omega)

theorem label_step_ret (he : o.Ends c') (hm : FlowMatch (.ret vs) o) :
    ∃ c'' o', Step P host ⟨s₁, f₁, [.label n cont c']⟩ ⟨s₁, f₁, c''⟩ ∧ o'.Ends c'' ∧
      FlowMatch (.ret vs) o' := by
  rcases o with _ | _ | ws | _ | _ | _ <;> simp only [FlowMatch] at hm
  obtain ⟨junk, rfl⟩ := hm
  obtain ⟨rest', rfl⟩ := he
  refine ⟨vals (junk ++ vs.reverse) ++ [.plain .return_], .ret (junk ++ vs.reverse), ?_,
    ⟨[], rfl⟩, junk, rfl⟩
  simpa only [List.append_assoc, List.singleton_append] using
    Step.returnLabel (P := P) (host := host) (s := s₁) (f := f₁) (n := n) (cont := cont)
      (vs := junk ++ vs.reverse) (rest := rest')

theorem label_step_trap (he : o.Ends c') (hm : FlowMatch .trap o) :
    ∃ c'' o', Step P host ⟨s₁, f₁, [.label n cont c']⟩ ⟨s₁, f₁, c''⟩ ∧ o'.Ends c'' ∧
      FlowMatch .trap o' := by
  rcases o with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
  have hc : c' = [.trap] := he
  subst hc
  exact ⟨[.trap], .trap, .trapLabel, rfl, trivial⟩

/-- One step out of a label for a branch to an outer label, a return or a trap. -/
theorem label_step_abrupt {fl fl' : Binaryen.Flow} (he : o.Ends c') (hm : FlowMatch fl o)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    ∃ c'' o', Step P host ⟨s₁, f₁, [.label n cont c']⟩ ⟨s₁, f₁, c''⟩ ∧ o'.Ends c'' ∧
      FlowMatch fl' o' := by
  rcases hfl with ⟨k, vs, rfl, rfl⟩ | ⟨hesc, hfl'⟩
  · exact label_step_brk he hm
  · rw [hfl']
    rcases fl with _ | _ | vs | _ | _ <;> simp only [Binaryen.Flow.Escapes] at hesc
    · exact label_step_ret he hm
    · exact label_step_trap he hm
    · rcases o <;> simp only [FlowMatch] at hm

/-- Leaving a label for a branch to an outer label, a return or a trap. -/
theorem exit_abrupt {fl fl' : Binaryen.Flow} (he : o.Ends c') (hm : FlowMatch fl o)
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl))
    (pre : List Val) (rest : List Admin) :
    WP P host s₁ f₁ (vals pre ++ [.label n cont c'] ++ rest) (Match (s₁, f₁, fl')) := by
  obtain ⟨c'', o', st, he', hm'⟩ := label_step_abrupt (P := P) (host := host) (s₁ := s₁)
    (f₁ := f₁) (n := n) (cont := cont) he hm hfl
  have hn : ¬ fl'.IsNormal := by
    rcases hfl with ⟨k, vs, -, rfl⟩ | ⟨hesc, rfl⟩
    · exact id
    · rcases fl' <;> simp_all [Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]
  exact WP.steps (Steps.ctx pre rest (.single st)) (wp_abrupt he' hm' hn pre rest)

end Label

/-! ## Blocks and loops -/

section Blocks

variable {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType} {B : List Instr}
  {np nr : Nat} {fl : Binaryen.Flow}

/-- The Core block type of a native block arity. -/
theorem blockType_of_arity (har : Binaryen.arity f bt = some (np, nr)) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ t₁.length = np ∧ t₂.length = nr := by
  cases bt with
  | empty =>
    simp only [Binaryen.arity, Option.some.injEq, Prod.mk.injEq] at har
    obtain ⟨rfl, rfl⟩ := har
    exact ⟨[], [], rfl, rfl, rfl⟩
  | value t =>
    simp only [Binaryen.arity, Option.some.injEq, Prod.mk.injEq] at har
    obtain ⟨rfl, rfl⟩ := har
    exact ⟨[], [f.module.instVal t], rfl, rfl, rfl⟩
  | typeIdx x =>
    simp only [Binaryen.arity, Option.map_eq_some_iff, Prod.mk.injEq] at har
    obtain ⟨⟨t₁, t₂⟩, hx, rfl, rfl⟩ := har
    exact ⟨t₁, t₂, hx, rfl, rfl⟩

/-- The stack below and the arguments of a block. -/
theorem rev_take_drop (stk : List Val) (np : Nat) :
    stk.reverse = (stk.drop np).reverse ++ (stk.take np).reverse := by
  conv_lhs => rw [← List.take_append_drop np stk]
  simp

/-- Entering a block or a loop, below the values `pre`. -/
theorem step_enter {lbl : Nat} {cont : List Instr} {i : Instr} (hp : np ≤ stk.length)
    (hst : ∀ args : List Val, args.length = np →
      Step P host ⟨s, f, vals args ++ [.plain i]⟩
        ⟨s, f, [.label lbl cont (vals args ++ expression B)]⟩)
    (rest : List Admin) :
    Step P host ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.label lbl cont (vals (stk.take np).reverse ++ expression B)] ++ rest⟩ := by
  have hlen : (stk.take np).reverse.length = np := by
    simp only [List.length_reverse, List.length_take]
    omega
  have e : vals stk.reverse ++ .plain i :: rest =
      vals (stk.drop np).reverse ++ (vals (stk.take np).reverse ++ [.plain i]) ++ rest := by
    rw [rev_take_drop stk np]
    simp
  rw [e]
  exact Step.ctx _ rest (hst _ hlen)

theorem steps_enter {lbl : Nat} {cont : List Instr} {i : Instr} (hp : np ≤ stk.length)
    (hst : ∀ args : List Val, args.length = np →
      Step P host ⟨s, f, vals args ++ [.plain i]⟩
        ⟨s, f, [.label lbl cont (vals args ++ expression B)]⟩)
    (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain i :: rest⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.label lbl cont (vals (stk.take np).reverse ++ expression B)] ++ rest⟩ :=
  .single (step_enter hp hst rest)

theorem step_block (har : Binaryen.arity f bt = some (np, nr)) (args : List Val)
    (hlen : args.length = np) :
    Step P host ⟨s, f, vals args ++ [.plain (.block bt B)]⟩
      ⟨s, f, [.label nr [] (vals args ++ expression B)]⟩ := by
  obtain ⟨t₁, t₂, hbt, h1, h2⟩ := blockType_of_arity har
  subst h2
  exact Step.block hbt (hlen.trans h1.symm)

theorem step_loop (har : Binaryen.arity f bt = some (np, nr)) (args : List Val)
    (hlen : args.length = np) :
    Step P host ⟨s, f, vals args ++ [.plain (.loop bt B)]⟩
      ⟨s, f, [.label np [.loop bt B] (vals args ++ expression B)]⟩ := by
  obtain ⟨t₁, t₂, hbt, h1, h2⟩ := blockType_of_arity har
  subst h1
  exact Step.loop hbt hlen

/-- The values a block hands on, below the values the block did not consume. -/
theorem stack_after (stk vs : List Val) (np nr : Nat) :
    vals (vs.take nr ++ stk.drop np).reverse =
      vals ((stk.drop np).reverse ++ (vs.take nr).reverse) := by
  simp

/-- Leaving a block's label with the values its body hands on. -/
theorem exit_blockVals {c' : List Admin} {o : Outcome} {pre : List Val} {rest : List Admin}
    (he : o.Ends c') (hm : FlowMatch fl o) (hvs : fl.blockVals = some vs) (hnr : nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr) :
    Steps P host ⟨s₁, f₁, vals pre ++ [.label nr [] c'] ++ rest⟩
      ⟨s₁, f₁, vals (pre ++ (vs.take nr).reverse) ++ rest⟩ := by
  rcases fl with ws | ⟨_ | k, ws⟩ | _ | _ | _ <;> simp only [Binaryen.Flow.blockVals,
    reduceCtorEq, Option.some.injEq] at hvs
  · subst ws
    rw [List.take_of_length_le (hnorm vs rfl).le]
    exact exit_normal he hm pre rest
  · subst ws
    simpa using exit_br0 (P := P) (host := host) (s₁ := s₁) (f₁ := f₁) (cont := []) he hm hnr
      pre rest

/-- **A block whose body hands on values**, as a run to its continuation. -/
theorem tg_block_vals {rest : List Admin} {c' : List Admin} {o : Outcome}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : Steps P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ ⟨s₁, f₁, c'⟩)
    (he : o.Ends c') (hm : FlowMatch fl o)
    (hvs : fl.blockVals = some vs) (hnr : nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr) :
    Relation.TransGen (Step P host) ⟨s, f, vals stk.reverse ++ .plain (.block bt B) :: rest⟩
      ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ := by
  have enter := step_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_block har) rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse rest
    (Steps.label nr [] hrun)
  rw [stack_after]
  exact Relation.TransGen.head' enter (inner.trans (exit_blockVals he hm hvs hnr hnorm))

/-- **A block whose body hands on values** (falls through or branches to it). -/
theorem wp_block_vals {rest : List Admin} {Q : Post H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WP P host s f (vals (stk.take np).reverse ++ expression B) (Match (s₁, f₁, fl)))
    (hvs : fl.blockVals = some vs) (hnr : nr ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = nr)
    (hk : WP P host s₁ f₁ (vals (vs.take nr ++ stk.drop np).reverse ++ rest) Q) :
    WP P host s f (vals stk.reverse ++ .plain (.block bt B) :: rest) Q := by
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hb
  have enter := steps_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_block har) rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse rest
    (Steps.label nr [] hrun)
  have hk' : WP P host s₁ f₁ (vals ((stk.drop np).reverse ++ (vs.take nr).reverse) ++ rest) Q := by
    rw [← stack_after]
    exact hk
  exact WP.steps (enter.trans (inner.trans (exit_blockVals he hm hvs hnr hnorm))) hk'

/-- **A block whose body branches to an outer label, returns or traps.** -/
theorem wp_block_abrupt {rest : List Admin} {fl' : Binaryen.Flow}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WP P host s f (vals (stk.take np).reverse ++ expression B) (Match (s₁, f₁, fl)))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    WP P host s f (vals stk.reverse ++ .plain (.block bt B) :: rest) (Match (s₁, f₁, fl')) := by
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hb
  have enter := steps_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_block har) rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse rest
    (Steps.label nr [] hrun)
  exact WP.steps (enter.trans inner) (exit_abrupt he hm hfl _ rest)

/-- **A loop whose body falls through**, as a run to its continuation. -/
theorem tg_loop_normal {rest : List Admin} {c' : List Admin} {o : Outcome}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : Steps P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ ⟨s₁, f₁, c'⟩)
    (he : o.Ends c') (hm : FlowMatch (.normal vs) o) (hlen : vs.length = nr) :
    Relation.TransGen (Step P host) ⟨s, f, vals stk.reverse ++ .plain (.loop bt B) :: rest⟩
      ⟨s₁, f₁, vals (vs.take nr ++ stk.drop np).reverse ++ rest⟩ := by
  have enter := step_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_loop har) rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse rest
    (Steps.label np [.loop bt B] hrun)
  have htake : vs.take nr = vs := List.take_of_length_le hlen.le
  have e : vals (vs.take nr ++ stk.drop np).reverse ++ rest =
      vals ((stk.drop np).reverse ++ vs.reverse) ++ rest := by
    rw [htake]
    simp
  rw [e]
  exact Relation.TransGen.head' enter (inner.trans (exit_normal he hm _ rest))

/-- **A loop whose body branches back to it**, as a run to the next iteration. -/
theorem tg_loop_back {rest : List Admin} {c' : List Admin} {o : Outcome}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hrun : Steps P host ⟨s, f, vals (stk.take np).reverse ++ expression B⟩ ⟨s₁, f₁, c'⟩)
    (he : o.Ends c') (hm : FlowMatch (.brk 0 vs) o) (hnp : np ≤ vs.length) :
    Relation.TransGen (Step P host) ⟨s, f, vals stk.reverse ++ .plain (.loop bt B) :: rest⟩
      ⟨s₁, f₁, vals (vs.take np ++ stk.drop np).reverse ++ .plain (.loop bt B) :: rest⟩ := by
  have enter := step_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_loop har) rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse rest
    (Steps.label np [.loop bt B] hrun)
  have e : vals (vs.take np ++ stk.drop np).reverse ++ .plain (.loop bt B) :: rest =
      vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++ expression [.loop bt B] ++ rest := by
    simp [expression]
  rw [e]
  exact Relation.TransGen.head' enter (inner.trans (exit_br0 he hm hnp _ rest))

/-- **A loop whose body falls through.** -/
theorem wp_loop_normal {rest : List Admin} {Q : Post H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WP P host s f (vals (stk.take np).reverse ++ expression B) (Match (s₁, f₁, .normal vs)))
    (hlen : vs.length = nr)
    (hk : WP P host s₁ f₁ (vals (vs.take nr ++ stk.drop np).reverse ++ rest) Q) :
    WP P host s f (vals stk.reverse ++ .plain (.loop bt B) :: rest) Q := by
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hb
  have enter := steps_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_loop har) rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse rest
    (Steps.label np [.loop bt B] hrun)
  have htake : vs.take nr = vs := List.take_of_length_le hlen.le
  have hk' : WP P host s₁ f₁ (vals ((stk.drop np).reverse ++ vs.reverse) ++ rest) Q := by
    rw [← htake, ← stack_after]
    exact hk
  exact WP.steps (enter.trans inner) (WP.steps (exit_normal he hm _ rest) hk')

/-- **A loop whose body branches back to it.** -/
theorem wp_loop_back {rest : List Admin} {Q : Post H}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WP P host s f (vals (stk.take np).reverse ++ expression B) (Match (s₁, f₁, .brk 0 vs)))
    (hnp : np ≤ vs.length)
    (hk : WP P host s₁ f₁ (vals (vs.take np ++ stk.drop np).reverse ++ .plain (.loop bt B) :: rest)
      Q) :
    WP P host s f (vals stk.reverse ++ .plain (.loop bt B) :: rest) Q := by
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hb
  have enter := steps_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_loop har) rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse rest
    (Steps.label np [.loop bt B] hrun)
  have hk' : WP P host s₁ f₁ (vals ((stk.drop np).reverse ++ (vs.take np).reverse) ++
      expression [.loop bt B] ++ rest) Q := by
    rw [← stack_after (nr := np)]
    simpa [expression] using hk
  exact WP.steps (enter.trans inner) (WP.steps (exit_br0 he hm hnp _ rest) hk')

/-- **A loop whose body branches to an outer label, returns or traps.** -/
theorem wp_loop_abrupt {rest : List Admin} {fl' : Binaryen.Flow}
    (har : Binaryen.arity f bt = some (np, nr)) (hp : np ≤ stk.length)
    (hb : WP P host s f (vals (stk.take np).reverse ++ expression B) (Match (s₁, f₁, fl)))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    WP P host s f (vals stk.reverse ++ .plain (.loop bt B) :: rest) (Match (s₁, f₁, fl')) := by
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hb
  have enter := steps_enter (P := P) (host := host) (s := s) (f := f) (B := B) hp
    (step_loop har) rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse rest
    (Steps.label np [.loop bt B] hrun)
  exact WP.steps (enter.trans inner) (exit_abrupt he hm hfl _ rest)

end Blocks

/-! ## Direct calls -/

section Calls

variable {s s₂ : Store H} {f f₂ : Frame} {stk vs : List Val} {x : FuncIdx} {a : Nat}
  {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType} {fl : Binaryen.Flow}

/-- The Core function type of a native one. -/
theorem expand_of_funcType {d : Validation.DefType} (h : Validation.DefType.funcType? d = some (ps, rs)) :
    ∃ ps' rs', Validation.Expand d (.func ps' rs') ∧ ps'.length = ps.length ∧ rs'.length = rs.length := by
  unfold Validation.DefType.funcType? at h
  split at h
  · rename_i ps' rs' he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ps', rs', Validation.Expand.iff.mpr he, by simp [Validation.Ty.length], by simp [Validation.Ty.length]⟩
  · cases h

/-- The function a native call finds, as Core sees it. -/
theorem func?_inv (hfi : s.func? f x = some (a, fi)) :
    f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi := by
  simp only [Store.func?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hfi
  obtain ⟨a', ha, fi', hfi', h⟩ := hfi
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨ha, hfi'⟩

/-- The callee frame of a call. -/
abbrev calleeFrame (fi : FuncInst H) (fn : Func) (stk : List Val) (n : Nat) : Frame :=
  Frame.forCall fi.module (stk.take n).reverse fn.locals

/-- **Entering a call**: the callee body runs in its label and frame, below the values the
call did not consume. -/
theorem steps_call_enter (hfi : s.func? f x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hp : ps.length ≤ stk.length)
    (rest : List Admin) :
    Relation.TransGen (Step P host) ⟨s, f, vals stk.reverse ++ .plain (.call x) :: rest⟩
      ⟨s, f, vals (stk.drop ps.length).reverse ++ [.frame rs.length (calleeFrame fi fn stk ps.length)
        [.label rs.length [] (expression fn.body)]] ++ rest⟩ := by
  obtain ⟨hx, hf⟩ := func?_inv hfi
  obtain ⟨ps', rs', he, hpl, hrl⟩ := expand_of_funcType hty
  have hlen : (stk.take ps.length).reverse.length = ps'.length := by
    simp only [List.length_reverse, List.length_take, hpl]
    omega
  have st1 : Step P host ⟨s, f, vals stk.reverse ++ [.plain (.call x)] ++ rest⟩
      ⟨s, f, vals stk.reverse ++ [.ref (.func a), .callRefType fi.type] ++ rest⟩ :=
    Step.ctx stk.reverse rest (Step.call hx hf)
  have e : vals stk.reverse ++ [.ref (.func a), .callRefType fi.type] ++ rest =
      vals (stk.drop ps.length).reverse ++
        (vals (stk.take ps.length).reverse ++ [.ref (.func a), .callRefType fi.type]) ++ rest := by
    rw [rev_take_drop stk ps.length]
    simp
  have st2 : Step P host ⟨s, f, vals (stk.drop ps.length).reverse ++
        (vals (stk.take ps.length).reverse ++ [.ref (.func a), .callRefType fi.type]) ++ rest⟩
      ⟨s, f, vals (stk.drop ps.length).reverse ++ [.frame rs'.length (calleeFrame fi fn stk ps.length)
        [.label rs'.length [] (expression fn.body)]] ++ rest⟩ :=
    Step.ctx _ rest (Step.callRefFunc trivial hf he hlen hcode)
  have e0 : vals stk.reverse ++ .plain (.call x) :: rest =
      vals stk.reverse ++ [.plain (.call x)] ++ rest := by simp
  rw [← hrl, e0]
  refine (Relation.TransGen.single st1).tail ?_
  rw [e]
  exact st2

/-- The postcondition of a callee body that hands back `vs`. -/
def callPost (s₂ : Store H) (vs : List Val) (n : Nat) : Store H → List Val → Prop :=
  fun s' res => s' = s₂ ∧ res = (vs.take n).reverse

/-- A matched callee outcome satisfies the function postcondition. -/
theorem funcPost_of_match {o : Outcome} {F : Frame} {n : Nat} (hm : FlowMatch fl o)
    (hvs : fl.retVals = some vs) (hn : n ≤ vs.length) (hnorm : ∀ ws, fl = .normal ws → ws.length = n) :
    funcPost P host n (callPost s₂ vs n) s₂ F o := by
  have hlen : (vs.take n).reverse.length = n := by
    simp only [List.length_reverse, List.length_take]
    omega
  rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | _ <;> simp only [Binaryen.Flow.retVals,
    reduceCtorEq, Option.some.injEq] at hvs
  · subst ws
    rcases o with ws' | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
    subst hm
    have htake : vs.take n = vs := List.take_of_length_le (hnorm vs rfl).le
    exact ⟨by simpa using hnorm vs rfl, rfl, by rw [htake]⟩
  · subst ws
    rcases o with _ | ⟨l, ws'⟩ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
    obtain ⟨rfl, junk, rfl⟩ := hm
    exact ⟨junk ++ (vs.drop n).reverse, (vs.take n).reverse, rev_split junk vs n, hlen, rfl, rfl⟩
  · subst ws
    rcases o with _ | _ | ws' | _ | _ | _ <;> simp only [FlowMatch] at hm
    obtain ⟨junk, rfl⟩ := hm
    exact ⟨junk ++ (vs.drop n).reverse, (vs.take n).reverse, rev_split junk vs n, hlen, rfl, rfl⟩

/-- **A call whose callee hands back values**, as a run to its continuation. -/
theorem tg_call_ok {rest c' : List Admin} {o : Outcome} (hfi : s.func? f x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : ps.length ≤ stk.length)
    (hrun : Steps P host ⟨s, calleeFrame fi fn stk ps.length, expression fn.body⟩ ⟨s₂, f₂, c'⟩)
    (he : o.Ends c') (hm : FlowMatch fl o)
    (hvs : fl.retVals = some vs) (hrs : rs.length ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length) :
    Relation.TransGen (Step P host) ⟨s, f, vals stk.reverse ++ .plain (.call x) :: rest⟩
      ⟨s₂, f, vals (vs.take rs.length ++ stk.drop ps.length).reverse ++ rest⟩ := by
  have enter := steps_call_enter (P := P) (host := host) hfi hcode hty hp rest
  have inner := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest
    (Steps.frame (f := f) rs.length (Steps.label rs.length [] hrun))
  obtain ⟨s', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) he
    (funcPost_of_match (s₂ := s₂) (F := f₂) hm hvs hrs hnorm)
  obtain ⟨hs', hres⟩ := hK
  subst s' res
  have exit := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest hret
  have e : vals (vs.take rs.length ++ stk.drop ps.length).reverse ++ rest =
      vals (stk.drop ps.length).reverse ++ vals (vs.take rs.length).reverse ++ rest := by simp
  rw [e]
  exact enter.trans_left (inner.trans exit)

/-- **A call whose callee hands back values.** -/
theorem wp_call_ok {rest : List Admin} {Q : Post H} (hfi : s.func? f x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : ps.length ≤ stk.length)
    (hb : WP P host s (calleeFrame fi fn stk ps.length)
      (vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body)))
      (Match (s₂, f₂, fl)))
    (hvs : fl.retVals = some vs) (hrs : rs.length ≤ vs.length)
    (hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length)
    (hk : WP P host s₂ f (vals (vs.take rs.length ++ stk.drop ps.length).reverse ++ rest) Q) :
    WP P host s f (vals stk.reverse ++ .plain (.call x) :: rest) Q := by
  rw [Binaryen.lowerList_liftInstrs] at hb
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hb
  have enter := (steps_call_enter (P := P) (host := host) hfi hcode hty hp rest).to_reflTransGen
  have inner := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest
    (Steps.frame (f := f) rs.length (Steps.label rs.length [] (by simpa [vals] using hrun)))
  obtain ⟨s', res, hret, hK⟩ := frame_ends (P := P) (host := host) (f := f) he
    (funcPost_of_match (s₂ := s₂) (F := f₂) hm hvs hrs hnorm)
  obtain ⟨hs', hres⟩ := hK
  subst s' res
  have exit := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest hret
  have hk' : WP P host s₂ f (vals (stk.drop ps.length).reverse ++ vals (vs.take rs.length).reverse ++
      rest) Q := by
    rw [← vals_append, ← stack_after]
    exact hk
  exact WP.steps (enter.trans (inner.trans exit)) hk'

/-- **A call whose callee traps.** -/
theorem wp_call_trap {rest : List Admin} (hfi : s.func? f x = some (a, fi))
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hp : ps.length ≤ stk.length)
    (hb : WP P host s (calleeFrame fi fn stk ps.length)
      (vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body)))
      (Match (s₂, f₂, .trap))) :
    WP P host s f (vals stk.reverse ++ .plain (.call x) :: rest) (Match (s₂, f, .trap)) := by
  rw [Binaryen.lowerList_liftInstrs] at hb
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp hb
  have hc : c' = [.trap] := by
    rcases o with _ | _ | _ | _ | _ | _ <;> simp only [FlowMatch] at hm
    exact he
  subst hc
  have enter := (steps_call_enter (P := P) (host := host) hfi hcode hty hp rest).to_reflTransGen
  have inner := Steps.ctx (P := P) (host := host) (stk.drop ps.length).reverse rest
    (Steps.frame (f := f) rs.length (Steps.label rs.length [] (by simpa [vals] using hrun)))
  have out : Steps P host ⟨s₂, f, [.frame rs.length f₂ [.label rs.length [] [.trap]]]⟩
      ⟨s₂, f, [.trap]⟩ :=
    (Relation.ReflTransGen.single (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame
  have hw : WP P host s₂ f (vals (stk.drop ps.length).reverse ++ .trap :: rest)
      (Match (s₂, f, .trap)) := wp_trap ⟨rfl, rfl, trivial⟩
  exact WP.steps (enter.trans (inner.trans (Steps.ctx _ rest out))) (by simpa using hw)

end Calls

/-! ## The simulation -/

/-- The statement of `wp_of_eval` for one evaluation. -/
def CoreGood (P : Numerics.Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (stk : List Val) (es : List Binaryen.BExpr) (r : Store H × Frame × Binaryen.Flow) : Prop :=
  ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChk s.funcs →
    chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    WP P host s f (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)) (Match r)

section Cases

variable {s s₁ s₂ : Store H} {f f₁ f₂ : Frame} {stk stk₁ stk₂ vs : List Val}
  {es args body : List Binaryen.BExpr} {i : Instr} {fl : Binaryen.Flow}
  {r : Store H × Frame × Binaryen.Flow}

/-- The code of an operator tree followed by more trees. -/
theorem code_op (stk : List Val) (i : Instr) (args es : List Binaryen.BExpr) :
    vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.op i args :: es)) =
      (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)) ++
        (.plain i :: expression (Binaryen.BExpr.lowerList es)) := by
  simp [expression]

/-- The code of a structured tree followed by more trees. -/
theorem code_block (stk : List Val) (bt : BlockType) (es : List Binaryen.BExpr) :
    vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.block bt body :: es)) =
      vals stk.reverse ++ .plain (.block bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es) := by
  simp [expression, Binaryen.BExpr.lower]

theorem code_loop (stk : List Val) (bt : BlockType) (es : List Binaryen.BExpr) :
    vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.loop bt body :: es)) =
      vals stk.reverse ++ .plain (.loop bt (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es) := by
  simp [expression, Binaryen.BExpr.lower]

theorem code_if (stk : List Val) (bt : BlockType) (c t el es : List Binaryen.BExpr) :
    vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.if_ bt c t el :: es)) =
      (vals stk.reverse ++ expression (Binaryen.BExpr.lowerList c)) ++
        (.plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) ::
          expression (Binaryen.BExpr.lowerList es)) := by
  simp [expression, Binaryen.BExpr.lower]

/-- The check of the code after a block, from the values it hands on. -/
theorem chk_after {labels : List Nat} {ret np nr : Nat} {out : Option Nat}
    (inv1 : EvalInv s f (s₁, f₁, fl)) (hnp : np ≤ stk.length) (hnr : nr ≤ vs.length)
    (h2 : chk s.funcs f.module f.locals.length ret labels (some (stk.length - np + nr)) es =
      some out) :
    chk s₁.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take nr ++ stk.drop np).length) es = some out := by
  have hlen : (vs.take nr ++ stk.drop np).length = stk.length - np + nr := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  rw [chk_inv inv1, hlen]
  exact h2

/-- What the arity check says about a checked body run. -/
theorem body_facts {labels : List Nat} {ret n₀ nr : Nat} {stk₀ : List Val}
    (hS : StoreChk s.funcs) (hbody : Binaryen.Eval s f stk₀ body (s₁, f₁, fl))
    (hb : endsAt (chk s.funcs f.module f.locals.length ret labels (some n₀) body) nr = true)
    (hlen : stk₀.length = n₀) :
    ∃ ob, (ob = none ∨ ob = some nr) ∧
      chk s.funcs f.module f.locals.length ret labels (some stk₀.length) body = some ob ∧
      FlowOk labels ret ob fl ∧ EvalInv s f (s₁, f₁, fl) := by
  obtain ⟨ob, hb', hob⟩ := endsAt_eq hb
  have hbc : chk s.funcs f.module f.locals.length ret labels (some stk₀.length) body = some ob :=
    hlen ▸ hb'
  obtain ⟨hok, inv1⟩ := flowOk_of_eval hbody hS hbc
  exact ⟨ob, hob, hbc, hok, inv1⟩

theorem core_nil : CoreGood P host s f stk [] (s, f, .normal stk) := by
  intro labels ret out _ _
  simpa using (wp_vals (P := P) (host := host) (s := s) (f := f) (vs := stk.reverse)
    (Q := Match (s, f, .normal stk)) ⟨rfl, rfl, rfl⟩)

theorem core_argsAbort (iha : CoreGood P host s f stk args (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
    CoreGood P host s f stk (.op i args :: es) (s₁, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_cons.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_op h1
  rw [code_op]
  exact wp_append_abrupt' (iha hS ha) hfl

theorem core_opOk (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGood P host s f stk args (s₁, f₁, .normal stk₁)) (hi : ∀ x, i ≠ .call x)
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂))
    (ihk : CoreGood P host s₂ f₂ stk₂ es r) : CoreGood P host s f stk (.op i args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨o, h1, h2⟩ := chk_cons.mp hc
  obtain ⟨hf, inv1⟩ := arity_args hS (flowOk_of_eval hargs) h1
  obtain ⟨oa, ha, -⟩ := chk1_op h1
  obtain ⟨ho, inv2⟩ := flat_normal hflat hf
  have inv12 : EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
  have h2' : chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
      some out := by
    rw [chk_inv inv12, ← ho]
    exact h2
  have st := steps_flat_normal (P := P) (host := host) hi hf hflat
    (expression (Binaryen.BExpr.lowerList es))
  rw [code_op]
  exact wp_append_normal (iha hS ha) (WP.steps st (ihk (storeChk_inv inv12 hS) h2'))

theorem core_opStop (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGood P host s f stk args (s₁, f₁, .normal stk₁))
    (hflat : Binaryen.evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hfl : ¬ fl.IsNormal) :
    CoreGood P host s f stk (.op i args :: es) (s₂, f₂, fl) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_cons.mp hc
  obtain ⟨hf, -⟩ := arity_args hS (flowOk_of_eval hargs) h1
  obtain ⟨oa, ha, -⟩ := chk1_op h1
  rw [code_op]
  exact wp_append_normal (iha hS ha) (wp_flat_abrupt hf hflat hfl _)

/-! ### Calls -/

section CallCases

variable {x : FuncIdx} {a : Nat} {fi : FuncInst H} {fn : Func} {ps rs : List Validation.CValType}

/-- What the arity check says about a checked call before and after its callee. -/
theorem call_facts {labels : List Nat} {ret : Nat} {out : Option Nat} (hS : StoreChk s.funcs)
    (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : Binaryen.Eval s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, fl))
    (hc : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op (.call x) args :: es) = some out) :
    ∃ oa ob, chk s.funcs f.module f.locals.length ret labels (some stk.length) args = some oa ∧
      chk s₁.funcs (calleeFrame fi fn stk₁ ps.length).module
        (calleeFrame fi fn stk₁ ps.length).locals.length rs.length [rs.length]
        (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob ∧
      (ob = none ∨ ob = some rs.length) ∧ FlowOk [rs.length] rs.length ob fl ∧
      EvalInv s f (s₁, f₁, .normal stk₁) ∧ s₂.funcs = s₁.funcs ∧ ps.length ≤ stk₁.length ∧
      chk s.funcs f.module f.locals.length ret labels
        (some (stk₁.length - ps.length + rs.length)) es = some out := by
  obtain ⟨inv1, hp, h2⟩ := arity_call_pre hS (flowOk_of_eval hargs) hfi hty hc
  obtain ⟨o, h1, -⟩ := chk_cons.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_op h1
  have hS1 : StoreChk s₁.funcs := storeChk_inv inv1 hS
  obtain ⟨ob, hob, hb'⟩ := callee_chk hS1 hfi hcode hty hp
  obtain ⟨hok, hinvb⟩ := flowOk_of_eval hbody hS1 hb'
  exact ⟨oa, ob, ha, hb', hob, hok, inv1, hinvb.1, hp, h2⟩

theorem core_callOk (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGood P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : Binaryen.Eval s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, fl))
    (ihb : CoreGood P host s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, fl))
    (hvs : fl.retVals = some vs)
    (ihk : CoreGood P host s₂ f₁ (vs.take rs.length ++ stk₁.drop ps.length) es r) :
    CoreGood P host s f stk (.op (.call x) args :: es) r := by
  intro labels ret out hS hc
  obtain ⟨oa, ob, ha, hb', hob, hok, inv1, hfuncs, hp, h2⟩ :=
    call_facts hS hargs hfi hcode hty hbody hc
  have hrs : rs.length ≤ vs.length := retVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = rs.length := by
    rintro ws rfl
    exact length_of_ends hok hob
  have inv2 : EvalInv s f (s₂, f₁, .normal (vs.take rs.length ++ stk₁.drop ps.length)) :=
    ⟨hfuncs.trans inv1.1, inv1.2.1, inv1.2.2⟩
  have hlen : (vs.take rs.length ++ stk₁.drop ps.length).length =
      stk₁.length - ps.length + rs.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have h2' : chk s₂.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take rs.length ++ stk₁.drop ps.length).length) es = some out := by
    rw [chk_inv inv2, hlen]
    exact h2
  have hk := ihk (storeChk_inv inv2 hS) h2'
  have hwb := ihb (storeChk_inv inv1 hS) hb'
  rw [code_op]
  exact wp_append_normal (iha hS ha) (wp_call_ok hfi hcode hty hp hwb hvs hrs hnorm hk)

theorem core_callTrap (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (iha : CoreGood P host s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : Binaryen.Eval s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, .trap))
    (ihb : CoreGood P host s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, .trap)) :
    CoreGood P host s f stk (.op (.call x) args :: es) (s₂, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨oa, ob, ha, hb', -, -, inv1, -, hp, -⟩ := call_facts hS hargs hfi hcode hty hbody hc
  have hwb := ihb (storeChk_inv inv1 hS) hb'
  rw [code_op]
  exact wp_append_normal (iha hS ha) (wp_call_trap hfi hcode hty hp hwb)

theorem core_callThrow {t : Nat} (hargs : Binaryen.Eval s f stk args (s₁, f₁, .normal stk₁))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : Binaryen.Eval s₁ (calleeFrame fi fn stk₁ ps.length) [] (Binaryen.liftInstrs fn.body)
      (s₂, f₂, .throw t)) :
    CoreGood P host s f stk (.op (.call x) args :: es) (s₂, f₁, .throw t) := by
  intro labels ret out hS hc
  obtain ⟨_, _, _, _, _, hok, _⟩ := call_facts hS hargs hfi hcode hty hbody hc
  exact absurd hok id

end CallCases

/-! ### Blocks, loops and conditionals -/

section BlockCases

variable {bt : BlockType} {np nr : Nat}

theorem core_blockOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : Binaryen.Eval s f (stk.take np) body (s₁, f₁, fl))
    (ihb : CoreGood P host s f (stk.take np) body (s₁, f₁, fl)) (hvs : fl.blockVals = some vs)
    (ihk : CoreGood P host s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    CoreGood P host s f stk (.block bt body :: es) r := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_block_pre har hc
  obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  have hk := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hnr h2)
  rw [code_block]
  exact wp_block_vals har hp (ihb hS hbc) hvs hnr hnorm hk

theorem core_blockAbrupt {fl' : Binaryen.Flow} (har : Binaryen.arity f bt = some (np, nr))
    (hbody : Binaryen.Eval s f (stk.take np) body (s₁, f₁, fl))
    (ihb : CoreGood P host s f (stk.take np) body (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreGood P host s f stk (.block bt body :: es) (s₁, f₁, fl') := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_block_pre har hc
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  rw [code_block]
  exact wp_block_abrupt har hp (ihb hS hbc) hfl

theorem core_loopOk (har : Binaryen.arity f bt = some (np, nr))
    (hbody : Binaryen.Eval s f (stk.take np) body (s₁, f₁, .normal vs))
    (ihb : CoreGood P host s f (stk.take np) body (s₁, f₁, .normal vs))
    (ihk : CoreGood P host s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    CoreGood P host s f stk (.loop bt body :: es) r := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, h2⟩ := arity_loop_pre har hc
  obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  have hlen : vs.length = nr := length_of_ends hok hob
  have hk := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hlen.ge h2)
  rw [code_loop]
  exact wp_loop_normal har hp (ihb hS hbc) hlen hk

theorem core_loopBack (har : Binaryen.arity f bt = some (np, nr))
    (hbody : Binaryen.Eval s f (stk.take np) body (s₁, f₁, .brk 0 vs))
    (ihb : CoreGood P host s f (stk.take np) body (s₁, f₁, .brk 0 vs))
    (ihk : CoreGood P host s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) r) :
    CoreGood P host s f stk (.loop bt body :: es) r := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  obtain ⟨m, hm, hle⟩ := hok
  have hnp : np ≤ vs.length := by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    exact hm ▸ hle
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  have hc' : chk s₁.funcs f₁.module f₁.locals.length ret labels
      (some (vs.take np ++ stk.drop np).length) (.loop bt body :: es) = some out := by
    rw [chk_inv inv1, hlen]
    exact hc
  have hk := ihk (storeChk_inv inv1 hS) hc'
  rw [code_loop] at hk ⊢
  exact wp_loop_back har hp (ihb hS hbc) hnp hk

theorem core_loopAbrupt {fl' : Binaryen.Flow} (har : Binaryen.arity f bt = some (np, nr))
    (hbody : Binaryen.Eval s f (stk.take np) body (s₁, f₁, fl))
    (ihb : CoreGood P host s f (stk.take np) body (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreGood P host s f stk (.loop bt body :: es) (s₁, f₁, fl') := by
  intro labels ret out hS hc
  obtain ⟨hp, hb, -⟩ := arity_loop_pre har hc
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  rw [code_loop]
  exact wp_loop_abrupt har hp (ihb hS hbc) hfl

/-- An `if` runs the chosen arm as a block. -/
theorem wp_if_arm {cv : Val} {b : Bool} {t el : List Binaryen.BExpr} {rest : List Admin}
    {Q : Post H} (hb : Binaryen.truthy cv = some b)
    (h : WP P host s f (vals stk.reverse ++
      .plain (.block bt (Binaryen.BExpr.lowerList (if b then t else el))) :: rest) Q) :
    WP P host s f (vals (cv :: stk).reverse ++
      .plain (.if_ bt (Binaryen.BExpr.lowerList t) (Binaryen.BExpr.lowerList el)) :: rest) Q := by
  obtain ⟨c₀, rfl, rfl⟩ := truthy_eq hb
  have e : vals (Val.i32 c₀ :: stk).reverse = vals (stk.reverse ++ [Val.i32 c₀]) := by simp
  rw [e]
  by_cases h0 : c₀ = 0
  · subst h0
    exact wp_if_false_cons (by simpa using h)
  · have h1 : (c₀ != 0) = true := by simpa using h0
    simp only [h1, ↓reduceIte] at h
    exact wp_if_true_cons h0 h

/-- What the arity check says about a checked `if` arm run. -/
theorem if_facts {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {labels : List Nat}
    {ret : Nat} {out : Option Nat} (hS : StoreChk s.funcs)
    (hcond : Binaryen.Eval s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (har : Binaryen.arity f₁ bt = some (np, nr))
    (harm : Binaryen.Eval s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (hc : chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.if_ bt c t el :: es) = some out) :
    ∃ oc ob, chk s.funcs f.module f.locals.length ret labels (some stk.length) c = some oc ∧
      chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels) (some (stk₁.take np).length)
        (if b then t else el) = some ob ∧ (ob = none ∨ ob = some nr) ∧
      FlowOk (nr :: labels) ret ob fl ∧ EvalInv s f (s₁, f₁, .normal (cv :: stk₁)) ∧
      EvalInv s₁ f₁ (s₂, f₂, fl) ∧ np ≤ stk₁.length ∧
      chk s₁.funcs f₁.module f₁.locals.length ret labels (some (stk₁.length - np + nr)) es =
        some out := by
  obtain ⟨inv1, hp, hbarm, h2⟩ := arity_if_pre (b := b) hS (flowOk_of_eval hcond) har hc
  rw [← chk_inv inv1] at hbarm h2
  obtain ⟨ob, hob, hbc, hok, inv2⟩ :=
    body_facts (storeChk_inv inv1 hS) harm hbarm (take_length_of_le hp)
  obtain ⟨o, h1, -⟩ := chk_cons.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_if h1
  exact ⟨oc, ob, hco, hbc, hob, hok, inv1, inv2, hp, h2⟩

theorem core_ifOk {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool}
    (hcond : Binaryen.Eval s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (ihc : CoreGood P host s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (harm : Binaryen.Eval s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (iharm : CoreGood P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (hvs : fl.blockVals = some vs) (ihk : CoreGood P host s₂ f₂ (vs.take nr ++ stk₁.drop np) es r) :
    CoreGood P host s f stk (.if_ bt c t el :: es) r := by
  intro labels ret out hS hc
  obtain ⟨oc, ob, hco, hbc, hob, hok, inv1, inv2, hp, h2⟩ := if_facts hS hcond har harm hc
  have hS1 : StoreChk s₁.funcs := storeChk_inv inv1 hS
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  have hk := ihk (storeChk_inv inv2 hS1) (chk_after inv2 hp hnr h2)
  have hwb := wp_block_vals har hp (iharm hS1 hbc) hvs hnr hnorm hk
  rw [code_if]
  exact wp_append_normal (ihc hS hco) (wp_if_arm hb hwb)

theorem core_ifAbrupt {c t el : List Binaryen.BExpr} {cv : Val} {b : Bool} {fl' : Binaryen.Flow}
    (hcond : Binaryen.Eval s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (ihc : CoreGood P host s f stk c (s₁, f₁, .normal (cv :: stk₁)))
    (hb : Binaryen.truthy cv = some b) (har : Binaryen.arity f₁ bt = some (np, nr))
    (harm : Binaryen.Eval s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (iharm : CoreGood P host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl)) :
    CoreGood P host s f stk (.if_ bt c t el :: es) (s₂, f₂, fl') := by
  intro labels ret out hS hc
  obtain ⟨oc, ob, hco, hbc, -, -, inv1, -, hp, -⟩ := if_facts hS hcond har harm hc
  have hwb := wp_block_abrupt (rest := expression (Binaryen.BExpr.lowerList es)) har hp
    (iharm (storeChk_inv inv1 hS) hbc) hfl
  rw [code_if]
  exact wp_append_normal (ihc hS hco) (wp_if_arm hb hwb)

theorem core_ifAbort {c t el : List Binaryen.BExpr}
    (ihc : CoreGood P host s f stk c (s₁, f₁, fl)) (hfl : ¬ fl.IsNormal) :
    CoreGood P host s f stk (.if_ bt c t el :: es) (s₁, f₁, fl) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_cons.mp hc
  obtain ⟨oc, hco, -⟩ := chk1_if h1
  rw [code_if]
  exact wp_append_abrupt' (ihc hS hco) hfl

end BlockCases

end Cases

/-- **Native evaluation of checked trees is a Core 3.0 run**, every profile and host. -/
theorem wp_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store H × Frame × Binaryen.Flow} (h : Binaryen.Eval s f stk es r) :
    CoreGood P host s f stk es r := by
  induction h with
  | nil => exact core_nil
  | argsAbort _ hfl iha => exact core_argsAbort iha hfl
  | callOk hargs hfi hcode hty hbody hvs _ iha ihb ihk =>
    exact core_callOk hargs iha hfi hcode hty hbody ihb hvs ihk
  | callTrap hargs hfi hcode hty hbody iha ihb =>
    exact core_callTrap hargs iha hfi hcode hty hbody ihb
  | callThrow hargs hfi hcode hty hbody => exact core_callThrow hargs hfi hcode hty hbody
  | opOk hi hargs hflat _ iha ihk => exact core_opOk hargs iha hi hflat ihk
  | opStop _ hargs hflat hfl iha => exact core_opStop hargs iha hflat hfl
  | blockOk har hbody hvs _ ihb ihk => exact core_blockOk har hbody ihb hvs ihk
  | blockBrk har hbody ihb => exact core_blockAbrupt har hbody ihb (.inl ⟨_, _, rfl, rfl⟩)
  | blockEsc har hbody hfl ihb => exact core_blockAbrupt har hbody ihb (.inr ⟨hfl, rfl⟩)
  | loopOk har hbody _ ihb ihk => exact core_loopOk har hbody ihb ihk
  | loopBack har hbody _ ihb ihk => exact core_loopBack har hbody ihb ihk
  | loopBrk har hbody ihb => exact core_loopAbrupt har hbody ihb (.inl ⟨_, _, rfl, rfl⟩)
  | loopEsc har hbody hfl ihb => exact core_loopAbrupt har hbody ihb (.inr ⟨hfl, rfl⟩)
  | ifOk hcond hb har harm hvs _ ihc iharm ihk =>
    exact core_ifOk hcond ihc hb har harm iharm hvs ihk
  | ifBrk hcond hb har harm ihc iharm =>
    exact core_ifAbrupt hcond ihc hb har harm iharm (.inl ⟨_, _, rfl, rfl⟩)
  | ifEsc hcond hb har harm hfl ihc iharm =>
    exact core_ifAbrupt hcond ihc hb har harm iharm (.inr ⟨hfl, rfl⟩)
  | ifAbort _ hfl ihc => exact core_ifAbort ihc hfl

end Silmaril.Wasm.Interp
