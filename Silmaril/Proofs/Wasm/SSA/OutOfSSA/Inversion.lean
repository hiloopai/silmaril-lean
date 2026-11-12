module

public import Silmaril.Proofs.Wasm.SSA.OutOfSSA.Func
public import Silmaril.Wasm.SSA.Fragment.Thms

/-!
# Out of SSA: inverting the decompiled code

Inversion lemmas for the fragment derivations of the shapes the decompiler
emits, static terms always evaluate, and operators passing `opSafe` cannot
trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.OutOfSSA

open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (extend Env)
open Silmaril.Wasm (IntType)

/-! ## Static terms evaluate -/

theorem staticLoc_eval {env : Env WVal} {ls : List WVal} {vars : List VLoc}
    (hv : VarsOK ls vars env) :
    ∀ (t : Tm Prim) {V : VLoc}, staticLoc vars t = some V →
      ∃ v, Silmaril.Isotope.LambdaSSA.Semantics.Tm.Eval instr env t () v () ∧ readL ls V = some v
  | .var i, V, hs => ⟨env i, .var, hv i V hs⟩
  | .unit, V, hs => by simp [staticLoc] at hs; subst hs; exact ⟨.unit, .unit, rfl⟩
  | .pair a b, V, hs => by
      simp only [staticLoc, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨A, hA, B, hB, rfl⟩ := hs
      obtain ⟨va, ha, hra⟩ := staticLoc_eval hv a hA
      obtain ⟨vb, hb, hrb⟩ := staticLoc_eval hv b hB
      exact ⟨.pair va vb, .pair ha hb, readL_pair.2 ⟨_, _, hra, hrb, rfl⟩⟩
  | .op f a, V, hs => by
      match f, a, hs with
      | .op (.const w), .unit, hs =>
          simp [staticLoc] at hs; subst hs
          exact ⟨.atom w, .op .unit (by simp [instr, Prim.run, decodeList, Op.eval]), rfl⟩
  | .let₁ .., _, hs | .let₂ .., _, hs | .inl _, _, hs | .inr _, _, hs | .case .., _, hs
  | .abort _, _, hs => by simp [staticLoc] at hs

/-! ## Inversions -/

theorem exec_op_inv {ls : List WVal} {o : Op} {es : List Expr} {ws : List WVal}
    {out : Out (Option WVal)} (h : Exec ls (.op o es) out) (ha : Args ls es (.ok ls ws)) :
    (∃ w, o.eval ws = some (.val w) ∧ out = .ok ls (some w)) ∨
      (o.eval ws = some .trap ∧ out = .trap) := by
  cases h with
  | op ha' hev =>
      cases Silmaril.Wasm.SSA.Args.det ha' ha
      exact .inl ⟨_, hev, rfl⟩
  | op_trap ha' hev =>
      cases Silmaril.Wasm.SSA.Args.det ha' ha
      exact .inr ⟨hev, rfl⟩
  | op_abrupt ha' hab =>
      cases Silmaril.Wasm.SSA.Args.det ha' ha
      exact hab.elim

theorem exec_localSet_inv {ls : List WVal} {x : Nat} {e : Expr} {out : Out (Option WVal)}
    (h : Exec ls (.localSet x e) out) :
    (∃ ls' w, Exec ls e (.ok ls' (some w)) ∧ out = .ok (ls'.set x w) none) ∨
      (Exec ls e out ∧ out.Abrupt) := by
  cases h with
  | localSet he => exact .inl ⟨_, _, he, rfl⟩
  | localSet_abrupt he hab => exact .inr ⟨he, hab⟩

theorem exec_if_inv {ls : List WVal} {ty : Option IntType} {e : Expr} {t f : List Expr}
    {out : Out (Option WVal)} (h : Exec ls (.if_ ty e t f) out) :
    (∃ ls₁ cv b o', Exec ls e (.ok ls₁ (some cv)) ∧ cv.truthy = some b ∧
      Seq ls₁ none (if b then t else f) o' ∧ BlockExit ty o' out) ∨
      (Exec ls e out ∧ out.Abrupt) := by
  cases h with
  | if_ hc hb hs hx => exact .inl ⟨_, _, _, _, hc, hb, hs, hx⟩
  | if_abrupt hc hab => exact .inr ⟨hc, hab⟩

theorem exec_block_inv {ls : List WVal} {ty : Option IntType} {body : List Expr}
    {out : Out (Option WVal)} (h : Exec ls (.block ty body) out) :
    ∃ o₁, Seq ls none body o₁ ∧ BlockExit ty o₁ out := by
  cases h with
  | block hs hx => exact ⟨_, hs, hx⟩

theorem seq_cons_inv {ls : List WVal} {r : Option WVal} {e : Expr} {es : List Expr}
    {out : Out (Option WVal)} (h : Seq ls r (e :: es) out) :
    (∃ ls₁ r₁, Exec ls e (.ok ls₁ r₁) ∧ Seq ls₁ r₁ es out) ∨ (Exec ls e out ∧ out.Abrupt) := by
  cases h with
  | cons hx hs => exact .inl ⟨_, _, hx, hs⟩
  | abrupt hx hab => exact .inr ⟨hx, hab⟩

theorem seq_append_inv {ls : List WVal} {r : Option WVal} :
    ∀ {A B : List Expr} {out : Out (Option WVal)}, Seq ls r (A ++ B) out →
      (Seq ls r A out ∧ out.Abrupt) ∨ ∃ ls₁ r₁, Seq ls r A (.ok ls₁ r₁) ∧ Seq ls₁ r₁ B out
  | [], B, out, h => .inr ⟨ls, r, .nil, h⟩
  | e :: A, B, out, h => by
      rcases seq_cons_inv h with ⟨ls₁, r₁, hx, hs⟩ | ⟨hx, hab⟩
      · rcases seq_append_inv hs with ⟨hs', hab⟩ | ⟨ls₂, r₂, hs', hB⟩
        · exact .inl ⟨.cons hx hs', hab⟩
        · exact .inr ⟨ls₂, r₂, .cons hx hs', hB⟩
      · exact .inl ⟨.abrupt hx hab, hab⟩

/-- An atom expression reads its location, without changing the locals. -/
theorem atomExpr_inv {ls : List WVal} {V : VLoc} {e : Expr} {v : SVal}
    (he : V.atomExpr = some e) (hr : readL ls V = some v) {out : Out (Option WVal)}
    (hx : Exec ls e out) : ∃ w, v = .atom w ∧ out = .ok ls (some w) := by
  obtain ⟨w, rfl, hex⟩ := atomExpr_exec he hr
  exact ⟨w, rfl, Silmaril.Wasm.SSA.Exec.det hx hex⟩

/-! ## Operators that cannot trap -/

theorem mayTrap_of_trap {o : Op} {vs : List WVal} (h : o.eval vs = some .trap) :
    o.mayTrap = true := by
  match o, vs with
  | .const _, [] => simp [Op.eval] at h
  | .un _, [_] => simp [Op.eval] at h
  | .bin (.rel _ _), [a, b] =>
      simp only [Op.eval, BinOp.eval] at h; split at h <;> simp at h
  | .bin (.int t op), [a, b] =>
      simp only [Op.eval, BinOp.eval] at h
      split at h
      · split at h
        · simp at h
        · rcases op with _ | _ | _ | s | s | _ | _ | _ | _ | s | _ | _ <;> (try cases s) <;>
            simp_all [Op.mayTrap, Silmaril.Wasm.Numerics.intBinOp]
      · simp at h
  | .select, [_, _, c] => simp only [Op.eval] at h; cases c.truthy <;> simp at h
  | .const _, _ :: _ | .un _, [] | .un _, _ :: _ :: _ | .bin _, [] | .bin _, [_]
  | .bin _, _ :: _ :: _ :: _ | .select, [] | .select, [_] | .select, [_, _]
  | .select, _ :: _ :: _ :: _ :: _ => simp [Op.eval] at h

theorem divSafe_noTrap {t : IntType} {op : Silmaril.Wasm.IntBinOp} {a d : WVal}
    (h : divSafe t op d = true) : BinOp.eval (.int t op) a d ≠ some .trap := by
  intro he
  simp only [BinOp.eval] at he
  split at he
  · rename_i x y hx hy
    split at he
    · simp at he
    · rename_i e herr
      simp only [divSafe, hy] at h
      rcases op with _ | _ | _ | s | s | _ | _ | _ | _ | s | _ | _ <;> (try cases s) <;>
        simp_all [Silmaril.Wasm.Numerics.intBinOp]
  · simp at he

theorem args?_cons {a r : VLoc} {l : List VLoc} (h : (VLoc.pair a r).args? = some l) :
    ∃ rest, r.args? = some rest ∧ l = a :: rest := by
  cases a <;> simp only [VLoc.args?, Option.map_eq_some_iff, reduceCtorEq] at h
  all_goals obtain ⟨rest, h1, h2⟩ := h; exact ⟨rest, h1, h2.symm⟩

theorem args?_nil {A : VLoc} (h : A.args? = some []) : A = .unit := by
  match A, h with
  | .unit, _ => rfl
  | .pair a r, h => obtain ⟨_, _, h⟩ := args?_cons h; cases h
  | .loc .., h | .const _, h => simp [VLoc.args?] at h

theorem args?_two {A x : VLoc} {d : WVal} (h : A.args? = some [x, .const d]) :
    ∃ x', A = .pair x' (.pair (.const d) .unit) := by
  match A, h with
  | .pair a r, h =>
      obtain ⟨rest, hr, hl⟩ := args?_cons h
      simp only [List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      match r, hr with
      | .pair b r', hr =>
          obtain ⟨rest', hr', hl'⟩ := args?_cons hr
          simp only [List.cons.injEq] at hl'
          obtain ⟨rfl, rfl⟩ := hl'
          exact ⟨_, by rw [args?_nil hr']⟩
      | .unit, hr | .loc .., hr | .const _, hr => simp [VLoc.args?] at hr
  | .unit, h | .loc .., h | .const _, h => simp [VLoc.args?] at h

/-- Arguments laid out as a pair ending in the constant `d` decode to `[w₁, d]`. -/
private theorem readL_args_two {ls : List WVal} {x : VLoc} {d : WVal} {ws : List WVal}
    (hr : readL ls (.pair x (.pair (.const d) .unit)) = some (encodeList ws)) :
    ∃ w₁, ws = [w₁, d] := by
  obtain ⟨va, vb, -, hvb, he⟩ := readL_pair.1 hr
  obtain ⟨vd, vu, hd, hu, he'⟩ := readL_pair.1 hvb
  have hvd : vd = .atom d := by simpa only [readL, Option.some.injEq, eq_comm] using hd
  have hvu : vu = .unit := by simpa only [readL, Option.some.injEq, eq_comm] using hu
  have hws : encodeList ws = .pair va (.pair (.atom d) .unit) := by rw [he, he', hvd, hvu]
  match ws, hws with
  | [w₁, w₂], hws => exact ⟨w₁, by simp_all [encodeList]⟩
  | [], hws | [_], hws | _ :: _ :: _ :: _, hws => simp [encodeList] at hws

theorem opSafe_noTrap {ls : List WVal} {vars : List VLoc} {o : Op} {a : Tm Prim} {A : VLoc}
    (hs : opSafe vars o a = true) (hA : staticLoc vars a = some A) {ws : List WVal}
    (hr : readL ls A = some (encodeList ws)) : o.eval ws ≠ some .trap := by
  intro ht
  have hs' : o.mayTrap = false ∨ ∃ t op x d, o = .bin (.int t op) ∧
      A.args? = some [x, .const d] ∧ divSafe t op d = true := by
    simp only [opSafe, Bool.or_eq_true, Bool.not_eq_true', hA, Option.bind_some] at hs
    rcases hs with hs | hs
    · exact .inl hs
    · split at hs
      · exact .inr ⟨_, _, _, _, rfl, by assumption, hs⟩
      · cases hs
  rcases hs' with hs' | ⟨t, op, x, d, rfl, hargs, hd⟩
  · show False
    exact Bool.false_ne_true (hs'.symm.trans (mayTrap_of_trap ht))
  · obtain ⟨x', rfl⟩ := args?_two hargs
    obtain ⟨w₁, rfl⟩ := readL_args_two hr
    exact divSafe_noTrap hd (by simpa [Op.eval] using ht)

end Silmaril.Proofs.Wasm.SSA.OutOfSSA
