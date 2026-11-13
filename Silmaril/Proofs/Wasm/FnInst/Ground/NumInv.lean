module

public import Silmaril.Proofs.Wasm.FnInst.Ground.NumRun
public import Silmaril.Wasm.Binaryen.NeutralOps.Thms
public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim
public import Silmaril.Wasm.Binaryen.ConstSelectSim

@[expose] public section

/-! # Inverting the machine's steps at an instruction of the stack fragment

`nstep_inv`: under the closed host, at every numerical profile, the only step of
`vals W ++ i :: rest` at a non-constant instruction `i` of the fragment is the one `nstep`
computes; it keeps store and frame. The head inversions are silmaril-lean's
(`head_drop`, `head_nop`, `head_select`), the earlier `NeutralOps.head_binop`, and `head_un`,
`head_test`, `head_rel`, `head_brIf` below.
-/

namespace Silmaril.Wasm.FnInst.Ground.Num

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.SingleThreaded.Exec.Pure (asInt asInt_eq_some)

variable {H : Type} {P : Profile}

theorem asInt_num (t : IntType) (x : BitVec t.width) : asInt t (.num ⟨.int t, x⟩) = some x :=
  asInt_eq_some.mpr rfl

/-- A numeric head step is a `NumericStep`. -/
theorem numeric_head {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c₀ : Config H} (hfam : Det.famOf e = .numeric) (h : Det.Head P s f args e c₀) :
    ∃ is', NumericStep P (vals args ++ [e]) is' ∧ c₀ = ⟨s, f, is'⟩ := by
  have hrel : Det.FamRel P (Det.famOf e) s f (vals args ++ [e]) c₀ :=
    h.fam_inv (by rw [hfam]; simp)
  simpa only [hfam, Det.FamRel] using hrel

theorem args_one {args : List Val} {t : IntType} {x : BitVec t.width}
    (h : vals args = [Admin.plain (.intConst t x)]) : args = [.num ⟨.int t, x⟩] :=
  Det.vals_inj.mp (by simpa [vals, Val.toAdmin] using h)

theorem args_two {args : List Val} {t : IntType} {x y : BitVec t.width}
    (h : vals args = [Admin.plain (.intConst t x), .plain (.intConst t y)]) :
    args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] :=
  Det.vals_inj.mp (by simpa [vals, Val.toAdmin] using h)

/-- An integer unary operator pops one operand of its type. -/
theorem head_un {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntUnOp}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.intUnOp t op)) c₀) :
    ∃ x : BitVec t.width, args = [.num ⟨.int t, x⟩] ∧
      c₀ = ⟨s, f, [.plain (.intConst t (intUnOp t op x))]⟩ := by
  obtain ⟨is', hv, rfl⟩ := numeric_head (P := P) rfl h
  generalize hl : vals args ++ [Admin.plain (.intUnOp t op)] = l at hv
  cases hv with
  | @intUnOp t' op' x =>
    obtain ⟨h1, h2⟩ := (Det.append_singleton_inj (l₂ := [Admin.plain (.intConst t' x)])).mp hl
    cases h2
    exact ⟨x, args_one h1, rfl⟩
  | _ =>
    have hlast : (vals args ++ [Admin.plain (.intUnOp t op)]).getLast? = _ :=
      congrArg List.getLast? hl
    simp at hlast

/-- An integer test pops one operand of its type. -/
theorem head_test {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntTestOp}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.intTestOp t op)) c₀) :
    ∃ x : BitVec t.width, args = [.num ⟨.int t, x⟩] ∧
      c₀ = ⟨s, f, [constI32 (intTestOp t op x)]⟩ := by
  obtain ⟨is', hv, rfl⟩ := numeric_head (P := P) rfl h
  generalize hl : vals args ++ [Admin.plain (.intTestOp t op)] = l at hv
  cases hv with
  | @intTestOp t' op' x =>
    obtain ⟨h1, h2⟩ := (Det.append_singleton_inj (l₂ := [Admin.plain (.intConst t' x)])).mp hl
    cases h2
    exact ⟨x, args_one h1, rfl⟩
  | _ =>
    have hlast : (vals args ++ [Admin.plain (.intTestOp t op)]).getLast? = _ :=
      congrArg List.getLast? hl
    simp at hlast

/-- An integer comparison pops two operands of its type. -/
theorem head_rel {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntRelOp}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.intRelOp t op)) c₀) :
    ∃ x y : BitVec t.width, args = [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] ∧
      c₀ = ⟨s, f, [constI32 (intRelOp t op x y)]⟩ := by
  obtain ⟨is', hv, rfl⟩ := numeric_head (P := P) rfl h
  generalize hl : vals args ++ [Admin.plain (.intRelOp t op)] = l at hv
  cases hv with
  | @intRelOp t' op' x y =>
    obtain ⟨h1, h2⟩ := (Det.append_singleton_inj
      (l₂ := [Admin.plain (.intConst t' x), .plain (.intConst t' y)])).mp hl
    cases h2
    exact ⟨x, y, args_two h1, rfl⟩
  | _ =>
    have hlast : (vals args ++ [Admin.plain (.intRelOp t op)]).getLast? = _ :=
      congrArg List.getLast? hl
    simp at hlast

/-- A conditional branch consumes exactly its `i32` condition (silmaril's private lemma of
`ConstBranchAny`, copied). -/
theorem head_brIf {s : Store H} {f : Frame} {args : List Val}
    {l : LabelIdx} {cfg : Config H} (h : Det.Head P s f args (.plain (.brIf l)) cfg) :
    ∃ c : BitVec 32, args = [Val.i32 c] ∧
      cfg = ⟨s, f, if c = 0 then [] else [.plain (.br l)]⟩ := by
  cases h with
  | brIfTrue hc => exact ⟨_, rfl, ite_eq_right hc ▸ rfl⟩
  | brIfFalse hc => exact ⟨_, rfl, ite_eq_left hc ▸ rfl⟩
  | _ => first
    | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
    | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
    | (exfalso; simp_all [Admin.IsCallRef])

/-- The binary operator's outcome. -/
theorem head_bin' {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntBinOp}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.intBinOp t op)) c₀) :
    ∃ o, nstep (.bin t op) args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  obtain ⟨a, b, rfl, ⟨z, hz, rfl⟩ | ⟨e, he, rfl⟩⟩ := Silmaril.Wasm.Binaryen.NeutralOps.head_binop h
  · refine ⟨.ok [.num ⟨.int t, z⟩], ?_, rfl⟩
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, nstep,
      asInt_num, Option.bind_some, Option.map_some, hz]
  · refine ⟨.stop [] .trap, ?_, rfl⟩
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, nstep,
      asInt_num, Option.bind_some, Option.map_some, he]

theorem head_select' {s : Store H} {f : Frame} {args : List Val} {ts : Option (List ValType)}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.select ts)) c₀) :
    ∃ o, nstep (.select ts) args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  obtain ⟨a, b, c, rfl, rfl⟩ := ConstSelect.head_select h
  exact ⟨.ok [if c = 0 then b else a], rfl, rfl⟩

theorem head_brIf' {s : Store H} {f : Frame} {args : List Val} {l : LabelIdx}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.brIf l)) c₀) :
    ∃ o, nstep (.brIf l) args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  obtain ⟨c, rfl, rfl⟩ := head_brIf h
  by_cases h0 : c = 0
  · subst h0
    exact ⟨.ok [], rfl, rfl⟩
  · refine ⟨.stop [] (.plain (.br l)), ?_, ?_⟩
    · have hc : asInt .i32 (Val.i32 c) = some c := asInt_num .i32 c
      simp only [List.reverse_singleton, nstep, hc]
      exact congrArg some (ite_eq_right h0)
    · rw [ite_eq_right h0]
      rfl

theorem head_un' {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntUnOp}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.intUnOp t op)) c₀) :
    ∃ o, nstep (.un t op) args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  obtain ⟨x, rfl, rfl⟩ := head_un h
  exact ⟨.ok [.num ⟨.int t, intUnOp t op x⟩], by
    simp only [List.reverse_singleton, nstep, asInt_num, Option.map_some], rfl⟩

theorem head_test' {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntTestOp}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.intTestOp t op)) c₀) :
    ∃ o, nstep (.test t op) args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  obtain ⟨x, rfl, rfl⟩ := head_test h
  exact ⟨.ok [Val.i32 (intTestOp t op x)], by
    simp only [List.reverse_singleton, nstep, asInt_num, Option.map_some], rfl⟩

theorem head_rel' {s : Store H} {f : Frame} {args : List Val} {t : IntType} {op : IntRelOp}
    {c₀ : Config H} (h : Det.Head P s f args (.plain (.intRelOp t op)) c₀) :
    ∃ o, nstep (.rel t op) args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  obtain ⟨x, y, rfl, rfl⟩ := head_rel h
  exact ⟨.ok [Val.i32 (intRelOp t op x y)], by
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, nstep,
      asInt_num, Option.bind_some, Option.map_some], rfl⟩

theorem head_drop' {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H}
    (h : Det.Head P s f args (.plain .drop) c₀) :
    ∃ o, nstep .drop args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  obtain ⟨v, rfl, rfl⟩ := RedundantSetLine.head_drop h
  exact ⟨.ok [], rfl, rfl⟩

theorem head_nop' {s : Store H} {f : Frame} {args : List Val} {c₀ : Config H}
    (h : Det.Head P s f args (.plain .nop) c₀) :
    ∃ o, nstep .nop args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  obtain ⟨rfl, rfl⟩ := ConstBranch.head_nop h
  exact ⟨.ok [], rfl, rfl⟩

/-- **Head inversion**: the head step of a non-constant instruction is `nstep`'s. -/
theorem head_n {i : NInstr} (hi : i.isConst = false) {s : Store H} {f : Frame}
    {args : List Val} {c₀ : Config H} (h : Det.Head P s f args (.plain i.lower) c₀) :
    ∃ o, nstep i args.reverse = some o ∧ c₀ = ⟨s, f, o.code⟩ := by
  cases i with
  | const => cases hi
  | un => exact head_un' h
  | bin => exact head_bin' h
  | test => exact head_test' h
  | rel => exact head_rel' h
  | drop => exact head_drop' h
  | nop => exact head_nop' h
  | select => exact head_select' h
  | brIf => exact head_brIf' h

theorem lower_val {i : NInstr} (hc : i.isConst = false) : (Admin.plain i.lower).val? = none := by
  cases i <;> first | rfl | exact absurd hc (by simp [NInstr.isConst])

theorem Out1.code_app (o : Out1) (S : List Val) :
    (o.app S).code = vals S.reverse ++ o.code := by
  cases o <;> simp [Out1.app, Out1.code]

/-- **Step inversion** at a non-constant instruction of the fragment. -/
theorem nstep_inv {i : NInstr} (hi : i.isConst = false) {s : Store H} {f : Frame}
    {W : List Val} {rest : List Admin} {c' : Config H}
    (h : Step P closedHost ⟨s, f, vals W ++ .plain i.lower :: rest⟩ c') :
    ∃ o, nstep i W.reverse = some o ∧ c' = ⟨s, f, o.code ++ rest⟩ := by
  obtain ⟨vs, args, c₀, rfl, hh, rfl⟩ := GuardSim.head_inv (lower_val hi)
    (by cases i <;> simp [NInstr.lower]) (by cases i <;> simp [NInstr.lower]) h
  obtain ⟨o, ho, rfl⟩ := head_n hi hh
  refine ⟨o.app vs.reverse, by simpa using nstep_app ho vs.reverse, ?_⟩
  rw [Out1.code_app]
  simp

end Silmaril.Wasm.FnInst.Ground.Num
