module

public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.SingleThreaded.Determinism.Family

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Proofs.Inversion

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (Det.famOf Det.Fam Det.FamShape)

variable {H : Type} {P : Profile} {host : HostSemantics H}

-- One closing tactic serves every rule; on some rules some of its branches are unused.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- A context `vals vs ++ X ++ rest` with a nonempty prefix or suffix is not a single
instruction. -/
theorem split_single {a : Admin} {vs : List Val} {X rest : List Admin}
    (hc : vals vs ++ X ++ rest = [a]) (hX : X ≠ []) (hne : vs ≠ [] ∨ rest ≠ []) : False := by
  have hl := congrArg List.length hc
  have := List.length_pos_iff.2 hX
  simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
  rcases hne with h | h
  · exact h (List.eq_nil_of_length_eq_zero (by omega))
  · exact h (List.eq_nil_of_length_eq_zero (by omega))

/-- `ctxt-instrs` never applies to a one-instruction code. -/
theorem ctxt_single {a : Admin} {vs : List Val} {is rest : List Admin}
    (hc : vals vs ++ is ++ rest = [a]) (his : is.all Admin.isVal = false)
    (hne : vs ≠ [] ∨ rest ≠ []) : False :=
  split_single hc (by rintro rfl; simp at his) hne

/-- The last instruction of a family left-hand side is of that family. -/
theorem famShape_last {k : Det.Fam} {a : Admin} {l : List Admin} (h : Det.FamShape k l)
    (hl : l.getLast? = some a) : Det.famOf a = k := by
  obtain ⟨args, e, rfl, -, hk⟩ := h
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at hl
  exact hl ▸ hk

section
open SingleThreaded.Det
variable {a : Admin}
theorem fam_parametric {l l' : List Admin} (h : ParametricStep l l') (hl : l.getLast? = some a) :
    famOf a = .parametric := famShape_last (SingleThreaded.Det.ParametricStep.shape h) hl
theorem fam_numeric {l l' : List Admin} (h : NumericStep P l l') (hl : l.getLast? = some a) :
    famOf a = .numeric := famShape_last (SingleThreaded.Det.NumericStep.shape h) hl
theorem fam_vector {l l' : List Admin} (h : VectorStep P l l') (hl : l.getLast? = some a) :
    famOf a = .vector := famShape_last (SingleThreaded.Det.VectorStep.shape h) hl
theorem fam_variable {c c' : Config H} (h : VariableStep c c') (hl : c.code.getLast? = some a) :
    famOf a = .variable := by rcases c; exact famShape_last (SingleThreaded.Det.VariableStep.shape h) hl
theorem fam_table {c c' : Config H} (h : TableStep P c c') (hl : c.code.getLast? = some a) :
    famOf a = .table := by rcases c; exact famShape_last (SingleThreaded.Det.TableStep.shape h) hl
theorem fam_memory {c c' : Config H} (h : MemoryStep P c c') (hl : c.code.getLast? = some a) :
    famOf a = .memory := by rcases c; exact famShape_last (SingleThreaded.Det.MemoryStep.shape h) hl
theorem fam_reference {c c' : Config H} (h : RefStep c c') (hl : c.code.getLast? = some a) :
    famOf a = .reference := by rcases c; exact famShape_last (SingleThreaded.Det.RefStep.shape h) hl
theorem fam_aggregate {c c' : Config H} (h : AggregateStep c c') (hl : c.code.getLast? = some a) :
    famOf a = .aggregate := by rcases c; exact famShape_last (SingleThreaded.Det.AggregateStep.shape h) hl
end

/-- Closes the cases of a `Step` that cannot apply to a one-instruction code `[a]`
(`hc : c.code = [a]`), where `a` is a control instruction. -/
local macro "single_close" hc:ident : tactic => `(tactic| first
  | (exfalso; simp only [List.cons.injEq, List.ne_nil_of_mem, reduceCtorEq, and_false,
      List.append_eq_nil_iff, List.cons_ne_nil, false_and] at $hc:ident; done)
  | (exfalso; have hl := congrArg List.length $hc:ident
     simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
     omega)
  | (exfalso; have hl := congrArg List.getLast? $hc:ident; simp at hl; done)
  | (exfalso; exact split_single $hc:ident (by simp) ‹_›)
  | (exfalso; have hl := congrArg List.getLast? $hc:ident; simp at hl; subst hl
     simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]; done))


/-- Closes a family case of a `Step` from `[a]`, `a` a control instruction. -/
local macro "fam_close" hc:ident : tactic => `(tactic| first
  | (exfalso; have := fam_parametric ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_numeric ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_vector ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_variable ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_table ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_memory ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_reference ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_aggregate ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done))

theorem frame_inv {c c' : Config H} (h : Step P host c c') {n : Nat} {fi : Frame}
    {is : List Admin} (hc : c.code = [.frame n fi is]) :
    (∃ s' fi' is', Step P host ⟨c.store, fi, is⟩ ⟨s', fi', is'⟩ ∧
        c' = ⟨s', c.frame, [.frame n fi' is']⟩) ∨
      ∃ out, FrameExit c.store fi n is out ∧ c' = ⟨c.store, c.frame, out⟩ := by
  cases h with
  | ctxtInstrs hs hne => exact (ctxt_single hc hs.not_all_isVal hne).elim
  | ctxtFrame hs =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inl ⟨_, _, _, hs, rfl⟩
  | frameVals hn =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .vals hn, rfl⟩
  | returnFrame hn =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .ret hn, rfl⟩
  | trapFrame =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .trap, rfl⟩
  | throwRefFrame =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .throw _, rfl⟩
  | returnCallRefFrameNull hr =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .returnCallNull hr, rfl⟩
  | returnCallRefFrameAddr hr hf he hn =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .returnCallAddr hr hf he hn, rfl⟩
  | _ =>
    try dsimp only at hc
    first | fam_close hc | single_close hc


/-- Closes every case that cannot apply to the one-instruction code `[a]` of `hc`. -/
local macro "inv_close" hc:ident : tactic => `(tactic| (
  try dsimp only at $hc:ident
  first
    | (exfalso; exact ctxt_single $hc:ident (Step.not_all_isVal ‹_›) ‹_›)
    | fam_close $hc
    | single_close $hc))

theorem trap_stuck {c c' : Config H} (h : Step P host c c') (hc : c.code = [.trap]) : False := by
  cases h <;> inv_close hc

theorem br_stuck {c c' : Config H} (h : Step P host c c') {l : LabelIdx}
    (hc : c.code = [.plain (.br l)]) : False := by
  cases h <;> inv_close hc

theorem return_stuck {c c' : Config H} (h : Step P host c c') (hc : c.code = [.plain .return_]) :
    False := by
  cases h <;> inv_close hc

theorem throwRef_stuck {c c' : Config H} (h : Step P host c c') (hc : c.code = [.plain .throwRef]) :
    False := by
  cases h <;> inv_close hc

theorem callRef_stuck {c c' : Config H} (h : Step P host c c') {r : Admin} (hr : r.IsCallRef)
    (hc : c.code = [r]) : False := by
  cases r with
  | plain i =>
    cases i <;> simp only [Admin.IsCallRef] at hr
    cases h <;> inv_close hc
  | callRefType d => cases h <;> inv_close hc
  | _ => simp only [Admin.IsCallRef] at hr

theorem unreachable_inv {c c' : Config H} (h : Step P host c c')
    (hc : c.code = [.plain .unreachable]) : c' = ⟨c.store, c.frame, [.trap]⟩ := by
  cases h with
  | parametric h' =>
    dsimp only at hc; subst hc
    generalize hl : [Admin.plain .unreachable] = l at h'
    cases h' <;> simp_all
  | _ => inv_close hc


theorem throwing_stuck {c c' : Config H} (h : Step P host c c') {a : Nat}
    (hc : c.code = throwing a) : False := by
  cases h with
  | @ctxtInstrs _ _ _ _ vs is _ rest hs hne =>
    dsimp only at hc
    obtain ⟨w, b, r, hb, rfl⟩ := Sim.exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs ++ w) ++ b :: (r ++ rest) =
        vals [Val.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      simpa [throwing, vals, Val.toAdmin] using hc
    obtain ⟨h1, rfl, h3⟩ := Sim.vals_append_cons_inj hb rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h3
    rcases List.append_eq_singleton_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at hne
    · exact throwRef_stuck hs (by simp)
  | @trapInstrs _ _ vs rest _ =>
    dsimp only at hc
    have hc' : vals vs ++ Admin.trap :: rest =
        vals [Val.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      simpa [throwing, vals, Val.toAdmin] using hc
    obtain ⟨-, h2, -⟩ := Sim.vals_append_cons_inj rfl rfl hc'
    cases h2
  | throwRefInstrs hne =>
    dsimp only at hc
    have hl := congrArg List.length hc
    simp only [throwing, List.length_append, vals_length, List.length_cons, List.length_nil] at hl
    rcases hne with h | h
    · exact h (List.eq_nil_of_length_eq_zero (by omega))
    · exact h (List.eq_nil_of_length_eq_zero (by omega))
  | _ =>
    try dsimp only at hc
    first
      | fam_close hc
      | (exfalso; simp [throwing] at hc; done)
      | (exfalso; have hl := congrArg List.length hc
         simp only [throwing, List.length_append, vals_length, List.length_cons, List.length_nil] at hl
         omega)
      | (exfalso; have hl := congrArg List.getLast? hc; simp [throwing] at hl; done)
      | (exfalso; have hl := congrArg List.getLast? hc; simp [throwing] at hl; subst hl
         simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]; done)

theorem label_inv {c c' : Config H} (h : Step P host c c') {n : Nat} {cont : List Instr}
    {is : List Admin} (hc : c.code = [.label n cont is]) :
    (∃ s' f' is', Step P host ⟨c.store, c.frame, is⟩ ⟨s', f', is'⟩ ∧
        c' = ⟨s', f', [.label n cont is']⟩) ∨
      ∃ out, LabelExit n cont is out ∧ c' = ⟨c.store, c.frame, out⟩ := by
  cases h with
  | ctxtLabel hs =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inl ⟨_, _, _, hs, rfl⟩
  | labelVals =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .vals _, rfl⟩
  | brLabelZero hl hn =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .brZero hl hn, rfl⟩
  | brLabelSucc hl =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .brSucc hl, rfl⟩
  | returnLabel =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .ret, rfl⟩
  | returnCallRefLabel hr =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .returnCall hr, rfl⟩
  | throwRefLabel =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .throw _, rfl⟩
  | trapLabel =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .trap, rfl⟩
  | _ => inv_close hc

theorem handler_inv {c c' : Config H} (h : Step P host c c') {n : Nat} {cs : List Catch}
    {is : List Admin} (hc : c.code = [.handler n cs is]) :
    (∃ s' f' is', Step P host ⟨c.store, c.frame, is⟩ ⟨s', f', is'⟩ ∧
        c' = ⟨s', f', [.handler n cs is']⟩) ∨
      ∃ out, HandlerExit c.store c.frame n cs is out ∧ c' = ⟨c.store, c.frame, out⟩ := by
  cases h with
  | ctxtHandler hs =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inl ⟨_, _, _, hs, rfl⟩
  | handlerVals =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .vals _, rfl⟩
  | brHandler =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .br, rfl⟩
  | returnHandler =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .ret, rfl⟩
  | returnCallRefHandler hr =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .returnCall hr, rfl⟩
  | trapHandler =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .trap, rfl⟩
  | throwRefHandlerEmpty =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .throwEmpty _, rfl⟩
  | throwRefHandlerCatch he ht =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .catch_ he ht, rfl⟩
  | throwRefHandlerCatchRef he ht =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .catchRef he ht, rfl⟩
  | throwRefHandlerCatchAll =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .catchAll _, rfl⟩
  | throwRefHandlerCatchAllRef =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .catchAllRef _, rfl⟩
  | throwRefHandlerNext hn =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .next hn, rfl⟩
  | _ => inv_close hc

/-- A one-instruction left-hand side `vals vs ++ [a]` has no values. -/
theorem vals_single {vs : List Val} {a b : Admin} (h : vals vs ++ [a] = [b]) : vs = [] ∧ a = b := by
  have hl := congrArg List.length h
  simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
  obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
  simpa using h

theorem block_inv {c c' : Config H} (h : Step P host c c') {bt : BlockType} {body : List Instr}
    (hc : c.code = [.plain (.block bt body)]) :
    ∃ t₂, c.frame.module.blockType? bt = some ([], t₂) ∧
      c' = ⟨c.store, c.frame, [.label t₂.length [] (expression body)]⟩ := by
  cases h with
  | block hbt hm =>
    obtain ⟨rfl, hc⟩ := vals_single hc
    simp only [Admin.plain.injEq, Instr.block.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain rfl : _ = [] := List.eq_nil_of_length_eq_zero hm.symm
    exact ⟨_, hbt, by simp [vals]⟩
  | _ => inv_close hc

theorem loop_inv {c c' : Config H} (h : Step P host c c') {bt : BlockType} {body : List Instr}
    (hc : c.code = [.plain (.loop bt body)]) :
    ∃ t₂, c.frame.module.blockType? bt = some ([], t₂) ∧
      c' = ⟨c.store, c.frame, [.label 0 [.loop bt body] (expression body)]⟩ := by
  cases h with
  | loop hbt hm =>
    obtain ⟨rfl, hc⟩ := vals_single hc
    simp only [Admin.plain.injEq, Instr.loop.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain rfl : _ = [] := List.eq_nil_of_length_eq_zero hm.symm
    exact ⟨_, hbt, by simp [vals]⟩
  | _ => inv_close hc

theorem call_inv {c c' : Config H} (h : Step P host c c') {x : FuncIdx}
    (hc : c.code = [.plain (.call x)]) :
    ∃ a fi, c.frame.module.funcs[x.toNat]? = some a ∧ c.store.funcs[a]? = some fi ∧
      c' = ⟨c.store, c.frame, [.ref (.func a), .callRefType fi.type]⟩ := by
  cases h with
  | call hx hf =>
    simp only [List.cons.injEq, Admin.plain.injEq, Instr.call.injEq, and_true] at hc
    subst hc
    exact ⟨_, _, hx, hf, rfl⟩
  | _ => inv_close hc

/-- `vals vs ++ [x] ++ rest` is a single instruction only as `[x]`. -/
theorem mid_single {vs : List Val} {x y : Admin} {rest : List Admin}
    (h : vals vs ++ [x] ++ rest = [y]) : vs = [] ∧ rest = [] ∧ x = y := by
  have hl := congrArg List.length h
  simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
  obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  simpa using h

theorem label_br_zero_inv {c c' : Config H} (h : Step P host c c') {n : Nat}
    {cont : List Instr} {l : LabelIdx} (hl : l.toNat = 0)
    (hc : c.code = [.label n cont [.plain (.br l)]]) :
    n = 0 ∧ c' = ⟨c.store, c.frame, expression cont⟩ := by
  rcases label_inv h hc with ⟨s', f', is', hs, -⟩ | ⟨out, hx, rfl⟩
  · exact (br_stuck hs rfl).elim
  · generalize hb : [Admin.plain (.br l)] = b at hx
    cases hx with
    | vals vs =>
      exact (SingleThreaded.Det.mem_vals (a := .plain (.br l)) (hb ▸ List.mem_singleton_self _)
        rfl).elim
    | @brZero vs' vs l' rest _ hn =>
      have hlen := congrArg List.length hb
      simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hlen
      obtain rfl : vs' = [] := List.eq_nil_of_length_eq_zero (by omega)
      obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact ⟨hn.symm, by simp [vals]⟩
    | brSucc hl' =>
      obtain ⟨-, -, hx⟩ := mid_single hb.symm
      simp only [Admin.plain.injEq, Instr.br.injEq] at hx
      subst hx; omega
    | ret => simpa using (mid_single hb.symm).2.2
    | returnCall hr =>
      obtain ⟨-, -, rfl⟩ := mid_single hb.symm
      simp [Admin.IsReturnCallRef] at hr
    | throw => simp [throwing] at hb
    | trap => simp at hb

theorem isCallRef_control {r : Admin} (h : r.IsCallRef) : Det.famOf r = .control := by
  cases r with
  | plain i => cases i <;> simp_all [Admin.IsCallRef, Det.famOf]
  | _ => simp_all [Admin.IsCallRef, Det.famOf]

/-- Peel the last two instructions `x, r` off a code ending in a non-value `r`. -/
theorem last_two {vs ws : List Val} {v w : Val} {x y r r' : Admin} (hx : x.val? = some v) (hy : y.val? = some w)
    (hr : r.val? = none) (hr' : r'.val? = none)
    (h : vals vs ++ [x, r] = vals ws ++ [y, r']) : vs = ws ∧ x = y ∧ r = r' := by
  have h' : vals (vs ++ [v]) ++ r :: [] = vals (ws ++ [w]) ++ r' :: [] := by
    rw [Admin.eq_of_val? hx, Admin.eq_of_val? hy] at h; simpa [vals] using h
  obtain ⟨h1, rfl, -⟩ := Sim.vals_append_cons_inj hr hr' h'
  obtain ⟨rfl, h2⟩ := List.append_inj' h1 rfl
  obtain rfl := List.singleton_inj.1 h2
  exact ⟨rfl, (Admin.eq_of_val? hx).trans (Admin.eq_of_val? hy).symm, rfl⟩

theorem callRef_wasm_inv {c c' : Config H} (h : Step P host c c') :
    ∀ {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H} {code : Func}, r.IsCallRef →
      c.store.funcs[a]? = some fi → fi.code = .wasm code →
      c.code = vals vs ++ [.ref (.func a), r] →
      ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
        c' = ⟨c.store, c.frame, vals vs₁ ++ [.frame rs.length (Frame.forCall fi.module vs₂ code.locals)
          [.label rs.length [] (expression code.body)]]⟩ := by
  induction h with
  | callRefFunc hr' hf' he hn hcode' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    obtain rfl : _ = code := FuncCode.wasm.inj (hcode'.symm.trans hcode)
    exact ⟨[], _, _, _, rfl, he, hn, by simp [vals]⟩
  | callRefHost hr' hf' _ _ hcode' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    cases hcode'.symm.trans hcode
  | callRefHostDiv hr' hf' _ _ hcode' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    cases hcode'.symm.trans hcode
  | callRefNull hr' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨-, hx, -⟩ := last_two (vs := []) rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) (by simpa [vals] using hc)
    cases hx
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro vs a r fi code hr hf hcode hc
    dsimp only at hc hf ⊢
    obtain ⟨w, b, t, hb, rfl⟩ := Sim.exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ w) ++ b :: (t ++ rest) =
        vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨h1, rfl, h3⟩ := Sim.vals_append_cons_inj hb (Admin.val?_of_isCallRef hr) hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h3
    rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
    · exact (callRef_stuck hs hr (by simp [vals])).elim
    · have h1' : (vs₀ ++ w') ++ [x] = vs ++ [Val.ref (.func a)] := by simpa using h1
      obtain ⟨hv, h2⟩ := List.append_inj' h1' rfl
      obtain rfl := List.singleton_inj.1 h2
      subst hv
      obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, hc''⟩ :=
        ih (vs := w') hr hf hcode (by simp [vals, Val.toAdmin])
      refine ⟨vs₀ ++ vs₁, vs₂, ps, rs, by simp, he, hn, ?_⟩
      simp only [Config.mk.injEq] at hc'' ⊢
      obtain ⟨rfl, rfl, rfl⟩ := hc''
      simp
  | @trapInstrs s f vs₀ rest _ =>
    intro vs a r fi code hr hf hcode hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isCallRef hr) hc'
    simp [Admin.IsCallRef] at hr
  | @throwRefInstrs s f vs₀ x rest _ =>
    intro vs a r fi code hr hf hcode hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin, throwing] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isCallRef hr) hc'
    simp [Admin.IsCallRef] at hr
  | _ =>
    intro vs a r fi code hr hf hcode hc
    have hl := congrArg List.getLast? hc
    simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
      Option.some_or, List.getLast?_cons] at hl
    have hk := isCallRef_control hr
    first
      | (exact absurd (fam_parametric ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_numeric ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_vector ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_variable ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_table ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_memory ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_reference ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_aggregate ‹_› hl) (by simp [hk]))
      | (simp at hl; done)
      | (simp at hl; subst hl; simp [Admin.IsCallRef] at hr; done)
      | (simp at hl; subst hl; simp [Admin.IsCallRef, Det.famOf] at hk; done)

theorem callRef_host_inv {c c' : Config H} (h : Step P host c c') :
    ∀ {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H} {code : H}, r.IsCallRef →
      c.store.funcs[a]? = some fi → fi.code = .host code →
      c.code = vals vs ++ [.ref (.func a), r] →
      ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
        ((∃ s' res, host code c.store vs₂ (.returned s' res) ∧
            c' = ⟨s', c.frame, vals vs₁ ++ res.toAdmin⟩) ∨
          (host code c.store vs₂ .diverged ∧ c' = c)) := by
  induction h with
  | callRefFunc hr' hf' he hn hcode' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    cases hcode'.symm.trans hcode
  | callRefHost hr' hf' he hn hcode' hhost =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    obtain rfl : _ = code := FuncCode.host.inj (hcode'.symm.trans hcode)
    exact ⟨[], _, _, _, rfl, he, hn, .inl ⟨_, _, hhost, by simp [vals]⟩⟩
  | callRefHostDiv hr' hf' he hn hcode' hhost =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    obtain rfl : _ = code := FuncCode.host.inj (hcode'.symm.trans hcode)
    exact ⟨[], _, _, _, rfl, he, hn, .inr ⟨hhost, rfl⟩⟩
  | callRefNull hr' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨-, hx, -⟩ := last_two (vs := []) rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) (by simpa [vals] using hc)
    cases hx
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro vs a r fi code hr hf hcode hc
    dsimp only at hc hf ⊢
    obtain ⟨w, b, t, hb, rfl⟩ := Sim.exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ w) ++ b :: (t ++ rest) =
        vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨h1, rfl, h3⟩ := Sim.vals_append_cons_inj hb (Admin.val?_of_isCallRef hr) hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h3
    rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
    · exact (callRef_stuck hs hr (by simp [vals])).elim
    · have h1' : (vs₀ ++ w') ++ [x] = vs ++ [Val.ref (.func a)] := by simpa using h1
      obtain ⟨hv, h2⟩ := List.append_inj' h1' rfl
      obtain rfl := List.singleton_inj.1 h2
      subst hv
      obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, hc''⟩ :=
        ih (vs := w') hr hf hcode (by simp [vals, Val.toAdmin])
      refine ⟨vs₀ ++ vs₁, vs₂, ps, rs, by simp, he, hn, ?_⟩
      rcases hc'' with ⟨s'', res, hh, hc''⟩ | ⟨hh, hc''⟩
      · simp only [Config.mk.injEq] at hc''
        obtain ⟨rfl, rfl, rfl⟩ := hc''
        exact .inl ⟨_, res, hh, by simp⟩
      · simp only [Config.mk.injEq] at hc''
        obtain ⟨rfl, rfl, hcc⟩ := hc''
        refine .inr ⟨hh, ?_⟩
        simp [hcc, vals, Val.toAdmin]
  | @trapInstrs s f vs₀ rest _ =>
    intro vs a r fi code hr hf hcode hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isCallRef hr) hc'
    simp [Admin.IsCallRef] at hr
  | @throwRefInstrs s f vs₀ x rest _ =>
    intro vs a r fi code hr hf hcode hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin, throwing] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isCallRef hr) hc'
    simp [Admin.IsCallRef] at hr
  | _ =>
    intro vs a r fi code hr hf hcode hc
    have hl := congrArg List.getLast? hc
    simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
      Option.some_or, List.getLast?_cons] at hl
    have hk := isCallRef_control hr
    first
      | (exact absurd (fam_parametric ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_numeric ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_vector ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_variable ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_table ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_memory ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_reference ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_aggregate ‹_› hl) (by simp [hk]))
      | (simp at hl; done)
      | (simp at hl; subst hl; simp [Admin.IsCallRef] at hr; done)
      | (simp at hl; subst hl; simp [Admin.IsCallRef, Det.famOf] at hk; done)

theorem call_inv_of {s : Store H} {f : Frame} {c : Config H} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : Step P host ⟨s, f, [.plain (.call x)]⟩ c) :
    c = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  obtain ⟨a', fi', hx', hf', rfl⟩ := call_inv h rfl
  obtain rfl : a' = a := Option.some.inj (hx'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  rfl

theorem callRef_wasm_inv_exact {s : Store H} {f : Frame} {c : Config H} {vs : List Val} {a : Nat}
    {r : Admin} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)} (hr : r.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (h : Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c) :
    c = ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]]⟩ := by
  obtain ⟨vs₁, vs₂, ps', rs', rfl, he', hn', rfl⟩ := callRef_wasm_inv h hr hf hcode rfl
  have := (Expand.iff.1 he).symm.trans (Expand.iff.1 he')
  simp only [Option.some.injEq, Ty.func.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  simp only [List.length_append] at hn
  obtain rfl : vs₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
  rfl

theorem loopBr0_inv {s : Store H} {f : Frame} {bt : BlockType} {c : Config H}
    (h : Step P host (loopBr0 s f bt) c) : c = labelBr0 s f bt := by
  obtain ⟨_, -, rfl⟩ := loop_inv h rfl
  rfl

theorem labelBr0_inv {s : Store H} {f : Frame} {bt : BlockType} {c : Config H}
    (h : Step P host (labelBr0 s f bt) c) : c = loopBr0 s f bt := by
  obtain ⟨-, rfl⟩ := label_br_zero_inv h rfl rfl
  rfl

theorem loopBr0_step {s : Store H} {f : Frame} {bt : BlockType} {t₂ : List CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) :
    Step P host (loopBr0 s f bt) (labelBr0 s f bt) := by
  have := Step.loop (P := P) (host := host) (s := s) (body := [.br ⟨0⟩]) (vs := []) hbt rfl
  simpa [vals, expression] using this

theorem labelBr0_step {s : Store H} {f : Frame} {bt : BlockType} :
    Step P host (labelBr0 s f bt) (loopBr0 s f bt) := by
  have := Step.brLabelZero (P := P) (host := host) (s := s) (f := f) (n := 0)
    (cont := [.loop bt [.br ⟨0⟩]]) (vs' := []) (vs := []) (l := ⟨0⟩) (rest := []) rfl rfl
  simpa [vals, expression] using this

theorem loopBr0_reach {s : Store H} {f : Frame} {bt : BlockType} {c : Config H}
    (h : Steps P host (loopBr0 s f bt) c) : c = loopBr0 s f bt ∨ c = labelBr0 s f bt := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hs ih =>
    rcases ih with rfl | rfl
    · exact .inr (loopBr0_inv hs)
    · exact .inl (labelBr0_inv hs)

theorem loopBr0_diverges {s : Store H} {f : Frame} {bt : BlockType} {t₂ : List CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) : Diverges P host (loopBr0 s f bt) :=
  InfiniteTrace.coinduct (fun c => c = loopBr0 s f bt ∨ c = labelBr0 s f bt)
    (by
      rintro c (rfl | rfl)
      · exact ⟨_, loopBr0_step hbt, .inr rfl⟩
      · exact ⟨_, labelBr0_step, .inl rfl⟩)
    (.inl rfl)

theorem loopBr0_not_terminal {s : Store H} {f : Frame} {bt : BlockType} {c : Config H}
    (h : Steps P host (loopBr0 s f bt) c) : ¬ c.Terminal := by
  rintro ⟨r, hr⟩
  rcases loopBr0_reach h with rfl | rfl <;> rcases r with vs | a | _ <;>
    simp [Result.toAdmin, throwing] at hr <;>
    exact SingleThreaded.Det.mem_vals (hr ▸ List.mem_singleton_self _) rfl

/-! ## Structured instructions under values -/

/-- Closes the cases of a `Step` that cannot apply to `vals us ++ [X]` (`hc`), `X` a
non-value control instruction that is no call. -/
local macro "head_close" hc:ident : tactic => `(tactic| (
  have hl := congrArg List.getLast? $hc:ident
  simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
    Option.some_or, List.getLast?_cons] at hl
  first
    | (exact absurd (fam_parametric ‹_› hl) (by simp [Det.famOf]))
    | (exact absurd (fam_numeric ‹_› hl) (by simp [Det.famOf]))
    | (exact absurd (fam_vector ‹_› hl) (by simp [Det.famOf]))
    | (exact absurd (fam_variable ‹_› hl) (by simp [Det.famOf]))
    | (exact absurd (fam_table ‹_› hl) (by simp [Det.famOf]))
    | (exact absurd (fam_memory ‹_› hl) (by simp [Det.famOf]))
    | (exact absurd (fam_reference ‹_› hl) (by simp [Det.famOf]))
    | (exact absurd (fam_aggregate ‹_› hl) (by simp [Det.famOf]))
    | (simp at hl; done)
    | (simp at hl; subst hl; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]; done)))

/-- The `ctxt-instrs` case of an inversion of `vals us ++ [X]`: the inner code is
`vals w ++ [X]` with `us = vs₀ ++ w`. -/
theorem ctxt_vals_single {vs₀ us : List Val} {X : Admin} {is rest : List Admin}
    (hX : X.val? = none) (his : is.all Admin.isVal = false)
    (hc : vals vs₀ ++ is ++ rest = vals us ++ [X]) :
    ∃ w, us = vs₀ ++ w ∧ is = vals w ++ [X] ∧ rest = [] := by
  obtain ⟨w, b, t, hb, rfl⟩ := Sim.exists_head_of_not_all his
  have hc' : vals (vs₀ ++ w) ++ b :: (t ++ rest) = vals us ++ X :: [] := by simpa using hc
  obtain ⟨h1, rfl, h3⟩ := Sim.vals_append_cons_inj hb hX hc'
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h3
  exact ⟨w, h1.symm, rfl, rfl⟩

/-- `trap-instrs` and `throw_ref-instrs` do not apply to `vals us ++ [X]`, `X` neither `TRAP`
nor `THROW_REF`. -/
theorem bubble_vals_single {vs us : List Val} {X : Admin} {rest : List Admin} (hX : X.val? = none)
    (hne : X ≠ .trap ∧ X ≠ .plain .throwRef)
    (hc : vals vs ++ [Admin.trap] ++ rest = vals us ++ [X] ∨
      ∃ a, vals vs ++ throwing a ++ rest = vals us ++ [X]) : False := by
  rcases hc with hc | ⟨a, hc⟩
  · have hc' : vals vs ++ Admin.trap :: rest = vals us ++ X :: [] := by simpa using hc
    exact hne.1 (Sim.vals_append_cons_inj rfl hX hc').2.1.symm
  · have hc' : vals (vs ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest = vals us ++ X :: [] := by
      simpa [throwing, vals, Val.toAdmin] using hc
    exact hne.2 (Sim.vals_append_cons_inj rfl hX hc').2.1.symm

theorem block_vals_inv {c c' : Config H} (h : Step P host c c') {bt : BlockType} {body : List Instr} :
    ∀ {us : List Val}, c.code = vals us ++ [.plain (.block bt body)] →
      ∃ ws vs t₁ t₂, us = ws ++ vs ∧ c.frame.module.blockType? bt = some (t₁, t₂) ∧
        vs.length = t₁.length ∧ c' = ⟨c.store, c.frame, vals ws ++ [.label t₂.length [] (vals vs ++ expression body)]⟩ := by
  induction h with
  | block hbt hm =>
    intro us hc
    obtain ⟨rfl, hx, -⟩ := Sim.vals_append_cons_inj rfl rfl hc
    simp only [Admin.plain.injEq, Instr.block.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨[], _, _, _, rfl, hbt, hm, by simp [vals]⟩
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    obtain ⟨ws, vs, t₁, t₂, rfl, hbt, hm, hc''⟩ := ih rfl
    refine ⟨vs₀ ++ ws, vs, t₁, t₂, by simp, hbt, hm, ?_⟩
    simp only [Config.mk.injEq] at hc'' ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hc''
    simp
  | trapInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inl hc)).elim
  | throwRefInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)).elim
  | _ => intro us hc; head_close hc

/-- `call x` under values resolves its callee and leaves the values in place. -/
theorem call_vals_inv {c c' : Config H} (h : Step P host c c') {x : FuncIdx} :
    ∀ {us : List Val}, c.code = vals us ++ [.plain (.call x)] →
      ∃ a fi, c.frame.module.funcs[x.toNat]? = some a ∧ c.store.funcs[a]? = some fi ∧
        c' = ⟨c.store, c.frame, vals us ++ [.ref (.func a), .callRefType fi.type]⟩ := by
  induction h with
  | call hx hf =>
    intro us hc
    obtain ⟨rfl, -, hx'⟩ := mid_single (rest := []) (by simpa using hc.symm)
    simp only [Admin.plain.injEq, Instr.call.injEq] at hx'
    subst hx'
    exact ⟨_, _, hx, hf, by simp [vals]⟩
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    obtain ⟨a, fi, hx, hf, hc''⟩ := ih rfl
    refine ⟨a, fi, hx, hf, ?_⟩
    simp only [Config.mk.injEq] at hc'' ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hc''
    simp
  | trapInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inl hc)).elim
  | throwRefInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)).elim
  | _ => intro us hc; head_close hc

theorem loop_vals_inv {c c' : Config H} (h : Step P host c c') {bt : BlockType} {body : List Instr} :
    ∀ {us : List Val}, c.code = vals us ++ [.plain (.loop bt body)] →
      ∃ ws vs t₁ t₂, us = ws ++ vs ∧ c.frame.module.blockType? bt = some (t₁, t₂) ∧
        vs.length = t₁.length ∧ c' = ⟨c.store, c.frame, vals ws ++ [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩ := by
  induction h with
  | loop hbt hm =>
    intro us hc
    obtain ⟨rfl, hx, -⟩ := Sim.vals_append_cons_inj rfl rfl hc
    simp only [Admin.plain.injEq, Instr.loop.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨[], _, _, _, rfl, hbt, hm, by simp [vals]⟩
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    obtain ⟨ws, vs, t₁, t₂, rfl, hbt, hm, hc''⟩ := ih rfl
    refine ⟨vs₀ ++ ws, vs, t₁, t₂, by simp, hbt, hm, ?_⟩
    simp only [Config.mk.injEq] at hc'' ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hc''
    simp
  | trapInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inl hc)).elim
  | throwRefInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)).elim
  | _ => intro us hc; head_close hc

theorem tryTable_vals_inv {c c' : Config H} (h : Step P host c c') {bt : BlockType} {cs : List Catch} {body : List Instr} :
    ∀ {us : List Val}, c.code = vals us ++ [.plain (.tryTable bt cs body)] →
      ∃ ws vs t₁ t₂, us = ws ++ vs ∧ c.frame.module.blockType? bt = some (t₁, t₂) ∧
        vs.length = t₁.length ∧ c' = ⟨c.store, c.frame, vals ws ++ [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩ := by
  induction h with
  | tryTable hbt hm =>
    intro us hc
    obtain ⟨rfl, hx, -⟩ := Sim.vals_append_cons_inj rfl rfl hc
    simp only [Admin.plain.injEq, Instr.tryTable.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨[], _, _, _, rfl, hbt, hm, by simp [vals]⟩
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    obtain ⟨ws, vs, t₁, t₂, rfl, hbt, hm, hc''⟩ := ih rfl
    refine ⟨vs₀ ++ ws, vs, t₁, t₂, by simp, hbt, hm, ?_⟩
    simp only [Config.mk.injEq] at hc'' ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hc''
    simp
  | trapInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inl hc)).elim
  | throwRefInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)).elim
  | _ => intro us hc; head_close hc

theorem if_vals_inv {c c' : Config H} (h : Step P host c c') {bt : BlockType}
    {b₁ b₂ : List Instr} :
    ∀ {us : List Val}, c.code = vals us ++ [.plain (.if_ bt b₁ b₂)] →
      ∃ ws k, us = ws ++ [.i32 k] ∧
        c' = ⟨c.store, c.frame, vals ws ++ [.plain (.block bt (if k = 0 then b₂ else b₁))]⟩ := by
  induction h with
  | @ifTrue s f k bt' b₁' b₂' hk =>
    intro us hc
    have hc'' : vals [Val.i32 k] ++ (Admin.plain (.if_ bt' b₁' b₂')) :: [] =
        vals us ++ .plain (.if_ bt b₁ b₂) :: [] := by
      simpa [vals, Val.toAdmin, constI32, Val.i32] using hc
    obtain ⟨rfl, hx, -⟩ := Sim.vals_append_cons_inj rfl rfl hc''
    simp only [Admin.plain.injEq, Instr.if_.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨[], k, rfl, by simp [vals]; intro h0; exact absurd h0 hk⟩
  | @ifFalse s f bt' b₁' b₂' =>
    intro us hc
    have hc'' : vals [Val.i32 0] ++ (Admin.plain (.if_ bt' b₁' b₂')) :: [] =
        vals us ++ .plain (.if_ bt b₁ b₂) :: [] := by
      simpa [vals, Val.toAdmin, constI32, Val.i32] using hc
    obtain ⟨rfl, hx, -⟩ := Sim.vals_append_cons_inj rfl rfl hc''
    simp only [Admin.plain.injEq, Instr.if_.injEq] at hx
    obtain ⟨rfl, rfl, rfl⟩ := hx
    exact ⟨[], 0, rfl, by simp [vals]⟩
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    obtain ⟨ws, k, rfl, hc''⟩ := ih rfl
    refine ⟨vs₀ ++ ws, k, by simp, ?_⟩
    simp only [Config.mk.injEq] at hc'' ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hc''
    simp
  | trapInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inl hc)).elim
  | throwRefInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)).elim
  | _ => intro us hc; head_close hc

/-! ## Branches under values -/

theorem br_vals_stuck {c c' : Config H} (h : Step P host c c') {l : LabelIdx} :
    ∀ {us : List Val}, c.code = vals us ++ [.plain (.br l)] → False := by
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    exact ih rfl
  | trapInstrs => intro us hc; exact bubble_vals_single rfl (by simp) (.inl hc)
  | throwRefInstrs => intro us hc; exact bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)
  | _ => intro us hc; head_close hc

theorem return_vals_stuck {c c' : Config H} (h : Step P host c c') :
    ∀ {us : List Val}, c.code = vals us ++ [.plain .return_] → False := by
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    exact ih rfl
  | trapInstrs => intro us hc; exact bubble_vals_single rfl (by simp) (.inl hc)
  | throwRefInstrs => intro us hc; exact bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)
  | _ => intro us hc; head_close hc

theorem brIf_vals_inv {c c' : Config H} (h : Step P host c c') {l : LabelIdx} :
    ∀ {us : List Val}, c.code = vals us ++ [.plain (.brIf l)] →
      ∃ ws k, us = ws ++ [.i32 k] ∧
        c' = ⟨c.store, c.frame, vals ws ++ (if k = 0 then [] else [.plain (.br l)])⟩ := by
  induction h with
  | @brIfTrue s f k l' hk =>
    intro us hc
    have hc'' : vals [Val.i32 k] ++ (Admin.plain (.brIf l')) :: [] =
        vals us ++ .plain (.brIf l) :: [] := by
      simpa [vals, Val.toAdmin, constI32, Val.i32] using hc
    obtain ⟨rfl, hx, -⟩ := Sim.vals_append_cons_inj rfl rfl hc''
    simp only [Admin.plain.injEq, Instr.brIf.injEq] at hx
    subst hx
    exact ⟨[], k, rfl, by simp [vals]; intro h0; exact absurd h0 hk⟩
  | @brIfFalse s f l' =>
    intro us hc
    have hc'' : vals [Val.i32 0] ++ (Admin.plain (.brIf l')) :: [] =
        vals us ++ .plain (.brIf l) :: [] := by
      simpa [vals, Val.toAdmin, constI32, Val.i32] using hc
    obtain ⟨rfl, hx, -⟩ := Sim.vals_append_cons_inj rfl rfl hc''
    simp only [Admin.plain.injEq, Instr.brIf.injEq] at hx
    subst hx
    exact ⟨[], 0, rfl, by simp [vals]⟩
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    obtain ⟨ws, k, rfl, hc''⟩ := ih rfl
    refine ⟨vs₀ ++ ws, k, by simp, ?_⟩
    simp only [Config.mk.injEq] at hc'' ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hc''
    simp
  | trapInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inl hc)).elim
  | throwRefInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)).elim
  | _ => intro us hc; head_close hc

/-- A trap under values only collapses (`trap-instrs`), keeping fewer values. -/
theorem trap_vals_inv {c c' : Config H} (h : Step P host c c') :
    ∀ {us : List Val}, c.code = vals us ++ [.trap] →
      ∃ w, c' = ⟨c.store, c.frame, vals w ++ [.trap]⟩ ∧ w.length < us.length := by
  induction h with
  | @trapInstrs s f vs rest hne =>
    intro us hc
    have hc' : vals vs ++ Admin.trap :: rest = vals us ++ Admin.trap :: [] := by simpa using hc
    obtain ⟨rfl, -, rfl⟩ := Sim.vals_append_cons_inj rfl rfl hc'
    refine ⟨[], by simp [vals], ?_⟩
    rcases hne with h | h
    · exact List.length_pos_iff.2 h
    · exact absurd rfl h
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    obtain ⟨w', hc'', hw⟩ := ih rfl
    simp only [Config.mk.injEq] at hc''
    obtain ⟨rfl, rfl, rfl⟩ := hc''
    refine ⟨vs₀ ++ w', by simp, by simp; omega⟩
  | @throwRefInstrs s f vs a rest _ =>
    intro us hc
    have hc' : vals (vs ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.trap :: [] := by
      simpa [throwing, vals, Val.toAdmin] using hc
    exact absurd (Sim.vals_append_cons_inj rfl rfl hc').2.1 (by simp)
  | _ => intro us hc; head_close hc

/-! ## Non-control instructions under values -/

theorem val_none_of_noncontrol {a : Admin} (h : Det.famOf a ≠ .control) : a.val? = none := by
  cases a with
  | plain i => cases i <;> simp_all [Det.famOf, Admin.val?]
  | _ => simp_all [Det.famOf]

theorem noncontrol_vals_inv {c c' : Config H} (h : Step P host c c') {i : Instr}
    (hk : Det.famOf (.plain i) ≠ .control) :
    ∀ {us : List Val}, c.code = vals us ++ [.plain i] →
      ∃ ws vs c₀, us = ws ++ vs ∧ FamStep P ⟨c.store, c.frame, vals vs ++ [.plain i]⟩ c₀ ∧
        c' = ⟨c₀.store, c₀.frame, vals ws ++ c₀.code⟩ := by
  have hv := val_none_of_noncontrol hk
  induction h with
  | parametric h => intro us hc; subst hc; exact ⟨[], us, _, rfl, .parametric h, by simp [vals]⟩
  | numeric h => intro us hc; subst hc; exact ⟨[], us, _, rfl, .numeric h, by simp [vals]⟩
  | vector h => intro us hc; subst hc; exact ⟨[], us, _, rfl, .vector h, by simp [vals]⟩
  | @«variable» c c' h =>
    intro us hc; rcases c with ⟨s, f, x⟩; dsimp only at hc; subst hc
    exact ⟨[], us, _, rfl, .variable h, by simp [vals]⟩
  | @table c c' h =>
    intro us hc; rcases c with ⟨s, f, x⟩; dsimp only at hc; subst hc
    exact ⟨[], us, _, rfl, .table h, by simp [vals]⟩
  | @memory c c' h =>
    intro us hc; rcases c with ⟨s, f, x⟩; dsimp only at hc; subst hc
    exact ⟨[], us, _, rfl, .memory h, by simp [vals]⟩
  | @reference c c' h =>
    intro us hc; rcases c with ⟨s, f, x⟩; dsimp only at hc; subst hc
    exact ⟨[], us, _, rfl, .reference h, by simp [vals]⟩
  | @aggregate c c' h =>
    intro us hc; rcases c with ⟨s, f, x⟩; dsimp only at hc; subst hc
    exact ⟨[], us, _, rfl, .aggregate h, by simp [vals]⟩
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single hv hs.not_all_isVal hc
    obtain ⟨ws, vs, c₀, rfl, h₀, he⟩ := ih rfl
    refine ⟨vs₀ ++ ws, vs, c₀, by simp, h₀, ?_⟩
    simp only [Config.mk.injEq] at he ⊢
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp
  | trapInstrs =>
    intro us hc
    exact (bubble_vals_single hv ⟨by simp, by rintro ⟨⟩; simp [Det.famOf] at hk⟩ (.inl hc)).elim
  | throwRefInstrs =>
    intro us hc
    exact (bubble_vals_single hv ⟨by simp, by rintro ⟨⟩; simp [Det.famOf] at hk⟩
      (.inr ⟨_, hc⟩)).elim
  | _ =>
    intro us hc
    exfalso
    have hl := congrArg List.getLast? hc
    simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
      Option.some_or, List.getLast?_cons] at hl
    first
      | (simp at hl; done)
      | (simp at hl; subst hl; simp [Det.famOf] at hk; done)
      | (simp at hl; subst hl; exact hk (isCallRef_control ‹_›))
      | (simp at hl; subst hl; simp [Admin.IsReturnCallRef] at *; done)

/-! ## Data-dependent branches -/

theorem pair_inv {x : Admin} {v : Val} {i i' : Instr} {vs : List Val} (hx : x.val? = some v)
    (hi : (Admin.plain i).val? = none) (h : [x, .plain i'] = vals vs ++ [.plain i]) :
    vs = [v] ∧ i' = i := by
  have hl := congrArg List.length h
  simp only [List.length_cons, List.length_nil, List.length_append, vals_length] at hl
  obtain ⟨w, rfl⟩ : ∃ w, vs = [w] := by
    rcases vs with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp at hl
    exact ⟨w, rfl⟩
  simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.cons.injEq, Admin.plain.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  simp at hx
  exact ⟨by rw [hx], rfl⟩

theorem brStep_step {s : Store H} {f : Frame} {us us' : List Val} {i : Instr} {X : List Admin}
    (h : BrStep s f us i us' X) :
    Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s, f, vals us' ++ X⟩ := by
  cases h with
  | tableLt hi => simpa [vals, Val.toAdmin, constI32, Val.i32] using Step.brTableLt (P := P) (host := host) (s := s) (f := f) hi
  | tableGe hi => simpa [vals, Val.toAdmin, constI32, Val.i32] using Step.brTableGe (P := P) (host := host) (s := s) (f := f) hi
  | onNullNull => simpa [vals, Val.toAdmin] using Step.brOnNullNull (P := P) (host := host) (s := s) (f := f)
  | onNullAddr hv => simpa [vals] using Step.brOnNullAddr (P := P) (host := host) (s := s) (f := f) hv
  | onNonNullNull => simpa [vals, Val.toAdmin] using Step.brOnNonNullNull (P := P) (host := host) (s := s) (f := f)
  | onNonNullAddr hv => simpa [vals] using Step.brOnNonNullAddr (P := P) (host := host) (s := s) (f := f) hv
  | onCastSucceed h => simpa [vals, Val.toAdmin] using Step.brOnCastSucceed (P := P) (host := host) h
  | onCastFail h => simpa [vals, Val.toAdmin] using Step.brOnCastFail (P := P) (host := host) h
  | onCastFailSucceed h => simpa [vals, Val.toAdmin] using Step.brOnCastFailSucceed (P := P) (host := host) h
  | onCastFailFail h => simpa [vals, Val.toAdmin] using Step.brOnCastFailFail (P := P) (host := host) h

theorem brData_vals_inv {c c' : Config H} (h : Step P host c c') {i : Instr}
    (hb : i.IsBrData) :
    ∀ {vs : List Val}, c.code = vals vs ++ [.plain i] →
      ∃ ws us us' X, vs = ws ++ us ∧ BrStep c.store c.frame us i us' X ∧
        c' = ⟨c.store, c.frame, vals ws ++ (vals us' ++ X)⟩ := by
  have hv : (Admin.plain i).val? = none := by cases i <;> simp_all [Instr.IsBrData, Admin.val?]
  have hk : Det.famOf (.plain i) = .control := by cases i <;> simp_all [Instr.IsBrData, Det.famOf]
  have hcr : ¬ (Admin.plain i).IsCallRef := by
    cases i <;> simp_all [Instr.IsBrData, Admin.IsCallRef]
  have hrcr : ¬ (Admin.plain i).IsReturnCallRef := by
    cases i <;> simp_all [Instr.IsBrData, Admin.IsReturnCallRef]
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro vs hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single hv hs.not_all_isVal hc
    obtain ⟨ws, us, us', X, rfl, hB, he⟩ := ih rfl
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨vs₀ ++ ws, us, us', X, by simp, hB, by simp⟩
  | trapInstrs =>
    intro vs hc
    exact (bubble_vals_single hv ⟨by simp, by rintro ⟨⟩; simp [Instr.IsBrData] at hb⟩ (.inl hc)).elim
  | throwRefInstrs =>
    intro vs hc
    exact (bubble_vals_single hv ⟨by simp, by rintro ⟨⟩; simp [Instr.IsBrData] at hb⟩
      (.inr ⟨_, hc⟩)).elim
  | @brTableLt s f k ls l' l hi =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv rfl hv hc
    exact ⟨[], _, _, _, rfl, .tableLt hi, by simp [vals]⟩
  | @brTableGe s f k ls l' hi =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv rfl hv hc
    exact ⟨[], _, _, _, rfl, .tableGe hi, by simp [vals]⟩
  | @brOnNullNull s f l =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv (v := .ref .null) rfl hv hc
    exact ⟨[], _, _, _, rfl, .onNullNull, by simp [vals]⟩
  | @brOnNullAddr s f v l hv' =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv (Admin.val?_toAdmin v) hv hc
    exact ⟨[], _, _, _, rfl, .onNullAddr hv', by simp [vals]⟩
  | @brOnNonNullNull s f l =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv (v := .ref .null) rfl hv hc
    exact ⟨[], _, _, _, rfl, .onNonNullNull, by simp [vals]⟩
  | @brOnNonNullAddr s f v l hv' =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv (Admin.val?_toAdmin v) hv hc
    exact ⟨[], _, _, _, rfl, .onNonNullAddr hv', by simp [vals]⟩
  | @brOnCastSucceed s f r l rt₁ rt₂ h =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv (v := .ref r) rfl hv hc
    exact ⟨[], _, _, _, rfl, .onCastSucceed h, by simp [vals, Val.toAdmin]⟩
  | @brOnCastFail s f r l rt₁ rt₂ h =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv (v := .ref r) rfl hv hc
    exact ⟨[], _, _, _, rfl, .onCastFail h, by simp [vals, Val.toAdmin]⟩
  | @brOnCastFailSucceed s f r l rt₁ rt₂ h =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv (v := .ref r) rfl hv hc
    exact ⟨[], _, _, _, rfl, .onCastFailSucceed h, by simp [vals, Val.toAdmin]⟩
  | @brOnCastFailFail s f r l rt₁ rt₂ h =>
    intro vs hc; obtain ⟨rfl, rfl⟩ := pair_inv (v := .ref r) rfl hv hc
    exact ⟨[], _, _, _, rfl, .onCastFailFail h, by simp [vals, Val.toAdmin]⟩
  | _ =>
    intro vs hc
    exfalso
    have hl := congrArg List.getLast? hc
    simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
      Option.some_or, List.getLast?_cons] at hl
    first
      | (have := fam_parametric ‹_› hl; simp [hk] at this; done)
      | (have := fam_numeric ‹_› hl; simp [hk] at this; done)
      | (have := fam_vector ‹_› hl; simp [hk] at this; done)
      | (have := fam_variable ‹_› hl; simp [hk] at this; done)
      | (have := fam_table ‹_› hl; simp [hk] at this; done)
      | (have := fam_memory ‹_› hl; simp [hk] at this; done)
      | (have := fam_reference ‹_› hl; simp [hk] at this; done)
      | (have := fam_aggregate ‹_› hl; simp [hk] at this; done)
      | (simp at hl; done)
      | (simp at hl; subst hl; simp [Instr.IsBrData] at hb; done)
      | (simp at hl; subst hl; exact hcr ‹_›)
      | (simp at hl; subst hl; exact hrcr ‹_›)

/-! ## Exceptions under values -/

theorem throw_vals_inv {c c' : Config H} (h : Step P host c c') {x : TagIdx} :
    ∀ {us : List Val}, c.code = vals us ++ [.plain (.throw x)] →
      ∃ ws vs ta ti ts, us = ws ++ vs ∧ c.store.tag? c.frame x = some (ta, ti) ∧
        Expand ti.type (.func ts .nil) ∧ vs.length = ts.length ∧
        c' = ⟨c.store.addExn ⟨ta, vs⟩, c.frame, vals ws ++ throwing c.store.exns.length⟩ := by
  induction h with
  | @throw s f x' vs ta ti ts ht he hn =>
    intro us hc
    obtain ⟨rfl, hx, -⟩ := Sim.vals_append_cons_inj rfl rfl hc
    simp only [Admin.plain.injEq, Instr.throw.injEq] at hx
    subst hx
    exact ⟨[], _, _, _, _, rfl, ht, he, hn, by simp [vals]⟩
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    obtain ⟨ws, vs, ta, ti, ts, rfl, ht, he, hn, hc''⟩ := ih rfl
    refine ⟨vs₀ ++ ws, vs, ta, ti, ts, by simp, ht, he, hn, ?_⟩
    simp only [Config.mk.injEq] at hc'' ⊢
    obtain ⟨rfl, rfl, rfl⟩ := hc''
    simp
  | trapInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inl hc)).elim
  | throwRefInstrs => intro us hc; exact (bubble_vals_single rfl (by simp) (.inr ⟨_, hc⟩)).elim
  | _ => intro us hc; head_close hc

/-- `throw_ref` under values: a null reference traps; an exception reference is thrown, after
the values below it are dropped (`throw_ref-instrs`). -/
theorem throwRef_vals_inv {c c' : Config H} (h : Step P host c c') :
    ∀ {us : List Val}, c.code = vals us ++ [.plain .throwRef] →
      (∃ ws, us = ws ++ [.ref .null] ∧ c' = ⟨c.store, c.frame, vals ws ++ [.trap]⟩) ∨
        ∃ ws ws' a, us = ws ++ ws' ++ [.ref (.exn a)] ∧ ws' ≠ [] ∧
          c' = ⟨c.store, c.frame, vals ws ++ throwing a⟩ := by
  induction h with
  | @throwRefNull s f =>
    intro us hc
    obtain ⟨rfl, -⟩ := pair_inv (v := .ref .null) rfl rfl hc
    exact .inl ⟨[], rfl, by simp [vals]⟩
  | @throwRefInstrs s f vs a rest hne =>
    intro us hc
    have hc' : vals (vs ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.plain .throwRef :: [] := by
      simpa [throwing, vals, Val.toAdmin] using hc
    obtain ⟨rfl, -, rfl⟩ := Sim.vals_append_cons_inj rfl rfl hc'
    refine .inr ⟨[], vs, a, by simp, ?_, by simp [vals]⟩
    simpa using hne
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single rfl hs.not_all_isVal hc
    rcases ih rfl with ⟨ws, rfl, hc''⟩ | ⟨ws, ws', a, rfl, hne', hc''⟩
    · simp only [Config.mk.injEq] at hc''
      obtain ⟨rfl, rfl, rfl⟩ := hc''
      exact .inl ⟨vs₀ ++ ws, by simp, by simp⟩
    · simp only [Config.mk.injEq] at hc''
      obtain ⟨rfl, rfl, rfl⟩ := hc''
      exact .inr ⟨vs₀ ++ ws, ws', a, by simp, hne', by simp⟩
  | @trapInstrs s f vs rest _ =>
    intro us hc
    have hc' : vals vs ++ Admin.trap :: rest = vals us ++ Admin.plain .throwRef :: [] := by
      simpa using hc
    exact absurd (Sim.vals_append_cons_inj rfl rfl hc').2.1 (by simp)
  | _ => intro us hc; head_close hc

/-! ## Contexts under values -/

theorem ctx_val_none {X : Admin} (hX : X.IsCtx) : X.val? = none := by
  cases X <;> simp_all [Admin.IsCtx, Admin.val?]

theorem ctx_control {X : Admin} (hX : X.IsCtx) : Det.famOf X = .control := by
  cases X <;> simp_all [Admin.IsCtx, Det.famOf]

theorem not_ctx_callRef {r : Admin} (h : r.IsCallRef) : ¬ r.IsCtx := by
  cases r <;> simp_all [Admin.IsCtx, Admin.IsCallRef]

theorem not_ctx_retCallRef {r : Admin} (h : r.IsReturnCallRef) : ¬ r.IsCtx := by
  cases r <;> simp_all [Admin.IsCtx, Admin.IsReturnCallRef]

theorem ctx_vals_inv_aux {c c' : Config H} (h : Step P host c c') {X : Admin} (hX : X.IsCtx) :
    ∀ {us : List Val}, c.code = vals us ++ [X] → us ≠ [] →
      ∃ c₀ : Config H, Step P host ⟨c.store, c.frame, [X]⟩ c₀ ∧
        c' = ⟨c₀.store, c₀.frame, vals us ++ c₀.code⟩ := by
  have hv := ctx_val_none hX
  have hk := ctx_control hX
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc hus
    dsimp only at hc ⊢
    obtain ⟨w, rfl, rfl, rfl⟩ := ctxt_vals_single hv hs.not_all_isVal hc
    rcases w with _ | ⟨v, w⟩
    · exact ⟨_, by simpa [vals] using hs, by simp⟩
    · obtain ⟨c₀, h₀, he⟩ := ih rfl (List.cons_ne_nil _ _)
      simp only [Config.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact ⟨c₀, h₀, by simp⟩
  | trapInstrs =>
    intro us hc _
    exact (bubble_vals_single hv ⟨by rintro rfl; simp [Admin.IsCtx] at hX,
      by rintro rfl; simp [Admin.IsCtx] at hX⟩ (.inl hc)).elim
  | throwRefInstrs =>
    intro us hc _
    exact (bubble_vals_single hv ⟨by rintro rfl; simp [Admin.IsCtx] at hX,
      by rintro rfl; simp [Admin.IsCtx] at hX⟩ (.inr ⟨_, hc⟩)).elim
  | _ =>
    intro us hc hus
    exfalso
    first
      | (have hl := congrArg List.length hc
         simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
         exact hus (List.eq_nil_of_length_eq_zero (by omega)))
      | (have hl := congrArg List.getLast? hc
         simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
           Option.some_or, List.getLast?_cons] at hl
         first
           | (have := fam_parametric ‹_› hl; simp [hk] at this; done)
           | (have := fam_numeric ‹_› hl; simp [hk] at this; done)
           | (have := fam_vector ‹_› hl; simp [hk] at this; done)
           | (have := fam_variable ‹_› hl; simp [hk] at this; done)
           | (have := fam_table ‹_› hl; simp [hk] at this; done)
           | (have := fam_memory ‹_› hl; simp [hk] at this; done)
           | (have := fam_reference ‹_› hl; simp [hk] at this; done)
           | (have := fam_aggregate ‹_› hl; simp [hk] at this; done)
           | (simp at hl; subst hl; simp [Admin.IsCtx] at hX; done)
           | (simp at hl; subst hl; exact not_ctx_callRef ‹_› hX)
           | (simp at hl; subst hl; exact not_ctx_retCallRef ‹_› hX))

/-- A `LABEL`, `HANDLER` or `FRAME` under values steps as itself, under those values. -/
theorem ctx_vals_inv {s : Store H} {f : Frame} {c : Config H} {us : List Val} {X : Admin}
    (hX : X.IsCtx) (h : Step P host ⟨s, f, vals us ++ [X]⟩ c) :
    ∃ c₀ : Config H, Step P host ⟨s, f, [X]⟩ c₀ ∧ c = ⟨c₀.store, c₀.frame, vals us ++ c₀.code⟩ := by
  rcases us with _ | ⟨v, us⟩
  · exact ⟨c, by simpa [vals] using h, by simp [vals]⟩
  · exact ctx_vals_inv_aux h hX rfl (List.cons_ne_nil _ _)

/-- A context instruction in the middle of a sequence steps as itself, in place. -/
theorem ctx_in_seq {s : Store H} {f : Frame} {c : Config H} {vs : List Val} {X : Admin}
    {rest : List Admin} (hX : X.IsCtx) (h : Step P host ⟨s, f, vals vs ++ X :: rest⟩ c) :
    ∃ c₀ : Config H, Step P host ⟨s, f, [X]⟩ c₀ ∧
      c = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ := by
  rcases c with ⟨s', f', code'⟩
  rcases Sim.Step.split_head (ctx_val_none hX) h with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩
  · obtain ⟨c₀, h₀, he⟩ := ctx_vals_inv hX hs
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨c₀, h₀, by simp⟩
  · simp [Admin.IsCtx] at hX
  · simp [Admin.IsCtx] at hX

/-- A label around values only leaves with them (`label-vals`). -/
theorem labelExit_vals {n : Nat} {cont : List Instr} {ws : List Val} {out : List Admin}
    (h : LabelExit n cont (vals ws) out) : out = vals ws := by
  generalize hw : vals ws = is at h
  have hm : ∀ x, x ∈ is → x.val? = none → False := fun x hx hv =>
    SingleThreaded.Det.mem_vals (hw ▸ hx) hv
  cases h with
  | vals vs => simp_all
  | @brZero _ _ l _ _ _ => exact (hm (.plain (.br l)) (by simp) rfl).elim
  | @brSucc _ l _ _ => exact (hm (.plain (.br l)) (by simp) rfl).elim
  | ret => exact (hm (.plain .return_) (by simp) rfl).elim
  | returnCall hc => exact (hm _ (by simp) (Admin.val?_of_isReturnCallRef hc)).elim
  | throw => exact (hm (.plain .throwRef) (by simp [throwing]) rfl).elim
  | trap => exact (hm .trap (by simp) rfl).elim

end Silmaril.Wasm.Execution.Core.Proofs.Inversion
