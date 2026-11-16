module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms

/-!
# Logged reaches of the canonical relation (proofs)

* `reachLXP_typed`: a reached callee is a typed function of the reached store;
* `reachLXP_cut`: a reach is the prefix of a logged run that **cuts** the reached call (an answer
  of more values than the callee's result arity) and so ends in a trap, every context left by the
  trap;
* `reachLXP_of_log`: every call recorded in a logged run is reached, after the calls logged
  before it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- **A reached callee is typed.** -/
theorem reachLXP_typed {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {z : (wasmOShape H).self.Op} (h : ReachLXP s f stk es l z) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), z.2.2.funcs[z.1]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) := by
  induction h with
  | call _ hfi hty => exact ⟨_, _, _, funcs_of_func? hfi, hty⟩
  | ind _ _ hfi hty => exact ⟨_, _, _, hfi, hty⟩
  | ref _ hfi hty => exact ⟨_, _, _, hfi, hty⟩
  | _ => assumption

/-- A list of more values than `n`. -/
abbrev cutVals (n : Nat) : List Val := List.replicate (n + 1) (.ref .null)

theorem cutVals_length (n : Nat) : n < (cutVals n).length := by simp

theorem trap_escapes : (POut.flow Flow.trap).Escapes := trivial

theorem trap_notThrow : (POut.flow Flow.trap).NotThrow := trivial

theorem trap_notNormal : ¬ (POut.flow Flow.trap).IsNormal := fun h => h

/-- **A reach cuts the reached call**: the prefix, then the call answered by more values than its
callee returns, is a logged run ending in a trap. -/
theorem reachLXP_cut {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {z : (wasmOShape H).self.Op} (h : ReachLXP s f stk es l z) :
    ∃ (ws : List Val) (f' : Frame),
      EvalLXPh s f stk es (l ++ [OCall.mk z.1 z.2.1 z.2.2 (.inl ws) z.2.2]) (z.2.2, f', .flow .trap) := by
  induction h with
  | @call s s₁ f f₁ stk stk₁ x args es a fi ps rs l hargs hfi hty =>
    exact ⟨_, f₁, .callCut hargs hfi hty (cutVals_length rs.length)⟩
  | @ind s s₁ f f₁ stk stk₁ x y args es ad i fa fi ps rs l hargs hres hfi hty hy =>
    exact ⟨_, f₁, .indCut hargs hres hfi hty hy (cutVals_length rs.length)⟩
  | @ref s s₁ f f₁ stk stk₁ y args es fa fi ps rs l hargs hfi hty hy =>
    exact ⟨_, f₁, .refCut hargs hfi hty hy (cutVals_length rs.length)⟩
  | args _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', .argsAbort d trap_notNormal⟩
  | callK hargs hfi hty _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.callRet hargs hfi hty d⟩
  | indK hargs hres hfi hty hy _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.indRet hargs hres hfi hty hy d⟩
  | refK hargs hfi hty hy _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.refRet hargs hfi hty hy d⟩
  | opK hi hargs hflat _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.opOk hi hargs hflat d⟩
  | block har _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', .blockEsc har d trap_escapes⟩
  | blockK har hbody hvs _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.blockOk har hbody hvs d⟩
  | loop har _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', .loopEsc har d trap_escapes⟩
  | loopK har hbody _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.loopOk har hbody d⟩
  | loopBack har hbody _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.loopBack har hbody d⟩
  | cond _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', .ifAbort d trap_notNormal⟩
  | arm hc hb har _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.ifEsc hc hb har d trap_escapes⟩
  | ifK hc hb har harm hvs _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.ifOk hc hb har harm hvs d⟩
  | handler har _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', .tryEsc har d trap_escapes trap_notThrow⟩
  | tryK har hbody hvs _ ih =>
    obtain ⟨ws, f', d⟩ := ih
    exact ⟨ws, f', by simpa using EvalLXPh.tryOk har hbody hvs d⟩

/-! ## Every logged call is reached -/

theorem psplit_app {α : Type} {l₁ l₂ u w : List α} {z : α} (h : l₁ ++ l₂ = u ++ z :: w) :
    (∃ w', l₁ = u ++ z :: w') ∨ (∃ u', u = l₁ ++ u' ∧ l₂ = u' ++ z :: w) := by
  rcases List.append_eq_append_iff.1 h with ⟨a', h₁, h₂⟩ | ⟨c', h₁, h₂⟩
  · exact .inr ⟨a', h₁, h₂⟩
  · rcases c' with _ | ⟨z', c''⟩
    · simp only [List.append_nil, List.nil_append] at h₁ h₂
      exact .inr ⟨[], by simp [h₁], h₂.symm⟩
    · simp only [List.cons_append, List.cons.injEq] at h₂
      obtain ⟨rfl, -⟩ := h₂
      exact .inl ⟨c'', h₁⟩

theorem psplit_mid {α : Type} {l₁ l₂ u w : List α} {y z : α} (h : l₁ ++ y :: l₂ = u ++ z :: w) :
    (∃ w', l₁ = u ++ z :: w') ∨ (u = l₁ ∧ y = z) ∨ (∃ u', u = l₁ ++ y :: u' ∧ l₂ = u' ++ z :: w) := by
  rcases psplit_app h with h₁ | ⟨u', rfl, h₂⟩
  · exact .inl h₁
  · rcases u' with _ | ⟨y', u''⟩
    · simp only [List.nil_append, List.cons.injEq] at h₂
      exact .inr (.inl ⟨by simp, h₂.1⟩)
    · simp only [List.cons_append, List.cons.injEq] at h₂
      obtain ⟨rfl, h₂⟩ := h₂
      exact .inr (.inr ⟨u'', rfl, h₂⟩)

theorem psplit_last {α : Type} {l₁ u w : List α} {y z : α} (h : l₁ ++ [y] = u ++ z :: w) :
    (∃ w', l₁ = u ++ z :: w') ∨ (u = l₁ ∧ y = z) := by
  rcases psplit_mid h with h₁ | h₁ | ⟨u', -, h₂⟩
  · exact .inl h₁
  · exact .inr h₁
  · exact absurd h₂ (by simp)

theorem oCall_mk_inj {g g' : Nat} {args args' : List Val} {s₁ s₁' s₂ s₂' : Store H}
    {b b' : List Val ⊕ Nat} (h : OCall.mk g args s₁ b s₂ = OCall.mk g' args' s₁' b' s₂') :
    g = g' ∧ args = args' ∧ s₁ = s₁' := by
  unfold OCall.mk at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- **Every logged call is reached**, after the calls logged before it. -/
theorem reachLXP_of_log {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × POut} (h : EvalLXPh s f stk es l r) :
    ∀ (u w : List (OCall H)) (g : Nat) (args : List Val) (s₁ s₂ : Store H) (b : List Val ⊕ Nat),
      l = u ++ OCall.mk g args s₁ b s₂ :: w → ReachLXP s f stk es u ⟨g, (args, s₁)⟩ := by
  induction h with
  | nil => intro u w _ _ _ _ _ h; simp at h
  | argsAbort _ _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | callRet hargs hfi hty _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_mid h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .args (ih₁ u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .call hargs hfi hty
    · exact .callK hargs hfi hty (ih₂ u' w g args s₁ s₂ b h₁)
  | callThrow hargs hfi hty ih =>
    intro u w g args s₁ s₂ b h
    rcases psplit_last h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩
    · exact .args (ih u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .call hargs hfi hty
  | callCut hargs hfi hty _ ih =>
    intro u w g args s₁ s₂ b h
    rcases psplit_last h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩
    · exact .args (ih u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .call hargs hfi hty
  | opOk hi hargs hflat _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_app h with ⟨w', h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .args (ih₁ u w' g args s₁ s₂ b h₁)
    · exact .opK hi hargs hflat (ih₂ u' w g args s₁ s₂ b h₁)
  | opStop _ _ _ _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | blockOk har hbody hvs _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_app h with ⟨w', h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .block har (ih₁ u w' g args s₁ s₂ b h₁)
    · exact .blockK har hbody hvs (ih₂ u' w g args s₁ s₂ b h₁)
  | blockBrk har _ ih => intro u w g args s₁ s₂ b h; exact .block har (ih u w g args s₁ s₂ b h)
  | blockEsc har _ _ ih => intro u w g args s₁ s₂ b h; exact .block har (ih u w g args s₁ s₂ b h)
  | loopOk har hbody _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_app h with ⟨w', h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .loop har (ih₁ u w' g args s₁ s₂ b h₁)
    · exact .loopK har hbody (ih₂ u' w g args s₁ s₂ b h₁)
  | loopBack har hbody _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_app h with ⟨w', h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .loop har (ih₁ u w' g args s₁ s₂ b h₁)
    · exact .loopBack har hbody (ih₂ u' w g args s₁ s₂ b h₁)
  | loopBrk har _ ih => intro u w g args s₁ s₂ b h; exact .loop har (ih u w g args s₁ s₂ b h)
  | loopEsc har _ _ ih => intro u w g args s₁ s₂ b h; exact .loop har (ih u w g args s₁ s₂ b h)
  | ifOk hc hb har harm hvs _ ih₁ ih₂ ih₃ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_app h with h₁ | ⟨u', rfl, h₁⟩
    · obtain ⟨w', h₁⟩ := h₁
      rcases psplit_app h₁ with ⟨w'', h₂⟩ | ⟨u'', rfl, h₂⟩
      · exact .cond (ih₁ u w'' g args s₁ s₂ b h₂)
      · exact .arm hc hb har (ih₂ u'' w' g args s₁ s₂ b h₂)
    · exact .ifK hc hb har harm hvs (ih₃ u' w g args s₁ s₂ b h₁)
  | ifBrk hc hb har _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_app h with ⟨w', h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .cond (ih₁ u w' g args s₁ s₂ b h₁)
    · exact .arm hc hb har (ih₂ u' w g args s₁ s₂ b h₁)
  | ifEsc hc hb har _ _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_app h with ⟨w', h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .cond (ih₁ u w' g args s₁ s₂ b h₁)
    · exact .arm hc hb har (ih₂ u' w g args s₁ s₂ b h₁)
  | ifAbort _ _ ih => intro u w g args s₁ s₂ b h; exact .cond (ih u w g args s₁ s₂ b h)
  | indRet hargs hres hfi hty hy _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_mid h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .args (ih₁ u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .ind hargs hres hfi hty hy
    · exact .indK hargs hres hfi hty hy (ih₂ u' w g args s₁ s₂ b h₁)
  | indThrow hargs hres hfi hty hy ih =>
    intro u w g args s₁ s₂ b h
    rcases psplit_last h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩
    · exact .args (ih u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .ind hargs hres hfi hty hy
  | indCut hargs hres hfi hty hy _ ih =>
    intro u w g args s₁ s₂ b h
    rcases psplit_last h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩
    · exact .args (ih u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .ind hargs hres hfi hty hy
  | indRes _ _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | refRet hargs hfi hty hy _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_mid h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .args (ih₁ u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .ref hargs hfi hty hy
    · exact .refK hargs hfi hty hy (ih₂ u' w g args s₁ s₂ b h₁)
  | refThrow hargs hfi hty hy ih =>
    intro u w g args s₁ s₂ b h
    rcases psplit_last h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩
    · exact .args (ih u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .ref hargs hfi hty hy
  | refCut hargs hfi hty hy _ ih =>
    intro u w g args s₁ s₂ b h
    rcases psplit_last h with ⟨w', h₁⟩ | ⟨rfl, h₁⟩
    · exact .args (ih u w' g args s₁ s₂ b h₁)
    · obtain ⟨rfl, rfl, rfl⟩ := oCall_mk_inj h₁; exact .ref hargs hfi hty hy
  | refNull _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | tail _ _ _ _ _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | tailRes _ _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | throw _ _ _ _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | throwRefNull _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | throwRefExn _ ih => intro u w g args s₁ s₂ b h; exact .args (ih u w g args s₁ s₂ b h)
  | tryOk har hbody hvs _ ih₁ ih₂ =>
    intro u w g args s₁ s₂ b h
    rcases psplit_app h with ⟨w', h₁⟩ | ⟨u', rfl, h₁⟩
    · exact .handler har (ih₁ u w' g args s₁ s₂ b h₁)
    · exact .tryK har hbody hvs (ih₂ u' w g args s₁ s₂ b h₁)
  | tryBrk har _ ih => intro u w g args s₁ s₂ b h; exact .handler har (ih u w g args s₁ s₂ b h)
  | tryEsc har _ _ _ ih => intro u w g args s₁ s₂ b h; exact .handler har (ih u w g args s₁ s₂ b h)
  | tryCatch har _ _ ih => intro u w g args s₁ s₂ b h; exact .handler har (ih u w g args s₁ s₂ b h)
  | tryRethrow har _ _ ih => intro u w g args s₁ s₂ b h; exact .handler har (ih u w g args s₁ s₂ b h)

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
