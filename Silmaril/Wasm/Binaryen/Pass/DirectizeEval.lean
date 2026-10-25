module

public import Silmaril.Wasm.Binaryen.DirectizeRel
public import Silmaril.Wasm.Binaryen.InlUnwrapClosed
public import Silmaril.Wasm.Binaryen.InlGen

@[expose] public section

/-! # Directize: element entries evaluate to function addresses

An element entry `ref.func g` evaluates, in one step and without touching the store or
the frame, to `ref.func a` with `a` the address the frame's module gives `g`
(`evalExpr_refFunc`). Lifted to the element segments of an instantiation
(`evalExprss_refFuncs`), this is the `R`-hypothesis of `Directize.slot_of_slot?`.
-/

namespace Silmaril.Wasm.Binaryen

namespace DirectizeEval

open Execution.Core Validation SingleThreaded

variable {H : Type} {P : Numerics.Profile}

theorem evalExpr_refFunc {s s' : Store H} {f f' : Frame} {g : FuncIdx} {vs : List Val}
    (h : EvalExpr P closedHost s f [.refFunc g] s' f' vs) :
    ∃ a, f.module.funcs[g.toNat]? = some a ∧ vs = [.ref (.func a)] ∧ s' = s ∧ f' = f := by
  unfold EvalExpr at h
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c₁, h₁, h₂⟩
  · simp only [expression, List.map_cons, List.map_nil, Config.mk.injEq] at heq
    obtain ⟨-, -, hv⟩ := heq
    cases vs with
    | nil => cases hv
    | cons v vs =>
      simp only [vals, List.map_cons, List.cons.injEq] at hv
      have := congrArg Admin.val? hv.1
      rw [Admin.val?_toAdmin] at this
      cases this
  · have h₁' : Step P Det.noHost ⟨s, f, expression [.refFunc g]⟩ c₁ := h₁
    rcases Det.Step.decomp h₁' with ⟨vs₀, args, e, rest, c₀, hcode, hh, rfl⟩ |
        ⟨pp, q, X, u, r, hcode, hX, -, -⟩
    · simp only [expression, List.map_cons, List.map_nil] at hcode
      rw [show vals vs₀ ++ (vals args ++ e :: rest) = vals (vs₀ ++ args) ++ e :: rest by simp]
        at hcode
      obtain ⟨hV, rfl, rfl⟩ := DirSim.vals_cons_eq (x := .plain (.refFunc g)) rfl hcode.symm
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hV
      have hc₀ : ∃ a, f.module.funcs[g.toNat]? = some a ∧ c₀ = ⟨s, f, [.ref (.func a)]⟩ := by
        cases hh with
        | reference h =>
          cases h with
          | refFunc ha => exact ⟨_, ha, rfl⟩
        | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
        | _ => fam_dismiss
      obtain ⟨a, ha, rfl⟩ := hc₀
      have hT : Config.Terminal (⟨s, f, vals [] ++ [Admin.ref (.func a)] ++ []⟩ : Config H) :=
        ⟨.values [.ref (.func a)], by simp [Result.toAdmin, vals, Val.toAdmin]⟩
      rcases Relation.ReflTransGen.cases_head h₂ with heq | ⟨c₂, h₃, -⟩
      · simp only [Config.mk.injEq] at heq
        obtain ⟨rfl, rfl, hv⟩ := heq
        refine ⟨a, ha, ?_, rfl, rfl⟩
        have : vals vs = vals [.ref (.func a)] := by simpa [vals, Val.toAdmin] using hv.symm
        exact List.map_injective_iff.mpr (fun x y h => by
          have := congrArg Admin.val? h; simpa using this) this
      · exact (InlR.terminal_no_step hT c₂ h₃).elim
    · simp only [expression, List.map_cons, List.map_nil] at hcode
      rcases hX with rfl | ⟨b, rfl⟩
      · rw [show vals (pp ++ q) ++ [Admin.trap] ++ (u ++ r) =
          vals (pp ++ q) ++ Admin.trap :: (u ++ r) by simp] at hcode
        have := DirSim.vals_cons_eq (x := .plain (.refFunc g)) rfl hcode.symm
        cases this.2.1
      · rw [show vals (pp ++ q) ++ [Admin.ref (.exn b), .plain .throwRef] ++ (u ++ r) =
          vals (pp ++ q ++ [.ref (.exn b)]) ++ .plain .throwRef :: (u ++ r) by
            simp [vals, Val.toAdmin]] at hcode
        have := DirSim.vals_cons_eq (x := .plain (.refFunc g)) rfl hcode.symm
        cases this.2.1

theorem evalExprs_length {host : HostSemantics H} : ∀ {s : Store H} {f : Frame} {es : List Expr}
    {s' : Store H} {f' : Frame} {rs : List Ref}, EvalExprs P host s f es s' f' rs →
    rs.length = es.length
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, .cons _ hs => by simp [evalExprs_length hs]

theorem evalExprss_length {host : HostSemantics H} : ∀ {s : Store H} {f : Frame}
    {ess : List (List Expr)} {s' : Store H} {f' : Frame} {rss : List (List Ref)},
    EvalExprss P host s f ess s' f' rss → rss.length = ess.length
  | _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, .cons _ hs => by simp [evalExprss_length hs]

theorem evalExprs_refFuncs : ∀ {s : Store H} {f : Frame} {es : List Expr} {s' : Store H}
    {f' : Frame} {rs : List Ref}, EvalExprs P closedHost s f es s' f' rs →
    (∀ e ∈ es, ∃ g, e = [.refFunc g]) →
    s' = s ∧ f' = f ∧ ∀ (j : Nat) (g : FuncIdx), es[j]? = some [.refFunc g] →
      ∃ a, f.module.funcs[g.toNat]? = some a ∧ rs[j]? = some (.func a)
  | _, _, _, _, _, _, .nil, _ => ⟨rfl, rfl, fun j g h => by simp at h⟩
  | _, _, _, _, _, _, .cons (e := e) he hs, hc => by
    obtain ⟨g, rfl⟩ := hc e (by simp)
    obtain ⟨a, ha, hv, rfl, rfl⟩ := evalExpr_refFunc he
    simp only [List.cons.injEq, Val.ref.injEq, and_true] at hv
    subst hv
    obtain ⟨rfl, rfl, hr⟩ := evalExprs_refFuncs hs (fun e he => hc e (by simp [he]))
    refine ⟨rfl, rfl, fun j g' hj => ?_⟩
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, List.cons.injEq,
        Instr.refFunc.injEq, and_true] at hj
      subst hj
      exact ⟨a, ha, rfl⟩
    | succ j => simpa using hr j g' (by simpa using hj)

theorem evalExprss_refFuncs : ∀ {s : Store H} {f : Frame} {ess : List (List Expr)}
    {s' : Store H} {f' : Frame} {rss : List (List Ref)}, EvalExprss P closedHost s f ess s' f' rss →
    (∀ es ∈ ess, ∀ e ∈ es, ∃ g, e = [.refFunc g]) →
    s' = s ∧ f' = f ∧ ∀ (i : Nat) (es : List Expr), ess[i]? = some es →
      ∀ (j : Nat) (g : FuncIdx), es[j]? = some [.refFunc g] →
        ∃ a, f.module.funcs[g.toNat]? = some a ∧ (rss.getD i [])[j]? = some (.func a)
  | _, _, _, _, _, _, .nil, _ => ⟨rfl, rfl, fun i es h => by simp at h⟩
  | _, _, _, _, _, _, .cons (es := es₀) he hs, hc => by
    obtain ⟨rfl, rfl, hr₁⟩ := evalExprs_refFuncs he (hc es₀ (by simp))
    obtain ⟨rfl, rfl, hr⟩ := evalExprss_refFuncs hs (fun es hes => hc es (by simp [hes]))
    refine ⟨rfl, rfl, fun i es hi j g hj => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simpa using hr₁ j g hj
    | succ i => simpa using hr i es (by simpa using hi) j g hj

end DirectizeEval

end Silmaril.Wasm.Binaryen
