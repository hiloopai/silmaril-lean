module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round8.NxElse.Thms

/-!
# Round 9, `otherwise` rules: heads of left-hand sides

* `lastHead_eval`, `vHead_eval`: an expression with a known head evaluates to a value with the
  same head.
* `vHead_eraseV`, `vHead_eraseC`: export erasure and code erasure keep heads.
* `vHead_pair`: the head of a pair is read from its left component only.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7

/-- The last result of a successful `mapM` is the result at the last element. -/
theorem mapM_getLast {α β : Type} {f : α → Res β} :
    ∀ {xs : List α} {ys : List β} {x : α}, xs.mapM f = .ok ys → xs.getLast? = some x →
      ∃ y, ys.getLast? = some y ∧ f x = .ok y
  | [], _, _, _, hx => by simp at hx
  | x₀ :: xs, ys, x, h, hx => by
    simp only [List.mapM_cons, Res.bind_eq_ok] at h
    obtain ⟨y₀, h₀, ys', h', hys⟩ := h
    cases hys
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hx
      subst hx
      simp only [List.mapM_nil] at h'
      cases h'
      exact ⟨y₀, rfl, h₀⟩
    | cons x₁ xs =>
      rw [List.getLast?_cons_cons] at hx
      obtain ⟨y, hy, hfy⟩ := mapM_getLast h' hx
      refine ⟨y, ?_, hfy⟩
      cases ys' with
      | nil => simp at hy
      | cons y₁ ys'' => rw [List.getLast?_cons_cons]; exact hy

/-- **An instruction-list expression with a known head evaluates to a list whose last element
has that head.** -/
theorem lastHead_eval {env : Env} {ρ : VarEnv} {o : MixopS} :
    ∀ {n : Nat} {e : Exp} {v : Value}, lastHead e = some o → evalExp n env ρ e = .ok v →
      ∃ vs w, v = .list vs ∧ vs.getLast? = some (.case o w)
  | 0, _, _, _, h => by simp [evalExp] at h
  | n + 1, .listE es, v, hl, h => by
    simp only [lastHead] at hl
    split at hl
    · rename_i op e₀ hlast
      cases hl
      rcases n with _ | n
      · simp [evalExp, evalExps, Functor.map, Except.map] at h
      simp only [evalExp, evalExps, Functor.map, Except.map] at h
      split at h
      · cases h
      · rename_i vs hvs
        cases h
        obtain ⟨y, hy, hfy⟩ := mapM_getLast hvs hlast
        rcases n with _ | n
        · simp [evalExp] at hfy
        simp only [evalExp, Functor.map, Except.map] at hfy
        split at hfy
        · cases hfy
        · cases hfy
          exact ⟨vs, _, rfl, hy⟩
    · cases hl
  | n + 1, .catE e₁ e₂, v, hl, h => by
    simp only [lastHead] at hl
    simp only [evalExp, Res.bind_eq_ok] at h
    obtain ⟨v₁, _, v₂, h₂, hc⟩ := h
    obtain ⟨vs₂, w, rfl, hw⟩ := lastHead_eval hl h₂
    cases v₁ <;> simp [Value.cat?, Res.ofOption] at hc
    · rename_i vs₁
      cases hc
      exact ⟨_, w, rfl, by rw [List.getLast?_append, hw]; rfl⟩
  | _ + 1, .varE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .boolE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .numE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .textE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .unE _ _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .binE _ _ _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .cmpE _ _ _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .tupE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .projE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .caseE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .uncaseE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .optE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .theE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .strE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .dotE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .compE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .liftE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .memE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .lenE _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .idxE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .sliceE _ _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .updE _ _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .extE _ _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .callE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .iterE _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .cvtE _ _ _, _, hl, _ => by simp [lastHead] at hl
  | _ + 1, .subE _ _ _, _, hl, _ => by simp [lastHead] at hl

/-- The shape of a conclusion with a known head. -/
theorem lhsHead_some {e : Exp} {o : MixopS} (h : lhsHead e = some o) :
    ∃ z is r, e = .tupE [.caseE "%;%" (.tupE [z, is]), r] ∧ lastHead is = some o := by
  unfold lhsHead at h
  split at h
  case h_2 => cases h
  rename_i l r
  unfold cfgHead at h
  split at h
  case h_2 => cases h
  rename_i op z is
  split at h
  case isFalse => cases h
  rename_i hop
  exact ⟨z, is, r, by rw [hop], h⟩

/-- A constructor expression evaluates to a constructor value. -/
theorem evalExp_caseE {n : Nat} {env : Env} {ρ : VarEnv} {op : MixopS} {e : Exp} {a : Value}
    (h : evalExp n env ρ (.caseE op e) = .ok a) :
    ∃ k a₀, n = k + 1 ∧ evalExp k env ρ e = .ok a₀ ∧ a = .case op a₀ := by
  rcases n with _ | k
  · simp [evalExp] at h
  simp only [evalExp, Functor.map, Except.map] at h
  split at h
  · cases h
  · rename_i a₀ ha₀
    cases h
    exact ⟨k, a₀, rfl, ha₀, rfl⟩

/-- **A conclusion with a known head evaluates to a value with that head.** -/
theorem vHead_eval {env : Env} {ρ : VarEnv} {o : MixopS} {n : Nat} {e : Exp} {v : Value}
    (hl : lhsHead e = some o) (h : evalExp n env ρ e = .ok v) : vHead v = some o := by
  obtain ⟨z, is, r, he, hlast⟩ := lhsHead_some hl
  rw [he] at h
  obtain ⟨k, a, b, -, ha, -, hv⟩ := Round8.NxElse.evalExp_pair h
  obtain ⟨k', a₀, -, ha₀, hav⟩ := evalExp_caseE ha
  obtain ⟨k'', zv, isv, -, -, hi, ha₀v⟩ := Round8.NxElse.evalExp_pair ha₀
  obtain ⟨vs, w, hisv, hw⟩ := lastHead_eval hlast hi
  have hshape : v = .tuple [.case "%;%" (.tuple [zv, .list vs]), b] := by
    rw [hv, hav, ha₀v, hisv]
  rw [hshape]
  simp [vHead, vHeadC, vHeadL, hw]

/-- The head of a pair is read from its left component only. -/
theorem vHead_pair (l r r' : Value) : vHead (.tuple [l, r]) = vHead (.tuple [l, r']) := rfl

/-- Export erasure keeps the head of a list value. -/
theorem vHeadL_eraseV (v : Value) : vHeadL (Swap.eraseV v) = vHeadL v := by
  match v with
  | .list vs =>
    simp only [Swap.eraseV, vHeadL]
    rw [Swap.eraseVs_eq_map, List.getLast?_map]
    cases vs.getLast? with
    | none => rfl
    | some u => cases u <;> simp [Swap.eraseV]
  | .opt none | .opt (some _) | .bool _ | .num _ | .text _ | .tuple _ | .case _ _ | .struct _ =>
    simp [Swap.eraseV, vHeadL]

/-- Export erasure keeps the head of a configuration value. -/
theorem vHeadC_eraseV (v : Value) : vHeadC (Swap.eraseV v) = vHeadC v := by
  match v with
  | .case op (.tuple [l, is]) => simp [Swap.eraseV, Swap.eraseVs, vHeadC, vHeadL_eraseV]
  | .case _ (.tuple []) | .case _ (.tuple [_]) | .case _ (.tuple (_ :: _ :: _ :: _)) =>
    simp [Swap.eraseV, Swap.eraseVs, vHeadC]
  | .case _ (.opt none) | .case _ (.opt (some _)) | .case _ (.bool _) | .case _ (.num _)
  | .case _ (.text _) | .case _ (.list _) | .case _ (.case _ _) | .case _ (.struct _) =>
    simp [Swap.eraseV, vHeadC]
  | .opt none | .opt (some _) | .bool _ | .num _ | .text _ | .tuple _ | .list _ | .struct _ =>
    simp [Swap.eraseV, vHeadC]

/-- **Export erasure keeps heads.** -/
theorem vHead_eraseV (v : Value) : vHead (Swap.eraseV v) = vHead v := by
  match v with
  | .tuple [l, r] => simp [Swap.eraseV, Swap.eraseVs, vHead, vHeadC_eraseV]
  | .tuple [] | .tuple [_] | .tuple (_ :: _ :: _ :: _) => simp [Swap.eraseV, Swap.eraseVs, vHead]
  | .opt none | .opt (some _) | .bool _ | .num _ | .text _ | .case _ _ | .list _ | .struct _ =>
    simp [Swap.eraseV, vHead]

section Code
open Round8.CodeErase.Swap (eraseC eraseCs)

theorem eraseCs_map : ∀ vs : List Value, eraseCs vs = vs.map eraseC
  | [] => rfl
  | v :: vs => by rw [eraseCs, eraseCs_map vs]; rfl

/-- Code erasure keeps the head of a list value. -/
theorem vHeadL_eraseC (v : Value) : vHeadL (eraseC v) = vHeadL v := by
  match v with
  | .list vs =>
    simp only [eraseC, vHeadL]
    rw [eraseCs_map, List.getLast?_map]
    cases vs.getLast? with
    | none => rfl
    | some u =>
      cases u with
      | opt o => cases o <;> simp [eraseC]
      | _ => simp [eraseC]
  | .opt none | .opt (some _) | .bool _ | .num _ | .text _ | .tuple _ | .case _ _ | .struct _ =>
    simp [eraseC, vHeadL]

/-- Code erasure keeps the head of a configuration value. -/
theorem vHeadC_eraseC (v : Value) : vHeadC (eraseC v) = vHeadC v := by
  match v with
  | .case op (.tuple [l, is]) => simp [eraseC, eraseCs, vHeadC, vHeadL_eraseC]
  | .case _ (.tuple []) | .case _ (.tuple [_]) | .case _ (.tuple (_ :: _ :: _ :: _)) =>
    simp [eraseC, eraseCs, vHeadC]
  | .case _ (.opt none) | .case _ (.opt (some _)) | .case _ (.bool _) | .case _ (.num _)
  | .case _ (.text _) | .case _ (.list _) | .case _ (.case _ _) | .case _ (.struct _) =>
    simp [eraseC, vHeadC]
  | .opt none | .opt (some _) | .bool _ | .num _ | .text _ | .tuple _ | .list _ | .struct _ =>
    simp [eraseC, vHeadC]

/-- **Code erasure keeps heads.** -/
theorem vHead_eraseC (v : Value) : vHead (eraseC v) = vHead v := by
  match v with
  | .tuple [l, r] => simp [eraseC, eraseCs, vHead, vHeadC_eraseC]
  | .tuple [] | .tuple [_] | .tuple (_ :: _ :: _ :: _) => simp [eraseC, eraseCs, vHead]
  | .opt none | .opt (some _) | .bool _ | .num _ | .text _ | .case _ _ | .list _ | .struct _ =>
    simp [eraseC, vHead]

/-- Code erasure of a pair is a pair. -/
theorem eraseC_pair {v a' b' : Value} (h : eraseC v = .tuple [a', b']) :
    ∃ a b, v = .tuple [a, b] ∧ a' = eraseC a := by
  match v, h with
  | .tuple [a, b], h =>
    simp only [eraseC, eraseCs, Value.tuple.injEq, List.cons.injEq] at h
    exact ⟨a, b, rfl, h.1.symm⟩
  | .tuple [], h | .tuple [_], h | .tuple (_ :: _ :: _ :: _), h => simp [eraseC, eraseCs] at h
  | .opt none, h | .opt (some _), h | .bool _, h | .num _, h | .text _, h | .case _ _, h
  | .list _, h | .struct _, h => simp [eraseC] at h

end Code

/-- Export erasure of a pair is a pair. -/
theorem eraseV_pair {v a' b' : Value} (h : Swap.eraseV v = .tuple [a', b']) :
    ∃ a b, v = .tuple [a, b] ∧ a' = Swap.eraseV a := by
  match v, h with
  | .tuple [a, b], h =>
    simp only [Swap.eraseV, Swap.eraseVs, Value.tuple.injEq, List.cons.injEq] at h
    exact ⟨a, b, rfl, h.1.symm⟩
  | .tuple [], h | .tuple [_], h | .tuple (_ :: _ :: _ :: _), h =>
    simp [Swap.eraseV, Swap.eraseVs] at h
  | .opt none, h | .opt (some _), h | .bool _, h | .num _, h | .text _, h | .case _ _, h
  | .list _, h | .struct _, h => simp [Swap.eraseV] at h

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
