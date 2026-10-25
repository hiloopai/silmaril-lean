module

public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim
public import Silmaril.Wasm.Binaryen.CodeSimClosed
public import Silmaril.Wasm.Binaryen.Pass.RemoveUnusedBrs

@[expose] public section

/-! # Guard conversion is export equivalent

`invertGuards` (`Pass/RemoveUnusedBrs.lean`) relates every body to its result by the
closure of the guard pairs (`guardL_rel`), so the result side simulates the original
(`GuardSim.guardBaseSim`), and under the closed host that one simulation gives export
equivalence (`CodeSimClosed.exportEquiv_of_baseSim`; the result-side states hold no
host-call redex, `guard_noRedex`). `RemoveUnusedBrsGuardAny.lean` adds the direct
converse and proves the full raw and checked passes exactly equivalent at every
numerical profile; the executable stage now specializes that stronger result.
-/

namespace Silmaril.Wasm.Binaryen.GuardSim

open Execution.Core Execution.Core.Sim Validation Numerics RemoveUnusedBrs
open SingleThreaded (decompose? decompHead)

variable {H : Type}

/-! ## The result-side states hold no host-call redex -/

theorem guard_noRedex : CodeSimClosed.NoRedexB H (fun a b => guardB b a) := by
  intro x y hxy s vs rest
  obtain ⟨l, R, R', hl, hR, hg⟩ := hxy
  cases hg with
  | start i =>
    rw [show vals vs ++ [Admin.plain (.localGet i), .plain (.intTestOp .i32 .eqz),
      .plain (.if_ .empty R' [])] ++ rest = vals vs ++ .plain (.localGet i) ::
      (.plain (.intTestOp .i32 .eqz) :: .plain (.if_ .empty R' []) :: rest) by simp]
    exact SingleThreaded.decompose?_vals_cons_none rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
  | read v =>
    rw [show vals vs ++ [v.toAdmin, .plain (.intTestOp .i32 .eqz), .plain (.if_ .empty R' [])] ++
      rest = vals (vs ++ [v]) ++ .plain (.intTestOp .i32 .eqz) ::
      (.plain (.if_ .empty R' []) :: rest) by simp]
    exact SingleThreaded.decompose?_vals_cons_none rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
  | test c =>
    rw [show vals vs ++ [constI32 (intTestOp .i32 .eqz c), .plain (.if_ .empty R' [])] ++ rest =
      vals (vs ++ [.i32 (intTestOp .i32 .eqz c)]) ++ .plain (.if_ .empty R' []) :: rest by
        simp [constI32]]
    exact SingleThreaded.decompose?_vals_cons_none rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
  | pick c =>
    rw [show vals vs ++ [Admin.plain (.block .empty (if c = 0 then R' else []))] ++ rest =
      vals vs ++ .plain (.block .empty (if c = 0 then R' else [])) :: rest by simp]
    exact SingleThreaded.decompose?_vals_cons_none rfl
      (fun _ _ => SingleThreaded.decompHead_plain rfl)
  | exit =>
    rw [show vals vs ++ [Admin.label 0 [] []] ++ rest = vals vs ++ .label 0 [] [] :: rest by simp,
      CodeSimClosed.decompose?_head rfl]
    have : decompose? s ([] : List Admin) = none :=
      SingleThreaded.decompose?_vals_nil (vs := [])
    simp [decompHead, this]

/-! ## The pass relates every body to its result -/

theorem GBI_succ : ∀ {n : Nat} {x y : List Instr}, GBI n x y → GBI (n + 1) x y
  | 0, _, _, h => h.elim
  | _ + 1, _, _, ⟨i, l, R, R', hl, hR, hx, hy⟩ =>
    ⟨i, l, R, R', hl, InstrsRel.mono (fun _ _ h => GBI_succ h) hR, hx, hy⟩

theorem GBI_mono {n m : Nat} (h : n ≤ m) {x y : List Instr} (hg : GBI n x y) : GBI m x y := by
  induction h with
  | refl => exact hg
  | step _ ih => exact GBI_succ ih

theorem instrsRel_le {n m : Nat} (h : n ≤ m) {x y : List Instr} (hr : InstrsRel (GBI n) x y) :
    InstrsRel (GBI m) x y :=
  InstrsRel.mono (fun _ _ => GBI_mono h) hr

theorem guardL_nil {es : List BExpr} (h : guardL es = []) : es = [] := by
  cases es with
  | nil => rfl
  | cons e es => simp [guardL] at h

theorem guardL_cons {es : List BExpr} {a : BExpr} {t : List BExpr} (h : guardL es = a :: t) :
    ∃ e es', es = e :: es' ∧ guardE e = a ∧ guardL es' = t := by
  cases es with
  | nil => simp [guardL] at h
  | cons e es =>
    simp only [guardL, List.cons.injEq] at h
    exact ⟨e, es, rfl, h.1, h.2⟩

theorem guardBlock_ne_op {bt : BlockType} {body : List BExpr} {i : Instr} {args : List BExpr} :
    guardBlock bt body ≠ .op i args := by
  unfold guardBlock
  split <;> simp

theorem guardE_op {e : BExpr} {i : Instr} {args' : List BExpr} (h : guardE e = .op i args') :
    ∃ args, e = .op i args ∧ guardL args = args' := by
  cases e with
  | op j args =>
    simp only [guardE, BExpr.op.injEq] at h
    exact ⟨args, by rw [h.1], h.2⟩
  | block bt body => exact absurd h guardBlock_ne_op
  | _ => simp [guardE] at h

/-- The shape of a converted guard before conversion. -/
theorem invertGuard_guardL {body : List BExpr} {cond rest : List BExpr}
    (h : invertGuard (guardL body) = some (cond, rest)) :
    ∃ (x : LocalIdx) (l : LabelIdx) (rest₀ : List BExpr), l.toNat = 0 ∧
      cond = [.op (.intTestOp .i32 .eqz) [.op (.localGet x) []]] ∧ rest = guardL rest₀ ∧
      (body = .op (.brIf l) [.op (.localGet x) []] :: rest₀ ∨
        body = .op (.localGet x) [] :: .op (.brIf l) [] :: rest₀) := by
  unfold invertGuard at h
  split at h
  · rename_i l x r heq
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨e, es', rfl, he, hes⟩ := guardL_cons heq
      obtain ⟨args, rfl, hargs⟩ := guardE_op he
      obtain ⟨e₁, es₁, rfl, he₁, hes₁⟩ := guardL_cons hargs
      obtain rfl := guardL_nil hes₁
      obtain ⟨args₁, rfl, hargs₁⟩ := guardE_op he₁
      obtain rfl := guardL_nil hargs₁
      exact ⟨x, l, es', hc.1, rfl, hes.symm, Or.inl rfl⟩
    · cases h
  · rename_i x l r heq
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨e, es', rfl, he, hes⟩ := guardL_cons heq
      obtain ⟨args, rfl, hargs⟩ := guardE_op he
      obtain rfl := guardL_nil hargs
      obtain ⟨e₁, es₁, rfl, he₁, hes₁⟩ := guardL_cons hes
      obtain ⟨args₁, rfl, hargs₁⟩ := guardE_op he₁
      obtain rfl := guardL_nil hargs₁
      exact ⟨x, l, es₁, hc.1, rfl, hes₁.symm, Or.inr rfl⟩
    · cases h
  · cases h

/-- A converted guard is a guard pair over related tails. -/
theorem guard_site {n : Nat} {x : LocalIdx} {l : LabelIdx} {rest₀ : List BExpr}
    (hl : l.toNat = 0)
    (hr : InstrsRel (GBI n) (BExpr.lowerList rest₀) (BExpr.lowerList (guardL rest₀))) :
    InstrsRel (GBI (n + 1)) [.block .empty (.localGet x :: .brIf l :: BExpr.lowerList rest₀)]
      (BExpr.lower (.if_ .empty [.op (.intTestOp .i32 .eqz) [.op (.localGet x) []]]
        (guardL rest₀) [])) :=
  .base ⟨x, l, _, _, hl, hr, rfl, by simp [BExpr.lower]⟩

mutual
theorem guardE_rel : ∀ e : BExpr, ∃ n, InstrsRel (GBI n) e.lower (guardE e).lower
  | .op i args => by
    obtain ⟨n, h⟩ := guardL_rel args
    exact ⟨n, by simpa [guardE] using h.append (InstrsRel.refl [i])⟩
  | .loop bt body => by
    obtain ⟨n, h⟩ := guardL_rel body
    exact ⟨n, by simpa [guardE, BExpr.lower] using InstrsRel.cons (InstrRel.loop bt h) .nil⟩
  | .tryTable bt cs body => by
    obtain ⟨n, h⟩ := guardL_rel body
    exact ⟨n, by simpa [guardE, BExpr.lower] using
      InstrsRel.cons (InstrRel.tryTable bt cs h) .nil⟩
  | .if_ bt c t e => by
    obtain ⟨n₁, h₁⟩ := guardL_rel c
    obtain ⟨n₂, h₂⟩ := guardL_rel t
    obtain ⟨n₃, h₃⟩ := guardL_rel e
    refine ⟨max n₁ (max n₂ n₃), ?_⟩
    have := (instrsRel_le (by omega) h₁).append
      (InstrsRel.cons (InstrRel.if_ bt (instrsRel_le (m := max n₁ (max n₂ n₃)) (by omega) h₂)
        (instrsRel_le (by omega) h₃)) .nil)
    simpa [guardE, BExpr.lower] using this
  | .block bt body => by
    simp only [guardE]
    unfold guardBlock
    split
    · rename_i cond rest hg
      obtain ⟨x, l, rest₀, hl, rfl, rfl, hb⟩ := invertGuard_guardL hg
      rcases hb with rfl | rfl
      · obtain ⟨n, h⟩ := guardL_rel rest₀
        exact ⟨n + 1, by simpa [BExpr.lower] using guard_site (x := x) hl h⟩
      · obtain ⟨n, h⟩ := guardL_rel rest₀
        exact ⟨n + 1, by simpa [BExpr.lower] using guard_site (x := x) hl h⟩
    · obtain ⟨n, h⟩ := guardL_rel body
      exact ⟨n, by simpa [BExpr.lower] using InstrsRel.cons (InstrRel.block _ h) .nil⟩
termination_by e => sizeOf e
theorem guardL_rel : ∀ es : List BExpr,
    ∃ n, InstrsRel (GBI n) (BExpr.lowerList es) (BExpr.lowerList (guardL es))
  | [] => ⟨0, .nil⟩
  | e :: es => by
    obtain ⟨n₁, h₁⟩ := guardE_rel e
    obtain ⟨n₂, h₂⟩ := guardL_rel es
    refine ⟨max n₁ n₂, ?_⟩
    simpa [guardL] using (instrsRel_le (by omega) h₁).append (instrsRel_le (by omega) h₂)
termination_by es => sizeOf es
end

/-- **Every body is related to its converted form.** -/
theorem guardL_guardBI (es : List BExpr) :
    InstrsRel guardBI (BExpr.lowerList es) (BExpr.lowerList (guardL es)) :=
  (guardL_rel es).elim fun _ h => instrsRel_guard h

theorem invertGuards_bodiesRel (m : BModule) :
    ModuleBodiesRel (fun a b => guardBI b a) (invertGuards m).lower m.lower := by
  refine ModuleBodiesRel.flip ⟨rfl, ?_⟩
  simp only [BModule.lower, invertGuards, List.map_map]
  induction m.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons ⟨rfl, rfl, guardL_guardBI f.body⟩ ih

/-- **Guard conversion is export equivalent** under the closed host, for valid input
and output. -/
theorem invertGuards_sound {o : GrowKind → Nat → Nat → Nat → Bool} {m : BModule} (hm : m.Ok)
    (hm' : (invertGuards m).Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) (invertGuards m).lower
      m.lower :=
  CodeSimClosed.exportEquiv_of_baseSim guardBaseSim guard_noRedex (invertGuards_bodiesRel m) hm' hm

end Silmaril.Wasm.Binaryen.GuardSim
