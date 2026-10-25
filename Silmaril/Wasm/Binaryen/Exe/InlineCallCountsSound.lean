module

public import Silmaril.Wasm.Binaryen.Exe.InlineExe

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Exe.Inl

open Silmaril.Wasm Silmaril.Wasm.Binaryen

mutual
@[simp] theorem size_addCallsE : ∀ (e : BExpr) (a : Array Nat),
    (addCallsE e a).size = a.size
  | .op i args, a => by
    cases i <;> simp [addCallsE, size_addCallsL]
  | .block _ b, a | .loop _ b, a | .tryTable _ _ b, a => by
    simp [addCallsE, size_addCallsL]
  | .if_ _ c t e, a => by simp [addCallsE, size_addCallsL]
@[simp] theorem size_addCallsL : ∀ (es : List BExpr) (a : Array Nat),
    (addCallsL es a).size = a.size
  | [], a => rfl
  | e :: es, a => by simp [addCallsL, size_addCallsE, size_addCallsL]
end

mutual
/-- Each bounded entry agrees with the original single-function counter. -/
theorem get_addCallsE : ∀ (e : BExpr) (a : Array Nat) (f : Nat) (hf : f < a.size),
    (addCallsE e a)[f]'(by simpa using hf) = a[f] + callsToE f e
  | .op i args, a, f, hf => by
    simp only [addCallsE]
    cases i <;> rw [get_addCallsL _ _ _ (by simpa using hf)] <;>
      simp [callsToE, callee?, Array.getElem_modify]
    split <;> omega
  | .block _ b, a, f, hf | .loop _ b, a, f, hf | .tryTable _ _ b, a, f, hf => by
    simpa [addCallsE, callsToE] using get_addCallsL b a f hf
  | .if_ _ c t e, a, f, hf => by
    simp only [addCallsE]
    rw [get_addCallsL _ _ _ (by simpa using hf),
      get_addCallsL _ _ _ (by simpa using hf), get_addCallsL _ _ _ hf]
    simp [callsToE, Nat.add_assoc]
theorem get_addCallsL : ∀ (es : List BExpr) (a : Array Nat) (f : Nat) (hf : f < a.size),
    (addCallsL es a)[f]'(by simpa using hf) = a[f] + callsToL f es
  | [], a, f, hf => by simp [addCallsL, callsToL]
  | e :: es, a, f, hf => by
    simp only [addCallsL]
    rw [get_addCallsL _ _ _ (by simpa using hf), get_addCallsE _ _ _ hf]
    simp [callsToL, Nat.add_assoc]
end

@[simp] theorem size_fold_addCalls (fs : List BFunc) (a : Array Nat) :
    (fs.foldl (fun counts fn => addCallsL fn.body counts) a).size = a.size := by
  induction fs generalizing a with
  | nil => rfl
  | cons fn fs ih => simp [ih]

theorem get_fold_addCalls (fs : List BFunc) (a : Array Nat) (f : Nat) (hf : f < a.size) :
    (fs.foldl (fun counts fn => addCallsL fn.body counts) a)[f]'(by simpa using hf) =
      fs.foldl (fun n fn => n + callsToL f fn.body) a[f] := by
  induction fs generalizing a with
  | nil => rfl
  | cons fn fs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simpa using hf), get_addCallsL _ _ _ hf]

/-- The shared count table computes the original predicate exactly, for all IR. -/
theorem calledOnceWith_eq (m : BModule) : calledOnceWith (moduleCallCounts m) m = calledOnce m := by
  funext f
  unfold calledOnceWith calledOnce
  split
  · rename_i hf
    rw [getElem!_pos (moduleCallCounts m) f hf]
    have h := get_fold_addCalls m.funcs
      (Array.replicate (m.numImportedFuncs + m.funcs.length) 0) f (by
        simpa [moduleCallCounts] using hf)
    rw [Array.getElem_replicate] at h
    simp only [moduleCallCounts]
    rw [h]
  · rfl

/-- Cached eligibility preserves the old heuristic without a validity premise. -/
theorem calleeOkWith_eq (budget : Nat) (m : BModule) :
    calleeOkWith (calledOnceWith (moduleCallCounts m) m) budget m = calleeOk budget m := by
  rw [calledOnceWith_eq]
  rfl

/-- One cached step returns exactly the result of the original site search. -/
theorem inlineStep_eq (budget : Nat) (m : BModule) :
    inlineStep budget m =
      match findSite (calleeOk budget m) m with
      | some (g, K, args, f) => inlineSite m g K args f
      | none => none := by
  by_cases h : budget = 0
  · subst budget
    have hz (once : Nat → Bool) : calleeOkWith once 0 m = calleeOk 0 m := by
      funext f
      simp only [calleeOkWith, calleeOk]
      cases m.defFunc? f.toNat <;> rfl
    simp only [inlineStep, hz]
    rfl
  · simp only [inlineStep, h, ↓reduceIte, calleeOkWith_eq]
    rfl

end Silmaril.Wasm.Binaryen.Exe.Inl
