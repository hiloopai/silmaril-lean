module

public import Silmaril.Wasm.Models.FXTRun.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Vals

/-!
# Pieces of the `StepFXT` interpreter, and `StepFXT` steps in contexts

* the decompositions computed by the interpreter: `splitV_spec`, `splitV_eq` (leading values),
  `splitEnd_eq` (the last `n` values), `asFunc_eq`, `asCont_eq`, `asI32_eq`, `lastFunc_eq`,
  `lastCont_eq`, `lastI32_eq`, `coreVals_eq`,
  `handlesB_false`, and **`findSus_eq`** (the code is the context found, plugged with the
  payload and the `suspend`);
* **`StepFXT` steps lift through evaluation contexts**: `T_seq` (values before, code after),
  `T_pre`, `T_label`, `T_frame` (the caller's frame stays), `T_handler`: a `StepFX'` step by the
  context rules of `StepFX'`, an intrinsic call by extending its context `CtxV`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXTRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXTRun
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {intr : H → Option Intr}

/-! ## Decompositions -/

theorem valOf_eq {a : AdminFX} {v : FVal} (h : valOf a = some v) : a = v.toAdmin := by
  cases a with
  | core a =>
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
    exact congrArg AdminFX.core (Silmaril.Wasm.SingleThreaded.Det.val?_eq_some.mp hw)
  | contRef k =>
    cases h
    rfl
  | _ => exact absurd h (by simp [valOf])

/-- Code is its leading values and the rest. -/
theorem splitV_spec : ∀ l : List AdminFX, l = fvals (splitV l).1 ++ (splitV l).2
  | [] => rfl
  | a :: l => by
    cases hv : valOf a with
    | none => simp [splitV, hv, fvals]
    | some v =>
      have ih := splitV_spec l
      have e : splitV (a :: l) = (v :: (splitV l).1, (splitV l).2) := by simp [splitV, hv]
      rw [e]
      show a :: l = v.toAdmin :: (fvals (splitV l).1 ++ (splitV l).2)
      rw [← valOf_eq hv]
      exact congrArg (a :: ·) ih

theorem splitV_eq {l : List AdminFX} {vs : List FVal} {r : List AdminFX}
    (h : splitV l = (vs, r)) : l = fvals vs ++ r := by
  have e := splitV_spec l
  rw [h] at e
  exact e

theorem splitEnd_eq {n : Nat} {vs u w : List FVal} (h : splitEnd n vs = some (u, w)) :
    vs = u ++ w ∧ w.length = n := by
  unfold splitEnd at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(List.take_append_drop _ _).symm, by simp only [List.length_drop]; omega⟩
  · exact absurd h (by simp)

theorem asFunc_eq {v : FVal} {a : Nat} (h : asFunc v = some a) : v = .val (.ref (.func a)) := by
  unfold asFunc at h
  split at h
  · cases h
    rfl
  · exact absurd h (by simp)

theorem asCont_eq {v : FVal} {k : Nat} (h : asCont v = some k) : v = .cont k := by
  unfold asCont at h
  split at h
  · cases h
    rfl
  · exact absurd h (by simp)

theorem asI32_eq {v : FVal} {c : BitVec 32} (h : asI32 v = some c) : v = .val (Val.i32 c) := by
  unfold asI32 at h
  split at h
  · cases h
    rfl
  · exact absurd h (by simp)

theorem lastFunc_eq {vs u : List FVal} {a : Nat} (h : lastFunc vs = some (u, a)) :
    vs = u ++ [.val (.ref (.func a))] := by
  unfold lastFunc at h
  split at h
  · rename_i u₀ v hse
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    rw [(splitEnd_eq hse).1, asFunc_eq hb]
  · cases h

theorem lastCont_eq {vs u : List FVal} {k : Nat} (h : lastCont vs = some (u, k)) :
    vs = u ++ [.cont k] := by
  unfold lastCont at h
  split at h
  · rename_i u₀ v hse
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    rw [(splitEnd_eq hse).1, asCont_eq hb]
  · cases h

theorem lastI32_eq {vs u : List FVal} {c : BitVec 32} (h : lastI32 vs = some (u, c)) :
    vs = u ++ [.val (Val.i32 c)] := by
  unfold lastI32 at h
  split at h
  · rename_i u₀ v hse
    obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    rw [(splitEnd_eq hse).1, asI32_eq hb]
  · cases h

theorem coreVals_eq : ∀ {args : List FVal} {cs : List Val}, coreVals args = some cs →
    args = liftV cs
  | [], cs, h => by
    simp only [coreVals, Option.some.injEq] at h
    subst h
    rfl
  | .val v :: r, cs, h => by
    obtain ⟨cs', h', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [coreVals_eq h']
    rfl
  | .cont _ :: _, _, h => absurd h (by simp [coreVals])

@[simp] theorem fvals_app (A B : List FVal) : fvals (A ++ B) = fvals A ++ fvals B :=
  List.map_append

@[simp] theorem fvals_nil' : fvals [] = [] := rfl

theorem cvals_liftV (cs : List Val) : cvals cs = fvals (liftV cs) := by
  simp [cvals, fvals, liftV, vals, FVal.toAdmin]

theorem handlesB_false {ta : Nat} : ∀ {E : CtxV}, handlesB ta E = false → ¬ E.Handles ta
  | .hole, _ => fun h => h
  | .seq _ E _, h => handlesB_false (E := E) h
  | .label _ _ E, h => handlesB_false (E := E) h
  | .frame _ _ E, h => handlesB_false (E := E) h
  | .handler hs E, h => by
    simp only [handlesB, Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq] at h
    rintro (⟨c, hc, hct⟩ | hE)
    · exact h.1 c hc hct
    · exact handlesB_false h.2 hE

/-- **The `suspend` found**: the code is the context plugged with the payload and `suspend`. -/
theorem findSus_eq {tar : Nat → Nat} {s : Store H} : ∀ {d : Nat} {f : Frame}
    {code : List AdminFX} {E : CtxV} {w : List FVal} {x : TagIdx},
    findSus tar s d f code = some (E, w, x) → code = E.plug (fvals w ++ [.fx (.suspend x)])
  | 0, _, _, _, _, _, h => absurd h (by simp [findSus])
  | d + 1, f, code, E, w, x, h => by
    unfold findSus at h
    split at h
    · rename_i vs x' rest hsp
      split at h
      · rename_i ta ti _
        split at h
        · rename_i u w' hse
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          rw [splitV_eq hsp, (splitEnd_eq hse).1]
          simp [CtxV.plug, fvals]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · rename_i vs n k body rest hsp
      obtain ⟨⟨E', w', x'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      rw [splitV_eq hsp, findSus_eq h1]
      simp [CtxV.plug]
    · rename_i vs n fi body rest hsp
      obtain ⟨⟨E', w', x'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      rw [splitV_eq hsp, findSus_eq h1]
      simp [CtxV.plug]
    · rename_i vs hs body rest hsp
      obtain ⟨⟨E', w', x'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      rw [splitV_eq hsp, findSus_eq h1]
      simp [CtxV.plug]
    · exact absurd h (by simp)

/-! ## Steps in contexts -/

/-- Rewrite both sides of a step. -/
theorem T_conv {a b a' b' : ConfigT H} (h : StepFXT P host fx intr a b) (ha : a = a')
    (hb : b = b') : StepFXT P host fx intr a' b' := by
  subst ha hb
  exact h

/-- A step below values and before code. -/
theorem T_seq (us : List FVal) (rest : List AdminFX) {s s' : Store H}
    {K K' : List (Option ContFX)} {f f' : Frame} {c c' : List AdminFX} {t t' : Tbl}
    (h : StepFXT P host fx intr ⟨⟨s, K, f, c⟩, t⟩ ⟨⟨s', K', f', c'⟩, t'⟩) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals us ++ c ++ rest⟩, t⟩
      ⟨⟨s', K', f', fvals us ++ c' ++ rest⟩, t'⟩ := by
  cases h with
  | lift h =>
    by_cases hne : us ≠ [] ∨ rest ≠ []
    · exact .lift (.seq h hne)
    · have hu : us = [] := by simp_all
      have hr : rest = [] := by simp_all
      subst hu hr
      simpa [fvals] using (StepFXT.lift (intr := intr) (t := t) h)
  | intr hc hf hcode hi hr =>
    exact StepFXT.intr (E := .seq us _ rest) hc hf hcode hi hr

/-- A step below values. -/
theorem T_pre (us : List FVal) {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {c c' : List AdminFX} {t t' : Tbl}
    (h : StepFXT P host fx intr ⟨⟨s, K, f, c⟩, t⟩ ⟨⟨s', K', f', c'⟩, t'⟩) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals us ++ c⟩, t⟩ ⟨⟨s', K', f', fvals us ++ c'⟩, t'⟩ :=
  T_conv (T_seq us [] h) (by simp) (by simp)

/-- A step inside a label. -/
theorem T_label (n : Nat) (k : List InstrFX) {s s' : Store H} {K K' : List (Option ContFX)}
    {f f' : Frame} {c c' : List AdminFX} {t t' : Tbl}
    (h : StepFXT P host fx intr ⟨⟨s, K, f, c⟩, t⟩ ⟨⟨s', K', f', c'⟩, t'⟩) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.label n k c]⟩, t⟩ ⟨⟨s', K', f', [.label n k c']⟩, t'⟩ := by
  cases h with
  | lift h => exact .lift (.ctxLabel h)
  | intr hc hf hcode hi hr => exact StepFXT.intr (E := .label n k _) hc hf hcode hi hr

/-- A step inside a function frame; the caller's frame `f` stays. -/
theorem T_frame (n : Nat) (f : Frame) {s s' : Store H} {K K' : List (Option ContFX)}
    {fi fi' : Frame} {c c' : List AdminFX} {t t' : Tbl}
    (h : StepFXT P host fx intr ⟨⟨s, K, fi, c⟩, t⟩ ⟨⟨s', K', fi', c'⟩, t'⟩) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.frame n fi c]⟩, t⟩
      ⟨⟨s', K', f, [.frame n fi' c']⟩, t'⟩ := by
  cases h with
  | lift h => exact .lift (.ctxFrame h)
  | intr hc hf hcode hi hr => exact StepFXT.intr (E := .frame n _ _) hc hf hcode hi hr

/-- A step inside a handler frame. -/
theorem T_handler (hs : List HClause) {s s' : Store H} {K K' : List (Option ContFX)}
    {f f' : Frame} {c c' : List AdminFX} {t t' : Tbl}
    (h : StepFXT P host fx intr ⟨⟨s, K, f, c⟩, t⟩ ⟨⟨s', K', f', c'⟩, t'⟩) :
    StepFXT P host fx intr ⟨⟨s, K, f, [.handler hs c]⟩, t⟩
      ⟨⟨s', K', f', [.handler hs c']⟩, t'⟩ := by
  cases h with
  | lift h => exact .lift (.ctxHandler h)
  | intr hc hf hcode hi hr => exact StepFXT.intr (E := .handler hs _) hc hf hcode hi hr

end Silmaril.Proofs.Wasm.Models.FXTRun
