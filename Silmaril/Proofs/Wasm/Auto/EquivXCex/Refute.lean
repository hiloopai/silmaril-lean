module

public import Silmaril.Wasm.Auto.EquivXCex.Defs

/-!
# Counterexamples for the extended checker: refutation

* `ctxOf_ok`: the canonical context is a typed context of the initial symbolic state;
* `not_segEquivX_of_cex`, `not_outEquivX_of_cex`: a counterexample refutes `SegEquivX` /
  `OutEquivX`. The proof runs both segments in the canonical context through `wp_init_iff` (the
  soundness of the symbolic run against the every-run logic, hence against silmaril-lean's
  small-step semantics) with the postcondition "the view equals the first run's view", which the
  first segment meets (total correctness) and the second does not.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EquivXCex

open Silmaril.Wasm.Auto.EquivXCex
open Silmaril.Wasm Silmaril.Wasm.Auto

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.Equiv (Env envOf)
open Silmaril.Wasm.Auto.Equiv

/-! ## The canonical context is typed -/

theorem setGlobal_self {s : Store Nat} {a : Nat} {g : GlobalInst} (h : s.globals[a]? = some g) :
    s.setGlobal a g.value = s := by
  unfold Store.setGlobal
  have hl : s.globals.modify a (fun g' => { g' with value := g.value }) = s.globals := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_modify]
    by_cases hi : a = i
    · subst hi
      rw [h]
      simp
    · simp [hi]
  rw [hl]

theorem setGlobals_self : ∀ (s : Store Nat) (ga : List Nat) (vs : List Val),
    (∀ (i : Nat) (hi : i < ga.length) (hv : i < vs.length),
      ∃ g, s.globals[ga[i]]? = some g ∧ g.value = vs[i]) → setGlobals s ga vs = s
  | s, a :: as, v :: vs, h => by
    obtain ⟨g, hg, hv⟩ := h 0 (by simp) (by simp)
    have h₁ : s.setGlobal a v = s := by
      have := setGlobal_self hg
      simpa [hv] using this
    show setGlobals (s.setGlobal a v) as vs = s
    rw [h₁]
    exact setGlobals_self s as vs fun i hi hv' => by
      have h₂ := h (i + 1) (by simp; omega) (by simp; omega)
      simpa only [List.getElem_cons_succ] using h₂
  | s, [], _, _ => rfl
  | s, _ :: _, [], _ => rfl

theorem initX_globs_length (lt st gt : List IntType) : (initX lt st gt).globs.length = gt.length := by
  simp [initX]

theorem ctxOf_ok (lt st gt : List IntType) (mem : Bool) (ρ : Env) (B0 : ByteArray) :
    (ctxOf lt st gt ρ B0).Ok lt st gt mem := by
  have hglen : (initX lt st gt).globs.length = gt.length := initX_globs_length lt st gt
  refine ⟨?_, rfl, by simp [ctxOf], List.nodup_range, ?_, ?_⟩
  · show (ctxOf lt st gt ρ B0).storeOf mem (initX lt st gt) = (ctxOf lt st gt ρ B0).s
    have hs : setGlobals (ctxOf lt st gt ρ B0).s (ctxOf lt st gt ρ B0).ga
        ((initX lt st gt).globs.map (denX ρ (memOf B0).bytes)) = (ctxOf lt st gt ρ B0).s := by
      apply setGlobals_self
      intro i hi hv
      have hi' : i < (initX lt st gt).globs.length := by simpa using hv
      refine ⟨⟨gty ((initX lt st gt).globs[i]'hi').1, denX ρ B0 ((initX lt st gt).globs[i]'hi')⟩, ?_, ?_⟩
      · simp [ctxOf, hi']
      · simp [memOf]
    unfold XCtx.storeOf
    simp only [ctxOf] at hs ⊢
    rw [hs]
    cases mem
    · rfl
    · simp [Store.setMem, memOf, evM, initX]
  · intro k hk
    have hk' : k < gt.length := by simpa [ctxOf] using hk
    simp [ctxOf, hk', hglen]
  · intro _
    rfl

/-! ## Refutation -/

/-- The postcondition "the view is `v`". -/
def ViewIs (loc : Bool) (v : List Val × List ByteArray × List (Option Val) × Option (List Val)) :
    Post Nat := fun s F o => viewOut loc s F o = v

theorem xout_view {loc : Bool} {mem : Bool} {c : XCtx Nat} {P : Profile}
    {host : HostSemantics Nat} (S : XState) :
    XOut .total P host c mem S [] [] (ViewIs loc (outView loc c mem S)) := by
  unfold XOut
  cases hT : firstFail c.ρ c.mi.bytes S.guards with
  | some T =>
    show viewOut loc _ _ _ = outView loc c mem S
    simp only [outView, hT]
  | none =>
    simp only [List.nil_append, List.append_nil]
    refine wp_vals_iff'.mpr ?_
    show viewOut loc _ _ _ = outView loc c mem S
    simp only [outView, hT]

theorem view_of_xout {loc : Bool} {mem : Bool} {c : XCtx Nat} {P : Profile}
    {host : HostSemantics Nat} {S : XState} {v : List Val × List ByteArray × List (Option Val) × Option (List Val)}
    (h : XOut .total P host c mem S [] [] (ViewIs loc v)) : outView loc c mem S = v := by
  unfold XOut at h
  cases hT : firstFail c.ρ c.mi.bytes S.guards with
  | some T =>
    rw [hT] at h
    simp only [outView, hT]
    exact h
  | none =>
    rw [hT] at h
    simp only [List.nil_append, List.append_nil] at h
    have h₁ := wp_vals_iff'.mp h
    simp only [outView, hT]
    exact h₁

/-- The trivial host relation. -/
def noHost : HostSemantics Nat := fun _ _ _ _ => False

theorem cexAtX_spec {loc : Bool} {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    {xs : List Nat} {B0 : ByteArray} (h : cexAtX loc lt st gt mem a b xs B0 = true) :
    ∃ A B, xsexec mem (initX lt st gt) a = some A ∧ xsexec mem (initX lt st gt) b = some B ∧
      outView loc (ctxOf lt st gt (envOf xs) B0) mem A ≠ outView loc (ctxOf lt st gt (envOf xs) B0) mem B := by
  unfold cexAtX at h
  split at h
  · rename_i A B ha hb
    exact ⟨A, B, ha, hb, of_decide_eq_true h⟩
  · cases h

/-- **Refutation of `SegEquivX` by a counterexample.** -/
theorem not_segEquivX_of_cex {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (xs : List Nat) (B0 : ByteArray) (h : cexAtX true lt st gt mem a b xs B0 = true) :
    ¬ SegEquivX lt st gt mem a b := by
  intro heq
  obtain ⟨A, B, ha, hb, hne⟩ := cexAtX_spec h
  have hc := ctxOf_ok lt st gt mem (envOf xs) B0
  have h₁ := heq .total (Profile.spec) noHost (ctxOf lt st gt (envOf xs) B0) [] []
    (ViewIs true (outView true (ctxOf lt st gt (envOf xs) B0) mem A)) hc
  rw [wp_init_iff hc ha, wp_init_iff hc hb] at h₁
  exact hne (view_of_xout (h₁.mp (xout_view A))).symm

/-- **Refutation of `OutEquivX` by a counterexample** (locals not compared). -/
theorem not_outEquivX_of_cex {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (xs : List Nat) (B0 : ByteArray) (h : cexAtX false lt st gt mem a b xs B0 = true) :
    ¬ OutEquivX lt st gt mem a b := by
  intro heq
  obtain ⟨A, B, ha, hb, hne⟩ := cexAtX_spec h
  have hc := ctxOf_ok lt st gt mem (envOf xs) B0
  have hblind : LocalsBlindX (ViewIs false (outView false (ctxOf lt st gt (envOf xs) B0) mem A)) := by
    intro s F F' o _
    simp [ViewIs, viewOut]
  have h₁ := heq .total (Profile.spec) noHost (ctxOf lt st gt (envOf xs) B0) []
    (ViewIs false (outView false (ctxOf lt st gt (envOf xs) B0) mem A)) hc hblind
  rw [wp_init_iff hc ha, wp_init_iff hc hb] at h₁
  exact hne (view_of_xout (h₁.mp (xout_view A))).symm

/-- `findCexX` returns counterexamples. -/
theorem cexAtX_of_findCexX {loc : Bool} {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    {xs : List Nat} {k : Nat} (h : findCexX loc lt st gt mem a b = some (xs, k)) :
    cexAtX loc lt st gt mem a b xs (probeMems.getD k ByteArray.empty) = true := by
  simp only [findCexX] at h
  have h₁ := List.find?_some h
  simpa using h₁

end Silmaril.Proofs.Wasm.Auto.EquivXCex
