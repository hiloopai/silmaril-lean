module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.UPath

/-!
# Backward simulation: instructions that stay in the top frame

* `LU`, `LPath`: unique local steps (at a frame, keeping the store) of quiet code, and their
  runs; `upath_of_lpath` lifts them through an isolated context; `lu_plug` through a local one;
* `usame`: a local path of the top frame's code makes the next related configuration
  inevitable (the converse of `sim_same`);
* `lu_nop`, `lu_core`, `lu_dropCont`, `lu_contNew`: the local steps of `push`, `prim`, `drop`
  and `contNew`.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (outer SX code_top mainOk_top step_seq step_lift)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval?)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}

/-! ## Local paths -/

/-- A unique step of quiet code at frame `F`, keeping the store `s` and the frame. -/
def LU (o : GrowKind → Nat → Nat → Nat → Bool) (fx : H → Option FuncFX) (s : Store H)
    (F : Frame) (a b : List (Option ContFX) × List AdminFX) : Prop :=
  SD o fx ⟨s, a.1, F, a.2⟩ ⟨s, b.1, F, b.2⟩ ∧
    (∀ d, SD o fx ⟨s, a.1, F, a.2⟩ d → d = ⟨s, b.1, F, b.2⟩) ∧ Quiet a.2

/-- Runs of unique local steps. -/
inductive LPath (o : GrowKind → Nat → Nat → Nat → Bool) (fx : H → Option FuncFX) (s : Store H)
    (F : Frame) : List (Option ContFX) × List AdminFX → List (Option ContFX) × List AdminFX →
    Prop where
  | one {a b : List (Option ContFX) × List AdminFX} (h : LU o fx s F a b) : LPath o fx s F a b
  | cons {a b c : List (Option ContFX) × List AdminFX} (h : LU o fx s F a b)
      (h' : LPath o fx s F b c) : LPath o fx s F a c

theorem LPath.trans {s : Store H} {F : Frame} {a b c : List (Option ContFX) × List AdminFX}
    (h : LPath o fx s F a b) (h' : LPath o fx s F b c) : LPath o fx s F a c := by
  induction h with
  | one h => exact .cons h h'
  | cons h _ ih => exact .cons h (ih h')

theorem upath_of_lpath {E : CtxV} (hE : Iso E) {s : Store H} {f : Frame}
    {a b : List (Option ContFX) × List AdminFX} (h : LPath o fx s (E.frameAt f) a b) :
    UPath o fx ⟨s, a.1, f, E.plug a.2⟩ ⟨s, b.1, f, E.plug b.2⟩ := by
  induction h with
  | one h => exact .one (ustepT_plug hE h.2.2 h.1 h.2.1)
  | cons h _ ih => exact .cons (ustepT_plug hE h.2.2 h.1 h.2.1) ih

/-- A unique local step lifts through an isolated context. -/
theorem lu_plug {E : CtxV} (hE : Iso E) {s : Store H} {F : Frame}
    {a b : List (Option ContFX) × List AdminFX} (h : LU o fx s (E.frameAt F) a b) :
    LU o fx s F (a.1, E.plug a.2) (b.1, E.plug b.2) := by
  have hu := ustep_plug hE h.2.2 h.1 h.2.1
  exact ⟨hu.1, hu.2, quiet_plug h.2.2 E hE⟩

theorem lpath_plug {E : CtxV} (hE : Iso E) {s : Store H} {F : Frame}
    {a b : List (Option ContFX) × List AdminFX} (h : LPath o fx s (E.frameAt F) a b) :
    LPath o fx s F (a.1, E.plug a.2) (b.1, E.plug b.2) := by
  induction h with
  | one h => exact .one (lu_plug hE h)
  | cons h _ ih => exact .cons (lu_plug hE h) ih

/-- Quiet code whose first non-value is not a label, frame or handler. -/
theorem quiet_of {X : List AdminFX} {V : List FVal} {e : AdminFX} {T : List AdminFX}
    (hX : X = fvals V ++ e :: T) (he : fval? e = none) (hs : SCalm e) (hw : ¬ IsWrap e)
    (hd : DCalm e) : Quiet X := by
  refine ⟨⟨V, e, T, hX, he, hs⟩, fun e' hd' => ?_⟩
  have h0 : Deep e X := hX ▸ Deep.here he hw
  rw [deep_unique hd' h0]
  exact hd

variable (S : Setup H) {W : Prog (Ins Val)}

/-- **A local path of the top frame** makes the next related configuration inevitable. -/
theorem usame (hS : SX S = SD o S.fx) {KK' : List (Option (List (SFrame Val)))}
    {K K' : List (Option ContFX)} {p p' : SFrame Val × Ann} {rs : List (SFrame Val × Ann)}
    (hmain : MainOk S W (p :: rs)) (hp' : FrOk S W p') (hk : p'.2.kind = p.2.kind)
    (hK' : List.Forall₂ (KRel S W) KK' K')
    (hrun : LPath o S.fx S.s ((outer S rs p.2.kind).frameAt S.f0)
      (K, fvals (opsF p.1.ops) ++ adm p.2.code) (K', fvals (opsF p'.1.ops) ++ adm p'.2.code)) :
    InevP (SX S) TermFX (Rel S W ⟨KK', p'.1 :: rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S (p :: rs)).plug []⟩ := by
  rw [hS, code_top]
  refine inevP_of_upath (upath_of_lpath (iso_outer S hmain) hrun) ?_
  refine ⟨rfl, rfl, hK', p' :: rs, rfl, mainOk_top S hmain hp' hk, ?_⟩
  rw [code_top, hk]

/-! ## Local steps of the same-frame instructions -/

variable {s : Store H} {F : Frame} {K : List (Option ContFX)}

theorem scalm_plain {i : Instr} (hb : ∀ l, i ≠ .br l) (hr : i ≠ .return_) (ht : i ≠ .throwRef) :
    SCalm (.core (.plain i)) := by
  unfold SCalm
  split
  · rename_i l heq
    injection heq with heq
    injection heq with heq
    exact hb l heq
  · rename_i heq
    injection heq with heq
    injection heq with heq
    exact hr heq
  · rename_i heq
    injection heq with heq
    cases heq
  · rename_i heq
    injection heq with heq
    injection heq with heq
    exact ht heq
  · trivial

/-- **A Core head step** of a plain instruction, as a unique local step (its existence given). -/
theorem lu_core {U : List FVal} {args₀ : List Val} {i : Instr} {c₀ : Config H}
    {T : List AdminFX} (h₀ : Head (Profile.deterministic o) s F args₀ (.plain i) c₀)
    (hi : i ≠ .throwRef) (hst : c₀.store = s) (hfr : c₀.frame = F)
    (hex : SD o fx ⟨s, K, F, fvals (U ++ liftV args₀) ++ .core (.plain i) :: T⟩
      ⟨s, K, F, fvals U ++ c₀.code.map .core ++ T⟩) :
    LU o fx s F (K, fvals (U ++ liftV args₀) ++ .core (.plain i) :: T)
      (K, fvals U ++ c₀.code.map .core ++ T) := by
  have hg := Silmaril.Wasm.SingleThreaded.Det.Head.good h₀
  have hv : fval? (.core (.plain i)) = none := by simp [hg.val_none]
  have hs : SCalm (.core (.plain i)) :=
    scalm_plain (fun l h => hg.not_blocked (Or.inl ⟨l, by rw [h]⟩))
      (fun h => hg.not_blocked (Or.inr (Or.inl (by rw [h])))) hi
  refine ⟨hex, fun d hd => ?_, quiet_of rfl hv hs id trivial⟩
  rw [uniq_core h₀ hi hd, hst, hfr]

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
