module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inv

/-!
# Statements without labels on Core 3.0

`SRes`: what the Core run of a statement from `s` that `bexec` ends in `(o, s')` gives: the
branch depth and returned value are `i32`s, and from any `Rel`-related configuration, under any
code after it, `HStep`s reach a configuration related to `s'` whose code is `outCode o`, then
code the statement did not reach (`junk`, empty when it ends normally), then the code after it.
`SRun S f`: every run of `S` with loop fuel `f` has `SRes`. Proved here for `nop`, `local.set`,
`global.set`, `i32.store8`, `memory.copy`, `br`, `br_if`, `return` and built-in calls.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd mcopy)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix eCode sCode ma0)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma nl : Nat}

/-- **What the Core run of a statement gives.** -/
def SRes (Pf : Profile) (hb : BI → H) (ma nl : Nat) (cs : Store H) (F : Frame) (S : S) (s : DSt)
    (o : Out) (s' : DSt) : Prop :=
  (∀ k, o = .br k → k < M32) ∧ (∀ v, o = .ret v → v < M32) ∧
    ∀ rest : List Admin, ∃ (cs' : Store H) (F' : Frame) (junk : List Admin),
      Rel hb nl ma cs' F' s' ∧ F'.module = F.module ∧ cs'.funcs = cs.funcs ∧ (o = .norm → junk = []) ∧
      HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, (sCode S).map Admin.plain ++ rest⟩)
        ((s'.st, s'.rp), ⟨cs', F', outCode o ++ junk ++ rest⟩)

/-- Every checked run of `S` (loop fuel `f`) is a Core run. -/
def SRun (Pf : Profile) (hb : BI → H) (ma nl : Nat) (S : S) (f : Nat) : Prop :=
  ∀ {s : DSt} {o : Out} {s' : DSt} {cs : Store H} {F : Frame}, bexec nl S f s = some (o, s') →
    Rel hb nl ma cs F s → SRes Pf hb ma nl cs F S s o s'

theorem sres_norm {cs cs' : Store H} {F F' : Frame} {S : S} {s s' : DSt}
    (hR : Rel hb nl ma cs' F' s') (hF : F'.module = F.module) (hfs : cs'.funcs = cs.funcs)
    (hrun : ∀ rest : List Admin, HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, (sCode S).map Admin.plain ++ rest⟩)
      ((s'.st, s'.rp), ⟨cs', F', rest⟩)) :
    SRes Pf hb ma nl cs F S s .norm s' :=
  ⟨(fun _ h => by cases h), (fun _ h => by cases h), fun rest =>
    ⟨cs', F', [], hR, hF, hfs, fun _ => rfl, by simpa [outCode] using hrun rest⟩⟩

theorem split2 (xs ys : List Instr) (rest : List Admin) :
    (xs ++ ys).map Admin.plain ++ rest = stackA [] ++ (xs.map Admin.plain ++ (ys.map Admin.plain ++ rest)) := by
  simp [stackA_nil]

theorem run_nop {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) :
    SRes Pf hb ma nl cs F .nop s .norm s :=
  sres_norm h rfl rfl fun rest => step_app (.parametric .nop) rest

theorem run_lset {cs : Store H} {F : Frame} {s s' : DSt} {o : Out} {i f : Nat} {e : E}
    (h : Rel hb nl ma cs F s) (hx : bexec nl (.lset i e) f s = some (o, s')) :
    SRes Pf hb ma nl cs F (.lset i e) s o s' := by
  obtain ⟨hi, v, hv, rfl, rfl⟩ := bexec_lset hx
  obtain ⟨hvl, re⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h e hv
  obtain ⟨hix, hR⟩ := rel_setL h hi hvl
  refine sres_norm hR rfl rfl fun rest => ?_
  show HSteps Pf hb ma _ (_, ⟨cs, _, rest⟩)
  have e₀ := split2 (eCode e) [Instr.localSet (ix i)] rest
  have r₂ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA [w v] ++ .plain (.localSet (ix i)) :: rest⟩)
      ((s.st, s.rp), ⟨cs, F.setLocal (ix i) (Val.i32 (w v)), rest⟩) := by
    simpa [stackA_nil] using r_lset (Pf := Pf) (hb := hb) (ma := ma) (q := (s.st, s.rp)) (s := cs) hix [] rest
  exact e₀ ▸ (re [] _).trans r₂

theorem run_gset {cs : Store H} {F : Frame} {s s' : DSt} {o : Out} {i f : Nat} {e : E}
    (h : Rel hb nl ma cs F s) (hx : bexec nl (.gset i e) f s = some (o, s')) :
    SRes Pf hb ma nl cs F (.gset i e) s o s' := by
  obtain ⟨hi, v, hv, rfl, rfl⟩ := bexec_gset hx
  obtain ⟨hvl, re⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h e hv
  obtain ⟨a, gi, hga, hR⟩ := rel_setG Pf h hi hvl
  refine sres_norm hR rfl rfl fun rest => ?_
  have e₀ := split2 (eCode e) [Instr.globalSet (ix i)] rest
  have r₂ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA [w v] ++ .plain (.globalSet (ix i)) :: rest⟩)
      ((s.st, s.rp), ⟨cs.setGlobal a (Val.i32 (w v)), F, rest⟩) := by
    simpa [stackA_nil] using r_gset (Pf := Pf) (hb := hb) (ma := ma) (q := (s.st, s.rp)) hga [] rest
  exact e₀ ▸ (re [] _).trans r₂

theorem split3 (xs ys zs : List Instr) (rest : List Admin) :
    (xs ++ ys ++ zs).map Admin.plain ++ rest =
      stackA [] ++ (xs.map Admin.plain ++ (ys.map Admin.plain ++ (zs.map Admin.plain ++ rest))) := by
  simp [stackA_nil]

theorem split4 (xs ys zs us : List Instr) (rest : List Admin) :
    (xs ++ ys ++ zs ++ us).map Admin.plain ++ rest =
      stackA [] ++ (xs.map Admin.plain ++ (ys.map Admin.plain ++ (zs.map Admin.plain ++
        (us.map Admin.plain ++ rest)))) := by
  simp [stackA_nil]

theorem run_st8 {cs : Store H} {F : Frame} {s s' : DSt} {o : Out} {f : Nat} {a v : E}
    (h : Rel hb nl ma cs F s) (hx : bexec nl (.st8 a v) f s = some (o, s')) :
    SRes Pf hb ma nl cs F (.st8 a v) s o s' := by
  obtain ⟨x, y, hxv, hyv, hxm, rfl, rfl⟩ := bexec_st8 hx
  obtain ⟨-, ra⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h a hxv
  obtain ⟨-, rv⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h v hyv
  obtain ⟨cs₁, hm, hg, hf, rs⟩ := memR_store (Pf := Pf) (hb := hb) (q := (s.st, s.rp)) h.memR
    (arg := ma0) rfl hxm y
  have hR : Rel hb nl ma cs₁ F { s with m := upd s.m x (y % 256) } := rel_mem h hm hg hf rfl rfl
  refine sres_norm hR rfl hf fun rest => ?_
  have e₀ := split3 (eCode a) (eCode v) [Instr.intStore .i32 (some .i8) (ix 0) ma0] rest
  have r₃ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA [w y, w x] ++
      .plain (.intStore .i32 (some .i8) (ix 0) ma0) :: rest⟩) ((s.st, s.rp), ⟨cs₁, F, rest⟩) := by
    simpa [stackA_nil] using rs [] rest
  exact e₀ ▸ (ra [] _).trans ((rv [w x] _).trans r₃)

theorem run_mcopy {cs : Store H} {F : Frame} {s s' : DSt} {o : Out} {f : Nat} {d src n : E}
    (h : Rel hb nl ma cs F s) (hx : bexec nl (.mcopy d src n) f s = some (o, s')) :
    SRes Pf hb ma nl cs F (.mcopy d src n) s o s' := by
  obtain ⟨x, y, z, hxv, hyv, hzv, hle, hb', rfl, rfl⟩ := bexec_mcopy hx
  obtain ⟨-, rd⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h d hxv
  obtain ⟨-, rs⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h src hyv
  obtain ⟨-, rn⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h n hzv
  obtain ⟨cs₁, hm, hg, hf, rc⟩ := memR_copy (Pf := Pf) (hb := hb) (q := (s.st, s.rp)) z h.memR hle hb'
  have hR : Rel hb nl ma cs₁ F { s with m := mcopy s.m x y z } := rel_mem h hm hg hf rfl rfl
  refine sres_norm hR rfl hf fun rest => ?_
  have e₀ := split4 (eCode d) (eCode src) (eCode n) [Instr.memoryCopy (ix 0) (ix 0)] rest
  have r₄ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA [w z, w y, w x] ++
      .plain (.memoryCopy (ix 0) (ix 0)) :: rest⟩) ((s.st, s.rp), ⟨cs₁, F, rest⟩) := by
    simpa [stackA_nil] using rc [] rest
  exact e₀ ▸ (rd [] _).trans ((rs [w x] _).trans ((rn [w y, w x] _).trans r₄))

theorem run_br {cs : Store H} {F : Frame} {s s' : DSt} {o : Out} {f k : Nat}
    (h : Rel hb nl ma cs F s) (hx : bexec nl (.br k) f s = some (o, s')) :
    SRes Pf hb ma nl cs F (.br k) s o s' := by
  obtain ⟨hk, rfl, rfl⟩ := bexec_br hx
  refine ⟨(fun k' hk' => by cases hk'; exact hk), (fun _ h' => by cases h'), fun rest => ⟨cs, F, [], h, rfl, rfl,
    (fun h' => by cases h'), ?_⟩⟩
  exact Relation.ReflTransGen.refl

theorem run_ret {cs : Store H} {F : Frame} {s s' : DSt} {o : Out} {f : Nat} {e : E}
    (h : Rel hb nl ma cs F s) (hx : bexec nl (.ret e) f s = some (o, s')) :
    SRes Pf hb ma nl cs F (.ret e) s o s' := by
  obtain ⟨v, hv, rfl, rfl⟩ := bexec_ret hx
  obtain ⟨hvl, re⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h e hv
  refine ⟨(fun _ h' => by cases h'), (fun v' hv' => by cases hv'; exact hvl), fun rest =>
    ⟨cs, F, [], h, rfl, rfl, (fun h' => by cases h'), ?_⟩⟩
  have e₀ := split2 (eCode e) [Instr.return_] rest
  have e₁ : stackA [w v] ++ (Admin.plain .return_ :: rest) = outCode (.ret v) ++ [] ++ rest := by
    simp [outCode, stackA_one]
  exact e₀ ▸ e₁ ▸ re [] _

theorem w_ne_zero {v : Nat} (hv : v < M32) (h0 : v ≠ 0) : w v ≠ 0 := by
  intro h
  have h' : (w v).toNat = 0 := by rw [h]; rfl
  rw [w_toNat hv] at h'
  exact h0 h'

theorem run_brIf {cs : Store H} {F : Frame} {s s' : DSt} {o : Out} {f k : Nat} {c : E}
    (h : Rel hb nl ma cs F s) (hx : bexec nl (.brIf k c) f s = some (o, s')) :
    SRes Pf hb ma nl cs F (.brIf k c) s o s' := by
  obtain ⟨hk, v, hv, rfl, rfl⟩ := bexec_brIf hx
  obtain ⟨hvl, re⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h c hv
  have e₀ (rest : List Admin) := split2 (eCode c) [Instr.brIf (ix k)] rest
  by_cases h0 : v ≠ 0
  · show SRes Pf hb ma nl cs F (.brIf k c) s (if v ≠ 0 then Out.br k else Out.norm) s
    rw [ite_t h0]
    refine ⟨(fun k' hk' => by cases hk'; exact hk), (fun _ h' => by cases h'), fun rest =>
      ⟨cs, F, [], h, rfl, rfl, (fun h' => by cases h'), ?_⟩⟩
    have r₂ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA [w v] ++ .plain (.brIf (ix k)) :: rest⟩)
        ((s.st, s.rp), ⟨cs, F, outCode (.br k) ++ [] ++ rest⟩) := by
      exact step_app (Pf := Pf) (hb := hb) (ma := ma) (q := (s.st, s.rp))
        (Step.brIfTrue (s := cs) (f := F) (l := ix k) (w_ne_zero hvl h0)) rest
    exact (e₀ rest) ▸ (re [] _).trans r₂
  · show SRes Pf hb ma nl cs F (.brIf k c) s (if v ≠ 0 then Out.br k else Out.norm) s
    rw [ite_f h0]
    have hv0 : v = 0 := Classical.not_not.mp h0
    refine sres_norm h rfl rfl fun rest => ?_
    have r₂ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA [w v] ++ .plain (.brIf (ix k)) :: rest⟩)
        ((s.st, s.rp), ⟨cs, F, rest⟩) := by
      rw [hv0]
      exact step_app (Pf := Pf) (hb := hb) (ma := ma) (q := (s.st, s.rp))
        (Step.brIfFalse (s := cs) (f := F) (l := ix k)) rest
    exact (e₀ rest) ▸ (re [] _).trans r₂

theorem run_call {cs : Store H} {F : Frame} {s s' : DSt} {o : Out} {f : Nat} {b : BI}
    {args : List E} {dst : List Nat} (h : Rel hb nl ma cs F s)
    (hx : bexec nl (.call b args dst) f s = some (o, s')) :
    SRes Pf hb ma nl cs F (.call b args dst) s o s' := by
  obtain ⟨rfl, -⟩ := call_run (Pf := Pf) h hx []
  refine ⟨(fun _ h' => by cases h'), (fun _ h' => by cases h'), fun rest => ?_⟩
  obtain ⟨-, cs', F', hR, hF, hfs, hrun⟩ := call_run (Pf := Pf) h hx rest
  exact ⟨cs', F', [], hR, hF, hfs, fun _ => rfl, by simpa [outCode] using hrun⟩

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
