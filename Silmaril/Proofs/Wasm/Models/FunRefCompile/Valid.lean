module

public import Silmaril.Wasm.Models.FunRefCompile.Defs
public import Silmaril.Wasm.Models.FunCompile.Thms

/-!
# Compiling FunRef: the compiled module validates

The typing derivation of `Silmaril.Proofs.Wasm.Models.FunCompile.Valid`, extended by the cell
instructions (`ty_newCell`, `ty_castCell`, `ty_getCell`, `ty_setCell`): `ty_compile` (the code of
every well-typed FunRef term has type `[] → [anyref]`), `funcOk_main` and `moduleValid`.

New.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FunRefCompile

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.FunRefCompile
open Silmaril.Wasm.Models.FunRef (Tm Prog HasTy)
open Silmaril.Wasm.Models.FunCompile (dBox dMain boxIdx lx fx unbox getField anyref)
open Silmaril.Proofs.Wasm.Models.FunCompile (anyC seqP consP subP HasTypes Good ty_localGet
  ty_localSet ty_constBox ty_unbox ty_castBox ty_getBox ty_newBox ty_arith ty_cmp ty_if frame1
  ty_getField ok_anyC ok_i32 depth_le_left depth_le_right localsOk bodyCtx bodyCtx_good
  ty_prologue fx_toNat)

/-! ## Cells -/

section Cells

variable {C : Context}

/-- The field types of `$cell`, closed. -/
def cellFieldsC : Ty (.list .field) := .cons (.field .var (.val anyC)) .nil

/-- The reference to a cell. -/
def cellT : CValType := .refT false (Ty.defHeap dCell)

theorem type_cellC (hΔ : HasTypes C modTypes) : C.type? cellIdx = some dCell := by
  simp [Context.type?, hΔ.types, modTypes, cellIdx, Idx.toNat]

theorem ty_newCell (hΔ : HasTypes C modTypes) :
    InstrsOk C [.structNew cellIdx] (.plain [anyC] [anyC]) := by
  have h := RefInstrOk.structNew (C := C) (fs := cellFieldsC) (type_cellC hΔ) ⟨rfl⟩
  exact subP (.instr (.reference h)) (by rw [hΔ]; decide) (by rw [hΔ]; decide)
    (by rw [hΔ]; decide) (by rw [hΔ]; decide)

theorem ty_castCell (hΔ : HasTypes C modTypes) :
    InstrOk C (.refCast cellRef) (.plain [anyC] [cellT]) := by
  have hr : C.closeRef cellRef = .ref false (Ty.defHeap dCell) := by
    simp only [Context.closeRef, hΔ.types]; rfl
  have h := RefInstrOk.refCast (C := C) (rt := cellRef) (rt' := .ref true (.abs .any))
    (TyOk.check_sound (by rw [hΔ, hr]; decide)) (TyOk.check_sound (by rw [hΔ]; decide))
    (Sub.check_sound (by rw [hΔ, hr]; decide))
  rw [hr] at h
  exact .reference h

theorem ty_getCell (hΔ : HasTypes C modTypes) :
    InstrsOk C [.structGet none cellIdx (fx 0)] (.plain [cellT] [anyC]) := by
  have h := RefInstrOk.structGet (C := C) (sx := none) (fs := cellFieldsC) (type_cellC hΔ) ⟨rfl⟩
    (show cellFieldsC.toList[(fx 0).toNat]? = some (.field .var (.val anyC)) from rfl) rfl
  exact subP (.instr (.reference h)) (by rw [hΔ]; decide) (by rw [hΔ]; decide)
    (by rw [hΔ]; decide) (by rw [hΔ]; decide)

theorem ty_setCell (hΔ : HasTypes C modTypes) :
    InstrsOk C [.structSet cellIdx (fx 0)] (.plain [cellT, anyC] []) := by
  have h := RefInstrOk.structSet (C := C) (fs := cellFieldsC) (type_cellC hΔ) ⟨rfl⟩
    (show cellFieldsC.toList[(fx 0).toNat]? = some (.field .var (.val anyC)) from rfl)
  exact subP (.instr (.reference h)) (by rw [hΔ]; decide) (by rw [hΔ]; decide)
    (by rw [hΔ]; decide) (by rw [hΔ]; decide)

end Cells

/-- The context of the module's code: types `dBox :: [dMain, dCell]`. -/
abbrev GoodR (C : Context) (n : Nat) : Prop := Good C [dMain, dCell] n

theorem GoodR.types {C : Context} {n : Nat} (h : GoodR C n) : HasTypes C modTypes := h.1

/-- The code of a `case` branch. -/
theorem ty_branch {C : Context} {d : Nat} {t : Tm} (hg : GoodR C (d + 1))
    (ht : InstrsOk C (compile (d + 1) t) (.plain [] [anyC])) :
    InstrsOk C (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) t)
      (.plain [] [anyC]) :=
  seqP (ty_getField hg (by omega) le_rfl (by omega))
    (seqP (ty_localSet hg.1 (hg.local (by omega) le_rfl) (hg.lim le_rfl)) ht)

/-- The code of `case`, from the code of its parts. -/
theorem ty_case {Γ : List FunRef.Ty} {σ τ : FunRef.Ty} {e l r : Tm}
    (ihe : ∀ {d : Nat} {C : Context} , Γ.length = d → GoodR C (d + e.depth) →
      InstrsOk C (compile d e) (.plain [] [anyC]))
    (ihl : ∀ {d : Nat} {C : Context} , (σ :: Γ).length = d → GoodR C (d + l.depth) →
      InstrsOk C (compile d l) (.plain [] [anyC]))
    (ihr : ∀ {d : Nat} {C : Context} , (τ :: Γ).length = d → GoodR C (d + r.depth) →
      InstrsOk C (compile d r) (.plain [] [anyC])) {d : Nat} {C : Context}
    (hd : Γ.length = d) (hg : GoodR C (d + (Tm.case e l r).depth)) :
    InstrsOk C (compile d (.case e l r)) (.plain [] [anyC]) := by
  have hdep : (Tm.case e l r).depth = max e.depth (max l.depth r.depth + 1) := rfl
  have hm : max l.depth r.depth + 1 ≤ max e.depth (max l.depth r.depth + 1) := le_max_right _ _
  have hml : l.depth ≤ max l.depth r.depth := le_max_left _ _
  have hmr : r.depth ≤ max l.depth r.depth := le_max_right _ _
  have hl : InstrsOk (C.withLabel [anyC])
      (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) l)
      (.plain [] [anyC]) := ty_branch (d := d) ((hg.mono (by omega)).withLabel [anyC])
    (ihl (d := d + 1) (by simp [hd]) ((hg.mono (by omega)).withLabel [anyC]))
  have hr : InstrsOk (C.withLabel [anyC])
      (getField (d + 1) 1 ++ .localSet (lx (d + 1)) :: compile (d + 1) r)
      (.plain [] [anyC]) := ty_branch (d := d) ((hg.mono (by omega)).withLabel [anyC])
    (ihr (d := d + 1) (by simp [hd]) ((hg.mono (by omega)).withLabel [anyC]))
  exact seqP (seqP (seqP (ihe hd (hg.mono depth_le_left))
    (seqP (ty_localSet hg.1 (hg.local (by omega) (by omega)) (hg.lim (by omega)))
      (ty_getField hg (by omega) (by omega) (by omega)))) (ty_unbox hg.1))
    (ty_if hg.1 hr hl)

/-- **The code of every well-typed FunRef term has type `[] → [anyref]`.** -/
theorem ty_compile {Γ : List FunRef.Ty} {e : Tm} {τ : FunRef.Ty} (h : HasTy Γ e τ) :
    ∀ {d : Nat} {C : Context}, Γ.length = d → GoodR C (d + e.depth) →
      InstrsOk C (compile d e) (.plain [] [anyC]) := by
  induction h with
  | var hi =>
    intro d C hd hg
    have hlt : _ < d := hd ▸ (List.getElem?_eq_some_iff.1 hi).1
    exact ty_localGet (hg.local (by omega) (by omega)) (hg.lim (by omega))
  | int n => exact fun _ hg => ty_constBox hg.1 _
  | bool b => exact fun _ hg => ty_constBox hg.1 _
  | arith op _ _ iha ihb =>
    exact fun hd hg => seqP (seqP (seqP (seqP (iha hd (hg.mono depth_le_left)) (ty_unbox hg.1))
      (frame1 hg.1 (ihb hd (hg.mono depth_le_right)) (ok_i32 _))) (frame1 hg.1 (ty_unbox hg.1)
        (ok_i32 _))) (ty_arith hg.1 op)
  | cmp op _ _ iha ihb =>
    exact fun hd hg => seqP (seqP (seqP (seqP (iha hd (hg.mono depth_le_left)) (ty_unbox hg.1))
      (frame1 hg.1 (ihb hd (hg.mono depth_le_right)) (ok_i32 _))) (frame1 hg.1 (ty_unbox hg.1)
        (ok_i32 _))) (ty_cmp hg.1 op)
  | ite _ _ _ ihc iht ihe =>
    exact fun hd hg => seqP (seqP (ihc hd (hg.mono depth_le_left)) (ty_unbox hg.1))
      (ty_if hg.1 (iht hd ((hg.mono (le_trans depth_le_left depth_le_right)).withLabel _))
        (ihe hd ((hg.mono (le_trans depth_le_right depth_le_right)).withLabel _)))
  | @let_ Γ a b σ τ _ _ iha ihb =>
    intro d C hd hg
    have hdep : (Tm.let_ a b).depth = max a.depth (b.depth + 1) := rfl
    have hm : b.depth + 1 ≤ max a.depth (b.depth + 1) := le_max_right _ _
    have hb : GoodR C (d + 1 + b.depth) := hg.mono (by omega)
    exact seqP (iha hd (hg.mono depth_le_left))
      (seqP (ty_localSet hg.1 (hg.local (by omega) (by omega)) (hg.lim (by omega)))
        (ihb (by simp [hd]) hb))
  | pair _ _ iha ihb =>
    exact fun hd hg => seqP (seqP (iha hd (hg.mono depth_le_left))
      (frame1 hg.1 (ihb hd (hg.mono depth_le_right)) (ok_anyC _))) (ty_newBox hg.1)
  | fst _ ih =>
    exact fun hd hg => seqP (ih hd hg) (consP (ty_castBox hg.1) (ty_getBox hg.1 (by omega)))
  | snd _ ih =>
    exact fun hd hg => seqP (ih hd hg) (consP (ty_castBox hg.1) (ty_getBox hg.1 (by omega)))
  | @inl Γ e σ τ _ ih =>
    intro d C hd hg
    show InstrsOk C ([.intConst .i32 0, .refI31] ++ (compile d e ++ [.structNew boxIdx])) _
    exact seqP (ty_constBox hg.1 _) (seqP (frame1 hg.1 (ih hd hg) (ok_anyC _)) (ty_newBox hg.1))
  | @inr Γ e σ τ _ ih =>
    intro d C hd hg
    show InstrsOk C ([.intConst .i32 1, .refI31] ++ (compile d e ++ [.structNew boxIdx])) _
    exact seqP (ty_constBox hg.1 _) (seqP (frame1 hg.1 (ih hd hg) (ok_anyC _)) (ty_newBox hg.1))
  | case _ _ _ ihe ihl ihr => exact fun hd hg => ty_case ihe ihl ihr hd hg
  | ref _ ih => exact fun hd hg => seqP (ih hd hg) (ty_newCell hg.1)
  | get _ ih =>
    exact fun hd hg => seqP (ih hd hg) (consP (ty_castCell hg.1) (ty_getCell hg.1))
  | set _ _ iha ihb =>
    exact fun hd hg => seqP (seqP (iha hd (hg.mono depth_le_left))
      (consP (ty_castCell hg.1) (frame1 hg.1 (ihb hd (hg.mono depth_le_right)) rfl)))
      (seqP (ty_setCell hg.1) (ty_constBox hg.1 _))

/-! ## Functions and modules -/

/-- **The body of `main` has type `[] → [i32]`.** -/
theorem ty_mainBody {C : Context} (hΔ : HasTypes C modTypes) {p : Prog} (hp : p.WellTyped)
    (hfit : p.Fits) : ExprOk (bodyCtx C (p.body.depth + 1)) (mainBody p) [.i32] := by
  have hg : GoodR (bodyCtx C (p.body.depth + 1)) (p.body.depth + 1) :=
    bodyCtx_good hΔ (by unfold Prog.Fits at hfit; omega)
  have hc : InstrsOk (bodyCtx C (p.body.depth + 1)) (compile 1 p.body) (.plain [] [anyC]) :=
    ty_compile hp.1 rfl (hg.mono (by omega))
  exact seqP (seqP (ty_prologue hg (by omega)) hc) (ty_unbox hg.1)

/-- `Func_ok` of `main`. -/
theorem funcOk_main {C : Context} (hΔ : HasTypes C modTypes) {p : Prog} (hp : p.WellTyped)
    (hfit : p.Fits) : FuncOk C (funcOf p) dMain := by
  have hd : C.type? (funcOf p).type = some dMain := by
    simp [Context.type?, hΔ.types, funcOf, modTypes, Idx.toNat]
  exact .mk (ps := .cons .i32 .nil) (rs := .cons .i32 .nil) hd ⟨rfl⟩ (localsOk hΔ _)
    (ty_mainBody hΔ hp hfit)

/-- The context `C` of `Module_ok` for a compiled module. -/
def modCtx (p : Prog) : Context :=
  moduleCtx (moduleOf p) (moduleCtx' (moduleOf p) modTypes [] [dMain]) [] [] [] [] []

theorem typesOk : TypesOk {} recTypes modTypes :=
  typesCheck?_sound (fun _ _ _ h => RecTypeOkAt.check_sound h) (by decide)

/-- **The compiled module of an accepted FunRef program validates.** -/
theorem moduleValid {p : Prog} (hp : p.WellTyped) (hfit : p.Fits) :
    ModuleValid (moduleOf p) :=
  ⟨⟨[], [.func dMain]⟩, ModuleOk.mk (fdts := [dMain]) (jts := []) (gts := []) (tts := [])
    (rts := []) (C' := moduleCtx' (moduleOf p) modTypes [] [dMain]) (C := modCtx p)
    typesOk .nil rfl rfl .nil .nil (fun _ h => absurd h List.not_mem_nil) .nil
    (.cons (funcOk_main (C := modCtx p) rfl hp hfit) .nil) (fun _ h => absurd h List.not_mem_nil)
    .nil (fun _ h => by cases h) (.cons (.func rfl) .nil) (List.nodup_singleton "main")⟩

end Silmaril.Proofs.Wasm.Models.FunRefCompile
