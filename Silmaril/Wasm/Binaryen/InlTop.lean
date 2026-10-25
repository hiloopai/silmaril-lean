module

public import Silmaril.Wasm.Binaryen.InlI

@[expose] public section

/-! # The inlining simulation, site mode

The body of the left callee frame started at the site against the right inlined block
(`SiteR`). Only the callee's outermost label steps here; once the left side leaves it
(normally, by a branch to it, by `return`, a trap or an exception), the right side waits
until the left side leaves the frame (`AG.site`, handled in caller mode).
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen.InlS Silmaril.Wasm.SingleThreaded

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- The outermost callee label in site mode. -/
theorem top_label {k : Nat} {L : List (Option Val)} {bO X : List Admin}
    (IH : SimIH p P H (sizeOf [Admin.label k [] bO])) (hLI : LI p 0 bO X) {s t : Store H}
    {F : Frame} (hm : F.module = p.mi) (hL : L.length = p.base) (he : F.locals.length = p.ext)
    {c₀ : Config H} (hh : Det.Head P s F [] (.label k [] bO) c₀) (hSR : SR p s t) :
    Res p P (.top k L) ⟨c₀.store, c₀.frame, c₀.code⟩ ⟨t, ⟨L ++ F.locals, p.mi⟩, [.label k [] X]⟩
      (wL [.label k [] bO]) := by
  have hzero : ∀ {Y : List Admin}, SiteR p k Y X → wL Y < wL [.label k [] bO] →
      Res p P (.top k L) ⟨s, F, Y⟩ ⟨t, ⟨L ++ F.locals, p.mi⟩, [.label k [] X]⟩
        (wL [.label k [] bO]) := fun hs hw =>
    ⟨_, ⟨hm, hL, he, rfl, X, rfl, hs⟩, hSR, .inr ⟨rfl, hw⟩⟩
  have hflat : ∀ {vs : List Val} {i : Instr} {rest : List Admin},
      bO = vals vs ++ .plain i :: rest →
      InlineTy.retGood 0 i ∧ ∃ rest', X = vals vs ++ .plain (InlineTy.xform p.base 0 i) ::
        rest' := fun hb' => by
    subst hb'
    obtain ⟨y, rest', rfl, hy, -⟩ := LI.vals_cons_inv hLI
    cases hy with
    | plain h => exact ⟨h, rest', rfl⟩
  cases hh with
  | ctxtLabel h =>
    rename_i s' f' b₁
    have hsz : sizeOf bO < sizeOf [Admin.label k [] bO] := by
      have := Exec.Drv.sizeOf_label_body (n := k) (cont := []) (is := bO)
      simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec] at this ⊢
      omega
    obtain ⟨n₁, ⟨hm₁, -, he₁, hfr₁, hrel⟩, hsr, hprog⟩ :=
      IH (.i 0 L) ⟨s, F, bO⟩ ⟨s', f', b₁⟩ ⟨t, ⟨L ++ F.locals, p.mi⟩, X⟩ hsz h
        ⟨hm, hL, he, rfl, hLI⟩ hSR
    refine ⟨⟨n₁.store, n₁.frame, [.label k [] n₁.code]⟩,
      ⟨hm₁, hL, he₁, hfr₁, n₁.code, rfl, .a hrel⟩, hsr, ?_⟩
    rcases hprog with hp | ⟨rfl, hw⟩
    · exact .inl (tg_label hp k [])
    · exact .inr ⟨rfl, by simp at hw ⊢; omega⟩
  | labelVals hb' =>
    rename_i vs
    subst hb'
    obtain rfl := LI.vals_inv hLI
    exact hzero (.b vs) (by simp)
  | brLabelZero hb' hl' hn =>
    rename_i vs' vs l rest
    have e : vals vs' ++ vals vs ++ [Admin.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [e] at hb'
    obtain ⟨-, rest', hX⟩ := hflat hb'
    have hX' : X = vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest' := by
      rw [hX]; simp [InlineTy.xform]
    subst hX' hb'
    exact hzero (by simpa [expression] using SiteR.f (p := p) (vs' := vs') (rest := rest') hn hl')
      (by simp [expression, wL_append, wL_vals]; omega)
  | brLabelSucc hb' hl' =>
    rename_i vs l rest
    have e : vals vs ++ [Admin.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by
      simp
    rw [e] at hb'
    subst hb'
    have hg := SiteR.g (p := p) (k := k) (vs := vs) (l := labelPred l) (rest := []) (X := X)
    simp only [List.append_nil] at hg
    exact hzero hg (by simp [wL_append, wL_vals, wA]; omega)
  | returnCallRefLabel hb' hc' =>
    rename_i vs c₁ rest
    have e : vals vs ++ [c₁] ++ rest = vals vs ++ c₁ :: rest := by simp
    rw [e] at hb'
    subst hb'
    obtain ⟨y, rest', -, hy, -⟩ := LI.vals_cons_inv hLI
    unfold Admin.IsReturnCallRef at hc'
    split at hc'
    · cases hy with | plain h => exact h.elim
    · cases hy
    · exact hc'.elim
  | returnLabel hb' =>
    rename_i vs rest
    have e : vals vs ++ [Admin.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by
      simp
    rw [e] at hb'
    obtain ⟨-, rest', hX⟩ := hflat hb'
    have hX' : X = vals vs ++ [.plain (.br (InlineTy.xLabel 0))] ++ rest' := by
      rw [hX]; simp [InlineTy.xform]
    subst hX' hb'
    exact hzero .c (by simp [wL_append, wL_vals, wA]; omega)
  | throwRefLabel =>
    rename_i a
    obtain ⟨y, rest', rfl, hy, hr⟩ := LI.vals_cons_inv (vs := [.ref (.exn a)])
      (a := .plain .throwRef) (rest := []) hLI
    cases hy
    cases hr
    exact hzero (.e a) (by simp [wA])
  | trapLabel =>
    obtain ⟨y, rest', rfl, hy, hr⟩ := LI.vals_cons_inv (vs := []) (a := .trap) (rest := []) hLI
    cases hy
    cases hr
    exact hzero .d (by simp [wA])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss

end Silmaril.Wasm.Binaryen.InlR
