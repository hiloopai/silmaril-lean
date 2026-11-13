module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.ULocal

/-!
# Unique steps out of labels, frames and handlers, and lifting unique steps

* `uniq_labelVals`, `uniq_frameVals`, `uniq_handlerVals`: a label, frame or handler around
  values only;
* `uniq_brZero`, `uniq_brSucc`: a label whose first non-value is a branch;
* **`ustep_plug`**: a unique step of quiet code at the frame of the hole is a unique step of the
  code plugged into an isolated context.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append fvals_nil fvals_cons fval?_toAdmin
  fvals_append_cons_inj fvals_inj no_step_fvals')
open Silmaril.Wasm.SingleThreaded.Det (noHost Head)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}
  {s : Store H} {K : List (Option ContFX)} {F : Frame}

theorem fvals_ne_trap {vs : List FVal} : fvals vs ≠ [.core .trap] :=
  fun h => fvals_ne_cons (W := []) (e := .core .trap) (T := []) rfl (h.trans rfl)

theorem fvals_ne_throw {vs : List FVal} {a : Nat} : fvals vs ≠ cthrowing a :=
  fun h => fvals_ne_cons rfl (h.trans (throw_code a))

theorem fvals_ne_br {vs vs' vs'' : List FVal} {l : LabelIdx} {rest : List AdminFX} :
    fvals vs ≠ fvals vs' ++ fvals vs'' ++ [.core (.plain (.br l))] ++ rest :=
  fun h => fvals_ne_cons rfl (h.trans (br_code _ _ _ _))

theorem fvals_ne_ret {vs vs' vs'' : List FVal} {rest : List AdminFX} :
    fvals vs ≠ fvals vs' ++ fvals vs'' ++ [.core (.plain .return_)] ++ rest :=
  fun h => fvals_ne_cons rfl (h.trans (ret_code _ _ _))

theorem fvals_ne_plug {vs vs' : List FVal} {E : CtxV} {e : AdminFX} {T : List AdminFX}
    (he : fval? e = none) : fvals vs ≠ E.plug (fvals vs' ++ e :: T) := by
  intro h
  obtain ⟨V, a, T', hc, ha⟩ := plug_head E ⟨vs', e, T, rfl, he⟩
  exact fvals_ne_cons ha (h.trans hc)

theorem fvals_ne_switch {vs vs' : List FVal} {E : CtxV} {k : Nat} {ct : TypeIdx} {x : TagIdx} :
    fvals vs ≠ E.plug (fvals vs' ++ [.contRef k, .fx (.switch ct x)]) := by
  intro h
  have e : fvals vs' ++ [AdminFX.contRef k, .fx (.switch ct x)] =
      fvals (vs' ++ [.cont k]) ++ .fx (.switch ct x) :: [] := by simp [FVal.toAdmin]
  rw [e] at h
  exact fvals_ne_plug rfl h

theorem fhead_vals_label {V vs : List FVal} {n : Nat} {k : List InstrFX} {d₀ : ConfigFX H}
    (hh : FHead (Profile.deterministic o) fx s K F V (.label n k (fvals vs)) d₀) :
    V = [] ∧ d₀ = ⟨s, K, F, fvals vs⟩ := by
  generalize he : AdminFX.label n k (fvals vs) = e at hh
  cases hh with
  | ctxLabel h' =>
    injection he with _ _ hb
    subst hb
    exact absurd rfl (no_step_fvals' h' vs)
  | labelVals => injection he with _ _ hb; rw [fvals_inj hb]; exact ⟨rfl, rfl⟩
  | brLabelZero => injection he with _ _ hb; exact absurd hb fvals_ne_br
  | brLabelSucc => injection he with _ _ hb; exact absurd hb (fvals_ne_br (vs' := []) ∘ (by simpa using ·))
  | returnLabel => injection he with _ _ hb; exact absurd hb (fvals_ne_ret (vs' := []) ∘ (by simpa using ·))
  | trapLabel => injection he with _ _ hb; exact absurd hb fvals_ne_trap
  | throwLabel => injection he with _ _ hb; exact absurd hb fvals_ne_throw
  | _ => cases he

theorem uniq_labelVals {U vs : List FVal} {n : Nat} {k : List InstrFX} {T : List AdminFX}
    {d : ConfigFX H} (h : SD o fx ⟨s, K, F, fvals U ++ .label n k (fvals vs) :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ fvals vs ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, hd⟩ := local_inv rfl (by simp) (by simp) h
  have h₂ : V₂ = [] ∧ d₀ = ⟨s, K, F, fvals vs⟩ := fhead_vals_label hh
  have hU : U = V₁ := by simpa [h₂.1] using hV
  rw [hd, h₂.2, hU]

theorem fhead_vals_frame {V vs : List FVal} {n : Nat} {fi : Frame} {d₀ : ConfigFX H}
    (hh : FHead (Profile.deterministic o) fx s K F V (.frame n fi (fvals vs)) d₀) :
    V = [] ∧ d₀ = ⟨s, K, F, fvals vs⟩ := by
  generalize he : AdminFX.frame n fi (fvals vs) = e at hh
  cases hh with
  | ctxFrame h' =>
    injection he with _ _ hb
    subst hb
    exact absurd rfl (no_step_fvals' h' vs)
  | frameVals => injection he with _ _ hb; rw [fvals_inj hb]; exact ⟨rfl, rfl⟩
  | returnFrame => injection he with _ _ hb; exact absurd hb fvals_ne_ret
  | trapFrame => injection he with _ _ hb; exact absurd hb fvals_ne_trap
  | throwFrame => injection he with _ _ hb; exact absurd hb fvals_ne_throw
  | _ => cases he

theorem uniq_frameVals {U vs : List FVal} {n : Nat} {fi : Frame} {T : List AdminFX}
    {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals U ++ .frame n fi (fvals vs) :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ fvals vs ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, hd⟩ := local_inv rfl (by simp) (by simp) h
  have h₂ : V₂ = [] ∧ d₀ = ⟨s, K, F, fvals vs⟩ := fhead_vals_frame hh
  have hU : U = V₁ := by simpa [h₂.1] using hV
  rw [hd, h₂.2, hU]

theorem fhead_vals_handler {V vs : List FVal} {hs : List HClause} {d₀ : ConfigFX H}
    (hh : FHead (Profile.deterministic o) fx s K F V (.handler hs (fvals vs)) d₀) :
    V = [] ∧ d₀ = ⟨s, K, F, fvals vs⟩ := by
  generalize he : AdminFX.handler hs (fvals vs) = e at hh
  cases hh with
  | ctxHandler h' =>
    injection he with _ hb
    subst hb
    exact absurd rfl (no_step_fvals' h' vs)
  | handlerVals => injection he with _ hb; rw [fvals_inj hb]; exact ⟨rfl, rfl⟩
  | brHandler => injection he with _ hb; exact absurd hb (fvals_ne_br (vs' := []) ∘ (by simpa using ·))
  | returnHandler => injection he with _ hb; exact absurd hb (fvals_ne_ret (vs' := []) ∘ (by simpa using ·))
  | trapHandler => injection he with _ hb; exact absurd hb fvals_ne_trap
  | throwHandler => injection he with _ hb; exact absurd hb fvals_ne_throw
  | suspend => injection he with _ hb; exact absurd hb (fvals_ne_plug (T := []) rfl)
  | switch => injection he with _ hb; exact absurd hb fvals_ne_switch
  | _ => cases he

theorem uniq_handlerVals {U vs : List FVal} {hs : List HClause} {T : List AdminFX}
    {d : ConfigFX H} (h : SD o fx ⟨s, K, F, fvals U ++ .handler hs (fvals vs) :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ fvals vs ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, hd⟩ := local_inv rfl (by simp) (by simp) h
  have h₂ : V₂ = [] ∧ d₀ = ⟨s, K, F, fvals vs⟩ := fhead_vals_handler hh
  have hU : U = V₁ := by simpa [h₂.1] using hV
  rw [hd, h₂.2, hU]

/-- A branch at the first non-value does not step without its label. -/
theorem br_stuck {A : List FVal} {l : LabelIdx} {rest : List AdminFX} {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals A ++ .core (.plain (.br l)) :: rest⟩ d) : False := by
  obtain ⟨V₁, V₂, d₀, -, hh, -⟩ := local_inv rfl (by simp) (by simp) h
  generalize he : AdminFX.core (.plain (.br l)) = e at hh
  cases hh with
  | core h' =>
    injection he with he
    subst he
    exact (Silmaril.Wasm.SingleThreaded.Det.Head.good h').not_blocked (Or.inl ⟨l, rfl⟩)
  | dropCont => injection he with he; cases he
  | invoke hc => injection he with he; subst he; exact hc
  | _ => cases he

theorem br_eq {A B : List FVal} {l l' : LabelIdx} {rest rest' : List AdminFX}
    (hb : fvals A ++ .core (.plain (.br l)) :: rest = fvals B ++ .core (.plain (.br l')) :: rest') :
    A = B ∧ l = l' ∧ rest = rest' := by
  obtain ⟨h1, h2, h3⟩ := fvals_append_cons_inj hb rfl rfl
  have h4 : l = l' := by injection h2 with h2; injection h2 with h2; injection h2
  exact ⟨h1, h4, h3⟩

theorem br_ne_ret {A B : List FVal} {l : LabelIdx} {rest rest' : List AdminFX} :
    fvals A ++ .core (.plain (.br l)) :: rest ≠ fvals B ++ .core (.plain .return_) :: rest' :=
  fun hb => by cases (fvals_append_cons_inj hb rfl rfl).2.1

theorem br_ne_trap {A : List FVal} {l : LabelIdx} {rest : List AdminFX} :
    fvals A ++ .core (.plain (.br l)) :: rest ≠ [.core .trap] :=
  fun hb => by
    cases (fvals_append_cons_inj (hb.trans (show [AdminFX.core .trap] = fvals [] ++ .core .trap :: []
      from rfl)) rfl rfl).2.1

theorem br_ne_throw {A : List FVal} {l : LabelIdx} {rest : List AdminFX} {a : Nat} :
    fvals A ++ .core (.plain (.br l)) :: rest ≠ cthrowing a :=
  fun hb => by cases (fvals_append_cons_inj (hb.trans (throw_code a)) rfl rfl).2.1

/-- The outcome of a head step at a label whose first non-value is a branch. -/
def BrOut (s : Store H) (K : List (Option ContFX)) (F : Frame) (n : Nat) (k : List InstrFX)
    (A : List FVal) (l : LabelIdx) (d₀ : ConfigFX H) : Prop :=
  (l.toNat = 0 ∧ ∃ vs' vs, A = vs' ++ vs ∧ vs.length = n ∧
    d₀ = ⟨s, K, F, fvals vs ++ k.map InstrFX.toAdmin⟩) ∨
  (0 < l.toNat ∧ d₀ = ⟨s, K, F, fvals A ++ [.core (.plain (.br (labelPred l)))]⟩)

theorem fhead_br_label {V A : List FVal} {n : Nat} {k : List InstrFX} {l : LabelIdx}
    {rest : List AdminFX} {d₀ : ConfigFX H}
    (hh : FHead (Profile.deterministic o) fx s K F V
      (.label n k (fvals A ++ .core (.plain (.br l)) :: rest)) d₀) :
    V = [] ∧ BrOut s K F n k A l d₀ := by
  generalize he : AdminFX.label n k (fvals A ++ .core (.plain (.br l)) :: rest) = e at hh
  cases hh with
  | ctxLabel h' => injection he with _ _ hb; exact (br_stuck (hb ▸ h')).elim
  | labelVals => injection he with _ _ hb; exact (fvals_ne_cons (e := .core (.plain (.br l))) rfl hb.symm).elim
  | @brLabelZero _ _ n' k' vs₁ vs₂ l' rest' hl' hn' =>
    injection he with h1 h2 hb
    obtain ⟨hA, hll, -⟩ := br_eq (B := vs₁ ++ vs₂) (l' := l') (rest' := rest') (hb.trans (by simp))
    exact ⟨rfl, .inl ⟨hll ▸ hl', _, _, hA, h1 ▸ hn', by rw [h2]⟩⟩
  | @brLabelSucc _ _ n' k' vs₁ l' rest' hl' =>
    injection he with _ _ hb
    obtain ⟨hA, hll, -⟩ := br_eq (B := vs₁) (l' := l') (rest' := rest') (hb.trans (by simp))
    exact ⟨rfl, .inr ⟨hll ▸ hl', by rw [hA, hll]⟩⟩
  | @returnLabel _ _ n' k' vs₁ rest' =>
    injection he with _ _ hb
    exact (br_ne_ret (B := vs₁) (rest' := rest') (hb.trans (by simp))).elim
  | trapLabel => injection he with _ _ hb; exact (br_ne_trap hb).elim
  | throwLabel => injection he with _ _ hb; exact (br_ne_throw hb).elim
  | _ => cases he

theorem uniq_brZero {U A vs : List FVal} {n : Nat} {k : List InstrFX} {l : LabelIdx}
    {rest T : List AdminFX} (hl : l.toNat = 0) (hn : vs.length = n) {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals U ++
      .label n k (fvals (A ++ vs) ++ .core (.plain (.br l)) :: rest) :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ fvals vs ++ k.map InstrFX.toAdmin ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, hd⟩ := local_inv rfl (by simp) (by simp) h
  obtain ⟨hV₂, hout⟩ := fhead_br_label hh
  have hU : U = V₁ := by simpa [hV₂] using hV
  rcases hout with ⟨-, vs', vs₂, hA, hn₂, hd₀⟩ | ⟨hl', -⟩
  · have hvs : vs = vs₂ := (List.append_inj' hA (by omega)).2
    rw [hd, hd₀, hU, hvs]
    simp
  · omega

theorem uniq_brSucc {U A : List FVal} {n : Nat} {k : List InstrFX} {l : LabelIdx}
    {rest T : List AdminFX} (hl : 0 < l.toNat) {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals U ++
      .label n k (fvals A ++ .core (.plain (.br l)) :: rest) :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ fvals A ++ [.core (.plain (.br (labelPred l)))] ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, hd⟩ := local_inv rfl (by simp) (by simp) h
  obtain ⟨hV₂, hout⟩ := fhead_br_label hh
  have hU : U = V₁ := by simpa [hV₂] using hV
  rcases hout with ⟨hl', -⟩ | ⟨-, hd₀⟩
  · omega
  · rw [hd, hd₀, hU]
    simp

/-- **A unique step of quiet code lifts** to a unique step under an isolated context. -/
theorem ustep_plug {E : CtxV} (hE : Iso E) {s s' : Store H} {K K' : List (Option ContFX)}
    {f : Frame} {X X' : List AdminFX} (hq : Quiet X)
    (hs : SD o fx ⟨s, K, E.frameAt f, X⟩ ⟨s', K', E.frameAt f, X'⟩)
    (hu : ∀ d, SD o fx ⟨s, K, E.frameAt f, X⟩ d → d = ⟨s', K', E.frameAt f, X'⟩) :
    UStep (SD o fx) ⟨s, K, f, E.plug X⟩ ⟨s', K', f, E.plug X'⟩ := by
  refine ⟨Silmaril.Proofs.Wasm.Models.FXAsyncFX.step_lift E hs, fun d hd => ?_⟩
  obtain ⟨c', hc', rfl⟩ := step_plug_inv hq E hE s K f d hd
  rw [hu c' hc', liftC_frameAt]

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
