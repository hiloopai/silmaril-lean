module

public import Silmaril.Proofs.Wasm.Models.FXBindT.Incl

/-!
# Inverting `cont.bind` under `StepFX'` and `StepFXT` (no host calls)

A step of `fvals V ++ ref.cont n :: cont.bind ct ct' :: T` is `cont.bind` (or a trap on a
consumed continuation) with a split `V = V₁ ++ V₂`: `V₂` is bound, `V₁` stays on the stack.

* `step_contBind'` (`StepFX'`): every split may occur;
* `step_contBindT` (`StepFXT`): the bound part has the arity of the types,
  `BindArity f.module ct ct' |V₂|`.

The proofs follow `step_resume'` (`Silmaril.Proofs.Wasm.Models.FXVRuns`): induction on the step,
`ctxt-instrs` by `seq_splitF`, the other rules by comparing first non-values.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBindT

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXBindT
open Silmaril.Proofs.Wasm.Models.FXVRuns (seq_splitF no_step_fvals' fx_head_stuck suffix_concat
  fvals_append_cons_inj invoke_ne_fx)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- The outcomes of a step at `cont.bind`, with the side condition `A` on the bound count. -/
def BindRes' (A : Nat → Prop) (s : Store H) (K : List (Option ContFX)) (f : Frame)
    (V : List FVal) (n : Nat) (T : List AdminFX) (y : ConfigFX H) : Prop :=
  ∃ V₁ V₂, V = V₁ ++ V₂ ∧ A V₂.length ∧
    ((∃ C, K[n]? = some (some C) ∧
        y = ⟨s, K.set n none ++ [some ⟨fun c => C.plug (fvals V₂ ++ c)⟩], f,
          fvals V₁ ++ .contRef K.length :: T⟩) ∨
      (K[n]? = some none ∧ y = ⟨s, K, f, fvals V₁ ++ .core .trap :: T⟩))

/-- The conclusion of the inversions, for the side condition `A f ct ct'`. -/
abbrev BindInv (A : Frame → TypeIdx → TypeIdx → Nat → Prop) (x y : ConfigFX H) : Prop :=
  ∀ V n ct ct' T, x.code = fvals V ++ .contRef n :: .fx (.contBind ct ct') :: T →
    BindRes' (A x.frame ct ct') x.store x.conts x.frame V n T y

theorem bindRes'_seq {A : Nat → Prop} {s s' : Store H} {K K' : List (Option ContFX)}
    {f f' : Frame} {V : List FVal} {n : Nat} {T es' : List AdminFX} (vs : List FVal)
    (rest : List AdminFX) (h : BindRes' A s K f V n T ⟨s', K', f', es'⟩) :
    BindRes' A s K f (vs ++ V) n (T ++ rest) ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  obtain ⟨V₁, V₂, rfl, hA, h⟩ := h
  refine ⟨vs ++ V₁, V₂, by simp, hA, ?_⟩
  rcases h with ⟨C, hk, hy⟩ | ⟨hk, hy⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inl ⟨C, hk, by simp⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inr ⟨hk, by simp⟩

theorem bind_code_eq (V : List FVal) (n : Nat) (ct ct' : TypeIdx) (T : List AdminFX) :
    fvals V ++ .contRef n :: .fx (.contBind ct ct') :: T =
      fvals (V ++ [.cont n]) ++ .fx (.contBind ct ct') :: T := by
  simp [FVal.toAdmin]

/-- The `cont.bind` rules: the operands are `V`, nothing follows. -/
theorem bind_inj' {vs V : List FVal} {k n : Nat} {ct ct' c₁ c₂ : TypeIdx} {T : List AdminFX}
    (hx : fvals vs ++ [.contRef k, .fx (.contBind c₁ c₂)] =
      fvals V ++ .contRef n :: .fx (.contBind ct ct') :: T) :
    vs = V ∧ k = n ∧ c₁ = ct ∧ c₂ = ct' ∧ T = [] := by
  have hx' : fvals (vs ++ [.cont k]) ++ AdminFX.fx (.contBind c₁ c₂) :: [] =
      fvals (V ++ [.cont n]) ++ .fx (.contBind ct ct') :: T := by
    simpa [FVal.toAdmin] using hx
  obtain ⟨hV, he, hT⟩ := fvals_append_cons_inj hx' rfl rfl
  obtain ⟨rfl, hk⟩ := List.append_inj' hV rfl
  simp only [List.cons.injEq, FVal.cont.injEq, and_true] at hk
  simp only [AdminFX.fx.injEq, FXInstr.contBind.injEq] at he
  exact ⟨rfl, hk, he.1, he.2, hT.symm⟩

/-- The `ctxt-instrs` case of the inversions. -/
theorem bind_seq {A : Frame → TypeIdx → TypeIdx → Nat → Prop} {s s' : Store H}
    {K K' : List (Option ContFX)} {f f' : Frame} {vs : List FVal} {es es' rest : List AdminFX}
    (h : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (ih : BindInv A ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    BindInv A ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  intro V n ct ct' T hx
  have hx' : fvals vs ++ es ++ rest = fvals (V ++ [.cont n]) ++ .fx (.contBind ct ct') :: T :=
    hx.trans (bind_code_eq V n ct ct' T)
  rcases seq_splitF rfl hx' with ⟨U, hU⟩ | ⟨V₂, T₁, hV, hes, hT⟩
  · exact (no_step_fvals' h U hU).elim
  · have hne : V₂ ≠ [] := fun h0 => fx_head_stuck h _ T₁ (by rw [hes, h0]; rfl)
    obtain ⟨L, hV₂, hVL⟩ := suffix_concat hV hne
    have hes' : es = fvals L ++ .contRef n :: .fx (.contBind ct ct') :: T₁ := by
      rw [hes, hV₂, bind_code_eq]
    have hres := bindRes'_seq vs rest (ih L n ct ct' T₁ hes')
    rw [hVL, hT]
    exact hres

/-- **Inversion at `ref.cont; cont.bind`** (`StepFX'`): any split. -/
theorem step_contBind' {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    BindInv (fun _ _ _ _ => True) x y := by
  induction h with
  | core _ =>
    intro V n ct ct' T hc
    have hm : AdminFX.contRef n ∈ _ := hc ▸ List.mem_append_right _ List.mem_cons_self
    simp at hm
  | seq h _ ih => exact bind_seq h ih
  | @contBind s K f vs k C _ _ hk =>
    intro V n ct ct' T hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := bind_inj' hx
    exact ⟨[], vs, rfl, trivial, Or.inl ⟨C, hk, by simp⟩⟩
  | @contBindUsed s K f vs k _ _ hk =>
    intro V n ct ct' T hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := bind_inj' hx
    exact ⟨[], vs, rfl, trivial, Or.inr ⟨hk, by simp⟩⟩
  | invoke hc =>
    exact fun V n ct ct' T hx =>
      (invoke_ne_fx hc (hx.trans (bind_code_eq V n ct ct' T))).elim
  | _ => intro V n ct ct' T hx; rw [bind_code_eq] at hx; fnvF_absurd hx

/-- **Inversion at `ref.cont; cont.bind`** (`StepFXT`): the bound part has the typed arity. -/
theorem step_contBindT {x y : ConfigFX H} (h : StepFXT P noHost fx x y) :
    BindInv (fun f ct ct' n => BindArity f.module ct ct' n) x y := by
  induction h with
  | core _ =>
    intro V n ct ct' T hc
    have hm : AdminFX.contRef n ∈ _ := hc ▸ List.mem_append_right _ List.mem_cons_self
    simp at hm
  | seq h _ ih => exact bind_seq (stepFXT_incl h) ih
  | @contBind s K f vs k C _ _ hk ha =>
    intro V n ct ct' T hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := bind_inj' hx
    exact ⟨[], vs, rfl, ha, Or.inl ⟨C, hk, by simp⟩⟩
  | @contBindUsed s K f vs k _ _ hk ha =>
    intro V n ct ct' T hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := bind_inj' hx
    exact ⟨[], vs, rfl, ha, Or.inr ⟨hk, by simp⟩⟩
  | invoke hc =>
    exact fun V n ct ct' T hx =>
      (invoke_ne_fx hc (hx.trans (bind_code_eq V n ct ct' T))).elim
  | _ => intro V n ct ct' T hx; rw [bind_code_eq] at hx; fnvF_absurd hx

end Silmaril.Proofs.Wasm.Models.FXBindT
