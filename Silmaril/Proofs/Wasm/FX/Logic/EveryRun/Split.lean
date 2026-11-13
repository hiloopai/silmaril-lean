module

public import Silmaril.Wasm.FX.Logic.EveryRun.Defs
public import Silmaril.Wasm.Models.FXVRuns.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Inverting `StepFX'`: a step of `V; a; R` is a step of `V; a`

**`step_split`** (no host calls, every profile): let `a` be the first instruction of
`fvals V ++ a :: R` that is not an FX value. A `StepFX'` step of this code is a step of
`fvals V₂ ++ [a]` for a suffix `V₂` of `V`, with the rest of the values and `R` untouched
(`ctxt-instrs`), or `a` is `trap` or the `throw_ref` of an exception and the step discards values
before it and code after it. It is the FX counterpart of silmaril-lean's `Sim.Step.split_head`
and is proved by induction on the step: the `core` rule through `Sim.Step.split_head`, the `seq`
rule by induction, every other rule because its left-hand side ends at its first non-value.

`step_split_app` restates it for `c₁ ++ c₂`: a step of `c₁ ++ c₂`, when `c₁` is not all values,
is a step of `c₁` followed by `c₂`, or a trap or an exception cutting into `c₂`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (Conts)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fnvF fnvF_fvals_append fnvF_cons_none
  fvals_append_cons_inj seq_splitF fvals_eq_core' fvals_liftV' no_step_fvals' invoke_eq
  fnvF_cases fval?_toAdmin)
open Silmaril.Proofs.Wasm.Models.FXLower (blockFX_noHost)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-! ## Lists of FX values and Core code -/

theorem map_core_vals (W : List Val) : (vals W).map AdminFX.core = fvals (liftV W) :=
  (fvals_liftV' W).symm

theorem fvals_liftV_append (A B : List Val) : fvals (liftV (A ++ B)) = fvals (liftV A) ++ fvals (liftV B) := by
  simp [liftV, fvals]

/-- Core code with an FX non-value inside: its value prefix is Core values. -/
theorem map_core_split {cs : List Admin} {V : List FVal} {a : AdminFX} {R : List AdminFX}
    (ha : fval? a = none) (hx : cs.map AdminFX.core = fvals V ++ a :: R) :
    ∃ W a' R', V = liftV W ∧ a = .core a' ∧ R = R'.map .core ∧ cs = vals W ++ a' :: R' ∧
      a'.val? = none := by
  obtain ⟨cs₁, cs₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp hx
  obtain ⟨a', R', rfl, ha', hR⟩ := List.map_eq_cons_iff.mp h₂
  obtain ⟨W, hV, hcs⟩ := fvals_eq_core' h₁.symm
  have hv : a'.val? = none := by
    rw [← ha'] at ha
    simpa using ha
  exact ⟨W, a', R', hV, ha'.symm, hR.symm, by rw [hcs], hv⟩

/-! ## The result of a split -/

/-- What a step of `fvals V ++ a :: R` from `s, K, f` is (`step_split`). -/
def SplitRes (P : Profile) (fx : H → Option FuncFX) (s : Store H) (K : Conts) (f : Frame)
    (V : List FVal) (a : AdminFX) (R : List AdminFX) (y : ConfigFX H) : Prop :=
  (∃ V₁ V₂ L₀, V = V₁ ++ V₂ ∧
      StepFX' P noHost fx ⟨s, K, f, fvals V₂ ++ [a]⟩ ⟨y.store, y.conts, y.frame, L₀⟩ ∧
      y.code = fvals V₁ ++ L₀ ++ R) ∨
  (a = .core .trap ∧ y.store = s ∧ y.conts = K ∧ y.frame = f ∧
      ∃ ws us r r', V = ws ++ us ∧ R = r ++ r' ∧ (us ≠ [] ∨ r ≠ []) ∧
        y.code = fvals ws ++ .core .trap :: r') ∨
  (a = .core (.plain .throwRef) ∧ y.store = s ∧ y.conts = K ∧ y.frame = f ∧
      ∃ ws us b r r', V = ws ++ us ++ [.val (.ref (.exn b))] ∧ R = r ++ r' ∧ (us ≠ [] ∨ r ≠ []) ∧
        y.code = fvals ws ++ cthrowing b ++ r')

/-- A split under more values and more code. -/
theorem SplitRes.lift {s s' : Store H} {K K' : Conts} {f f' : Frame} {V₂ : List FVal}
    {a : AdminFX} {T es' : List AdminFX} (vs : List FVal) (rest : List AdminFX)
    (h : SplitRes P fx s K f V₂ a T ⟨s', K', f', es'⟩) :
    SplitRes P fx s K f (vs ++ V₂) a (T ++ rest) ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  rcases h with ⟨V₁, V₃, L₀, rfl, hs, hc⟩ | ⟨ha, hs, hK, hf, ws, us, r, r', rfl, rfl, hne, hc⟩ |
      ⟨ha, hs, hK, hf, ws, us, b, r, r', rfl, rfl, hne, hc⟩
  · refine Or.inl ⟨vs ++ V₁, V₃, L₀, by simp, hs, ?_⟩
    simp only at hc ⊢
    rw [hc]
    simp
  · refine Or.inr (Or.inl ⟨ha, hs, hK, hf, vs ++ ws, us, r, r' ++ rest, by simp, by simp, hne, ?_⟩)
    simp only at hc ⊢
    rw [hc]
    simp
  · refine Or.inr (Or.inr ⟨ha, hs, hK, hf, vs ++ ws, us, b, r, r' ++ rest, by simp, by simp, hne,
      ?_⟩)
    simp only at hc ⊢
    rw [hc]
    simp

/-- A rule whose left-hand side ends at its first non-value. -/
theorem root_split {x y : ConfigFX H} (h : StepFX' P noHost fx x y) {V : List FVal} {a : AdminFX}
    {R : List AdminFX} (ha : fval? a = none) (hx : x.code = fvals V ++ a :: R)
    (h1 : (fnvF x.code).2.length = 1) : SplitRes P fx x.store x.conts x.frame V a R y := by
  have hf : (fnvF x.code).2 = a :: R := by rw [hx, fnvF_fvals_append, fnvF_cons_none ha]
  have hR : R = [] := by
    rw [hf] at h1
    exact List.length_eq_zero_iff.mp (by simpa using h1)
  refine Or.inl ⟨[], V, y.code, rfl, ?_, by simp [hR]⟩
  have hx' : x = ⟨x.store, x.conts, x.frame, fvals V ++ [a]⟩ := by
    rw [← hR, ← hx]
  rw [← hx']
  exact h

/-- The `core` arm of `step_split`. -/
theorem core_split {s s' : Store H} {K : Conts} {f f' : Frame} {cs cs' : List Admin}
    (h : Step P (blockFX noHost fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩) {V : List FVal} {a : AdminFX}
    {R : List AdminFX} (ha : fval? a = none) (hx : cs.map AdminFX.core = fvals V ++ a :: R) :
    SplitRes P fx s K f V a R ⟨s', K, f', cs'.map .core⟩ := by
  obtain ⟨W, a', R', rfl, rfl, rfl, rfl, hv⟩ := map_core_split ha hx
  have h' : Step P noHost ⟨s, f, vals W ++ a' :: R'⟩ ⟨s', f', cs'⟩ := by
    rw [← blockFX_noHost fx]; exact h
  rcases Sim.Step.split_head hv h' with ⟨ws, us, is', rfl, hu, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, r, r', rfl, rfl, hne, rfl⟩ |
      ⟨rfl, rfl, rfl, ws, us, b, r, r', rfl, rfl, hne, rfl⟩
  · have hu' : StepFX' P noHost fx ⟨s, K, f, fvals (liftV us) ++ [.core a']⟩ ⟨s', K, f', is'.map .core⟩ := by
      have := StepFX'.core (K := K) (fx := fx) (P := P) (host := noHost)
        (show Step P (blockFX noHost fx) ⟨s, f, vals us ++ [a']⟩ ⟨s', f', is'⟩ by
          rw [blockFX_noHost]; exact hu)
      simpa [map_core_vals] using this
    exact Or.inl ⟨liftV ws, liftV us, is'.map .core, by simp [liftV], hu', by simp [map_core_vals]⟩
  · refine Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, liftV ws, liftV us, r.map .core, r'.map .core,
      by simp [liftV], by simp, by simpa [liftV] using hne, by simp [map_core_vals]⟩)
  · refine Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, liftV ws, liftV us, b, r.map .core, r'.map .core,
      by simp [liftV], by simp, by simpa [liftV] using hne, ?_⟩)
    simp [map_core_vals, cthrowing]

/-- The `seq` arm of `step_split`. -/
theorem seq_split {s s' : Store H} {K K' : Conts} {f f' : Frame} {vs : List FVal}
    {es es' rest : List AdminFX} (h : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (ih : ∀ V a R, fval? a = none → es = fvals V ++ a :: R →
      SplitRes P fx s K f V a R ⟨s', K', f', es'⟩)
    {V : List FVal} {a : AdminFX} {R : List AdminFX} (ha : fval? a = none)
    (hx : fvals vs ++ es ++ rest = fvals V ++ a :: R) :
    SplitRes P fx s K f V a R ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  rcases seq_splitF ha hx with ⟨U, hU⟩ | ⟨V₂, T₁, rfl, hes, rfl⟩
  · exact absurd hU (no_step_fvals' h U)
  · exact (ih V₂ a T₁ ha hes).lift vs rest

/-- The `trapSeq` arm of `step_split`. -/
theorem trapSeq_split {s : Store H} {K : Conts} {f : Frame} {vs : List FVal} {rest : List AdminFX}
    (hne : vs ≠ [] ∨ rest ≠ []) {V : List FVal} {a : AdminFX} {R : List AdminFX}
    (ha : fval? a = none) (hx : fvals vs ++ [.core .trap] ++ rest = fvals V ++ a :: R) :
    SplitRes P fx s K f V a R ⟨s, K, f, [.core .trap]⟩ := by
  have hx' : fvals vs ++ .core .trap :: rest = fvals V ++ a :: R := by rw [← hx]; simp
  obtain ⟨rfl, rfl, rfl⟩ := fvals_append_cons_inj hx' rfl ha
  exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, [], vs, rest, [], rfl, by simp, hne, rfl⟩)

/-- The `throwSeq` arm of `step_split`. -/
theorem throwSeq_split {s : Store H} {K : Conts} {f : Frame} {vs : List FVal} {b : Nat}
    {rest : List AdminFX} (hne : vs ≠ [] ∨ rest ≠ []) {V : List FVal} {a : AdminFX}
    {R : List AdminFX} (ha : fval? a = none) (hx : fvals vs ++ cthrowing b ++ rest = fvals V ++ a :: R) :
    SplitRes P fx s K f V a R ⟨s, K, f, cthrowing b⟩ := by
  have hx' : fvals (vs ++ [.val (.ref (.exn b))]) ++ .core (.plain .throwRef) :: rest =
      fvals V ++ a :: R := by
    rw [← hx]; simp [cthrowing, throwing, FVal.toAdmin, Val.toAdmin]
  obtain ⟨rfl, rfl, rfl⟩ := fvals_append_cons_inj hx' rfl ha
  exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, [], vs, b, rest, [], rfl, by simp, hne, rfl⟩)

/-- The `invoke` arm of `step_split`. -/
theorem invoke_fnv {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef) :
    (fnvF (cvals vs ++ [.core (.ref (.func a)), .core c])).2.length = 1 := by
  have hcv := Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc
  rw [invoke_eq, fnvF_fvals_append, fnvF_cons_none (by simp [fval?, hcv])]
  rfl

/-- **Head decomposition for `StepFX'`.** -/
theorem step_split {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ V a R, fval? a = none → x.code = fvals V ++ a :: R →
      SplitRes P fx x.store x.conts x.frame V a R y := by
  have h0 := h
  induction h with
  | core h => exact fun V a R ha hx => core_split h ha hx
  | seq h _ ih => exact fun V a R ha hx => seq_split h (ih h) ha hx
  | trapSeq hne => exact fun V a R ha hx => trapSeq_split hne ha hx
  | throwSeq hne => exact fun V a R ha hx => throwSeq_split hne ha hx
  | invoke hc => exact fun V a R ha hx => root_split h0 ha hx (invoke_fnv hc)
  | _ =>
    intro V a R ha hx
    refine root_split h0 ha hx ?_
    simp [fnvF_fvals_append, fnvF, fval?, Admin.val?, constI32, Val.i32, Val.toAdmin,
      Silmaril.Proofs.Wasm.Models.FXVRuns.fnvF_cvals_append]

/-- **A step of `c₁ ++ c₂`** with `c₁ = fvals V ++ a :: R₁`: a step of `c₁` followed by `c₂`, or a
cut. -/
theorem step_split_app {s : Store H} {K : Conts} {f : Frame} {V : List FVal} {a : AdminFX}
    {R₁ c₂ : List AdminFX} {y : ConfigFX H} (ha : fval? a = none)
    (h : StepFX' P noHost fx ⟨s, K, f, fvals V ++ a :: R₁ ++ c₂⟩ y) :
    (∃ c₁', StepFX' P noHost fx ⟨s, K, f, fvals V ++ a :: R₁⟩ ⟨y.store, y.conts, y.frame, c₁'⟩ ∧
        y.code = c₁' ++ c₂) ∨
    (a = .core .trap ∧ y.store = s ∧ y.conts = K ∧ y.frame = f ∧
        ∃ ws r', y.code = fvals ws ++ .core .trap :: r') ∨
    (a = .core (.plain .throwRef) ∧ y.store = s ∧ y.conts = K ∧ y.frame = f ∧
        ∃ ws V' b r', V = V' ++ [.val (.ref (.exn b))] ∧ y.code = fvals ws ++ cthrowing b ++ r') := by
  rcases step_split h V a (R₁ ++ c₂) ha (by simp) with ⟨V₁, V₂, L₀, rfl, hs, hc⟩ | hc | hc
  · refine Or.inl ⟨fvals V₁ ++ L₀ ++ R₁, ?_, by rw [hc]; simp⟩
    by_cases hne : V₁ ≠ [] ∨ R₁ ≠ []
    · simpa using StepFX'.seq (vs := V₁) (rest := R₁) hs hne
    · have hV : V₁ = [] ∧ R₁ = [] := by simpa only [ne_eq, not_or, not_not] using hne
      rw [hV.1, hV.2]
      simpa using hs
  · obtain ⟨ha, hs, hK, hf, ws, -, -, r', -, -, -, hc⟩ := hc
    exact Or.inr (Or.inl ⟨ha, hs, hK, hf, ws, r', hc⟩)
  · obtain ⟨ha, hs, hK, hf, ws, us, b, -, r', hV, -, -, hc⟩ := hc
    exact Or.inr (Or.inr ⟨ha, hs, hK, hf, ws, ws ++ us, b, r', by simp [hV], hc⟩)

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
