module

public import Silmaril.Proofs.Wasm.Models.FXVRuns.Fnv

/-!
# Stuck shapes of `StepFX'` (no host calls)

* `not_step_drop_head`: Core `drop` with no operand before it does not step;
* `drop_head_stuck`: so FX code starting with `drop` does not step under `StepFX'`;
* `br_tail_stuck`: FX values then a branch do not step (the branch needs a label);
* `suspend_tail_stuck`: FX values then `suspend` do not step (`suspend` needs a handler);
* `contdrop_inv`: FX values, a continuation reference, `drop`, then any code: the only step
  drops the continuation (`dropCont`, under `ctxt-instrs`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXVRuns

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXLower (blockFX_noHost)
open Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-! ## Core: `drop` with no operand -/

theorem not_parametric_drop {is' : List Admin} : ¬ ParametricStep [.plain .drop] is' := by
  intro h
  generalize hl : [Admin.plain .drop] = l at h
  cases h <;> simp_all

theorem not_head_drop {s : Store H} {f : Frame} {c : Config H} :
    ¬ Head P s f [] (.plain .drop) c := by
  intro h
  cases h with
  | parametric h => exact not_parametric_drop h
  | numeric h => exact absurd (famOf_of_shape (NumericStep.shape h)).2 (by decide)
  | vector h => exact absurd (famOf_of_shape (VectorStep.shape h)).2 (by decide)
  | «variable» h => exact absurd (famOf_of_shape (VariableStep.shape h)).2 (by decide)
  | table h => exact absurd (famOf_of_shape (TableStep.shape h)).2 (by decide)
  | memory h => exact absurd (famOf_of_shape (MemoryStep.shape h)).2 (by decide)
  | reference h => exact absurd (famOf_of_shape (RefStep.shape h)).2 (by decide)
  | aggregate h => exact absurd (famOf_of_shape (AggregateStep.shape h)).2 (by decide)
  | callRefFunc _ hc => exact hc.elim

/-- **Core `drop` with no operand does not step.** -/
theorem not_step_drop_head {s : Store H} {f : Frame} {rest : List Admin} {c : Config H} :
    ¬ Step P noHost ⟨s, f, .plain .drop :: rest⟩ c := by
  intro h
  have hf0 : fnv (Admin.plain .drop :: rest) = ([], .plain .drop :: rest) :=
    fnv_cons_of_none rfl rest
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest', c₀, hf, -, hh, -⟩ := fnv_headDec hd
    simp only at hf
    rw [hf0] at hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hf
    obtain ⟨h1, rfl, -⟩ := hf
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h1.symm
    exact not_head_drop hh
  · obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ := fnv_bubble hb <;> simp only at hf <;>
      rw [hf0] at hf <;> simp at hf

/-! ## `StepFX'` -/

/-- A `ctxt-instrs` decomposition of code starting with a non-value: no values in front. -/
theorem seq_head {vs : List FVal} {es rest T : List AdminFX} {e : AdminFX}
    (he : fval? e = none) (hc : fvals vs ++ es ++ rest = e :: T) :
    es = [] ∨ ∃ es₁, es = e :: es₁ := by
  cases vs with
  | cons v vs =>
    have h1 : v.toAdmin = e := (List.cons.inj hc).1
    have h2 : fval? e = some v := by rw [← h1]; exact fval?_toAdmin v
    rw [he] at h2
    cases h2
  | nil =>
    cases es with
    | nil => exact Or.inl rfl
    | cons e' es => exact Or.inr ⟨es, by rw [(List.cons.inj hc).1]⟩

/-- A `ctxt-instrs` decomposition of FX values then one non-value. -/
theorem seq_tail {vs V : List FVal} {es rest : List AdminFX} {e : AdminFX}
    (he : fval? e = none) (hc : fvals vs ++ es ++ rest = fvals V ++ [e]) :
    (∃ U, es = fvals U) ∨ ∃ V₂, es = fvals V₂ ++ [e] := by
  rcases seq_splitF (V := V) (T := []) he hc with hU | ⟨V₂, T₁, -, hes, hT⟩
  · exact Or.inl hU
  · have hT₁ : T₁ = [] := (List.append_eq_nil_iff.mp hT.symm).1
    exact Or.inr ⟨V₂, by rw [hes, hT₁]⟩

/-- An `invoke` left-hand side does not start with a non-value. -/
theorem invoke_ne_head {vs : List Val} {a : Nat} {c : Admin} {e : AdminFX} {T : List AdminFX}
    (he : fval? e = none) : cvals vs ++ [.core (.ref (.func a)), .core c] ≠ e :: T := by
  intro hx
  have h1 := congrArg (fun l => (fnvF l).1) hx
  simp [fnvF_cons_none he] at h1

/-- The `core` case of `drop_head_stuck`. -/
theorem drop_head_core {s s' : Store H} {f f' : Frame} {cs cs' : List Admin} {T : List AdminFX}
    (h : Step P (blockFX noHost fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩)
    (hc : cs.map .core = .core (.plain .drop) :: T) : False := by
  obtain ⟨c, cs₁, hcs, hc1, -⟩ := List.map_eq_cons_iff.mp hc
  have hc1' : c = .plain .drop := AdminFX.core.inj hc1
  have h' : Step P noHost ⟨s, f, .plain .drop :: cs₁⟩ ⟨s', f', cs'⟩ := by
    rw [← blockFX_noHost fx, ← hc1', ← hcs]
    exact h
  exact not_step_drop_head h'

/-- **FX code starting with `drop` does not step.** -/
theorem drop_head_stuck {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ T, x.code ≠ .core (.plain .drop) :: T := by
  induction h with
  | core h => exact fun T hc => drop_head_core h hc
  | seq h' _ ih =>
    intro T hc
    rcases seq_head rfl hc with hes | ⟨es₁, hes⟩
    · exact no_step_nil' h' hes
    · exact ih es₁ hes
  | invoke _ => exact fun T => invoke_ne_head rfl
  | _ => intro T hx; fnvF_absurd hx

/-- The last instruction of an `invoke` left-hand side is its call. -/
theorem invoke_last {vs : List Val} {a : Nat} {c : Admin} {V : List FVal} {e : AdminFX}
    (h : cvals vs ++ [.core (.ref (.func a)), .core c] = fvals V ++ [e]) : e = .core c := by
  have h1 := congrArg List.getLast? h
  simp only [List.getLast?_append, List.getLast?_cons_cons, List.getLast?_singleton,
    Option.some_or] at h1
  exact (Option.some.inj h1).symm

/-- The `core` case of `br_tail_stuck`. -/
theorem br_tail_core {s s' : Store H} {f f' : Frame} {cs cs' : List Admin} {V : List FVal}
    {l : LabelIdx} (h : Step P (blockFX noHost fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩)
    (hc : cs.map .core = fvals V ++ [.core (.plain (.br l))]) : False := by
  obtain ⟨A, B, hcs, hA, hB⟩ := List.map_eq_append_iff.mp hc
  obtain ⟨W, -, hAW⟩ := fvals_eq_core' hA.symm
  obtain ⟨b, hBb, hb⟩ := List.map_eq_singleton_iff.mp hB
  have hcs' : cs = vals W ++ [.plain (.br l)] := by rw [hcs, hAW, hBb, AdminFX.core.inj hb]
  have h' : Step P noHost ⟨s, f, vals W ++ [.plain (.br l)]⟩ ⟨s', f', cs'⟩ := by
    rw [← blockFX_noHost fx, ← hcs']
    exact h
  have hf : fnv (vals W ++ [Admin.plain (.br l)]) = (W, [.plain (.br l)]) := by
    rw [fnv_vals_append, fnv_cons_of_none rfl]
    simp
  exact not_step_blocked h' hf (Or.inl ⟨l, rfl⟩)

/-- **FX values then a branch do not step.** -/
theorem br_tail_stuck {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ V l, x.code ≠ fvals V ++ [.core (.plain (.br l))] := by
  induction h with
  | core h => exact fun V l hc => br_tail_core h hc
  | seq h' _ ih =>
    intro V l hc
    rcases seq_tail rfl hc with ⟨U, hU⟩ | ⟨V₂, hes⟩
    · exact no_step_fvals' h' U hU
    · exact ih V₂ l hes
  | invoke hc =>
    intro V l hx
    have h1 : AdminFX.core (.plain (.br l)) = .core _ := invoke_last hx
    rw [← AdminFX.core.inj h1] at hc
    exact hc
  | _ => intro V l hx; fnvF_absurd hx

/-- **FX values then `suspend` do not step** (`suspend` needs an enclosing handler). -/
theorem suspend_tail_stuck {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ V i, x.code ≠ fvals V ++ [.fx (.suspend i)] := by
  induction h with
  | core _ =>
    intro V i hc
    have hm : AdminFX.fx (.suspend i) ∈ _ := hc ▸ List.mem_append_right _ (List.mem_singleton_self _)
    simp at hm
  | seq h' _ ih =>
    intro V i hc
    rcases seq_tail rfl hc with ⟨U, hU⟩ | ⟨V₂, hes⟩
    · exact no_step_fvals' h' U hU
    · exact ih V₂ i hes
  | invoke _ =>
    intro V i hx
    exact absurd (invoke_last hx) (by simp)
  | _ => intro V i hx; fnvF_absurd hx

/-- The continuation reference and `drop` as FX values then a non-value. -/
theorem contdrop_eq (V : List FVal) (k : Nat) (T : List AdminFX) :
    fvals V ++ [.contRef k, .core (.plain .drop)] ++ T =
      fvals (V ++ [.cont k]) ++ .core (.plain .drop) :: T := by
  simp [FVal.toAdmin]

/-- The conclusion of `contdrop_inv`. -/
abbrev ContDropRes (x y : ConfigFX H) : Prop :=
  ∀ V k T, x.code = fvals V ++ [.contRef k, .core (.plain .drop)] ++ T →
    y = ⟨x.store, x.conts, x.frame, fvals V ++ T⟩

/-- A suffix of `V ++ [b]` that is not empty ends with `b`. -/
theorem suffix_concat {V vs V₂ : List FVal} {b : FVal} (hV : V ++ [b] = vs ++ V₂)
    (hne : V₂ ≠ []) : ∃ L, V₂ = L ++ [b] ∧ V = vs ++ L := by
  obtain ⟨L, b', hL⟩ := (List.eq_nil_or_concat V₂).resolve_left hne
  have hV' : V ++ [b] = (vs ++ L) ++ [b'] := by rw [hV, hL, List.concat_eq_append, List.append_assoc]
  obtain ⟨hV'', hb⟩ := List.append_inj' hV' rfl
  have hbb : b' = b := (List.cons.inj hb).1.symm
  exact ⟨L, by rw [hL, List.concat_eq_append, hbb], hV''⟩

/-- The `ctxt-instrs` case of `contdrop_inv`. -/
theorem contdrop_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {vs : List FVal} {es es' rest : List AdminFX}
    (h' : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (ih : ContDropRes ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩) :
    ContDropRes ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ := by
  intro V k T hc
  have hc' : fvals vs ++ es ++ rest = fvals (V ++ [.cont k]) ++ .core (.plain .drop) :: T :=
    hc.trans (contdrop_eq V k T)
  rcases seq_splitF rfl hc' with ⟨U, hU⟩ | ⟨V₂, T₁, hV, hes, hT⟩
  · exact absurd hU (no_step_fvals' h' U)
  · have hne : V₂ ≠ [] := fun h0 => drop_head_stuck h' T₁ (by rw [hes, h0]; rfl)
    obtain ⟨L, hV₂, hVL⟩ := suffix_concat hV hne
    have hes' : es = fvals L ++ [.contRef k, .core (.plain .drop)] ++ T₁ := by
      rw [hes, hV₂, contdrop_eq]
    have hy : (⟨s', K', f', es'⟩ : ConfigFX H) = ⟨s, K, f, fvals L ++ T₁⟩ := ih L k T₁ hes'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    rw [hVL, hT, fvals_append]
    simp only [List.append_assoc]

/-- The `dropCont` case of `contdrop_inv`. -/
theorem contdrop_base {s : Store H} {K : List (Option ContFX)} {f : Frame} {k' : Nat} :
    ContDropRes (⟨s, K, f, [.contRef k', .core (.plain .drop)]⟩ : ConfigFX H) ⟨s, K, f, []⟩ := by
  intro V k T hc
  have hc' : fvals [.cont k'] ++ AdminFX.core (.plain .drop) :: [] =
      fvals (V ++ [.cont k]) ++ .core (.plain .drop) :: T := hc.trans (contdrop_eq V k T)
  obtain ⟨hV, -, hT⟩ := fvals_append_cons_inj hc' rfl rfl
  have hl : 1 = V.length + 1 := by simpa using congrArg List.length hV
  have hV0 : V = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [hV0, ← hT]
  rfl

/-- The `invoke` case of `contdrop_inv`. -/
theorem contdrop_invoke {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef)
    {V : List FVal} {k : Nat} {T : List AdminFX} :
    cvals vs ++ [.core (.ref (.func a)), .core c] ≠
      fvals V ++ [.contRef k, .core (.plain .drop)] ++ T := by
  intro hx
  rw [invoke_eq, contdrop_eq] at hx
  obtain ⟨-, he, -⟩ := fvals_append_cons_inj hx
    (by simp [Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc]) rfl
  rw [AdminFX.core.inj he] at hc
  exact hc

/-- **The only step of `V; ref.cont k; drop; T` drops the continuation.** -/
theorem contdrop_inv {x y : ConfigFX H} (h : StepFX' P noHost fx x y) : ContDropRes x y := by
  induction h with
  | core _ =>
    intro V k T hc
    have hm : AdminFX.contRef k ∈ _ := hc ▸ List.mem_append_left _
      (List.mem_append_right _ (List.mem_cons_self))
    simp at hm
  | seq h' _ ih => exact contdrop_seq h' ih
  | dropCont => exact contdrop_base
  | invoke hc => exact fun V k T hx => (contdrop_invoke hc hx).elim
  | _ => intro V k T hx; rw [contdrop_eq] at hx; fnvF_absurd hx

end Silmaril.Proofs.Wasm.Models.FXVRuns
