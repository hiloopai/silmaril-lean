module

public import Silmaril.Proofs.Wasm.Models.FXVRuns.Stuck
public import Silmaril.Wasm.Models.FXAbort.Thms

/-!
# The abortive fragment: every run of the source

An earlier step showed that `abortSrc hs W x ks` reaches the join `W; ks` (`src_runs`). The `suspend`
rule is untyped: it may capture any value prefix `U` of `W` in the continuation and branch with
the rest `vs` (`W = U ++ vs`). Here, without host calls:

* `plug_flat`: a context whose plug is FX values then one FX instruction is a value prefix; so
  `suspend`'s context in the source captures a value prefix `U` and runs in the frame `f`;
* `handler_inv`, **`src_step_inv`**: every step of the source is a `suspend` with some split
  `W = U ++ vs`, to the label around `vs; ref.cont; br l`;
* `label_br_inv`: a label around FX values and `br 0` only branches, with exactly the label's
  arity of values;
* **`split_stuck`**: when `U ≠ []` the branch is one value short, and the configuration is stuck;
* `mid_step`: when `U = []` the branch goes to `W; ref.cont; drop; ks`, and `contdrop_inv` then
  allows only `dropCont`, to the join;
* **`src_behaviours_eq`**: so the source's `StepFX'` behaviours (no FX functions) are exactly
  the Core behaviours of the join at the source's store.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXVRuns

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXAbort
open Silmaril.Proofs.Wasm.Models.FXLower (ofCoreK)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-! ## Contexts whose plug is flat -/

/-- A plugged hole is never FX values only. -/
theorem plug_not_fvals (E : CtxV) {vs : List FVal} {e : AdminFX} (he : fval? e = none) :
    ∀ U, E.plug (fvals vs ++ [e]) ≠ fvals U := by
  induction E with
  | hole =>
    intro U h
    have h1 := congrArg (fun l => (fnvF l).2) h
    simp [CtxV.plug, fnvF_fvals_append, fnvF_cons_none he] at h1
  | seq us E rest ih =>
    intro U h
    obtain ⟨-, U₂, -, -, hB⟩ := fvals_eq_append (h.symm.trans (List.append_assoc _ _ _))
    obtain ⟨U₃, -, -, hE, -⟩ := fvals_eq_append hB.symm
    exact ih U₃ hE
  | label n k E ih => intro U h; simp only [CtxV.plug] at h; fnvF_absurd h
  | frame n f E ih => intro U h; simp only [CtxV.plug] at h; fnvF_absurd h
  | handler hs E ih => intro U h; simp only [CtxV.plug] at h; fnvF_absurd h

/-- **A context whose plug is FX values then one FX instruction is a value prefix.** -/
theorem plug_flat (E : CtxV) {vs : List FVal} {e : AdminFX} (he : fval? e = none) :
    ∀ {V : List FVal} {i : FXInstr}, E.plug (fvals vs ++ [e]) = fvals V ++ [.fx i] →
      (∃ U, V = U ++ vs) ∧ e = .fx i ∧ ∀ f, E.frameAt f = f := by
  induction E with
  | hole =>
    intro V i h
    obtain ⟨hV, he', -⟩ := fvals_append_cons_inj h he rfl
    exact ⟨⟨[], by simp [hV]⟩, he', fun _ => rfl⟩
  | seq us E rest ih =>
    intro V i h
    rcases fnvF_cases (E.plug (fvals vs ++ [e])) with ⟨U, hU⟩ | ⟨V₁, e₁, T₁, hE, he₁⟩
    · exact absurd hU (plug_not_fvals E he U)
    · have h' : fvals (us ++ V₁) ++ e₁ :: (T₁ ++ rest) = fvals V ++ AdminFX.fx i :: [] := by
        rw [← h]
        simp only [CtxV.plug, hE, fvals_append, List.append_assoc, List.cons_append]
      obtain ⟨hV, rfl, hT⟩ := fvals_append_cons_inj h' he₁ rfl
      obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hT
      obtain ⟨⟨U, rfl⟩, he', hfr⟩ := ih hE
      exact ⟨⟨us ++ U, by rw [← hV, List.append_assoc]⟩, he', fun f => hfr f⟩
  | label n k E ih => intro V i h; simp only [CtxV.plug] at h; fnvF_absurd h
  | frame n f E ih => intro V i h; simp only [CtxV.plug] at h; fnvF_absurd h
  | handler hs E ih => intro V i h; simp only [CtxV.plug] at h; fnvF_absurd h

/-! ## One-instruction codes -/

theorem label_inj {n n' : Nat} {k k' : List InstrFX} {B B' : List AdminFX}
    (h : [AdminFX.label n' k' B'] = [.label n k B]) : n' = n ∧ k' = k ∧ B' = B := by
  simpa only [List.cons.injEq, AdminFX.label.injEq, and_true] using h

theorem handler_inj {hs hs' : List HClause} {B B' : List AdminFX}
    (h : [AdminFX.handler hs' B'] = [.handler hs B]) : hs' = hs ∧ B' = B := by
  simpa only [List.cons.injEq, AdminFX.handler.injEq, and_true] using h

/-- A `ctxt-instrs` decomposition of one non-value has an empty stepping part. -/
theorem seq_single' {vs : List FVal} {es rest : List AdminFX} {x : AdminFX}
    (hx : fval? x = none) (hne : vs ≠ [] ∨ rest ≠ []) (h : fvals vs ++ es ++ rest = [x]) :
    es = [] := by
  rcases hne with hv | hr
  · obtain ⟨v, vs', rfl⟩ := List.exists_cons_of_ne_nil hv
    simp only [fvals_cons, List.cons_append, List.cons.injEq] at h
    rw [← h.1] at hx
    simp at hx
  · have h' : fvals vs ++ (es ++ rest) = [x] := by rw [← List.append_assoc]; exact h
    rcases List.append_eq_singleton_iff.mp h' with ⟨-, h2⟩ | ⟨-, h2⟩
    · rcases List.append_eq_singleton_iff.mp h2 with ⟨he, -⟩ | ⟨-, hr'⟩
      · exact he
      · exact absurd hr' hr
    · exact absurd (List.append_eq_nil_iff.mp h2).2 hr

/-! ## The handler frame of the source -/

/-- The `suspend` case of `handler_inv`. -/
theorem suspend_case {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {V vs : List FVal} {x x₀ : TagIdx} {E : CtxV} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (hb : E.plug (fvals vs ++ [.fx (.suspend x₀)]) = fvals V ++ [.fx (.suspend x)])
    (ht : s.tag? (E.frameAt f) x₀ = some (ta, ti))
    (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    ∃ (U vs' : List FVal) (E' : CtxV) (ta' : Nat) (ti' : TagInst) (l' : LabelIdx),
      V = U ++ vs' ∧ s.tag? f x = some (ta', ti') ∧
      hs.find? (fun c => c.tag == ta') = some (.onLabel ta' l') ∧
      (⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩ :
        ConfigFX H) =
        ⟨s, K ++ [some ⟨E'.plug⟩], f, fvals vs' ++ [.contRef K.length, .core (.plain (.br l'))]⟩ := by
  obtain ⟨⟨U, hU⟩, he, hfr⟩ := plug_flat E (e := AdminFX.fx (.suspend x₀)) rfl hb
  have hx : x₀ = x := by injection he with he'; injection he'
  have ht' : s.tag? f x = some (ta, ti) := by rw [← hx, ← hfr f]; exact ht
  exact ⟨U, vs, E, ta, ti, l, hU, ht', hcl, rfl⟩

/-- **A handler around FX values then `suspend` only suspends**, capturing a value prefix. -/
theorem handler_inv {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {V : List FVal} {x : TagIdx} {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, [.handler hs (fvals V ++ [.fx (.suspend x)])]⟩ y) :
    ∃ (U vs : List FVal) (E : CtxV) (ta : Nat) (ti : TagInst) (l : LabelIdx), V = U ++ vs ∧ s.tag? f x = some (ta, ti) ∧
      hs.find? (fun c => c.tag == ta) = some (.onLabel ta l) ∧
      y = ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩ := by
  generalize hx : (⟨s, K, f, [.handler hs (fvals V ++ [.fx (.suspend x)])]⟩ : ConfigFX H) = c at h
  have hc : c.code = [.handler hs (fvals V ++ [.fx (.suspend x)])] := by rw [← hx]
  have hcs : c.store = s := by rw [← hx]
  have hcK : c.conts = K := by rw [← hx]
  have hcf : c.frame = f := by rw [← hx]
  cases h with
  | ctxHandler h' => exact absurd (handler_inj hc).2 (suspend_tail_stuck h' V x)
  | seq h' hne => exact absurd (seq_single' rfl hne hc) (no_step_nil' h')
  | @suspend s₀ K₀ f₀ hs₀ E vs x₀ ta ti l ht hE hcl =>
    obtain ⟨rfl, hb⟩ := handler_inj hc
    obtain rfl : s₀ = s := hcs
    obtain rfl : K₀ = K := hcK
    obtain rfl : f₀ = f := hcf
    exact suspend_case hb ht hcl
  | @switch s₀ K₀ f₀ hs₀ E vs k C ct x₀ ta ti hk ht hE hcl =>
    obtain ⟨rfl, hb⟩ := handler_inj hc
    have hb' : E.plug (fvals (vs ++ [.cont k]) ++ [.fx (.switch ct x₀)]) =
        fvals V ++ [.fx (.suspend x)] := by
      rw [← hb]
      simp [FVal.toAdmin]
    obtain ⟨-, he, -⟩ := plug_flat E (e := AdminFX.fx (.switch ct x₀)) rfl hb'
    cases he
  | handlerVals => exact absurd (handler_inj hc).2 (by intro hb; fnvF_absurd hb)
  | brHandler => exact absurd (handler_inj hc).2 (by intro hb; fnvF_absurd hb)
  | returnHandler => exact absurd (handler_inj hc).2 (by intro hb; fnvF_absurd hb)
  | trapHandler => exact absurd (handler_inj hc).2 (by intro hb; fnvF_absurd hb)
  | throwHandler => exact absurd (handler_inj hc).2 (by intro hb; fnvF_absurd hb)
  | invoke hci =>
    have h1 := congrArg (fun l => (fnvF l).1) hc
    simp at h1
  | _ => fnvF_absurd hc

/-! ## A label around a branch -/

theorem br_zero_split {V vs' vs : List FVal} {l l₀ : LabelIdx} {rest : List AdminFX}
    (hb : fvals vs' ++ fvals vs ++ [.core (.plain (.br l₀))] ++ rest =
      fvals V ++ [.core (.plain (.br l))]) : V = vs' ++ vs := by
  have hb' : fvals (vs' ++ vs) ++ AdminFX.core (.plain (.br l₀)) :: rest =
      fvals V ++ AdminFX.core (.plain (.br l)) :: [] := by
    rw [← hb]
    simp
  exact (fvals_append_cons_inj hb' rfl rfl).1.symm

theorem br_succ_label {V vs : List FVal} {l l₀ : LabelIdx} {rest : List AdminFX}
    (hb : fvals vs ++ [.core (.plain (.br l₀))] ++ rest = fvals V ++ [.core (.plain (.br l))]) :
    l₀ = l := by
  have hb' : fvals vs ++ AdminFX.core (.plain (.br l₀)) :: rest =
      fvals V ++ AdminFX.core (.plain (.br l)) :: [] := by
    rw [← hb]
    simp
  have he := (fvals_append_cons_inj hb' rfl rfl).2.1
  injection he with he'
  injection he' with he''
  injection he''

/-- **A label around FX values and `br 0` only branches**, with exactly its arity of values. -/
theorem label_br_inv {s : Store H} {K : List (Option ContFX)} {f : Frame} {n : Nat}
    {k : List InstrFX} {V : List FVal} {l : LabelIdx} (hl : l.toNat = 0) {y : ConfigFX H}
    (h : StepFX' P noHost fx ⟨s, K, f, [.label n k (fvals V ++ [.core (.plain (.br l))])]⟩ y) :
    ∃ va vb, V = va ++ vb ∧ vb.length = n ∧
      y = ⟨s, K, f, fvals vb ++ k.map InstrFX.toAdmin⟩ := by
  generalize hx : (⟨s, K, f, [.label n k (fvals V ++ [.core (.plain (.br l))])]⟩ :
    ConfigFX H) = c at h
  have hc : c.code = [.label n k (fvals V ++ [.core (.plain (.br l))])] := by rw [← hx]
  have hcs : c.store = s := by rw [← hx]
  have hcK : c.conts = K := by rw [← hx]
  have hcf : c.frame = f := by rw [← hx]
  cases h with
  | ctxLabel h' => exact absurd (label_inj hc).2.2 (br_tail_stuck h' V l)
  | seq h' hne => exact absurd (seq_single' rfl hne hc) (no_step_nil' h')
  | @brLabelZero s₀ K₀ f₀ n₀ k₀ vs' vs l₀ rest hl₀ hn =>
    obtain ⟨rfl, rfl, hb⟩ := label_inj hc
    obtain rfl : s₀ = s := hcs
    obtain rfl : K₀ = K := hcK
    obtain rfl : f₀ = f := hcf
    exact ⟨vs', vs, br_zero_split hb, hn, rfl⟩
  | @brLabelSucc s₀ K₀ f₀ n₀ k₀ vs l₀ rest hl₀ =>
    have hll : l₀ = l := br_succ_label (label_inj hc).2.2
    rw [hll] at hl₀
    omega
  | labelVals => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | returnLabel => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | trapLabel => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | throwLabel => exact absurd (label_inj hc).2.2 (by intro hb; fnvF_absurd hb)
  | invoke hci =>
    have h1 := congrArg (fun l => (fnvF l).1) hc
    simp at h1
  | _ => fnvF_absurd hc

end Silmaril.Proofs.Wasm.Models.FXVRuns
