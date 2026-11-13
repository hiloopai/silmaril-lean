module

public import Silmaril.Raw.Wasm.Unified.FXSim.Doomed
public import Silmaril.Raw.Wasm.Unified.FXSim.Fwd

/-!
# Core steps of Core code read from FX code are CoreFX steps, or doomed (unrefined)

`bwd`: a Core step of Core code `cs` that FX code `es` reads as (`LiftAs es cs`) is matched by
one CoreFX step (without FX functions) of `es` to FX code that reads as the result, **or** the
result is doomed (`Doomed`). The second case is `return_call_ref-label` on a label that `es`
holds as an FX label: CoreFX has no rule popping an FX label around a `return_call_ref`.

Code without structured instructions (`Struct`) reads only as its embedding, where the CoreFX
`core` rule applies; this covers the Core rules whose left-hand side has no `block`, `loop`,
`if` or label at the top (the families, calls, branches, exceptions, handlers and frames). The
remaining rules are matched one by one.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Unified.FXSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Unified.Versions
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded.Det (famOf FamShape)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Code without structured instructions -/

/-- Structured source instructions. -/
def StructI : Instr → Prop
  | .block _ _ | .loop _ _ | .if_ _ _ _ => True
  | _ => False

@[simp] theorem struct_plain (i : Instr) : Struct (.plain i) ↔ StructI i := by
  cases i <;> simp [Struct, StructI]

@[simp] theorem not_struct_ref (r : Ref) : ¬ Struct (.ref r) := id

@[simp] theorem not_struct_callRefType (d : Silmaril.Wasm.Validation.DefType) :
    ¬ Struct (.callRefType d) := id

@[simp] theorem not_struct_returnCallRefType (d : Silmaril.Wasm.Validation.DefType) :
    ¬ Struct (.returnCallRefType d) := id

@[simp] theorem not_struct_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    ¬ Struct (.handler n cs b) := id

@[simp] theorem not_struct_frame (n : Nat) (f : Frame) (b : List Admin) :
    ¬ Struct (.frame n f b) := id

@[simp] theorem not_struct_trap : ¬ Struct .trap := id

@[simp] theorem not_struct_toAdmin' (v : Val) : ¬ Struct v.toAdmin := not_struct_toAdmin v

theorem forall_noStruct_vals (vs : List Val) : (∀ a ∈ vals vs, ¬ Struct a) = True :=
  eq_true (noStruct_vals vs)

theorem not_struct_of_isCallRef {c : Admin} (h : c.IsCallRef) : ¬ Struct c := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsCallRef] at h
  · cases i <;> simp at h
    simp [StructI]
  · exact id

theorem famOf_of_struct {e : Admin} (h : Struct e) : famOf e = .control := by
  unfold Struct at h
  split at h
  all_goals first | rfl | exact h.elim

/-- Close `∀ a ∈ code, ¬ Struct a` for a literal left-hand side. -/
macro "nostruct" : tactic =>
  `(tactic| (simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil,
      and_true, true_and, forall_noStruct_vals]; try simp [StructI, constI32, throwing]))

/-- The family left-hand sides have no structured instruction. -/
theorem noStruct_fam {args : List Val} {e : Admin} {k : Silmaril.Wasm.SingleThreaded.Det.Fam}
    (hk : famOf e = k) (hc : k ≠ .control) : ∀ a ∈ vals args ++ [e], ¬ Struct a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact noStruct_vals args a ha
  · rw [List.mem_singleton.mp ha]
    exact fun hs => hc (hk ▸ famOf_of_struct hs)

/-! ## The backward step -/

/-- The outcome of a backward step: a matching CoreFX step, or doomed Core code. -/
def Bwd (P : Profile) (host : HostSemantics H) (s : Store H) (K : List (Option ContFX))
    (f : Frame) (es : List AdminFX) (c' : Config H) : Prop :=
  (∃ es', StepFX P host noFX ⟨s, K, f, es⟩ ⟨c'.store, K, c'.frame, es'⟩ ∧ LiftAs es' c'.code) ∨
    ∃ d, Doomed d c'.code

/-- The embedding of a Core step. -/
theorem bwd_core {c c' : Config H} (h0 : Step P host c c') (K : List (Option ContFX))
    {es : List AdminFX} (he : es = c.code.map .core) : Bwd P host c.store K c.frame es c' := by
  obtain ⟨s, f, cs⟩ := c
  obtain ⟨s', f', cs'⟩ := c'
  subst he
  refine .inl ⟨_, .core ?_, liftAs_map_core cs'⟩
  rw [blockFX_noFX]
  exact h0

theorem bwd_noStruct {c c' : Config H} (h0 : Step P host c c') (K : List (Option ContFX))
    {es : List AdminFX} (hl : LiftAs es c.code) (hn : ∀ a ∈ c.code, ¬ Struct a) :
    Bwd P host c.store K c.frame es c' :=
  bwd_core h0 K (LiftAs.eq_map_core hl hn)

theorem Bwd.step {s s' : Store H} {K : List (Option ContFX)} {f f' : Frame}
    {es es' : List AdminFX} {cs' : List Admin}
    (h : StepFX P host noFX ⟨s, K, f, es⟩ ⟨s', K, f', es'⟩) (hl : LiftAs es' cs') :
    Bwd P host s K f es ⟨s', f', cs'⟩ :=
  .inl ⟨es', h, hl⟩

/-- A label of Core code read from FX code: a Core label read as itself, or an FX label. -/
theorem lift_label {es : List AdminFX} {n : Nat} {cont : List Instr} {body : List Admin}
    (hl : LiftAs es [.label n cont body]) :
    es = [.core (.label n cont body)] ∨
      ∃ k es₁, es = [.label n k es₁] ∧ LiftIs k cont ∧ LiftAs es₁ body := by
  obtain ⟨a, rfl, ha⟩ := LiftAs.singleton_right hl
  cases ha with
  | core => exact .inl rfl
  | label hk hes => exact .inr ⟨_, _, rfl, hk, hes⟩

/-- A structured instruction after values, read from FX code. -/
theorem lift_vals_one {es : List AdminFX} {vs : List Val} {c : Admin}
    (hl : LiftAs es (vals vs ++ [c])) : ∃ a, es = cvals vs ++ [a] ∧ LiftA a c := by
  obtain ⟨A, B, rfl, hA, hB⟩ := LiftAs.append_right hl
  obtain ⟨a, rfl, ha⟩ := LiftAs.singleton_right hB
  exact ⟨a, by rw [LiftAs.vals_right hA], ha⟩

theorem map_core_vals_one (vs : List Val) (c : Admin) :
    cvals vs ++ [AdminFX.core c] = (vals vs ++ [c]).map .core := by
  simp [cvals]

/-- Split FX code read as `vals vs ++ X ++ rest` with `X` without structured instructions. -/
theorem lift_split3 {es : List AdminFX} {vs : List Val} {X rest : List Admin}
    (hl : LiftAs es (vals vs ++ X ++ rest)) (hX : ∀ a ∈ X, ¬ Struct a) :
    ∃ R, es = cvals vs ++ X.map .core ++ R ∧ LiftAs R rest := by
  obtain ⟨AB, R, rfl, hAB, hR⟩ := LiftAs.append_right hl
  obtain ⟨A, B, rfl, hA, hB⟩ := LiftAs.append_right hAB
  exact ⟨R, by rw [LiftAs.vals_right hA, LiftAs.eq_map_core hB hX], hR⟩

set_option maxHeartbeats 4000000 in
/-- **A Core step of code read from FX code is a CoreFX step, or doomed.** -/
theorem bwd {c c' : Config H} (h : Step P host c c') :
    Step P host c c' → ∀ (K : List (Option ContFX)) (es : List AdminFX), LiftAs es c.code →
      Bwd P host c.store K c.frame es c' := by
  induction h with
  | @ctxtInstrs s s' f f' vs is is' rest hs hne ih =>
    intro _ K es hl
    obtain ⟨AB, C, rfl, hAB, hC⟩ := LiftAs.append_right hl
    obtain ⟨A, B, rfl, hA, hB⟩ := LiftAs.append_right hAB
    rw [LiftAs.vals_right hA]
    rcases ih hs K B hB with ⟨B', hst, hB'⟩ | ⟨d, hd⟩
    · exact .inl ⟨_, StepFX.seq hst (LiftAs.hne' hC hne),
        LiftAs.append (LiftAs.append (liftAs_cvals vs) hB') hC⟩
    · exact .inr ⟨d, Doomed.ctx hd vs rest⟩
  | @ctxtLabel s s' f f' n cont is is' hs ih =>
    intro h0 K es hl
    rcases lift_label hl with rfl | ⟨k, es₁, rfl, hk, hes⟩
    · exact bwd_core h0 K rfl
    · rcases ih hs K es₁ hes with ⟨es', hst, hes'⟩ | ⟨d, hd⟩
      · exact .inl ⟨_, StepFX.ctxLabel hst, .cons (.label hk hes') .nil⟩
      · exact .inr ⟨d + 1, Doomed.label (vs := []) (rest := []) hd⟩
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro h0 K es hl
    obtain ⟨a, rfl, ha⟩ := lift_vals_one hl
    cases ha with
    | core => exact bwd_core h0 K (map_core_vals_one _ _)
    | block hb =>
      exact Bwd.step (StepFX.block hbt hm)
        (.cons (.label .nil (LiftAs.append (liftAs_cvals vs) (LiftIs.toAdmin hb))) .nil)
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro h0 K es hl
    obtain ⟨a, rfl, ha⟩ := lift_vals_one hl
    cases ha with
    | core => exact bwd_core h0 K (map_core_vals_one _ _)
    | loop hb =>
      exact Bwd.step (StepFX.loop hbt hm)
        (.cons (.label (.cons (.loop hb) .nil)
          (LiftAs.append (liftAs_cvals vs) (LiftIs.toAdmin hb))) .nil)
  | @ifTrue s f c bt b₁ b₂ hc =>
    intro h0 K es hl
    obtain ⟨a, rfl, ha⟩ := lift_vals_one (vs := [.i32 c]) hl
    cases ha with
    | core => exact bwd_core h0 K (map_core_vals_one _ _)
    | if_ h₁ h₂ => exact Bwd.step (StepFX.ifTrue hc) (.cons (.block h₁) .nil)
  | @ifFalse s f bt b₁ b₂ =>
    intro h0 K es hl
    obtain ⟨a, rfl, ha⟩ := lift_vals_one (vs := [.i32 0]) hl
    cases ha with
    | core => exact bwd_core h0 K (map_core_vals_one _ _)
    | if_ h₁ h₂ => exact Bwd.step StepFX.ifFalse (.cons (.block h₂) .nil)
  | @labelVals s f n cont vs =>
    intro h0 K es hl
    rcases lift_label hl with rfl | ⟨k, es₁, rfl, hk, hes⟩
    · exact bwd_core h0 K rfl
    · rw [LiftAs.vals_right hes]
      exact Bwd.step StepFX.labelVals (liftAs_cvals vs)
  | @brLabelZero s f n cont vs' vs l rest hl0 hn =>
    intro h0 K es hl
    rcases lift_label hl with rfl | ⟨k, es₁, rfl, hk, hes⟩
    · exact bwd_core h0 K rfl
    · rw [← vals_append] at hes
      obtain ⟨R, rfl, -⟩ := lift_split3 hes (by nostruct)
      have heq : cvals (vs' ++ vs) ++ [AdminFX.core (.plain (.br l))] ++ R =
          cvals vs' ++ cvals vs ++ [.core (.plain (.br l))] ++ R := by simp [cvals]
      rw [List.map_singleton, heq]
      exact Bwd.step (StepFX.brLabelZero hl0 hn) (LiftAs.append (liftAs_cvals vs)
        (LiftIs.toAdmin hk))
  | @brLabelSucc s f n cont vs l rest hl0 =>
    intro h0 K es hl
    rcases lift_label hl with rfl | ⟨k, es₁, rfl, hk, hes⟩
    · exact bwd_core h0 K rfl
    · obtain ⟨R, rfl, -⟩ := lift_split3 hes (by nostruct)
      exact Bwd.step (StepFX.brLabelSucc hl0) (LiftAs.append (liftAs_cvals vs)
        (liftAs_single_core _))
  | @returnLabel s f n cont vs rest =>
    intro h0 K es hl
    rcases lift_label hl with rfl | ⟨k, es₁, rfl, hk, hes⟩
    · exact bwd_core h0 K rfl
    · obtain ⟨R, rfl, -⟩ := lift_split3 hes (by nostruct)
      exact Bwd.step StepFX.returnLabel (LiftAs.append (liftAs_cvals vs) (liftAs_single_core _))
  | @returnCallRefLabel s f k cont vs c rest hc =>
    intro h0 K es hl
    rcases lift_label hl with rfl | ⟨k', es₁, rfl, hk, hes⟩
    · exact bwd_core h0 K rfl
    · exact .inr ⟨0, Doomed.rcr (rest := []) hc⟩
  | @trapLabel s f n cont =>
    intro h0 K es hl
    rcases lift_label hl with rfl | ⟨k, es₁, rfl, hk, hes⟩
    · exact bwd_core h0 K rfl
    · rw [LiftAs.eq_map_core hes (by nostruct)]
      exact Bwd.step StepFX.trapLabel (liftAs_single_core _)
  | @throwRefLabel s f n cont a =>
    intro h0 K es hl
    rcases lift_label hl with rfl | ⟨k, es₁, rfl, hk, hes⟩
    · exact bwd_core h0 K rfl
    · rw [LiftAs.eq_map_core hes (by nostruct)]
      exact Bwd.step StepFX.throwLabel (liftAs_map_core _)
  | @trapInstrs s f vs rest hne =>
    intro h0 K es hl
    obtain ⟨R, rfl, hR⟩ := lift_split3 hl (by nostruct)
    exact Bwd.step (StepFX.trapSeq (LiftAs.hne' hR hne)) (liftAs_single_core _)
  | @throwRefInstrs s f vs a rest hne =>
    intro h0 K es hl
    obtain ⟨R, rfl, hR⟩ := lift_split3 hl (by nostruct)
    exact Bwd.step (StepFX.throwSeq (LiftAs.hne' hR hne)) (liftAs_map_core _)
  | @parametric s f is is' hp =>
    intro h0 K es hl
    obtain ⟨args, e, heq, -, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.ParametricStep.shape hp
    exact bwd_noStruct h0 K hl (heq ▸ noStruct_fam hk (by decide))
  | @numeric s f is is' hp =>
    intro h0 K es hl
    obtain ⟨args, e, heq, -, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.NumericStep.shape hp
    exact bwd_noStruct h0 K hl (heq ▸ noStruct_fam hk (by decide))
  | @vector s f is is' hp =>
    intro h0 K es hl
    obtain ⟨args, e, heq, -, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.VectorStep.shape hp
    exact bwd_noStruct h0 K hl (heq ▸ noStruct_fam hk (by decide))
  | «variable» hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro h0 K es hl
    obtain ⟨args, e, heq, -, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.VariableStep.shape hp
    exact bwd_noStruct h0 K hl (heq ▸ noStruct_fam hk (by decide))
  | table hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro h0 K es hl
    obtain ⟨args, e, heq, -, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.TableStep.shape hp
    exact bwd_noStruct h0 K hl (heq ▸ noStruct_fam hk (by decide))
  | memory hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro h0 K es hl
    obtain ⟨args, e, heq, -, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.MemoryStep.shape hp
    exact bwd_noStruct h0 K hl (heq ▸ noStruct_fam hk (by decide))
  | reference hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro h0 K es hl
    obtain ⟨args, e, heq, -, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.RefStep.shape hp
    exact bwd_noStruct h0 K hl (heq ▸ noStruct_fam hk (by decide))
  | aggregate hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro h0 K es hl
    obtain ⟨args, e, heq, -, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.AggregateStep.shape hp
    exact bwd_noStruct h0 K hl (heq ▸ noStruct_fam hk (by decide))
  | _ =>
    intro h0 K es hl
    apply bwd_noStruct h0 K hl
    first
      | (nostruct; done)
      | (nostruct; exact not_struct_of_isCallRef ‹_›)

end Silmaril.Raw.Wasm.Unified.FXSim
