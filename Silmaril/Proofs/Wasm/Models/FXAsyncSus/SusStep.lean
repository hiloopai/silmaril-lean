module

public import Silmaril.Proofs.Wasm.Models.FXAsyncSus.Canon

/-!
# The steps of code whose deep focus is a `suspend`

`Silmaril.Proofs.Wasm.Models.FXAsyncBack.step_plug_inv` inverts steps of quiet code only. Code
whose deep focus (`Deep`) is `suspend x` is not quiet. **`step_sus`**: every host-free
`StepFX'` step of such code is the `suspend` rule at some handler frame `hs` of it, under an
outer context `Eo` (`SusOut`): the code is `Eo.plug [handler hs (E.plug (fvals vs ++
[suspend x]))]`, the tag resolves at the frame of the `suspend`, `E` does not handle it, and the
successor replaces the handler frame by the payload, the new continuation and the branch. No
other rule applies: every other rule has a different deep focus, or none.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append_cons_inj fnvF_cases no_step_fvals')
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (IsWrap Deep deep_unique deep_unique_here
  deep_label_inner deep_frame_inner deep_handler_inner not_deep_fvals deep_seq_inv deep_suspend
  deep_switch isCallRef_fval)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {x : TagIdx}

/-- **A `suspend` step**, under an outer context. -/
def SusOut (c d : ConfigFX H) (x : TagIdx) : Prop :=
  ∃ (Eo : CtxV) (hs : List HClause) (E : CtxV) (vs : List FVal) (ta : Nat) (ti : TagInst)
    (l : LabelIdx),
    c.code = Eo.plug [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x)]))] ∧
    c.store.tag? (E.frameAt (Eo.frameAt c.frame)) x = some (ta, ti) ∧ ¬ E.Handles ta ∧
    hs.find? (fun c => c.tag == ta) = some (.onLabel ta l) ∧
    d = ⟨c.store, c.conts ++ [some ⟨E.plug⟩], c.frame,
      Eo.plug (fvals vs ++ [.contRef c.conts.length, .core (.plain (.br l))])⟩

/-- The deep focus `suspend x`. -/
abbrev SX' (x : TagIdx) : AdminFX := .fx (.suspend x)

theorem nodeep_of {L : List AdminFX} {V : List FVal} {e : AdminFX} {T : List AdminFX}
    (hL : L = fvals V ++ e :: T) (he : fval? e = none) (hw : ¬ IsWrap e) (hne : e ≠ SX' x) :
    ¬ Deep (SX' x) L := by
  rw [hL]
  exact fun h => hne (deep_unique_here he hw h)

theorem nodeep_label {n : Nat} {k : List InstrFX} {b : List AdminFX} (hb : ¬ Deep (SX' x) b) :
    ¬ Deep (SX' x) [.label n k b] :=
  fun h => hb (deep_label_inner (V := []) (T := []) h)

theorem nodeep_frame {n : Nat} {fi : Frame} {b : List AdminFX} (hb : ¬ Deep (SX' x) b) :
    ¬ Deep (SX' x) [.frame n fi b] :=
  fun h => hb (deep_frame_inner (V := []) (T := []) h)

theorem nodeep_handler {hs : List HClause} {b : List AdminFX} (hb : ¬ Deep (SX' x) b) :
    ¬ Deep (SX' x) [.handler hs b] :=
  fun h => hb (deep_handler_inner (V := []) (T := []) h)

theorem nodeep_fvals {V : List FVal} : ¬ Deep (SX' x) (fvals V) := not_deep_fvals

/-- The first non-value on the way to a deep focus is in the code: the focus or a wrapper. -/
theorem deep_mem {e : AdminFX} {L : List AdminFX} (h : Deep e L) : ∃ a ∈ L, a = e ∨ IsWrap a := by
  cases h with
  | here => exact ⟨e, List.mem_append_right _ (List.mem_cons_self ..), Or.inl rfl⟩
  | label => exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Or.inr trivial⟩
  | frame => exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Or.inr trivial⟩
  | handler => exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Or.inr trivial⟩

theorem nodeep_core {cs : List Admin} : ¬ Deep (SX' x) (cs.map .core) := by
  intro h
  obtain ⟨a, ha, hor⟩ := deep_mem h
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
  rcases hor with hb | hb
  · cases hb
  · exact hb

theorem nodeep_br {V' V : List FVal} {l : LabelIdx} {rest : List AdminFX} :
    ¬ Deep (SX' x) (fvals V' ++ fvals V ++ [.core (.plain (.br l))] ++ rest) :=
  nodeep_of (V := V' ++ V) (e := .core (.plain (.br l))) (T := rest) (by simp) rfl id (by simp)

theorem nodeep_ret {V' V : List FVal} {rest : List AdminFX} :
    ¬ Deep (SX' x) (fvals V' ++ fvals V ++ [.core (.plain .return_)] ++ rest) :=
  nodeep_of (V := V' ++ V) (e := .core (.plain .return_)) (T := rest) (by simp) rfl id (by simp)

theorem nodeep_trapSeq {vs : List FVal} {rest : List AdminFX} :
    ¬ Deep (SX' x) (fvals vs ++ [.core .trap] ++ rest) :=
  nodeep_of (V := vs) (e := .core .trap) (T := rest) (by simp) rfl id (by simp)

theorem nodeep_throwSeq {vs : List FVal} {a : Nat} {rest : List AdminFX} :
    ¬ Deep (SX' x) (fvals vs ++ cthrowing a ++ rest) :=
  nodeep_of (V := vs ++ [.val (.ref (.exn a))]) (e := .core (.plain .throwRef)) (T := rest)
    (by simp [cthrowing, throwing, FVal.toAdmin, Val.toAdmin]) rfl id (by simp)

theorem nodeep_invoke {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef) :
    ¬ Deep (SX' x) (cvals vs ++ [.core (.ref (.func a)), .core c]) :=
  nodeep_of (V := liftV vs ++ [.val (.ref (.func a))]) (e := .core c) (T := [])
    (by rw [Silmaril.Proofs.Wasm.Models.FXVRuns.fvals_append, fvals_liftV]; simp [FVal.toAdmin, Val.toAdmin]) (isCallRef_fval hc) id
    (by simp)

theorem nodeep_contRef_fx {vs : List FVal} {k : Nat} {i : FXInstr} (hi : i ≠ .suspend x) :
    ¬ Deep (SX' x) (fvals vs ++ [.contRef k, .fx i]) :=
  nodeep_of (V := vs ++ [.cont k]) (e := .fx i) (T := []) (by simp [FVal.toAdmin]) rfl id
    (by simpa using hi)

theorem nodeep_null_fx {vs : List FVal} {i : FXInstr} (hi : i ≠ .suspend x) :
    ¬ Deep (SX' x) (fvals vs ++ [.core (.ref .null), .fx i]) :=
  nodeep_of (V := vs ++ [.val (.ref .null)]) (e := .fx i) (T := [])
    (by simp [FVal.toAdmin, Val.toAdmin]) rfl id (by simpa using hi)

theorem nodeep_c_contRef_fx {vs : List Val} {k : Nat} {i : FXInstr} (hi : i ≠ .suspend x) :
    ¬ Deep (SX' x) (cvals vs ++ [.contRef k, .fx i]) := by
  rw [← fvals_liftV]; exact nodeep_contRef_fx hi

theorem nodeep_c_null_fx {vs : List Val} {i : FXInstr} (hi : i ≠ .suspend x) :
    ¬ Deep (SX' x) (cvals vs ++ [.core (.ref .null), .fx i]) := by
  rw [← fvals_liftV]; exact nodeep_null_fx hi

theorem nodeep_ref_fx {r : Ref} {i : FXInstr} (hi : i ≠ .suspend x) :
    ¬ Deep (SX' x) [.core (.ref r), .fx i] :=
  nodeep_of (V := [.val (.ref r)]) (e := .fx i) (T := []) (by simp [FVal.toAdmin, Val.toAdmin])
    rfl id (by simpa using hi)

theorem nodeep_if {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List InstrFX} :
    ¬ Deep (SX' x) [.core (constI32 c), .if_ bt b₁ b₂] :=
  nodeep_of (V := [.val (Val.i32 c)]) (e := .if_ bt b₁ b₂) (T := [])
    (by simp [FVal.toAdmin, constI32]) rfl id (by simp)

theorem nodeep_dropCont {k : Nat} : ¬ Deep (SX' x) [.contRef k, .core (.plain .drop)] :=
  nodeep_of (V := [.cont k]) (e := .core (.plain .drop)) (T := []) (by simp [FVal.toAdmin]) rfl
    id (by simp)

theorem nodeep_trap : ¬ Deep (SX' x) [.core .trap] :=
  nodeep_of (V := []) (T := []) rfl rfl id (by simp)

theorem nodeep_throw {a : Nat} : ¬ Deep (SX' x) (cthrowing a) :=
  nodeep_of (Silmaril.Proofs.Wasm.Models.FXAsyncBack.throw_code a) rfl id (by simp)

theorem nodeep_vals_fx {V : List FVal} {i : FXInstr} (hi : i ≠ .suspend x) {T : List AdminFX} :
    ¬ Deep (SX' x) (fvals V ++ .fx i :: T) :=
  nodeep_of rfl rfl id (by simpa using hi)

theorem nodeep_switch {hs : List HClause} {E : CtxV} {vs : List FVal} {k : Nat} {ct : TypeIdx}
    {x' : TagIdx} :
    ¬ Deep (SX' x) [.handler hs (E.plug (fvals vs ++ [.contRef k, .fx (.switch ct x')]))] := by
  intro hd
  have h : SX' x = .fx (.switch ct x') :=
    deep_unique (deep_handler_inner (V := []) (T := []) hd) (deep_switch _ _ _ _ _)
  cases h

/-- The `suspend` rule itself. -/
theorem sus_here {s : Store H} {K : List (Option ContFX)} {f : Frame} {hs : List HClause}
    {E : CtxV} {vs : List FVal} {x' : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? (E.frameAt f) x' = some (ta, ti)) (hE : ¬ E.Handles ta)
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l))
    (hd : Deep (SX' x) [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x')]))]) :
    SusOut ⟨s, K, f, [.handler hs (E.plug (fvals vs ++ [.fx (.suspend x')]))]⟩
      ⟨s, K ++ [some ⟨E.plug⟩], f, fvals vs ++ [.contRef K.length, .core (.plain (.br l))]⟩ x := by
  have hx : SX' x = .fx (.suspend x') :=
    deep_unique (deep_handler_inner (V := []) (T := []) hd) (deep_suspend E vs x')
  have hx' : x = x' := by injection hx with h; injection h
  subst hx'
  exact ⟨.hole, hs, E, vs, ta, ti, l, rfl, ht, hE, hc, rfl⟩

theorem sus_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {vs : List FVal}
    {es es' rest : List AdminFX} (hstep : StepFX' P noHost fx ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩)
    (ih : Deep (SX' x) es → SusOut ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩ x)
    (hd : Deep (SX' x) (fvals vs ++ es ++ rest)) :
    SusOut ⟨s, K, f, fvals vs ++ es ++ rest⟩ ⟨s', K', f', fvals vs ++ es' ++ rest⟩ x := by
  have hes : ∃ V a T, es = fvals V ++ a :: T ∧ fval? a = none := by
    rcases fnvF_cases es with ⟨W, hW⟩ | hne
    · exact absurd hW (no_step_fvals' hstep W)
    · exact hne
  obtain ⟨Eo, hs, E, ws, ta, ti, l, hc, ht, hE, hcl, hd'⟩ := ih (deep_seq_inv hes hd)
  have hd'' : s' = s ∧ K' = K ++ [some ⟨E.plug⟩] ∧ f' = f ∧
      es' = Eo.plug (fvals ws ++ [.contRef K.length, .core (.plain (.br l))]) := by
    simpa only [ConfigFX.mk.injEq] using hd'
  refine ⟨.seq vs Eo rest, hs, E, ws, ta, ti, l, ?_, ht, hE, hcl, ?_⟩
  · show fvals vs ++ es ++ rest = fvals vs ++ Eo.plug _ ++ rest
    rw [show es = _ from hc]
  · rw [hd''.1, hd''.2.1, hd''.2.2.1, hd''.2.2.2]
    rfl

theorem sus_label {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame} {n : Nat}
    {k : List InstrFX} {es es' : List AdminFX}
    (ih : Deep (SX' x) es → SusOut ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩ x)
    (hd : Deep (SX' x) [.label n k es]) :
    SusOut ⟨s, K, f, [.label n k es]⟩ ⟨s', K', f', [.label n k es']⟩ x := by
  obtain ⟨Eo, hs, E, ws, ta, ti, l, hc, ht, hE, hcl, hd'⟩ :=
    ih (deep_label_inner (V := []) (T := []) hd)
  have hd'' : s' = s ∧ K' = K ++ [some ⟨E.plug⟩] ∧ f' = f ∧
      es' = Eo.plug (fvals ws ++ [.contRef K.length, .core (.plain (.br l))]) := by
    simpa only [ConfigFX.mk.injEq] using hd'
  refine ⟨.label n k Eo, hs, E, ws, ta, ti, l, ?_, ht, hE, hcl, ?_⟩
  · show [AdminFX.label n k es] = [.label n k (Eo.plug _)]
    rw [show es = _ from hc]
  · rw [hd''.1, hd''.2.1, hd''.2.2.1, hd''.2.2.2]
    rfl

theorem sus_frame {s s' : Store H} {K K' : List (Option ContFX)} {f fi fi' : Frame} {n : Nat}
    {es es' : List AdminFX}
    (ih : Deep (SX' x) es → SusOut ⟨s, K, fi, es⟩ ⟨s', K', fi', es'⟩ x)
    (hd : Deep (SX' x) [.frame n fi es]) :
    SusOut ⟨s, K, f, [.frame n fi es]⟩ ⟨s', K', f, [.frame n fi' es']⟩ x := by
  obtain ⟨Eo, hs, E, ws, ta, ti, l, hc, ht, hE, hcl, hd'⟩ :=
    ih (deep_frame_inner (V := []) (T := []) hd)
  have hd'' : s' = s ∧ K' = K ++ [some ⟨E.plug⟩] ∧ fi' = fi ∧
      es' = Eo.plug (fvals ws ++ [.contRef K.length, .core (.plain (.br l))]) := by
    simpa only [ConfigFX.mk.injEq] using hd'
  refine ⟨.frame n fi Eo, hs, E, ws, ta, ti, l, ?_, ht, hE, hcl, ?_⟩
  · show [AdminFX.frame n fi es] = [.frame n fi (Eo.plug _)]
    rw [show es = _ from hc]
  · rw [hd''.1, hd''.2.1, hd''.2.2.1, hd''.2.2.2]
    rfl

theorem sus_handler {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {hs₀ : List HClause} {es es' : List AdminFX}
    (ih : Deep (SX' x) es → SusOut ⟨s, K, f, es⟩ ⟨s', K', f', es'⟩ x)
    (hd : Deep (SX' x) [.handler hs₀ es]) :
    SusOut ⟨s, K, f, [.handler hs₀ es]⟩ ⟨s', K', f', [.handler hs₀ es']⟩ x := by
  obtain ⟨Eo, hs, E, ws, ta, ti, l, hc, ht, hE, hcl, hd'⟩ :=
    ih (deep_handler_inner (V := []) (T := []) hd)
  have hd'' : s' = s ∧ K' = K ++ [some ⟨E.plug⟩] ∧ f' = f ∧
      es' = Eo.plug (fvals ws ++ [.contRef K.length, .core (.plain (.br l))]) := by
    simpa only [ConfigFX.mk.injEq] using hd'
  refine ⟨.handler hs₀ Eo, hs, E, ws, ta, ti, l, ?_, ht, hE, hcl, ?_⟩
  · show [AdminFX.handler hs₀ es] = [.handler hs₀ (Eo.plug _)]
    rw [show es = _ from hc]
  · rw [hd''.1, hd''.2.1, hd''.2.2.1, hd''.2.2.2]
    rfl

/-- **Every step of code with deep focus `suspend x` is a `suspend` step** (`SusOut`). -/
theorem step_sus {c d : ConfigFX H} (h : StepFX' P noHost fx c d) :
    Deep (SX' x) c.code → SusOut c d x := by
  induction h with
  | core _ => exact fun hd => absurd hd nodeep_core
  | seq hstep _ ih => exact sus_seq hstep ih
  | ctxLabel _ ih => exact sus_label ih
  | ctxFrame _ ih => exact sus_frame ih
  | ctxHandler _ ih => exact sus_handler ih
  | block => exact fun hd => absurd hd (nodeep_of rfl rfl id (by simp))
  | loop => exact fun hd => absurd hd (nodeep_of rfl rfl id (by simp))
  | ifTrue => exact fun hd => absurd hd nodeep_if
  | ifFalse => exact fun hd => absurd hd nodeep_if
  | labelVals => exact fun hd => absurd hd (nodeep_label nodeep_fvals)
  | brLabelZero => exact fun hd => absurd hd (nodeep_label nodeep_br)
  | brLabelSucc => exact fun hd => absurd hd (nodeep_label (nodeep_br (V' := [])))
  | brHandler => exact fun hd => absurd hd (nodeep_handler (nodeep_br (V' := [])))
  | returnLabel => exact fun hd => absurd hd (nodeep_label (nodeep_ret (V' := [])))
  | returnHandler => exact fun hd => absurd hd (nodeep_handler (nodeep_ret (V' := [])))
  | frameVals => exact fun hd => absurd hd (nodeep_frame nodeep_fvals)
  | returnFrame => exact fun hd => absurd hd (nodeep_frame nodeep_ret)
  | handlerVals => exact fun hd => absurd hd (nodeep_handler nodeep_fvals)
  | dropCont => exact fun hd => absurd hd nodeep_dropCont
  | trapSeq => exact fun hd => absurd hd nodeep_trapSeq
  | trapLabel => exact fun hd => absurd hd (nodeep_label nodeep_trap)
  | trapFrame => exact fun hd => absurd hd (nodeep_frame nodeep_trap)
  | trapHandler => exact fun hd => absurd hd (nodeep_handler nodeep_trap)
  | throwSeq => exact fun hd => absurd hd nodeep_throwSeq
  | throwLabel => exact fun hd => absurd hd (nodeep_label nodeep_throw)
  | throwFrame => exact fun hd => absurd hd (nodeep_frame nodeep_throw)
  | throwHandler => exact fun hd => absurd hd (nodeep_handler nodeep_throw)
  | invoke hc => exact fun hd => absurd hd (nodeep_invoke hc)
  | contNew => exact fun hd => absurd hd (nodeep_ref_fx (by simp))
  | contNewNull => exact fun hd => absurd hd (nodeep_ref_fx (by simp))
  | contBind => exact fun hd => absurd hd (nodeep_contRef_fx (by simp))
  | contBindNull => exact fun hd => absurd hd (nodeep_null_fx (by simp))
  | contBindUsed => exact fun hd => absurd hd (nodeep_contRef_fx (by simp))
  | resume => exact fun hd => absurd hd (nodeep_contRef_fx (by simp))
  | resumeNull => exact fun hd => absurd hd (nodeep_null_fx (by simp))
  | resumeUsed => exact fun hd => absurd hd (nodeep_contRef_fx (by simp))
  | resumeThrow => exact fun hd => absurd hd (nodeep_c_contRef_fx (by simp))
  | resumeThrowNull => exact fun hd => absurd hd (nodeep_c_null_fx (by simp))
  | suspend ht hE hc => exact sus_here ht hE hc
  | switch => exact fun hd => absurd hd nodeep_switch

end Silmaril.Proofs.Wasm.Models.FXAsyncSus
