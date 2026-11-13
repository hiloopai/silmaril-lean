module

public import Silmaril.Raw.Wasm.Unified.FXSim.Basic
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.SingleThreaded.Determinism.Family
public import Silmaril.Wasm.Behaviour.Semantics.V2.Defs

/-!
# Doomed Core code has no behaviours (unrefined)

`Doomed d cs` (`Silmaril.Wasm.Unified.Versions.FXSim`): the first non-value of `cs` is a
`return_call_ref`, or a label (`d` deep) with a doomed body. A Core step from doomed code goes to
doomed code of smaller depth (`doomed_step`: the only steps pop a label around a
`return_call_ref` or step inside such a label), so a run from doomed code reaches no result and
does not diverge: `doomed_behavioursOf` (the behaviours are empty).

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.Unified.FXSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Unified.Versions
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded.Det (famOf FamShape)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem hot_val_none {a : Admin} (h : Hot a) : a.val? = none := by
  rcases h with ⟨n, cont, body, rfl⟩ | h
  · rfl
  · exact Admin.val?_of_isReturnCallRef h

@[simp] theorem not_hot_toAdmin (v : Val) : ¬ Hot v.toAdmin := fun h => by
  have := hot_val_none h
  rw [Admin.val?_toAdmin] at this
  cases this

@[simp] theorem noHot_vals (vs : List Val) : ∀ a ∈ vals vs, ¬ Hot a := by
  intro a ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
  exact not_hot_toAdmin v

@[simp] theorem hot_plain (i : Instr) : Hot (.plain i) ↔ Admin.IsReturnCallRef (.plain i) := by
  simp [Hot]

@[simp] theorem not_hot_ref (r : Ref) : ¬ Hot (.ref r) := by simp [Hot, Admin.IsReturnCallRef]

@[simp] theorem not_hot_callRefType (d : Silmaril.Wasm.Validation.DefType) : ¬ Hot (.callRefType d) := by
  simp [Hot, Admin.IsReturnCallRef]

@[simp] theorem not_hot_handler (n : Nat) (cs : List Catch) (b : List Admin) :
    ¬ Hot (.handler n cs b) := by
  simp [Hot, Admin.IsReturnCallRef]

@[simp] theorem not_hot_frame (n : Nat) (f : Frame) (b : List Admin) : ¬ Hot (.frame n f b) := by
  simp [Hot, Admin.IsReturnCallRef]

@[simp] theorem not_hot_trap : ¬ Hot .trap := by simp [Hot, Admin.IsReturnCallRef]

theorem forall_noHot_vals (vs : List Val) : (∀ a ∈ vals vs, ¬ Hot a) = True :=
  eq_true (noHot_vals vs)

theorem not_hot_of_isCallRef {c : Admin} (h : c.IsCallRef) : ¬ Hot c := by
  rintro (⟨n, cont, body, rfl⟩ | h')
  · exact h
  · rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsCallRef] at h
    · cases i <;> simp at h
      exact h'
    · exact h'

theorem famOf_of_hot {e : Admin} (h : Hot e) : famOf e = .control := by
  rcases h with ⟨n, cont, body, rfl⟩ | h
  · rfl
  · rcases e with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsReturnCallRef] at h
    · cases i <;> simp at h
      rfl
    · rfl

/-- Close `∀ a ∈ code, ¬ Hot a` for a literal left-hand side. -/
macro "nohot" : tactic =>
  `(tactic| (simp only [List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil,
      and_true, true_and, forall_noHot_vals]; try simp [Admin.IsReturnCallRef, constI32]))

/-- Doomed code, read off at its first non-value. -/
def DHead (d : Nat) (a : Admin) : Prop :=
  (d = 0 ∧ a.IsReturnCallRef) ∨
    ∃ d' n cont body, d = d' + 1 ∧ a = .label n cont body ∧ Doomed d' body

theorem DHead.hot {d : Nat} {a : Admin} (h : DHead d a) : Hot a := by
  rcases h with ⟨-, h⟩ | ⟨d', n, cont, body, -, rfl, -⟩
  · exact Or.inr h
  · exact Or.inl ⟨n, cont, body, rfl⟩

theorem Doomed.inv {d : Nat} {X : List Admin} (h : Doomed d X) :
    ∃ ws a r, X = vals ws ++ a :: r ∧ DHead d a := by
  cases h with
  | rcr hc => exact ⟨_, _, _, rfl, Or.inl ⟨rfl, hc⟩⟩
  | label hd => exact ⟨_, _, _, rfl, Or.inr ⟨_, _, _, _, rfl, rfl, hd⟩⟩

theorem Doomed.of_head {d : Nat} {a : Admin} (h : DHead d a) (ws : List Val) (r : List Admin) :
    Doomed d (vals ws ++ a :: r) := by
  rcases h with ⟨rfl, hc⟩ | ⟨d', n, cont, body, rfl, rfl, hd⟩
  · exact .rcr hc
  · exact .label hd

/-- The first non-value of doomed code is its doomed head. -/
theorem Doomed.head {d : Nat} {vs : List Val} {b : Admin} {rest : List Admin}
    (h : Doomed d (vals vs ++ b :: rest)) (hb : b.val? = none) : DHead d b := by
  obtain ⟨ws, a, r, heq, ha⟩ := Doomed.inv h
  obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj hb (hot_val_none ha.hot) heq
  exact ha

theorem Doomed.not_noHot {d : Nat} {X : List Admin} (h : Doomed d X) (hn : ∀ a ∈ X, ¬ Hot a) :
    False := by
  obtain ⟨ws, a, r, rfl, ha⟩ := Doomed.inv h
  exact hn a (List.mem_append_right _ (List.mem_cons_self ..)) ha.hot

theorem Doomed.ctx {d : Nat} {X : List Admin} (h : Doomed d X) (vs : List Val)
    (rest : List Admin) : Doomed d (vals vs ++ X ++ rest) := by
  obtain ⟨ws, a, r, rfl, ha⟩ := Doomed.inv h
  have heq : vals vs ++ (vals ws ++ a :: r) ++ rest = vals (vs ++ ws) ++ a :: (r ++ rest) := by
    simp
  rw [heq]
  exact Doomed.of_head ha _ _

theorem not_doomed_vals {d : Nat} {vs : List Val} (h : Doomed d (vals vs)) : False :=
  Doomed.not_noHot h (noHot_vals vs)

theorem doomed_single {d : Nat} {a : Admin} (h : Doomed d [a]) : DHead d a := by
  obtain ⟨ws, a', r, heq, ha⟩ := Doomed.inv h
  cases ws with
  | nil =>
    have h' : a = a' ∧ r = [] := by simpa [vals] using heq
    obtain ⟨rfl, -⟩ := h'
    exact ha
  | cons w ws => simp [vals] at heq

/-- A label of doomed code has a doomed body one level less deep. -/
theorem doomed_label {d n : Nat} {cont : List Instr} {body : List Admin}
    (h : Doomed d [.label n cont body]) : ∃ d', d = d' + 1 ∧ Doomed d' body := by
  rcases doomed_single h with ⟨-, hc⟩ | ⟨d', n', cont', body', rfl, heq, hd⟩
  · exact absurd hc (by simp [Admin.IsReturnCallRef])
  · cases heq
    exact ⟨d', rfl, hd⟩

/-- A doomed body whose first non-value is `b` (not a label or `return_call_ref`) is impossible. -/
theorem doomed_body_false {d : Nat} {vs : List Val} {b : Admin} {rest : List Admin}
    (h : Doomed d (vals vs ++ b :: rest)) (hb : b.val? = none) (hnot : ¬ Hot b) : False :=
  hnot (Doomed.head h hb).hot

set_option maxHeartbeats 2000000 in
/-- **A Core step from doomed code goes to doomed code of smaller depth.** -/
theorem doomed_step {c c' : Config H} (h : Step P host c c') :
    ∀ d, Doomed d c.code → ∃ d' < d, Doomed d' c'.code := by
  induction h with
  | @ctxtInstrs s s' f f' vs is is' rest hs hne ih =>
    intro d hd
    obtain ⟨vs₁, b, es₁, hb, rfl⟩ := Sim.exists_head_of_not_all (Step.not_all_isVal hs)
    have heq : vals vs ++ (vals vs₁ ++ b :: es₁) ++ rest = vals (vs ++ vs₁) ++ b :: (es₁ ++ rest) := by
      simp
    have hd' : Doomed d (vals (vs ++ vs₁) ++ b :: (es₁ ++ rest)) := heq ▸ hd
    obtain ⟨d', hlt, hd''⟩ := ih d (Doomed.of_head (Doomed.head hd' hb) vs₁ es₁)
    exact ⟨d', hlt, Doomed.ctx hd'' vs rest⟩
  | @ctxtLabel s s' f f' n cont is is' hs ih =>
    intro d hd
    obtain ⟨d₀, rfl, hd₀⟩ := doomed_label hd
    obtain ⟨d', hlt, hd'⟩ := ih d₀ hd₀
    exact ⟨d' + 1, Nat.succ_lt_succ hlt, Doomed.label (vs := []) (rest := []) hd'⟩
  | @returnCallRefLabel s f k cont vs c rest hc =>
    intro d hd
    obtain ⟨d₀, rfl, -⟩ := doomed_label hd
    exact ⟨0, Nat.succ_pos _, Doomed.rcr (rest := []) hc⟩
  | @labelVals s f n cont vs =>
    intro d hd
    obtain ⟨d₀, -, hd₀⟩ := doomed_label hd
    exact (not_doomed_vals hd₀).elim
  | @brLabelZero s f n cont vs' vs l rest hl hn =>
    intro d hd
    obtain ⟨d₀, -, hd₀⟩ := doomed_label hd
    have heq : vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest =
        vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
    rw [heq] at hd₀
    exact (doomed_body_false hd₀ rfl (by simp [Hot, Admin.IsReturnCallRef])).elim
  | @brLabelSucc s f n cont vs l rest hl =>
    intro d hd
    obtain ⟨d₀, -, hd₀⟩ := doomed_label hd
    have heq : vals vs ++ [.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by simp
    rw [heq] at hd₀
    exact (doomed_body_false hd₀ rfl (by simp [Hot, Admin.IsReturnCallRef])).elim
  | @returnLabel s f n cont vs rest =>
    intro d hd
    obtain ⟨d₀, -, hd₀⟩ := doomed_label hd
    have heq : vals vs ++ [.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by simp
    rw [heq] at hd₀
    exact (doomed_body_false hd₀ rfl (by simp [Hot, Admin.IsReturnCallRef])).elim
  | @trapLabel s f n cont =>
    intro d hd
    obtain ⟨d₀, -, hd₀⟩ := doomed_label hd
    exact (Doomed.not_noHot hd₀ (by simp [Hot, Admin.IsReturnCallRef])).elim
  | @throwRefLabel s f n cont a =>
    intro d hd
    obtain ⟨d₀, -, hd₀⟩ := doomed_label hd
    exact (Doomed.not_noHot hd₀ (by simp [Hot, Admin.IsReturnCallRef, throwing])).elim
  | @trapInstrs s f vs rest hne =>
    intro d hd
    have heq : vals vs ++ [.trap] ++ rest = vals vs ++ .trap :: rest := by simp
    rw [heq] at hd
    exact (doomed_body_false hd rfl (by simp [Hot, Admin.IsReturnCallRef])).elim
  | @throwRefInstrs s f vs a rest hne =>
    intro d hd
    have heq : vals vs ++ throwing a ++ rest =
        vals (vs ++ [.ref (.exn a)]) ++ .plain .throwRef :: rest := by
      simp [throwing, vals, Val.toAdmin]
    rw [heq] at hd
    exact (doomed_body_false hd rfl (by simp [Hot, Admin.IsReturnCallRef])).elim
  | @parametric s f is is' hp =>
    intro d hd
    change Doomed d is at hd
    obtain ⟨args, e, heq, he, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.ParametricStep.shape hp
    rw [heq] at hd
    exact absurd (famOf_of_hot (Doomed.head hd (rest := []) he).hot) (by rw [hk]; decide)
  | @numeric s f is is' hp =>
    intro d hd
    change Doomed d is at hd
    obtain ⟨args, e, heq, he, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.NumericStep.shape hp
    rw [heq] at hd
    exact absurd (famOf_of_hot (Doomed.head hd (rest := []) he).hot) (by rw [hk]; decide)
  | @vector s f is is' hp =>
    intro d hd
    change Doomed d is at hd
    obtain ⟨args, e, heq, he, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.VectorStep.shape hp
    rw [heq] at hd
    exact absurd (famOf_of_hot (Doomed.head hd (rest := []) he).hot) (by rw [hk]; decide)
  | «variable» hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro d hd
    change Doomed d code at hd
    obtain ⟨args, e, heq, he, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.VariableStep.shape hp
    rw [heq] at hd
    exact absurd (famOf_of_hot (Doomed.head hd (rest := []) he).hot) (by rw [hk]; decide)
  | table hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro d hd
    change Doomed d code at hd
    obtain ⟨args, e, heq, he, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.TableStep.shape hp
    rw [heq] at hd
    exact absurd (famOf_of_hot (Doomed.head hd (rest := []) he).hot) (by rw [hk]; decide)
  | memory hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro d hd
    change Doomed d code at hd
    obtain ⟨args, e, heq, he, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.MemoryStep.shape hp
    rw [heq] at hd
    exact absurd (famOf_of_hot (Doomed.head hd (rest := []) he).hot) (by rw [hk]; decide)
  | reference hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro d hd
    change Doomed d code at hd
    obtain ⟨args, e, heq, he, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.RefStep.shape hp
    rw [heq] at hd
    exact absurd (famOf_of_hot (Doomed.head hd (rest := []) he).hot) (by rw [hk]; decide)
  | aggregate hp =>
    rename_i c₀ c₀'
    rcases c₀ with ⟨s, f, code⟩
    intro d hd
    change Doomed d code at hd
    obtain ⟨args, e, heq, he, hk⟩ := Silmaril.Wasm.SingleThreaded.Det.AggregateStep.shape hp
    rw [heq] at hd
    exact absurd (famOf_of_hot (Doomed.head hd (rest := []) he).hot) (by rw [hk]; decide)
  | _ =>
    intro d hd
    exfalso
    apply Doomed.not_noHot hd
    first
      | (nohot; done)
      | (nohot; exact not_hot_of_isCallRef ‹_›)

/-- Runs from doomed code stay doomed. -/
theorem doomed_steps {c c' : Config H} (h : Steps P host c c') {d : Nat}
    (hd : Doomed d c.code) : ∃ d', Doomed d' c'.code := by
  induction h with
  | refl => exact ⟨d, hd⟩
  | tail _ hst ih =>
    obtain ⟨d₁, hd₁⟩ := ih
    obtain ⟨d', -, hd'⟩ := doomed_step hst d₁ hd₁
    exact ⟨d', hd'⟩

/-- Doomed code is not a result. -/
theorem doomed_not_result {d : Nat} {X : List Admin} (h : Doomed d X) (r : Result) :
    X ≠ r.toAdmin := by
  rintro rfl
  cases r with
  | values vs => exact not_doomed_vals h
  | throw a => exact Doomed.not_noHot h (by simp [Result.toAdmin, Hot, Admin.IsReturnCallRef])
  | trap => exact Doomed.not_noHot h (by simp [Result.toAdmin, Hot, Admin.IsReturnCallRef])

/-- Doomed code does not diverge. -/
theorem doomed_not_diverges {c : Config H} {d : Nat} (hd : Doomed d c.code) :
    ¬ Silmaril.InfiniteTrace (Step P host) c := by
  rintro ⟨tr, h0, hstep⟩
  have key : ∀ n, ∃ d', d' + n ≤ d ∧ Doomed d' (tr n).code := by
    intro n
    induction n with
    | zero => exact ⟨d, le_refl _, h0 ▸ hd⟩
    | succ n ih =>
      obtain ⟨d₁, hle, hd₁⟩ := ih
      obtain ⟨d', hlt, hd'⟩ := doomed_step (hstep n) d₁ hd₁
      exact ⟨d', by omega, hd'⟩
  obtain ⟨d', hle, -⟩ := key (d + 1)
  omega

/-- **Doomed code has no behaviours.** -/
theorem doomed_behavioursOf {s : Store H} {f : Frame} {cs : List Admin} {d : Nat}
    (hd : Doomed d cs) : behavioursOf P host ⟨s, f, cs⟩ = ∅ := by
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro (⟨c', r, hst, hc, -⟩ | ⟨-, hdiv⟩)
  · obtain ⟨d', hd'⟩ := doomed_steps hst (c := ⟨s, f, cs⟩) hd
    exact doomed_not_result hd' r hc
  · exact doomed_not_diverges (c := ⟨s, f, cs⟩) hd hdiv

end Silmaril.Raw.Wasm.Unified.FXSim
