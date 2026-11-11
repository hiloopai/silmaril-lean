module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Seq
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label

/-!
# The every-run logic: labels

`Safe.label`: if the body `b` of `LABEL_m{cont}`, sitting on the values `us`, is
safe with `labelPostK m cont us Q k`, then `vals us ++ [LABEL_m{cont} b]` is safe
with `Q` for at most `k + 1` steps. The steps of a label are classified by
silmaril-lean's `Sim.Closure.Step.label_inv` (`LabelRed`): a step of the body, or
one of the bubbling rules, each of which is read off the exit of the body.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## More exit inversions -/

/-- An exit whose first non-value is a `return_call_ref` is a tail call. -/
theorem exits_rcr_inv {o : Outcome} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef) (h : Exits o (vals vs ++ c :: rest)) :
    ∃ vs₀ a, vs = vs₀ ++ [.ref (.func a)] ∧ o = .tail vs₀ a c := by
  have h' : FnvOk o (vs, c :: rest) := by
    rw [← fnv_vals_cons (SingleThreaded.val?_returnCallRef hc)]; exact h.fnv
  rcases SingleThreaded.Det.IsReturnCallRef.cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;>
    rcases o with _ | _ | _ | _ | _ | ⟨vs₀, a, r⟩ <;> simp_all [FnvOk]

/-- A `return_call_ref` on a null reference is not an exit. -/
theorem not_exits_null_rcr {o : Outcome} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef) (h : Exits o (vals vs ++ .ref .null :: c :: rest)) : False := by
  have e : vals vs ++ .ref .null :: c :: rest = vals (vs ++ [.ref .null]) ++ c :: rest := by
    simp [vals, Val.toAdmin]
  obtain ⟨vs₀, a, h₁, -⟩ := exits_rcr_inv hc (e ▸ h)
  have := (List.append_inj' h₁ rfl).2
  simp at this

/-- A trap, either bare or still inside a sequence. -/
theorem trap_shape_cases (vs : List Val) (rest : List Admin) :
    (vs = [] ∧ rest = []) ∨ (vs ≠ [] ∨ rest ≠ []) := by
  by_cases h : vs ≠ [] ∨ rest ≠ []
  · exact Or.inr h
  · exact Or.inl (by simpa only [ne_eq, not_or, not_not] using h)

/-! ## Labels -/

section Label

variable {m : Nat} {cont : List Instr} {us : List Val} {Q : Post H} {k : Nat}

/-- A label around a body that steps, steps. -/
theorem label_ctxt {s s' : Store H} {f f' : Frame} {b b' : List Admin}
    (h : Step P host ⟨s, f, b⟩ ⟨s', f', b'⟩) :
    Step P host ⟨s, f, vals us ++ [.label m cont b]⟩ ⟨s', f', vals us ++ [.label m cont b']⟩ :=
  Sim.Step.vals_left (Step.ctxtLabel h) us

/-- A label around a trap or an exception still inside a sequence can step. -/
theorem label_progress_cut {s : Store H} {f : Frame} {vs : List Val} {k₀ rest : List Admin}
    (hk : k₀ = [.trap] ∨ ∃ a, k₀ = throwing a) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.label m cont (vals vs ++ k₀ ++ rest)]⟩ c' := by
  rcases trap_shape_cases vs rest with ⟨rfl, rfl⟩ | hne
  · rcases hk with rfl | ⟨a, rfl⟩
    · exact ⟨_, Sim.Step.vals_left Step.trapLabel us⟩
    · exact ⟨_, Sim.Step.vals_left Step.throwRefLabel us⟩
  · rcases hk with rfl | ⟨a, rfl⟩
    · exact ⟨_, label_ctxt (Step.trapInstrs hne)⟩
    · exact ⟨_, label_ctxt (Step.throwRefInstrs hne)⟩

/-- A branch to the label itself can step. -/
theorem label_progress_br0 {s : Store H} {f : Frame} {vs₁ vs₂ : List Val} {x : LabelIdx}
    {rest : List Admin} (hx : x.toNat = 0) (hn : vs₂.length = m) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.label m cont (vals (vs₁ ++ vs₂) ++ .plain (.br x) :: rest)]⟩ c' := by
  have e : vals (vs₁ ++ vs₂) ++ .plain (.br x) :: rest =
      vals vs₁ ++ vals vs₂ ++ [.plain (.br x)] ++ rest := by simp
  exact ⟨_, Sim.Step.vals_left (e ▸ Step.brLabelZero hx hn) us⟩

/-- A label whose body has exited can step. -/
theorem label_progress {s : Store H} {f : Frame} {b : List Admin} {o : Outcome}
    (he : Exits o b) (hq : labelPostK P host m cont us Q k s f o) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.label m cont b]⟩ c' := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact ⟨_, Sim.Step.vals_left ((show b = vals vs from he) ▸ Step.labelVals) us⟩
  · obtain ⟨x, rest, hx, rfl⟩ := he
    obtain ⟨vs₁, vs₂, rfl, hn, -⟩ := hq
    exact label_progress_br0 hx hn
  · obtain ⟨x, rest, hx, rfl⟩ := he
    exact ⟨_, Sim.Step.vals_left (by simpa using Step.brLabelSucc (rest := rest) (by omega)) us⟩
  · obtain ⟨rest, rfl⟩ := he
    exact ⟨_, Sim.Step.vals_left (by simpa using Step.returnLabel (rest := rest)) us⟩
  · obtain ⟨vs, rest, rfl⟩ := he
    simpa using label_progress_cut (vs := vs) (rest := rest) (Or.inl rfl)
  · obtain ⟨vs, rest, rfl⟩ := he
    exact label_progress_cut (Or.inr ⟨a, rfl⟩)
  · obtain ⟨hr, rest, rfl⟩ := he
    have hs : Step P host ⟨s, f, [.label m cont (vals (vs ++ [.ref (.func a)]) ++ [r] ++ rest)]⟩
        ⟨s, f, vals (vs ++ [.ref (.func a)]) ++ [r]⟩ := Step.returnCallRefLabel hr
    rw [List.append_assoc, List.singleton_append, ← tail_code] at hs
    exact ⟨_, Sim.Step.vals_left hs us⟩

/-- A label whose body can step, or has exited, can step. -/
theorem label_progress' {n : Nat} {s : Store H} {f : Frame} {b : List Admin}
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1) ⟨s, f, b⟩) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.label m cont b]⟩ c' := by
  rcases h with ⟨o, he, hq⟩ | ⟨⟨⟨s', f', b'⟩, hb⟩, -⟩
  · exact label_progress he hq
  · exact ⟨_, label_ctxt hb⟩

/-- A branch to the label itself. -/
theorem label_brZero {n : Nat} {s : Store H} {f : Frame} {vs' vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = m) (hk : n ≤ k)
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1)
      ⟨s, f, vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (vals vs ++ expression cont)⟩ := by
  have e : vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest = vals (vs' ++ vs) ++ .plain (.br l) :: rest := by
    simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inl ⟨l, rfl⟩))
  have ho : o = .br 0 (vs' ++ vs) := hl ▸ exits_br_inv (e ▸ he)
  subst ho
  obtain ⟨vs₁, vs₂, hv, hn₂, hs⟩ := hq
  have hvs : vs = vs₂ := (List.append_inj' hv (hn.trans hn₂.symm)).2
  subst hvs
  simpa using hs.mono hk

/-- The body fell through. -/
theorem label_values {n : Nat} {s : Store H} {f : Frame} {vs : List Val}
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1) ⟨s, f, vals vs⟩) :
    Safe P host Q n ⟨s, f, vals us ++ vals vs⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_vals)
  have ho : o = .normal vs := exits_vals_inv he
  subst ho
  exact Safe.of_exits (o := .normal (us ++ vs)) (by simp [Exits, vals]) hq

/-- A branch to an outer label. -/
theorem label_brSucc {n : Nat} {s : Store H} {f : Frame} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : 0 < l.toNat)
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1)
      ⟨s, f, vals vs ++ [.plain (.br l)] ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (vals vs ++ [.plain (.br (labelPred l))])⟩ := by
  have e : vals vs ++ [.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inl ⟨l, rfl⟩))
  obtain ⟨j, hj⟩ : ∃ j, l.toNat = j + 1 := ⟨l.toNat - 1, by omega⟩
  have ho : o = .br (j + 1) vs := hj ▸ exits_br_inv (e ▸ he)
  subst ho
  have hx : (labelPred l).toNat = j := by
    show l.toNat - 1 = j
    omega
  exact Safe.of_exits (o := .br j (us ++ vs)) ⟨labelPred l, [], hx, by simp⟩ hq

/-- A tail call leaving the label. -/
theorem label_rcr {n : Nat} {s : Store H} {f : Frame} {vs : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef)
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1) ⟨s, f, vals vs ++ [c] ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (vals vs ++ [c])⟩ := by
  have e : vals vs ++ [c] ++ rest = vals vs ++ c :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inr (Or.inr hc)))
  obtain ⟨vs₀, a, rfl, rfl⟩ := exits_rcr_inv hc (e ▸ he)
  exact Safe.of_exits (o := .tail (us ++ vs₀) a c) ⟨hc, [], by simp [vals, Val.toAdmin]⟩ hq

/-- A `return` leaving the label. -/
theorem label_return {n : Nat} {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1)
      ⟨s, f, vals vs ++ [.plain .return_] ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (vals vs ++ [.plain .return_])⟩ := by
  have e : vals vs ++ [.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inr (Or.inl rfl)))
  have ho : o = .ret vs := exits_ret_inv (e ▸ he)
  subst ho
  exact Safe.of_exits (o := .ret (us ++ vs)) ⟨[], by simp⟩ hq

/-- An exception leaving the label. -/
theorem label_throw {n : Nat} {s : Store H} {f : Frame} {a : Nat}
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1) ⟨s, f, throwing a⟩) :
    Safe P host Q n ⟨s, f, vals us ++ throwing a⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_throwing)
  have ho : o = .throw a := exits_throw_inv (vs := []) (rest := []) (by simpa using he)
  subst ho
  exact Safe.of_exits (o := .throw a) ⟨us, [], by simp⟩ hq

/-- A trap leaving the label. -/
theorem label_trap {n : Nat} {s : Store H} {f : Frame}
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1) ⟨s, f, [.trap]⟩) :
    Safe P host Q n ⟨s, f, vals us ++ [.trap]⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_trap)
  have ho : o = .trap := exits_trap_inv (vs := []) (rest := []) he
  subst ho
  exact Safe.of_exits (o := .trap) ⟨us, [], rfl⟩ hq

/-- The steps of a label, read off the body. -/
theorem label_succ {n : Nat} {s : Store H} {f : Frame} {b : List Admin} {c' : Config H}
    (hk : n ≤ k) (ih : ∀ s f b, Safe P host (labelPostK P host m cont us Q k) n ⟨s, f, b⟩ →
      Safe P host Q n ⟨s, f, vals us ++ [.label m cont b]⟩)
    (h : Safe P host (labelPostK P host m cont us Q k) (n + 1) ⟨s, f, b⟩)
    (hst : Step P host ⟨s, f, vals us ++ [.label m cont b]⟩ c') : Safe P host Q n c' := by
  rcases c' with ⟨s', f', es'⟩
  obtain ⟨is', hr, rfl⟩ := Sim.Closure.Step.label_inv hst
  cases hr with
  | ctxt hb => exact ih _ _ _ (h.step_inv hb)
  | values vs => exact label_values h
  | brZero hl hn => exact label_brZero hl hn hk h
  | brSucc hl => exact label_brSucc hl h
  | returnCallRef hc => exact label_rcr hc h
  | return_ => exact label_return h
  | throwRef a => exact label_throw h
  | trap => exact label_trap h

/-- **Labels.** The body of a label is safe with `labelPostK`: the label is safe
for at most `k + 1` steps. -/
theorem Safe.label : ∀ {n : Nat} {s : Store H} {f : Frame} {b : List Admin}, n ≤ k + 1 →
    Safe P host (labelPostK P host m cont us Q k) n ⟨s, f, b⟩ →
    Safe P host Q n ⟨s, f, vals us ++ [.label m cont b]⟩
  | 0, _, _, _, _, _ => trivial
  | _ + 1, _, _, _, hn, h =>
    Safe.of_step (label_progress' h) fun _ hst =>
      label_succ (by omega) (fun _ _ _ => Safe.label (by omega)) h hst

end Label

/-- **Labels** for every-run weakest preconditions. -/
theorem HWP.label {s : Store H} {f : Frame} {m : Nat} {cont : List Instr} {us : List Val}
    {b : List Admin} {Q : Post H} (h : HWP P host s f b (labelPost P host m cont us Q)) :
    HWP P host s f (vals us ++ [.label m cont b]) Q :=
  fun n => Safe.label (k := n) (by omega) ((h n).post_mono fun _ _ _ => labelPost.toK n)

end Silmaril.Wasm.Logic.Hoare
