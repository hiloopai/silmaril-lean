module

public import Silmaril.Proofs.Wasm.Logic.Total.Seq

/-!
# Total correctness: labels and function frames

* `TSafe.label`: if the body of `LABEL_m{cont}` on the values `us` is totally
  correct with `labelPostT m cont us Q` (a branch to the label continues, totally
  correctly, with `cont`), the label is totally correct with `Q`;
* `TSafe.frame`: if the body of a function frame called from `f` on `us` is
  totally correct with `framePostT m f us Q` (a tail call continues, totally
  correctly, with the call it makes), the frame is totally correct with `Q`.

Both are by induction on the total-correctness derivation of the body; an
exited body that still steps (a trap or an exception bubbling) is handled by
induction on the size of its code (`Hoare.Exits.step`). The steps are classified
by silmaril-lean's `Sim.Closure.Step.label_inv` and
`Sim.Closure.Step.frame_redex_aux`, as for `Hoare.Safe.label`/`Hoare.Safe.frame`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Labels -/

section Label

variable {m : Nat} {cont : List Instr} {us : List Val} {Q : Post H}

theorem labelPostT.toK {s : Store H} {f : Frame} {o : Outcome}
    (h : labelPostT P host m cont us Q s f o) : labelPostK P host m cont us Q 0 s f o := by
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  · exact h
  · obtain ⟨vs₁, vs₂, he, hn, -⟩ := h
    exact ⟨vs₁, vs₂, he, hn, trivial⟩
  all_goals exact h

theorem tlabel_values {s : Store H} {f : Frame} {vs : List Val}
    (h : TSafe P host (labelPostT P host m cont us Q) ⟨s, f, vals vs⟩) :
    TSafe P host Q ⟨s, f, vals us ++ vals vs⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_vals)
  have ho : o = .normal vs := exits_vals_inv he
  subst ho
  exact .exit (.normal (us ++ vs)) (by simp [Exits, vals]) hq

theorem tlabel_brZero {s : Store H} {f : Frame} {vs' vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = m)
    (h : TSafe P host (labelPostT P host m cont us Q)
      ⟨s, f, vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest⟩) :
    TSafe P host Q ⟨s, f, vals us ++ (vals vs ++ expression cont)⟩ := by
  have e : vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest =
      vals (vs' ++ vs) ++ .plain (.br l) :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inl ⟨l, rfl⟩))
  have ho : o = .br 0 (vs' ++ vs) := hl ▸ exits_br_inv (e ▸ he)
  subst ho
  obtain ⟨vs₁, vs₂, hv, hn₂, hs⟩ := hq
  have hvs : vs = vs₂ := (List.append_inj' hv (hn.trans hn₂.symm)).2
  subst hvs
  simpa using hs

theorem tlabel_brSucc {s : Store H} {f : Frame} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : 0 < l.toNat)
    (h : TSafe P host (labelPostT P host m cont us Q) ⟨s, f, vals vs ++ [.plain (.br l)] ++ rest⟩) :
    TSafe P host Q ⟨s, f, vals us ++ (vals vs ++ [.plain (.br (labelPred l))])⟩ := by
  have e : vals vs ++ [.plain (.br l)] ++ rest = vals vs ++ .plain (.br l) :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inl ⟨l, rfl⟩))
  obtain ⟨j, hj⟩ : ∃ j, l.toNat = j + 1 := ⟨l.toNat - 1, by omega⟩
  have ho : o = .br (j + 1) vs := hj ▸ exits_br_inv (e ▸ he)
  subst ho
  have hx : (labelPred l).toNat = j := by
    show l.toNat - 1 = j
    omega
  exact .exit (.br j (us ++ vs)) ⟨labelPred l, [], hx, by simp⟩ hq

theorem tlabel_rcr {s : Store H} {f : Frame} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef)
    (h : TSafe P host (labelPostT P host m cont us Q) ⟨s, f, vals vs ++ [c] ++ rest⟩) :
    TSafe P host Q ⟨s, f, vals us ++ (vals vs ++ [c])⟩ := by
  have e : vals vs ++ [c] ++ rest = vals vs ++ c :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inr (Or.inr hc)))
  obtain ⟨vs₀, a, rfl, rfl⟩ := exits_rcr_inv hc (e ▸ he)
  exact .exit (.tail (us ++ vs₀) a c) ⟨hc, [], by simp [vals, Val.toAdmin]⟩ hq

theorem tlabel_return {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    (h : TSafe P host (labelPostT P host m cont us Q) ⟨s, f, vals vs ++ [.plain .return_] ++ rest⟩) :
    TSafe P host Q ⟨s, f, vals us ++ (vals vs ++ [.plain .return_])⟩ := by
  have e : vals vs ++ [.plain .return_] ++ rest = vals vs ++ .plain .return_ :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inr (Or.inl rfl)))
  have ho : o = .ret vs := exits_ret_inv (e ▸ he)
  subst ho
  exact .exit (.ret (us ++ vs)) ⟨[], by simp⟩ hq

theorem tlabel_throw {s : Store H} {f : Frame} {a : Nat}
    (h : TSafe P host (labelPostT P host m cont us Q) ⟨s, f, throwing a⟩) :
    TSafe P host Q ⟨s, f, vals us ++ throwing a⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_throwing)
  have ho : o = .throw a := exits_throw_inv (vs := []) (rest := []) (by simpa using he)
  subst ho
  exact .exit (.throw a) ⟨us, [], by simp⟩ hq

theorem tlabel_trap {s : Store H} {f : Frame}
    (h : TSafe P host (labelPostT P host m cont us Q) ⟨s, f, [.trap]⟩) :
    TSafe P host Q ⟨s, f, vals us ++ [.trap]⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_trap)
  have ho : o = .trap := exits_trap_inv (vs := []) (rest := []) he
  subst ho
  exact .exit .trap ⟨us, [], rfl⟩ hq

/-- The steps of a label, read off the body. -/
theorem tlabel_succ {s : Store H} {f : Frame} {b : List Admin} {c' : Config H}
    (ih : ∀ s' f' b', Step P host ⟨s, f, b⟩ ⟨s', f', b'⟩ →
      TSafe P host Q ⟨s', f', vals us ++ [.label m cont b']⟩)
    (h : TSafe P host (labelPostT P host m cont us Q) ⟨s, f, b⟩)
    (hst : Step P host ⟨s, f, vals us ++ [.label m cont b]⟩ c') : TSafe P host Q c' := by
  rcases c' with ⟨s', f', es'⟩
  obtain ⟨is', hr, rfl⟩ := Sim.Closure.Step.label_inv hst
  cases hr with
  | ctxt hb => exact ih _ _ _ hb
  | values vs => exact tlabel_values h
  | brZero hl hn => exact tlabel_brZero hl hn h
  | brSucc hl => exact tlabel_brSucc hl h
  | returnCallRef hc => exact tlabel_rcr hc h
  | return_ => exact tlabel_return h
  | throwRef a => exact tlabel_throw h
  | trap => exact tlabel_trap h

/-- A label around an exited body. -/
theorem tlabel_exit : ∀ (n : Nat) {s : Store H} {f : Frame} {b : List Admin} {o : Outcome},
    Sim.codeSize b < n → Exits o b → labelPostT P host m cont us Q s f o →
    TSafe P host Q ⟨s, f, vals us ++ [.label m cont b]⟩
  | 0, _, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, _, _, _, hn, he, hq =>
    .step (label_progress he (labelPostT.toK hq)) fun _ hst =>
      tlabel_succ (fun _ _ _ hb => by
        obtain ⟨rfl, rfl, he', hlt⟩ := he.step hb
        exact tlabel_exit n (by omega) he' hq) (.exit _ he hq) hst

/-- **Labels** for total correctness. -/
theorem TSafe.label : ∀ {c : Config H}, TSafe P host (labelPostT P host m cont us Q) c →
    TSafe P host Q ⟨c.store, c.frame, vals us ++ [.label m cont c.code]⟩ := by
  intro c h
  induction h with
  | exit o he hq => exact tlabel_exit _ (Nat.lt_succ_self _) he hq
  | @step c hp hs ih =>
    obtain ⟨⟨s', f', b'⟩, hc'⟩ := hp
    exact .step ⟨_, label_ctxt hc'⟩ fun _ hst =>
      tlabel_succ (fun _ _ _ hb => ih _ hb) (.step ⟨_, hc'⟩ hs) hst

end Label

/-! ## Function frames -/

section Frame

variable {m : Nat} {f : Frame} {us : List Val} {Q : Post H}

theorem framePostT.toK {s : Store H} {F : Frame} {o : Outcome}
    (h : framePostT P host m f us Q s F o) : framePostK P host m f us Q 0 s F o := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, c⟩
  any_goals exact h
  obtain ⟨vs₁, args, fn, ps, rs, h₁, h₂, h₃, h₄, -⟩ := h
  exact ⟨vs₁, args, fn, ps, rs, h₁, h₂, h₃, h₄, trivial⟩

theorem tframe_values {s : Store H} {F : Frame} {vs : List Val}
    (h : TSafe P host (framePostT P host m f us Q) ⟨s, F, vals vs⟩) :
    TSafe P host Q ⟨s, f, vals us ++ vals vs⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_vals)
  have ho : o = .normal vs := exits_vals_inv he
  subst ho
  exact .exit (.normal (us ++ vs)) (by simp [Exits, vals]) hq.2

theorem tframe_ret {s : Store H} {F : Frame} {vs' vs : List Val} {rest : List Admin}
    (hn : vs.length = m)
    (h : TSafe P host (framePostT P host m f us Q)
      ⟨s, F, vals vs' ++ vals vs ++ [.plain .return_] ++ rest⟩) :
    TSafe P host Q ⟨s, f, vals us ++ vals vs⟩ := by
  have e : vals vs' ++ vals vs ++ [.plain .return_] ++ rest =
      vals (vs' ++ vs) ++ .plain .return_ :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inr (Or.inl rfl)))
  have ho : o = .ret (vs' ++ vs) := exits_ret_inv (e ▸ he)
  subst ho
  obtain ⟨vs₁, res, hv, hn', hq⟩ := hq
  have hres : vs = res := (List.append_inj' hv (hn.trans hn'.symm)).2
  subst hres
  exact .exit (.normal (us ++ vs)) (by simp [Exits, vals]) hq

theorem tframe_callNull {s : Store H} {F : Frame} {vs : List Val} {c : Admin} {rest : List Admin}
    (hc : c.IsReturnCallRef)
    (h : TSafe P host (framePostT P host m f us Q) ⟨s, F, vals vs ++ [.ref .null, c] ++ rest⟩) :
    False := by
  have e : vals vs ++ [.ref .null, c] ++ rest = vals (vs ++ [.ref .null]) ++ c :: rest := by
    simp [vals, Val.toAdmin]
  obtain ⟨o, he, -⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inr (Or.inr hc)))
  exact not_exits_null_rcr hc (by simpa using he)

theorem tframe_callAddr {s : Store H} {F : Frame} {vs' vs : List Val} {a : Nat} {c : Admin}
    {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)} (hc : c.IsReturnCallRef)
    (hf : s.funcs[a]? = some fn) (hE : Expand fn.type (.func ps rs)) (hn : vs.length = ps.length)
    (h : TSafe P host (framePostT P host m f us Q)
      ⟨s, F, vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest⟩) :
    TSafe P host Q ⟨s, f, vals us ++ (vals vs ++ [.ref (.func a), c.retToCallIn F.module])⟩ := by
  have e : vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest =
      vals (vs' ++ vs) ++ .ref (.func a) :: c :: rest := by simp [vals]
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck fun _ =>
    e ▸ tail_code (vs' ++ vs) a c rest ▸ not_step_blocked (Or.inr (Or.inr hc))
  have ho : o = .tail (vs' ++ vs) a c := exits_tail_inv hc (e ▸ he)
  subst ho
  obtain ⟨vs₁, args, fn', ps', rs', hv, hf', hE', hn', hs⟩ := hq
  obtain rfl : fn' = fn := Option.some.inj (hf'.symm.trans hf)
  have hps : ps' = ps := by
    have h₂ := SingleThreaded.Det.Expand.det hE' hE
    injection h₂
  have hargs : vs = args := (List.append_inj' hv (hn.trans (hps ▸ hn'.symm))).2
  subst hargs
  simpa using hs

theorem tframe_throw {s : Store H} {F : Frame} {a : Nat}
    (h : TSafe P host (framePostT P host m f us Q) ⟨s, F, throwing a⟩) :
    TSafe P host Q ⟨s, f, vals us ++ throwing a⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_throwing)
  have ho : o = .throw a := exits_throw_inv (vs := []) (rest := []) (by simpa using he)
  subst ho
  exact .exit (.throw a) ⟨us, [], by simp⟩ hq

theorem tframe_trap {s : Store H} {F : Frame}
    (h : TSafe P host (framePostT P host m f us Q) ⟨s, F, [.trap]⟩) :
    TSafe P host Q ⟨s, f, vals us ++ [.trap]⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_trap)
  have ho : o = .trap := exits_trap_inv (vs := []) (rest := []) he
  subst ho
  exact .exit .trap ⟨us, [], rfl⟩ hq

/-- The steps of a frame, read off the body. -/
theorem tframe_succ {s : Store H} {F : Frame} {b : List Admin} {c' : Config H}
    (ih : ∀ s' F' b', Step P host ⟨s, F, b⟩ ⟨s', F', b'⟩ →
      TSafe P host Q ⟨s', f, vals us ++ [.frame m F' b']⟩)
    (h : TSafe P host (framePostT P host m f us Q) ⟨s, F, b⟩)
    (hst : Step P host ⟨s, f, vals us ++ [.frame m F b]⟩ c') : TSafe P host Q c' := by
  rcases c' with ⟨s', f', es'⟩
  obtain ⟨is₀, rfl, hr⟩ := Sim.Closure.Step.frame_redex_aux hst us m F b rfl
  cases hr with
  | ctxt hb => exact ih _ _ _ hb
  | values hn => exact tframe_values h
  | ret hn => exact tframe_ret hn h
  | callNull hc => exact (tframe_callNull hc h).elim
  | callAddr hc hf hE hn => exact tframe_callAddr hc hf hE hn h
  | throw => exact tframe_throw h
  | trap => exact tframe_trap h

/-- A frame around an exited body. -/
theorem tframe_exit : ∀ (n : Nat) {s : Store H} {F : Frame} {b : List Admin} {o : Outcome},
    Sim.codeSize b < n → Exits o b → framePostT P host m f us Q s F o →
    TSafe P host Q ⟨s, f, vals us ++ [.frame m F b]⟩
  | 0, _, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, _, _, _, _, hn, he, hq =>
    .step (frame_progress he (framePostT.toK hq)) fun _ hst =>
      tframe_succ (fun _ _ _ hb => by
        obtain ⟨rfl, rfl, he', hlt⟩ := he.step hb
        exact tframe_exit n (by omega) he' hq) (.exit _ he hq) hst

/-- **Function frames** for total correctness. -/
theorem TSafe.frame : ∀ {c : Config H}, TSafe P host (framePostT P host m f us Q) c →
    TSafe P host Q ⟨c.store, f, vals us ++ [.frame m c.frame c.code]⟩ := by
  intro c h
  induction h with
  | exit o he hq => exact tframe_exit _ (Nat.lt_succ_self _) he hq
  | @step c hp hs ih =>
    obtain ⟨⟨s', F', b'⟩, hc'⟩ := hp
    exact .step ⟨_, frame_ctxt hc'⟩ fun _ hst =>
      tframe_succ (fun _ _ _ hb => ih _ hb) (.step ⟨_, hc'⟩ hs) hst

end Frame

end Silmaril.Wasm.Logic.Hoare
