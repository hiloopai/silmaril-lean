module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Handler
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Frame

/-!
# The every-run logic: function frames

`Safe.frame`: if the body `b` of a function frame `FRAME_m{F}`, called from frame
`f` on the values `us`, is safe with `framePostK m f us Q k`, then
`vals us ++ [FRAME_m{F} b]` is safe with `Q` in frame `f` for at most `k + 1`
steps. The steps of a frame are classified by silmaril-lean's
`Sim.Closure.Step.frame_redex_aux` (`FrameRedex`). A tail call out of the body
(`return_call_ref-frame-addr`) continues with the call it makes, which
`framePostK` asks to be safe for `k` steps.

Limitation: a `return_call_ref` on a null reference (which traps inside a frame)
is not an exit of the body, so a body that reaches one is not safe.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

section Frame

variable {m : Nat} {f : Frame} {us : List Val} {Q : Post H} {k : Nat}

theorem frame_ctxt {s s' : Store H} {F F' : Frame} {b b' : List Admin}
    (h : Step P host ⟨s, F, b⟩ ⟨s', F', b'⟩) :
    Step P host ⟨s, f, vals us ++ [.frame m F b]⟩ ⟨s', f, vals us ++ [.frame m F' b']⟩ :=
  Sim.Step.vals_left (Step.ctxtFrame h) us

/-- A frame around a trap or an exception that is still inside a sequence steps. -/
theorem frame_progress_cut {s : Store H} {F : Frame} {vs : List Val} {k₀ rest : List Admin}
    (hk : k₀ = [.trap] ∨ ∃ a, k₀ = throwing a) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.frame m F (vals vs ++ k₀ ++ rest)]⟩ c' := by
  rcases trap_shape_cases vs rest with ⟨rfl, rfl⟩ | hne
  · rcases hk with rfl | ⟨a, rfl⟩
    · exact ⟨_, Sim.Step.vals_left Step.trapFrame us⟩
    · exact ⟨_, Sim.Step.vals_left Step.throwRefFrame us⟩
  · rcases hk with rfl | ⟨a, rfl⟩
    · exact ⟨_, frame_ctxt (Step.trapInstrs hne)⟩
    · exact ⟨_, frame_ctxt (Step.throwRefInstrs hne)⟩

/-- A tail call out of the frame steps. -/
theorem frame_progress_tail {s : Store H} {F : Frame} {vs₁ args : List Val} {a : Nat} {r : Admin}
    {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)} (hr : r.IsReturnCallRef)
    (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs)) (hn : args.length = ps.length) :
    ∃ c', Step P host
      ⟨s, f, vals us ++ [.frame m F (vals (vs₁ ++ args) ++ .ref (.func a) :: r :: rest)]⟩ c' := by
  have e : vals (vs₁ ++ args) ++ .ref (.func a) :: r :: rest =
      vals vs₁ ++ vals args ++ [.ref (.func a), r] ++ rest := by simp [vals]
  exact ⟨_, Sim.Step.vals_left (e ▸ Step.returnCallRefFrameAddr hr hf he hn) us⟩

/-- A frame whose body has exited can step. -/
theorem frame_progress {s : Store H} {F : Frame} {b : List Admin} {o : Outcome}
    (he : Exits o b) (hq : framePostK P host m f us Q k s F o) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.frame m F b]⟩ c' := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact ⟨_, Sim.Step.vals_left ((show b = vals vs from he) ▸ Step.frameVals hq.1) us⟩
  · exact hq.elim
  · obtain ⟨rest, rfl⟩ := he
    obtain ⟨vs₁, res, rfl, hn, -⟩ := hq
    exact ⟨_, Sim.Step.vals_left (by simpa using Step.returnFrame (vs' := vs₁) (rest := rest) hn) us⟩
  · obtain ⟨vs, rest, rfl⟩ := he
    simpa using frame_progress_cut (vs := vs) (rest := rest) (Or.inl rfl)
  · obtain ⟨vs, rest, rfl⟩ := he
    exact frame_progress_cut (Or.inr ⟨a, rfl⟩)
  · obtain ⟨hr, rest, rfl⟩ := he
    obtain ⟨vs₁, args, fn, ps, rs, rfl, hf, hE, hn, -⟩ := hq
    exact frame_progress_tail hr hf hE hn

theorem frame_progress' {n : Nat} {s : Store H} {F : Frame} {b : List Admin}
    (h : Safe P host (framePostK P host m f us Q k) (n + 1) ⟨s, F, b⟩) :
    ∃ c', Step P host ⟨s, f, vals us ++ [.frame m F b]⟩ c' := by
  rcases h with ⟨o, he, hq⟩ | ⟨⟨⟨s', F', b'⟩, hb⟩, -⟩
  · exact frame_progress he hq
  · exact ⟨_, frame_ctxt hb⟩

/-! ### The bubbling steps of a frame -/

theorem frame_values {n : Nat} {s : Store H} {F : Frame} {vs : List Val}
    (h : Safe P host (framePostK P host m f us Q k) (n + 1) ⟨s, F, vals vs⟩) :
    Safe P host Q n ⟨s, f, vals us ++ vals vs⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_vals)
  have ho : o = .normal vs := exits_vals_inv he
  subst ho
  exact Safe.of_exits (o := .normal (us ++ vs)) (by simp [Exits, vals]) hq.2

theorem frame_ret {n : Nat} {s : Store H} {F : Frame} {vs' vs : List Val} {rest : List Admin}
    (hn : vs.length = m)
    (h : Safe P host (framePostK P host m f us Q k) (n + 1)
      ⟨s, F, vals vs' ++ vals vs ++ [.plain .return_] ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ vals vs⟩ := by
  have e : vals vs' ++ vals vs ++ [.plain .return_] ++ rest =
      vals (vs' ++ vs) ++ .plain .return_ :: rest := by simp
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inr (Or.inl rfl)))
  have ho : o = .ret (vs' ++ vs) := exits_ret_inv (e ▸ he)
  subst ho
  obtain ⟨vs₁, res, hv, hn', hq⟩ := hq
  have hres : vs = res := (List.append_inj' hv (hn.trans hn'.symm)).2
  subst hres
  exact Safe.of_exits (o := .normal (us ++ vs)) (by simp [Exits, vals]) hq

theorem frame_callNull {n : Nat} {s : Store H} {F : Frame} {vs : List Val} {c : Admin}
    {rest : List Admin} (hc : c.IsReturnCallRef)
    (h : Safe P host (framePostK P host m f us Q k) (n + 1)
      ⟨s, F, vals vs ++ [.ref .null, c] ++ rest⟩) : False := by
  have e : vals vs ++ [.ref .null, c] ++ rest = vals (vs ++ [.ref .null]) ++ c :: rest := by
    simp [vals, Val.toAdmin]
  obtain ⟨o, he, -⟩ := h.exit_of_stuck (fun _ => e ▸ not_step_blocked (Or.inr (Or.inr hc)))
  exact not_exits_null_rcr hc (by simpa using he)

theorem frame_callAddr {n : Nat} {s : Store H} {F : Frame} {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)} (hk : n ≤ k)
    (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (hE : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length)
    (h : Safe P host (framePostK P host m f us Q k) (n + 1)
      ⟨s, F, vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest⟩) :
    Safe P host Q n ⟨s, f, vals us ++ (vals vs ++ [.ref (.func a), c.retToCallIn F.module])⟩ := by
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
  simpa using hs.mono hk

theorem frame_throw {n : Nat} {s : Store H} {F : Frame} {a : Nat}
    (h : Safe P host (framePostK P host m f us Q k) (n + 1) ⟨s, F, throwing a⟩) :
    Safe P host Q n ⟨s, f, vals us ++ throwing a⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_throwing)
  have ho : o = .throw a := exits_throw_inv (vs := []) (rest := []) (by simpa using he)
  subst ho
  exact Safe.of_exits (o := .throw a) ⟨us, [], by simp⟩ hq

theorem frame_trap {n : Nat} {s : Store H} {F : Frame}
    (h : Safe P host (framePostK P host m f us Q k) (n + 1) ⟨s, F, [.trap]⟩) :
    Safe P host Q n ⟨s, f, vals us ++ [.trap]⟩ := by
  obtain ⟨o, he, hq⟩ := h.exit_of_stuck (fun _ => not_step_trap)
  have ho : o = .trap := exits_trap_inv (vs := []) (rest := []) he
  subst ho
  exact Safe.of_exits (o := .trap) ⟨us, [], rfl⟩ hq

/-- The steps of a frame, read off the body. -/
theorem frame_succ {n : Nat} {s : Store H} {F : Frame} {b : List Admin} {c' : Config H}
    (hk : n ≤ k) (ih : ∀ s F b, Safe P host (framePostK P host m f us Q k) n ⟨s, F, b⟩ →
      Safe P host Q n ⟨s, f, vals us ++ [.frame m F b]⟩)
    (h : Safe P host (framePostK P host m f us Q k) (n + 1) ⟨s, F, b⟩)
    (hst : Step P host ⟨s, f, vals us ++ [.frame m F b]⟩ c') : Safe P host Q n c' := by
  rcases c' with ⟨s', f', es'⟩
  obtain ⟨is₀, rfl, hr⟩ := Sim.Closure.Step.frame_redex_aux hst us m F b rfl
  cases hr with
  | ctxt hb => exact ih _ _ _ (h.step_inv hb)
  | values hn => exact frame_values h
  | ret hn => exact frame_ret hn h
  | callNull hc => exact (frame_callNull hc h).elim
  | callAddr hc hf hE hn => exact frame_callAddr hk hc hf hE hn h
  | throw => exact frame_throw h
  | trap => exact frame_trap h

/-- **Function frames.** -/
theorem Safe.frame : ∀ {n : Nat} {s : Store H} {F : Frame} {b : List Admin}, n ≤ k + 1 →
    Safe P host (framePostK P host m f us Q k) n ⟨s, F, b⟩ →
    Safe P host Q n ⟨s, f, vals us ++ [.frame m F b]⟩
  | 0, _, _, _, _, _ => trivial
  | _ + 1, _, _, _, hn, h =>
    Safe.of_step (frame_progress' h) fun _ hst =>
      frame_succ (by omega) (fun _ _ _ => Safe.frame (by omega)) h hst

end Frame

end Silmaril.Wasm.Logic.Hoare
