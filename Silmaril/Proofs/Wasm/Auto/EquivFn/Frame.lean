module

public import Silmaril.Wasm.Auto.EquivFn.Defs
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Behaviour.Semantics.V3

/-!
# Function-level equivalence: frames, calls and behaviours

* `wp_frame_pinned`: a frame around a pinned body (every run ends with outcome `o'` in store
  `s'`, `o'` falling through with the frame's arity or trapping) has the weakest precondition
  `FrameOut` of that outcome, in both readings. Forward by running the body to its exit inside
  the frame (`steps_frame`) and the frame's exit step; backward by the frame rule. This is the
  converse of the frame rule for pinned bodies; it is false for arbitrary bodies.
* `wp_call_pinned`: the same for a call of a Wasm function whose body is pinned
  (`call_step_inv`: the call's only step enters the frame);
* `callEquivAt_of_pinned`: two functions whose bodies are pinned to the same outcome are
  call-equivalent;
* `tfspec_of_pinned`, `behaviours_of_pinned`: a pinned body gives a total specification and the
  behaviour set `{outBeh o'}` of `$invoke`.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EquivFn

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EquivFn
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv (wp_step_inv wp_exit_post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Runs -/

theorem wp_steps_inv {m : Corr} {Q : Post H} {c c' : Config H}
    (h : Wp m P host c.store c.frame c.code Q) (hs : Steps P host c c') :
    Wp m P host c'.store c'.frame c'.code Q := by
  induction hs with
  | refl => exact h
  | @tail b d _ hst ih =>
    rcases b with ⟨s₁, f₁, c₁⟩
    rcases d with ⟨s₂, f₂, c₂⟩
    exact wp_step_inv ih hst

theorem steps_frame {n : Nat} {f : Frame} {us : List Val} {c c' : Config H}
    (hs : Steps P host c c') :
    Steps P host ⟨c.store, f, vals us ++ [.frame n c.frame c.code]⟩
      ⟨c'.store, f, vals us ++ [.frame n c'.frame c'.code]⟩ := by
  induction hs with
  | refl => exact .refl
  | @tail b d _ hst ih =>
    rcases b with ⟨s₁, f₁, c₁⟩
    rcases d with ⟨s₂, f₂, c₂⟩
    exact ih.tail (frame_ctxt (m := n) (f := f) (us := us) hst)

theorem tsafe_exists_exit {Q : Post H} {c : Config H} (h : TSafe P host Q c) :
    ∃ c' o, Steps P host c c' ∧ Exits o c'.code ∧ Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, o, .refl, he, hq⟩
  | step hp _ ih =>
    obtain ⟨c₁, h₁⟩ := hp
    obtain ⟨c', o, hs, he, hq⟩ := ih c₁ h₁
    exact ⟨c', o, Relation.ReflTransGen.head h₁ hs, he, hq⟩

/-- A configuration with exactly one successor has the weakest precondition of it. -/
theorem wp_iff_of_det {m : Corr} {Q : Post H} {c c' : Config H} (hst : Step P host c c')
    (huniq : ∀ d, Step P host c d → d = c') :
    Wp m P host c.store c.frame c.code Q ↔ Wp m P host c'.store c'.frame c'.code Q := by
  constructor
  · intro h
    exact wp_steps_inv h (Relation.ReflTransGen.single hst)
  · intro h
    cases m with
    | part =>
      intro k
      cases k with
      | zero => trivial
      | succ k =>
        exact Safe.of_step ⟨c', hst⟩ fun d hd => by
          rw [huniq d hd]
          exact h k
    | total =>
      exact TSafe.step ⟨c', hst⟩ fun d hd => by
        rw [huniq d hd]
        exact h

/-! ## Frames around exited bodies -/

theorem wp_frame_vals {m : Corr} {n : Nat} {s : Store H} {F f : Frame} {us res : List Val}
    {Q : Post H} (hn : res.length = n) (h : Wp m P host s f (vals us ++ [.frame n F (vals res)]) Q) :
    Q s f (.normal (us ++ res)) := by
  have hst : Step P host ⟨s, f, vals us ++ [.frame n F (vals res)]⟩ ⟨s, f, vals us ++ vals res⟩ :=
    Sim.Step.vals_left (Step.frameVals hn) us
  have h₁ := wp_step_inv h hst
  exact wp_exit_post h₁ (by simp [Exits])

theorem wp_frame_trap {m : Corr} {n : Nat} {s : Store H} {F f : Frame} {us vs : List Val}
    {rest : List Admin} {Q : Post H}
    (h : Wp m P host s f (vals us ++ [.frame n F (vals vs ++ .trap :: rest)]) Q) :
    Q s f .trap := by
  have h₁ : Wp m P host s f (vals us ++ [.frame n F [.trap]]) Q := by
    rcases trap_shape_cases vs rest with ⟨rfl, rfl⟩ | hne
    · simpa using h
    · have hst := frame_ctxt (P := P) (host := host) (m := n) (f := f) (us := us)
        (Step.trapInstrs (s := s) (f := F) (vs := vs) (rest := rest) hne)
      have e : vals vs ++ [Admin.trap] ++ rest = vals vs ++ .trap :: rest := by simp
      rw [e] at hst
      exact wp_step_inv h hst
  have hst : Step P host ⟨s, f, vals us ++ [.frame n F [.trap]]⟩ ⟨s, f, vals us ++ [.trap]⟩ :=
    Sim.Step.vals_left (Step.trapFrame (s := s) (f := f) (fi := F) (n := n)) us
  exact wp_exit_post (wp_step_inv h₁ hst) ⟨us, [], by simp⟩

theorem framePostK_of_out {n k : Nat} {f F : Frame} {us : List Val} {Q : Post H} {s : Store H}
    {o : Outcome} (h : FrameOut n f us Q s o) : framePostK P host n f us Q k s F o := by
  rcases o with res | _ | _ | _ | _ | _
  · exact h
  · exact h.elim
  · exact h.elim
  · exact h
  · exact h.elim
  · exact h.elim

theorem framePostT_of_out {n : Nat} {f F : Frame} {us : List Val} {Q : Post H} {s : Store H}
    {o : Outcome} (h : FrameOut n f us Q s o) : framePostT P host n f us Q s F o := by
  rcases o with res | _ | _ | _ | _ | _
  · exact h
  · exact h.elim
  · exact h.elim
  · exact h
  · exact h.elim
  · exact h.elim

/-! ## The converse of the frame rule for pinned bodies -/

/-- **A frame around a pinned body.** -/
theorem wp_frame_pinned {m : Corr} {n : Nat} {s s' : Store H} {F f : Frame} {b : List Admin}
    {o' : Outcome} {us : List Val} {Q : Post H} (hp : Pinned P host s F b s' o') (ho : Fits n o') :
    Wp m P host s f (vals us ++ [.frame n F b]) Q ↔ FrameOut n f us Q s' o' := by
  constructor
  · show Wp m P host s f (vals us ++ [.frame n F b]) Q → FrameOut n f us Q s' o'
    intro h
    obtain ⟨c', o, hs, he, hq⟩ := tsafe_exists_exit hp
    obtain ⟨hs', rfl⟩ := hq
    have hrun : Steps P host ⟨s, f, vals us ++ [.frame n F b]⟩
        ⟨c'.store, f, vals us ++ [.frame n c'.frame c'.code]⟩ :=
      steps_frame (n := n) (f := f) (us := us) hs
    have h₁ : Wp m P host s' f (vals us ++ [.frame n c'.frame c'.code]) Q := by
      rw [← hs']
      exact wp_steps_inv (c := ⟨s, f, vals us ++ [.frame n F b]⟩) h hrun
    rcases o with res | _ | _ | _ | _ | _
    · have hc : c'.code = vals res := he
      have h₂ : Wp m P host s' f (vals us ++ [.frame n c'.frame (vals res)]) Q := hc ▸ h₁
      exact ⟨ho, wp_frame_vals ho h₂⟩
    · exact ho.elim
    · exact ho.elim
    · obtain ⟨vs, rest, hc⟩ := he
      have h₂ : Wp m P host s' f (vals us ++ [.frame n c'.frame (vals vs ++ .trap :: rest)]) Q :=
        hc ▸ h₁
      exact wp_frame_trap h₂
    · exact ho.elim
    · exact ho.elim
  · show FrameOut n f us Q s' o' → Wp m P host s f (vals us ++ [.frame n F b]) Q
    intro hout
    have hpin : ∀ s₁ F₁ o, Pin s' o' s₁ F₁ o → FrameOut n f us Q s₁ o := by
      rintro s₁ F₁ o ⟨rfl, rfl⟩
      exact hout
    cases m with
    | part =>
      intro k
      have hb : Safe P host (framePostK P host n f us Q k) k ⟨s, F, b⟩ :=
        (TWP.hwp hp k).post_mono fun s₁ F₁ o h₁ => framePostK_of_out (hpin s₁ F₁ o h₁)
      exact Safe.frame (m := n) (f := f) (us := us) (Q := Q) (k := k) (by omega) hb
    | total =>
      have hb : TSafe P host (framePostT P host n f us Q) ⟨s, F, b⟩ :=
        TSafe.post_mono hp fun s₁ F₁ o h₁ => framePostT_of_out (hpin s₁ F₁ o h₁)
      exact TSafe.frame (m := n) (f := f) (us := us) hb

/-- A pinned body stays pinned inside its function label. -/
theorem pinned_label {n : Nat} {s s' : Store H} {F : Frame} {b : List Admin} {o' : Outcome}
    (hp : Pinned P host s F b s' o') (ho : Fits n o') :
    Pinned P host s F [.label n [] b] s' o' := by
  have hl : TSafe P host (labelPostT P host n [] [] (Pin s' o')) ⟨s, F, b⟩ := by
    refine TSafe.post_mono hp ?_
    rintro s₁ F₁ o ⟨rfl, rfl⟩
    rcases o with res | _ | _ | _ | _ | _
    · exact ⟨rfl, by simp⟩
    · exact ho.elim
    · exact ho.elim
    · exact ⟨rfl, rfl⟩
    · exact ho.elim
    · exact ho.elim
  have h₁ := TSafe.label (m := n) (cont := []) (us := []) hl
  show TSafe P host (Pin s' o') ⟨s, F, [.label n [] b]⟩
  simpa using h₁

/-! ## Calls -/

/-- **A call of a function whose body is pinned.** -/
theorem wp_call_pinned {m : Corr} {s s' : Store H} {f : Frame} {vs₀ args : List Val} {a : Nat}
    {c : Admin} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)} {o' : Outcome}
    {Q : Post H} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length)
    (hp : Pinned P host s (Frame.forCall fi.module args code.locals) (expression code.body) s' o')
    (ho : Fits rs.length o') :
    Wp m P host s f (vals vs₀ ++ vals args ++ [.ref (.func a), c]) Q ↔
      FrameOut rs.length f vs₀ Q s' o' := by
  have hstep : Step P host ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c]⟩
      ⟨s, f, vals vs₀ ++ [callFrame fi code rs args]⟩ := by
    simpa [callFrame] using Sim.Step.vals_left (Step.callRefFunc hc hf he hn hcode) vs₀
  have h₁ := wp_iff_of_det (m := m) (Q := Q) hstep fun d hd => call_step_inv hc hf hcode he hn hd
  rw [h₁]
  exact wp_frame_pinned (pinned_label hp ho) ho

/-- **Call-level equivalence of two functions whose bodies are pinned to the same outcome.** -/
theorem callEquivAt_of_pinned {s s' : Store H} {a₁ a₂ : Nat} {args : List Val}
    {fi₁ fi₂ : FuncInst H} {code₁ code₂ : Func} {ps₁ rs₁ ps₂ rs₂ : Ty (.list .val)} {o' : Outcome}
    (hf₁ : s.funcs[a₁]? = some fi₁) (hcode₁ : fi₁.code = .wasm code₁)
    (he₁ : Expand fi₁.type (.func ps₁ rs₁)) (hn₁ : args.length = ps₁.length)
    (hf₂ : s.funcs[a₂]? = some fi₂) (hcode₂ : fi₂.code = .wasm code₂)
    (he₂ : Expand fi₂.type (.func ps₂ rs₂)) (hn₂ : args.length = ps₂.length)
    (hrs : rs₁.length = rs₂.length)
    (hp₁ : Pinned P host s (Frame.forCall fi₁.module args code₁.locals) (expression code₁.body) s' o')
    (hp₂ : Pinned P host s (Frame.forCall fi₂.module args code₂.locals) (expression code₂.body) s' o')
    (ho : Fits rs₁.length o') :
    CallEquivAt P host s a₁ a₂ args := by
  intro m f vs₀ c Q hc
  have ho₂ : Fits rs₂.length o' := hrs ▸ ho
  rw [wp_call_pinned hc hf₁ hcode₁ he₁ hn₁ hp₁ ho, wp_call_pinned hc hf₂ hcode₂ he₂ hn₂ hp₂ ho₂, hrs]

/-! ## Specifications and behaviours -/

/-- **A pinned body gives a total specification** of the call. -/
theorem tfspec_of_pinned {s s' : Store H} {args : List Val} {a : Nat} {fi : FuncInst H}
    {code : Func} {ps rs : Ty (.list .val)} {o' : Outcome}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (he : Expand fi.type (.func ps rs)) (hn : args.length = ps.length)
    (hp : Pinned P host s (Frame.forCall fi.module args code.locals) (expression code.body) s' o')
    (ho : Fits rs.length o') :
    TFSpecAt P host a (pinSpec s args s' o') := by
  rintro s₁ args₁ ⟨rfl, rfl⟩ f vs₀ c hc
  refine (wp_call_pinned (m := .total) hc hf hcode he hn hp ho).mpr ?_
  rcases o' with res | _ | _ | _ | _ | _
  · exact ⟨ho, rfl, Or.inl ⟨res, rfl, rfl, rfl⟩⟩
  · exact ho.elim
  · exact ho.elim
  · exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
  · exact ho.elim
  · exact ho.elim

theorem not_trap_mem_vals {vs : List Val} : Admin.trap ∉ vals vs := by
  intro h
  obtain ⟨v, -, hv⟩ : ∃ v ∈ vs, v.toAdmin = .trap := by simpa [vals] using h
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at hv

theorem result_eq_of_vals {r : Result} {rs : List Val} (h : r.toAdmin = vals rs) :
    r = .values rs := by
  rcases r with ws | a | _
  · have h₁ : vals ws = vals rs := h
    have hw : ws = rs := by
      have h₂ : ws.map Val.toAdmin = rs.map Val.toAdmin := h₁
      have h₃ := congrArg (List.map Admin.val?) h₂
      simp only [List.map_map] at h₃
      have h₄ : ws.map some = rs.map some := by
        have e : ∀ v : Val, (Admin.val? ∘ Val.toAdmin) v = some v := fun v => by
          rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl
        simpa [Function.comp_def, e] using h₃
      exact List.map_injective_iff.mpr (Option.some_injective _) h₄
    rw [hw]
  · have h₁ : Admin.plain .throwRef ∈ vals rs := by rw [← h]; simp [Result.toAdmin]
    obtain ⟨v, -, hv⟩ : ∃ v ∈ rs, v.toAdmin = .plain .throwRef := by simpa [vals] using h₁
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at hv
  · have h₁ : Admin.trap ∈ vals rs := by rw [← h]; simp [Result.toAdmin]
    exact (not_trap_mem_vals h₁).elim

theorem result_eq_of_trap {r : Result} {vs : List Val} {rest : List Admin}
    (h : r.toAdmin = vals vs ++ .trap :: rest) : r = .trap := by
  have h₁ : Admin.trap ∈ r.toAdmin := by rw [h]; simp
  rcases r with ws | a | _
  · exact (not_trap_mem_vals h₁).elim
  · simp [Result.toAdmin] at h₁
  · rfl

theorem not_step_result {r : Result} {c c' : Config H} (h : c.code = r.toAdmin) :
    ¬ Step P host c c' := by
  rcases c with ⟨s, f, code⟩
  have hc : code = r.toAdmin := h
  subst hc
  rcases r with vs | a | _
  · exact not_step_vals
  · exact not_step_throwing
  · exact not_step_trap

/-- A run of a pinned call to a result. -/
theorem result_of_pinned {s s' : Store H} {args : List Val} {a : Nat} {o' : Outcome}
    (h : TFSpecAt P host a (pinSpec s args s' o')) (ho : o' = .trap ∨ ∃ res, o' = .normal res)
    {c' : Config H} {r : Result}
    (hs : Steps P host (invoke s a args) c') (hfin : c'.code = r.toAdmin) :
    r.toBehaviour = outBeh o' := by
  have hw : HWP P host s {} (invoke s a args).code (callPost {} [] ((pinSpec s args s' o').post s args)) :=
    TWP.hwp (by
      rw [invoke_code]
      exact h s args ⟨rfl, rfl⟩ {} [] (.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) trivial)
  have hs' : Steps P host ⟨s, {}, (invoke s a args).code⟩ c' := hs
  rcases hw.sound hs' with ⟨c'', hc⟩ | ⟨o, he, hq⟩
  · exact absurd hc (not_step_result hfin)
  · obtain ⟨-, ⟨res, rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨a', rfl, -, h₂⟩⟩ := hq
    · have hv : c'.code = vals ([] ++ res) := he
      rw [result_eq_of_vals (hfin.symm.trans hv)]
      simp [Result.toBehaviour, outBeh]
    · obtain ⟨vs, rest, hc⟩ := he
      rw [result_eq_of_trap (hfin.symm.trans hc)]
      rfl
    · rcases ho with h₃ | ⟨res, h₃⟩ <;> rw [h₃] at h₂ <;> cases h₂

/-- A pinned call has a run to its result. -/
theorem outBeh_mem_of_pinned {s s' : Store H} {args : List Val} {a : Nat} {o' : Outcome}
    (h : TFSpecAt P host a (pinSpec s args s' o')) (ho : o' = .trap ∨ ∃ res, o' = .normal res) :
    outBeh o' ∈ behaviours P host s a args := by
  have ht := h s args ⟨rfl, rfl⟩ {} []
    (.callRefType ((s.funcs[a]?.map FuncInst.type).getD default)) trivial
  obtain ⟨c', o, hs, he, hq⟩ := tsafe_exists_exit ht
  have hs' : Steps P host (invoke s a args) c' := by rw [invoke_code]; exact hs
  obtain ⟨-, ⟨res, rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩ | ⟨a', rfl, -, h₂⟩⟩ := hq
  · have hc : c'.code = vals ([] ++ res) := he
    exact returns_mem_behavioursOf hs' (by simpa using hc)
  · obtain ⟨vs, rest, hc⟩ := he
    rcases trap_shape_cases vs rest with ⟨rfl, rfl⟩ | hne
    · exact traps_mem_behavioursOf hs' (by simpa using hc)
    · have hst : Step P host c' ⟨c'.store, c'.frame, [.trap]⟩ := by
        rcases c' with ⟨s₁, f₁, code₁⟩
        have hc' : code₁ = vals vs ++ [.trap] ++ rest := by simpa using hc
        rw [hc']
        exact Step.trapInstrs hne
      exact traps_mem_behavioursOf (hs'.tail hst) rfl
  · rcases ho with h₃ | ⟨res, h₃⟩ <;> rw [h₃] at h₂ <;> cases h₂

/-- **The behaviours of a pinned call**: exactly `outBeh o'`. -/
theorem behaviours_of_pinned {s s' : Store H} {args : List Val} {a : Nat} {o' : Outcome}
    (h : TFSpecAt P host a (pinSpec s args s' o')) (ho : o' = .trap ∨ ∃ res, o' = .normal res) :
    behaviours P host s a args = {outBeh o'} := by
  apply Set.Subset.antisymm
  · intro b hb
    by_cases hd : b = .diverges
    · have hdiv : Diverges P host (invoke s a args) := diverges_mem_behavioursOf_iff.mp (hd ▸ hb)
      exact absurd hdiv (h.invoke_terminates ⟨rfl, rfl⟩)
    · obtain ⟨c', r, hs, hfin, hbr⟩ := exists_result_of_mem hb hd
      rw [hbr, result_of_pinned h ho hs hfin]
      rfl
  · exact Set.singleton_subset_iff.mpr (outBeh_mem_of_pinned h ho)

end Silmaril.Proofs.Wasm.Auto.EquivFn