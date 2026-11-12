module

public import Silmaril.Proofs.Wasm.SSA.CoreCert.Strict

@[expose] public section

/-!
# A strict frame in an evaluation context (proofs)

`Ctx`: evaluation contexts of Core 3.0 configurations (value prefixes, suffixes, labels,
frames and handlers around one hole). When the hole holds a strict frame `X` (`LFrame`), the
frame is the first non-value at every level, so:

* `ctx_step`: every step of `E[X]` is a step of `X` alone, in context (`Sim.Step.split_head`,
  `Sim.Closure.Step.label_inv`, `Sim.Closure.Step.frame_redex_aux`, `Sim.Step.handler_inv`);
* `ctx_lift`, `ctx_lift_steps`, `ctx_lift_diverges`: runs and divergence of a strict frame lift
  to any context.
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA
open Silmaril.Wasm.SSA.CoreCert

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- Evaluation contexts, outermost layer first. -/
inductive Ctx where
  | hole (vs : List Val) (rest : List Admin)
  | label (vs : List Val) (n : Nat) (cont : List Instr) (E : Ctx) (rest : List Admin)
  | frame (vs : List Val) (n : Nat) (fr : Frame) (E : Ctx) (rest : List Admin)
  | handler (vs : List Val) (n : Nat) (cs : List Catch) (E : Ctx) (rest : List Admin)

/-- Plug a sequence into a context. -/
def Ctx.plug : Ctx → List Admin → List Admin
  | .hole vs rest, l => vals vs ++ l ++ rest
  | .label vs n cont E rest, l => vals vs ++ [.label n cont (E.plug l)] ++ rest
  | .frame vs n fr E rest, l => vals vs ++ [.frame n fr (E.plug l)] ++ rest
  | .handler vs n cs E rest, l => vals vs ++ [.handler n cs (E.plug l)] ++ rest

/-- The frame of the hole, under the enclosing frame `F`. -/
def Ctx.innerF : Ctx → Frame → Frame
  | .hole _ _, F => F
  | .label _ _ _ E _, F => E.innerF F
  | .frame _ _ fr E _, _ => E.innerF fr
  | .handler _ _ _ E _, F => E.innerF F

/-- A context with more values before and code after it. -/
def Ctx.seq (pre : List Val) (post : List Admin) : Ctx → Ctx
  | .hole vs rest => .hole (pre ++ vs) (rest ++ post)
  | .label vs n cont E rest => .label (pre ++ vs) n cont E (rest ++ post)
  | .frame vs n fr E rest => .frame (pre ++ vs) n fr E (rest ++ post)
  | .handler vs n cs E rest => .handler (pre ++ vs) n cs E (rest ++ post)

theorem Ctx.plug_seq (E : Ctx) (pre : List Val) (post l : List Admin) :
    (E.seq pre post).plug l = vals pre ++ E.plug l ++ post := by
  cases E <;> simp [Ctx.seq, Ctx.plug, vals, List.append_assoc]

theorem Ctx.plug_inj (E : Ctx) {l l' : List Admin} (h : E.plug l = E.plug l') : l = l' := by
  induction E with
  | hole vs rest => simpa [Ctx.plug] using h
  | label vs n cont E rest ih => exact ih (by simpa [Ctx.plug] using h)
  | frame vs n fr E rest ih => exact ih (by simpa [Ctx.plug] using h)
  | handler vs n cs E rest ih => exact ih (by simpa [Ctx.plug] using h)

theorem Ctx.innerF_seq (E : Ctx) (pre : List Val) (post : List Admin) (F : Frame) :
    (E.seq pre post).innerF F = E.innerF F := by
  cases E <;> rfl

/-! ## The head of a plugged strict frame -/

theorem lFrame_val? {X : Admin} (h : LFrame X) : X.val? = none := by
  obtain ⟨n, fr, b, rfl, -, -⟩ := h
  rfl

theorem Ctx.plug_head (E : Ctx) {X : Admin} (hX : LFrame X) :
    ∃ ws a r, E.plug [X] = vals ws ++ a :: r ∧ a.val? = none ∧ a.IsCtx := by
  obtain ⟨n, fr, b, rfl, -, -⟩ := hX
  cases E with
  | hole vs rest => exact ⟨vs, .frame n fr b, rest, by simp [Ctx.plug], rfl, trivial⟩
  | label vs n' cont E rest =>
    exact ⟨vs, .label n' cont (E.plug [.frame n fr b]), rest, by simp [Ctx.plug], rfl, trivial⟩
  | frame vs n' fr' E rest =>
    exact ⟨vs, .frame n' fr' (E.plug [.frame n fr b]), rest, by simp [Ctx.plug], rfl, trivial⟩
  | handler vs n' cs E rest =>
    exact ⟨vs, .handler n' cs (E.plug [.frame n fr b]), rest, by simp [Ctx.plug], rfl, trivial⟩

theorem Ctx.plug_ne {E : Ctx} {X : Admin} (hX : LFrame X) {ws : List Val} {k : Admin}
    {r : List Admin} (hk : k.val? = none) (hk' : ¬ k.IsCtx) : E.plug [X] ≠ vals ws ++ k :: r := by
  obtain ⟨ws', a, r', he, ha, hac⟩ := E.plug_head hX
  intro h
  rw [he] at h
  obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj ha hk h
  exact hk' hac

theorem Ctx.plug_ne_at {E : Ctx} {X : Admin} (hX : LFrame X) {ws : List Val} {k : Admin}
    {r : List Admin} (hk : k.val? = none) (hk' : ¬ k.IsCtx)
    (h : E.plug [X] = vals ws ++ [k] ++ r) : False :=
  E.plug_ne hX hk hk' (by simpa using h)

theorem Ctx.plug_ne_at2 {E : Ctx} {X : Admin} (hX : LFrame X) {ws₁ ws₂ : List Val} {k : Admin}
    {r : List Admin} (hk : k.val? = none) (hk' : ¬ k.IsCtx)
    (h : E.plug [X] = vals ws₁ ++ vals ws₂ ++ [k] ++ r) : False :=
  E.plug_ne (ws := ws₁ ++ ws₂) hX hk hk' (by simpa [vals] using h)

theorem Ctx.plug_ne_ref {E : Ctx} {X : Admin} (hX : LFrame X) {ws : List Val} {ρ : Ref}
    {k : Admin} {r : List Admin} (hk : k.val? = none) (hk' : ¬ k.IsCtx)
    (h : E.plug [X] = vals ws ++ [.ref ρ, k] ++ r) : False :=
  E.plug_ne (ws := ws ++ [.ref ρ]) hX hk hk' (by simpa [vals, Val.toAdmin] using h)

theorem Ctx.plug_ne_ref2 {E : Ctx} {X : Admin} (hX : LFrame X) {ws₁ ws₂ : List Val} {ρ : Ref}
    {k : Admin} {r : List Admin} (hk : k.val? = none) (hk' : ¬ k.IsCtx)
    (h : E.plug [X] = vals ws₁ ++ vals ws₂ ++ [.ref ρ, k] ++ r) : False :=
  E.plug_ne (ws := ws₁ ++ ws₂ ++ [.ref ρ]) hX hk hk' (by simpa [vals, Val.toAdmin] using h)

theorem Ctx.plug_ne_vals {E : Ctx} {X : Admin} (hX : LFrame X) (ws : List Val) :
    E.plug [X] ≠ vals ws := by
  obtain ⟨ws', a, r', he, ha, -⟩ := E.plug_head hX
  intro h
  rw [he] at h
  have hm : a ∈ vals ws := by rw [← h]; simp
  simp only [vals, List.mem_map] at hm
  obtain ⟨v, -, rfl⟩ := hm
  simp at ha

theorem returnCallRef_shape {c : Admin} (hc : c.IsReturnCallRef) : c.val? = none ∧ ¬ c.IsCtx := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · exact ⟨rfl, id⟩
  · exact ⟨rfl, id⟩
  · exact absurd hc id

theorem Ctx.plug_ne_result {E : Ctx} {X : Admin} (hX : LFrame X) (r : Result) :
    E.plug [X] ≠ r.toAdmin := by
  cases r with
  | values vs => exact E.plug_ne_vals hX vs
  | throw a =>
    have : (Result.throw a).toAdmin = vals [.ref (.exn a)] ++ Admin.plain .throwRef :: [] := rfl
    rw [this]
    exact E.plug_ne hX rfl id
  | trap => exact E.plug_ne (ws := []) hX rfl id

/-! ## Inversion -/

/-- The steps of a `FRAME` redex are steps of the frame instruction, in the same frame. -/
theorem frameRedex_step {s s' : Store H} {f f' fi : Frame} {n : Nat} {b is : List Admin}
    (h : Sim.Closure.FrameRedex P host s f n fi b s' f' is) :
    f' = f ∧ Step P host ⟨s, f, [.frame n fi b]⟩ ⟨s', f, is⟩ := by
  cases h with
  | ctxt hs => exact ⟨rfl, .ctxtFrame hs⟩
  | values hn => exact ⟨rfl, .frameVals hn⟩
  | ret hn => exact ⟨rfl, .returnFrame hn⟩
  | callNull hc => exact ⟨rfl, .returnCallRefFrameNull hc⟩
  | callAddr hc hf he hn => exact ⟨rfl, .returnCallRefFrameAddr hc hf he hn⟩
  | throw => exact ⟨rfl, .throwRefFrame⟩
  | trap => exact ⟨rfl, .trapFrame⟩

/-- The conclusion of `ctx_step` at a context. -/
def CtxStepAt (P : Numerics.Profile) (host : HostSemantics H) (E : Ctx) (X : Admin) : Prop :=
  ∀ {s : Store H} {F : Frame} {c' : Config H}, Step P host ⟨s, F, E.plug [X]⟩ c' →
    ∃ l, Step P host ⟨s, E.innerF F, [X]⟩ ⟨c'.store, E.innerF F, l⟩ ∧ c'.frame = F ∧
      c'.code = E.plug l

/-- A `LABEL` around a plugged strict frame only steps inside. -/
theorem labelRed_ctxt {E : Ctx} {X : Admin} (hX : LFrame X) {s s' : Store H} {F F' : Frame}
    {n : Nat} {cont : List Instr} {is : List Admin}
    (h : Sim.Closure.LabelRed P host s F n cont (E.plug [X]) s' F' is) :
    ∃ b', Step P host ⟨s, F, E.plug [X]⟩ ⟨s', F', b'⟩ ∧ is = [.label n cont b'] := by
  generalize hB : E.plug [X] = B at h
  cases h with
  | ctxt hb => exact ⟨_, hB ▸ hb, rfl⟩
  | values vs₀ => exact (E.plug_ne_vals hX vs₀ hB).elim
  | brZero hl hn => exact (E.plug_ne_at2 hX rfl (by simp [Admin.IsCtx]) hB).elim
  | brSucc hl => exact (E.plug_ne_at hX rfl (by simp [Admin.IsCtx]) hB).elim
  | returnCallRef hc =>
    exact (E.plug_ne_at hX (returnCallRef_shape hc).1 (returnCallRef_shape hc).2 hB).elim
  | return_ => exact (E.plug_ne_at hX rfl (by simp [Admin.IsCtx]) hB).elim
  | throwRef a => exact (E.plug_ne_result hX (.throw a) hB).elim
  | trap => exact (E.plug_ne_result hX .trap hB).elim

/-- A `FRAME` around a plugged strict frame only steps inside. -/
theorem frameRedex_ctxt {E : Ctx} {X : Admin} (hX : LFrame X) {s s' : Store H} {F F' fr : Frame}
    {n : Nat} {is : List Admin}
    (h : Sim.Closure.FrameRedex P host s F n fr (E.plug [X]) s' F' is) :
    ∃ fr' b', Step P host ⟨s, fr, E.plug [X]⟩ ⟨s', fr', b'⟩ ∧ F' = F ∧ is = [.frame n fr' b'] := by
  generalize hB : E.plug [X] = B at h
  cases h with
  | ctxt hb => exact ⟨_, _, hB ▸ hb, rfl, rfl⟩
  | values hn => exact (E.plug_ne_vals hX _ hB).elim
  | ret hn => exact (E.plug_ne_at2 hX rfl (by simp [Admin.IsCtx]) hB).elim
  | callNull hc =>
    exact (E.plug_ne_ref hX (returnCallRef_shape hc).1 (returnCallRef_shape hc).2 hB).elim
  | callAddr hc hf he hn =>
    exact (E.plug_ne_ref2 hX (returnCallRef_shape hc).1 (returnCallRef_shape hc).2 hB).elim
  | throw => exact (E.plug_ne_result hX (.throw _) hB).elim
  | trap => exact (E.plug_ne_result hX .trap hB).elim

/-- A `HANDLER` around a plugged strict frame only steps inside. -/
theorem handlerInv_ctxt {E : Ctx} {X : Admin} (hX : LFrame X) {s s' : Store H} {F F' : Frame}
    {n : Nat} {cs : List Catch} {is : List Admin}
    (h : Sim.HandlerInv P host s F n cs (E.plug [X]) s' F' is) :
    ∃ b', Step P host ⟨s, F, E.plug [X]⟩ ⟨s', F', b'⟩ ∧ is = [.handler n cs b'] := by
  rcases h with hb | ⟨-, -, vs₀, hB, -⟩ | ⟨-, -, vs₀, k, r, hk, hB, -⟩ | ⟨hB | ⟨a, hB⟩, -⟩
  · exact hb
  · exact (E.plug_ne_vals hX vs₀ hB).elim
  · rcases hk with ⟨l, rfl⟩ | rfl | ⟨c, hc, rfl⟩
    · exact (E.plug_ne_at hX rfl (by simp [Admin.IsCtx]) hB).elim
    · exact (E.plug_ne_at hX rfl (by simp [Admin.IsCtx]) hB).elim
    · exact (E.plug_ne_at hX (returnCallRef_shape hc).1 (returnCallRef_shape hc).2 hB).elim
  · exact (E.plug_ne_result hX .trap hB).elim
  · exact (E.plug_ne_result hX (.throw a) hB).elim

theorem ctx_step_hole {X : Admin} (hX : LFrame X) (vs : List Val) (rest : List Admin) :
    CtxStepAt P host (.hole vs rest) X := by
  intro s F c' h
  obtain ⟨s', F', es'⟩ := c'
  have h' : Step P host ⟨s, F, vals vs ++ X :: rest⟩ ⟨s', F', es'⟩ := by
    simpa [Ctx.plug] using h
  obtain ⟨n, fr, b, rfl, -, -⟩ := hX
  rcases Sim.Step.split_head rfl h' with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  · obtain ⟨is₀, rfl, hr⟩ := Sim.Closure.Step.frame_redex_aux hs us n fr b rfl
    obtain ⟨rfl, hst⟩ := frameRedex_step hr
    exact ⟨is₀, hst, rfl, by simp [Ctx.plug, vals]⟩
  · cases hc
  · cases hc

theorem ctx_step_label {E : Ctx} {X : Admin} (hX : LFrame X) (ih : CtxStepAt P host E X)
    (vs : List Val) (n : Nat) (cont : List Instr) (rest : List Admin) :
    CtxStepAt P host (.label vs n cont E rest) X := by
  intro s F c' h
  obtain ⟨s', F', es'⟩ := c'
  have h' : Step P host ⟨s, F, vals vs ++ Admin.label n cont (E.plug [X]) :: rest⟩
      ⟨s', F', es'⟩ := by simpa [Ctx.plug] using h
  rcases Sim.Step.split_head rfl h' with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  · obtain ⟨is'', hr, rfl⟩ := Sim.Closure.Step.label_inv hs
    obtain ⟨b', hb, rfl⟩ := labelRed_ctxt hX hr
    obtain ⟨l, hst, rfl, rfl⟩ := ih hb
    exact ⟨l, hst, rfl, by simp [Ctx.plug, vals]⟩
  · cases hc
  · cases hc

theorem ctx_step_frame {E : Ctx} {X : Admin} (hX : LFrame X) (ih : CtxStepAt P host E X)
    (vs : List Val) (n : Nat) (fr : Frame) (rest : List Admin) :
    CtxStepAt P host (.frame vs n fr E rest) X := by
  intro s F c' h
  obtain ⟨s', F', es'⟩ := c'
  have h' : Step P host ⟨s, F, vals vs ++ Admin.frame n fr (E.plug [X]) :: rest⟩
      ⟨s', F', es'⟩ := by simpa [Ctx.plug] using h
  rcases Sim.Step.split_head rfl h' with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  · obtain ⟨is₀, rfl, hr⟩ := Sim.Closure.Step.frame_redex_aux hs us n fr _ rfl
    obtain ⟨fr', b', hb, rfl, rfl⟩ := frameRedex_ctxt hX hr
    obtain ⟨l, hst, rfl, rfl⟩ := ih hb
    exact ⟨l, hst, rfl, by simp [Ctx.plug, vals]⟩
  · cases hc
  · cases hc

theorem ctx_step_handler {E : Ctx} {X : Admin} (hX : LFrame X) (ih : CtxStepAt P host E X)
    (vs : List Val) (n : Nat) (cs : List Catch) (rest : List Admin) :
    CtxStepAt P host (.handler vs n cs E rest) X := by
  intro s F c' h
  obtain ⟨s', F', es'⟩ := c'
  have h' : Step P host ⟨s, F, vals vs ++ Admin.handler n cs (E.plug [X]) :: rest⟩
      ⟨s', F', es'⟩ := by simpa [Ctx.plug] using h
  rcases Sim.Step.split_head rfl h' with ⟨ws, us, is', rfl, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
  · obtain ⟨is'', hr, rfl⟩ := Sim.Step.handler_inv hs
    obtain ⟨b', hb, rfl⟩ := handlerInv_ctxt hX hr
    obtain ⟨l, hst, rfl, rfl⟩ := ih hb
    exact ⟨l, hst, rfl, by simp [Ctx.plug, vals]⟩
  · cases hc
  · cases hc

theorem ctx_step_at (E : Ctx) {X : Admin} (hX : LFrame X) : CtxStepAt P host E X := by
  induction E with
  | hole vs rest => exact ctx_step_hole hX vs rest
  | label vs n cont E rest ih => exact ctx_step_label hX ih vs n cont rest
  | frame vs n fr E rest ih => exact ctx_step_frame hX ih vs n fr rest
  | handler vs n cs E rest ih => exact ctx_step_handler hX ih vs n cs rest

/-- **A step of a context holding a strict frame is a step of the frame.** -/
theorem ctx_step {E : Ctx} {X : Admin} (hX : LFrame X) {s : Store H} {F : Frame}
    {c' : Config H} (h : Step P host ⟨s, F, E.plug [X]⟩ c') :
    ∃ l, Step P host ⟨s, E.innerF F, [X]⟩ ⟨c'.store, E.innerF F, l⟩ ∧ c'.frame = F ∧
      c'.code = E.plug l :=
  ctx_step_at E hX h

/-! ## Lifting -/

/-- A step at the hole's frame is a step of the plugged context. -/
theorem ctx_lift (E : Ctx) {s s' : Store H} {F : Frame} {l l' : List Admin}
    (h : Step P host ⟨s, E.innerF F, l⟩ ⟨s', E.innerF F, l'⟩) :
    Step P host ⟨s, F, E.plug l⟩ ⟨s', F, E.plug l'⟩ := by
  induction E generalizing F with
  | hole vs rest => exact Sim.Step.append_right (Sim.Step.vals_left h vs) rest
  | label vs n cont E rest ih =>
    exact Sim.Step.append_right (Sim.Step.vals_left (Step.ctxtLabel (ih h)) vs) _
  | frame vs n fr E rest ih =>
    exact Sim.Step.append_right (Sim.Step.vals_left (Step.ctxtFrame (ih h)) vs) _
  | handler vs n cs E rest ih =>
    exact Sim.Step.append_right (Sim.Step.vals_left (Step.ctxtHandler (ih h)) vs) _

/-- **Runs of a strict frame lift to any context.** -/
theorem ctx_lift_steps (E : Ctx) {X : Admin} (hX : LFrame X) {t : Store H} {F : Frame}
    {c : Config H} (h : Steps P host ⟨t, E.innerF F, [X]⟩ c) :
    Steps P host ⟨t, F, E.plug [X]⟩ ⟨t, F, E.plug c.code⟩ := by
  induction h with
  | refl => exact .refl
  | @tail c₁ c₂ h₁ hs ih =>
    have r₁ := frame_steps hX h₁
    have r₂ := frameRun_step r₁ hs
    obtain ⟨s₁, f₁, l₁⟩ := c₁
    obtain ⟨s₂, f₂, l₂⟩ := c₂
    obtain ⟨rfl, rfl, -, -⟩ := r₁
    obtain ⟨rfl, rfl, -, -⟩ := r₂
    exact ih.tail (ctx_lift E hs)

/-- **Divergence of a strict frame lifts to any context.** -/
theorem ctx_lift_diverges (E : Ctx) {X : Admin} (hX : LFrame X) {t : Store H} {F : Frame}
    (h : Diverges P host ⟨t, E.innerF F, [X]⟩) : Diverges P host ⟨t, F, E.plug [X]⟩ := by
  refine Silmaril.InfiniteTrace.coinduct (fun d => ∃ c : Config H, d = ⟨t, F, E.plug c.code⟩ ∧
      FrameRun P t (E.innerF F) X c ∧ Diverges P host c) ?_
    ⟨⟨t, E.innerF F, [X]⟩, rfl, frame_steps (host := host) hX .refl, h⟩
  rintro d ⟨c, rfl, hr, hd⟩
  obtain ⟨c', hs, hd'⟩ := hd.unfold
  have hr' := frameRun_step hr hs
  refine ⟨⟨t, F, E.plug c'.code⟩, ?_, c', rfl, hr', hd'⟩
  obtain ⟨s₁, f₁, l₁⟩ := c
  obtain ⟨s₂, f₂, l₂⟩ := c'
  obtain ⟨rfl, rfl, -, -⟩ := hr
  obtain ⟨rfl, rfl, -, -⟩ := hr'
  exact ctx_lift E hs

end Silmaril.Proofs.Wasm.SSA.CoreCert
