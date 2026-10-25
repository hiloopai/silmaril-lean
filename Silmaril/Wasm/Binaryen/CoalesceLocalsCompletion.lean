module

public import Silmaril.Wasm.Binaryen.CoalesceLocalsLiteSim
public import Silmaril.Wasm.Binaryen.EffectRank
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadCtl

@[expose] public section

/-! # Completing a transient dead-local write

The original side of CoalesceLocals temporarily stores the dead value. Its
immediate constant overwrite is a real, uniquely forced reduction. `Completion`
retains that reduction through arbitrary execution contexts, with the store
unchanged and a strictly decreasing body-aware rank. Nothing restricts the
numerical profile or the code following the overwrite.
-/

namespace Silmaril.Wasm.Binaryen.CoalesceLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- One pending local write, possibly under runtime execution contexts. -/
inductive Completion : Config H → Config H → Prop where
  | set (s : Store H) (f : Frame) (vs : List Val) (w : Val) (x : LocalIdx)
      (rest : List Admin) (hx : x.toNat < f.locals.length) :
      Completion ⟨s, f, vals vs ++ [w.toAdmin, .plain (.localSet x)] ++ rest⟩
        ⟨s, f.setLocal x w, vals vs ++ rest⟩
  | label {s : Store H} {f f' : Frame} {b b' : List Admin}
      (h : Completion ⟨s, f, b⟩ ⟨s, f', b'⟩)
      (vs : List Val) (n : Nat) (cont : List Instr) (rest : List Admin) :
      Completion ⟨s, f, vals vs ++ [.label n cont b] ++ rest⟩
        ⟨s, f', vals vs ++ [.label n cont b'] ++ rest⟩
  | handler {s : Store H} {f f' : Frame} {b b' : List Admin}
      (h : Completion ⟨s, f, b⟩ ⟨s, f', b'⟩)
      (vs : List Val) (n : Nat) (cs : List Catch) (rest : List Admin) :
      Completion ⟨s, f, vals vs ++ [.handler n cs b] ++ rest⟩
        ⟨s, f', vals vs ++ [.handler n cs b'] ++ rest⟩
  | frame {s : Store H} {fi fi' : Frame} {b b' : List Admin}
      (h : Completion ⟨s, fi, b⟩ ⟨s, fi', b'⟩)
      (f : Frame) (vs : List Val) (n : Nat) (rest : List Admin) :
      Completion ⟨s, f, vals vs ++ [.frame n fi b] ++ rest⟩
        ⟨s, f, vals vs ++ [.frame n fi' b'] ++ rest⟩

namespace Completion

theorem step {c d : Config H} (h : Completion c d) : Step P host c d := by
  induction h with
  | set s f vs w x rest hx =>
    simpa using Step.append_right (Step.vals_left (.variable (.localSet hx)) vs) rest
  | label _ vs n cont rest ih =>
    exact Step.append_right (Step.vals_left (.ctxtLabel ih) vs) rest
  | handler _ vs n cs rest ih =>
    exact Step.append_right (Step.vals_left (.ctxtHandler ih) vs) rest
  | frame _ f vs n rest ih =>
    exact Step.append_right (Step.vals_left (.ctxtFrame ih) vs) rest

theorem store {c d : Config H} (h : Completion c d) : d.store = c.store := by
  cases h <;> rfl

theorem rank {c d : Config H} (h : Completion c d) : aszs d.code < aszs c.code := by
  induction h with
  | set => simp; omega
  | label _ _ _ _ _ ih => simp only [aszs_append, aszs_cons, asz_label, aszs_nil] at *; omega
  | handler _ _ _ _ _ ih => simp only [aszs_append, aszs_cons, asz, aszs_nil] at *; omega
  | frame _ _ _ _ _ ih => simp only [aszs_append, aszs_cons, asz, aszs_nil] at *; omega

/-- Completion remains a single pending write after adding any value prefix and suffix. -/
theorem context {c d : Config H} (h : Completion c d) (vs : List Val) (rest : List Admin) :
    Completion ⟨c.store, c.frame, vals vs ++ c.code ++ rest⟩
      ⟨d.store, d.frame, vals vs ++ d.code ++ rest⟩ := by
  cases h with
  | set s f ws w x tail hx =>
    simpa using Completion.set s f (vs ++ ws) w x (tail ++ rest) hx
  | label hb ws n cont tail =>
    simpa using Completion.label hb (vs ++ ws) n cont (tail ++ rest)
  | handler hb ws n cs tail =>
    simpa using Completion.handler hb (vs ++ ws) n cs (tail ++ rest)
  | frame hb f ws n tail =>
    simpa using Completion.frame hb f (vs ++ ws) n (tail ++ rest)

end Completion

/-- The next store is uniquely forced even when following code is nondeterministic. -/
theorem set_step_unique {s : Store H} {f : Frame} {vs : List Val} {w : Val}
    {x : LocalIdx} {rest : List Admin} {d : Config H}
    (h : Step P host ⟨s, f, vals vs ++ [w.toAdmin, .plain (.localSet x)] ++ rest⟩ d) :
    d = ⟨s, f.setLocal x w, vals vs ++ rest⟩ := by
  obtain ⟨s', f', es'⟩ := d
  have he : vals vs ++ [w.toAdmin, Admin.plain (.localSet x)] ++ rest =
      vals (vs ++ [w]) ++ Admin.plain (.localSet x) :: rest := by simp [vals]
  rw [he] at h
  rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨us₀, w', rfl, h1, h2, h3, -⟩ := step_set_inv hs us x rfl
    dsimp only at h1 h2 h3
    subst h1 h2 h3
    obtain ⟨rfl, rfl⟩ : vs = ws ++ us₀ ∧ w = w' := by
      rw [← List.append_assoc] at hV
      exact List.append_inj' hV rfl |>.imp id (fun h => by simpa using h)
    simp
  · cases h
  · cases h

/-- A body which can step cannot simultaneously take an administrative label exit. -/
theorem labelRed_ctxt_of_step {s s' : Store H} {f f' : Frame} {n : Nat}
    {cont : List Instr} {b es' : List Admin} {c : Config H}
    (hs : Step P closedHost ⟨s, f, b⟩ c)
    (hr : Closure.LabelRed P closedHost s f n cont b s' f' es') :
    ∃ out, Step P closedHost ⟨s, f, b⟩ ⟨s', f', out⟩ ∧ es' = [.label n cont out] := by
  cases hr with
  | ctxt h => exact ⟨_, h, rfl⟩
  | values => exact (not_step_vals hs).elim
  | brZero | brSucc | return_ => ctl_step
  | returnCallRef hc =>
    rename_i vs a rest
    exact (Det.Step.fnv_good hs _ rest
      (by simp [fnv_cons_of_none (IsReturnCallRef.val_none hc)])
      (IsReturnCallRef.blocked hc)).elim
  | throwRef => exact (not_step_throwing hs).elim
  | trap => exact (not_step_trap hs).elim

/-- A stepping handler body excludes every administrative exit rule. -/
theorem handlerInv_ctxt_of_step {s s' : Store H} {f f' : Frame} {n : Nat}
    {cs : List Catch} {b es' : List Admin} {c : Config H}
    (hs : Step P closedHost ⟨s, f, b⟩ c)
    (hr : HandlerInv P closedHost s f n cs b s' f' es') :
    ∃ out, Step P closedHost ⟨s, f, b⟩ ⟨s', f', out⟩ ∧ es' = [.handler n cs out] := by
  rcases hr with ⟨out, h, rfl⟩ | ⟨rfl, rfl, vs, rfl, -⟩ |
      ⟨rfl, rfl, vs, k, rest, hk, rfl, -⟩ | ⟨hb, -⟩
  · exact ⟨out, h, rfl⟩
  · exact (not_step_vals hs).elim
  · rcases hk with ⟨l, rfl⟩ | rfl | ⟨a, ha, rfl⟩
    · exact (Det.Step.fnv_good hs _ rest (by simp) (.inl ⟨l, rfl⟩)).elim
    · exact (Det.Step.fnv_good hs _ rest (by simp) (.inr (.inl rfl))).elim
    · exact (Det.Step.fnv_good hs _ rest
        (by simp [fnv_cons_of_none (IsReturnCallRef.val_none ha)])
        (IsReturnCallRef.blocked ha)).elim
  · rcases hb with rfl | ⟨a, rfl⟩
    · exact (not_step_trap hs).elim
    · exact (not_step_throwing hs).elim

/-- A stepping frame body excludes every administrative exit rule. -/
theorem frameRedex_ctxt_of_step {s s' : Store H} {f f' fi : Frame} {n : Nat}
    {b es' : List Admin} {c : Config H}
    (hs : Step P closedHost ⟨s, fi, b⟩ c)
    (hr : Closure.FrameRedex P closedHost s f n fi b s' f' es') :
    ∃ fi' out, Step P closedHost ⟨s, fi, b⟩ ⟨s', fi', out⟩ ∧
      f' = f ∧ es' = [.frame n fi' out] := by
  cases hr with
  | ctxt h => exact ⟨_, _, h, rfl, rfl⟩
  | values => exact (not_step_vals hs).elim
  | ret => ctl_step
  | callNull hc =>
    rename_i vs a rest
    exact (Det.Step.fnv_good hs _ rest
      (by simp [fnv_cons_of_none (IsReturnCallRef.val_none hc)])
      (IsReturnCallRef.blocked hc)).elim
  | callAddr hc =>
    rename_i vs' vs a e rest fn ps rs hf he hn
    exact (Det.Step.fnv_good hs _ rest
      (by simp [fnv_cons_of_none (IsReturnCallRef.val_none hc)])
      (IsReturnCallRef.blocked hc)).elim
  | throw => exact (not_step_throwing hs).elim
  | trap => exact (not_step_trap hs).elim

namespace Completion

/-- The transient overwrite is forced under every nested runtime context. -/
theorem unique {c d : Config H} (h : Completion c d) :
    ∀ e, Step P closedHost c e → e = d := by
  induction h with
  | set => exact fun _ hs => set_step_unique hs
  | @label s f f' b b' hb vs n cont rest ih =>
    rintro ⟨s₁, g, es⟩ hs
    have he : vals vs ++ [Admin.label n cont b] ++ rest =
        vals vs ++ Admin.label n cont b :: rest := by simp
    rw [he] at hs
    rcases Step.split_head rfl hs with ⟨ws, us, is', hV, hs₁, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨out, hr, rfl⟩ := Closure.Step.label_inv hs₁
      obtain ⟨z, hz, rfl⟩ := labelRed_ctxt_of_step hb.step hr
      obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj (ih _ hz)
      simp [hV]
    · cases h
    · cases h
  | @handler s f f' b b' hb vs n cs rest ih =>
    rintro ⟨s₁, g, es⟩ hs
    have he : vals vs ++ [Admin.handler n cs b] ++ rest =
        vals vs ++ Admin.handler n cs b :: rest := by simp
    rw [he] at hs
    rcases Step.split_head rfl hs with ⟨ws, us, is', hV, hs₁, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨out, hr, rfl⟩ := Step.handler_inv hs₁
      obtain ⟨z, hz, rfl⟩ := handlerInv_ctxt_of_step hb.step hr
      obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj (ih _ hz)
      simp [hV]
    · cases h
    · cases h
  | @frame s fi fi' b b' hb f vs n rest ih =>
    rintro ⟨s₁, g, es⟩ hs
    have he : vals vs ++ [Admin.frame n fi b] ++ rest =
        vals vs ++ Admin.frame n fi b :: rest := by simp
    rw [he] at hs
    rcases Step.split_head rfl hs with ⟨ws, us, is', hV, hs₁, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨out, rfl, hr⟩ := Closure.Step.frame_redex_aux hs₁ us n fi b rfl
      obtain ⟨fj, z, hz, rfl, rfl⟩ := frameRedex_ctxt_of_step hb.step hr
      obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj (ih _ hz)
      simp [hV]
    · cases h
    · cases h

end Completion

end Silmaril.Wasm.Binaryen.CoalesceLocalsLite
