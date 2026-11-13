module

public import Silmaril.Proofs.Wasm.Game.Machine.SoftJoin

/-!
# Where profile choices happen, and trapped configurations

* `Soft.at`: a `Soft` step happens at the first non-value of the code (`Det.fnv`): a bubble of
  `TRAP` (with its result) or of `THROW_REF` behind an exception reference, a choice
  instruction, or a `Soft` step inside the label, handler or frame there;
* `Doomed`: a `TRAP` under a callout context (`Ctx.fill`). Every host-free step from a doomed
  configuration, under any profile, keeps the store and the frame and stays doomed
  (`step_doomed`), so every run to a result ends in a trap in the same store
  (`reach_doomed`). This replaces the uniqueness of normal forms that the deterministic proof
  used for trapping providers.

New (no source file); `doomed_step` follows `Silmaril.Proofs.Wasm.Game.Linking.Split.fill_trap_reach`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Choice

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ### The first non-value -/

theorem fnv_append_of_cons {l : List Admin} {W : List Val} {e : Admin} {R : List Admin}
    (h : fnv l = (W, e :: R)) (m : List Admin) : fnv (l ++ m) = (W, e :: (R ++ m)) := by
  induction l generalizing W with
  | nil => simp at h
  | cons a l ih =>
    rcases ha : a.val? with _ | v
    · rw [fnv_cons_of_none ha] at h
      simp only [Prod.mk.injEq, List.nil_eq, List.cons.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.cons_append, fnv_cons_of_none ha]
    · have hav : a = v.toAdmin := Admin.eq_of_val? ha
      subst hav
      rw [fnv_toAdmin_cons] at h
      rw [List.cons_append, fnv_toAdmin_cons]
      simp only [Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, h2⟩ := h
      have := ih (W := (fnv l).1) (by rw [← h2])
      simp [this]

/-- The left-hand side of a choice family rule. -/
theorem famRel_shape' {P : Profile} {k : Fam} {s : Store H} {f : Frame} {code : List Admin}
    {c : Config H} (hk : ChoiceFam k) (h : FamRel P k s f code c) : FamShape k code := by
  cases k with
  | numeric => obtain ⟨_, hn, -⟩ := h; exact NumericStep.shape hn
  | vector => obtain ⟨_, hn, -⟩ := h; exact VectorStep.shape hn
  | table => exact TableStep.shape h
  | memory => exact MemoryStep.shape h
  | _ => exact hk.elim

/-- The redex of a `Soft` step at the first non-value `e` of the code, with `W` before it and
`rest` after it. -/
def SoftAt (P : Profile) (s : Store H) (f : Frame) (W : List Val) (e : Admin) (rest : List Admin)
    (d : Config H) : Prop :=
  (e = .trap ∧ ∃ p q u r, (q ≠ [] ∨ u ≠ []) ∧ W = p ++ q ∧ rest = u ++ r ∧
    d = ⟨s, f, vals p ++ [.trap] ++ r⟩) ∨
  (e = .plain .throwRef ∧ ∃ W' a, W = W' ++ [.ref (.exn a)]) ∨ ChoiceFam (famOf e) ∨
  (∃ n cont is s' f' is', e = .label n cont is ∧ Soft P ⟨s, f, is⟩ ⟨s', f', is'⟩ ∧
    d = ⟨s', f', vals W ++ [.label n cont is'] ++ rest⟩) ∨
  (∃ n cs is s' f' is', e = .handler n cs is ∧ Soft P ⟨s, f, is⟩ ⟨s', f', is'⟩ ∧
    d = ⟨s', f', vals W ++ [.handler n cs is'] ++ rest⟩) ∨
  (∃ n fi is s' fi' is', e = .frame n fi is ∧ Soft P ⟨s, fi, is⟩ ⟨s', fi', is'⟩ ∧
    d = ⟨s', f, vals W ++ [.frame n fi' is'] ++ rest⟩)

/-- `SoftAt` under a value prefix and a suffix. -/
theorem SoftAt.instrs {P : Profile} {s : Store H} {f : Frame} {W : List Val} {e : Admin}
    {rest : List Admin} {s' : Store H} {f' : Frame} {is' : List Admin} (vs : List Val)
    (rest₀ : List Admin) (h : SoftAt P s f W e rest ⟨s', f', is'⟩) :
    SoftAt P s f (vs ++ W) e (rest ++ rest₀) ⟨s', f', vals vs ++ is' ++ rest₀⟩ := by
  rcases h with ⟨he, p, q, u, r, hqu, hW, hr, hd⟩ | ⟨he, W', a, hW⟩ | hk |
    ⟨n, cont, is, s₁, f₁, is₁, he, hs, hd⟩ | ⟨n, cs, is, s₁, f₁, is₁, he, hs, hd⟩ |
    ⟨n, fi, is, s₁, fi₁, is₁, he, hs, hd⟩
  · obtain ⟨hs', hf', hc'⟩ := Config.mk.inj hd
    refine .inl ⟨he, vs ++ p, q, u, r ++ rest₀, hqu, by rw [hW, List.append_assoc],
      by rw [hr, List.append_assoc], ?_⟩
    rw [hs', hf', hc']
    simp [vals_append]
  · exact .inr (.inl ⟨he, vs ++ W', a, by rw [hW, List.append_assoc]⟩)
  · exact .inr (.inr (.inl hk))
  · obtain ⟨hs', hf', hc'⟩ := Config.mk.inj hd
    refine .inr (.inr (.inr (.inl ⟨n, cont, is, s₁, f₁, is₁, he, hs, ?_⟩)))
    rw [hs', hf', hc']
    simp [vals_append]
  · obtain ⟨hs', hf', hc'⟩ := Config.mk.inj hd
    refine .inr (.inr (.inr (.inr (.inl ⟨n, cs, is, s₁, f₁, is₁, he, hs, ?_⟩))))
    rw [hs', hf', hc']
    simp [vals_append]
  · obtain ⟨hs', hf', hc'⟩ := Config.mk.inj hd
    refine .inr (.inr (.inr (.inr (.inr ⟨n, fi, is, s₁, fi₁, is₁, he, hs, ?_⟩))))
    rw [hs', hf', hc']
    simp [vals_append]

theorem soft_at_choice {P : Profile} {k : Fam} {s : Store H} {f : Frame} {code : List Admin}
    {c : Config H} (hk : ChoiceFam k) (h : FamRel P k s f code c) :
    ∃ W e rest, fnv code = (W, e :: rest) ∧ SoftAt P s f W e rest c := by
  obtain ⟨args, e, rfl, hv, he⟩ := famRel_shape' hk h
  refine ⟨args, e, [], by simp [fnv_cons_of_none hv], .inr (.inr (.inl ?_))⟩
  rw [he]
  exact hk

theorem soft_at_bubble {P : Profile} {s : Store H} {f : Frame} {code : List Admin}
    {c : Config H} (h : Bubble s f code c) :
    ∃ W e rest, fnv code = (W, e :: rest) ∧ SoftAt P s f W e rest c := by
  obtain ⟨p, q, u, r, hqu, ⟨hf, -, hc⟩ | ⟨a, hf, -, -⟩⟩ := fnv_bubble h
  · exact ⟨p ++ q, .trap, u ++ r, hf, .inl ⟨rfl, p, q, u, r, hqu, rfl, rfl, hc⟩⟩
  · exact ⟨_, _, _, hf, .inr (.inl ⟨rfl, p ++ q, a, rfl⟩)⟩

/-- **A `Soft` step happens at the first non-value.** -/
theorem Soft.at {P : Profile} {c d : Config H} (h : Soft P c d) :
    ∃ W e rest, fnv c.code = (W, e :: rest) ∧ SoftAt P c.store c.frame W e rest d := by
  induction h with
  | choice hk h => exact soft_at_choice hk h
  | bubble h => exact soft_at_bubble h
  | @instrs s s' f f' vs is is' rest _ ih =>
    obtain ⟨W, e, R, hf, hat⟩ := ih
    refine ⟨vs ++ W, e, R ++ rest, ?_, hat.instrs vs rest⟩
    have h1 := fnv_append_of_cons hf rest
    simp only [List.append_assoc, fnv_vals_append, h1]
  | @label s s' f f' n cont is is' hs _ =>
    refine ⟨[], .label n cont is, [], fnv_cons_of_none rfl _, ?_⟩
    exact .inr (.inr (.inr (.inl ⟨n, cont, is, s', f', is', rfl, hs, by simp⟩)))
  | @handler s s' f f' n cs is is' hs _ =>
    refine ⟨[], .handler n cs is, [], fnv_cons_of_none rfl _, ?_⟩
    exact .inr (.inr (.inr (.inr (.inl ⟨n, cs, is, s', f', is', rfl, hs, by simp⟩))))
  | @frame s s' f fi fi' n is is' hs _ =>
    refine ⟨[], .frame n fi is, [], fnv_cons_of_none rfl _, ?_⟩
    exact .inr (.inr (.inr (.inr (.inr ⟨n, fi, is, s', fi', is', rfl, hs, by simp⟩))))

/-! ### Trapped configurations -/

theorem fnv_top_trap (pre : List Val) (rest : List Admin) :
    fnv (vals pre ++ [.trap] ++ rest) = (pre, .trap :: rest) := by
  simp [fnv_cons_of_none (a := .trap) rfl]

theorem fnv_vals_single (pre : List Val) (x : Admin) (hx : x.val? = none) (rest : List Admin) :
    fnv (vals pre ++ [x] ++ rest) = (pre, x :: rest) := by
  simp [fnv_cons_of_none hx]

/-- `SoftAt` at a known first non-value. -/
theorem Soft.at_of {P : Profile} {s : Store H} {f : Frame} {code : List Admin} {d : Config H}
    (hs : Soft P ⟨s, f, code⟩ d) {W : List Val} {x : Admin} {R : List Admin}
    (hf : fnv code = (W, x :: R)) : SoftAt P s f W x R d := by
  obtain ⟨W', e', R', hf', hat⟩ := Soft.at hs
  have heq : W = W' ∧ x = e' ∧ R = R' := by simpa using hf.symm.trans hf'
  rw [heq.1, heq.2.1, heq.2.2]
  exact hat

/-- A `Soft` step at a label is a `Soft` step of its body. -/
theorem SoftAt.label_inv {P : Profile} {s : Store H} {f : Frame} {W : List Val} {n : Nat}
    {cont : List Instr} {B rest : List Admin} {d : Config H}
    (h : SoftAt P s f W (.label n cont B) rest d) :
    ∃ s' f' B', Soft P ⟨s, f, B⟩ ⟨s', f', B'⟩ ∧ d = ⟨s', f', vals W ++ [.label n cont B'] ++ rest⟩ := by
  rcases h with h | h | h | ⟨n', cont', is, s', f', is', he, hin, hd⟩ | h | h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact h.elim
  · obtain ⟨hn, hc, hb⟩ := Admin.label.inj he
    exact ⟨s', f', is', hb ▸ hin, by rw [hd, ← hn, ← hc]⟩
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)

/-- A `Soft` step at a handler is a `Soft` step of its body. -/
theorem SoftAt.handler_inv {P : Profile} {s : Store H} {f : Frame} {W : List Val} {n : Nat}
    {cs : List Catch} {B rest : List Admin} {d : Config H}
    (h : SoftAt P s f W (.handler n cs B) rest d) :
    ∃ s' f' B', Soft P ⟨s, f, B⟩ ⟨s', f', B'⟩ ∧ d = ⟨s', f', vals W ++ [.handler n cs B'] ++ rest⟩ := by
  rcases h with h | h | h | h | ⟨n', cs', is, s', f', is', he, hin, hd⟩ | h
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact h.elim
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)
  · obtain ⟨hn, hc, hb⟩ := Admin.handler.inj he
    exact ⟨s', f', is', hb ▸ hin, by rw [hd, ← hn, ← hc]⟩
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)

/-- A `Soft` step at a frame is a `Soft` step of its body under its frame. -/
theorem SoftAt.frame_inv {P : Profile} {s : Store H} {f : Frame} {W : List Val} {n : Nat}
    {fi : Frame} {B rest : List Admin} {d : Config H}
    (h : SoftAt P s f W (.frame n fi B) rest d) :
    ∃ s' fi' B', Soft P ⟨s, fi, B⟩ ⟨s', fi', B'⟩ ∧ d = ⟨s', f, vals W ++ [.frame n fi' B'] ++ rest⟩ := by
  rcases h with h | h | h | h | h | ⟨n', fi₀, is, s', fi', is', he, hin, hd⟩
  · exact absurd h.1 (by simp)
  · exact absurd h.1 (by simp)
  · exact h.elim
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)
  · obtain ⟨hn, hf, hb⟩ := Admin.frame.inj he
    exact ⟨s', fi', is', by rw [hf, hb]; exact hin, by rw [hd, ← hn]⟩

/-- The result of a step from a trapped configuration: same store and frame, still trapped. -/
def Doomed (s : Store H) (f : Frame) (d : Config H) : Prop :=
  d.store = s ∧ d.frame = f ∧ ∃ E' : Ctx, d.code = E'.fill [.trap]

theorem soft_doomed_top {P : Profile} {pre : List Val} {rest : List Admin} {s : Store H}
    {f : Frame} {d : Config H} (hs : Soft P ⟨s, f, vals pre ++ [.trap] ++ rest⟩ d) :
    Doomed s f d := by
  rcases Soft.at_of hs (fnv_top_trap pre rest) with ⟨-, p, q, u, r, -, -, -, hd⟩ | h | h | h | h | h
  · exact ⟨by rw [hd], by rw [hd], .top p r, by rw [hd]; rfl⟩
  · exact absurd h.1 (by simp)
  · exact h.elim
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)

/-- `Soft` steps from a `TRAP` under a callout context are bubbles: they keep the store and the
frame, and the `TRAP` stays under a callout context. -/
theorem soft_doomed {P : Profile} (E : Ctx) :
    ∀ {s : Store H} {f : Frame} {d : Config H}, Soft P ⟨s, f, E.fill [.trap]⟩ d →
      Doomed s f d := by
  induction E with
  | top pre rest => exact fun hs => soft_doomed_top hs
  | label pre n cont E rest ih =>
    intro s f d hs
    obtain ⟨s', f', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).label_inv
    obtain ⟨hs', hf', E', hE'⟩ := ih hin
    have hB : B' = E'.fill [.trap] := hE'
    exact ⟨by rw [hd]; exact hs', by rw [hd]; exact hf', .label pre n cont E' rest, by rw [hd, hB]; rfl⟩
  | handler pre n cs E rest ih =>
    intro s f d hs
    obtain ⟨s', f', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).handler_inv
    obtain ⟨hs', hf', E', hE'⟩ := ih hin
    have hB : B' = E'.fill [.trap] := hE'
    exact ⟨by rw [hd]; exact hs', by rw [hd]; exact hf', .handler pre n cs E' rest, by rw [hd, hB]; rfl⟩
  | frame pre n fi E rest ih =>
    intro s f d hs
    obtain ⟨s', fi', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).frame_inv
    obtain ⟨hs', -, E', hE'⟩ := ih hin
    have hB : B' = E'.fill [.trap] := hE'
    exact ⟨by rw [hd]; exact hs', by rw [hd], .frame pre n fi' E' rest, by rw [hd, hB]; rfl⟩

/-- The canonical step of a trapped configuration: the `TRAP` bubbles one level up, unless
it is a bare `TRAP`. -/
theorem doomed_step_or {P : Profile} :
    ∀ (E : Ctx) (s : Store H) (f : Frame), E = .top [] [] ∨
      ∃ E' : Ctx, Step P noHost ⟨s, f, E.fill [.trap]⟩ ⟨s, f, E'.fill [.trap]⟩
  | .top pre rest, s, f => by
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · exact .inr ⟨.top [] [], .trapInstrs hne⟩
    · have h : pre = [] ∧ rest = [] := by simpa only [ne_eq, not_or, not_not] using hne
      exact .inl (by rw [h.1, h.2])
  | .label pre n cont E rest, s, f => by
    refine .inr ?_
    rcases doomed_step_or E s f with h₁ | ⟨E', hE'⟩
    · rw [h₁]
      exact ⟨.top pre rest, lift_instrs pre rest ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩
        .trapLabel⟩
    · exact ⟨.label pre n cont E' rest, lift_instrs pre rest _ _ (.ctxtLabel hE')⟩
  | .handler pre n cs E rest, s, f => by
    refine .inr ?_
    rcases doomed_step_or E s f with h₁ | ⟨E', hE'⟩
    · rw [h₁]
      exact ⟨.top pre rest, lift_instrs pre rest ⟨s, f, [.handler n cs [.trap]]⟩ ⟨s, f, [.trap]⟩
        .trapHandler⟩
    · exact ⟨.handler pre n cs E' rest, lift_instrs pre rest _ _ (.ctxtHandler hE')⟩
  | .frame pre n fi E rest, s, f => by
    refine .inr ?_
    rcases doomed_step_or E s fi with h₁ | ⟨E', hE'⟩
    · rw [h₁]
      exact ⟨.top pre rest, lift_instrs pre rest ⟨s, f, [.frame n fi [.trap]]⟩ ⟨s, f, [.trap]⟩
        .trapFrame⟩
    · exact ⟨.frame pre n fi E' rest, lift_instrs pre rest ⟨s, f, [.frame n fi (E.fill [.trap])]⟩
        ⟨s, f, [.frame n fi (E'.fill [.trap])]⟩ (.ctxtFrame hE')⟩

/-- **Every step of a trapped configuration keeps it trapped**, in the same store and frame. -/
theorem step_doomed {P : Profile} {E : Ctx} {s : Store H} {f : Frame} {d : Config H}
    (h : Step P noHost ⟨s, f, E.fill [.trap]⟩ d) :
    d.store = s ∧ d.frame = f ∧ ∃ E' : Ctx, d.code = E'.fill [.trap] := by
  rcases doomed_step_or (P := P) E s f with hE | ⟨E₀, h₀⟩
  · have h' : Step P noHost ⟨s, f, [.trap]⟩ d := by rw [hE] at h; exact h
    exact absurd h' (fun h'' => not_step_trap h'')
  · rcases eq_or_soft h₀ h with hd | hs
    · exact ⟨by rw [hd], by rw [hd], E₀, by rw [hd]⟩
    · exact soft_doomed E hs

/-- A trapped code holds a non-value other than `THROW_REF` at top level. -/
theorem fill_trap_nonvalue (E : Ctx) :
    ∃ x ∈ E.fill [.trap], x.val? = none ∧ x ≠ .plain .throwRef := by
  cases E with
  | top pre rest => exact ⟨.trap, by simp [Ctx.fill], rfl, by simp⟩
  | label pre n cont E rest =>
    exact ⟨.label n cont (E.fill [.trap]), by simp [Ctx.fill], rfl, by simp⟩
  | handler pre n cs E rest =>
    exact ⟨.handler n cs (E.fill [.trap]), by simp [Ctx.fill], rfl, by simp⟩
  | frame pre n fi E rest =>
    exact ⟨.frame n fi (E.fill [.trap]), by simp [Ctx.fill], rfl, by simp⟩

/-- A trapped code is the code of a result only if that result is a trap. -/
theorem fill_trap_toAdmin {E : Ctx} {r : Result} (h : E.fill [.trap] = r.toAdmin) :
    r = .trap := by
  obtain ⟨x, hx, hv, hne⟩ := fill_trap_nonvalue E
  have hx' : x ∈ r.toAdmin := h ▸ hx
  cases r with
  | trap => rfl
  | values vs => exact absurd hv (mem_vals hx')
  | throw a =>
    have hx'' : x = .ref (.exn a) ∨ x = .plain .throwRef := by
      simpa [Result.toAdmin] using hx'
    rcases hx'' with rfl | rfl
    · simp [Admin.val?] at hv
    · exact absurd rfl hne

end Silmaril.Proofs.Wasm.Game.Choice
