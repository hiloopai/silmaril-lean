module

public import Silmaril.Proofs.Wasm.Game.Machine.SoftAt

/-!
# Trapped configurations terminate

Every host-free step from a trapped configuration `E.fill [TRAP]` (a `TRAP` under a callout
context) strictly decreases the size of the code, under any profile (`trapped_step_lt`): the
canonical step bubbles the `TRAP` one level up (`doomed_step_lt`), and the other steps are
`Soft` bubbles (`Choice.eq_or_soft`), which drop a non-empty part of a code sequence
(`trapped_soft_lt`, from the non-emptiness kept in `SoftAt`). Together with `step_doomed`
(steps keep the configuration trapped, in the same store and frame) this is the measure for
the divergence-sensitive backward simulation of a trapping provider.

New (no source file).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Choice

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-! ### Sizes of code -/

theorem sizeOf_append_list {α : Type} [SizeOf α] (l₁ l₂ : List α) :
    sizeOf (l₁ ++ l₂) + 1 = sizeOf l₁ + sizeOf l₂ := by
  induction l₁ with
  | nil => simp only [List.nil_append, List.nil.sizeOf_spec]; omega
  | cons a l ih => simp only [List.cons_append, List.cons.sizeOf_spec]; omega

theorem sizeOf_list_pos {α : Type} [SizeOf α] (l : List α) : 1 ≤ sizeOf l := by
  cases l with
  | nil => simp only [List.nil.sizeOf_spec, le_refl]
  | cons a l => simp only [List.cons.sizeOf_spec]; omega

theorem sizeOf_list_ne_nil {α : Type} [SizeOf α] {l : List α} (h : l ≠ []) : 2 ≤ sizeOf l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l =>
    have h₁ : 1 ≤ sizeOf l := sizeOf_list_pos l
    simp only [List.cons.sizeOf_spec]
    omega

/-- Replacing the middle of a sequence by a smaller one makes it smaller. -/
theorem sizeOf_mid_lt {A B X Y : List Admin} (h : sizeOf X < sizeOf Y) :
    sizeOf (A ++ X ++ B) < sizeOf (A ++ Y ++ B) := by
  have h₁ := sizeOf_append_list (A ++ X) B
  have h₂ := sizeOf_append_list A X
  have h₃ := sizeOf_append_list (A ++ Y) B
  have h₄ := sizeOf_append_list A Y
  omega

/-- A single block with a smaller body is smaller. -/
theorem sizeOf_label_lt {n : Nat} {cont : List Instr} {b b' : List Admin}
    (h : sizeOf b' < sizeOf b) :
    sizeOf [Admin.label n cont b'] < sizeOf [Admin.label n cont b] := by
  simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec]
  omega

theorem sizeOf_handler_lt {n : Nat} {cs : List Catch} {b b' : List Admin}
    (h : sizeOf b' < sizeOf b) :
    sizeOf [Admin.handler n cs b'] < sizeOf [Admin.handler n cs b] := by
  simp only [List.cons.sizeOf_spec, Admin.handler.sizeOf_spec]
  omega

theorem sizeOf_frame_lt {n : Nat} {fi fi' : Frame} {b b' : List Admin}
    (h : sizeOf b' < sizeOf b) (hf : sizeOf fi' = sizeOf fi) :
    sizeOf [Admin.frame n fi' b'] < sizeOf [Admin.frame n fi b] := by
  simp only [List.cons.sizeOf_spec, Admin.frame.sizeOf_spec]
  omega

/-- A bare `TRAP` is smaller than a block holding code. -/
theorem sizeOf_trap_lt_label {n : Nat} {cont : List Instr} {b : List Admin} :
    sizeOf [Admin.trap] < sizeOf [Admin.label n cont b] := by
  have h := sizeOf_list_pos b
  simp only [List.cons.sizeOf_spec, Admin.label.sizeOf_spec, Admin.trap.sizeOf_spec]
  omega

theorem sizeOf_trap_lt_handler {n : Nat} {cs : List Catch} {b : List Admin} :
    sizeOf [Admin.trap] < sizeOf [Admin.handler n cs b] := by
  have h := sizeOf_list_pos b
  simp only [List.cons.sizeOf_spec, Admin.handler.sizeOf_spec, Admin.trap.sizeOf_spec]
  omega

theorem sizeOf_trap_lt_frame {n : Nat} {fi : Frame} {b : List Admin} :
    sizeOf [Admin.trap] < sizeOf [Admin.frame n fi b] := by
  have h := sizeOf_list_pos b
  simp only [List.cons.sizeOf_spec, Admin.frame.sizeOf_spec, Admin.trap.sizeOf_spec]
  omega

/-- Dropping a non-empty part around a `TRAP` makes the code smaller. -/
theorem sizeOf_bubble_lt {p q : List Val} {u r : List Admin} (hqu : q ≠ [] ∨ u ≠ []) :
    sizeOf (vals p ++ [Admin.trap] ++ r) < sizeOf (vals (p ++ q) ++ [Admin.trap] ++ (u ++ r)) := by
  have hv : vals (p ++ q) = vals p ++ vals q := vals_append p q
  have hq : 1 ≤ sizeOf (vals q) := sizeOf_list_pos _
  have hu : 1 ≤ sizeOf u := sizeOf_list_pos _
  have hqu' : 2 ≤ sizeOf (vals q) ∨ 2 ≤ sizeOf u := by
    rcases hqu with h | h
    · refine .inl (sizeOf_list_ne_nil ?_)
      intro hq'
      exact h (by simpa [vals] using hq')
    · exact .inr (sizeOf_list_ne_nil h)
  rw [hv]
  have e₁ := sizeOf_append_list (vals p ++ [Admin.trap]) r
  have e₂ := sizeOf_append_list (vals p) [Admin.trap]
  have e₃ := sizeOf_append_list (vals p ++ vals q ++ [Admin.trap]) (u ++ r)
  have e₄ := sizeOf_append_list (vals p ++ vals q) [Admin.trap]
  have e₅ := sizeOf_append_list (vals p) (vals q)
  have e₆ := sizeOf_append_list u r
  omega

/-! ### The canonical step -/

/-- **The canonical step of a trapped configuration decreases the size of the code.** -/
theorem doomed_step_lt {P : Profile} :
    ∀ (E : Ctx) (s : Store H) (f : Frame), E = .top [] [] ∨
      ∃ E' : Ctx, Step P noHost ⟨s, f, E.fill [.trap]⟩ ⟨s, f, E'.fill [.trap]⟩ ∧
        sizeOf (E'.fill [.trap]) < sizeOf (E.fill [.trap])
  | .top pre rest, s, f => by
    by_cases hne : pre ≠ [] ∨ rest ≠ []
    · refine .inr ⟨.top [] [], .trapInstrs hne, ?_⟩
      have h := sizeOf_bubble_lt (p := []) (q := pre) (u := rest) (r := []) hne
      simpa [Ctx.fill] using h
    · have h : pre = [] ∧ rest = [] := by simpa only [ne_eq, not_or, not_not] using hne
      exact .inl (by rw [h.1, h.2])
  | .label pre n cont E rest, s, f => by
    refine .inr ?_
    rcases doomed_step_lt (P := P) E s f with h₁ | ⟨E', hE', hlt⟩
    · rw [h₁]
      refine ⟨.top pre rest, lift_instrs pre rest ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩
        .trapLabel, ?_⟩
      have h := sizeOf_mid_lt (A := vals pre) (B := rest)
        (sizeOf_trap_lt_label (n := n) (cont := cont) (b := [.trap]))
      simpa [Ctx.fill] using h
    · refine ⟨.label pre n cont E' rest, lift_instrs pre rest _ _ (.ctxtLabel hE'), ?_⟩
      exact sizeOf_mid_lt (sizeOf_label_lt hlt)
  | .handler pre n cs E rest, s, f => by
    refine .inr ?_
    rcases doomed_step_lt (P := P) E s f with h₁ | ⟨E', hE', hlt⟩
    · rw [h₁]
      refine ⟨.top pre rest, lift_instrs pre rest ⟨s, f, [.handler n cs [.trap]]⟩
        ⟨s, f, [.trap]⟩ .trapHandler, ?_⟩
      have h := sizeOf_mid_lt (A := vals pre) (B := rest)
        (sizeOf_trap_lt_handler (n := n) (cs := cs) (b := [.trap]))
      simpa [Ctx.fill] using h
    · refine ⟨.handler pre n cs E' rest, lift_instrs pre rest _ _ (.ctxtHandler hE'), ?_⟩
      exact sizeOf_mid_lt (sizeOf_handler_lt hlt)
  | .frame pre n fi E rest, s, f => by
    refine .inr ?_
    rcases doomed_step_lt (P := P) E s fi with h₁ | ⟨E', hE', hlt⟩
    · rw [h₁]
      refine ⟨.top pre rest, lift_instrs pre rest ⟨s, f, [.frame n fi [.trap]]⟩ ⟨s, f, [.trap]⟩
        .trapFrame, ?_⟩
      have h := sizeOf_mid_lt (A := vals pre) (B := rest)
        (sizeOf_trap_lt_frame (n := n) (fi := fi) (b := [.trap]))
      simpa [Ctx.fill] using h
    · refine ⟨.frame pre n fi E' rest, lift_instrs pre rest ⟨s, f, [.frame n fi (E.fill [.trap])]⟩
        ⟨s, f, [.frame n fi (E'.fill [.trap])]⟩ (.ctxtFrame hE'), ?_⟩
      exact sizeOf_mid_lt (sizeOf_frame_lt hlt rfl)

/-! ### `Soft` steps -/

/-- A `Soft` step at the top-level `TRAP` drops a non-empty part. -/
theorem trapped_soft_top_lt {P : Profile} {pre : List Val} {rest : List Admin} {s : Store H}
    {f : Frame} {d : Config H} (hs : Soft P ⟨s, f, vals pre ++ [.trap] ++ rest⟩ d) :
    sizeOf d.code < sizeOf (vals pre ++ [Admin.trap] ++ rest) := by
  rcases Soft.at_of hs (fnv_top_trap pre rest) with
    ⟨-, p, q, u, r, hqu, hW, hr, hd⟩ | h | h | h | h | h
  · rw [hd, hW, hr]
    exact sizeOf_bubble_lt hqu
  · exact absurd h.1 (by simp)
  · exact h.elim
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)
  · obtain ⟨_, _, _, _, _, _, h, -⟩ := h; exact absurd h (by simp)

/-- **`Soft` steps of a trapped configuration decrease the size of the code.** -/
theorem trapped_soft_lt {P : Profile} (E : Ctx) :
    ∀ {s : Store H} {f : Frame} {d : Config H}, Soft P ⟨s, f, E.fill [.trap]⟩ d →
      sizeOf d.code < sizeOf (E.fill [.trap]) := by
  induction E with
  | top pre rest => exact fun hs => trapped_soft_top_lt hs
  | label pre n cont E rest ih =>
    intro s f d hs
    obtain ⟨s', f', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).label_inv
    rw [hd]
    exact sizeOf_mid_lt (sizeOf_label_lt (ih hin))
  | handler pre n cs E rest ih =>
    intro s f d hs
    obtain ⟨s', f', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).handler_inv
    rw [hd]
    exact sizeOf_mid_lt (sizeOf_handler_lt (ih hin))
  | frame pre n fi E rest ih =>
    intro s f d hs
    obtain ⟨s', fi', B', hin, hd⟩ := (Soft.at_of hs (fnv_vals_single pre _ rfl rest)).frame_inv
    have hfi : fi' = fi := (soft_doomed E hin).2.1
    rw [hd]
    exact sizeOf_mid_lt (sizeOf_frame_lt (ih hin) (by rw [hfi]))

/-- **Every step of a trapped configuration decreases the size of the code.** -/
theorem trapped_step_lt {P : Profile} {E : Ctx} {s : Store H} {f : Frame} {d : Config H}
    (h : Step P noHost ⟨s, f, E.fill [.trap]⟩ d) : sizeOf d.code < sizeOf (E.fill [.trap]) := by
  rcases doomed_step_lt (P := P) E s f with hE | ⟨E₀, h₀, hlt⟩
  · have h' : Step P noHost ⟨s, f, [.trap]⟩ d := by rw [hE] at h; exact h
    exact absurd h' (fun h'' => not_step_trap h'')
  · rcases eq_or_soft h₀ h with hd | hs
    · rw [hd]; exact hlt
    · exact trapped_soft_lt E hs

end Silmaril.Proofs.Wasm.Game.Choice
