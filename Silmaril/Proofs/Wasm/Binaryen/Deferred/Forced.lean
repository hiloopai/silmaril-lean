module

public import Silmaril.Wasm.Binaryen.Deferred.Defs
public import Silmaril.Wasm.Binaryen.CoalesceLocalsCompletion
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro

@[expose] public section

/-! # Forced local steps and a rank they decrease

Silmaril's CoalesceLocals reverse simulation (`Silmaril.Wasm.Binaryen.CoalesceLocalsCompletion`,
pinned silmaril-lean) lets the left side complete one pending `local.set` before its
frame agrees with the right side. `Forced` generalises that `Completion` to three
local steps, each of which is the *only* closed-host step of its configuration at
every numerical profile:

* `set`: `w; local.set x` (in bounds) writes `w`;
* `get`: `local.get x` (holding `v`) pushes `v`;
* `tee`: `w; local.tee x` expands to `w; w; local.set x`;

under any value prefix and suffix, and under labels, handlers and frames. A forced
step keeps the store and strictly decreases `fwRank`, a payload-independent rank in
which `local.tee` weighs 4, `local.get` weighs 2 and every other instruction and
value weighs 1. The context cases and their uniqueness proofs are silmaril's
(`Completion.{label,handler,frame}`, `Completion.unique`), copied with the new base
cases added.
-/

namespace Silmaril.Wasm.Binaryen.Deferred

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Binaryen.CoalesceLocalsLite (labelRed_ctxt_of_step handlerInv_ctxt_of_step
  frameRedex_ctxt_of_step)

variable {H : Type} {P : Profile}

/-! ## The rank -/

theorem fwRank_pos {a : List Admin} (ha : a ≠ []) : 0 < fwRank a := by
  cases a with
  | nil => simp at ha
  | cons x a => have := fwAdminRank_pos x; simp; omega

instance lawfulCodeRank_fwRank : LawfulCodeRank fwRank where
  context_lt := by intros; simp only [fwRank_append]; omega
  infix_lt := by
    intro p m q hm
    have := fwRank_pos hm
    simp only [fwRank_append]
    omega
  label_body_lt := by intros; simp [fwAdminRank]; omega
  label_lt := by intros; simp_all [fwAdminRank]
  handler_body_lt := by intros; simp [fwAdminRank]; omega
  handler_lt := by intros; simp_all [fwAdminRank]
  frame_body_lt := by intros; simp [fwAdminRank]; omega
  frame_lt := by intros; simp_all [fwAdminRank]

/-- The rank ignores the frame of a runtime frame. -/
theorem fwRank_frame_lt (p q : List Admin) (n : Nat) (fi fj : Frame) {b₁ b : List Admin}
    (h : fwRank b₁ < fwRank b) :
    fwRank (p ++ [.frame n fj b₁] ++ q) < fwRank (p ++ [.frame n fi b] ++ q) := by
  simp only [fwRank_append, fwRank_cons, fwRank_nil, fwAdminRank]
  omega

/-! ## Forced steps -/

namespace Forced

theorem rank {c d : Config H} (h : Forced c d) : fwRank d.code < fwRank c.code := by
  induction h with
  | set => simp; omega
  | get => simp [fwAdminRank]
  | tee => simp [fwAdminRank]; omega
  | label _ _ _ _ _ ih => simp only [fwRank_append, fwRank_cons, fwAdminRank, fwRank_nil] at *; omega
  | handler _ _ _ _ _ ih => simp only [fwRank_append, fwRank_cons, fwAdminRank, fwRank_nil] at *; omega
  | frame _ _ _ _ _ ih => simp only [fwRank_append, fwRank_cons, fwAdminRank, fwRank_nil] at *; omega

/-! ## Uniqueness of forced steps -/

/-- A typed-free read has exactly one closed-host successor. -/
theorem get_unique {s : Store H} {f : Frame} {vs : List Val} {x : LocalIdx} {v : Val}
    {rest : List Admin} (hv : f.local? x = some (some v)) :
    ∀ e, Step P closedHost ⟨s, f, vals vs ++ [.plain (.localGet x)] ++ rest⟩ e →
      e = ⟨s, f, vals vs ++ [v.toAdmin] ++ rest⟩ := by
  rintro ⟨s₁, g, es⟩ hs
  have hs' : Step P closedHost ⟨s, f, vals vs ++ .plain (.localGet x) :: rest⟩ ⟨s₁, g, es⟩ := by
    simpa using hs
  obtain ⟨w, hw, hs₁, hg, hes⟩ : ∃ w, f.local? x = some (some w) ∧ s₁ = s ∧ g = f ∧
      es = vals vs ++ w.toAdmin :: rest := RedundantSetLine.get_step_inv hs'
  have hwv : w = v := Option.some.inj (Option.some.inj (hw.symm.trans hv))
  rw [hs₁, hg, hes, hwv]
  simp

theorem unique_label {s : Store H} {f f' : Frame} {b b' : List Admin}
    (hb : Step P closedHost ⟨s, f, b⟩ ⟨s, f', b'⟩)
    (ih : ∀ e, Step P closedHost ⟨s, f, b⟩ e → e = ⟨s, f', b'⟩)
    (vs : List Val) (n : Nat) (cont : List Instr) (rest : List Admin) :
    ∀ e, Step P closedHost ⟨s, f, vals vs ++ [.label n cont b] ++ rest⟩ e →
      e = ⟨s, f', vals vs ++ [.label n cont b'] ++ rest⟩ := by
  rintro ⟨s₁, g, es⟩ hs
  have hs' : Step P closedHost ⟨s, f, vals vs ++ .label n cont b :: rest⟩ ⟨s₁, g, es⟩ := by
    simpa using hs
  rcases Step.split_head rfl hs' with ⟨ws, us, is', hV, hs₁, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨out, hr, rfl⟩ := Closure.Step.label_inv hs₁
    obtain ⟨z, hz, rfl⟩ := labelRed_ctxt_of_step hb hr
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj (ih _ hz)
    simp [hV]
  · cases h
  · cases h

theorem unique_handler {s : Store H} {f f' : Frame} {b b' : List Admin}
    (hb : Step P closedHost ⟨s, f, b⟩ ⟨s, f', b'⟩)
    (ih : ∀ e, Step P closedHost ⟨s, f, b⟩ e → e = ⟨s, f', b'⟩)
    (vs : List Val) (n : Nat) (cs : List Catch) (rest : List Admin) :
    ∀ e, Step P closedHost ⟨s, f, vals vs ++ [.handler n cs b] ++ rest⟩ e →
      e = ⟨s, f', vals vs ++ [.handler n cs b'] ++ rest⟩ := by
  rintro ⟨s₁, g, es⟩ hs
  have hs' : Step P closedHost ⟨s, f, vals vs ++ .handler n cs b :: rest⟩ ⟨s₁, g, es⟩ := by
    simpa using hs
  rcases Step.split_head rfl hs' with ⟨ws, us, is', hV, hs₁, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨out, hr, rfl⟩ := Step.handler_inv hs₁
    obtain ⟨z, hz, rfl⟩ := handlerInv_ctxt_of_step hb hr
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj (ih _ hz)
    simp [hV]
  · cases h
  · cases h

theorem unique_frame {s : Store H} {fi fi' : Frame} {b b' : List Admin}
    (hb : Step P closedHost ⟨s, fi, b⟩ ⟨s, fi', b'⟩)
    (ih : ∀ e, Step P closedHost ⟨s, fi, b⟩ e → e = ⟨s, fi', b'⟩)
    (f : Frame) (vs : List Val) (n : Nat) (rest : List Admin) :
    ∀ e, Step P closedHost ⟨s, f, vals vs ++ [.frame n fi b] ++ rest⟩ e →
      e = ⟨s, f, vals vs ++ [.frame n fi' b'] ++ rest⟩ := by
  rintro ⟨s₁, g, es⟩ hs
  have hs' : Step P closedHost ⟨s, f, vals vs ++ .frame n fi b :: rest⟩ ⟨s₁, g, es⟩ := by
    simpa using hs
  rcases Step.split_head rfl hs' with ⟨ws, us, is', hV, hs₁, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨out, rfl, hr⟩ := Closure.Step.frame_redex_aux hs₁ us n fi b rfl
    obtain ⟨fj, z, hz, rfl, rfl⟩ := frameRedex_ctxt_of_step hb hr
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj (ih _ hz)
    simp [hV]
  · cases h
  · cases h

/-- **A forced step is the only closed-host step**, at every numerical profile and
under every nested runtime context. -/
theorem unique {c d : Config H} (h : Forced c d) :
    ∀ e, Step P closedHost c e → e = d := by
  induction h with
  | set => exact fun _ hs => SimplifyLocalsLite.localSet_step_unique hs
  | get _ _ _ _ _ _ hv => exact get_unique hv
  | tee => exact fun _ hs => SimplifyLocalsLite.localTee_step_unique hs
  | label hb vs n cont rest ih => exact unique_label hb.step ih vs n cont rest
  | handler hb vs n cs rest ih => exact unique_handler hb.step ih vs n cs rest
  | frame hb f vs n rest ih => exact unique_frame hb.step ih f vs n rest

end Forced

end Silmaril.Wasm.Binaryen.Deferred
