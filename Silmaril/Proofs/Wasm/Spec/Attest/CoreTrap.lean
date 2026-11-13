module

public import Silmaril.Wasm.Spec.Attest.Core.Defs
public import Silmaril.Wasm.Game.Strategy.Thms
public import Silmaril.Proofs.Wasm.Spec.Attest.Comp

/-!
# Core 3.0 modules propagate traps

* `steps_fill_trap`: a trap in a callout context reduces to a trap at the top (every profile,
  every host, store and frame unchanged);
* `reach_of_steps_active`: a host-free Core run from an active thread is a run of the machine;
* `path_append`, `path_snoc`, `path_pos`: runs of the instance's transition system;
* **`strategy_trapProp`**: for every scalar instance, store and profile, a trap answer to a
  pending import call makes the pending export call return a trap.

`step_lift_instrs` is copied from `Silmaril.Proofs.Wasm.Game.Linking.Split.Typed` (this
repository), whose topic does not export it; `steps_fill_trap` follows its `fill_trap_reach`
at the level of Core runs. The rest is new.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Spec.Attest

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec.Attest Silmaril.Wasm.Spec.Attest.Core
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ### Traps bubble up -/

theorem step_lift_instrs {P : Profile} {host : HostSemantics Nat} {s s' : Store Nat}
    {g g' : Frame} {pre : List Val} {is is' rest : List Admin}
    (h : Step P host ⟨s, g, is⟩ ⟨s', g', is'⟩) :
    Step P host ⟨s, g, vals pre ++ is ++ rest⟩ ⟨s', g', vals pre ++ is' ++ rest⟩ := by
  by_cases hne : pre ≠ [] ∨ rest ≠ []
  · exact Step.ctxtInstrs h hne
  · have hnil : pre = [] ∧ rest = [] := by simpa only [ne_eq, not_or, not_not] using hne
    rw [hnil.1, hnil.2]
    simpa [vals] using h

/-- A trap at the top of a sequence ends the sequence. -/
theorem steps_top_trap (P : Profile) (host : HostSemantics Nat) (s : Store Nat) (F : Frame)
    (pre : List Val) (rest : List Admin) :
    Steps P host ⟨s, F, vals pre ++ [.trap] ++ rest⟩ ⟨s, F, [.trap]⟩ := by
  by_cases hne : pre ≠ [] ∨ rest ≠ []
  · exact .single (Step.trapInstrs hne)
  · have hnil : pre = [] ∧ rest = [] := by simpa only [ne_eq, not_or, not_not] using hne
    rw [hnil.1, hnil.2]
    exact .refl

/-- Runs inside a label. -/
theorem steps_label {P : Profile} {host : HostSemantics Nat} {c c' : Config Nat} (pre : List Val)
    (n : Nat) (cont : List Instr) (rest : List Admin) (h : Steps P host c c') :
    Steps P host ⟨c.store, c.frame, vals pre ++ [.label n cont c.code] ++ rest⟩
      ⟨c'.store, c'.frame, vals pre ++ [.label n cont c'.code] ++ rest⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (step_lift_instrs (Step.ctxtLabel hst))

/-- Runs inside a handler. -/
theorem steps_handler {P : Profile} {host : HostSemantics Nat} {c c' : Config Nat}
    (pre : List Val) (n : Nat) (cs : List Catch) (rest : List Admin) (h : Steps P host c c') :
    Steps P host ⟨c.store, c.frame, vals pre ++ [.handler n cs c.code] ++ rest⟩
      ⟨c'.store, c'.frame, vals pre ++ [.handler n cs c'.code] ++ rest⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (step_lift_instrs (Step.ctxtHandler hst))

/-- Runs inside a frame. -/
theorem steps_frame {P : Profile} {host : HostSemantics Nat} {c c' : Config Nat} (F : Frame)
    (pre : List Val) (n : Nat) (rest : List Admin) (h : Steps P host c c') :
    Steps P host ⟨c.store, F, vals pre ++ [.frame n c.frame c.code] ++ rest⟩
      ⟨c'.store, F, vals pre ++ [.frame n c'.frame c'.code] ++ rest⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (step_lift_instrs (Step.ctxtFrame hst))

/-- **Trap bubbling**: a trap in a callout context reaches the top, store and frame unchanged. -/
theorem steps_fill_trap (P : Profile) (host : HostSemantics Nat) (s : Store Nat) :
    ∀ (E : Ctx) (F : Frame), Steps P host ⟨s, F, E.fill [.trap]⟩ ⟨s, F, [.trap]⟩
  | .top pre rest, F => steps_top_trap P host s F pre rest
  | .label pre n cont E rest, F => by
    show Steps P host ⟨s, F, vals pre ++ [.label n cont (E.fill [.trap])] ++ rest⟩ ⟨s, F, [.trap]⟩
    have h₁ := steps_label pre n cont rest (steps_fill_trap P host s E F)
    have h₂ : Step P host ⟨s, F, vals pre ++ [.label n cont [.trap]] ++ rest⟩
        ⟨s, F, vals pre ++ [.trap] ++ rest⟩ := step_lift_instrs Step.trapLabel
    exact (h₁.tail h₂).trans (steps_top_trap P host s F pre rest)
  | .handler pre n cs E rest, F => by
    show Steps P host ⟨s, F, vals pre ++ [.handler n cs (E.fill [.trap])] ++ rest⟩
      ⟨s, F, [.trap]⟩
    have h₁ := steps_handler pre n cs rest (steps_fill_trap P host s E F)
    have h₂ : Step P host ⟨s, F, vals pre ++ [.handler n cs [.trap]] ++ rest⟩
        ⟨s, F, vals pre ++ [.trap] ++ rest⟩ := step_lift_instrs Step.trapHandler
    exact (h₁.tail h₂).trans (steps_top_trap P host s F pre rest)
  | .frame pre n fi E rest, F => by
    show Steps P host ⟨s, F, vals pre ++ [.frame n fi (E.fill [.trap])] ++ rest⟩ ⟨s, F, [.trap]⟩
    have h₁ := steps_frame F pre n rest (steps_fill_trap P host s E fi)
    have h₂ : Step P host ⟨s, F, vals pre ++ [.frame n fi [.trap]] ++ rest⟩
        ⟨s, F, vals pre ++ [.trap] ++ rest⟩ := step_lift_instrs Step.trapFrame
    exact (h₁.tail h₂).trans (steps_top_trap P host s F pre rest)

/-- **Host-free Core runs of an active thread are machine runs.** -/
theorem reach_of_steps_active {P : Profile} {s : Store Nat} {F : Frame} {X : List Admin}
    {c' : Config Nat} (h : Steps P (fun _ _ _ _ => False) ⟨s, F, X⟩ c') :
    Reach P (s, .active F X) (c'.store, .active c'.frame c'.code) := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail ⟨_, _, rfl, hst⟩

/-! ### Runs of the instance -/

variable {I : ScalarInstance} {P : Profile}

theorem path_append {x y z : I.HState} {p q : List (Move I.E I.F)} (h₁ : I.Path P x p y)
    (h₂ : I.Path P y q z) : I.Path P x (p ++ q) z := by
  induction h₁ with
  | nil => exact h₂
  | cons ht _ ih => exact .cons ht (ih h₂)

theorem path_snoc {x z : I.HState} {p : List (Move I.E I.F)} {m : Move I.E I.F}
    (h : I.Path P x (p ++ [m]) z) : ∃ y, I.Path P x p y ∧ I.Trans P y m z := by
  induction p generalizing x with
  | nil =>
    cases h with
    | cons ht hp => cases hp; exact ⟨x, .nil x, ht⟩
  | cons o p ih =>
    cases h with
    | cons ht hp =>
      obtain ⟨y, h₁, h₂⟩ := ih hp
      exact ⟨y, .cons ht h₁, h₂⟩

theorem trans_pos {x y : I.HState} {m : Move I.E I.F} (h : I.Trans P x m y) :
    Step x.pos m y.pos := by
  cases h with
  | call s f => exact .ask f
  | ucall _ _ _ => exact .call _ _
  | uret v => exact .reply _ _ v
  | oret _ _ _ => exact .ret _ _

theorem path_pos {x y : I.HState} {p : List (Move I.E I.F)} (h : I.Path P x p y) :
    Path x.pos p y.pos := by
  induction h with
  | nil => exact .nil _
  | cons ht _ ih => exact .cons (trans_pos ht) ih

/-- The trap answer is an answer of every function type. -/
theorem ofResult_trap (ft : FnType) : Answer.ofResult? ft .trap = some .trap := by
  simp only [Answer.ofResult?]

/-- A trap answer to a callout, resumed: the trap reaches the top of the thread. -/
theorem reach_resume_trap {s : Store Nat} {t : Thread} {h : Nat} {args : List Val}
    (hc : CalloutAt s t h args) :
    ∃ F, Reach P (s, resumeResult s t .trap) (s, .active F [.trap]) := by
  obtain ⟨E, a, hd⟩ := hc
  have hr : resumeResult s t .trap = .active (t.config s).frame (E.fill [.trap]) := by
    simp only [resumeResult, hd, Result.toAdmin]
  rw [hr]
  exact ⟨_, reach_of_steps_active (steps_fill_trap P _ s E _)⟩

/-- **Every Core 3.0 module propagates traps**, at every profile and store. -/
theorem strategy_trapProp (I : ScalarInstance) (P : Profile) (s : Store Nat) :
    TrapProp (I.strategy P s) trapAns trapAns := by
  intro p q m hp hw
  obtain ⟨y, hy⟩ := I.mem_strategy_iff.1 hp
  obtain ⟨p', rfl, -⟩ := path_wait hw
  obtain ⟨y₀, -, ht⟩ := path_snoc hy
  cases ht with
  | @ucall f s₀ s' t₀ t' h args e run callout op =>
    have hpos : Path .idle (p' ++ [.inl (.ask m)]) (.wait f m) := path_pos hy
    have hfq : (.wait f m : Pos I.E I.F) = .wait q m := Path.det hpos hw
    cases hfq
    obtain ⟨F, hreach⟩ := reach_resume_trap (P := P) callout
    refine I.mem_strategy_iff.2 ⟨.idle s', path_append hy (.cons (.uret .trap) (.cons ?_ (.nil _)))⟩
    exact .oret (r := .trap) hreach (show ((Thread.active F [.trap]).config s').code = [.trap] from rfl)
      (ofResult_trap _)

end Silmaril.Proofs.Wasm.Spec.Attest
