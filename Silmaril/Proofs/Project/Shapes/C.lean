module

public import Silmaril.Project.Shapes.C.Defs

/-!
# Proofs for `Silmaril.Project.Shapes.C.Thms`: what follows a procedure's return

A state of `CFn.source k0` is final when the body has evaluated to a value `v` with only the
procedure frame on top of the caller's continuation `k0`. Core does not stop there: it pops the
procedure frame and continues in `k0`. With the empty continuation the next two states are
`value v` with no frames and `halt (defined v)`, so a returned state is safe
(`safe_of_final`). With a continuation that goes wrong it is not: a `mainNext` frame outside the
startup sequence ends the run with an error (`not_safe_of_final_mainNext`).
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.C

open Silmaril.Cerberus
open Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes.C
open Silmaril.X86.SystemV.CApi (Signature)

variable {file : Program} {labels : Labels}

/-! ## The requests after a return -/

theorem request_procedureReturn (v : Val) (ls : Labels) (k : List Frame)
    (m : Mem.Concrete.State) :
    request file labels ⟨.value v, .procedureReturn ls :: k, m⟩ = .next (.value v) k := by
  unfold request
  rw [requestAux.eq_def]
  simp [awaitsScheduling]

theorem request_empty (v : Val) (m : Mem.Concrete.State) :
    request file labels ⟨.value v, [], m⟩ = .end_ (.defined v) := by
  unfold request
  rw [requestAux.eq_def]
  simp [awaitsScheduling]

theorem request_mainNext (v w : Val) (p : Mem.Concrete.Pointer) (m : Mem.Concrete.State) :
    request file labels ⟨.value v, [.mainNext p (.value w)], m⟩ =
      .end_ (.error "startup allocation continuation") := by
  unfold request
  rw [requestAux.eq_def]
  simp [awaitsScheduling]

/-! ## Steps from a request -/

theorem step_of_next {s t : State} {a : Label} {c : Control} {k : List Frame}
    (hr : request file labels s = .next c k) (hs : Step file labels s a t) :
    t = ⟨c, k, s.memory⟩ := by
  cases hs with
  | respond _ resp =>
    rw [hr] at resp
    cases resp
    rfl

theorem step_of_end {s t : State} {a : Label} {o : Outcome}
    (hr : request file labels s = .end_ o) (hs : Step file labels s a t) :
    t = ⟨.halt o, [], s.memory⟩ := by
  cases hs with
  | respond _ resp =>
    rw [hr] at resp
    cases resp
    rfl

theorem no_step_halt {o : Outcome} {k : List Frame} {m : Mem.Concrete.State} {a : Label}
    {t : State} : ¬ Step file labels ⟨.halt o, k, m⟩ a t := by
  intro hs
  cases hs with
  | respond live _ => exact live o rfl

theorem step_next {s : State} {c : Control} {k : List Frame}
    (live : ∀ o, s.control ≠ .halt o) (hr : request file labels s = .next c k) :
    Step file labels s .tau ⟨c, k, s.memory⟩ :=
  .respond live (by rw [hr]; exact .next)

theorem step_end {s : State} {o : Outcome}
    (live : ∀ o, s.control ≠ .halt o) (hr : request file labels s = .end_ o) :
    Step file labels s (.terminal o) ⟨.halt o, [], s.memory⟩ :=
  .respond live (by rw [hr]; exact .end_)

/-! ## After the return -/

variable {sig : Signature}

/-- The states reachable from a returned state with the empty continuation: itself, the value
with no frames, and the defined end. -/
theorem reach_of_final {F : CFn sig} {m : Mem.Concrete.State} {t : State} {v : Val}
    (ht : Relation.ReflTransGen (F.source []).step
      ⟨.value v, [.procedureReturn F.bodyLabels], m⟩ t) :
    t = ⟨.value v, [.procedureReturn F.bodyLabels], m⟩ ∨ t = ⟨.value v, [], m⟩ ∨
      t = ⟨.halt (.defined v), [], m⟩ := by
  induction ht with
  | refl => exact .inl rfl
  | tail _ hstep ih =>
    obtain ⟨a, hstep⟩ := hstep
    rcases ih with rfl | rfl | rfl
    · have h := step_of_next (request_procedureReturn (file := F.file) (labels := F.labels)
        v F.bodyLabels [] m) hstep
      exact .inr (.inl h)
    · have h := step_of_end (request_empty (file := F.file) (labels := F.labels) v m) hstep
      exact .inr (.inr h)
    · exact absurd hstep no_step_halt

/-- **A returned call with the empty continuation is safe**: Core pops the procedure frame and
halts with the defined value; nothing after it can go wrong, and the run is finite. -/
theorem safe_of_final {F : CFn sig} {s : State} {v : Val} (h : (F.source []).final s v) :
    (F.source []).Safe s := by
  obtain ⟨hc, hk⟩ := h
  obtain ⟨control, stack, m⟩ := s
  simp only at hc hk
  subst hc hk
  refine ⟨fun t ht hw => ?_, ?_⟩
  · obtain ⟨o, ho, hnd⟩ := hw
    rcases reach_of_final ht with rfl | rfl | rfl
    · cases ho
    · cases ho
    · cases ho; exact hnd v rfl
  · refine ⟨_, fun t ⟨a, hs⟩ => ?_⟩
    have ht := step_of_next (request_procedureReturn (file := F.file) (labels := F.labels)
      v F.bodyLabels [] m) hs
    subst ht
    refine ⟨_, fun u ⟨b, hu⟩ => ?_⟩
    have hu' := step_of_end (request_empty (file := F.file) (labels := F.labels) v m) hu
    subst hu'
    exact ⟨_, fun w ⟨c, hw⟩ => absurd hw no_step_halt⟩

/-- **With a continuation that goes wrong, a returned state is not safe**: after the return,
a `mainNext` frame outside the startup sequence ends the run with an error. So a meaning that
quantified over every caller continuation would hold of no argument tuple. -/
theorem not_safe_of_final_mainNext {F : CFn sig} {p : Mem.Concrete.Pointer} {w : Val}
    {s : State} {v : Val} (h : (F.source [.mainNext p (.value w)]).final s v) :
    ¬ (F.source [.mainNext p (.value w)]).Safe s := by
  obtain ⟨hc, hk⟩ := h
  obtain ⟨control, stack, m⟩ := s
  simp only at hc hk
  subst hc hk
  intro hsafe
  have h1 : (F.source [.mainNext p (.value w)]).step
      ⟨.value v, .procedureReturn F.bodyLabels :: [.mainNext p (.value w)], m⟩
      ⟨.value v, [.mainNext p (.value w)], m⟩ :=
    ⟨_, step_next (fun _ h => by cases h) (request_procedureReturn _ _ _ _)⟩
  have h2 : (F.source [.mainNext p (.value w)]).step ⟨.value v, [.mainNext p (.value w)], m⟩
      ⟨.halt (.error "startup allocation continuation"), [], m⟩ :=
    ⟨_, step_end (fun _ h => by cases h) (request_mainNext _ _ _ _)⟩
  refine hsafe.1 _ (.tail (.single h1) h2) ⟨_, rfl, fun v' h => ?_⟩
  cases h

end Silmaril.Proofs.Project.Shapes.C

end
