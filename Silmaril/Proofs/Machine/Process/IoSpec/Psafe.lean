module

public import Silmaril.Machine.Process.IoSpec.Defs
public import Silmaril.Machine.Process.LpsBridge.Rel.Thms

/-!
# Proofs: `IoSafeN` is sound for LPS (`ioSafe_psafe`)

Names in `Silmaril.Proofs.Machine.Process.IoSpec`.

* `trapRequestF_eq`: the request of an aligned trap is `reqOf segs (trapped …)`.
* `ioSafeN_mono`, `next_mono`, `ioSafe_next`: index monotonicity.
* `Good`: the invariant of the simulation, over LPS configurations of `flagMachine oracle
  nstep`: an aligned configuration whose open state is `IoSafeN` for every index; a trap
  configuration whose every answer continues `IoSafeN`; a process-safe configuration (a `Q`
  exit); a halted configuration with an allowed empty remainder.
* `good_nil`, `good_noerr`, `good_step`, `good_star`: the invariant holds of every reachable
  configuration (with the remaining trace), allows the empty remainder and has no error step.
* **`ioSafe_psafe`**: if `nstep` agrees with `c` and `E` is sound, an aligned configuration
  whose open state is `IoSafeN c E Q n` for every `n` (with an abstraction of its model) is
  process-safe, given process safety at the `Q` exits.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.IoSpec

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Proofs.Machine.Process.LpsBridge

variable {oracle : Oracle} {nstep : NStep} {c : MState → Option MState} {segs : List Segment}
  {refused : RefusalFilter} {E : SysEnv} {Q : MState → E.Model → (List Event → Prop) → Prop}

theorem trapRequestF_eq (cfg : Config (flagMachine oracle nstep)) (m : MState) :
    trapRequestF segs cfg m = reqOf segs (trapped ⟨m, none⟩ (oracle cfg.ms.counter)) :=
  rfl

theorem next_mono {Model : Type} {k k' : MState → Model → (List Event → Prop) → Prop}
    (hk : ∀ m e A, k m e A → k' m e A) {A : List Event → Prop} {o : IoOut Model} :
    o.Next k A → o.Next k' A := by
  cases o with
  | resume m' e' evs => exact hk _ _ _
  | halt evs => exact id

theorem ioSafeN_mono : ∀ {n k : Nat} {m : MState} {e : E.Model} {A : List Event → Prop},
    k ≤ n → IoSafeN c E Q n m e A → IoSafeN c E Q k m e A
  | _, 0, _, _, _, _, _ => trivial
  | 0, _ + 1, _, _, _, hk, _ => absurd hk (by omega)
  | n + 1, k + 1, m, e, A, hk, h => by
    obtain ⟨hA, hq | ⟨m', hs, hn⟩ | ⟨ht, hall⟩⟩ := h
    · exact ⟨hA, .inl hq⟩
    · exact ⟨hA, .inr (.inl ⟨m', hs, ioSafeN_mono (by omega) hn⟩)⟩
    · refine ⟨hA, .inr (.inr ⟨ht, fun ch => ⟨(hall ch).1, fun o ho => ?_⟩⟩)⟩
      exact next_mono (fun _ _ _ => ioSafeN_mono (by omega)) ((hall ch).2 o ho)

/-- **The simulation invariant.** -/
def Good (c : MState → Option MState) (E : SysEnv) (Q : MState → E.Model → (List Event → Prop) → Prop)
    (segs : List Segment) (refused : RefusalFilter) (A : List Event → Prop)
    (c₁ : Config (flagMachine oracle nstep)) : Prop :=
  (∃ m e, AlignedF c₁ m ∧ E.Abs e c₁.model ∧ ∀ n, IoSafeN c E Q n m e A) ∨
  (∃ (cfg : Config (flagMachine oracle nstep)) (m : MState) (e : E.Model), c₁ = trapCfgF cfg m ∧ AlignedF cfg m ∧
    AtSyscall m ∧ E.Abs e cfg.model ∧ A [] ∧
    E.Handles (trapped ⟨m, none⟩ (oracle cfg.ms.counter)) e ∧
    ∀ o, E.arm (trapped ⟨m, none⟩ (oracle cfg.ms.counter)) e o →
      o.Next (fun m' e' A' => ∀ n, IoSafeN c E Q n m' e' A') A) ∨
  PSafeF segs refused A c₁ ∨
  (c₁.model.halted ≠ none ∧ A [])

variable (hM : Agrees nstep c) (hS : Sound E segs refused)
  (hQ : ∀ (c' : Config (flagMachine oracle nstep)) m' e' (A' : List Event → Prop),
    AlignedF c' m' → E.Abs e' c'.model → Q m' e' A' → PSafeF segs refused A' c')

include hM hQ in
/-- The aligned case, unfolded: a `Q` exit, an agreeing step, or a handled trap. -/
theorem aligned_cases {A : List Event → Prop} {c₁ : Config (flagMachine oracle nstep)}
    {m : MState} {e : E.Model} (al : AlignedF c₁ m) (he : E.Abs e c₁.model)
    (h : ∀ n, IoSafeN c E Q n m e A) :
    PSafeF segs refused A c₁ ∨
    (∃ m', c m = some m' ∧ ∀ n, IoSafeN c E Q n m' e A) ∨
    (AtSyscall m ∧ A [] ∧ ∀ ch : X86FlagChoices.Choice, E.Handles (trapped ⟨m, none⟩ ch) e ∧
      ∀ o, E.arm (trapped ⟨m, none⟩ ch) e o →
        o.Next (fun m' e' A' => ∀ n, IoSafeN c E Q n m' e' A') A) := by
  by_cases hq : Q m e A
  · exact .inl (hQ c₁ m e A al he hq)
  · cases hcm : c m with
    | some m' =>
      refine .inr (.inl ⟨m', rfl, fun n => ?_⟩)
      obtain ⟨-, hq' | ⟨m'', hs, hn⟩ | ⟨ht, -⟩⟩ := h (n + 1)
      · exact absurd hq' hq
      · rw [hcm] at hs; cases hs; exact hn
      · rw [hM.stuck ht] at hcm; cases hcm
    | none =>
      obtain ⟨hA, hq' | ⟨m'', hs, -⟩ | ⟨ht, -⟩⟩ := h 1
      · exact absurd hq' hq
      · rw [hcm] at hs; cases hs
      · refine .inr (.inr ⟨ht, hA, fun ch => ⟨?_, fun o ho => ?_⟩⟩)
        · obtain ⟨-, hq' | ⟨m'', hs, -⟩ | ⟨-, hall⟩⟩ := h 1
          · exact absurd hq' hq
          · rw [hcm] at hs; cases hs
          · exact (hall ch).1
        · cases o with
          | resume m' e' evs =>
            intro n
            obtain ⟨-, hq' | ⟨m'', hs, -⟩ | ⟨-, hall⟩⟩ := h (n + 1)
            · exact absurd hq' hq
            · rw [hcm] at hs; cases hs
            · exact (hall ch).2 _ ho
          | halt evs =>
            obtain ⟨-, hq' | ⟨m'', hs, -⟩ | ⟨-, hall⟩⟩ := h 1
            · exact absurd hq' hq
            · rw [hcm] at hs; cases hs
            · exact (hall ch).2 _ ho

theorem good_nil {A : List Event → Prop} {c₁ : Config (flagMachine oracle nstep)}
    (g : Good c E Q segs refused A c₁) : A [] := by
  rcases g with ⟨m, e, al, he, h⟩ | ⟨-, -, -, -, -, -, -, hA, -, -⟩ | hp | ⟨-, hA⟩
  · exact (h 1).1
  · exact hA
  · exact hp.1 [] c₁ (.refl _)
  · exact hA

include hM hS hQ in
theorem good_noerr {A : List Event → Prop} {c₁ : Config (flagMachine oracle nstep)}
    (g : Good c E Q segs refused A c₁) {evs : List Event} :
    ¬ SStep segs spec refused c₁ evs .error := by
  rcases g with ⟨m, e, al, he, h⟩ | ⟨cfg, m, e, rfl, al, ht, he, hA, hH, -⟩ | hp | ⟨hh, -⟩
  · rcases aligned_cases hM hQ al he h with hp | ⟨m', hs, -⟩ | ⟨ht, -, -⟩
    · exact hp.2 [] c₁ evs (.refl _)
    · intro herr
      obtain ⟨-, uniq⟩ := sstepF_step (segs := segs) (refused := refused) hM al hs
      cases (uniq _ _ herr).2
    · intro herr
      obtain ⟨-, uniq⟩ := sstepF_trap (segs := segs) (refused := refused) hM al ht
      cases (uniq _ _ herr).2
  · have svc : (flagMachine oracle nstep).svcPending (trapCfgF cfg m).ms =
        some (m.core.read .rax) := rfl
    have S := hS m (oracle cfg.ms.counter) cfg.model e he al.alive al.lazy ht hH
    intro herr
    cases herr with
    | instrFault _ p => rw [svc] at p; cases p
    | instrUnmodeled _ p => rw [svc] at p; cases p
    | @syscallMaterializationFault _ _ x8 eff model' evs _ p hs hr hh hmat =>
      rw [svc] at p; cases p
      obtain ⟨-, hres, -⟩ := S.2 _ _ _ hs
      rw [X86Launch.materializeModelAccesses_no_lazy _ _ (hres hh).1] at hmat
      cases hmat
    | syscallUnmodeled _ p hs => rw [svc] at p; cases p; exact S.1 hs
  · exact hp.2 [] c₁ evs (.refl _)
  · exact haltedF_no_step hh

include hM hS hQ in
theorem good_step {A : List Event → Prop} {c₁ c₂ : Config (flagMachine oracle nstep)}
    {evs : List Event} (g : Good c E Q segs refused A c₁)
    (s : SStep segs spec refused c₁ evs (.next c₂)) :
    Good c E Q segs refused (fun tr => A (evs ++ tr)) c₂ := by
  rcases g with ⟨m, e, al, he, h⟩ | ⟨cfg, m, e, rfl, al, ht, he, hA, hH, hk⟩ | hp | ⟨hh, -⟩
  · rcases aligned_cases hM hQ al he h with hp | ⟨m', hs, hn⟩ | ⟨ht, hA, hall⟩
    · refine .inr (.inr (.inl ⟨fun tr c' hstar => hp.1 _ _ (.step s hstar),
        fun tr c' evs' hstar => hp.2 _ _ _ (.step s hstar)⟩))
    · obtain ⟨-, uniq⟩ := sstepF_step (segs := segs) (refused := refused) hM al hs
      obtain ⟨rfl, e'⟩ := uniq _ _ s
      cases e'
      refine .inl ⟨m', e, ⟨rfl, al.alive, al.lazy⟩, he, fun n => ?_⟩
      simpa only [List.nil_append] using hn n
    · obtain ⟨-, uniq⟩ := sstepF_trap (segs := segs) (refused := refused) hM al ht
      obtain ⟨rfl, e'⟩ := uniq _ _ s
      cases e'
      refine .inr (.inl ⟨c₁, m, e, rfl, al, ht, he, by simpa using hA,
        (hall _).1, fun o ho => ?_⟩)
      simpa only [List.nil_append] using (hall _).2 o ho
  · have svc : (flagMachine oracle nstep).svcPending (trapCfgF cfg m).ms =
        some (m.core.read .rax) := rfl
    have S := hS m (oracle cfg.ms.counter) cfg.model e he al.alive al.lazy ht hH
    cases s with
    | instr _ p => rw [svc] at p; cases p
    | @syscall _ _ x8 eff model' model'' evs _ p hs hr hh hmat =>
      rw [svc] at p; cases p
      obtain ⟨-, hres, -⟩ := S.2 _ _ _ hs
      obtain ⟨lazy, cont⟩ := hres hh
      rw [X86Launch.materializeModelAccesses_no_lazy _ _ lazy] at hmat
      cases hmat
      obtain ⟨e', he', ho⟩ := cont hr
      exact .inl ⟨_, e', ⟨rfl, hh, lazy⟩, he', hk _ ho⟩
    | @exit _ _ x8 eff model' evs code _ p hs hh hkill =>
      rw [svc] at p; cases p
      have := hk _ ((S.2 _ _ _ hs).2.2 code hh)
      exact .inr (.inr (.inr ⟨by simp [hh], by simpa [IoOut.Next] using this⟩))
    | @killed _ _ x8 eff model' evs sig _ p hs hkill =>
      rw [svc] at p; cases p
      rw [(S.2 _ _ _ hs).1] at hkill; cases hkill
  · exact .inr (.inr (.inl ⟨fun tr c' hstar => hp.1 _ _ (.step s hstar),
      fun tr c' evs' hstar => hp.2 _ _ _ (.step s hstar)⟩))
  · exact absurd s (haltedF_no_step hh)

include hM hS hQ in
theorem good_star {A : List Event → Prop} {c₁ c₃ : Config (flagMachine oracle nstep)}
    {tr : List Event} (hstar : Star segs spec refused c₁ tr c₃)
    (g : Good c E Q segs refused A c₁) :
    Good c E Q segs refused (fun t => A (tr ++ t)) c₃ := by
  induction hstar generalizing A with
  | refl => simpa using g
  | step s _ ih =>
    have := ih (good_step hM hS hQ g s)
    simpa only [List.append_assoc] using this

include hM hS hQ in
/-- **`IoSafeN` is sound for LPS.** -/
theorem ioSafe_psafe {A : List Event → Prop} {cfg : Config (flagMachine oracle nstep)}
    {m : MState} {e : E.Model} (al : AlignedF cfg m) (he : E.Abs e cfg.model)
    (h : ∀ n, IoSafeN c E Q n m e A) : PSafeF segs refused A cfg := by
  have g : Good c E Q segs refused A cfg := .inl ⟨m, e, al, he, h⟩
  constructor
  · intro tr c' hstar
    simpa using good_nil (good_star hM hS hQ hstar g)
  · intro tr c' evs hstar
    exact good_noerr hM hS hQ (good_star hM hS hQ hstar g)

end Silmaril.Proofs.Machine.Process.IoSpec
