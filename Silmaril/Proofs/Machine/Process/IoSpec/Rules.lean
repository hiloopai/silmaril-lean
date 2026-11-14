module

public import Silmaril.Proofs.Machine.Process.IoSpec.Arms

/-!
# Proofs: proof rules for `IoSafeN`

Names in `Silmaril.Proofs.Machine.Process.IoSpec`.

* **`ioSafe_of_safeN`** (syscall-free code lifts): a safe run of the pure machine
  (`∀ n, SafeN c R n m`, the safety notion of the `FnSpec` link logic) to states `R` that are
  `IoSafe` is `IoSafe`; no event is emitted and the environment is unchanged on the way.
* `ioSafe_of_q`: a `Q` exit is `IoSafe`.
* **`ioSafe_trap`**: a handled trap whose every answer continues `IoSafe` is `IoSafe`.
* **`ioSafe_exit`**: on `lpsEnv`, an `exit`/`exit_group` trap is `IoSafe` if the empty trace
  and `[exitEv (rdi &&& 255) fs]` are allowed.
* `ioSafe_psafeLps`: `ioSafe_psafe` specialised to `lpsEnv` (`sound_lpsEnv`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Process.IoSpec

open Silmaril.Process.LPS
open Silmaril.Process.LPS.Machines
open Silmaril.X86 (MState)
open Silmaril.Machine.X86.Safe (SafeN)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec
open Silmaril.Proofs.Machine.Process.LpsBridge

variable {c : MState → Option MState} {E : SysEnv}
  {Q : MState → E.Model → (List Event → Prop) → Prop}

/-- A `Q` exit is `IoSafe` (given the empty remainder). -/
theorem ioSafe_of_q {m : MState} {e : E.Model} {A : List Event → Prop} (hA : A [])
    (hq : Q m e A) : ∀ n, IoSafeN c E Q n m e A
  | 0 => trivial
  | _ + 1 => ⟨hA, .inl hq⟩

/-- **Syscall-free code lifts.** -/
theorem ioSafe_of_safeN {R : MState → Prop} {e : E.Model} {A : List Event → Prop} (hA : A [])
    (hR : ∀ m', R m' → ∀ n, IoSafeN c E Q n m' e A) :
    ∀ n {m : MState}, (∀ k, SafeN c R k m) → IoSafeN c E Q n m e A
  | 0, _, _ => trivial
  | n + 1, m, h => by
    by_cases hr : R m
    · exact hR m hr (n + 1)
    · obtain ⟨m', hs⟩ := safeN_step_of hr h
      exact ⟨hA, .inr (.inl ⟨m', hs, ioSafe_of_safeN hA hR n (safeN_succ_of hr hs h)⟩)⟩

/-- **The trap rule.** -/
theorem ioSafe_trap {m : MState} {e : E.Model} {A : List Event → Prop} (ht : AtSyscall m)
    (hA : A [])
    (h : ∀ ch : X86FlagChoices.Choice, E.Handles (trapped ⟨m, none⟩ ch) e ∧
      ∀ o, E.arm (trapped ⟨m, none⟩ ch) e o →
        o.Next (fun m' e' A' => ∀ n, IoSafeN c E Q n m' e' A') A) :
    ∀ n, IoSafeN c E Q n m e A
  | 0 => trivial
  | n + 1 => ⟨hA, .inr (.inr ⟨ht, fun ch => ⟨(h ch).1, fun o ho =>
      next_mono (fun _ _ _ hk => hk n) ((h ch).2 o ho)⟩⟩)⟩

/-- **The `exit` rule on `lpsEnv`.** -/
theorem ioSafe_exit {segs : List Segment}
    {Q : MState → (lpsEnv segs).Model → (List Event → Prop) → Prop} {m : MState}
    {e : (lpsEnv segs).Model} {A : List Event → Prop} (ht : AtSyscall m)
    (number : (m.core.read .rax).toNat = 60 ∨ (m.core.read .rax).toNat = 231)
    (hA : A []) (hE : A [.exitEv (m.core.read .rdi &&& 255) e.fs]) :
    ∀ n, IoSafeN c (lpsEnv segs) Q n m e A := by
  refine ioSafe_trap ht hA fun ch => ⟨⟨exitArm, by simp [lpsArms], number⟩, ?_⟩
  rintro o ⟨a, ha, hH, ho⟩
  simp only [lpsArms, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · cases ho
    exact hE
  · have h1 : (m.core.read .rax).toNat = 1 := hH.1
    omega
  · have h0 : (m.core.read .rax).toNat = 0 := hH.1
    omega

/-- `ioSafe_psafe` on `lpsEnv`. -/
theorem ioSafe_psafeLps {oracle : Oracle} {nstep : NStep} {segs : List Segment}
    {refused : RefusalFilter} {Q : MState → (lpsEnv segs).Model → (List Event → Prop) → Prop}
    (hM : Agrees nstep c)
    (hQ : ∀ (c' : Config (flagMachine oracle nstep)) m' (e' : (lpsEnv segs).Model)
      (A' : List Event → Prop), AlignedF c' m' → c'.model = e' → Q m' e' A' →
      PSafeF segs refused A' c')
    {A : List Event → Prop} {cfg : Config (flagMachine oracle nstep)} {m : MState}
    (al : AlignedF cfg m) (h : ∀ n, IoSafeN c (lpsEnv segs) Q n m cfg.model A) :
    PSafeF segs refused A cfg :=
  ioSafe_psafe hM sound_lpsEnv (fun c' m' e' A' al' he' hq => hQ c' m' e' A' al' he'.symm hq)
    al rfl h

end Silmaril.Proofs.Machine.Process.IoSpec
