module

public import Silmaril.Raw.Wasm.Auto.Equiv.Step
public import Silmaril.Wasm.Logic.Total.Thms

/-!
# Soundness of symbolic execution

* `sexec_exec` (from `sstep_exec1`, `Silmaril.Raw.Wasm.Auto.Equiv.Step`): a symbolic run agrees with the straight-line
  interpreter `Silmaril.Wasm.Logic.Core.exec` on every concrete state that the symbolic
  state denotes (any environment, any frame, any values below the stack top);
* `wp_sexec` (from `wp_sstep`, ibid.): the forward rule in both readings of the every-run logic,
  from the instruction rules of `Silmaril.Wasm.Logic.Instr.Thms`;
* `wp_steps_inv`, `wp_sexec_inv`: the backward rule, from `exec_sound` and the
  step inversions `HWP.step_inv`/`TSafe.step_inv`;
* `wp_sexec_iff`: the every-run weakest precondition of a symbolically executed
  segment is that of its final symbolic state.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1 popInt popV localVal? exec_sound Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {ρ : Env}

/-- **A symbolic run is a run of `exec`.** -/
theorem sexec_exec {S S' : SState} {a : List Instr} (h : sexec S a = some S') (s : Store H)
    (f : Frame) (extra : List Val) :
    exec s (frameAt f ρ S) (stackAt ρ S ++ extra) a =
      some (s, frameAt f ρ S', stackAt ρ S' ++ extra) := by
  induction a generalizing S with
  | nil =>
    cases h
    rfl
  | cons i is ih =>
    simp only [sexec] at h
    split at h
    · rename_i S₁ h₁
      rw [Silmaril.Wasm.Logic.Core.exec_cons_of_some (sstep_exec1 h₁ s f extra)]
      exact ih h
    · cases h

/-! ## The every-run logic -/

theorem codeAt_eq (S : SState) (us : List Val) (a : List Instr) (rest : List Admin) :
    codeAt ρ S us a rest = vals (stackAt ρ S ++ us.reverse).reverse ++ expression a ++ rest := by
  simp [codeAt]

theorem wp_steps_inv {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {c c' : Config H} (hs : Steps P host c c') (h : Wp m P host c.store c.frame c.code Q) :
    Wp m P host c'.store c'.frame c'.code Q := by
  induction hs with
  | refl => exact h
  | tail _ hst ih =>
    cases m
    · exact HWP.step_inv ih hst
    · exact TSafe.step_inv ih hst

/-- **Backward rule**: the weakest precondition of a symbolically executed segment
gives that of its final state. -/
theorem wp_sexec_inv {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {S S' : SState} {a : List Instr} (h : sexec S a = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin)
    (hw : Wp m P host s (frameAt f ρ S) (codeAt ρ S us a rest) Q) :
    Wp m P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q := by
  have he := sexec_exec (ρ := ρ) h s f us.reverse
  have hs := exec_sound (P := P) (host := host) rest he
  rw [codeAt_eq] at hw
  have := wp_steps_inv hs hw
  simpa using this

/-- **Forward rule** for a symbolically executed segment. -/
theorem wp_sexec {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {S S' : SState} {a : List Instr} (h : sexec S a = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin)
    (hw : Wp m P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q) :
    Wp m P host s (frameAt f ρ S) (codeAt ρ S us a rest) Q := by
  induction a generalizing S with
  | nil =>
    cases h
    simpa [codeAt, expression] using hw
  | cons i is ih =>
    simp only [sexec] at h
    split at h
    · rename_i S₁ h₁
      have h₂ := ih h
      have := wp_sstep h₁ s f us (expression is ++ rest) (by simpa [codeAt] using h₂)
      simpa [codeAt, expression] using this
    · cases h

/-- **The weakest precondition of a symbolically executed segment** is that of its
final symbolic state, in both readings, for every profile, host relation, context and
postcondition. -/
theorem wp_sexec_iff {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {S S' : SState} {a : List Instr} (h : sexec S a = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin) :
    Wp m P host s (frameAt f ρ S) (codeAt ρ S us a rest) Q ↔
      Wp m P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q :=
  ⟨wp_sexec_inv h s f us rest, wp_sexec h s f us rest⟩

end Silmaril.Proofs.Wasm.Auto.Equiv