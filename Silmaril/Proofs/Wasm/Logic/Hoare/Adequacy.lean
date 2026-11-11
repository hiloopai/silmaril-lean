module

public import Silmaril.Proofs.Wasm.Logic.Hoare.Call

/-!
# The every-run logic: adequacy

* `HWP.sound` (**partial correctness and safety**): every configuration reachable
  from a code with an every-run weakest precondition can step, or has exited with
  an outcome satisfying the postcondition. In particular a run that ends in values,
  a trap or an uncaught exception satisfies the postcondition (`HWP.sound_vals`,
  `HWP.sound_trap`, `HWP.sound_throw`).
* `TSafe.not_diverges` (**total correctness**): a configuration with a total
  weakest precondition has no infinite run; `TSafe.safe` turns it into partial
  correctness.
* `FSpecValid.invoke_vals`, `FSpecValid.invoke_trap`: a valid specification holds
  for every run of the embedder's `$invoke`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Partial correctness -/

/-- Safe, or exited with the postcondition (an exit may still bubble). -/
def SafeOrExit (P : Profile) (host : HostSemantics H) (Q : Post H) (n : Nat) (c : Config H) : Prop :=
  Safe P host Q n c ∨ ∃ o, Exits o c.code ∧ Q c.store c.frame o

theorem SafeOrExit.step {Q : Post H} {n : Nat} {c c' : Config H}
    (h : SafeOrExit P host Q (n + 1) c) (hst : Step P host c c') : SafeOrExit P host Q n c' := by
  rcases h with h | ⟨o, he, hq⟩
  · exact .inl (h.step_inv hst)
  · rcases c with ⟨s, f, code⟩
    rcases c' with ⟨s', f', code'⟩
    obtain ⟨rfl, rfl, he', -⟩ := he.step hst
    exact .inr ⟨o, he', hq⟩

theorem SafeOrExit.steps {Q : Post H} {c c' : Config H} (h : ∀ n, Safe P host Q n c)
    (hs : Steps P host c c') : ∀ n, SafeOrExit P host Q n c' := by
  induction hs with
  | refl => exact fun n => .inl (h n)
  | tail _ hst ih => exact fun n => (ih (n + 1)).step hst

/-- **Adequacy (partial correctness and safety).** -/
theorem HWP.sound {s : Store H} {f : Frame} {code : List Admin} {Q : Post H} {c' : Config H}
    (h : HWP P host s f code Q) (hs : Steps P host ⟨s, f, code⟩ c') :
    (∃ c'', Step P host c' c'') ∨ ∃ o, Exits o c'.code ∧ Q c'.store c'.frame o := by
  rcases SafeOrExit.steps h hs 1 with (⟨o, he, hq⟩ | ⟨hp, -⟩) | h'
  · exact .inr ⟨o, he, hq⟩
  · exact .inl hp
  · exact .inr h'

/-- A run that ends in values satisfies the normal postcondition. -/
theorem HWP.sound_vals {s s' : Store H} {f f' : Frame} {code : List Admin} {Q : Post H}
    {vs : List Val} (h : HWP P host s f code Q) (hs : Steps P host ⟨s, f, code⟩ ⟨s', f', vals vs⟩) :
    Q s' f' (.normal vs) := by
  rcases h.sound hs with ⟨c'', hc⟩ | ⟨o, he, hq⟩
  · exact (not_step_vals hc).elim
  · exact exits_vals_inv he ▸ hq

/-- A run that ends in a trap satisfies the trap postcondition. -/
theorem HWP.sound_trap {s s' : Store H} {f f' : Frame} {code : List Admin} {Q : Post H}
    (h : HWP P host s f code Q) (hs : Steps P host ⟨s, f, code⟩ ⟨s', f', [.trap]⟩) :
    Q s' f' .trap := by
  rcases h.sound hs with ⟨c'', hc⟩ | ⟨o, he, hq⟩
  · exact (not_step_trap hc).elim
  · exact exits_trap_inv (vs := []) (rest := []) he ▸ hq

/-- A run that ends in an uncaught exception satisfies the throw postcondition. -/
theorem HWP.sound_throw {s s' : Store H} {f f' : Frame} {code : List Admin} {Q : Post H} {a : Nat}
    (h : HWP P host s f code Q) (hs : Steps P host ⟨s, f, code⟩ ⟨s', f', throwing a⟩) :
    Q s' f' (.throw a) := by
  rcases h.sound hs with ⟨c'', hc⟩ | ⟨o, he, hq⟩
  · exact (not_step_throwing hc).elim
  · exact exits_throw_inv (vs := []) (rest := []) (by simpa using he) ▸ hq

/-! ## Total correctness -/

/-- An exit has no infinite run: bubbling shortens the code. -/
theorem Exits.not_diverges : ∀ (m : Nat) {o : Outcome} {c : Config H},
    Sim.codeSize c.code < m → Exits o c.code → ¬ Diverges P host c
  | 0, _, _, hm, _, _ => absurd hm (by omega)
  | m + 1, o, ⟨s, f, code⟩, hm, he, hd => by
    obtain ⟨⟨s', f', code'⟩, hst, hd'⟩ := Silmaril.InfiniteTrace.unfold hd
    obtain ⟨-, -, he', hr⟩ := he.step hst
    have hm' : Sim.codeSize code < m + 1 := hm
    exact Exits.not_diverges m (show Sim.codeSize code' < m by omega) he' hd'

/-- **Total correctness**: no infinite run. -/
theorem TSafe.not_diverges {Q : Post H} {c : Config H} (h : TSafe P host Q c) :
    ¬ Diverges P host c := by
  induction h with
  | exit o he _ => exact Exits.not_diverges _ (Nat.lt_succ_self _) he
  | step _ _ ih =>
    intro hd
    obtain ⟨c', hst, hd'⟩ := Silmaril.InfiniteTrace.unfold hd
    exact ih c' hst hd'

/-- Total correctness implies partial correctness. -/
theorem TSafe.safe {Q : Post H} {c : Config H} (h : TSafe P host Q c) : ∀ n, Safe P host Q n c := by
  induction h with
  | exit o he hq => exact fun _ => Safe.of_exits he hq
  | step hp _ ih =>
    intro n
    cases n with
    | zero => trivial
    | succ n => exact Safe.of_step hp fun c' hc => ih c' hc n

theorem TWP.hwp {s : Store H} {f : Frame} {code : List Admin} {Q : Post H}
    (h : TWP P host s f code Q) : HWP P host s f code Q :=
  TSafe.safe h

/-! ## Function specifications and `$invoke` -/

theorem invoke_code (s : Store H) (a : Nat) (args : List Val) :
    invoke s a args = ⟨s, {}, vals [] ++ vals args ++
      [.ref (.func a), .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]⟩ := rfl

/-- A valid specification gives the every-run weakest precondition of `$invoke`. -/
theorem FSpecValid.hwp_invoke {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    (h : FSpecValid P host a S) (hpre : S.pre s args) :
    HWP P host s {} (invoke s a args).code (callPost {} [] (S.post s args)) := by
  intro n
  rw [invoke_code]
  exact h n s args hpre {} [] _ trivial

/-- **Adequacy of function specifications.** Every run of `$invoke` that returns
values satisfies the postcondition. -/
theorem FSpecValid.invoke_vals {a : Nat} {S : FSpec H} {s s' : Store H} {f' : Frame}
    {args res : List Val} (h : FSpecValid P host a S) (hpre : S.pre s args)
    (hs : Steps P host (invoke s a args) ⟨s', f', vals res⟩) : S.post s args s' (.normal res) := by
  obtain ⟨-, h'⟩ := (h.hwp_invoke hpre).sound_vals (by rw [invoke_code] at hs ⊢; exact hs)
  rcases h' with ⟨res', he, hp⟩ | ⟨he, -⟩ | ⟨a, he, -⟩
  · obtain rfl : res = res' := by simpa using he
    exact hp
  · exact Outcome.noConfusion he
  · exact Outcome.noConfusion he

/-- Every run of `$invoke` that traps satisfies the trap postcondition. -/
theorem FSpecValid.invoke_trap {a : Nat} {S : FSpec H} {s s' : Store H} {f' : Frame}
    {args : List Val} (h : FSpecValid P host a S) (hpre : S.pre s args)
    (hs : Steps P host (invoke s a args) ⟨s', f', [.trap]⟩) : S.post s args s' .trap := by
  obtain ⟨-, h'⟩ := (h.hwp_invoke hpre).sound_trap (by rw [invoke_code] at hs ⊢; exact hs)
  rcases h' with ⟨res', he, -⟩ | ⟨-, hp⟩ | ⟨a, he, -⟩
  · exact Outcome.noConfusion he
  · exact hp
  · exact Outcome.noConfusion he

/-- Every reachable configuration of `$invoke` can step or has exited. -/
theorem FSpecValid.invoke_safe {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    {c' : Config H} (h : FSpecValid P host a S) (hpre : S.pre s args)
    (hs : Steps P host (invoke s a args) c') :
    (∃ c'', Step P host c' c'') ∨ ∃ o, Exits o c'.code ∧ callPost {} [] (S.post s args) c'.store c'.frame o :=
  (h.hwp_invoke hpre).sound (by rw [invoke_code] at hs ⊢; exact hs)

end Silmaril.Wasm.Logic.Hoare
