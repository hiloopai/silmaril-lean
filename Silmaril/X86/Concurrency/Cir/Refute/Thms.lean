module

public import Silmaril.X86.Concurrency.Cir.Refute.Defs
public import Silmaril.X86.Concurrency.Cir.Thms
public import Silmaril.X86.MemoryModel.Xl.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Refute

/-!
# Refuting bad outcomes by forced cycles: what is proved

PROVED with the standard axioms (proofs in
`Silmaril/Proofs/X86/Concurrency/Cir/Refute.lean`):

* `refuteCombo_sound`: a refuted choice of traces has no well-formed, XL-consistent candidate
  whose reads return the traces' bytes;
* `safe_of_check`: a passing `safeCheck t T good` makes `good` hold of every final state of
  `AxReach t T M` for `M` = XL, and so for TSO and SC (`safe_of_check_model`);
* `behavIn_safe`: the same for the behaviours of a CIR program over a domain;
* `witness_sound`: a passing `witnessCheck` gives an SC behaviour satisfying the condition, and
  so one under TSO and XL (`witness_model`).
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Refute

open Silmaril.X86.MemoryModel.Litmus (Test XTrace Cond Final AxReach Model axReach_mono)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

/-- A refuted choice of traces has no XL-consistent well-formed candidate. -/
theorem refuteCombo_sound {t : Test} {trs : List XTrace} (h : refuteCombo t trs = true)
    {x : Exec} (hx : x.evs = (Silmaril.X86.MemoryModel.Litmus.units trs).map Prod.fst)
    (hW : x.Wf = true)
    (hro : Silmaril.X86.MemoryModel.Litmus.ReadsOk t x
      ((Silmaril.X86.MemoryModel.Litmus.units trs).map Prod.snd)) (hX : x.Xl) : False :=
  Silmaril.Proofs.X86.Concurrency.Cir.Refute.refuteCombo_sound h hx hW hro hX

/-- **The safety check is sound under XL.** -/
theorem safe_of_check {t : Test} {T : List (List XTrace)} {good : Cond}
    (h : safeCheck t T good = true) {f : Final} (hf : AxReach t T Exec.Xl f) :
    good.eval f = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Refute.safe_of_check h hf

/-- Every model of the axiomatic enumerator is at least as strong as XL. -/
theorem model_le_xl (M : Model) : ∀ x : Exec, M.Holds x → x.Xl := by
  cases M with
  | sc => exact fun x h => x.xl_of_sc h
  | tso => exact fun x h => x.xl_of_tso h
  | xl => exact fun _ h => h

/-- **The safety check is sound under SC, TSO and XL.** -/
theorem safe_of_check_model {t : Test} {T : List (List XTrace)} {good : Cond}
    (h : safeCheck t T good = true) (M : Model) {f : Final} (hf : AxReach t T M.Holds f) :
    good.eval f = true :=
  safe_of_check h (axReach_mono (model_le_xl M) hf)

/-- **CIR programs**: a passing check over the program's traces makes `good` hold of every
behaviour over the domain, under SC, TSO and XL. -/
theorem behavIn_safe {P : Prog} {dom : List Nat} {good : Cond}
    (h : safeCheck P.memTest (P.traces dom) good = true) (M : Model) {f : Final}
    (hf : BehavIn P dom M.Holds f) : good.eval f = true :=
  safe_of_check_model h M hf

/-- **A passing witness check gives an SC behaviour** satisfying the condition. -/
theorem witness_sound {t : Test} {T : List (List XTrace)} {ks : List Nat}
    {rfA : List (Nat × Option Nat)} {coA : List ((Nat × Nat) × List Nat)} {w : Cond}
    (h : witnessCheck t T ks rfA coA w = true) : ∃ f, AxReach t T Exec.Sc f ∧ w.eval f = true :=
  Silmaril.Proofs.X86.Concurrency.Cir.Refute.witness_sound h

/-- SC implies every model. -/
theorem sc_le_model (M : Model) : ∀ x : Exec, x.Sc → M.Holds x := by
  cases M with
  | sc => exact fun _ h => h
  | tso => exact fun x h => x.tso_of_sc h
  | xl => exact fun x h => x.xl_of_sc h

/-- **A witness is a behaviour under SC, TSO and XL.** -/
theorem witness_model {t : Test} {T : List (List XTrace)} {ks : List Nat}
    {rfA : List (Nat × Option Nat)} {coA : List ((Nat × Nat) × List Nat)} {w : Cond}
    (h : witnessCheck t T ks rfA coA w = true) (M : Model) :
    ∃ f, AxReach t T M.Holds f ∧ w.eval f = true := by
  obtain ⟨f, hf, hw⟩ := witness_sound h
  exact ⟨f, axReach_mono (sc_le_model M) hf, hw⟩

/-- **An automatic witness is a behaviour under SC, TSO and XL.** -/
theorem witnessAuto_model {t : Test} {T : List (List XTrace)} {ks : List Nat} {w : Cond}
    (h : witnessAuto t T ks w = true) (M : Model) :
    ∃ f, AxReach t T M.Holds f ∧ w.eval f = true := by
  unfold witnessAuto at h
  split at h
  · exact witness_model h M
  · simp at h

end Silmaril.X86.Concurrency.Cir.Refute
