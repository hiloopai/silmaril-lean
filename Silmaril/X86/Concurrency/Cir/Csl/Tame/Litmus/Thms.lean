module

public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Litmus.Defs
public import Silmaril.X86.Concurrency.Cir.Csl.Tame.Thms
public import Silmaril.X86.Concurrency.Cir.Robust.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Csl.TameLitmus

/-!
# Message passing through a release store on XL: why tameness is needed

PROVED (standard axioms only):

* `mp_nt_xl_allowed`: with an `nt` data store, the weak outcome (flag seen, data not) is
  reached on the CIR-native XL machine (an explicit eight-step run).
* `mp_nt_tso_forbidden`: the same test never ends in the weak outcome on TSO (the explorer,
  kernel `decide`).
* `mp_wb_forbidden`: with a write-back data store the test is tame (`mp_wb_tame`), and the weak
  outcome is forbidden on **every** buffered model (TSO's check, through
  `Csl.Tame.reach_tso_of_wb`).
* `mp_nt_untame` and `wb_needed`: the `nt` test fails the syntactic check, and for it XL has a
  final state TSO does not; so `Csl.Tame.reach_tso_of_wb` (and with it the release rule on XL)
  cannot drop its side condition.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Csl.Tame.Litmus

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Robust

/-- **Allowed on XL**: the weak outcome of message passing with an `nt` data store. -/
theorem mp_nt_xl_allowed : ∃ C : OCfg, OReach .xl 2 (mp .nt).cfg.toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ weakOut (C.ts 1).2 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.TameLitmus.nt_xl_run

/-- **Forbidden on TSO**, even with the `nt` data store. -/
theorem mp_nt_tso_forbidden {C : OCfg} (hr : OReach .tso 2 (mp .nt).cfg.toO C)
    (hd : C.Drained) (hf : ∀ t < 2, (C.ts t).1 = .skip) : ¬ weakOut (C.ts 1).2 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.TameLitmus.nt_tso_forbidden hr hd hf

/-- The write-back test passes the tameness check. -/
theorem mp_wb_tame : (mp .wb).cfg.WbStores 2 := by
  intro t ht
  rcases t with _ | _ | t
  · rfl
  · rfl
  · omega

/-- The `nt` test fails it. -/
theorem mp_nt_untame : ¬ (mp .nt).cfg.WbStores 2 := fun h => by
  have h0 : (writer .nt).wbStores = true := h 0 (by decide)
  simp [writer, Stmt.wbStores] at h0

/-- **Forbidden on every buffered model** with a write-back data store. -/
theorem mp_wb_forbidden {M : OModel} {C : OCfg} (hr : OReach M 2 (mp .wb).cfg.toO C)
    (hd : C.Drained) (hf : ∀ t < 2, (C.ts t).1 = .skip) : ¬ weakOut (C.ts 1).2 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Csl.TameLitmus.wb_tso_forbidden
    (reach_tso_of_wb mp_wb_tame hr) hd hf

/-- **The side condition is needed**: for the untame `nt` test, XL reaches a finished, drained
configuration that TSO does not. -/
theorem wb_needed : ∃ C : OCfg, OReach .xl 2 (mp .nt).cfg.toO C ∧ C.Drained ∧
    (∀ t < 2, (C.ts t).1 = .skip) ∧ ¬ OReach .tso 2 (mp .nt).cfg.toO C := by
  obtain ⟨C, hr, hd, hf, hw⟩ := mp_nt_xl_allowed
  exact ⟨C, hr, hd, hf, fun ht => mp_nt_tso_forbidden ht hd hf hw⟩

end Silmaril.X86.Concurrency.Cir.Csl.Tame.Litmus
