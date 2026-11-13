module

public import Silmaril.X86.Concurrency.Cir.Proc.Lps.Defs
import Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps

/-!
# Process-level threads and LPS: theorems

PROVED, standard axioms (proofs in
`Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps`). Assumed (model, not proved): silmaril's LPS
port and its native x86-64 table.

* **`lps_extension`**: on the numbers the thread layer owns, LPS agrees with the
  single-threaded view (`gettid`, `set_tid_address` with a pinned id; `exit`, `exit_group`) or
  has the `unmodeled` outcome (`clone`, `futex`, `clone3`);
* `tidArmFresh_gettid`, `tidArmFresh_setTid`: the first observation picks and pins an id;
* `halt_code`: LPS's halt status `w &&& 255` is the thread layer's `w.toNat % 256`.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.Proc.Lps

/-- **The thread layer extends LPS.** -/
theorem lps_extension : TidArm nrGettid ∧ TidArm nrSetTid ∧ ExitArm ∧ PendingArms :=
  ⟨Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps.tidArm_gettid,
    Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps.tidArm_setTid,
    Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps.exitArm,
    Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps.pendingArms⟩

theorem tidArmFresh_gettid : TidArmFresh nrGettid :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps.tidArmFresh_gettid

theorem tidArmFresh_setTid : TidArmFresh nrSetTid :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps.tidArmFresh_setTid

theorem halt_code (w : Word) : (w &&& 255).toNat = w.toNat % 256 :=
  Silmaril.Proofs.X86.Concurrency.Cir.Proc.Lps.halt_code w

end Silmaril.X86.Concurrency.Cir.Proc.Lps
