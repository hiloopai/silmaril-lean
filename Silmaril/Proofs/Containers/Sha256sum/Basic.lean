module

public import Silmaril.Containers.Sha256sum.Defs

public section
namespace Silmaril.Proofs.Containers.Sha256sum
open Silmaril.Containers.Sha256sum Silmaril.Process.LPS

theorem reports_noUB (b : Behavior) (errorFree : ErrorFree b) (modeled : ¬ b.unmodeled)
    (r : Report) (occurs : r.Occurs b) : r.observe.NoUB := by
  cases r with
  | ended _ _ => trivial
  | fault => exact (errorFree occurs).elim
  | unmodeled => exact (modeled occurs).elim

end Silmaril.Proofs.Containers.Sha256sum
