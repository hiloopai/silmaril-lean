module

public import Silmaril.Process.Mt.X86.Defs
import Silmaril.Proofs.Process.Mt.X86

/-!
# The multithreaded x86 process: the executable scheduler is sound

PROVED (standard axioms; proofs in `Silmaril.Proofs.Process.Mt.X86`):

* `exec1_sound`: a step of the executable scheduler (`exec1`) is a step of
  `MtProc X sc Prim.table (Base.none γ)`, and keeps `Cover` (the thread-id list is exact);
* **`run_sound`**: every run of a schedule (`run`) is a run of the process (`MtReach`).

So the `#guard` runs in `Silmaril.Proofs.Process.Mt.Examples` are runs of the model.
-/

@[expose] public section

namespace Silmaril.Process.Mt.X86

variable {γ : Type} {X : Env γ}

theorem exec1_sound {t : Nat} {tids tids' : List Nat} {C C' : XCfg γ} (hc : Cover tids C)
    (h : exec1 X tids C t = some (C', tids')) :
    MtProc X sc Prim.table (Base.none γ) C C' ∧ Cover tids' C' :=
  Silmaril.Proofs.Process.Mt.X86.exec1_sound hc h

theorem run_sound {ts : List Nat} {tids tids' : List Nat} {C C' : XCfg γ} (hc : Cover tids C)
    (h : run X ts (C, tids) = some (C', tids')) :
    MtReach (mtX X) sc Prim.table (Base.none γ) C C' ∧ Cover tids' C' :=
  Silmaril.Proofs.Process.Mt.X86.run_sound hc h

end Silmaril.Process.Mt.X86
