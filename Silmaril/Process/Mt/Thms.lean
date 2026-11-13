module

public import Silmaril.Process.Mt.Defs
import Silmaril.Proofs.Process.Mt.Solo

/-!
# The multithreaded process model: conservativity

PROVED (standard axioms; proofs in `Silmaril.Proofs.Process.Mt.Solo`): the single-threaded
process (`SoloStep`) is the one-thread case of `MtStep` under sequential consistency.

* `solo_step`: **every single-threaded step is a one-thread step**, with no hypothesis;
* `step_solo`: from a state that requests no `clone` and no `futex` (`NoThreadSys`), every
  one-thread step is a single-threaded step;
* `fault_iff`: the two fault predicates agree;
* `reach_solo`, `solo_reach`: the same for runs;
* **`solo_must`**: a demonic result (`SMust`: every run avoids faults, terminates and reaches
  `Q`) of the single-threaded process holds of the one-thread process, when no reachable
  state requests `clone` or `futex`. So single-threaded results transfer unchanged.
-/

@[expose] public section

namespace Silmaril.Process.Mt

variable {γ : Type} {U : UIsa γ} {P : PrimTable γ} {base : Base γ} {tid : Nat}

theorem solo_step {x x' : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C)
    (h : SoloStep U P base tid x x') : ∃ C', MtStep U sc P base C C' ∧ SoloRel tid x' C' :=
  Silmaril.Proofs.Process.Mt.Solo.solo_step hR h

theorem step_solo {x : SoloCfg U.St γ} {C C' : MtCfg U.St γ sc.S} (hR : SoloRel tid x C)
    (hn : NoThreadSys U tid x) (h : MtStep U sc P base C C') :
    ∃ x', SoloStep U P base tid x x' ∧ SoloRel tid x' C' :=
  Silmaril.Proofs.Process.Mt.Solo.step_solo hR hn h

theorem fault_iff {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C) :
    MtFault U sc P C ↔ SoloFault U P tid x :=
  Silmaril.Proofs.Process.Mt.Solo.fault_iff hR

theorem reach_solo {x x' : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S} (hR : SoloRel tid x C)
    (h : Relation.ReflTransGen (SoloStep U P base tid) x x') :
    ∃ C', MtReach U sc P base C C' ∧ SoloRel tid x' C' :=
  Silmaril.Proofs.Process.Mt.Solo.reach_solo hR h

theorem solo_reach {x : SoloCfg U.St γ} {C C' : MtCfg U.St γ sc.S} (hR : SoloRel tid x C)
    (hn : ∀ y, Relation.ReflTransGen (SoloStep U P base tid) x y → NoThreadSys U tid y)
    (h : MtReach U sc P base C C') :
    ∃ x', Relation.ReflTransGen (SoloStep U P base tid) x x' ∧ SoloRel tid x' C' :=
  Silmaril.Proofs.Process.Mt.Solo.solo_reach hR hn h

/-- **Single-threaded results transfer.** -/
theorem solo_must {Q : SoloCfg U.St γ → Prop} {x : SoloCfg U.St γ} {C : MtCfg U.St γ sc.S}
    (h : SMust (SoloStep U P base tid) (SoloFault U P tid) Q x)
    (hn : ∀ y, Relation.ReflTransGen (SoloStep U P base tid) x y → NoThreadSys U tid y)
    (hR : SoloRel tid x C) :
    SMust (MtStep U sc P base) (MtFault U sc P) (fun C => ∃ y, SoloRel tid y C ∧ Q y) C :=
  Silmaril.Proofs.Process.Mt.Solo.solo_must_aux h hn C hR

/-- The initial one-thread process is related to its single-threaded process. -/
theorem soloRel_init {s : U.St} {m : Memory} {g : γ} :
    SoloRel tid ⟨s, m, {}, g, none⟩ (MtCfg.init (S := sc.S) tid s m g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun t h => by simp [MtCfg.init, h], ⟨{ st := .run s }, by simp [MtCfg.init], .inl rfl⟩⟩

end Silmaril.Process.Mt
