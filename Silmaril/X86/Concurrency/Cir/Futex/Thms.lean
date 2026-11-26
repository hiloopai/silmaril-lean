module

public import Silmaril.X86.Concurrency.Cir.Futex.Defs
public import Silmaril.X86.Concurrency.Cir.Sync.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.Futex

/-!
# CIR futexes: what is proved

All statements are PROVED with the standard axioms; the proofs are in
`Silmaril/Proofs/X86/Concurrency/Cir/Futex.lean`.

* `Exec.fsw_sw`: a futex wake edge is a synchronisation edge (queue bytes lie above the
  control bytes), so `Exec.fswHb_sc`, `fswHb_ghb`, `fswHb_ghbXl`: every wake happens-before
  edge is a path of the model's own order (`ppo; rfe; ppo` for TSO, `lockXl; rfe; lockXl` for
  XL: the wake's and the dequeue's queue accesses are locked).
* `Exec.scF_iff`, `tsoF_iff`, `xlF_iff`: adding the wake edges changes no model. With
  `scF_le_tsoF`, `tsoF_le_xlF`, `scF_le_xlF`: **SC ⊑ TSO ⊑ XL with futex synchronisation**, and
  `behavIn_scF_iff` etc.: CIR behaviours under the synchronising models are the plain ones.
* `Exec.futex_dekker_xl` / `futex_dekker_tso`: **the futex handshake loses no wake-up.** If a
  store `s` is `po`-before a wake whose locked queue write `w` is coherence-before a waiter's
  enqueue `q`, and an `mfence` separates the enqueue from the check `l`, then the check does not
  read from before `s` (`fr l s` is impossible). This is the step that makes "set the flag, then
  wake" safe, for every program.
* `behavIn_bbehavIn`: allowing blocked threads only adds behaviours.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Axiomatic (Exec BRel)
open Silmaril.X86.MemoryModel.Litmus (Final)
open Relation

/-- A futex wake edge is a synchronisation edge. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.fsw_sw {x : Exec} {w r : Fin x.n}
    (h : x.fsw w r = true) : x.sw w r = true := Silmaril.Proofs.X86.Concurrency.Cir.Futex.fsw_sw h

/-- **SC**: a wake edge is a path of `po | com;sm`. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.fswHb_sc {x : Exec} {a b : Fin x.n}
    (h : x.fswHb a b = true) : TransGen x.scRel.Holds a b :=
  Exec.swHb_sc (Silmaril.Proofs.X86.Concurrency.Cir.Futex.fswHb_swHb h)

/-- **TSO**: a wake edge is a `ghb` path. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.fswHb_ghb {x : Exec} {a b : Fin x.n}
    (h : x.fswHb a b = true) : TransGen x.ghb.Holds a b :=
  Exec.swHb_ghb (Silmaril.Proofs.X86.Concurrency.Cir.Futex.fswHb_swHb h)

/-- **XL**: a wake edge is a `ghbXl` path. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.fswHb_ghbXl {x : Exec} {a b : Fin x.n}
    (h : x.fswHb a b = true) : TransGen x.ghbXl.Holds a b :=
  Exec.swHb_ghbXl (Silmaril.Proofs.X86.Concurrency.Cir.Futex.fswHb_swHb h)

/-- Adding the wake edges to SC changes nothing. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.scF_iff (x : Exec) : x.ScF ↔ x.Sc :=
  Silmaril.Proofs.X86.Concurrency.Cir.Futex.scF_iff x

/-- Adding the wake edges to TSO changes nothing. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.tsoF_iff (x : Exec) : x.TsoF ↔ x.Tso :=
  Silmaril.Proofs.X86.Concurrency.Cir.Futex.tsoF_iff x

/-- Adding the wake edges to XL changes nothing. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.xlF_iff (x : Exec) : x.XlF ↔ x.Xl :=
  Silmaril.Proofs.X86.Concurrency.Cir.Futex.xlF_iff x

/-- SC ⊑ TSO, with wake edges. -/
theorem scF_le_tsoF : Exec.ScF ⊑ Exec.TsoF := fun x h =>
  (x.tsoF_iff).mpr (sc_le_tso x ((x.scF_iff).mp h))

/-- TSO ⊑ XL, with wake edges. -/
theorem tsoF_le_xlF : Exec.TsoF ⊑ Exec.XlF := fun x h =>
  (x.xlF_iff).mpr (tso_le_xl x ((x.tsoF_iff).mp h))

/-- SC ⊑ XL, with wake edges. -/
theorem scF_le_xlF : Exec.ScF ⊑ Exec.XlF := scF_le_tsoF.trans tsoF_le_xlF

/-- CIR behaviours under SC with wake edges are the SC behaviours. -/
theorem behavIn_scF_iff {P : Prog} {dom : List Nat} {f : Final} :
    BehavIn P dom Exec.ScF f ↔ BehavIn P dom Exec.Sc f := behavIn_congr Exec.scF_iff

/-- CIR behaviours under TSO with wake edges are the TSO behaviours. -/
theorem behavIn_tsoF_iff {P : Prog} {dom : List Nat} {f : Final} :
    BehavIn P dom Exec.TsoF f ↔ BehavIn P dom Exec.Tso f := behavIn_congr Exec.tsoF_iff

/-- CIR behaviours under XL with wake edges are the XL behaviours. -/
theorem behavIn_xlF_iff {P : Prog} {dom : List Nat} {f : Final} :
    BehavIn P dom Exec.XlF f ↔ BehavIn P dom Exec.Xl f := behavIn_congr Exec.xlF_iff

/-- **No lost wake-up (XL)**: a store `s` before a wake's locked queue write `w`, `w`
coherence-before a waiter's enqueue `q`, and an `mfence` between `q` and the check `l`: the
check cannot read from before `s`. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.futex_dekker_xl {x : Exec} (hx : x.Xl)
    {s w q l : Fin x.n} (hs : x.lockXl s w = true) (hco : x.coR w q = true)
    (hf : x.mfence q l = true) : x.frR l s = false := by
  cases h : x.frR l s
  · rfl
  · exact (Silmaril.Proofs.X86.Concurrency.Cir.Futex.dekker_xl hx hs hco hf h).elim

/-- **No lost wake-up (TSO)**. -/
theorem _root_.Silmaril.X86.MemoryModel.Axiomatic.Exec.futex_dekker_tso {x : Exec} (hx : x.Tso)
    {s w q l : Fin x.n} (hs : x.lockXl s w = true) (hco : x.coR w q = true)
    (hf : x.mfence q l = true) : x.frR l s = false :=
  Exec.futex_dekker_xl (tso_le_xl x hx) hs hco hf

/-- Allowing blocked threads only adds behaviours. -/
theorem behavIn_bbehavIn {P : Prog} {dom : List Nat} {M : Exec → Prop} {f : Final}
    (h : BehavIn P dom M f) : BBehavIn P dom M f :=
  Silmaril.Proofs.X86.Concurrency.Cir.Futex.behavIn_bbehavIn h

/-- Blocked behaviours are monotone in the model. -/
theorem bbehavIn_mono {P : Prog} {dom : List Nat} {M M' : Exec → Prop} (h : M ⊑ M') {f : Final}
    (hf : BBehavIn P dom M f) : BBehavIn P dom M' f :=
  Silmaril.X86.MemoryModel.Litmus.axReach_mono h hf

end Silmaril.X86.Concurrency.Cir
