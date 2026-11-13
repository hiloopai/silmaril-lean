module

public import Silmaril.Process.Mt.Pthread.Glibc.Defs
import Silmaril.Proofs.Process.Mt.Pthread.Spin

/-!
# glibc's pthreads against the specifications: results

* **`spin_primitive`** (proved): glibc 2.39's `pthread_spin_lock`, `pthread_spin_trylock` and
  `pthread_spin_unlock`, as transcribed in `Glibc/Defs` from the pinned bytes, implement the
  spin-lock specification (`Shapes.Mt.Primitive`) under `sc`, `tso` and `xl`.
* `spin_reach`: the underlying simulation, for any start the abstraction relates.
* `CodeModel.sound_mono` (proved): an obligation at a memory model gives it at every model
  below, for code models whose runs grow with the model. So `Task.glibcObl f X .tso` gives
  `.sc`, and `Task.glibcObl f X .xl` gives `.sc` and `.tso`.

The obligations of the other functions (`Task.glibcObl`) are stated, not proved.
-/

@[expose] public section

namespace Silmaril.Process.Mt.Pthread.Glibc

open Silmaril.Process.Mt.Csl
open Silmaril.X86.MemoryModel.Lattice (Name)

/-- **glibc's spin lock implements its specification** under SC, x86-TSO and XL: the most
general client running the pinned code refines the atomic specification, for every client
invariant. -/
theorem spin_primitive (pol : Pol) : Silmaril.Project.Shapes.Mt.Primitive spinSpec (model pol) :=
  fun I Q => Silmaril.Proofs.Process.Mt.Pthread.Spin.sound pol I Q

/-- The simulation behind `spin_primitive`: every run of the machine from a configuration
standing for `C₀` stands for a run of the specification from `C₀`, and a faulting machine
configuration for a faulting abstract one. -/
theorem spin_reach {pol : Pol} {c₀ c : SConf} (r : Star (model pol).step c₀ c)
    {C₀ : Cfg (TIsa.mgc (S := pstore) spinSpec)} (ha : (model pol).abs c₀ C₀) :
    ∃ C, Reach (TIsa.mgc (S := pstore) spinSpec) C₀ C ∧ (model pol).abs c C ∧
      ((model pol).fault c → Fault (TIsa.mgc (S := pstore) spinSpec) C) :=
  Silmaril.Proofs.Process.Mt.Pthread.Spin.reach r ha

theorem star_mono {α : Type} {r s : α → α → Prop} (h : ∀ a b, r a b → s a b) {a b : α}
    (hr : Star r a b) : Star s a b := by
  induction hr with
  | refl => exact Star.refl
  | step h₁ _ ih => exact Star.step (h _ _ h₁) ih

/-- **Obligations move down the lattice**: a code model sound at `b` is sound at every `a`
below `b`, when its runs grow with the model. -/
theorem CodeModel.sound_mono {sp : PrimSpec PSt} {X : CodeModel sp} (hm : X.Mono) {a b : Name}
    (hab : a.le b = true) {I : HProp Unit Unit} {Q : Nat → List (List Nat) → Heap Unit Unit → Prop}
    (h : (X.at b).Sound I Q) : (X.at a).Sound I Q :=
  fun c₀ c C₀ ha hg r => h c₀ c C₀ ha hg (star_mono (hm a b hab) r)

/-- The glibc obligations at `tso` give them at `sc`; those at `xl` give `sc` and `tso`. -/
theorem glibcObl_mono {f : Fn} {X : CodeModel f.spec} (hm : X.Mono) {a b : Name}
    (hab : a.le b = true) (h : Task.glibcObl f X b) : Task.glibcObl f X a :=
  fun I Q => CodeModel.sound_mono hm hab (h I Q)

end Silmaril.Process.Mt.Pthread.Glibc
