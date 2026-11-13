module

public import Silmaril.Compiler.C.Sem.Targets.Defs
@[expose] public section

/-!
# Mir interpreter adequacy targets for images that fit

These statements add only an image-fit premise to the corresponding frozen targets.
Every byte of a successful link must lie below the configured memory bound.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.Category.Syntax
open Silmaril.Machine Silmaril.Machine.Lir
open Silmaril.Compile.C.Sem
open CategoryTheory

/-- `Mir.run` is adequate for returns when every linked image byte fits in memory. -/
def mir_run_returned_fit : Prop :=
  ∀ (cfg : Mir.Config) (n : Nat) (us : Array Mir.Unit) (vs : List UInt64) (m : Mir.Interp.Mem),
    (∀ l, Mir.link cfg.layout us = .ok l →
      ∀ i < l.image.size, l.dataBase + i < cfg.memSize) →
    Mir.run cfg n us = .ok (.returned vs m) →
    (.returned (vs.map UInt64.toBitVec, m.toLir) : Mir.LirOutcome) ∈ Mir.beh cfg us

/-- `Mir.run` is adequate for traps when every linked image byte fits in memory. -/
def mir_run_trapped_fit : Prop :=
  ∀ (cfg : Mir.Config) (n : Nat) (us : Array Mir.Unit) (m : Mir.Interp.Mem),
    (∀ l, Mir.link cfg.layout us = .ok l →
      ∀ i < l.image.size, l.dataBase + i < cfg.memSize) →
    Mir.run cfg n us = .ok (.trapped m) → (.trapped m.toLir : Mir.LirOutcome) ∈ Mir.beh cfg us

end Silmaril.Compile.Targets
