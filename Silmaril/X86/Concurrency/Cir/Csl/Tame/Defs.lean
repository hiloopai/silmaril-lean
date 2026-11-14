module

public import Silmaril.X86.Concurrency.Cir.Csl.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Defs

/-!
# Tame CIR programs: every store write-back

The CIR-native XL machine (`OStep .xl`)
differs from TSO only in its flush rule: an entry may leave the buffer before older ones when
one of the two is a weak (`nt`/`str`) store (`Ent.passes`). A program whose stores are all
write-back never buffers a weak entry, so XL's extra freedom is never available and XL's runs
are TSO's (`Csl.Tame.oreach_tso_of_wb`).

This is the operational counterpart of the axiomatic `Exec.xl_iff_tso_of_tame`
(`Silmaril.X86.MemoryModel.Xl.Thms`), whose `Exec.Tame` asks that every memory unit be write-back
and not tearable. CIR's cells never tear, so only the write-back half is needed here, and it is
**syntactic**: `Stmt.wbStores` is a `Bool` check on the program text.

* `Stmt.wbStores` (defined in `Cir/Tv/Defs.lean`, shared with the
  translation-validation modules): every `store` in the
  statement has flavour `wb`. Loads, RMWs, fences, futex calls and `local` blocks never create a weak buffer entry, whatever their annotation.
* `Ent.wb`: a buffer entry is not a weak store.
* `Cfg.WbStores N C`: every thread below `N` is `wbStores`.
-/

@[expose] public section

-- **The tameness check** `Stmt.wbStores` (every `store` of the statement is write-back) is
-- defined in `Cir/Tv/Defs.lean`, where the localisation proof also uses it.

namespace Silmaril.X86.Concurrency.Cir.Csl

open Silmaril.X86.Concurrency.Cir

/-- A buffer entry that is not a weak store (a write-back store or an `sfence` barrier). -/
def Ent.wb : Ent → Bool
  | .st _ _ w => !w
  | .bar => true

/-- **A tame start**: every thread below `N` passes the syntactic check `Stmt.wbStores`. -/
def Cfg.WbStores (N : Nat) (C : Cfg) : Prop := ∀ t < N, (C.ts t).1.wbStores = true

/-- A tame buffered configuration: tame threads and no weak entry in any buffer. -/
def OCfg.Wb (N : Nat) (C : OCfg) : Prop :=
  (∀ t < N, (C.ts t).1.wbStores = true) ∧ ∀ t, ∀ e ∈ C.buf t, e.wb = true

end Silmaril.X86.Concurrency.Cir.Csl
