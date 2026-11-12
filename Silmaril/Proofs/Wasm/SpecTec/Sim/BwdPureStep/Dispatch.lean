module

public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.RefEq
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Agg
public import Silmaril.Proofs.Wasm.SpecTec.Sim.BwdPureStep.Store
public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms

/-!
# The dispatch, and the concrete `B`

`pure_done`, `step_done`: every index of `pureDone`, `stepDone` is dispatched to its lemma, at
every `B` satisfying `BwdB` (`$wrap__`/`$extend__` as Core's, and the four store updaters left
`$table` and `$mem` to their clauses). `bwdB_builtins` proves `BwdB` for `Prims.builtins`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.BwdPureStep

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- What the dispatched lemmas assume of `B`. -/
structure BwdB (B : Builtins) : Prop where
  /-- `$wrap__(32, 31, ·)` and `$extend__(31, 32, ·, ·)` are Core's. -/
  rfuns : RefsGC.RFuns (simEnv B)
  /-- `B` leaves `$with_local` to its clause. -/
  withLocal : ∀ Z X V : Value, B.call "with_local" [.val Z, .val X, .val V] = none
  /-- `B` leaves `$with_global` to its clause. -/
  withGlobal : ∀ Z X V : Value, B.call "with_global" [.val Z, .val X, .val V] = none
  /-- `B` leaves `$with_elem` to its clause. -/
  withElem : ∀ Z X R : Value, B.call "with_elem" [.val Z, .val X, .val R] = none
  /-- `B` leaves `$with_data` to its clause. -/
  withData : ∀ Z X R : Value, B.call "with_data" [.val Z, .val X, .val R] = none
  /-- `B` leaves `$table` to its clause. -/
  table : ∀ Z X : Value, B.call "table" [.val Z, .val X] = none
  /-- `B` leaves `$mem` to its clause. -/
  mem : ∀ Z X : Value, B.call "mem" [.val Z, .val X] = none

variable {H : Type} {hn : H → String} {P : Numerics.Profile} {host : HostSemantics H}
variable (B : Builtins) (Hb : BwdB B)

include Hb in
/-- `Step_pure`, the indices of `pureDone`. -/
theorem pure_done (i : Nat) (hi : i ∈ pureDone) {s : Store H} {f : Frame} {is : List Admin}
    {w : Value} (hf : Fires (simEnv B) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    PureBwd P host s f is w := by
  simp only [pureDone, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  exacts [bwd_refI31 B Hb.rfuns hf, bwd_isNullTrue B hf, bwd_isNullFalse B hf,
    bwd_asNonNullNull B hf, bwd_asNonNullAddr B hf, bwd_eqNull B hf, bwd_eqTrue B hf,
    bwd_eqFalse B hf, bwd_i31GetNull B hf, bwd_i31GetNum B Hb.rfuns hf, bwd_arrayNew B hf,
    bwd_externConvertNull B hf, bwd_externConvertAddr B hf, bwd_anyConvertNull B hf,
    bwd_anyConvertAddr B hf]

include Hb in
/-- `Step`, the indices of `stepDone`. -/
theorem step_done (i : Nat) (hi : i ∈ stepDone) {c : Config H} {w : Value}
    (hf : Fires (simEnv B) "Step" i (.tuple [configV hn c, w])) : BwdP hn P host c w := by
  simp only [stepDone, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwd_localSet B Hb.withLocal hf, bwd_globalSet B Hb.withGlobal hf,
    bwd_tableSetOob B Hb.table hf, bwd_tableSetVal B Hb.table hf,
    bwd_elemDrop B Hb.withElem hf, bwd_storeNumOob B Hb.mem hf, bwd_storePackOob B Hb.mem hf,
    bwd_dataDrop B Hb.withData hf, bwd_structSetNull B hf, bwd_arraySetNull B hf,
    bwd_arraySetOob B hf]

/-- **`BwdB` for the concrete `B`.** -/
theorem bwdB_builtins {prof : Numerics.Profile} (hn : H → String) (host : HostSemantics H) :
    BwdB (Prims.builtins prof hn host) where
  rfuns := Prims.rFuns_builtins hn host
  withLocal _ _ _ := by
    simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]
  withGlobal _ _ _ := by
    simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]
  withElem _ _ _ := by
    simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]
  withData _ _ _ := by
    simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]
  table _ _ := by
    simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]
  mem _ _ := by
    simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

end Silmaril.Wasm.SpecTec.Sim.BwdPureStep
