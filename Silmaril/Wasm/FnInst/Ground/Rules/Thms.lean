module

public import Silmaril.Wasm.FnInst.Ground.Thms
public import Silmaril.Wasm.Binaryen.DropGet.Thms
public import Silmaril.Wasm.Binaryen.RseLine.Thms

@[expose] public section

/-! # Existing wasm-opt stage proofs restated through the bridge

Each stage below already has a proof over silmaril's full semantics
(`Silmaril.Wasm.Binaryen.{DropGet,RseLine}`: one forward `BaseSim`, one typed reverse
simulation, at every numerical profile). Here the same stages are proved again as **one rule
lemma at the minimal signature** (`good_dropGet`, `good_rseSet`, `good_rseTee`, in
`Silmaril.Proofs.Wasm.FnInst.Ground.Rules`) **plus the generic transfer**
(`exportEquiv_of_rules`), reusing only each stage's syntactic body relation
(`dropGet_bodiesRel`, `rseLine_bodiesRel`). The restated theorems are weaker than the
originals in one respect: export equivalence is at every *deterministic* profile (silmaril's
closed-host closure needs determinism for the converse), not at every profile.

The rules of the fragment without a stage of their own get their module form the same way
(`neutral_module`, `eqz3_module`, `fold_module`, `constDrop_module`).
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool}

/-- The `drop-get` source pairs are good. -/
theorem dgBI_good : ∀ x y, Silmaril.Wasm.Binaryen.DropGet.dgBI x y → GBI x y
  | _, _, .mk x => gbi_of_good (good_dropGet x)

/-- The `rse-line` source pairs (rewritten side on the left) are good. -/
theorem rsBI_good : ∀ x y, RedundantSetLine.rsBI x y → GBI x y
  | _, _, .set x => gbi_of_good (good_rseSet x)
  | _, _, .tee x => gbi_of_good (good_rseTee x)

/-- **`drop-get`, restated**: rule lemma `good_dropGet` + generic transfer. -/
theorem dropGet_sound_ground {m : BModule} (hm : m.Ok)
    (hm' : (Silmaril.Wasm.Binaryen.DropGet.dropGet m).Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) m.lower
      (Silmaril.Wasm.Binaryen.DropGet.dropGet m).lower :=
  exportEquiv_of_rules dgBI_good (Silmaril.Wasm.Binaryen.DropGet.dropGet_bodiesRel m) hm hm'

/-- **`rse-line`, restated**: rule lemmas `good_rseSet`, `good_rseTee` + generic transfer. -/
theorem rseLine_sound_ground {m : BModule} (hm : m.Ok)
    (hm' : (RedundantSetLine.rseLine m).Ok) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
      (RedundantSetLine.rseLine m).lower m.lower :=
  exportEquiv_of_rules rsBI_good (Silmaril.Wasm.Binaryen.RseLine.rseLine_bodiesRel m) hm' hm

variable {m m' : Module}

theorem neutral_module {b : Bin} {k : BitVec 32} (hk : Neutral b k)
    (hrel : ModuleBodiesRel (Pair [.const k, .bin b] []) m m') (hm : ∃ mt, ModuleOk m mt)
    (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) m m' :=
  exportEquiv_of_pair (good_neutral hk) hrel hm hm'

theorem eqz3_module (hrel : ModuleBodiesRel (Pair [.eqz, .eqz, .eqz] [.eqz]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) m m' :=
  exportEquiv_of_pair good_eqz3 hrel hm hm'

theorem fold_module {b : Bin} {x y : BitVec 32}
    (hrel : ModuleBodiesRel (Pair [.const x, .const y, .bin b] [.const (b.eval x y)]) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) m m' :=
  exportEquiv_of_pair (good_fold b x y) hrel hm hm'

theorem constDrop_module {k : BitVec 32} (hrel : ModuleBodiesRel (Pair [.const k, .drop] []) m m')
    (hm : ∃ mt, ModuleOk m mt) (hm' : ∃ mt, ModuleOk m' mt) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H)) m m' :=
  exportEquiv_of_pair (good_constDrop k) hrel hm hm'

end Silmaril.Wasm.FnInst.Ground
