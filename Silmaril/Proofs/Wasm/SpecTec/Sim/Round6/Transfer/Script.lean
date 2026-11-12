module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Transfer.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Thms
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# Round 6: the rules of `Step_read` that consult `Ref_ok`

`plainOrTagsB_read` says every rule of `Step_read` is plain for `Expand` or names
a cast constructor. This check pins the second kind down by index: **every rule of `Step_read`
outside the eight cast rules `Round5.Read.readDoneK` (2–5, 65–68) is plain for `Expand`**
(`plain_read_of_not_mem`), a kernel `rfl` over the pinned script.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Transfer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Reading

set_option maxRecDepth 8000000 in
set_option maxHeartbeats 8000000 in
/-- Every rule of `Step_read` outside the cast rules is plain for `Expand`. -/
theorem plainExceptB_read :
    plainExceptB ["Expand"] Round5.Read.readDoneK
      (RefsGC.relRules (envOfScript Specs.wasm30) "Step_read") = true := by
  rfl

/-- **A rule of `Step_read` outside the cast rules is plain for `Expand`.** -/
theorem plain_read_of_not_mem {i : Nat} {r : Rule}
    (hi : (RefsGC.relRules (envOfScript Specs.wasm30) "Step_read")[i]? = some r)
    (hk : i ∉ Round5.Read.readDoneK) : PlainRule (· ∈ ["Expand"]) r := by
  have hm : (r, i) ∈ (RefsGC.relRules (envOfScript Specs.wasm30) "Step_read").zipIdx :=
    List.mem_zipIdx_iff_getElem?.2 hi
  have hc := List.all_eq_true.1 plainExceptB_read _ hm
  have hk' : Round5.Read.readDoneK.contains i = false := by simpa using hk
  rw [hk', Bool.false_or] at hc
  exact plainRule_of_plainRuleB hc

end Silmaril.Wasm.SpecTec.Sim.Round6.Transfer
