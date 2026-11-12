module

public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.Script.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-!
# Round 7, the whole-evaluator erasure: the per-definition check and the script's size

`xDefOk gr gd d`: the definitions and relations that the top-level definition `d` binds pass the
syntactic check, and so does every conclusion alternative of the relations' rules (`xAltsOk`). The kernel chunks `CheckScript00`–`CheckScript39` check it on 25 top-level
definitions of the fixed wasm-3.0 script each; `fixed_length` (a kernel computation) says that 40
chunks cover the script. Chunking the script, rather than the definitions map `defsOfDefs`, keeps
each chunk cheap: the map is a left-nested chain of appends, so reaching its `k`-th entry in the
kernel costs time growing with `k` (round 3, pass 3).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- Every `gr` relation of `m` has rules every further conclusion alternative of which (the tail
of `Round6.Reading.conclAlts`; its head, the conclusion itself, is checked by `xRelsOk`) passes the
check. -/
def xAltsOk (gr gd : String → Bool) (m : Map RelDef) : Bool :=
  m.all fun p => !gr p.1 || p.2.2.2.2.all fun r => match r with
    | .ruleD _ _ _ e _ =>
      (if Round6.Reading.hasOptNil e then Round6.Reading.optAlts e else []).all (xExp gr gd)

/-- The definitions and relations bound by the top-level definition `d` pass the check, and so
do the conclusion alternatives of the relations' rules. -/
def xDefOk (gr gd : String → Bool) (d : Def) : Bool :=
  xDefsOk gr gd (defsOfDef d) && xRelsOk gr gd (relsOfDef d) && xAltsOk gr gd (relsOfDef d)

/-- A chunk from two halves. -/
theorem all_drop_take_add {α : Type} (f : α → Bool) (l : List α) (a m n : Nat)
    (h₁ : ((l.drop a).take m).all f = true) (h₂ : ((l.drop (a + m)).take n).all f = true) :
    ((l.drop a).take (m + n)).all f = true := by
  rw [List.take_add, List.all_append, h₁, List.drop_drop, h₂]
  rfl

set_option maxRecDepth 100000 in
theorem fixed_length : Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed.length ≤ 25 * 40 := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
