module

public import Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: the encoder lemma for `ExpFree` (round 2, pass 2)

`Round7.TypAgree.hasTyp_config_iff` moves the typing of a configuration between `simEnv B` and
`utf8Env B` at values whose `EXPORTS` fields are empty (`Round7.TypAgree.ExpFree`). This header
names the boolean check used to prove that the image `configV hn c` of an export-free
configuration (`Round5.Pos.NoExports c`) is such a value:

* `efB v`: every record field of `v` named `EXPORTS` is the empty list. `efB v = true` implies
  `ExpFree v` (`Round7.ExpEnc.expFree_of_efB`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-- `w` is the empty list value. -/
def isNilList : Value → Bool
  | .list [] => true
  | _ => false

mutual
/-- **Every `EXPORTS` record field of `v` is `[]`**, as a boolean. -/
def efB : Value → Bool
  | .bool _ => true
  | .num _ => true
  | .text _ => true
  | .tuple vs => efBs vs
  | .case _ w => efB w
  | .struct gs => efBf gs
  | .list vs => efBs vs
  | .opt none => true
  | .opt (some w) => efB w

/-- `efB` on a list of values. -/
def efBs : List Value → Bool
  | [] => true
  | v :: vs => efB v && efBs vs

/-- `efB` on the fields of a record, with the `EXPORTS` check. -/
def efBf : List (IL.AtomS × Value) → Bool
  | [] => true
  | (a, v) :: gs => efB v && (a != "EXPORTS" || isNilList v) && efBf gs
end

end Silmaril.Wasm.SpecTec.Sim.Round7.ExpEnc
