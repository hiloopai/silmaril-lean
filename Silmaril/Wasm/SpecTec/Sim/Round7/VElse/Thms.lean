module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VElse.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.VElse.Check

/-!
# Round 7, memory SIMD: the `otherwise` rules of `Step_read` and rule 43

Kernel-checked syntax facts for the `$vbytes_` transfer of `OpenRMRest.rest`
(`docs/projects/spectec/README.md`):

* `read_else`: the `otherwise` rules of `Step_read` are 3, 5, 21, 29, 30, 32–34, 36, 37, 54, 55,
  57–59, 61, 62, 66, 68, 84, 85, 90–92, 96, 97, 101 and 102 (0-based). This confirms round 3's
  parse outside Lean.
* `step_else`: `Step` has none.
* `read_43_atom`: rule 43 (`vload-num-val`) has the left-hand side `(z; … VLOAD …)`, its last
  instruction a `VLOAD` case.
* `read_elseOk`: every `otherwise` rule after 43 ends its left-hand side with a `case` of a
  different mixop.

These are statements about the syntax of the rules. The semantic step, that rule 43 therefore
does not fire on a value another rule's left-hand side matched (so the `otherwise` premises of
rules 54–102 read alike at `withVBytes B` and at `B`), needs the declarative reading of
conclusions and is not proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VElse

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VElse.read_elseOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_elseOk

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.VElse.read_else' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms read_else

end Silmaril.Wasm.SpecTec.Sim.Round7.VElse
