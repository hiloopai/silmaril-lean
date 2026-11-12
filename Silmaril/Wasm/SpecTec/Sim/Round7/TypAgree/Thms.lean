module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.TypAgree.Eq

/-!
# SpecTec ↔ Core 3.0, round 7: typing agrees in `simEnv B` and `utf8Env B` away from `name`

The typing half of `Round7.Task.envAgreeNE` (pass 8). For primitives `B` that leave `$utf8`
uninterpreted (round 6's `BI`, `Round7.BI_utf8`), in a scope whose definition variables are
reachable (`Round7.Script.DefsOk`) and whose type variables are bound to types over `tyA`
(`TypsOk tyA`):

* `hasTyp_utf8Env_eq_A`, `hasTyp_utf8Env_iff_A`: at a type over `tyA` (141 reachable types with
  no path to `name`), the two environments type every value alike, at every fuel;
* `hasTyp_utf8Env_eq_B`, `hasTyp_utf8Env_iff_B`, `hasTyp_config_iff`: at a type over `tyB` (every
  reachable type except `name` and `exportinst`, including `config`, `state`, `store`,
  `moduleinst` and `instr`), they type every value whose `EXPORTS` fields are empty (`ExpFree`)
  alike;
* `quantsOk_utf8Env_iff`: so the quantifiers of a rule are well typed alike when their types are
  over `tyB` and their values are `ExpFree`; `relQuantsOk_B` (kernel) says every rule of every
  relation `Step` reaches quantifies over `tyB`.

The kernel facts `typMapOk_A`, `typMapOk_B` and `relQuantsOk_B` are `decide +kernel` over the
fixed script. The induction is `Raw/…/Round7/TypAgree/Agree.lean` (unrefined).

Not shown here: that the quantifier values of a `utf8Env B` derivation from an export-free
configuration are `ExpFree` (the "determination" ingredient (c) of pass 7), the encoder lemma
`ExpFree (configV hn c)` for export-free `c`, and the transfer of `otherwise` premises. So
`Round7.Task.envAgreeNE` is still open.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.typMapOk_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typMapOk_A

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.typMapOk_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms typMapOk_B

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.relQuantsOk_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relQuantsOk_B

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.hasTyp_utf8Env_eq_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasTyp_utf8Env_eq_A

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.hasTyp_utf8Env_eq_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasTyp_utf8Env_eq_B

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.hasTyp_config_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hasTyp_config_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree.quantsOk_utf8Env_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quantsOk_utf8Env_iff

end Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
