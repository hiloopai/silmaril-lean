module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Fwd
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Simple
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Adj
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.ElseBwd.Chain2
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.ElseBwd.CheckBad

/-!
# Round 9, RE and RM: the `otherwise` rules of `Step_read` (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd`; see `docs/projects/spectec/README.md`.
Definitions are in `Round9/ElseBwd/Defs.lean`; the head lemmas and the transfer are in
`Silmaril/Proofs/…/Round9/ElseBwd/{Head,Else}`, the kernel checks in `…/{Check,CheckBad}`, and the
rule case for RE, unrefined, in `Silmaril/Raw/…/Round9/ElseBwd/Fwd`.

The one argument shared by RE and RM:

* **`otherwiseAtB_map`, `otherwiseAt_map`**: for any map `ε` that takes pairs to pairs and keeps
  instruction heads, an `otherwise` premise that held where rule `i` fired holds at the image,
  given the backward firing (`PairReflectB`/`PairReflectD`) only at the earlier rules whose head is
  not known to differ from rule `i`'s. `vHead_eraseV` and `vHead_eraseC`: both erasures keep
  heads.
* **`elsePairs_fixed`** (kernel): in the fixed script those pairs are `elsePairs`, 94 of the 1,638
  pairs `(i, j)` with `i` one of the 28 `otherwise` rules of `Step_read` and `j < i`. No rule of
  `Step` has an `otherwise` premise.

For RE:

* **`stepBadE_fixed`** (kernel): of the 36 rules of `BadFwd`, the 28 `otherwise` rules pass the
  check once `otherwise` is allowed (`goodRuleE`); eight are left.
* **`badFwd_of_else`**: `NxStep.BadFwd` follows from `BadFwdE` (those eight rules) and
  `ElseBwdB` (`PairReflectB` along `eraseV` at the 94 pairs).
* **`stepFwdS_else`, `sStepB_fwd_BI_else`, `sReadB_fwd_BI_else`**: round 8's `stepFwdS`,
  `sStepB_fwd_BI`, `sReadB_fwd_BI` with `BadFwd` replaced by `BadFwdE` and `ElseBwdB`.

The first backward firings, for RE:

* **`simplePairs_fixed`** (kernel): 45 of the 94 pairs are simple: the earlier rule is an
  out-of-bounds, null or handler rule `z; L ~> R` whose quantifiers other than the state `z` have
  export-free type and whose premises are `if`s.
* **`pairReflect_simple`**: `PairReflectB` along `eraseV` at each simple pair, given conforming
  primitives that commute with erasure on `gdE`. `elseBwdB_of_rest`: `ElseBwdB` from the other 49
  pairs (`ElseBwdBRest`).
* **`stepFwdS_rest`, `sStepB_fwd_BI_rest`, `sReadB_fwd_BI_rest`**: the three results above with
  `ElseBwdB` replaced by `ElseBwdBRest`.

* **`adjPairs_fixed`** (kernel), **`pairReflectB_adj`**: at 26 pairs the earlier rule is
  `throw_ref-instrs`, whose instructions hold `REF.EXN_ADDR a` then `THROW_REF`; these cannot line
  up with the `otherwise` rule's list-literal instructions, so the backward firing holds
  vacuously. `elseBwdBRest_of_left`: `ElseBwdBRest` from the 23 pairs left (`leftPairs`,
  `ElseBwdBLeft`).
* **`stepFwdS_left`, `sStepB_fwd_BI_left`, `sReadB_fwd_BI_left`**: the results with `BadFwdE`
  and `ElseBwdBLeft` (23 pairs) as the only hypotheses besides the primitives.
* **`chainPairs_fixed`** (kernel), **`pairReflect_chain`**: at 12 pairs the earlier rule is itself
  an `otherwise` rule (`…-zero`) whose own earlier rules are all, against `i`, head-differing,
  adjacency-clashing or simple; its `otherwise` premise goes back because a simple rule's firing
  goes forward (`fireFwd_simple`). `elseBwdBLeft_of_left'`: `ElseBwdBLeft` from the 11 pairs of
  `leftPairs'`. **`stepFwdS_left'`, `sStepB_fwd_BI_left'`, `sReadB_fwd_BI_left'`**.
* **`chain2Pairs_fixed`** (kernel), **`pairReflect_chain2`**: `table.copy-gt` and
  `memory.copy-gt` against `…-le`, one level deeper (`fireFwd_elseRule`).
  `elseBwdBLeft'_of_left''`: `ElseBwdBLeft'` from the 9 pairs of `leftPairs''`.
  **`stepFwdS_left''`, `sStepB_fwd_BI_left''`, `sReadB_fwd_BI_left''`**: the RE results with
  `BadFwdE` (8 rules) and `ElseBwdBLeft''` (9 pairs) as the only hypotheses besides the
  primitives.

For RM:

* **`otherwise_eraseC`**: the declarative `otherwise` of a fired `Step_read` rule goes along code
  erasure, given `ElseBwdD` (`PairReflectD` along `eraseC` at the same 94 pairs).
* **`pairReflectD_adj`**, **`elseBwdD_of_rest`**: the 26 pairs with `throw_ref-instrs` hold along
  `eraseC` too, so `ElseBwdD` follows from `ElseBwdDRest` (68 pairs). `otherwise_eraseC_rest`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (DDerivesB otherwiseB SStepB SReadB)

/-- **`Step` and `Step_read` go to the erased side**, given conforming primitives that commute
with erasure on `gdE`, `BadFwdE` at the eight rules that fail `goodRuleE`, and the backward firing
at the 94 pairs (`ElseBwdB`). -/
theorem stepFwdS_else {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hE : BadFwdE (utf8Env B))
    (hP : ElseBwdB (utf8Env B)) {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  Round8.NxStep.stepFwdS hB H (badFwd_of_else hB H hP hE) hx h

section BI

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdE` and
`ElseBwdB`. -/
theorem sStepB_fwd_BI_else (hE : BadFwdE (NxPrims.envBI P hn host))
    (hP : ElseBwdB (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  Round8.NxStep.sStepB_fwd_BI P hn host
    (badFwd_of_else (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hP hE) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given `BadFwdE`
and `ElseBwdB`. -/
theorem sReadB_fwd_BI_else (hE : BadFwdE (NxPrims.envBI P hn host))
    (hP : ElseBwdB (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  Round8.NxStep.sReadB_fwd_BI P hn host
    (badFwd_of_else (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hP hE) h

end BI

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.otherwiseAtB_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms otherwiseAtB_map

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.otherwiseAt_map' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms otherwiseAt_map

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.elsePairs_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms elsePairs_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.stepBadE_fixed' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms stepBadE_fixed

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sStepB_fwd_BI_else' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI_else

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sReadB_fwd_BI_else' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_else

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.otherwise_eraseC' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms otherwise_eraseC

/-- **`Step` and `Step_read` go to the erased side**, given `BadFwdE` and the backward firing at
the 49 pairs outside `simplePairs`. -/
theorem stepFwdS_rest {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hE : BadFwdE (utf8Env B))
    (hR : ElseBwdBRest (utf8Env B)) {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  stepFwdS_else hB H hE (elseBwdB_of_rest hB H hR) hx h

section BIRest

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdE` and
`ElseBwdBRest`. -/
theorem sStepB_fwd_BI_rest (hE : BadFwdE (NxPrims.envBI P hn host))
    (hR : ElseBwdBRest (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  sStepB_fwd_BI_else P hn host hE
    (elseBwdB_of_rest (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hR) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given `BadFwdE`
and `ElseBwdBRest`. -/
theorem sReadB_fwd_BI_rest (hE : BadFwdE (NxPrims.envBI P hn host))
    (hR : ElseBwdBRest (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  sReadB_fwd_BI_else P hn host hE
    (elseBwdB_of_rest (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host) hR) h

end BIRest

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.pairReflect_simple' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms pairReflect_simple

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sReadB_fwd_BI_rest' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_rest

/-- **`Step` and `Step_read` go to the erased side**, given `BadFwdE` and the backward firing at
the 23 pairs of `leftPairs`. -/
theorem stepFwdS_left {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hE : BadFwdE (utf8Env B))
    (hL : ElseBwdBLeft (utf8Env B)) {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  stepFwdS_rest hB H hE (elseBwdBRest_of_left hL) hx h

section BILeft

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdE` and
`ElseBwdBLeft`. -/
theorem sStepB_fwd_BI_left (hE : BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwdBLeft (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  sStepB_fwd_BI_rest P hn host hE (elseBwdBRest_of_left hL) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given `BadFwdE`
and `ElseBwdBLeft`. -/
theorem sReadB_fwd_BI_left (hE : BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwdBLeft (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  sReadB_fwd_BI_rest P hn host hE (elseBwdBRest_of_left hL) h

end BILeft

/-- **The declarative `otherwise` goes along code erasure** (RM), given the backward firing at the
68 pairs outside `adjPairs`. -/
theorem otherwise_eraseC_rest {B : Builtins} (hR : ElseBwdDRest (simEnv B)) {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {i : Nat} {ri : Rule} {v : Value}
    (hrel : (simEnv B).findRel? "Step_read" = some (ps, op, t, rules))
    (hi : rules[i]? = some ri) (hel : hasElse ri = true)
    (hF : FiredD (simEnv B) "Step_read" [] i v) (h : Sim.otherwiseAt (simEnv B) "Step_read" [] i v) :
    Sim.otherwiseAt (simEnv B) "Step_read" [] i (Round8.CodeErase.Swap.eraseC v) :=
  otherwise_eraseC (elseBwdD_of_rest hR) hrel hi hel hF h

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sReadB_fwd_BI_left' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_left

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sStepB_fwd_BI_left' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI_left

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.otherwise_eraseC_rest' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms otherwise_eraseC_rest

/-- **`Step` and `Step_read` go to the erased side**, given `BadFwdE` and the backward firing at
the 11 pairs of `leftPairs'`. -/
theorem stepFwdS_left' {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hE : BadFwdE (utf8Env B))
    (hL : ElseBwdBLeft' (utf8Env B)) {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  stepFwdS_left hB H hE (elseBwdBLeft_of_left' hB H hL) hx h

section BILeft'

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdE` and
`ElseBwdBLeft'`. -/
theorem sStepB_fwd_BI_left' (hE : BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwdBLeft' (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  sStepB_fwd_BI_left P hn host hE
    (elseBwdBLeft_of_left' (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host)
      hL) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given `BadFwdE`
and `ElseBwdBLeft'`. -/
theorem sReadB_fwd_BI_left' (hE : BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwdBLeft' (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  sReadB_fwd_BI_left P hn host hE
    (elseBwdBLeft_of_left' (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host)
      hL) h

end BILeft'

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.pairReflect_chain' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms pairReflect_chain

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sReadB_fwd_BI_left'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_left'

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sStepB_fwd_BI_left'' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI_left'

/-- **`Step` and `Step_read` go to the erased side**, given `BadFwdE` (8 rules) and the backward
firing at the 9 pairs of `leftPairs''`. -/
theorem stepFwdS_left'' {B : Builtins}
    (hB : NxSound.BuiltinsVT NxTyped.sigX NxTyped.tsigFixed (utf8Env B))
    (H : EraseAll.BIErase NxErase.QT EraseAll.gdE (utf8Env B)) (hE : BadFwdE (utf8Env B))
    (hL : ElseBwdBLeft'' (utf8Env B)) {x : IL.Id} {op : MixopS} {args : List ArgV} {v : Value}
    (hx : Round8.NxStep.stepRel x = true)
    (h : DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op args v) :
    DDerivesB (utf8Env B) (otherwiseB (utf8Env B)) x op (args.map Swap.eraseA) (Swap.eraseV v) :=
  stepFwdS_left' hB H hE (elseBwdBLeft'_of_left'' hB H hL) hx h

section BILeft''

variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **SpecTec's `Step` goes to the erased side** at round 4's primitives, given `BadFwdE` and
`ElseBwdBLeft''`. -/
theorem sStepB_fwd_BI_left'' (hE : BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwdBLeft'' (NxPrims.envBI P hn host)) {c c' : Value}
    (h : SStepB (NxPrims.envBI P hn host) c c') :
    SStepB (NxPrims.envBI P hn host) (Swap.eraseV c) (Swap.eraseV c') :=
  sStepB_fwd_BI_left' P hn host hE
    (elseBwdBLeft'_of_left'' (NxPrims.builtinsVT_BI P hn host)
      (NxClause.biErase_QT_BI P hn host) hL) h

/-- **SpecTec's `Step_read` goes to the erased side** at round 4's primitives, given `BadFwdE`
and `ElseBwdBLeft''`. -/
theorem sReadB_fwd_BI_left'' (hE : BadFwdE (NxPrims.envBI P hn host))
    (hL : ElseBwdBLeft'' (NxPrims.envBI P hn host)) {c : Value} {js : List Value}
    (h : SReadB (NxPrims.envBI P hn host) c js) :
    SReadB (NxPrims.envBI P hn host) (Swap.eraseV c) (js.map Swap.eraseV) :=
  sReadB_fwd_BI_left' P hn host hE
    (elseBwdBLeft'_of_left'' (NxPrims.builtinsVT_BI P hn host)
      (NxClause.biErase_QT_BI P hn host) hL) h

end BILeft''

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sStepB_fwd_BI_left''' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sStepB_fwd_BI_left''

/--
info: 'Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd.sReadB_fwd_BI_left''' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sReadB_fwd_BI_left''

end Silmaril.Wasm.SpecTec.Sim.Round9.ElseBwd
