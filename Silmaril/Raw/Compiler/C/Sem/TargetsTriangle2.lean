module

public import Silmaril.Compiler.C.Sem.TargetsTriangle.Defs
public import Silmaril.Compiler.C.Sem.TargetsCoreC2.Defs
public import Silmaril.Compiler.C.Sem.TargetsCoreC3.Defs
public import Silmaril.Compiler.C.Sem.TargetsCoreC4.Defs
public import Silmaril.Compiler.C.Sem.TargetsLadderCheck.Defs
@[expose] public section

/-!
# Per-program triangles for C2, C3, C4 and checked C2/C0 agreement (statements)

The same-rung targets have exactly the shape of
`Targets.ccomp_factors_through_core_c0`: an elaboration witness, followed by
universal factorization of the runtime-linked ccomp Mir through that very Core
program. For rung N, `checkCN_sound` supplies direct validity and a nonempty Mir
behaviour set; `Targets.cN_core_realises` supplies `Core.beh q = CN.beh p`;
`C.Sem.factor` then gives the two valid steps. The existence clause is the
existence clause of that rung's already-proved Core-realisation target.

The mixed target uses `checkC2` with `elabC0`. Its two checked-ladder premises
are essential: `ladder_check_sound_c2` and `ladder_check_sound_c1` give
`C2.beh p = C1.beh p = C0.beh p`. Rewrite the direct validity from
`checkC2_sound` along this equality, then apply `factor_elabC0`. The nonempty
Mir behaviour set is unchanged. For existence, the declaration-free
`return;` main used by `TriangleProofs` and `LadderCheckSound` is accepted by
`elabC0`, `ladderCheck1` and `ladderCheck2`; these are executable, terminating
checks with kernel equations. This does not assume a universal ladder law or
any C2/C3 agreement (C3 changes float layout).

As in `TargetsTriangle`, the existence clauses omit `checkCN`, which runs
ccomp and the Ail codec through partial definitions opaque to the kernel.
Scoring must additionally require a real dev corpus program satisfying the
whole conjunction: `checkCN && (elabCN p).isSome` for each same-rung target,
and `checkC2 && (elabC0 p).isSome && ladderCheck1 && ladderCheck2` for the
mixed target. An elaboration witness alone does not establish that gate.
The elaborators are worker-written; these targets do not assert agreement
with Cerberus-generated Core. These are statements only, for coordinator
review before any new target proof.
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.C.Sem

/-- Runtime-linked ccomp factors through the checked C2 Core elaboration,
with an elaboration witness and the same-rung both-accept corpus gate. -/
def ccomp_factors_through_core_c2 : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC2 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    checkC2 p = true → elabC2 p = some q →
      ∃ us, ccompMirRt p = some us ∧
        Valid (Core.cAC C2.sem) p q ∧ Valid (Core.cCM mirConfig ctlAddress) q us ∧
        (Mir.beh mirConfig us).Nonempty)

/-- Runtime-linked ccomp factors through the checked C3 Core elaboration,
with an elaboration witness and the same-rung both-accept corpus gate. -/
def ccomp_factors_through_core_c3 : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC3 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    checkC3 p = true → elabC3 p = some q →
      ∃ us, ccompMirRt p = some us ∧
        Valid (Core.cAC C3.sem) p q ∧ Valid (Core.cCM mirConfig ctlAddress) q us ∧
        (Mir.beh mirConfig us).Nonempty)

/-- Runtime-linked ccomp factors through the checked C4 Core elaboration,
with an elaboration witness and the same-rung both-accept corpus gate. -/
def ccomp_factors_through_core_c4 : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC4 p = some q) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    checkC4 p = true → elabC4 p = some q →
      ∃ us, ccompMirRt p = some us ∧
        Valid (Core.cAC C4.sem) p q ∧ Valid (Core.cCM mirConfig ctlAddress) q us ∧
        (Mir.beh mirConfig us).Nonempty)

/-- Runtime-linked ccomp validated at C2 factors through the C0 elaboration
when both adjacent checks certify exact C2/C1/C0 behaviour equality. The
existence witness must satisfy the elaborator and both ladder checks together;
scoring additionally requires `checkC2` on that same corpus program. -/
def ccomp_factors_through_core_mixed_c2c0 : Prop :=
  (∃ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC0 p = some q ∧ ladderCheck1 p = true ∧ ladderCheck2 p = true) ∧
  (∀ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    checkC2 p = true → elabC0 p = some q →
      ladderCheck1 p = true → ladderCheck2 p = true →
      ∃ us, ccompMirRt p = some us ∧
        Valid (Core.cAC C0.sem) p q ∧ Valid (Core.cCM mirConfig ctlAddress) q us ∧
        (Mir.beh mirConfig us).Nonempty)

end Silmaril.Compile.Targets
