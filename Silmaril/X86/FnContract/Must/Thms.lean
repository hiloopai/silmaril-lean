module

public import Silmaril.X86.FnContract.Must.Defs
public import Silmaril.Proofs.X86.FnContract.Must
/-!
# Demonic function contracts: what is proved (header)

PROVED (standard axioms; proofs in `Silmaril/Proofs/Machine/X86/FnContract/Must.lean`, names in
`Silmaril.X86.FnContract`):

* views: `Spec.resultV_ofIsa`, `returnedV_ofIsa`;
* **bridges** to the deterministic notions (`FnContract.Spec.Strict` on a `SegVC.Isa`):
  `Spec.Strict.must` (strict ⇒ demonic on `ofIsa I`), `Spec.Must.strict` (the converse),
  `Spec.must_ofIsa_iff`;
* **tier A**: `Spec.TotalIn.mustInLoosen`, `Spec.TotalIn.mustLoosen` (a first-return run
  inside `P` ⇒ demonic on `loosen I P`), `Spec.Strict.mustLoosen` (strict ⇒ demonic on
  `loosen I ⊤`);
* **transfer**: `Spec.MustIn.of_le`, `Spec.Must.of_le` (along `RelIsa.Le`),
  `Spec.Must.strict_of_le` (demonic on `A` ⇒ strict on every deterministic `C` with
  `Le (ofIsa C) A`, the "transfer for free" statement for existing consumers),
  `Spec.Must.strict_of_loosen`, `Spec.Must.of_sim` (along a simulation, to the pulled-back
  spec `Spec.comapRel`, under `ViewsRel`); `ViewsRel.refl`, `Spec.comap_eq_sub` and
  `viewsRel_infoLe_mstate` (`InfoLe` on `MState` satisfies `ViewsRel`);
* **structure**: `Spec.MustIn.mono` (run predicate), `Spec.MustIn.sub` (spec refinement),
  `Spec.MustIn.frame` (frame rule), `Spec.MustIn.call`, `Spec.Must.call` (a contracted call
  inside a caller's `Must` run), `Spec.MustIn.exists_result` (a run, given `Progress`),
  `progress_loosen`;
* here: `FnContract.Strict.toMust`, `FnContract.Strict.toMustLoosen`, `FnContract.Must.ofLe`,
  `FnContract.Must.toStrict`.

The smoke instance on libmini's `strlen` (`strlenSpec_must`) is in
`FnContract/Must/LibMini/Thms.lean`, so this header does not import the ladder rung (whose
`Defs` import `Silmaril.Machine.SystemV.Defs`).
-/

@[expose] public section

namespace Silmaril.X86

open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.RelIsa (ofIsa loosen Le)

variable {σ : Type}

/-- A strict contract is a demonic contract on the same deterministic machine. -/
def FnContract.Strict.toMust {I : Isa σ} (C : FnContract.Strict I) : FnContract.Must (ofIsa I) where
  toSpec := C.toSpec
  must := FnContract.Spec.Strict.must C.strict

/-- A strict contract is a demonic contract on the everywhere-loosened machine. -/
def FnContract.Strict.toMustLoosen {I : Isa σ} (C : FnContract.Strict I) :
    FnContract.Must (loosen I fun _ => True) where
  toSpec := C.toSpec
  must := FnContract.Spec.Strict.mustLoosen C.strict

/-- A demonic contract transfers to every machine with fewer behaviours. -/
def FnContract.Must.ofLe {A C : RelIsa σ} (h : Le C A) (M : FnContract.Must A) :
    FnContract.Must C where
  toSpec := M.toSpec
  must := FnContract.Spec.Must.of_le h M.must

/-- A demonic contract is a strict contract of every deterministic machine that refines it. -/
def FnContract.Must.toStrict {A : RelIsa σ} {C : Isa σ} (h : Le (ofIsa C) A)
    (M : FnContract.Must A) : FnContract.Strict C where
  toSpec := M.toSpec
  total := FnContract.Spec.Strict.total (FnContract.Spec.Must.strict_of_le h M.must)
  strict := FnContract.Spec.Must.strict_of_le h M.must

@[simp] theorem FnContract.Strict.toMust_toSpec {I : Isa σ} (C : FnContract.Strict I) :
    C.toMust.toSpec = C.toSpec := rfl

@[simp] theorem FnContract.Must.toStrict_toSpec {A : RelIsa σ} {C : Isa σ}
    (h : Le (ofIsa C) A) (M : FnContract.Must A) : (M.toStrict h).toSpec = M.toSpec := rfl

end Silmaril.X86
