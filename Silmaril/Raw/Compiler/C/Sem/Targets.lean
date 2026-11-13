module

public import Silmaril.Compiler.C.Sem.Validator.Defs
public import Silmaril.Compiler.Mir.SSA.Defs
public import Silmaril.Compiler.Target.RenameCorrect.Defs
@[expose] public section

/-!
# The target statements of the `csem` campaign (frozen)

Every statement the campaign counts, as a `Prop`. **This file is frozen**: the evaluator
checks its hash, so no statement can be weakened. A target is *proved* when a theorem named in
the evaluator's registry has exactly this
type (`example : Targets.x := @proof`), no `sorry`, and only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). Proofs live anywhere in the library.

Groups (docs/CSemantics.md):

* **lattice**: the laws of semantic lattices and of the composition API (proved);
* **mir**: the meaning of Mir (definitional, proved), determinism (proved), and the adequacy of
  the executable interpreter `Mir.run` (open);
* **c0**: fuel monotonicity and determinism of the C0 interpreter (open);
* **renamer**: the key lemma (proved), and the certificate for `RegAlloc.renumber` itself
  (open: the direct proof; an LCF-style checker is the alternative);
* **triangle**: factorization of Ail → Mir through Core (proved, generic and instantiated);
* **ccomp**: the per-program Ail → Mir validator `checkC0` is sound (open, scored with the
  number of programs it accepts; goal 1), and the stretch ∀-statement (not scored);
* **core**: Core realises C0 wherever the C0-only elaboration `elabC0` answers (open, scored with
  the number of programs elaborated).
-/

namespace Silmaril.Compile.Targets

open Silmaril.Compile.Category Silmaril.Compile.Category.Syntax
open Silmaril.Machine Silmaril.Machine.Lir
open Silmaril.Compile.C.Sem
open CategoryTheory

universe u

/-! ## lattice -/

def refinesOn_trans : Prop :=
  ∀ (X : Syntax.{0}) (F : Set X.Prog) (S T U : X.Sem), RefinesOn F S T → RefinesOn F T U →
    RefinesOn F S U

def refinesOn_union : Prop :=
  ∀ (X : Syntax.{0}) (F G : Set X.Prog) (S T : X.Sem),
    RefinesOn (F ∪ G) S T ↔ RefinesOn F S T ∧ RefinesOn G S T

def refinesOn_inf : Prop :=
  ∀ (X : Syntax.{0}) (F : Set X.Prog) (S T U : X.Sem),
    RefinesOn F U (S ⊓ T) ↔ RefinesOn F U S ∧ RefinesOn F U T

def sup_refinesOn : Prop :=
  ∀ (X : Syntax.{0}) (F : Set X.Prog) (S T U : X.Sem),
    RefinesOn F (S ⊔ T) U ↔ RefinesOn F S U ∧ RefinesOn F T U

def overlap_eq_inter : Prop :=
  ∀ (X : Syntax.{0}) (S T : X.Sem), overlap S T = refinesSet S T ∩ refinesSet T S

def refinesOn_iff_valid_cast : Prop :=
  ∀ (X : Syntax.{0}) (F : Set X.Prog) (S T : X.Sem),
    RefinesOn F S T ↔ ∀ p ∈ F, Valid (X.cast T S) p p

def validOn_of_refinesOn : Prop :=
  ∀ (X : Syntax.{0}) (L' : Language.{0}) (F : Set X.Prog) (S T : X.Sem) (c : X.lang S ⟶ L')
    (run : X.Prog → Option L'.Prog), ValidOn F S c run → RefinesOn F S T →
    ValidOn F T (reSource c T) run

def realises_factor : Prop :=
  ∀ (L M N : Language.{0}) (c : L ⟶ M) (d : M ⟶ N) (F : Set L.Prog) (e : L.Prog → M.Prog),
    Realises c F e → ∀ p ∈ F, ∀ r, Valid (c ≫ d) p r → Valid c p (e p) ∧ Valid d (e p) r

def realises_factor_of_le : Prop :=
  ∀ (L M N : Language.{0}) (c : L ⟶ M) (d : M ⟶ N) (a : L ⟶ N) (F : Set L.Prog)
    (e : L.Prog → M.Prog), Realises c F e → a ≤ c ≫ d → ∀ p ∈ F, ∀ r, Valid a p r →
    ∃ q, Valid c p q ∧ Valid d q r

def pipeline_sound : Prop :=
  ∀ (L L' : Language.{0}) (c : L ⟶ L') (P : Pipeline c) (p : L.Prog) (p' : L'.Prog),
    P.run p = some p' → Valid c p p'

def roundTrip_endo_refines : Prop :=
  ∀ (L S : Language.{0}) (T : RoundTrip L S) (E : EndoPass S) (p : L.Prog),
    L.Refines p ((T.endo E).run p)

/-! ## mir -/

def mir_link_valid : Prop :=
  ∀ (cfg : Mir.Config) (us : Array Mir.Unit) (q : Mir.LirProgram),
    (Mir.linkCompiler cfg).run us = some q → Valid (Mir.linkCompiler cfg).conv us q

def mir_beh_deterministic : Prop :=
  ∀ (cfg : Mir.Config) (us : Array Mir.Unit),
    (Mir.beh cfg us).Subsingleton ∨ Mir.beh cfg us = Set.univ

def mir_ssa_optimize_link_sound : Prop :=
  ∀ (cfg : Mir.Config) (E : EndoPass (Mir.ssaLang cfg)) (us : Array Mir.Unit)
    (q : Mir.LirProgram), (Mir.optimizeAndLink cfg E).run us = some q →
    Valid (Mir.linkCompiler cfg).conv us q

/-- `Mir.run` is adequate for returns (open). -/
def mir_run_returned : Prop :=
  ∀ (cfg : Mir.Config) (n : Nat) (us : Array Mir.Unit) (vs : List UInt64) (m : Mir.Interp.Mem),
    Mir.run cfg n us = .ok (.returned vs m) →
    (.returned (vs.map UInt64.toBitVec, m.toLir) : Mir.LirOutcome) ∈ Mir.beh cfg us

/-- `Mir.run` is adequate for traps (open). -/
def mir_run_trapped : Prop :=
  ∀ (cfg : Mir.Config) (n : Nat) (us : Array Mir.Unit) (m : Mir.Interp.Mem),
    Mir.run cfg n us = .ok (.trapped m) → (.trapped m.toLir : Mir.LirOutcome) ∈ Mir.beh cfg us

/-- `Mir.run` is adequate for undefined behaviour (open). -/
def mir_run_stuck : Prop :=
  ∀ (cfg : Mir.Config) (n : Nat) (us : Array Mir.Unit) (why : String) (pt : Mir.Interp.Point)
    (m : Mir.Interp.Mem), Mir.run cfg n us = .ok (.stuck why pt m) → Mir.beh cfg us = Set.univ

/-! ## c0 -/

/-- More fuel does not change a final result of the C0 interpreter (open). -/
def c0_run_mono : Prop :=
  ∀ (n k : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) (r : C0.Result),
    C0.run n p = r → (r = .outOfFuel → False) → C0.run (n + k) p = r

/-- C0 is deterministic: one behaviour, or every behaviour after undefined behaviour (open). -/
def c0_deterministic : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, (C0.beh p).Subsingleton ∨ C0.beh p = Set.univ

/-! ## renamer -/

open Silmaril.Compile.Target.RegAlloc in
/-- The key lemma: a renaming that is interference-free under a liveness certificate preserves
every non-stuck behaviour (proved). -/
def renamer_key_lemma : Prop :=
  ∀ (p : Prog Nat) (σ : FuncId → Nat → Nat) (live : Point → Set Nat), LiveCert p σ live →
    ∀ (f : FuncId) (args : List Word) (mem : Memory) (s : State Nat), p.start f args mem = some s →
    ∀ b : Behavior, Behaves p s b → b ≠ .stuck →
      ∃ t, (renameProg σ p).start f args mem = some t ∧ Behaves (renameProg σ p) t b

open Silmaril.Compile.Target.RegAlloc in
/-- `renumber` is renaming followed by dropping self-moves (proved). -/
def renumber_decomposes : Prop :=
  ∀ (k : Nat) (p : Prog Nat), renumber k p = dropProg (renumberDrop p) (renameProg (renumberσ k p) p)

open Silmaril.Compile.Target.RegAlloc in
/-- The direct proof of `renumber`: its numbering has a liveness certificate (open; a
conjecture until proved: an LCF-style checker is the alternative). -/
def renumber_certified : Prop :=
  ∀ (k : Nat) (p : Prog Nat), ∃ live, LiveCert p (renumberσ k p) live

/-! ## triangle -/

/-- On a fragment where Core realises a C semantics, valid direct lowerings to Mir factor
through Core (proved). -/
def triangle_factor : Prop :=
  ∀ (S : C.Sem.Semantics) (F : Set Silmaril.Cerberus.Ail.TypedProgram)
    (elaborate : Silmaril.Cerberus.Ail.TypedProgram → Silmaril.Cerberus.Core.Dynamics.Program),
    (∀ p ∈ F, Core.beh (elaborate p) = S p) → ∀ (cfg : Mir.Config) (ctl : Nat), ∀ p ∈ F,
      ∀ m, Valid (Core.cAM S cfg ctl) p m →
        ∃ q, Valid (Core.cAC S) p q ∧ Valid (Core.cCM cfg ctl) q m

/-! ## ccomp -/

/-- **Goal 1, per program** (translation validation, scored): whenever the validator accepts a
program, ccomp compiles it to Mir validly and non-vacuously under C0 (open; the stub validator
makes it trivial, so the evaluator scores it only once `checkC0` accepts a corpus program, and
then counts the accepted programs as `tv_accepted`). -/
def ccomp_tv_sound : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, checkC0 p = true →
    ∃ us, ccompMir p = some us ∧
      Valid (Core.cAM C0.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

/-- **Goal 1, for all programs** (stretch, not scored): ccomp's front end is valid and
non-vacuous on every C0 program that calls no external function. -/
def ccomp_c0_valid_all : Prop :=
  ∀ p : Silmaril.Cerberus.Ail.TypedProgram, C0.InFragment p → C0.externals p = [] →
    ∀ us, ccompMir p = some us →
      Valid (Core.cAM C0.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty

/-! ## core -/

/-- **Core realises C0** where the C0-only elaboration answers (open; scored once `elabC0`
elaborates a corpus program, counted as `core_realised`): the hypothesis of `C.Sem.factor` on
`{p | (elabC0 p).isSome}`, so on those programs ccomp's direct route and the Core route have the
same valid lowerings. Exact realisation is needed (`Realises`), so the elaboration must decline
programs whose Core behaviours differ from C0's (unsequenced orders C0 fixes, unspecified values
where C0 reports undefined behaviour). -/
def c0_core_realises : Prop :=
  ∀ (p : Silmaril.Cerberus.Ail.TypedProgram) (q : Silmaril.Cerberus.Core.Dynamics.Program),
    elabC0 p = some q → C0.InFragment p ∧ Core.beh q = C0.beh p

end Silmaril.Compile.Targets
