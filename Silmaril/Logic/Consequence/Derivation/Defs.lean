module

public import Silmaril.Logic.Consequence.Soundness.Defs

/-!
# Derivation systems: explicit proof objects, a checker, and the consequence they define

A **derivation system** `D : DerivationSystem J` has judgments `J`, rule labels `D.Rule`, and the
rule instances `D.Instance r ps c`: the rule `r` concludes `c` from the premises `ps`, in order.
A label names a rule *instance* and carries whatever data it needs (a witness term, a motive), so
that checking one step is a decidable question about the step alone.

**Proof objects.** Two explicit forms, both checked against `D.Instance`:

* trees (`ProofTree R J`): a leaf `assume j` uses an assumption; a node `infer r c ts` records its
  rule label, its conclusion and its subproofs. `D.Valid Γ t` says every node is an instance of
  its rule and every leaf is in `Γ`;
* indexed lines (`Line R J`), the shape of Alethe and of index-based (NDJSON) proof formats: a line
  is an assumption or a rule applied to *earlier* lines, cited by position. `D.LinesValid Γ ls`.

**The consequence.** `D.derives : System (List J) J` holds when a valid tree from `Γ` concludes
`c`; `D.proofs` is the same with the trees as data (a `WSystem`). `D.linearDerives` uses indexed
lines; the two agree (`Thms`).

**Checking.** With decidable equality on judgments and decidable instances, `D.check Γ t` and
`D.checkLines Γ ls` are Boolean checkers; `Thms` proves they decide validity exactly.

**Elaboration.** A concrete proof usually names its rules loosely (a rule name and a few
arguments) and lets the conclusions carry the rest. `ProofTree.elaborate f` turns such raw labels into
rule labels with an untrusted function `f`, which sees each node's premise conclusions and
conclusion; the result is then checked, so `f` is never trusted.

**Semantics.** A satisfaction relation on judgments `sat : M → J → Prop` makes `D` *locally
sound* (`LocallySound`) when every rule instance preserves truth in each model. `listSat M sat`
is the interpretation of `D.derives` (a model satisfies a list of assumptions when it satisfies
each); `Thms` proves local soundness gives `D.derives.SoundFor (listSat M sat)`, hence
consistency at every context with a model.
-/

@[expose] public section

namespace Silmaril.Consequence

universe u v w

/-- **A derivation system**: rule labels and their instances over judgments `J`. -/
structure DerivationSystem (J : Type u) where
  /-- Rule labels: each names a rule instance, with the data it needs. -/
  Rule : Type v
  /-- `Instance r ps c`: the rule `r` concludes `c` from the premises `ps`, in this order. -/
  Instance : Rule → List J → J → Prop

/-- **Proof trees**: assumptions at the leaves; each node records its rule, its conclusion and
its subproofs. -/
inductive ProofTree (R : Type v) (J : Type u) where
  /-- Use an assumption. -/
  | assume (j : J)
  /-- Conclude `c` by the rule `r` from the subproofs `ts`. -/
  | infer (r : R) (c : J) (ts : List (ProofTree R J))

/-- **Indexed proof lines**: an assumption, or a rule applied to earlier lines by position. -/
inductive Line (R : Type v) (J : Type u) where
  /-- Use an assumption. -/
  | assume (j : J)
  /-- Conclude `c` by the rule `r` from the earlier lines numbered `prems` (from `0`). -/
  | infer (r : R) (c : J) (prems : List ℕ)

namespace ProofTree

variable {R : Type v} {R' : Type w} {J : Type u}

/-- The conclusion of a proof tree. -/
def concl : ProofTree R J → J
  | assume j => j
  | infer _ c _ => c

mutual

/-- Replace every assumption leaf `assume j` by the proof `g j` (grafting). -/
def graft (g : J → ProofTree R J) : ProofTree R J → ProofTree R J
  | assume j => g j
  | infer r c ts => infer r c (graftAll g ts)

/-- `graft` on a list of subproofs. -/
def graftAll (g : J → ProofTree R J) : List (ProofTree R J) → List (ProofTree R J)
  | [] => []
  | t :: ts => graft g t :: graftAll g ts

end

mutual

/-- **Elaborate raw rule labels** with `f`, which sees the premise conclusions and the conclusion
of each node. Untrusted: the result is checked afterwards. -/
def elaborate (f : R → List J → J → Option R') : ProofTree R J → Option (ProofTree R' J)
  | assume j => some (assume j)
  | infer r c ts =>
    match elaborateAll f ts, f r (ts.map concl) c with
    | some ts', some r' => some (infer r' c ts')
    | _, _ => none

/-- `elaborate` on a list of subproofs. -/
def elaborateAll (f : R → List J → J → Option R') :
    List (ProofTree R J) → Option (List (ProofTree R' J))
  | [] => some []
  | t :: ts =>
    match elaborate f t, elaborateAll f ts with
    | some t', some ts' => some (t' :: ts')
    | _, _ => none

end

mutual

/-- Flatten a tree into indexed lines, after `base` earlier lines; the last line is the root. -/
def lines (base : ℕ) : ProofTree R J → List (Line R J)
  | assume j => [.assume j]
  | infer r c ts =>
    let (ls, ixs) := linesAll base ts
    ls ++ [.infer r c ixs]

/-- Flatten a list of subproofs after `base` earlier lines: their lines and their roots' indices. -/
def linesAll (base : ℕ) : List (ProofTree R J) → List (Line R J) × List ℕ
  | [] => ([], [])
  | t :: ts =>
    let l := lines base t
    let (ls, ixs) := linesAll (base + l.length) ts
    (l ++ ls, (base + l.length - 1) :: ixs)

end

end ProofTree

/-- The conclusion of a line. -/
def Line.concl {R : Type v} {J : Type u} : Line R J → J
  | .assume j => j
  | .infer _ c _ => c

namespace DerivationSystem

variable {J : Type u} (D : DerivationSystem.{u, v} J)

/-- The proof trees of `D`. -/
abbrev Proof := ProofTree D.Rule J

/-- **A valid proof tree from the assumptions `Γ`**: every leaf is in `Γ`, every node is an
instance of its rule on its subproofs' conclusions. -/
inductive Valid (Γ : List J) : D.Proof → Prop
  | assume {j : J} : j ∈ Γ → Valid Γ (.assume j)
  | infer {r : D.Rule} {c : J} {ts : List D.Proof} :
      D.Instance r (ts.map ProofTree.concl) c → (∀ t ∈ ts, Valid Γ t) → Valid Γ (.infer r c ts)

/-- **`Γ ⊢ c` in `D`**: some valid proof tree from `Γ` concludes `c`. -/
def derives : System (List J) J := fun Γ c => ∃ t : D.Proof, D.Valid Γ t ∧ t.concl = c

/-- The valid proof trees from `Γ` concluding `c`, as data. -/
def proofs : WSystem.{u, u, max u v} (List J) J :=
  fun Γ c => {t : D.Proof // D.Valid Γ t ∧ t.concl = c}

/-- The conclusions of the cited earlier lines, when every citation is in range. -/
def cite (prev : List J) : List ℕ → Option (List J)
  | [] => some []
  | i :: ixs =>
    match prev[i]?, cite prev ixs with
    | some p, some ps => some (p :: ps)
    | _, _ => none

/-- **Valid indexed lines**, after the earlier conclusions `prev`: each assumption is in `Γ`, and
each step is an instance of its rule on the conclusions of earlier lines. -/
def LinesValid (Γ : List J) : List J → List (Line D.Rule J) → Prop
  | _, [] => True
  | prev, .assume j :: ls => j ∈ Γ ∧ LinesValid Γ (prev ++ [j]) ls
  | prev, .infer r c ixs :: ls =>
    (∃ ps, cite prev ixs = some ps ∧ D.Instance r ps c) ∧
      LinesValid Γ (prev ++ [c]) ls

/-- **`Γ ⊢ c` by indexed lines**: some valid list of lines from `Γ` ends with `c`. -/
def linearDerives : System (List J) J :=
  fun Γ c => ∃ ls : List (Line D.Rule J), D.LinesValid Γ [] ls ∧ (ls.getLast?.map Line.concl) = some c

section Check

variable [DecidableEq J] [∀ r ps c, Decidable (D.Instance r ps c)]

mutual

/-- **Check a proof tree** from the assumptions `Γ`. -/
def check (Γ : List J) : D.Proof → Bool
  | .assume j => decide (j ∈ Γ)
  | .infer r c ts => decide (D.Instance r (ts.map ProofTree.concl) c) && checkAll Γ ts

/-- Check every subproof. -/
def checkAll (Γ : List J) : List D.Proof → Bool
  | [] => true
  | t :: ts => check Γ t && checkAll Γ ts

end

/-- **Check indexed lines** from the assumptions `Γ`, after the earlier conclusions `prev`. -/
def checkLines (Γ : List J) : List J → List (Line D.Rule J) → Bool
  | _, [] => true
  | prev, .assume j :: ls => decide (j ∈ Γ) && checkLines Γ (prev ++ [j]) ls
  | prev, .infer r c ixs :: ls =>
    (match cite prev ixs with
      | some ps => decide (D.Instance r ps c)
      | none => false) && checkLines Γ (prev ++ [c]) ls

end Check

/-- **Local soundness** for a satisfaction relation on judgments: every rule instance preserves
truth in every model. -/
def LocallySound {M : Type w} (sat : M → J → Prop) : Prop :=
  ∀ m r ps c, D.Instance r ps c → (∀ p ∈ ps, sat m p) → sat m c

end DerivationSystem

/-- **Elaborate raw labels of indexed lines** with `f`, which sees the cited conclusions and the
conclusion of each step. Untrusted, like `ProofTree.elaborate`. -/
def Line.elaborate {R : Type v} {R' : Type w} {J : Type u} (f : R → List J → J → Option R') :
    List J → List (Line R J) → Option (List (Line R' J))
  | _, [] => some []
  | prev, .assume j :: ls => (Line.elaborate f (prev ++ [j]) ls).map (.assume j :: ·)
  | prev, .infer r c ixs :: ls =>
    match (DerivationSystem.cite prev ixs).bind (f r · c), Line.elaborate f (prev ++ [c]) ls with
    | some r', some ls' => some (.infer r' c ixs :: ls')
    | _, _ => none

/-- **The interpretation of assumption lists**: a model satisfies a list when it satisfies each
judgment of it. -/
def listSat {J : Type u} (M : Type w) (sat : M → J → Prop) : Satisfaction.{u, u, w} (List J) J where
  Model := M
  satAx m Γ := ∀ j ∈ Γ, sat m j
  satC := sat

end Silmaril.Consequence
