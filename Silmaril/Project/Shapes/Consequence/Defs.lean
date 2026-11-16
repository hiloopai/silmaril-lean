module

public import Silmaril.Project.Defs
public import Silmaril.Project.Registry.Consequence.Defs
public import Silmaril.Logic.Consequence.Defs
public import Silmaril.Logic.Consequence.Gentzen.Defs
public import Silmaril.Logic.Consequence.Structural.Defs
public import Silmaril.Logic.Consequence.Interp.Defs
public import Silmaril.Logic.Consequence.Shape.Defs

/-!
# Standard problem shapes: consequence systems

The questions a project asks about its consequence systems (`S : Silmaril.Consequence.System
Ax C`, that is `Ax → C → Prop`, `S Γ φ` read "`Γ ⊢ φ`", registered with
`silmaril consequence_system`), as problems over arguments. Each
shape keeps the context `Γ` and the conclusion `φ` as its last arguments, so an instance that
fixes the systems (and maps, and `ff`) is a problem over contexts and conclusions, and its SZS
statuses are the usual questions. `Silmaril.Project.Shapes.Consequence.Thms` proves each reading
below for exactly the binders that remain, in order (so for an empty type of contexts, THM and
UNS of `derives S` both hold, and SAT and CSA both fail — nothing is assumed nonempty):

| name | statement | THM | SAT | UNS | CSA |
|---|---|---|---|---|---|
| `silmaril.shapes.consequence.derives` | `Derives S Γ φ`: `S Γ φ` | `S` is universal | `S` derives something | `S` is empty | `S` is not universal |
| `silmaril.shapes.consequence.context_universal` | `ContextUniversal S Γ`: `∀ φ, S Γ φ` | every context derives every conclusion | some context derives every conclusion | no context derives every conclusion | some context does not derive every conclusion |
| `silmaril.shapes.consequence.derives_bottom` | `DerivesBottom S ff Γ`: `S Γ ff` | every context derives `ff` | some context derives `ff` | no context derives `ff` | some context does not derive `ff` |
| `silmaril.shapes.consequence.sound_at` | `SoundAt S T Γ φ`: `S Γ φ → T Γ φ` | `S` is sound for `T`: `S ≤ T` | | | a counterexample: `S Γ φ`, not `T Γ φ` |
| `silmaril.shapes.consequence.complete_at` | `CompleteAt S T Γ φ`: `T Γ φ → S Γ φ` | `S` is complete for `T`: `T ≤ S` | | | a counterexample: `T Γ φ`, not `S Γ φ` |
| `silmaril.shapes.consequence.complete_within_at` | `CompleteWithinAt S T μ b Γ φ`: `μ Γ φ ≤ b → T Γ φ → S Γ φ` | `S` is complete for `T` on the pairs with `μ Γ φ ≤ b` | | | a counterexample within the bound |
| `silmaril.shapes.consequence.translates_at` | `TranslatesAt S T f g Γ φ`: `S Γ φ → T (f Γ) (g φ)` | `(f, g)` preserves consequence | | | a consequence it does not preserve |
| `silmaril.shapes.consequence.reflects_at` | `ReflectsAt S T f g Γ φ`: `T (f Γ) (g φ) → S Γ φ` | `(f, g)` reflects consequence (conservativity) | | | a translated consequence whose source is not one |

`silmaril.shapes.consequence.tarski_closed S` (`Structural.Closed tarskiRules S`) certifies that a
list-premise system satisfies identity, weakening along list inclusion and cut.

`silmaril.shapes.consequence.gentzen_closed rs S` (`Gentzen.Closed rs S`, closed once `rs` and
`S` are fixed) certifies that a sequent relation `S : Gentzen.Seq C` is closed under the rule
profile `rs` (`Gentzen.defaultRules`, `withWeakening W`, …): THM certified, UNS (a closed
refutation) not closed. A list-to-list system is only a *raw* sequent relation until such a
problem is proved.

`silmaril.shapes.consequence.artifact_defined X I e` (closed once fixed) certifies that the
CID-pinned bytes of the registered value `X` decode **and** the partial interpretation `I` is
defined on the decoded value at the configuration `e`: THM. Its refutation (UNS) says only that
this does not hold — the bytes do not decode, *or* the reading is undefined; separate decode
evidence (the value's `.is`) tells the two apart. A system read through `I.orBot e` that derives
nothing is a *defined, empty* system only with this certificate and an established emptiness
(`derives` UNS over all contexts and conclusions).

**Shape evidence** (closed once the system is fixed; each is a core predicate of
`Silmaril.Logic.Consequence.Shape`, not restated): `context_free S` (`ContextFree`: what a
context derives does not depend on the context), `conclusion_free S` (`ConclusionFree`),
`supported_ax S tt` / `supported_c S ff` (`SupportedAx`/`SupportedC`: every judgement has the
context `tt` / the conclusion `ff`; a different property from context- or conclusion-freeness),
and for list contexts, per conclusion `c`, the checker `fun Γ => S Γ c` is `ListPred.PermInv`
(`ctx_perm_inv`), `ListPred.SetInv` (`ctx_set_inv`), `ListPred.UpClosed` (`ctx_up_closed`: left
`⊆`-weakening) or `ListPred.AppendExtensive` (`ctx_append_extensive`; not `AppendClosed`).

Fixing `Γ` too (`derives S (Γ := …)`) asks about one context: THM says `Γ` derives every
conclusion (`Γ` is **context-universal**), CSA that some conclusion is not derived. Fixing `φ`
as well is the **member judgment** `Γ ⊢ φ`: THM true, CSA false (at arity 0 an UNS answer is
a CSA), no answer unknown.

**Three different properties, never one "inconsistent".** *Universal* (`derives` THM) says
every context derives every conclusion; *context-universal* (`context_universal` with `Γ`
fixed, or `derives` with `Γ` fixed, THM) says one context does; *derives `ff`*
(`derives_bottom`, for a chosen conclusion `ff`) says a context derives that conclusion. They
coincide only under structural rules a system may not have (for instance, `ff ⊢ φ` for every
`φ` and cut). The explorer and these docs name each one, never an unqualified
"inconsistent".

**Directions.** `sound_at S T` is `S ≤ T` (every consequence of `S` is one of `T`): a derivation
system `S` is sound for its target `T`; `complete_at S T` is the converse inclusion. A CSA
answer whose proof is a literal `⟨Γ, φ, h⟩` records `Γ` and `φ` as its witnesses.

**Unknown is not false.** Derivability is undecidable in general; a problem with no answer is
unknown, and only a Lean proof changes that.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Consequence

open Silmaril.Consequence (System)

/-- **`Γ ⊢ φ` in `S`.** -/
@[problem "silmaril.shapes.consequence.derives" (title := "A context derives a conclusion")]
def Derives {Ax C : Type} (S : System Ax C) (Γ : Ax) (φ : C) : Prop := S Γ φ

/-- **`Γ` derives every conclusion in `S`.** -/
@[problem "silmaril.shapes.consequence.context_universal"
  (title := "A context derives every conclusion")]
def ContextUniversal {Ax C : Type} (S : System Ax C) (Γ : Ax) : Prop := ∀ φ, S Γ φ

/-- **`Γ` derives the chosen conclusion `ff` in `S`.** -/
@[problem "silmaril.shapes.consequence.derives_bottom"
  (title := "A context derives a chosen conclusion ff")]
def DerivesBottom {Ax C : Type} (S : System Ax C) (ff : C) (Γ : Ax) : Prop := S Γ ff

/-- **Soundness at `(Γ, φ)`**: if `Γ ⊢ φ` in `S` then in `T`. -/
@[problem "silmaril.shapes.consequence.sound_at" (title := "A system is sound for another")]
def SoundAt {Ax C : Type} (S T : System Ax C) (Γ : Ax) (φ : C) : Prop := S Γ φ → T Γ φ

/-- **Completeness at `(Γ, φ)`**: if `Γ ⊢ φ` in `T` then in `S`. -/
@[problem "silmaril.shapes.consequence.complete_at" (title := "A system is complete for another")]
def CompleteAt {Ax C : Type} (S T : System Ax C) (Γ : Ax) (φ : C) : Prop := T Γ φ → S Γ φ

/-- **Bounded completeness at `(Γ, φ)`**: if `μ Γ φ ≤ b` and `Γ ⊢ φ` in `T`, then in `S`. -/
@[problem "silmaril.shapes.consequence.complete_within_at"
  (title := "A system is complete for another within a measure bound")]
def CompleteWithinAt {Ax C : Type} (S T : System Ax C) (μ : Ax → C → ℕ) (b : ℕ) (Γ : Ax) (φ : C) :
    Prop := μ Γ φ ≤ b → T Γ φ → S Γ φ

/-- **A list-premise system satisfies identity, weakening and cut** (`Structural.Closed
Structural.tarskiRules`: a premise is a consequence, premises may be added along list inclusion,
and finite multi-cut). -/
@[problem "silmaril.shapes.consequence.tarski_closed"
  (title := "A system satisfies identity, weakening and cut")]
def TarskiClosed {C : Type} (S : System (List C) C) : Prop :=
  Silmaril.Consequence.Structural.Closed Silmaril.Consequence.Structural.tarskiRules S

/-- **A sequent relation is closed under a Gentzen rule profile.** -/
@[problem "silmaril.shapes.consequence.gentzen_closed"
  (title := "A sequent relation is closed under a Gentzen rule profile")]
def GentzenClosed {C : Type} (rs : Silmaril.Consequence.Gentzen.Rules C)
    (S : Silmaril.Consequence.Gentzen.Seq C) : Prop :=
  Silmaril.Consequence.Gentzen.Closed rs S

/-- **An artifact is read by a partial interpretation**: its bytes decode to `v` with `I e v`
defined. -/
@[problem "silmaril.shapes.consequence.artifact_defined"
  (title := "An artifact's bytes decode and a partial interpretation is defined on them")]
def ArtifactDefined {Env V : Type} {Ax C : Env → Type} (X : Silmaril.Project.Value V)
    (I : Silmaril.Consequence.Interp Env V Ax C) (e : Env) : Prop :=
  ∃ v, X.parse = some v ∧ I.Defined e v

/-- **Context-free**: `Silmaril.Consequence.ContextFree S`. -/
@[problem "silmaril.shapes.consequence.context_free" (title := "What a context derives does not depend on it")]
def ContextFreeShape {Ax C : Type} (S : System Ax C) : Prop := Silmaril.Consequence.ContextFree S

/-- **Conclusion-free**: `Silmaril.Consequence.ConclusionFree S`. -/
@[problem "silmaril.shapes.consequence.conclusion_free" (title := "Whether a context derives does not depend on the conclusion")]
def ConclusionFreeShape {Ax C : Type} (S : System Ax C) : Prop := Silmaril.Consequence.ConclusionFree S

/-- **Supported at the context `tt`**: `Silmaril.Consequence.SupportedAx S tt`. -/
@[problem "silmaril.shapes.consequence.supported_ax" (title := "Every judgement has a designated context")]
def SupportedAxShape {Ax C : Type} (S : System Ax C) (tt : Ax) : Prop := Silmaril.Consequence.SupportedAx S tt

/-- **Supported at the conclusion `ff`**: `Silmaril.Consequence.SupportedC S ff`. -/
@[problem "silmaril.shapes.consequence.supported_c" (title := "Every judgement has a designated conclusion")]
def SupportedCShape {Ax C : Type} (S : System Ax C) (ff : C) : Prop := Silmaril.Consequence.SupportedC S ff

/-- **Permutation-invariant contexts**: each conclusion's checker is `ListPred.PermInv`. -/
@[problem "silmaril.shapes.consequence.ctx_perm_inv" (title := "Contexts may be permuted")]
def CtxPermInv {α C : Type} (S : System (List α) C) : Prop :=
  ∀ c, Silmaril.Consequence.ListPred.PermInv (fun Γ => S Γ c)

/-- **Set-invariant contexts**: each conclusion's checker is `ListPred.SetInv`. -/
@[problem "silmaril.shapes.consequence.ctx_set_inv" (title := "Contexts are read as sets")]
def CtxSetInv {α C : Type} (S : System (List α) C) : Prop :=
  ∀ c, Silmaril.Consequence.ListPred.SetInv (fun Γ => S Γ c)

/-- **Up-closed contexts** (left `⊆`-weakening): each conclusion's checker is `ListPred.UpClosed`. -/
@[problem "silmaril.shapes.consequence.ctx_up_closed" (title := "Contexts may be weakened (⊆)")]
def CtxUpClosed {α C : Type} (S : System (List α) C) : Prop :=
  ∀ c, Silmaril.Consequence.ListPred.UpClosed (fun Γ => S Γ c)

/-- **Append-extensive contexts**: each conclusion's checker is `ListPred.AppendExtensive`. -/
@[problem "silmaril.shapes.consequence.ctx_append_extensive" (title := "Contexts may be extended by appending")]
def CtxAppendExtensive {α C : Type} (S : System (List α) C) : Prop :=
  ∀ c, Silmaril.Consequence.ListPred.AppendExtensive (fun Γ => S Γ c)

/-- **A translation preserves `Γ ⊢ φ`**: from `S` to `T` along `f` on contexts and `g` on
conclusions. -/
@[problem "silmaril.shapes.consequence.translates_at"
  (title := "A translation preserves consequence")]
def TranslatesAt {Ax C Bx D : Type} (S : System Ax C) (T : System Bx D) (f : Ax → Bx)
    (g : C → D) (Γ : Ax) (φ : C) : Prop := S Γ φ → T (f Γ) (g φ)

/-- **A translation reflects `Γ ⊢ φ`**: if the translation of `Γ ⊢ φ` holds in `T`, then
`Γ ⊢ φ` holds in `S`. -/
@[problem "silmaril.shapes.consequence.reflects_at"
  (title := "A translation reflects consequence")]
def ReflectsAt {Ax C Bx D : Type} (S : System Ax C) (T : System Bx D) (f : Ax → Bx)
    (g : C → D) (Γ : Ax) (φ : C) : Prop := T (f Γ) (g φ) → S Γ φ

end Silmaril.Project.Shapes.Consequence
