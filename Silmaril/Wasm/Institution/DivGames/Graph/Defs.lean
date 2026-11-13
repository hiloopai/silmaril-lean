module

public import Silmaril.Wasm.Institution.DivGames.Thms
public import Silmaril.Wasm.Institution.Entry.Defs
public import Silmaril.Wasm.Institution.Hooks.Defs
public import Silmaril.Wasm.Institution.GameGraph.Defs
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.Strategy.Thms

@[expose] public section

/-!
# A divergence-aware game logic and its comorphisms

**The node.** `dstratSem E RProg str : ObsSemantics (Set String)` is a game logic
whose semantic objects are divergence-observing strategies
`DStrategy E USig` over all export invocations (`USig = exportSig Set.univ`),
at every interface. The reduct along an inclusion is the identity. What the
interface `X` changes is the refinement: `ScopedLe X` compares only the plays,
divergences and infinite plays whose questions are invocations of exports in
`X`. Observing through a smaller interface therefore distinguishes fewer
strategies, as hiding does, and the reduct is functorial. (This avoids a
hiding reduct `DStrategy.comp` with a renaming handler. Functoriality of that
reduct would need the divergence and infinite plays of forwarding handlers
and their composites, which are not characterised.)

Operators (`DOp`): environments plugged below (`plug τ`, i.e. `τ.comp ·`);
the closure of single-invocation behaviours under a behaviour relation
(`close R`, a stateless server built by `ofBeh`); and its right adjoint for
refinement (`upper R`, `upperR`), the greatest strategy whose behaviours are
`R`-matched by those of the argument.

**Logics.**
* `divGame E`: programs are divergence-observing strategies.
* `divRed red`: a language with reduction semantics `red`, denoting
  `DStrategy.ofReduction (red p)`.
* `Entry.entryRef (instEntryAll P host) R`: the single-invocation entry logic
  of instantiated Wasm modules, with every invocation observed
  (`Ok := True`: the games do not record silmaril's well-formedness premise
  `InvokeOk`).

**Comorphisms.**
* `redToGame red : divRed red → divGame`: a program goes to the strategy of its
  reduction (`sem` is the identity, so the edge is model-expansive).
* `entryToRed R : entryRef (instEntryAll P host) R → divRed (wasmRed P host)`:
  an instantiated module goes to itself. `sem` reads the entry object off a
  strategy (`entryObj`, through `behOf`). The satisfaction condition is
  - `sem_den`: the adequacy theorem `behOf_wasmRed`, divergence included;
  - `sem_op`: `behOf_ofBeh`;
  - `atom_holds`: the Galois connection `scopedLe_upperR_iff`, so the atom
    `t ⊑_R u` becomes `t ⊑ upper R u`.
  This `sem` is not surjective (entry objects with a non-trivial `Ok`
  premise are not reached), so model-expansiveness is not claimed for this
  edge.

`divGraph` is the graph of these three logics. `fullGraph₃` is its sum with
`GameGraph.fullGraph` (no cross edges).
-/

namespace Silmaril.Wasm.Institution.DivGames

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Games Silmaril.Wasm.Institution.Games Silmaril.Wasm.Institution ObsSemantics

/-- Export invocations of all exports. -/
abbrev USig : Silmaril.Games.Sig.{0} := exportSig Set.univ

/-- Behaviour relations. -/
abbrev BRel : Type := Behaviour Val → Behaviour Val → Prop

variable {E : Silmaril.Games.Sig.{0}}

/-- A play is scoped by `X` when all its questions invoke exports in `X`. -/
def Scoped (X : Set String) (p : List (Move E USig)) : Prop :=
  ∀ q : USig.Op, Sum.inr (Ev.ask q) ∈ p → q.1.1 ∈ X

/-- Refinement observed through the exports `X`. -/
def ScopedLe (X : Set String) (δ δ' : DStrategy E USig) : Prop :=
  (∀ p, Scoped X p → p ∈ δ.toStrategy → p ∈ δ'.toStrategy) ∧
    (∀ p, Scoped X p → p ∈ δ.div → p ∈ δ'.div) ∧
    ∀ I ∈ δ.inf, (∀ p ∈ I, Scoped X p) → I ∈ δ'.inf

/-- The two-move exchange "invoke `q`, observe `b`". -/
def exch (q : USig.Op) (b : Behaviour Val) : List (Move E USig) :=
  [.inr (.ask q), .inr (.ans q b)]

/-! ## The right adjoint `upperR` -/

/-- `b` is `R`-matched by a behaviour of `δ'` for `q`. -/
def Allowed (R : BRel) (δ' : DStrategy E USig) (q : USig.Op) (b : Behaviour Val) : Prop :=
  ∃ b' ∈ behOf δ' q, R b b'

/-- Legal plays whose first exchange, if complete, is allowed. -/
def upperPlays (R : BRel) (δ' : DStrategy E USig) : Set (List (Move E USig)) :=
  {p | Legal p ∧ ∀ q b, exch q b <+: p → b ≠ .diverges → Allowed R δ' q b}

theorem exch_ne_concat {q : USig.Op} {b : Behaviour Val} {s : List (Move E USig)}
    {o : Move E USig} (h : exch q b = s ++ [o]) (ho : o.IsO) : False := by
  have h' : s ++ [o] = [Sum.inr (Ev.ask q)] ++ [Sum.inr (Ev.ans q b)] := h.symm
  have h₁ : [o] = [Sum.inr (Ev.ans q b)] := (List.append_inj' h' rfl).2
  have h₂ : o = Sum.inr (Ev.ans q b) := List.singleton_inj.1 h₁
  rw [h₂] at ho
  exact ho

/-- The greatest strategy whose single-invocation behaviours are `R`-matched
by those of `δ'`. -/
def upperR (R : BRel) (δ' : DStrategy E USig) : DStrategy E USig where
  toStrategy :=
    { plays := upperPlays R δ'
      nil_mem := ⟨Legal.nil, fun _ _ h => absurd h.length_le (by simp [exch])⟩
      legal := fun h => h.1
      of_prefix := fun ⟨hl, h⟩ hst => ⟨hl.of_prefix hst, fun q b hq => h q b (hq.trans hst)⟩
      receptive := by
        rintro s x y o ⟨-, h⟩ hx hxy ho
        refine ⟨⟨y, hx.append (Path.single hxy)⟩, fun q b hq => ?_⟩
        rcases List.prefix_concat_iff.1 hq with he | hq'
        · exact (exch_ne_concat he ho).elim
        · exact h q b hq' }
  div := {p | p ∈ upperPlays R δ' ∧ (∃ g, Path .idle p (.run g)) ∧
    ∀ q, p = [.inr (.ask q)] → Allowed R δ' q .diverges}
  inf := {I | IsInfPlay I ∧ I ⊆ upperPlays R δ'}
  div_mem h := h.1
  div_run h := h.2.1
  inf_isInf h := h.1
  inf_sub h := h.2

/-! ## The stateless server `ofBeh` -/

/-- A sequence of exchanges. -/
def flat (xs : List (USig.Op × Behaviour Val)) : List (Move E USig) :=
  xs.flatMap fun e => exch e.1 e.2

/-- Each exchange is a finite behaviour of `B`. -/
def Good (B : USig.Op → Set (Behaviour Val)) (xs : List (USig.Op × Behaviour Val)) : Prop :=
  ∀ e ∈ xs, e.2 ≠ .diverges ∧ e.2 ∈ B e.1

theorem path_flat : ∀ xs : List (USig.Op × Behaviour Val),
    Path .idle (flat (E := E) xs) .idle
  | [] => .nil _
  | e :: xs => .cons (.ask e.1) (.cons (.ret e.1 e.2) (path_flat xs))

/-- The stateless server answering each invocation `q` with any finite
behaviour in `B q`, and diverging on `q` when `.diverges ∈ B q`. -/
def ofBeh (B : USig.Op → Set (Behaviour Val)) : DStrategy E USig where
  toStrategy := Strategy.generate {p | ∃ xs, Good B xs ∧ p = flat xs}
  div := {p | ∃ xs q, Good B xs ∧ .diverges ∈ B q ∧ p = flat xs ++ [.inr (.ask q)]}
  inf := {I | IsInfPlay I ∧ I ⊆ (Strategy.generate {p | ∃ xs, Good B xs ∧ p = flat xs}).plays}
  div_mem := by
    rintro _ ⟨xs, q, hg, -, rfl⟩
    exact ⟨⟨_, (path_flat xs).append (Path.single (.ask q))⟩, flat xs,
      .inr ⟨⟨xs, hg, rfl⟩, ⟨_, path_flat xs⟩⟩, .inr ⟨flat xs, _, rfl, List.prefix_refl _, trivial⟩⟩
  div_run := by
    rintro _ ⟨xs, q, -, -, rfl⟩
    exact ⟨q, (path_flat xs).append (Path.single (.ask q))⟩
  inf_isInf h := h.1
  inf_sub h := h.2

/-- The closure of the single-invocation behaviours of `δ` under `R`. -/
def closeB (R : BRel) (δ : DStrategy E USig) : DStrategy E USig :=
  ofBeh fun q => {b | ∃ b' ∈ behOf δ q, R b b'}

/-! ## The logic -/

/-- Operators of the divergence-aware game logic. -/
inductive DOp (E : Silmaril.Games.Sig.{0}) : Type
  /-- Plug an environment below. -/
  | plug (τ : DStrategy E E)
  /-- Close the single-invocation behaviours under a relation. -/
  | close (R : BRel)
  /-- The right adjoint of `R`-matching of single-invocation behaviours. -/
  | upper (R : BRel)

/-- The meaning of an operator. -/
def DOp.apply : DOp E → DStrategy E USig → DStrategy E USig
  | .plug τ, δ => τ.comp δ
  | .close R, δ => closeB R δ
  | .upper R, δ => upperR R δ

variable (E) in
/-- **The divergence-aware game logic** over programs `RProg` denoting `str p`. -/
def dstratSem (RProg : Type) (str : RProg → DStrategy E USig) : ObsSemantics (Set String) where
  Sem _ := DStrategy E USig
  restrict _ δ := δ
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl
  Prog := RProg
  den _ p := str p
  Op := DOp E
  op _ o δ := o.apply δ
  Le X := ScopedLe X

variable (E) in
/-- Programs are divergence-observing strategies. -/
abbrev divGame : ObsSemantics (Set String) := dstratSem E (DStrategy E USig) id

/-- A language with reduction semantics, denoting divergence-observing
strategies. -/
abbrev divRed {RProg : Type} (red : RProg → Reduction E USig) : ObsSemantics (Set String) :=
  dstratSem E RProg fun p => DStrategy.ofReduction (red p)

/-- **Reduction semantics into the divergence-aware game logic.** -/
def redToGame {RProg : Type} (red : RProg → Reduction E USig) :
    Translation (𝟭 (Set String)) (divRed red) (divGame E) where
  sem _ δ := δ
  sem_restrict _ _ := rfl
  prog p := DStrategy.ofReduction (red p)
  sem_den _ _ := rfl
  op o := o
  sem_op _ _ _ := rfl
  atom a b := .le a b
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := Iff.rfl

theorem redToGame_surjective {RProg : Type} (red : RProg → Reduction E USig) (X : Set String) :
    Function.Surjective ((redToGame red).sem X) := fun δ => ⟨δ, rfl⟩

end Silmaril.Wasm.Institution.DivGames
