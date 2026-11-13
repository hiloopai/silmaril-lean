module

public import Silmaril.Wasm.Institution.DivGames.Graph.Defs
public import Silmaril.Proofs.Wasm.Institution.DivGames.Graph

@[expose] public section

/-!
# The entry comorphism and the divergence-aware logic graph

* `instEntryAll P host`: the single-invocation entry points of instantiated
  modules, with every invocation observed (`Ok := True`). The behaviours are
  silmaril's (`instEntry`).
* `entryToRed P host R`: **a comorphism from the entry logic
  `Entry.entryRef (instEntryAll P host) R` into the divergence-aware game logic
  of the Wasm reduction** (`divRed (wasmRed P host)`). An instantiated module
  goes to itself, and its game denotation is `DStrategy.ofReduction (wasmRed
  P host w)`. The satisfaction condition holds by:
  - `sem_den`: `behOf_wasmRed`, single-invocation adequacy with divergence;
  - `sem_op`: `behOf_ofBeh`;
  - `atom_holds`: `scopedLe_upperR_iff`.
* `divGraph P host R`: the logics `entry → red → game`. `fullGraph₃` is
  `GameGraph.fullGraph` plus `divGraph` (`LogicGraph.sum`, no cross edges).
* `valid_entry_iff`: validity of the entry sentence `w ⊑ w'` at `X` is scoped
  refinement of the game denotation of `w` below `upperR R` of that of `w'`.
  Through `redToGame`, validity in `divRed` is validity in `divGame`
  (`valid_redToGame_iff`, model-expansive borrowing).
-/

namespace Silmaril.Wasm.Institution.DivGames

open CategoryTheory Silmaril.Logic.Institution Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics Silmaril.Games Silmaril.Wasm.Institution.Games Silmaril.Wasm.Institution
open ObsSemantics

variable {H : Type} (P : Profile) (host : HostSemantics H)

/-- Single-invocation entry points of instantiated modules, every invocation
observed. -/
def instEntryAll : Equiv.EntryPoints (Inst H) String Val :=
  ⟨fun _ _ _ => True, (instEntry P host).beh⟩

/-- The entry object read off a divergence-observing strategy. -/
def entryObj (X : Set String) (δ : DStrategy Silmaril.Games.Sig.empty USig) :
    Entry.Obj String Val X :=
  ⟨fun _ _ => True, fun x vs => behOf δ ⟨(x.1, vs), trivial⟩⟩

/-- The Wasm reduction, at the full export signature. -/
abbrev wasmRedU : Inst H → Reduction Silmaril.Games.Sig.empty USig := wasmRed P host

theorem refines_entryObj_iff {X : Set String} {R : BRel} {δ δ' : DStrategy Silmaril.Games.Sig.empty USig} :
    Entry.Refines R (entryObj X δ) (entryObj X δ') ↔
      ∀ q : USig.Op, q.1.1 ∈ X → Behaviours.Refines R (behOf δ q) (behOf δ' q) :=
  ⟨fun h q hq => h ⟨q.1.1, hq⟩ q.1.2 trivial, fun h x vs _ => h ⟨(x.1, vs), trivial⟩ x.2⟩

/-- **The entry comorphism**; see the module documentation. -/
def entryToRed (R : BRel) :
    Translation (𝟭 (Set String)) (Entry.entryRef (instEntryAll P host) R)
      (divRed (wasmRedU P host)) where
  sem X δ := entryObj X δ
  sem_restrict _ _ := rfl
  prog w := w
  sem_den X w := by
    show entryObj X _ = ⟨_, _⟩
    simp only [entryObj, Entry.Obj.mk.injEq]
    exact ⟨rfl, funext fun x => funext fun vs => behOf_wasmRed P host w x.1 vs⟩
  op R' := DOp.close R'
  sem_op X R' δ := by
    show entryObj X (closeB R' δ) = ⟨_, _⟩
    simp only [entryObj, closeB, Entry.Obj.mk.injEq, true_and]
    funext x vs
    exact behOf_ofBeh _ _
  atom t u := .le t (.app (DOp.upper R) u)
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := scopedLe_upperR_iff.trans refines_entryObj_iff.symm

/-! ## The graph -/

/-- Logics of the divergence-aware graph. -/
inductive DNode where
  /-- The single-invocation entry logic of instantiated modules. -/
  | entry
  /-- The divergence-aware logic of the Wasm reduction. -/
  | red
  /-- The divergence-aware game logic. -/
  | game

/-- The semantics of a node. -/
def dsem (R : BRel) : DNode → ObsSemantics (Set String)
  | .entry => Entry.entryRef (instEntryAll P host) R
  | .red => divRed (wasmRedU P host)
  | .game => divGame Silmaril.Games.Sig.empty

/-- Comorphism edges. -/
inductive DEdge : DNode → DNode → Type where
  | entryRed : DEdge .entry .red
  | redGame : DEdge .red .game

/-- The translation of an edge. -/
def dedge (R : BRel) :
    {a b : DNode} → DEdge a b → Translation (𝟭 (Set String)) (dsem P host R a) (dsem P host R b)
  | _, _, .entryRed => entryToRed P host R
  | _, _, .redGame => redToGame (wasmRedU P host)

/-- **The divergence-aware logic graph.** -/
def divGraph (R : BRel) : Silmaril.Inst.LogicGraph₁ where
  Logics := DNode
  inst a := (dsem P host R a).inst
  Comor := DEdge
  comor e := (dedge P host R e).coHom
  Mor _ _ := PEmpty
  mor e := e.elim

/-- The reduction-to-game edge is model-expansive. -/
theorem redGame_modelExpansive (R : BRel) :
    ((divGraph P host R).comor DEdge.redGame).ModelExpansive :=
  (redToGame (wasmRedU P host)).coHom_modelExpansive (redToGame_surjective _)

/-- **The Wasm logic graph with reduction, game and divergence-aware game
semantics**: `GameGraph.fullGraph` and `divGraph`, with no cross edges. -/
def fullGraph₃ (Env : Module → Store H → List ExternAddr → Prop) (R : BRel) :
    Silmaril.Inst.LogicGraph₁ :=
  LogicGraph.sum (GameGraph.fullGraph P host Env) (divGraph P host R) (fun _ _ => PEmpty)
    (fun e => e.elim)

/-! ## Validity -/

/-- Validity of the entry sentence `w ⊑ w'` at `X`. -/
theorem valid_entry_iff (R : BRel) (X : Set String) (w w' : Inst H) :
    (Entry.entryRef (instEntryAll P host) R).Valid ((Entry.entryRef (instEntryAll P host) R).leSen X w w') ↔
      ScopedLe X (DStrategy.ofReduction (wasmRedU P host w))
        (upperR R (DStrategy.ofReduction (wasmRedU P host w'))) := by
  have h₁ : Entry.den (instEntryAll P host) X w =
      entryObj X (DStrategy.ofReduction (wasmRedU P host w)) :=
    ((entryToRed P host R).sem_den X w).symm
  have h₂ : Entry.den (instEntryAll P host) X w' =
      entryObj X (DStrategy.ofReduction (wasmRedU P host w')) :=
    ((entryToRed P host R).sem_den X w').symm
  refine ((Entry.entryRef (instEntryAll P host) R).valid_leSen_iff X w w').trans ?_
  show Entry.Refines R (Entry.den (instEntryAll P host) X w) (Entry.den (instEntryAll P host) X w') ↔ _
  rw [h₁, h₂]
  exact refines_entryObj_iff.trans scopedLe_upperR_iff.symm

/-- Borrowing along `redToGame`: validity in the divergence-aware reduction
logic is validity of the translated sentence in the divergence-aware game
logic. -/
theorem valid_redToGame_iff {K : Silmaril.Wasm.Institution.Sig (Set String)}
    (s : Sen (divRed (wasmRedU P host)) K) :
    (divRed (wasmRedU P host)).Valid s ↔
      (divGame Silmaril.Games.Sig.empty).Valid ((redToGame (wasmRedU P host)).sen s) :=
  (redToGame (wasmRedU P host)).valid_iff (redToGame_surjective _) s

end Silmaril.Wasm.Institution.DivGames
