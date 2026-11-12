module

public import Silmaril.SSA.LambdaRTL.Defs

/-!
# A flat three-address CFG for λRTL (acyclic stage)

The flat IR follows the three-address grammar of Ghalayini–Krishnaswami, *The Denotational
Semantics of SSA*, §2.1 (Fig. "Grammar for 3-address code"):

* blocks `β ::= x = o; β | (x, y) = o; β | τ` (`Body`);
* terminators `τ ::= br k v | case o {x ⇒ τ} {y ⇒ τ'}` (`Term`), with nested conditional
  terminators as in the paper. Two deliberate differences from the paper's grammar, both
  dictated by λRTL: `br k v` carries an argument (λRTL jumps pass a value; `ret v` is a `br`
  to an exit label), and the branches of `case` *assign* the payload to a register on entry
  (`x := ιₗ⁻¹ o` resp. `y := ιᵣ⁻¹ o`), since a λRTL `case o x r y s` binds `x`/`y`;
* a graph `G` is an entry body and a list of labelled blocks `(k, ⟨x, β⟩)`; a jump `br k v`
  to block `k` assigns the block's parameter register `x := v` and runs `β`.

**Acyclicity by list order.** A block may only jump *forward*: `jump` resolves a label in the
part of the block list *after* the current block, and a label that is not found there is an
**exit** of the graph (the same convention as a λRTL region's free labels). This makes `jump`
structurally recursive on the block list (no fuel, no well-founded order on labels), and a
backward jump is not a loop but an exit. Loops are a later stage (`docs/projects/ssa.md`).

**Flattening.** `flatten : Region V L F → CFG V (L ⊕ Path) F` erases the dominator tree into
labelled blocks. Block labels are tree paths `Path = List Bool` (cf. the structural block
addresses of the thesis formalisation, imbrem/thesis @69a8126,
`formalization/thesis/Isotope/TAC/Bridge/DomFlat.lean`, CC0; the construction here is new and
adapted to λRTL's binary `case`/`join`):

* `case o x r y s` at path `p` becomes the terminator
  `case o {x ⇒ br (p++[0]) x} {y ⇒ br (p++[1]) y}` and two blocks `p++[0] := ⟨x, r⟩`,
  `p++[1] := ⟨y, s⟩` (the case binder is the assignment at branch entry; the jump re-assigns
  the same value to the block parameter, which is idempotent);
* `join r ℓ x t` at path `p` continues the current block with `r` (at `p++[0]`, with `ℓ`
  resolved to `p++[1]`) and adds the block `p++[1] := ⟨x, t⟩` *after* all blocks of `r`;
* free labels `ℓ` become exits `Sum.inl ℓ`.

Blocks of a subtree precede the handler blocks of enclosing joins, so every internal jump is
forward. `CFG.toRegion` reads any (forward) CFG back as a λRTL region by nesting `join`s.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

deriving instance DecidableEq for Op

namespace CFG

universe v w

/-- Terminators `τ ::= br k v | case o {x ⇒ τ} {y ⇒ τ'}`. -/
inductive Term (V : Type w) (K : Type w) (F : Type v) : Type (max v w)
  | br (k : K) (a : Val V)
  | case (o : Op V F) (x : V) (t : Term V K F) (y : V) (u : Term V K F)
  deriving DecidableEq

/-- Basic-block bodies `β ::= x = o; β | (x, y) = o; β | τ`. -/
inductive Body (V : Type w) (K : Type w) (F : Type v) : Type (max v w)
  | let1 (x : V) (o : Op V F) (β : Body V K F)
  | let2 (x y : V) (o : Op V F) (β : Body V K F)
  | term (τ : Term V K F)
  deriving DecidableEq

/-- A block with its parameter register (assigned by incoming jumps). -/
structure Block (V : Type w) (K : Type w) (F : Type v) : Type (max v w) where
  param : V
  body : Body V K F
  deriving DecidableEq

/-- A flat CFG: a nameless entry block and a list of labelled blocks, in forward order. -/
structure _root_.Silmaril.SSA.LambdaRTL.CFG (V : Type w) (K : Type w) (F : Type v) :
    Type (max v w) where
  entry : Body V K F
  blocks : List (K × Block V K F)
  deriving DecidableEq

/-- Structural block addresses: paths in the dominator tree. -/
abbrev Path : Type := List Bool

section Syntax

variable {V K K' : Type w} {F F' : Type v}

/-- Jump targets of a terminator. -/
def Term.targets : Term V K F → List K
  | .br k _ => [k]
  | .case _ _ t _ u => t.targets ++ u.targets

/-- Jump targets of a body. -/
def Body.targets : Body V K F → List K
  | .let1 _ _ β | .let2 _ _ _ β => β.targets
  | .term τ => τ.targets

/-- Every label occurring in a block list (block labels and jump targets). -/
def blockLabels (bs : List (K × Block V K F)) : List K :=
  bs.flatMap fun kb => kb.1 :: kb.2.body.targets

/-- Every label occurring in a CFG. -/
def _root_.Silmaril.SSA.LambdaRTL.CFG.labels (g : CFG V K F) : List K :=
  g.entry.targets ++ blockLabels g.blocks

/-- Relabelling of a terminator. -/
def Term.relabel (π : K → K') : Term V K F → Term V K' F
  | .br k a => .br (π k) a
  | .case o x t y u => .case o x (t.relabel π) y (u.relabel π)

/-- Relabelling of a body. -/
def Body.relabel (π : K → K') : Body V K F → Body V K' F
  | .let1 x o β => .let1 x o (β.relabel π)
  | .let2 x y o β => .let2 x y o (β.relabel π)
  | .term τ => .term (τ.relabel π)

/-- Relabelling of a block. -/
def Block.relabel (π : K → K') (b : Block V K F) : Block V K' F :=
  ⟨b.param, b.body.relabel π⟩

/-- Relabelling of a CFG (block labels and jump targets). -/
def _root_.Silmaril.SSA.LambdaRTL.CFG.relabel (π : K → K') (g : CFG V K F) : CFG V K' F :=
  ⟨g.entry.relabel π, g.blocks.map fun kb => (π kb.1, kb.2.relabel π)⟩

/-- Renaming instruction symbols in a terminator. -/
def Term.mapOp (h : F → F') : Term V K F → Term V K F'
  | .br k a => .br k a
  | .case o x t y u => .case (o.mapOp h) x (t.mapOp h) y (u.mapOp h)

/-- Renaming instruction symbols in a body. -/
def Body.mapOp (h : F → F') : Body V K F → Body V K F'
  | .let1 x o β => .let1 x (o.mapOp h) (β.mapOp h)
  | .let2 x y o β => .let2 x y (o.mapOp h) (β.mapOp h)
  | .term τ => .term (τ.mapOp h)

/-- Renaming instruction symbols in a block. -/
def Block.mapOp (h : F → F') (b : Block V K F) : Block V K F' :=
  ⟨b.param, b.body.mapOp h⟩

/-- Renaming instruction symbols in a CFG. -/
def _root_.Silmaril.SSA.LambdaRTL.CFG.mapOp (h : F → F') (g : CFG V K F) : CFG V K F' :=
  ⟨g.entry.mapOp h, g.blocks.map fun kb => (kb.1, kb.2.mapOp h)⟩

/-! ### Reading a CFG back as a λRTL region -/

/-- A terminator as a region. -/
def Term.toRegion : Term V K F → Region V K F
  | .br k a => .br k a
  | .case o x t y u => .case o x t.toRegion y u.toRegion

/-- A body as a region. -/
def Body.toRegion : Body V K F → Region V K F
  | .let1 x o β => .let1 x o β.toRegion
  | .let2 x y o β => .let2 x y o β.toRegion
  | .term τ => τ.toRegion

/-- Close a region under the blocks of a list, innermost first:
`joinAll r [(k₁,b₁), …, (kₙ,bₙ)] = (…(r where k₁(x₁) ⇒ β₁)…) where kₙ(xₙ) ⇒ βₙ`. -/
def joinAll : Region V K F → List (K × Block V K F) → Region V K F
  | r, [] => r
  | r, kb :: bs => joinAll (.join r kb.1 kb.2.param kb.2.body.toRegion) bs

/-- A (forward) CFG as a λRTL region with labels `K`. -/
def _root_.Silmaril.SSA.LambdaRTL.CFG.toRegion (g : CFG V K F) : Region V K F :=
  joinAll g.entry.toRegion g.blocks

end Syntax

/-! ### Region label renaming -/

section MapLabel

variable {V L K : Type w} {F : Type v}

/-- Renaming the labels of a region (jump targets and join labels). -/
def _root_.Silmaril.SSA.LambdaRTL.Region.mapLabel (f : L → K) : Region V L F → Region V K F
  | .br ℓ a => .br (f ℓ) a
  | .let1 x o r => .let1 x o (r.mapLabel f)
  | .let2 x y o r => .let2 x y o (r.mapLabel f)
  | .case o x r y s => .case o x (r.mapLabel f) y (s.mapLabel f)
  | .join r ℓ x t => .join (r.mapLabel f) (f ℓ) x (t.mapLabel f)

end MapLabel

/-! ### Flattening a dominator tree -/

section Flatten

variable {V L : Type w} {F : Type v} [DecidableEq L]

/-- Resolution of a label: bound join labels go to their handler block, free labels exit. -/
def res (env : L → Option Path) (ℓ : L) : L ⊕ Path :=
  match env ℓ with
  | some q => .inr q
  | none => .inl ℓ

/-- The label environment inside the body of `join r ℓ x t` at path `p`. -/
def bindLabel (env : L → Option Path) (ℓ : L) (q : Path) : L → Option Path :=
  fun l => if l = ℓ then some q else env l

/-- The body of the current block for a subtree at path `p`. -/
def _root_.Silmaril.SSA.LambdaRTL.Region.entryBody :
    (L → Option Path) → Path → Region V L F → Body V (L ⊕ Path) F
  | env, _, .br ℓ a => .term (.br (res env ℓ) a)
  | env, p, .let1 x o r => .let1 x o (r.entryBody env p)
  | env, p, .let2 x y o r => .let2 x y o (r.entryBody env p)
  | _, p, .case o x _ y _ =>
      .term (.case o x (.br (.inr (p ++ [false])) (.var x)) y (.br (.inr (p ++ [true])) (.var y)))
  | env, p, .join r ℓ _ _ => r.entryBody (bindLabel env ℓ (p ++ [true])) (p ++ [false])

/-- The blocks generated by a subtree at path `p`, in forward order. -/
def _root_.Silmaril.SSA.LambdaRTL.Region.blocks :
    (L → Option Path) → Path → Region V L F → List ((L ⊕ Path) × Block V (L ⊕ Path) F)
  | _, _, .br _ _ => []
  | env, p, .let1 _ _ r => r.blocks env p
  | env, p, .let2 _ _ _ r => r.blocks env p
  | env, p, .case _ x r y s =>
      (.inr (p ++ [false]), ⟨x, r.entryBody env (p ++ [false])⟩) :: r.blocks env (p ++ [false]) ++
        (.inr (p ++ [true]), ⟨y, s.entryBody env (p ++ [true])⟩) :: s.blocks env (p ++ [true])
  | env, p, .join r ℓ x t =>
      r.blocks (bindLabel env ℓ (p ++ [true])) (p ++ [false]) ++
        (.inr (p ++ [true]), ⟨x, t.entryBody env (p ++ [true])⟩) :: t.blocks env (p ++ [true])

/-- **Flattening**: the erasure of a dominator tree into a flat CFG. -/
def flatten (r : Region V L F) : CFG V (L ⊕ Path) F :=
  ⟨r.entryBody (fun _ => none) [], r.blocks (fun _ => none) []⟩

end Flatten

/-! ### Store semantics -/

section Semantics

variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [Monad M]
  [DecidableEq V]

/-- Execution of a terminator; jumps are handed to the continuation `j`. -/
def Term.exec (m : Model F M α) {R : Type w} (j : K → α → (V → α) → M R) :
    Term V K F → (V → α) → M R
  | .br k a, σ => j k (a.eval m σ) σ
  | .case o x t y u, σ => o.eval m σ >>= m.split >>= fun
      | .inl a => t.exec m j (upd σ x a)
      | .inr b => u.exec m j (upd σ y b)

/-- Execution of a body; jumps are handed to the continuation `j`. -/
def Body.exec (m : Model F M α) {R : Type w} (j : K → α → (V → α) → M R) :
    Body V K F → (V → α) → M R
  | .let1 x o β, σ => o.eval m σ >>= fun a => β.exec m j (upd σ x a)
  | .let2 x y o β, σ => o.eval m σ >>= m.unpair >>= fun p =>
      β.exec m j (upd (upd σ x p.1) y p.2)
  | .term τ, σ => τ.exec m j σ

variable [DecidableEq K]

/-- A jump `br k a` into a block list: the first block labelled `k` assigns its parameter and
runs, resolving its own jumps in the *rest* of the list; an unknown label is an exit. -/
def jump (m : Model F M α) :
    List (K × Block V K F) → K → α → (V → α) → M (K × α × (V → α))
  | [], k, a, σ => pure (k, a, σ)
  | kb :: bs, k, a, σ =>
      if k = kb.1 then kb.2.body.exec m (jump m bs) (upd σ kb.2.param a) else jump m bs k a σ

/-- Store semantics of a CFG: `(exit label, argument, final store)`. -/
def _root_.Silmaril.SSA.LambdaRTL.CFG.run (m : Model F M α) (g : CFG V K F) (σ : V → α) :
    M (K × α × (V → α)) :=
  g.entry.exec m (jump m g.blocks) σ

end Semantics

/-! ### Translation validation -/

section Validate

variable {V L K : Type w} {F : Type v}
  [DecidableEq V] [DecidableEq L] [DecidableEq K] [DecidableEq F] [Inhabited K]

/-- The block relabelling read off positionally from a candidate CFG `g`, with exits renamed
by `exit`. -/
def relabelOf (exit : L → K) (r : Region V L F) (g : CFG V K F) : L ⊕ Path → K
  | .inl ℓ => exit ℓ
  | .inr q =>
      (((flatten r).blocks.map Prod.fst).zip (g.blocks.map Prod.fst) |>.lookup (.inr q)).getD
        default

/-- **Validator**: `g` is the flattening of `r` up to a relabelling that is injective on the
labels occurring in the flattening, and that renames exits by `exit`. Decidable by
construction. -/
def validate (exit : L → K) (r : Region V L F) (g : CFG V K F) : Bool :=
  let π := relabelOf exit r g
  let ls := (flatten r).labels
  decide (g = (flatten r).relabel π) && ls.all fun a => ls.all fun b => decide (π a = π b → a = b)

end Validate

end CFG

end Silmaril.SSA.LambdaRTL
