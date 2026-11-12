module

public import Silmaril.SSA.LambdaRTL.Defs

/-!
# Versioning: from acyclic λRTL to dominance-scoped λSSA

`Version.version` translates an arbitrary acyclic λRTL region (assignments may overwrite
registers, and a join handler may read registers clobbered before the jump) into a λSSA region
over the name type `V × ℕ`:

* every assignment to `x` binds a fresh *version* `(x, k)`; a use of `y` reads its current
  version `(y, cur y)`;
* every join label `ℓ` additionally receives the tuple of the current versions of its
  **live-ins** (φ-insertion): the free variables of its handler other than its parameter,
  together with every live-in of the enclosing join labels (the handler may jump outward,
  carrying their values from the jump site). Jumps to in-scope join labels pack that tuple with
  `pair`; the handler unpacks it with `let2`s into fresh versions. Labels not bound by an
  enclosing join are exits and are left unpacked.

Freshness uses the depth `d` along a scope path: every name in scope has version `≤ d`, and new
binders get versions `> d`. Since `IsSSA` only forbids rebinding names *in scope*, sibling scopes
may reuse versions. The infinite supply of names is provided by `ℕ`; no hypothesis on `V`
beyond decidable equality is needed.

Live-in lists are computed syntactically (`Region.fvList`, list-valued free variables) and
deduplicated; they are conservative (not a minimal liveness analysis).

Semantic correctness needs one law of the model, `Model.PairLawful`
(`unpair (pair a b) = pure (a, b)`), because φ-arguments are passed as pairs.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

universe v w

variable {V L : Type w} {F : Type v}

/-- Free variables of a value, as a list. -/
def Val.fvList : Val V → List V
  | .var x => [x]
  | .unit => []
  | .pair a b => a.fvList ++ b.fvList

/-- Free variables of an operand, as a list. -/
def Op.fvList : Op V F → List V
  | .val a | .app _ a | .inl a | .inr a | .abort a => a.fvList

/-- Lexically free variables of a region, as a list (with possible duplicates). -/
def Region.fvList [DecidableEq V] : Region V L F → List V
  | .br _ a => a.fvList
  | .let1 x o r => o.fvList ++ r.fvList.filter fun z => decide (z ≠ x)
  | .let2 x y o r => o.fvList ++ r.fvList.filter fun z => decide (z ≠ x ∧ z ≠ y)
  | .case o x r y s =>
      o.fvList ++ r.fvList.filter (fun z => decide (z ≠ x)) ++ s.fvList.filter fun z => decide (z ≠ y)
  | .join r _ x t => r.fvList ++ t.fvList.filter fun z => decide (z ≠ x)

/-- Model law used by versioning: destructuring a constructed pair returns its components. -/
structure Model.PairLawful {M : Type w → Type w} {α : Type w} [Monad M] (m : Model F M α) :
    Prop where
  unpair_pair : ∀ a b, m.unpair (m.pair a b) = pure (a, b)

namespace Version

/-- Update of a current-version map. -/
def setv [DecidableEq V] (cur : V → ℕ) (x : V) (n : ℕ) : V → ℕ :=
  fun y => if y = x then n else cur y

/-- Update of a label environment. -/
def setl [DecidableEq L] (lenv : L → Option (List V)) (ℓ : L) (ys : List V) :
    L → Option (List V) :=
  fun l => if l = ℓ then some ys else lenv l

/-- Read each variable at its current version. -/
def rn (cur : V → ℕ) : Val V → Val (V × ℕ)
  | .var x => .var (x, cur x)
  | .unit => .unit
  | .pair a b => .pair (rn cur a) (rn cur b)

/-- Read each variable of an operand at its current version. -/
def rnOp (cur : V → ℕ) : Op V F → Op (V × ℕ) F
  | .val a => .val (rn cur a)
  | .app f a => .app f (rn cur a)
  | .inl a => .inl (rn cur a)
  | .inr a => .inr (rn cur a)
  | .abort a => .abort (rn cur a)

/-- The tuple `((y₁, cur y₁), ((y₂, cur y₂), … ()))` of current versions. -/
def pack (cur : V → ℕ) : List V → Val (V × ℕ)
  | [] => .unit
  | y :: ys => .pair (.var (y, cur y)) (pack cur ys)

/-- Unpack a tuple held in `src` into fresh versions `(yᵢ, d + 2i + 1)` (the temporaries
`(yᵢ, d + 2i + 2)` hold the remaining tuple), then continue with `b`. -/
def unpack {L : Type w} : List V → V × ℕ → ℕ → Region (V × ℕ) L F → Region (V × ℕ) L F
  | [], _, _, b => b
  | y :: ys, src, d, b =>
      .let2 (y, d + 1) (y, d + 2) (.val (.var src)) (unpack ys (y, d + 2) (d + 2) b)

/-- Current versions after `unpack`. -/
def unpackCur [DecidableEq V] : List V → (V → ℕ) → ℕ → V → ℕ
  | [], cur, _ => cur
  | y :: ys, cur, d => unpackCur ys (setv cur y (d + 1)) (d + 2)

/-- The live-ins passed to a join handler `ℓ(x) => t` under enclosing live-ins `live`. -/
def liveIns [DecidableEq V] (t : Region V L F) (x : V) (live : List V) : List V :=
  ((t.fvList ++ live).filter fun z => decide (z ≠ x)).dedup

/-- The versioning translation. `lenv ℓ = some ys` for join labels in scope (with live-ins
`ys`), `none` for exits; `live` contains every list in the range of `lenv`; `cur` maps each
variable to its current version; every name in scope has version `≤ d`. -/
def version [DecidableEq V] [DecidableEq L] :
    (L → Option (List V)) → List V → (V → ℕ) → ℕ → Region V L F → Region (V × ℕ) L F
  | lenv, _, cur, _, .br ℓ a =>
      match lenv ℓ with
      | none => .br ℓ (rn cur a)
      | some ys => .br ℓ (.pair (rn cur a) (pack cur ys))
  | lenv, live, cur, d, .let1 x o r =>
      .let1 (x, d + 1) (rnOp cur o) (version lenv live (setv cur x (d + 1)) (d + 1) r)
  | lenv, live, cur, d, .let2 x y o r =>
      .let2 (x, d + 1) (y, d + 2) (rnOp cur o)
        (version lenv live (setv (setv cur x (d + 1)) y (d + 2)) (d + 2) r)
  | lenv, live, cur, d, .case o x r y s =>
      .case (rnOp cur o) (x, d + 1) (version lenv live (setv cur x (d + 1)) (d + 1) r)
        (y, d + 1) (version lenv live (setv cur y (d + 1)) (d + 1) s)
  | lenv, live, cur, d, .join r ℓ x t =>
      .join (version (setl lenv ℓ (liveIns t x live)) (liveIns t x live ++ live).dedup cur d r)
        ℓ (x, d + 1)
        (.let2 (x, d + 2) (x, d + 3) (.val (.var (x, d + 1)))
          (unpack (liveIns t x live) (x, d + 3) (d + 3)
            (version lenv live (unpackCur (liveIns t x live) (setv cur x (d + 2)) (d + 3))
              (d + 3 + 2 * (liveIns t x live).length) t)))

/-- Versioning of a whole program: no join labels in scope, every variable at version `0`. -/
def versionTop [DecidableEq V] [DecidableEq L] (r : Region V L F) : Region (V × ℕ) L F :=
  version (fun _ => none) [] (fun _ => 0) 0 r

/-- The initial SSA context of `versionTop r`: version `0` of each free variable. -/
def initCtx [DecidableEq V] (r : Region V L F) : Finset (V × ℕ) :=
  (r.fvList.map fun y => (y, 0)).toFinset

variable {M : Type w → Type w} {α : Type w}

/-- The value of the tuple `pack` in a store. -/
def packVal (m : Model F M α) (σ : V → α) : List V → α
  | [] => m.unit
  | y :: ys => m.pair (σ y) (packVal m σ ys)

/-- How a λRTL exit is seen after versioning: jumps to in-scope join labels carry the packed
live-ins of the jump-site store. -/
def enc (m : Model F M α) (lenv : L → Option (List V)) (e : L × α × (V → α)) : L × α :=
  match lenv e.1 with
  | none => (e.1, e.2.1)
  | some ys => (e.1, m.pair e.2.1 (packVal m e.2.2 ys))

end Version

end Silmaril.SSA.LambdaRTL
