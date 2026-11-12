module

public import Silmaril.Raw.Machine.RTL.BigStep
public import Silmaril.SSA.Isotope.Thms

/-!
# SSA-form RTL as a lambda-SSA region

"SSA is functional programming": a block `b` of a well-formed SSA function is
nested inside the `cfg` of its immediate dominator, so that the dominance
discipline becomes ordinary lexical scope and the dominator tree becomes the
nesting of `cfg` binders.

## Where the naive dominator-tree recipe fails, and what replaces it

The recipe "`T(b) = cfg (bodyOf b) ((domTreeChildren b).length) (fun i => T(child i))`"
does not typecheck against `Region.HasType.cfg`. That rule gives each block the
context `R i :: Γ` where `Γ` is the context *at the `cfg` node*, and operationally
`Region.Follow` restores the environment captured at the `cfg` node. So a block
nested directly under `cfg (bodyOf b) …` would see only the block parameters of
its dominators and none of the values their ops define — whereas `UsesDominated`
lets a block read exactly those. The fix is to place the `cfg` **after** the
dominator's own straight-line code rather than around it:

```
T(l) = let₁ op₀; … ; let₁ opₖ; cfg (terminator of l) (children l).length (fun i => T(child i))
```

Now the context at the `cfg` node contains every definition of `l`, so a child
sees its own parameters over all the definitions of all its dominators, which is
exactly `Func.Defined`.

Two further adjustments the sketch needs:

* **A register is a projection, not a binder.** A block has many parameters and
  an op may have many results, while a `cfg` block binds exactly one value.
  Unpacking a tuple with `let₂` at the head of a block would make every de Bruijn
  index depend on how many registers each earlier op defines. Instead each
  `let₁` binds one *packed tuple* — the block's parameters, or one op's results —
  and a register reference is the term `proj j (var i)`, which is a `Tm`-level
  `let₂` chain. Then each op contributes exactly one to the de Bruijn depth.
* **The entry block needs a label.** `idom` is `none` at the entry, so the entry
  block is nobody's dominator-tree child and a back edge to it would have no
  label. The translation therefore wraps everything in one outermost
  `cfg (br 0 (var 0)) 1 …` whose single block is the entry block. The function's
  packed argument is handed to it by that initial branch.

## The external labels

`Region.HasType Γ r L` with `Γ = [packTy fn.sig.params]` and
`L = [packTy fn.sig.results, Ty.unit]`: external label `0` is `ret`, carrying the
packed returned values, and external label `1` is `trap`, carrying `unit`.

## What is preserved

Typing (`toLambdaSSA_hasType`) and finite outcomes (`toLambdaSSA_eval_iff`, an
`iff` against the big-step `Func.Exec` of `Machine/RTL/BigStep.lean`), from
which whole-program behaviour follows (`toLambdaSSA_behaves_returned_iff`).

Divergence is preserved in **one direction only**
(`toLambdaSSA_diverges_of_external`): an externally divergent run of the region
is an infinite run of the function. The converse — that an infinite RTL run
makes the region diverge — is not proved; that theorem's docstring says what
stands in the way.

Both the `iff` on finite outcomes and the divergence theorem need two
hypotheses beyond `Func.WellFormed`: `Func.CallsMatch`, which says that each
call names its callee's declared arity, and `CallOracle.MatchesSigs`, which says
that the oracle returns that many words. Without the second, an abstract oracle
could return a tuple of the wrong width and the region would take a step the
machine cannot.

The lambda-SSA `Region.Fault` judgment plays no role: RTL's `trap` is an
ordinary exit label rather than a fault, and RTL's stuckness — division by zero,
an out-of-bounds access, an unwritten register — is the *absence* of a
transition on both sides, so it is already covered by the `iff` on finite
outcomes together with determinism.
-/

@[expose] public section

namespace Silmaril.Machine.RTL.SSA

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {R : Type}

/-! ## Projections out of a packed tuple -/

/-- The `j`-th component of a right-nested packed tuple, as a chain of `let₂`
eliminations. A tuple of `n` words has type `packTy n`, and `proj j` has type
`wordTy` whenever `j < n`. -/
def proj {Φ : Type} : Nat → Tm Φ → Tm Φ
  | 0, t => .let₂ t (.var 1)
  | j + 1, t => .let₂ t (proj j (.var 0))

/-- A projection out of a tuple long enough to have the component is a word. -/
theorem proj_hasType {Φ : Type} [Silmaril.HasTy Φ Ty] :
    ∀ {Γ : VCtx Ty} {t : Tm Φ} {n j : Nat}, j < n → Tm.HasType Γ t (packTy n) →
      Tm.HasType Γ (proj j t) wordTy
  | _, _, _ + 1, 0, _, ht => .let₂ ht (.var rfl)
  | _, _, _ + 1, _ + 1, hj, ht =>
      .let₂ ht (proj_hasType (Nat.lt_of_succ_lt_succ hj) (.var rfl))

/-- The position of an element in a list. -/
def idxIn {α : Type} [DecidableEq α] : List α → α → Option Nat
  | [], _ => none
  | x :: xs, r => if x = r then some 0 else (idxIn xs r).map (· + 1)

/-- A located element is inside the list. -/
theorem idxIn_lt {α : Type} [DecidableEq α] {g : List α} {r : α} {j : Nat}
    (h : idxIn g r = some j) : j < g.length := by
  induction g generalizing j with
  | nil => simp [idxIn] at h
  | cons x xs ih =>
    rw [idxIn] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact Nat.succ_pos _
    · obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      exact Nat.succ_lt_succ (ih hj')

/-- A located element is the one at the position found. -/
theorem idxIn_getElem {α : Type} [DecidableEq α] {g : List α} {r : α} {j : Nat}
    (h : idxIn g r = some j) : g[j]? = some r := by
  induction g generalizing j with
  | nil => simp [idxIn] at h
  | cons x xs ih =>
    rw [idxIn] at h
    split at h
    · rename_i hx
      obtain rfl := Option.some.inj h
      simpa using hx
    · obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using ih hj'

/-- An element of a list is located in it. -/
theorem idxIn_isSome {α : Type} [DecidableEq α] {g : List α} {r : α} (h : r ∈ g) :
    (idxIn g r).isSome := by
  induction g with
  | nil => simp at h
  | cons x xs ih =>
    rw [idxIn]
    split
    · rfl
    · rename_i hx
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hx
      · simpa using ih h

/-- The position of an element, as a plain index. -/
theorem idxIn_getD {α : Type} [DecidableEq α] {g : List α} {r : α} (h : r ∈ g) :
    g[(idxIn g r).getD 0]? = some r := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (idxIn_isSome h)
  rw [hj]
  exact idxIn_getElem hj

/-! ## Scopes

A scope records what the translation has bound so far: the register tuples, most
recent first, and the enclosing `cfg`s of the dominator tree with the number of
labels in scope at each. -/

/-- The state of the translation at a point of a block: the tuples bound, most
recent first, and the enclosing dominator-tree `cfg`s with their label depths,
innermost first. The label `none` is the outermost `cfg`, whose only block is the
entry block. -/
structure Scope (R : Type) where
  /-- The register tuples bound so far; entry `i` is the tuple at de Bruijn index
  `i`. -/
  vals : List (List R)
  /-- The enclosing `cfg`s, innermost first, paired with the number of labels in
  scope inside them. -/
  labels : List (Option Label × Nat)

namespace Scope

variable [DecidableEq R]

/-- Search the bound tuples for a register, returning how many tuples ago it was
bound and its position in that tuple. -/
def findReg : List (List R) → R → Nat → Option (Nat × Nat)
  | [], _, _ => none
  | g :: gs, r, i =>
    match idxIn g r with
    | some j => some (i, j)
    | none => findReg gs r (i + 1)

@[simp] theorem findReg_nil (r : R) (i : Nat) : findReg [] r i = none := rfl

/-- Searching a nonempty scope looks in its head tuple first. -/
theorem findReg_cons (g : List R) (gs : List (List R)) (r : R) (i : Nat) :
    findReg (g :: gs) r i =
      match idxIn g r with
      | some j => some (i, j)
      | none => findReg gs r (i + 1) := rfl

/-- A located register names a tuple of the scope and a position inside it. -/
theorem findReg_spec {vals : List (List R)} {r : R} :
    ∀ {base i j : Nat}, findReg vals r base = some (i, j) →
      base ≤ i ∧ ∃ g, vals[i - base]? = some g ∧ j < g.length ∧ g[j]? = some r := by
  induction vals with
  | nil => intro base i j h; simp [findReg] at h
  | cons g gs ih =>
    intro base i j h
    rw [findReg] at h
    split at h
    · rename_i j' hj'
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      exact ⟨Nat.le_refl _, g, by simp, idxIn_lt hj', idxIn_getElem hj'⟩
    · obtain ⟨hle, g', hg', hj, hr⟩ := ih h
      refine ⟨Nat.le_of_succ_le hle, g', ?_, hj, hr⟩
      rw [show i - base = (i - (base + 1)) + 1 by omega]
      simpa using hg'

/-- Whether a register is in scope does not depend on where the numbering starts. -/
theorem findReg_isSome_congr : ∀ (vals : List (List R)) (r : R) (i j : Nat),
    (findReg vals r i).isSome = (findReg vals r j).isSome
  | [], _, _, _ => rfl
  | g :: gs, r, i, j => by
    rw [findReg_cons, findReg_cons]
    cases hg : idxIn g r with
    | some _ => rfl
    | none => exact findReg_isSome_congr gs r (i + 1) (j + 1)

/-- A register bound by a tuple of the scope is located. -/
theorem findReg_isSome {vals : List (List R)} {r : R} {g : List R} (hg : g ∈ vals)
    (hr : r ∈ g) : ∀ base, (findReg vals r base).isSome := by
  induction vals with
  | nil => simp at hg
  | cons g' gs ih =>
    intro base
    rw [findReg]
    split
    · rfl
    · rename_i hnone
      rcases List.mem_cons.mp hg with rfl | hg
      · rw [Option.isSome_iff_exists.mp (idxIn_isSome hr) |>.choose_spec] at hnone
        exact absurd hnone (by simp)
      · exact ih hg (base + 1)

/-- The term denoting a register's current value. A register that is not in
scope, which `UsesDominated` rules out, denotes the junk term `unit`. -/
def ref {Φ : Type} (sc : Scope R) (r : R) : Tm Φ :=
  match findReg sc.vals r 0 with
  | some (i, j) => proj j (.var i)
  | none => .unit

/-- A register list as a packed tuple term, in order, terminated by `unit`. -/
def pack {Φ : Type} (sc : Scope R) : List R → Tm Φ
  | [] => .unit
  | r :: rs => .pair (sc.ref r) (sc.pack rs)

omit [DecidableEq R] in
/-- Bind one more tuple at de Bruijn index zero. -/
def push (sc : Scope R) (g : List R) : Scope R := { sc with vals := g :: sc.vals }

/-- Bind the result tuple of each op in turn. -/
def afterOps (sc : Scope R) (ops : List (Op R)) : Scope R :=
  ops.foldl (fun s o => s.push o.defs) sc

/-- The number of labels in scope inside the innermost enclosing `cfg`. -/
def depth (sc : Scope R) : Nat := (sc.labels.head?.map Prod.snd).getD 0

/-- The label depth recorded for an enclosing `cfg`. -/
def labelDepth : List (Option Label × Nat) → Option Label → Option Nat
  | [], _ => none
  | (a, d) :: rest, x => if a = x then some d else labelDepth rest x

/-- The lambda-SSA value context of a scope: one packed type per bound tuple,
over the function's own packed argument. -/
def ctx (sc : Scope R) (fn : Func R) : VCtx Ty :=
  sc.vals.map (fun g => packTy g.length) ++ [packTy fn.sig.params]

omit [DecidableEq R] in
@[simp] theorem push_vals (sc : Scope R) (g : List R) : (sc.push g).vals = g :: sc.vals := rfl

omit [DecidableEq R] in
@[simp] theorem afterOps_nil (sc : Scope R) : sc.afterOps [] = sc := rfl

omit [DecidableEq R] in
@[simp] theorem afterOps_cons (sc : Scope R) (o : Op R) (os : List (Op R)) :
    sc.afterOps (o :: os) = (sc.push o.defs).afterOps os := rfl

omit [DecidableEq R] in
/-- Binding one more tuple extends the context at its head. -/
@[simp] theorem ctx_push (sc : Scope R) (fn : Func R) (g : List R) :
    (sc.push g).ctx fn = packTy g.length :: sc.ctx fn := rfl

omit [DecidableEq R] in
/-- Binding tuples never changes the labels in scope. -/
@[simp] theorem push_labels (sc : Scope R) (g : List R) : (sc.push g).labels = sc.labels := rfl

omit [DecidableEq R] in
/-- Running through a block's ops never changes the labels in scope. -/
@[simp] theorem afterOps_labels (sc : Scope R) (ops : List (Op R)) :
    (sc.afterOps ops).labels = sc.labels := by
  induction ops generalizing sc with
  | nil => rfl
  | cons o os ih => exact ih (sc.push o.defs)

omit [DecidableEq R] in
/-- Running through a block's ops never changes the innermost label depth. -/
@[simp] theorem afterOps_depth (sc : Scope R) (ops : List (Op R)) :
    (sc.afterOps ops).depth = sc.depth := by
  rw [depth, depth, afterOps_labels]

omit [DecidableEq R] in
/-- A tuple of the scope types the de Bruijn index that names it. -/
theorem ctx_getElem {sc : Scope R} {fn : Func R} {i : Nat} {g : List R}
    (h : sc.vals[i]? = some g) : At (sc.ctx fn) i (packTy g.length) := by
  have hlt : i < sc.vals.length := (List.getElem?_eq_some_iff.mp h).1
  rw [ctx, At, List.getElem?_append_left (by simpa using hlt), List.getElem?_map, h]
  rfl

/-- A register is in scope when some tuple the scope has bound holds it. -/
def HasReg (sc : Scope R) (r : R) : Prop := ∃ g ∈ sc.vals, r ∈ g

/-- A register in scope is found by the search. -/
theorem findReg_isSome_of_hasReg {sc : Scope R} {r : R} (h : sc.HasReg r) :
    (findReg sc.vals r 0).isSome := by
  obtain ⟨g, hg, hr⟩ := h
  exact findReg_isSome hg hr 0

omit [DecidableEq R] in
/-- Extending the bound tuples keeps every register already in scope. -/
theorem HasReg.mono {sc sc' : Scope R} {r : R} (h : sc.HasReg r)
    (hsub : sc.vals ⊆ sc'.vals) : sc'.HasReg r := by
  obtain ⟨g, hg, hr⟩ := h
  exact ⟨g, hsub hg, hr⟩

omit [DecidableEq R] in
/-- A tuple the scope has bound puts all of its registers in scope. -/
theorem hasReg_of_mem {sc : Scope R} {g : List R} {r : R} (hg : g ∈ sc.vals)
    (hr : r ∈ g) : sc.HasReg r := ⟨g, hg, hr⟩

/-- Every register of the list is in scope. -/
def Covers (sc : Scope R) (rs : List R) : Prop := ∀ r ∈ rs, sc.HasReg r

omit [DecidableEq R] in
/-- A covered sublist is covered. -/
theorem Covers.mono {sc : Scope R} {rs rs' : List R} (h : sc.Covers rs)
    (hsub : rs' ⊆ rs) : sc.Covers rs' := fun r hr => h r (hsub hr)

omit [DecidableEq R] in
/-- Extending the bound tuples keeps every covered list covered. -/
theorem Covers.vals {sc sc' : Scope R} {rs : List R} (h : sc.Covers rs)
    (hsub : sc.vals ⊆ sc'.vals) : sc'.Covers rs := fun r hr => (h r hr).mono hsub

omit [DecidableEq R] in
/-- Binding one more tuple keeps every register that was already in scope. -/
theorem Covers.push {sc : Scope R} {rs : List R} (h : sc.Covers rs) (g : List R) :
    (sc.push g).Covers rs := h.vals (by simp)

omit [DecidableEq R] in
/-- Running through a block's ops only adds tuples. -/
theorem vals_subset_afterOps (sc : Scope R) :
    ∀ (ops : List (Op R)), sc.vals ⊆ (sc.afterOps ops).vals
  | [] => fun _ h => h
  | o :: os => fun g hg => vals_subset_afterOps (sc.push o.defs) os (by simp [hg])

omit [DecidableEq R] in
/-- Every op's destinations become a tuple of the scope. -/
theorem defs_mem_afterOps (sc : Scope R) :
    ∀ {ops : List (Op R)} {o : Op R}, o ∈ ops → o.defs ∈ (sc.afterOps ops).vals
  | o' :: os, o, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact vals_subset_afterOps (sc.push o.defs) os (by simp)
    · exact defs_mem_afterOps (sc.push o'.defs) h

/-- The reference term of a register in scope is a word. -/
theorem ref_hasType {Φ : Type} [Silmaril.HasTy Φ Ty] {sc : Scope R} {fn : Func R} {r : R}
    (h : sc.HasReg r) :
    Tm.HasType (sc.ctx fn) (sc.ref (Φ := Φ) r) wordTy := by
  obtain ⟨⟨i, j⟩, hij⟩ := Option.isSome_iff_exists.mp (findReg_isSome_of_hasReg h)
  obtain ⟨-, g, hg, hj, -⟩ := findReg_spec hij
  rw [Nat.sub_zero] at hg
  rw [ref, hij]
  exact proj_hasType hj (.var (ctx_getElem hg))

/-- A packed tuple of registers in scope has the packed type of its length. -/
theorem pack_hasType {Φ : Type} [Silmaril.HasTy Φ Ty] {sc : Scope R} {fn : Func R}
    {rs : List R} (h : sc.Covers rs) :
    Tm.HasType (sc.ctx fn) (sc.pack (Φ := Φ) rs) (packTy rs.length) := by
  induction rs with
  | nil => exact .unit
  | cons r rs ih =>
    exact .pair (ref_hasType (h r (by simp))) (ih (fun x hx => h x (by simp [hx])))

end Scope

/-! ## The dominator tree, with a root above the entry -/

namespace Func

variable [DecidableEq R]

/-- The dominator-tree children of a block, with an artificial root `none` above
the entry so that the entry block has a label of its own and may be the target of
a back edge. -/
def domChildren (fn : Func R) : Option Label → List Label
  | none => [fn.entry]
  | some a => fn.digraph.domTreeChildren a

/-- The number of parameters of a block; a missing block has none. -/
def paramCount (fn : Func R) (l : Label) : Nat :=
  ((fn.block? l).map fun b => b.params.length).getD 0

/-- The de Bruijn label index of a transfer to block `t` from the given scope:
walk out to the `cfg` of `t`'s immediate dominator, adding each level's arity,
then take `t`'s position among that `cfg`'s blocks. -/
def jumpLabel (fn : Func R) (sc : Scope R) (t : Label) : Nat :=
  let parent := fn.digraph.idom t
  match Scope.labelDepth sc.labels parent with
  | some d =>
      (sc.depth - d) + (idxIn (fn.domChildren parent) t).getD 0
  | none => 0

end Func

/-! ## Label contexts

The labels in scope at a point of the translation are the dominator-tree
children of each enclosing `cfg`, innermost first, over the two external labels.
`Scope.labels` records the running total of those arities so that a transfer can
be resolved by subtraction rather than by another traversal. -/

/-- The number of labels in scope inside a list of enclosing `cfg`s. -/
def labelsDepth (ls : List (Option Label × Nat)) : Nat := (ls.head?.map Prod.snd).getD 0

@[simp] theorem labelsDepth_nil : labelsDepth [] = 0 := rfl

@[simp] theorem labelsDepth_cons (a : Option Label) (d : Nat)
    (ls : List (Option Label × Nat)) : labelsDepth ((a, d) :: ls) = d := rfl

variable [DecidableEq R]

/-- The internal part of the label context: the dominator-tree children of each
enclosing `cfg`, innermost first. -/
def labelsCtx (fn : Func R) (ls : List (Option Label × Nat)) : LCtx Ty :=
  ls.flatMap fun al => (fn.domChildren al.1).map fun c => packTy (fn.paramCount c)

omit [DecidableEq R] in
@[simp] theorem labelsCtx_nil (fn : Func R) : labelsCtx fn [] = [] := rfl

omit [DecidableEq R] in
@[simp] theorem labelsCtx_cons (fn : Func R) (a : Option Label) (d : Nat)
    (ls : List (Option Label × Nat)) :
    labelsCtx fn ((a, d) :: ls) =
      (fn.domChildren a).map (fun c => packTy (fn.paramCount c)) ++ labelsCtx fn ls := rfl

namespace Scope

/-- The recorded depths are the running totals of the enclosing `cfg` arities. -/
def LabelsOk (fn : Func R) : List (Option Label × Nat) → Prop
  | [] => True
  | (a, d) :: rest => d = (fn.domChildren a).length + labelsDepth rest ∧ LabelsOk fn rest

/-- The full label context of a scope: the enclosing `cfg`s' blocks, then the
return label carrying the packed results and the trap label carrying `unit`. -/
def lctx (sc : Scope R) (fn : Func R) : LCtx Ty :=
  labelsCtx fn sc.labels ++ [packTy fn.sig.results, Silmaril.Ty.unit]

omit [DecidableEq R] in
/-- The recorded depth counts the labels the enclosing `cfg`s bind. -/
theorem labelsDepth_eq {fn : Func R} :
    ∀ {ls : List (Option Label × Nat)}, LabelsOk fn ls →
      labelsDepth ls = (labelsCtx fn ls).length
  | [], _ => rfl
  | (a, d) :: rest, h => by
    rw [labelsDepth_cons, labelsCtx_cons, List.length_append, List.length_map, h.1,
      labelsDepth_eq h.2]

omit [DecidableEq R] in
/-- Depths decrease outwards, so a recorded depth never exceeds the innermost
one. -/
theorem labelDepth_le {fn : Func R} :
    ∀ {ls : List (Option Label × Nat)} {a : Option Label} {d : Nat}, LabelsOk fn ls →
      labelDepth ls a = some d → d ≤ labelsDepth ls
  | [], _, _, _, h => by simp [labelDepth] at h
  | (a₀, d₀) :: rest, a, d, hok, h => by
    rw [labelDepth] at h
    split at h
    · exact Nat.le_of_eq (Option.some.inj h).symm
    · rw [labelsDepth_cons, hok.1]
      exact Nat.le_add_left_of_le (labelDepth_le hok.2 h)

omit [DecidableEq R] in
/-- **The label index of a transfer is correct.** Subtracting the depth recorded
for an enclosing `cfg` from the innermost depth skips exactly the labels bound
inside it, so adding the target's position among that `cfg`'s blocks names the
target. -/
theorem labelsCtx_getElem {fn : Func R} :
    ∀ {ls : List (Option Label × Nat)} {a : Option Label} {d k : Nat} {c : Label},
      LabelsOk fn ls → labelDepth ls a = some d → (fn.domChildren a)[k]? = some c →
      (labelsCtx fn ls)[labelsDepth ls - d + k]? = some (packTy (fn.paramCount c))
  | [], _, _, _, _, _, h, _ => by simp [labelDepth] at h
  | (a₀, d₀) :: rest, a, d, k, c, hok, h, hc => by
    have hk : k < (fn.domChildren a).length := (List.getElem?_eq_some_iff.mp hc).1
    rw [labelDepth] at h
    split at h
    · rename_i ha
      subst ha
      obtain rfl := Option.some.inj h
      rw [labelsDepth_cons, Nat.sub_self, Nat.zero_add, labelsCtx_cons,
        List.getElem?_append_left (by simpa using hk), List.getElem?_map, hc]
      rfl
    · have hle := labelDepth_le hok.2 h
      have hlen : ((fn.domChildren a₀).map (fun c => packTy (fn.paramCount c))).length
          = (fn.domChildren a₀).length := by simp
      have hidx : labelsDepth ((a₀, d₀) :: rest) - d + k
          = (fn.domChildren a₀).length + (labelsDepth rest - d + k) := by
        rw [labelsDepth_cons, hok.1]
        omega
      rw [hidx, labelsCtx_cons,
        List.getElem?_append_right (by rw [hlen]; exact Nat.le_add_right _ _), hlen,
        Nat.add_sub_cancel_left]
      exact labelsCtx_getElem hok.2 h hc

omit [DecidableEq R] in
/-- The return label sits just above every label the enclosing `cfg`s bind. -/
theorem lctx_ret {sc : Scope R} {fn : Func R} (hok : LabelsOk fn sc.labels) :
    At (sc.lctx fn) sc.depth (packTy fn.sig.results) := by
  rw [lctx, At, depth, show (sc.labels.head?.map Prod.snd).getD 0 = labelsDepth sc.labels from rfl,
    labelsDepth_eq hok, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

omit [DecidableEq R] in
/-- The trap label sits just above the return label. -/
theorem lctx_trap {sc : Scope R} {fn : Func R} (hok : LabelsOk fn sc.labels) :
    At (sc.lctx fn) (sc.depth + 1) Silmaril.Ty.unit := by
  rw [lctx, At, depth, show (sc.labels.head?.map Prod.snd).getD 0 = labelsDepth sc.labels from rfl,
    labelsDepth_eq hok, List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

end Scope

/-! ## The translation -/


/-- The term computing one op's results, packed into a tuple. Every op is an
opcode applied to its packed operands, `move` included, so that each op
contributes exactly one binder; a `store` produces the empty tuple, which is
`unit`. -/
def Op.toTm (sigs : List Signature) (sc : Scope R) : Op R → Tm (Opcode sigs)
  | .const _ v => .op (.const v) .unit
  | .move _ s => .op .move (sc.pack [s])
  | .unary o _ s => .op (.unary o) (sc.pack [s])
  | .binary o _ a b => .op (.binary o) (sc.pack [a, b])
  | .load w e _ base off => .op (.load w e off) (sc.pack [base])
  | .store w base off src => .op (.store w off) (sc.pack [base, src])
  | .call f args _ => .op (.call f) (sc.pack args)

/-- The region a terminator becomes. A jump is a branch to the dominator-tree
label of its target; a conditional is a `case` on the branch opcode, taking the
left injection when the condition is nonzero; a return and a trap are branches to
the two external labels, which sit just above every internal one. -/
def Term.toRegion (sigs : List Signature) (fn : Func R) (sc : Scope R) :
    Term R → Region (Opcode sigs)
  | .jump t as => .br (fn.jumpLabel sc t) (sc.pack as)
  | .cond c t₁ a₁ t₂ a₂ =>
      .case (.op .test (sc.pack [c]))
        ((Region.br (fn.jumpLabel sc t₁) (sc.pack a₁)).renameVars Nat.succ)
        ((Region.br (fn.jumpLabel sc t₂) (sc.pack a₂)).renameVars Nat.succ)
  | .ret vs => .br sc.depth (sc.pack vs)
  | .trap => .br (sc.depth + 1) .unit

/-- The `let₁` chain for a block's straight-line code, wrapping the region that
follows it. -/
def opsRegion (sigs : List Signature) (sc : Scope R) :
    List (Op R) → Region (Opcode sigs) → Region (Opcode sigs)
  | [], k => k
  | o :: os, k => .let₁ (Op.toTm sigs sc o) (opsRegion sigs (sc.push o.defs) os k)

/-- The region of block `l`, with the `cfg` of its dominator-tree children placed
after its own straight-line code. `sc` is the scope at the enclosing `cfg` node,
before `l`'s packed parameter is bound. `fuel` bounds the depth of the dominator
tree and is instantiated with the number of blocks, which always suffices. -/
def blockRegion (sigs : List Signature) (fuel : Nat) (fn : Func R) (sc : Scope R)
    (l : Label) : Region (Opcode sigs) :=
  match fuel with
  | 0 => .br 0 .unit
  | fuel + 1 =>
    match fn.block? l with
    | none => .br 0 .unit
    | some b =>
      let sc₀ := sc.push b.params
      let sc₁ := sc₀.afterOps b.ops
      let kids := fn.domChildren (some l)
      let sc₂ : Scope R := { sc₁ with labels := (some l, kids.length + sc.depth) :: sc₁.labels }
      opsRegion sigs sc₀ b.ops
        (.cfg (Term.toRegion sigs fn sc₂ b.term) kids.length
          (fun i => blockRegion sigs fuel fn sc₂ (kids[i.val]'i.isLt)))

/-- **An SSA-form RTL function as a lambda-SSA region.** The outermost `cfg` has
the entry block as its only block and hands it the function's packed argument, so
that a back edge to the entry has a label like any other transfer. -/
def toLambdaSSA (sigs : List Signature) (fn : Func R) : Region (Opcode sigs) :=
  .cfg (.br 0 (.var 0)) 1
    (fun _ => blockRegion sigs fn.blocks.length fn ⟨[], [(none, 1)]⟩ fn.entry)

/-! ## Calls name their callee's arity

`Func.WellFormed` has no access to the function table, so it cannot check a call
against its callee's signature. Typing the translation needs that check, and it
is supplied separately. -/

/-- Every call supplies and receives its callee's declared number of words. -/
def Func.callsMatch (sigs : List Signature) (fn : Func R) : Bool :=
  fn.blocks.all fun b => b.ops.all fun o =>
    match o with
    | .call f args results =>
        (args.length == (sigAt sigs f).params) && (results.length == (sigAt sigs f).results)
    | _ => true

/-- Every call agrees with its callee's signature. -/
def Func.CallsMatch (sigs : List Signature) (fn : Func R) : Prop := fn.callsMatch sigs = true

instance (sigs : List Signature) (fn : Func R) : Decidable (fn.CallsMatch sigs) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Typing preservation -/

/-- Every call of an op list names its callee's declared arity. -/
def OpsCallsMatch (sigs : List Signature) (ops : List (Op R)) : Prop :=
  ∀ o ∈ ops, ∀ f args results, o = .call f args results →
    args.length = (sigAt sigs f).params ∧ results.length = (sigAt sigs f).results

/-- The term of an op has the packed type of the registers it defines, provided
every register it reads is in scope and, for a call, its arity matches its
callee's signature. -/
theorem Op.toTm_hasType {sigs : List Signature} {sc : Scope R} {fn : Func R} {o : Op R}
    (hcov : sc.Covers o.uses)
    (hcall : ∀ f args results, o = .call f args results →
      args.length = (sigAt sigs f).params ∧ results.length = (sigAt sigs f).results) :
    Tm.HasType (sc.ctx fn) (Op.toTm sigs sc o) (packTy o.defs.length) := by
  cases o with
  | const d v => exact .op .unit
  | move d s => exact .op (Scope.pack_hasType hcov)
  | unary op d s => exact .op (Scope.pack_hasType hcov)
  | binary op d a b => exact .op (Scope.pack_hasType hcov)
  | load w e d base off => exact .op (Scope.pack_hasType hcov)
  | store w base off src => exact .op (Scope.pack_hasType hcov)
  | call f args results =>
    obtain ⟨hargs, hres⟩ := hcall f args results rfl
    have ha : Tm.HasType (sc.ctx fn) (sc.pack (Φ := Opcode sigs) args)
        (packTy (sigAt sigs f).params) := by
      rw [← hargs]; exact Scope.pack_hasType hcov
    show Tm.HasType _ _ (packTy results.length)
    rw [hres]
    exact .op ha

/-- The `let₁` chain for a block's straight-line code types whatever follows it
in the context the ops leave behind. -/
theorem opsRegion_hasType {sigs : List Signature} {fn : Func R} :
    ∀ {sc : Scope R} {ops : List (Op R)} {k : Region (Opcode sigs)} {L : LCtx Ty},
      (∀ i o, ops[i]? = some o → (sc.afterOps (ops.take i)).Covers o.uses) →
      OpsCallsMatch sigs ops →
      Region.HasType ((sc.afterOps ops).ctx fn) k L →
      Region.HasType (sc.ctx fn) (opsRegion sigs sc ops k) L
  | _, [], _, _, _, _, hk => hk
  | sc, o :: os, k, L, hcov, hcall, hk => by
    refine .let₁ (Op.toTm_hasType (hcov 0 o rfl) (hcall o (by simp))) ?_
    refine opsRegion_hasType (sc := sc.push o.defs) (fun i o' ho' => ?_)
      (fun o' ho' => hcall o' (by simp [ho'])) hk
    simpa using hcov (i + 1) o' (by simpa using ho')



/-! ### The scope invariant

The descent down the dominator tree enters block `l` with a scope that already
holds every definition of every strict dominator of `l`, and whose enclosing
`cfg`s are exactly the proper dominator-tree ancestors of `l`. Both halves are
inductive: a child of `l` gains `l`'s own definitions and `l`'s own `cfg`. -/

/-- The scope at the `cfg` of block `l`: every parameter and every op result of
`l` bound, and `l`'s own `cfg` recorded above the enclosing ones. -/
def blockScope (fn : Func R) (sc : Scope R) (l : Label) (b : Block R) : Scope R :=
  let sc₁ := (sc.push b.params).afterOps b.ops
  { sc₁ with labels := (some l, (fn.domChildren (some l)).length + sc.depth) :: sc₁.labels }

omit [DecidableEq R] in
@[simp] theorem blockScope_vals (fn : Func R) (sc : Scope R) (l : Label) (b : Block R) :
    (blockScope fn sc l b).vals = ((sc.push b.params).afterOps b.ops).vals := rfl

omit [DecidableEq R] in
@[simp] theorem blockScope_ctx (fn : Func R) (sc : Scope R) (l : Label) (b : Block R) :
    (blockScope fn sc l b).ctx fn = ((sc.push b.params).afterOps b.ops).ctx fn := rfl

omit [DecidableEq R] in
@[simp] theorem blockScope_labels (fn : Func R) (sc : Scope R) (l : Label) (b : Block R) :
    (blockScope fn sc l b).labels =
      (some l, (fn.domChildren (some l)).length + sc.depth) :: sc.labels := by
  rw [blockScope]
  simp

omit [DecidableEq R] in
@[simp] theorem blockScope_depth (fn : Func R) (sc : Scope R) (l : Label) (b : Block R) :
    (blockScope fn sc l b).depth = (fn.domChildren (some l)).length + sc.depth := by
  rw [Scope.depth, blockScope_labels]
  rfl

/-- The region of a block that exists: its straight-line code, then the `cfg` of
its dominator-tree children. -/
theorem blockRegion_succ {sigs : List Signature} {fuel : Nat} {fn : Func R} {sc : Scope R}
    {l : Label} {b : Block R} (hb : fn.block? l = some b) :
    blockRegion sigs (fuel + 1) fn sc l =
      opsRegion sigs (sc.push b.params) b.ops
        (.cfg (Term.toRegion sigs fn (blockScope fn sc l b) b.term)
          (fn.domChildren (some l)).length
          (fun i => blockRegion sigs fuel fn (blockScope fn sc l b)
            ((fn.domChildren (some l))[i.val]'i.isLt))) := by
  rw [blockRegion, hb]
  rfl

/-- `sc` is a correct scope for entering block `l`: the enclosing `cfg`s carry
the running totals of their arities and cover every proper dominator-tree
ancestor of `l`, and every register a strict dominator of `l` defines is in
scope. -/
structure EnterOk (fn : Func R) (sc : Scope R) (l : Label) : Prop where
  /-- The recorded label depths are the running totals of the enclosing arities. -/
  labelsOk : Scope.LabelsOk fn sc.labels
  /-- Every proper dominator-tree ancestor of `l` has its `cfg` in scope. -/
  ancestors : ∀ a, fn.digraph.StrictlyDominates a l →
    (Scope.labelDepth sc.labels (some a)).isSome
  /-- The artificial root above the entry block is in scope. -/
  root : (Scope.labelDepth sc.labels none).isSome
  /-- Every register a strict dominator of `l` defines is in scope. -/
  domDefs : ∀ a r, fn.digraph.StrictlyDominates a l → r ∈ fn.defsOf a → sc.HasReg r
  /-- `l` is reachable, so it has a place in the dominator tree. -/
  reachable : fn.Reachable l

omit [DecidableEq R] in
/-- A reachable block is a dominator-tree child of its immediate dominator; the
entry block is the only child of the artificial root. -/
theorem mem_domChildren_idom {fn : Func R} {t : Label} (ht : fn.Reachable t) :
    t ∈ fn.domChildren (fn.digraph.idom t) := by
  cases h : fn.digraph.idom t with
  | some a => exact Graph.Digraph.mem_domTreeChildren_iff.mpr h
  | none =>
    by_cases he : t = fn.digraph.entry
    · rw [Func.domChildren]
      exact List.mem_singleton.mpr he
    · obtain ⟨a, ha, -, -⟩ := Graph.Digraph.idom_spec ht he
      rw [h] at ha
      exact absurd ha (by simp)

omit [DecidableEq R] in
/-- Transferring to a reachable block whose immediate dominator has a `cfg` in
scope names that block in the label context. -/
theorem jumpLabel_at {sc : Scope R} {fn : Func R} {t : Label}
    (hok : Scope.LabelsOk fn sc.labels) (ht : fn.Reachable t)
    (hd : (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome) :
    At (sc.lctx fn) (fn.jumpLabel sc t) (packTy (fn.paramCount t)) := by
  obtain ⟨d, hdd⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (idxIn_isSome (mem_domChildren_idom ht))
  have hidx := Scope.labelsCtx_getElem (fn := fn) hok hdd (idxIn_getElem hk)
  have hj : fn.jumpLabel sc t = labelsDepth sc.labels - d + k := by
    simp only [Func.jumpLabel, hdd, hk, Option.getD_some]
    rfl
  rw [hj, Scope.lctx, At, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hidx).1]
  exact hidx

/-- Indexing a list through `Fin` and mapping it agree. -/
theorem ofFn_getElem_map {α β : Type} (l : List α) (f : α → β) :
    List.ofFn (fun i : Fin l.length => f (l[i.val]'i.isLt)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp

omit [DecidableEq R] in
/-- Well-formedness bounds the dominator depth of every reachable block, so the
number of blocks is always enough fuel for the descent. -/
theorem domDepth_lt {fn : Func R} (hsig : fn.WellFormedSig) {l : Label}
    (hl : fn.Reachable l) : fn.digraph.domDepth l < fn.blocks.length := by
  have hentry : fn.digraph.entry < fn.digraph.size := hsig.1
  have hnodes : fn.digraph.nodes = List.range fn.digraph.size := by
    simp [Graph.Digraph.nodes, hentry]
  have hsub : (l :: fn.digraph.strictDoms l) ⊆ fn.digraph.nodes := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Graph.Digraph.mem_nodes_of_reachable hl
    · exact Graph.Digraph.strictDoms_subset_nodes _ _ hx
  have hnd : (l :: fn.digraph.strictDoms l).Nodup :=
    List.nodup_cons.mpr
      ⟨Graph.Digraph.not_mem_strictDoms_self _ _, Graph.Digraph.strictDoms_nodup _ _⟩
  have hle := List.Nodup.length_le_of_subset hnd hsub
  rw [hnodes, List.length_range] at hle
  have hle' : (fn.digraph.strictDoms l).length + 1 ≤ fn.digraph.size := by simpa using hle
  exact hle'

omit [DecidableEq R] in
/-- Every register that well-formedness permits at a point of a block is in the
scope the translation has built there. -/
theorem covers_of_defined {fn : Func R} {sc : Scope R} {l : Label} {b : Block R}
    (hb : fn.block? l = some b)
    (hdom : ∀ a r, fn.digraph.StrictlyDominates a l → r ∈ fn.defsOf a → sc.HasReg r)
    {j : Nat} {r : R} (h : fn.Defined l j r) :
    ((sc.push b.params).afterOps (b.ops.take j)).HasReg r := by
  have hbase : sc.vals ⊆ ((sc.push b.params).afterOps (b.ops.take j)).vals := by
    refine List.Subset.trans ?_ (Scope.vals_subset_afterOps (sc.push b.params) (b.ops.take j))
    simp
  rcases h with ⟨a, hda, hne, hr⟩ | ⟨b', hb', hcase⟩
  · exact (hdom a r ⟨hda, hne⟩ hr).mono hbase
  · have hbb : b' = b := by rw [hb] at hb'; exact (Option.some.inj hb').symm
    rw [hbb] at hcase
    rcases hcase with hp | ⟨o, ho, hd⟩
    · exact Scope.hasReg_of_mem
        (Scope.vals_subset_afterOps (sc.push b.params) (b.ops.take j) (by simp)) hp
    · exact Scope.hasReg_of_mem (Scope.defs_mem_afterOps (sc.push b.params) ho) hd

/-- Well-formedness makes every register an op reads available at that op. -/
theorem defined_of_usesDominated {fn : Func R} (hud : fn.UsesDominated) {l : Label}
    {b : Block R} (hb : fn.block? l = some b) {j : Nat} {o : Op R} (ho : b.ops[j]? = some o)
    {r : R} (hr : r ∈ o.uses) : fn.Defined l j r := by
  rw [Func.UsesDominated, Func.usesDominated, List.all_eq_true] at hud
  have hlt : l < fn.blocks.length := (List.getElem?_eq_some_iff.mp hb).1
  have h1 := hud l (List.mem_range.mpr hlt)
  rw [hb] at h1
  simp only [Bool.and_eq_true, List.all_eq_true] at h1
  have hidx : j < b.ops.length := (List.getElem?_eq_some_iff.mp ho).1
  have h2 := h1.1 j (List.mem_range.mpr hidx)
  rw [ho, List.all_eq_true] at h2
  exact Func.defined_of_okUse (h2 r hr)

/-- Well-formedness makes every register a terminator reads available at it. -/
theorem defined_of_usesDominated_term {fn : Func R} (hud : fn.UsesDominated) {l : Label}
    {b : Block R} (hb : fn.block? l = some b) {r : R} (hr : r ∈ b.term.uses) :
    fn.Defined l b.ops.length r := by
  rw [Func.UsesDominated, Func.usesDominated, List.all_eq_true] at hud
  have hlt : l < fn.blocks.length := (List.getElem?_eq_some_iff.mp hb).1
  have h1 := hud l (List.mem_range.mpr hlt)
  rw [hb] at h1
  simp only [Bool.and_eq_true, List.all_eq_true] at h1
  exact Func.defined_of_okUse (h1.2 r hr)

omit [DecidableEq R] in
/-- A well-formed function's terminators name existing targets with the right
number of arguments. -/
theorem params_length_of_argsMatch {fn : Func R} (h : fn.ArgsMatch) {l : Label}
    {b : Block R} (hb : fn.block? l = some b) {tgt : Label} {as : List R}
    (ha : (tgt, as) ∈ b.term.args) : as.length = fn.paramCount tgt ∧ tgt < fn.blocks.length := by
  rw [Func.ArgsMatch, Func.argsMatch, List.all_eq_true] at h
  have hmem : b ∈ fn.blocks := List.mem_of_getElem? hb
  have h1 := h b hmem
  rw [List.all_eq_true] at h1
  have h2 := h1 (tgt, as) ha
  cases hbt : fn.block? tgt with
  | none => rw [hbt] at h2; simp at h2
  | some tb =>
    rw [hbt] at h2
    simp only [beq_iff_eq] at h2
    refine ⟨?_, (List.getElem?_eq_some_iff.mp hbt).1⟩
    rw [Func.paramCount, hbt]
    exact h2.symm

omit [DecidableEq R] in
/-- Every call of a block's ops names its callee's declared arity. -/
theorem opsCallsMatch_of_callsMatch {sigs : List Signature} {fn : Func R}
    (h : fn.CallsMatch sigs) {l : Label} {b : Block R} (hb : fn.block? l = some b) :
    OpsCallsMatch sigs b.ops := by
  rw [Func.CallsMatch, Func.callsMatch, List.all_eq_true] at h
  have h1 := h b (List.mem_of_getElem? hb)
  rw [List.all_eq_true] at h1
  rintro o ho f args results rfl
  have := h1 _ ho
  simpa using this

omit [DecidableEq R] in
/-- A well-formed function's terminators pass the signature check. -/
theorem term_okIn {fn : Func R} (hsig : fn.WellFormedSig) {l : Label} {b : Block R}
    (hb : fn.block? l = some b) : b.term.okIn fn.sig.results fn.blocks.length = true := by
  have h := hsig.2.2
  rw [List.all_eq_true] at h
  exact h b (List.mem_of_getElem? hb)

omit [DecidableEq R] in
/-- Every target of a well-formed function's terminator exists. -/
theorem lt_of_mem_successors {fn : Func R} (hsig : fn.WellFormedSig) {l : Label}
    {b : Block R} (hb : fn.block? l = some b) {tgt : Label} (ht : tgt ∈ b.term.successors) :
    tgt < fn.blocks.length := by
  have h := term_okIn hsig hb
  unfold Term.okIn at h
  rw [Bool.and_eq_true] at h
  have h1 := h.1
  rw [List.all_eq_true] at h1
  simpa using h1 tgt ht

omit [DecidableEq R] in
/-- A well-formed function returns the number of values its signature declares. -/
theorem ret_length {fn : Func R} (hsig : fn.WellFormedSig) {l : Label} {b : Block R}
    (hb : fn.block? l = some b) {vs : List R} (hterm : b.term = .ret vs) :
    vs.length = fn.sig.results := by
  have h := term_okIn hsig hb
  rw [hterm] at h
  unfold Term.okIn at h
  rw [Bool.and_eq_true] at h
  simpa using h.2

omit [DecidableEq R] in
/-- Reachable blocks exist. -/
theorem lt_blocks_length_of_reachable {fn : Func R} (hsig : fn.WellFormedSig) {l : Label}
    (hl : fn.Reachable l) : l < fn.blocks.length := by
  rcases Graph.Digraph.mem_nodes_iff.mp (Graph.Digraph.mem_nodes_of_reachable hl) with h | h
  · exact h ▸ hsig.1
  · exact h

/-- A terminator becomes a well-typed region, given that every register it reads
is in scope and every target it names is a reachable block whose immediate
dominator has a `cfg` in scope. -/
theorem Term.toRegion_hasType {sigs : List Signature} {sc : Scope R} {fn : Func R}
    {t : Term R} (hok : Scope.LabelsOk fn sc.labels) (hcov : sc.Covers t.uses)
    (hret : ∀ vs, t = .ret vs → vs.length = fn.sig.results)
    (htgt : ∀ tgt ∈ t.successors, fn.Reachable tgt ∧
      (Scope.labelDepth sc.labels (fn.digraph.idom tgt)).isSome)
    (hargs : ∀ tgt as, (tgt, as) ∈ t.args → as.length = fn.paramCount tgt) :
    Region.HasType (sc.ctx fn) (Term.toRegion sigs fn sc t) (sc.lctx fn) := by
  cases t with
  | jump tgt as =>
    obtain ⟨hr, hd⟩ := htgt tgt (by simp [Term.successors])
    have hlen := hargs tgt as (by simp [Term.args])
    refine .br (jumpLabel_at hok hr hd) ?_
    rw [← hlen]
    exact Scope.pack_hasType hcov
  | cond c t₁ a₁ t₂ a₂ =>
    obtain ⟨hr₁, hd₁⟩ := htgt t₁ (by simp [Term.successors])
    obtain ⟨hr₂, hd₂⟩ := htgt t₂ (by simp [Term.successors])
    have hl₁ := hargs t₁ a₁ (by simp [Term.args])
    have hl₂ := hargs t₂ a₂ (by simp [Term.args])
    have hc : sc.Covers [c] := hcov.mono (by intro x hx; simp [Term.uses] at hx ⊢; tauto)
    have hA₁ : sc.Covers a₁ := hcov.mono (by intro x hx; simp [Term.uses]; tauto)
    have hA₂ : sc.Covers a₂ := hcov.mono (by intro x hx; simp [Term.uses]; tauto)
    refine .case (A := Silmaril.Ty.unit) (B := Silmaril.Ty.unit)
      (.op (Scope.pack_hasType hc)) ?_ ?_
    · refine Region.HasType.renameVars (Silmaril.Isotope.SSA.Ren.wk _ _) (.br (jumpLabel_at hok hr₁ hd₁) ?_)
      rw [← hl₁]
      exact Scope.pack_hasType hA₁
    · refine Region.HasType.renameVars (Silmaril.Isotope.SSA.Ren.wk _ _) (.br (jumpLabel_at hok hr₂ hd₂) ?_)
      rw [← hl₂]
      exact Scope.pack_hasType hA₂
  | ret vs =>
    refine .br (Scope.lctx_ret hok) ?_
    rw [← hret vs rfl]
    exact Scope.pack_hasType hcov
  | trap => exact .br (Scope.lctx_trap hok) .unit

omit [DecidableEq R] in
/-- The label context a block's `cfg` presents to its children is the ambient
one extended by that `cfg`'s blocks. -/
theorem blockScope_lctx {fn : Func R} {sc : Scope R} {l : Label} {b : Block R} :
    (blockScope fn sc l b).lctx fn =
      List.ofFn (fun i : Fin (fn.domChildren (some l)).length =>
        packTy (fn.paramCount ((fn.domChildren (some l))[i.val]'i.isLt))) ++ sc.lctx fn := by
  rw [ofFn_getElem_map (fn.domChildren (some l)) (fun c => packTy (fn.paramCount c)),
    Scope.lctx, Scope.lctx, blockScope_labels, labelsCtx_cons, List.append_assoc]

/-- **Every block's region is well typed**, by induction down the dominator
tree. The fuel is the number of blocks minus the block's dominator depth, which
strictly decreases at every child. -/
theorem blockRegion_hasType {sigs : List Signature} {fn : Func R} (hwf : fn.WellFormed)
    (hcalls : fn.CallsMatch sigs) :
    ∀ (fuel : Nat) {sc : Scope R} {l : Label} {b : Block R},
      fn.block? l = some b → EnterOk fn sc l →
      fn.blocks.length - fn.digraph.domDepth l ≤ fuel →
      Region.HasType ((sc.push b.params).ctx fn) (blockRegion sigs fuel fn sc l)
        (sc.lctx fn) := by
  intro fuel
  induction fuel with
  | zero =>
    intro sc l b hb henter hfuel
    exact absurd hfuel (by have := domDepth_lt hwf.sig henter.reachable; omega)
  | succ fuel ih =>
    intro sc l b hb henter hfuel
    rw [blockRegion_succ hb]
    have hcov : ∀ (j : Nat) (r : R), fn.Defined l j r →
        ((sc.push b.params).afterOps (b.ops.take j)).HasReg r :=
      fun j r hd => covers_of_defined hb henter.domDefs hd
    refine opsRegion_hasType (fn := fn)
      (fun i o ho r hr => hcov i r (defined_of_usesDominated hwf.usesDominated hb ho hr))
      (opsCallsMatch_of_callsMatch hcalls hb) ?_
    -- the `cfg` of the dominator-tree children
    refine Region.HasType.cfg
      (R := fun i : Fin (fn.domChildren (some l)).length =>
        packTy (fn.paramCount ((fn.domChildren (some l))[i.val]'i.isLt))) ?_ ?_
    · rw [← blockScope_lctx]
      refine Term.toRegion_hasType (sc := blockScope fn sc l b) ?_ ?_ ?_ ?_ ?_
      · rw [blockScope_labels]
        exact ⟨rfl, henter.labelsOk⟩
      · intro r hr
        have := hcov b.ops.length r
          (defined_of_usesDominated_term hwf.usesDominated hb hr)
        rwa [List.take_length] at this
      · intro vs hterm
        exact ret_length hwf.sig hb hterm
      · intro tgt ht
        have hlt := lt_of_mem_successors hwf.sig hb ht
        have hedge : fn.Edge l tgt := Func.edge_of_term hb ht hlt
        have hreach : fn.Reachable tgt := henter.reachable.step hedge
        refine ⟨hreach, ?_⟩
        rw [blockScope_labels]
        cases hid : fn.digraph.idom tgt with
        | none =>
          rw [Scope.labelDepth]
          simpa using henter.root
        | some p =>
          have hdp : fn.digraph.Dominates p l :=
            Graph.Digraph.idom_dominates_of_edge hedge hid
          rw [Scope.labelDepth]
          split
          · rfl
          · rename_i hne
            exact henter.ancestors p ⟨hdp, fun h => hne (by rw [h])⟩
      · intro tgt as ha
        exact (params_length_of_argsMatch hwf.argsMatch hb ha).1
    · intro i
      have hmem : (fn.domChildren (some l))[i.val]'i.isLt ∈ fn.domChildren (some l) :=
        List.getElem_mem _
      have hid : fn.digraph.idom ((fn.domChildren (some l))[i.val]'i.isLt) = some l :=
        Graph.Digraph.mem_domTreeChildren_iff.mp hmem
      have hreach : fn.Reachable ((fn.domChildren (some l))[i.val]'i.isLt) :=
        Graph.Digraph.reachable_of_idom hid
      obtain ⟨b', hb'⟩ : ∃ b', fn.block? ((fn.domChildren (some l))[i.val]'i.isLt) = some b' :=
        ⟨_, List.getElem?_eq_getElem (lt_blocks_length_of_reachable hwf.sig hreach)⟩
      have hparam : fn.paramCount ((fn.domChildren (some l))[i.val]'i.isLt)
          = b'.params.length := by rw [Func.paramCount, hb']; rfl
      have henter' : EnterOk fn (blockScope fn sc l b)
          ((fn.domChildren (some l))[i.val]'i.isLt) := by
        refine ⟨?_, ?_, ?_, ?_, hreach⟩
        · rw [blockScope_labels]; exact ⟨rfl, henter.labelsOk⟩
        · intro a hsd
          have hdl : fn.digraph.Dominates a l := Graph.Digraph.dominates_idom hid hsd
          rw [blockScope_labels, Scope.labelDepth]
          split
          · rfl
          · rename_i hne
            exact henter.ancestors a ⟨hdl, fun h => hne (by rw [h])⟩
        · rw [blockScope_labels, Scope.labelDepth]
          simpa using henter.root
        · intro a r hsd hr
          have hdl : fn.digraph.Dominates a l := Graph.Digraph.dominates_idom hid hsd
          by_cases hal : a = l
          · subst hal
            rw [Func.defsOf, hb] at hr
            rcases List.mem_append.mp hr with hr | hr
            · exact Scope.hasReg_of_mem
                (Scope.vals_subset_afterOps (sc.push b.params) b.ops (by simp)) hr
            · obtain ⟨o, ho, hd⟩ := List.mem_flatMap.mp hr
              exact Scope.hasReg_of_mem (Scope.defs_mem_afterOps (sc.push b.params) ho) hd
          · refine (henter.domDefs a r ⟨hdl, hal⟩ hr).mono ?_
            refine List.Subset.trans ?_
              (Scope.vals_subset_afterOps (sc.push b.params) b.ops)
            simp
      have hfuel' : fn.blocks.length
          - fn.digraph.domDepth ((fn.domChildren (some l))[i.val]'i.isLt) ≤ fuel := by
        have := Graph.Digraph.domDepth_lt_of_idom hid
        omega
      have hres := ih hb' henter' hfuel'
      rw [blockScope_lctx, Scope.ctx_push] at hres
      rw [hparam]
      exact hres

/-- **The translation of a well-formed SSA function is a well-typed lambda-SSA
region**: it takes the function's packed arguments and exits either at the return
label with the packed results or at the trap label with `unit`. -/
theorem toLambdaSSA_hasType {sigs : List Signature} {fn : Func R} (h : fn.WellFormed)
    (hcall : fn.CallsMatch sigs) :
    Region.HasType [packTy fn.sig.params] (toLambdaSSA sigs fn)
      [packTy fn.sig.results, Silmaril.Ty.unit] := by
  obtain ⟨b, hb⟩ : ∃ b, fn.block? fn.entry = some b :=
    ⟨_, List.getElem?_eq_getElem h.sig.1⟩
  have hparams : b.params.length = fn.sig.params := by
    have hp := h.sig.2.1
    rw [hb] at hp
    simpa using hp
  have hpc : fn.paramCount fn.entry = fn.sig.params := by
    rw [Func.paramCount, hb]
    exact hparams
  refine Region.HasType.cfg (R := fun _ : Fin 1 => packTy fn.sig.params) (.br rfl (.var rfl))
    (fun _ => ?_)
  have hent : EnterOk fn ⟨[], [(none, 1)]⟩ fn.entry := by
    refine ⟨⟨by simp [Func.domChildren], trivial⟩, ?_, by simp [Scope.labelDepth], ?_,
      Graph.Digraph.reachable_entry _⟩
    · intro a hsd
      exact absurd (Graph.Digraph.Dominates.eq_entry hsd.1) hsd.2
    · intro a r hsd _
      exact absurd (Graph.Digraph.Dominates.eq_entry hsd.1) hsd.2
  have hmain := blockRegion_hasType h hcall fn.blocks.length hb hent (by omega)
  simpa [Scope.ctx, Scope.lctx, labelsCtx, Func.domChildren, hpc, hparams] using hmain

/-- The translation of a well-formed SSA function is scoped, which is what
`ofLambdaSSA` consumes. This is a corollary of typing, recorded separately
because that is the form the flattener's hypotheses take. -/
theorem toLambdaSSA_scoped {sigs : List Signature} {fn : Func R} (h : fn.WellFormed)
    (hcall : fn.CallsMatch sigs) :
    (toLambdaSSA sigs fn).Scoped 2 1 := by
  simpa using (toLambdaSSA_hasType h hcall).scoped

/-! ## Semantics preservation -/

/-! ### Reading and writing whole register lists

The translation moves whole lists of registers at once — a block's parameters,
one op's results, a terminator's arguments — so the frame facts it needs are
stated about `Frame.readAll` and `Frame.writeAll` rather than one register at a
time. -/

omit [DecidableEq R] in
/-- Reading no registers reads no words. -/
@[simp] theorem readAll_nil (fr : Frame R) : fr.readAll ([] : List R) = some [] := rfl

omit [DecidableEq R] in
/-- Reading a nonempty register list reads its head and then its tail. -/
theorem readAll_cons (fr : Frame R) (r : R) (rs : List R) :
    fr.readAll (r :: rs)
      = (fr.get r).bind fun w => (fr.readAll rs).bind fun ws => some (w :: ws) := by
  simp [Frame.readAll]

omit [DecidableEq R] in
/-- Reading a nonempty register list succeeds exactly when its head and its tail
both do. -/
theorem readAll_cons_eq_some {fr : Frame R} {r : R} {rs : List R} {ws : List Word} :
    fr.readAll (r :: rs) = some ws ↔
      ∃ w ws', fr.get r = some w ∧ fr.readAll rs = some ws' ∧ ws = w :: ws' := by
  rw [readAll_cons]
  constructor
  · intro h
    obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ws', hws, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    exact ⟨w, ws', hw, hws, h.symm⟩
  · rintro ⟨w, ws', hw, hws, rfl⟩
    rw [hw, hws]
    rfl

omit [DecidableEq R] in
/-- A successful read produces one word per register. -/
theorem readAll_length {fr : Frame R} : ∀ {rs : List R} {ws : List Word},
    fr.readAll rs = some ws → rs.length = ws.length
  | [], _, h => by simp at h; simp [h]
  | _ :: rs, _, h => by
    obtain ⟨_, ws', _, hws, rfl⟩ := readAll_cons_eq_some.mp h
    simpa using readAll_length hws

omit [DecidableEq R] in
/-- A successful read reads each of its registers. -/
theorem readAll_getElem {fr : Frame R} : ∀ {rs : List R} {ws : List Word} {j : Nat} {r : R},
    fr.readAll rs = some ws → rs[j]? = some r → ∃ w, ws[j]? = some w ∧ fr.get r = some w
  | [], _, _, _, _, hj => by simp at hj
  | r' :: rs, _, j, r, h, hj => by
    obtain ⟨w, ws', hw, hws, rfl⟩ := readAll_cons_eq_some.mp h
    cases j with
    | zero =>
      refine ⟨w, rfl, ?_⟩
      rw [← (show r' = r by simpa using hj)]
      exact hw
    | succ j => simpa using readAll_getElem hws (by simpa using hj)

omit [DecidableEq R] in
/-- A read depends only on the registers it names. -/
theorem readAll_congr {fr fr' : Frame R} : ∀ {rs : List R},
    (∀ r ∈ rs, fr'.get r = fr.get r) → fr'.readAll rs = fr.readAll rs
  | [], _ => rfl
  | r :: rs, h => by
    rw [readAll_cons, readAll_cons, h r (by simp), readAll_congr (fun x hx => h x (by simp [hx]))]

/-- Writing a register list needs one word per register. -/
theorem writeAll_length {fr fr' : Frame R} : ∀ {rs : List R} {ws : List Word},
    fr.writeAll rs ws = some fr' → rs.length = ws.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Frame.writeAll] at h
  | _ :: _, [], h => by simp [Frame.writeAll] at h
  | _ :: rs, _ :: ws, h => by
    have h' : (fr.set _ _).writeAll rs ws = some fr' := h
    simpa using writeAll_length h'

/-- One word per register always writes. -/
theorem writeAll_isSome (fr : Frame R) : ∀ {rs : List R} {ws : List Word},
    rs.length = ws.length → ∃ fr', fr.writeAll rs ws = some fr'
  | [], [], _ => ⟨fr, rfl⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | r :: rs, w :: ws, h => writeAll_isSome (fr.set r w) (by simpa using h)

/-- Writing a register list leaves every register outside it alone. -/
theorem get_writeAll_of_not_mem {fr fr' : Frame R} : ∀ {rs : List R} {ws : List Word} {r : R},
    fr.writeAll rs ws = some fr' → r ∉ rs → fr'.get r = fr.get r
  | [], [], _, h, _ => by rw [show fr' = fr from (Option.some.inj h).symm]
  | [], _ :: _, _, h, _ => by simp [Frame.writeAll] at h
  | _ :: _, [], _, h, _ => by simp [Frame.writeAll] at h
  | r' :: rs, w :: ws, r, h, hr => by
    have h' : (fr.set r' w).writeAll rs ws = some fr' := h
    have hne : r ≠ r' := fun hx => hr (by simp [hx])
    rw [get_writeAll_of_not_mem h' (fun hx => hr (by simp [hx])), Frame.get_set]
    simp [hne]

/-- Reading back a list of distinct registers just written returns the words
written. -/
theorem readAll_writeAll {fr fr' : Frame R} : ∀ {rs : List R} {ws : List Word},
    fr.writeAll rs ws = some fr' → rs.Nodup → fr'.readAll rs = some ws
  | [], [], h, _ => by rw [show fr' = fr from (Option.some.inj h).symm]; rfl
  | [], _ :: _, h, _ => by simp [Frame.writeAll] at h
  | _ :: _, [], h, _ => by simp [Frame.writeAll] at h
  | r :: rs, w :: ws, h, hnd => by
    have h' : (fr.set r w).writeAll rs ws = some fr' := h
    have hhd : fr'.get r = some w := by
      rw [get_writeAll_of_not_mem h' (List.nodup_cons.mp hnd).1, Frame.get_set]
      simp
    rw [readAll_cons, hhd, readAll_writeAll h' (List.nodup_cons.mp hnd).2]
    rfl

/-- A lambda-SSA environment matches an RTL frame at a scope when every tuple the
scope binds holds the frame's values for its registers. -/
def Scope.Agrees (sc : Scope R) (env : Semantics.Env Word) (fr : Frame R) : Prop :=
  ∀ i g, sc.vals[i]? = some g → ∃ ws, fr.readAll g = some ws ∧ env i = packValues ws


/-! ### Single assignment makes every definition fresh

`Func.SingleAssignment` is a `Nodup` on the concatenation of every block's
definitions. What the semantics needs from it is local: an op's destinations are
untouched by the block's parameters, by the earlier ops of the block and by every
other block, so writing them cannot disturb a value the translation has already
bound. -/

/-- Distinct positions of a list whose flattening is duplicate-free contribute
disjoint lists. -/
theorem flatMap_disjoint {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ {i j : Nat} {a c : α}, i ≠ j →
      l[i]? = some a → l[j]? = some c → ∀ {x : β}, x ∈ f a → x ∉ f c
  | [], _, _, _, _, _, _, ha, _, _, _ => by simp at ha
  | d :: ds, hnd, i, j, a, c, hij, ha, hc, x, hx => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j =>
        obtain rfl : a = d := (Option.some.inj (by simpa using ha)).symm
        intro hxc
        exact hnd.2.2 x hx x
          (List.mem_flatMap.mpr ⟨c, List.mem_of_getElem? (by simpa using hc), hxc⟩) rfl
    | succ i =>
      cases j with
      | zero =>
        obtain rfl : c = d := (Option.some.inj (by simpa using hc)).symm
        intro hxc
        exact hnd.2.2 x hxc x
          (List.mem_flatMap.mpr ⟨a, List.mem_of_getElem? (by simpa using ha), hx⟩) rfl
      | succ j =>
        exact flatMap_disjoint hnd.2.1 (show i ≠ j by omega)
          (by simpa using ha) (by simpa using hc) hx

/-- Every position of a list whose flattening is duplicate-free contributes a
duplicate-free list. -/
theorem flatMap_nodup_at {α β : Type} {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ {i : Nat} {a : α}, l[i]? = some a → (f a).Nodup
  | [], _, _, _, ha => by simp at ha
  | d :: ds, hnd, i, a, ha => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    cases i with
    | zero => exact (Option.some.inj (by simpa using ha)).symm ▸ hnd.1
    | succ i => exact flatMap_nodup_at hnd.2.1 (by simpa using ha)

omit [DecidableEq R] in
/-- The registers a block defines are the ones the whole function's `Nodup`
constrains. -/
theorem defsOf_eq {fn : Func R} {l : Label} {b : Block R} (hb : fn.block? l = some b) :
    fn.defsOf l = b.defs := by rw [Func.defsOf, hb]

omit [DecidableEq R] in
/-- Distinct blocks of a single-assignment function define disjoint registers. -/
theorem defsOf_disjoint {fn : Func R} (h : fn.SingleAssignment) {a l : Label} (hne : a ≠ l)
    {r : R} (hr : r ∈ fn.defsOf a) : r ∉ fn.defsOf l := by
  cases ha : fn.block? a with
  | none => rw [Func.defsOf, ha] at hr; simp at hr
  | some ba =>
    cases hl : fn.block? l with
    | none => rw [Func.defsOf, hl]; simp
    | some bl =>
      rw [Func.defsOf, ha] at hr
      rw [Func.defsOf, hl]
      exact flatMap_disjoint h hne ha hl hr

omit [DecidableEq R] in
/-- A single-assignment function defines each block's registers only once. -/
theorem block_defs_nodup {fn : Func R} (h : fn.SingleAssignment) {l : Label} {b : Block R}
    (hb : fn.block? l = some b) : b.defs.Nodup := flatMap_nodup_at h hb

omit [DecidableEq R] in
/-- A block of a single-assignment function has distinct parameters. -/
theorem params_nodup {fn : Func R} (h : fn.SingleAssignment) {l : Label} {b : Block R}
    (hb : fn.block? l = some b) : b.params.Nodup :=
  (List.nodup_append.mp (block_defs_nodup h hb)).1

omit [DecidableEq R] in
/-- An op of a single-assignment function has distinct destinations. -/
theorem op_defs_nodup {fn : Func R} (h : fn.SingleAssignment) {l : Label} {b : Block R}
    (hb : fn.block? l = some b) {j : Nat} {o : Op R} (ho : b.ops[j]? = some o) : o.defs.Nodup :=
  flatMap_nodup_at (List.nodup_append.mp (block_defs_nodup h hb)).2.1 ho

omit [DecidableEq R] in
/-- An op's destinations are neither its block's parameters nor the destinations
of an earlier op of the same block. -/
theorem op_defs_fresh_in_block {fn : Func R} (h : fn.SingleAssignment) {l : Label} {b : Block R}
    (hb : fn.block? l = some b) {j : Nat} {o : Op R} (ho : b.ops[j]? = some o) {r : R}
    (hr : r ∈ o.defs) :
    r ∉ b.params ∧ ∀ o' ∈ b.ops.take j, r ∉ o'.defs := by
  have hnd := block_defs_nodup h hb
  rw [Block.defs, List.nodup_append] at hnd
  have hmem : r ∈ b.ops.flatMap Op.defs := List.mem_flatMap.mpr ⟨o, List.mem_of_getElem? ho, hr⟩
  refine ⟨fun hp => hnd.2.2 r hp r hmem rfl, ?_⟩
  intro o' ho' hr'
  have hj : j < b.ops.length := (List.getElem?_eq_some_iff.mp ho).1
  have hget : b.ops[j] = o := by
    rw [List.getElem?_eq_getElem hj] at ho
    exact Option.some.inj ho
  have hsplit : b.ops = b.ops.take j ++ (o :: b.ops.drop (j + 1)) := by
    rw [← hget, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hnd2 := hnd.2.1
  rw [hsplit, List.flatMap_append, List.nodup_append] at hnd2
  exact hnd2.2.2 r (List.mem_flatMap.mpr ⟨o', ho', hr'⟩) r
    (by rw [List.flatMap_cons]; exact List.mem_append_left _ hr) rfl

/-! ### Scopes, semantically

`Scope.Agrees` is the semantic counterpart of `Scope.Covers`: `Covers` says the
translation can *name* a register, `Agrees` says the name denotes the frame's
value for it. The lemmas below are the three ways the invariant moves: binding
one more tuple, changing the frame at registers out of scope, and passing to an
enclosing `cfg`'s scope. -/

omit [DecidableEq R] in
/-- The tuples a block's straight-line code binds are its ops' destinations, most
recent first. -/
theorem Scope.afterOps_vals (sc : Scope R) : ∀ (ops : List (Op R)),
    (sc.afterOps ops).vals = (ops.map Op.defs).reverse ++ sc.vals
  | [] => rfl
  | o :: os => by
    rw [Scope.afterOps_cons, Scope.afterOps_vals (sc.push o.defs) os]
    simp

omit [DecidableEq R] in
/-- Binding one more tuple puts exactly its registers in scope. -/
@[simp] theorem Scope.hasReg_push {sc : Scope R} {g : List R} {r : R} :
    (sc.push g).HasReg r ↔ r ∈ g ∨ sc.HasReg r := by
  simp [Scope.HasReg, Scope.push_vals]

omit [DecidableEq R] in
/-- A register is in scope after a block's straight-line code exactly when it was
already in scope or one of the ops defines it. -/
theorem Scope.hasReg_afterOps {sc : Scope R} {ops : List (Op R)} {r : R} :
    (sc.afterOps ops).HasReg r ↔ sc.HasReg r ∨ ∃ o ∈ ops, r ∈ o.defs := by
  simp only [Scope.HasReg, Scope.afterOps_vals, List.mem_append, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨g, hg | hg, hr⟩
    · obtain ⟨o, ho, rfl⟩ := hg
      exact Or.inr ⟨o, ho, hr⟩
    · exact Or.inl ⟨g, hg, hr⟩
  · rintro (⟨g, hg, hr⟩ | ⟨o, ho, hr⟩)
    · exact ⟨g, Or.inr hg, hr⟩
    · exact ⟨o.defs, Or.inl ⟨o, ho, rfl⟩, hr⟩

omit [DecidableEq R] in
/-- A register list is fresh for a scope when the scope binds none of it. Writing
a fresh list is what cannot disturb a value the translation has already bound. -/
def Scope.Fresh (sc : Scope R) (rs : List R) : Prop := ∀ r ∈ rs, ¬ sc.HasReg r

omit [DecidableEq R] in
/-- Binding one more tuple preserves agreement, provided the frame already holds
the tuple's values. -/
theorem Scope.Agrees.push {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R}
    (h : sc.Agrees env fr) {g : List R} {ws : List Word} (hg : fr.readAll g = some ws) :
    (sc.push g).Agrees (Semantics.extend env (packValues ws)) fr := by
  intro i g' hi
  cases i with
  | zero =>
    obtain rfl : g = g' := Option.some.inj (by simpa using hi)
    exact ⟨ws, hg, rfl⟩
  | succ i => simpa using h i g' (by simpa using hi)

omit [DecidableEq R] in
/-- Agreement depends only on the frame's values at the registers in scope. -/
theorem Scope.Agrees.frame {sc : Scope R} {env : Semantics.Env Word} {fr fr' : Frame R}
    (h : sc.Agrees env fr) (hsame : ∀ r, sc.HasReg r → fr'.get r = fr.get r) :
    sc.Agrees env fr' := by
  intro i g hi
  obtain ⟨ws, hws, henv⟩ := h i g hi
  refine ⟨ws, ?_, henv⟩
  rw [readAll_congr (fun r hr => hsame r ⟨g, List.mem_of_getElem? hi, hr⟩)]
  exact hws

omit [DecidableEq R] in
/-- Agreement passes outwards to an enclosing `cfg`'s scope: dropping the
innermost tuples and shifting the environment past them leaves it intact. -/
theorem Scope.Agrees.drop {sc sc' : Scope R} {env env' : Semantics.Env Word} {fr : Frame R}
    (h : sc.Agrees env fr) {k : Nat} (hvals : sc'.vals = sc.vals.drop k)
    (henv : ∀ i, env' i = env (i + k)) : sc'.Agrees env' fr := by
  intro i g hi
  rw [hvals, List.getElem?_drop] at hi
  obtain ⟨ws, hws, he⟩ := h (k + i) g hi
  refine ⟨ws, hws, ?_⟩
  rw [henv i, Nat.add_comm]
  exact he

omit [DecidableEq R] in
/-- Every register in scope has a value in the frame. -/
theorem Scope.Agrees.get_isSome {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R}
    (h : sc.Agrees env fr) {r : R} (hr : sc.HasReg r) : ∃ w, fr.get r = some w := by
  obtain ⟨g, hg, hrg⟩ := hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hg
  obtain ⟨ws, hws, -⟩ := h i g hi
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hrg
  obtain ⟨w, -, hw⟩ := readAll_getElem hws hj
  exact ⟨w, hw⟩

omit [DecidableEq R] in
/-- A covered register list reads. -/
theorem Scope.Agrees.readAll {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R}
    (h : sc.Agrees env fr) : ∀ {rs : List R}, sc.Covers rs → ∃ ws, fr.readAll rs = some ws
  | [], _ => ⟨[], rfl⟩
  | r :: rs, hcov => by
    obtain ⟨w, hw⟩ := h.get_isSome (hcov r (by simp))
    obtain ⟨ws, hws⟩ := h.readAll (hcov.mono (fun x hx => List.mem_cons_of_mem r hx))
    exact ⟨w :: ws, readAll_cons_eq_some.mpr ⟨w, ws, hw, hws, rfl⟩⟩

/-- A located register's value sits at the position the search found. -/
theorem Scope.Agrees.findReg {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R}
    (h : sc.Agrees env fr) {r : R} {i j : Nat} (hij : Scope.findReg sc.vals r 0 = some (i, j)) :
    ∃ w ws, fr.get r = some w ∧ env i = packValues ws ∧ ws[j]? = some w := by
  obtain ⟨-, g, hg, -, hr⟩ := Scope.findReg_spec hij
  rw [Nat.sub_zero] at hg
  obtain ⟨ws, hws, he⟩ := h i g hg
  obtain ⟨w, hwj, hw⟩ := readAll_getElem hws hr
  exact ⟨w, ws, hw, he, hwj⟩

/-! ### Inverting evaluation

`Tm.Eval` and `Region.Eval` are indexed by the term and the region, so a
derivation for something the translation emitted can be taken apart. These are
the inversions that the case analyses below go through. -/

/-- A variable evaluates to its value and changes nothing. -/
theorem eval_var_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {i : Nat} {s s' : σ} {v : Value Word}
    (h : Semantics.Tm.Eval instr env (.var i) s v s') : v = env i ∧ s' = s := by
  cases h
  exact ⟨rfl, rfl⟩

/-- The unit term evaluates to unit and changes nothing. -/
theorem eval_unit_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {s s' : σ} {v : Value Word}
    (h : Semantics.Tm.Eval instr env .unit s v s') : v = .unit ∧ s' = s := by
  cases h
  exact ⟨rfl, rfl⟩

/-- A pair evaluates its components left to right. -/
theorem eval_pair_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {a b : Tm Φ} {s s' : σ} {v : Value Word}
    (h : Semantics.Tm.Eval instr env (.pair a b) s v s') :
    ∃ va vb s₁, Semantics.Tm.Eval instr env a s va s₁ ∧
      Semantics.Tm.Eval instr env b s₁ vb s' ∧ v = .pair va vb := by
  cases h with | pair h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

/-- A pair elimination evaluates its scrutinee to a pair. -/
theorem eval_let₂_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {a b : Tm Φ} {s s' : σ} {v : Value Word}
    (h : Semantics.Tm.Eval instr env (.let₂ a b) s v s') :
    ∃ va vb s₁, Semantics.Tm.Eval instr env a s (.pair va vb) s₁ ∧
      Semantics.Tm.Eval instr (Semantics.extend (Semantics.extend env va) vb) b s₁ v s' := by
  cases h with | let₂ h₁ h₂ => exact ⟨_, _, _, h₁, h₂⟩

/-- An operator application evaluates its argument and then takes a transition. -/
theorem eval_op_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {f : Φ} {a : Tm Φ} {s s' : σ} {v : Value Word}
    (h : Semantics.Tm.Eval instr env (.op f a) s v s') :
    ∃ va s₁, Semantics.Tm.Eval instr env a s va s₁ ∧ instr f va s₁ v s' := by
  cases h with | op h₁ h₂ => exact ⟨_, _, h₁, h₂⟩

/-- A branch evaluates its argument and exits at its label. -/
theorem region_eval_br_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {label : Nat} {arg : Tm Φ} {s s' : σ} {lbl : Nat}
    {v : Value Word} (h : Semantics.Region.Eval instr env (.br label arg) s lbl v s') :
    lbl = label ∧ Semantics.Tm.Eval instr env arg s v s' := by
  cases h with | br h₁ => exact ⟨rfl, h₁⟩

/-- A region's `let₁` evaluates its argument and then its body. -/
theorem region_eval_let₁_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {a : Tm Φ} {r : Region Φ} {s s' : σ} {lbl : Nat}
    {v : Value Word} (h : Semantics.Region.Eval instr env (.let₁ a r) s lbl v s') :
    ∃ va s₁, Semantics.Tm.Eval instr env a s va s₁ ∧
      Semantics.Region.Eval instr (Semantics.extend env va) r s₁ lbl v s' := by
  cases h with | let₁ h₁ h₂ => exact ⟨_, _, h₁, h₂⟩

/-- A region's `case` takes the branch its scrutinee selects. -/
theorem region_eval_case_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {a : Tm Φ} {l r : Region Φ} {s s' : σ} {lbl : Nat}
    {v : Value Word} (h : Semantics.Region.Eval instr env (.case a l r) s lbl v s') :
    (∃ va s₁, Semantics.Tm.Eval instr env a s (.inl va) s₁ ∧
        Semantics.Region.Eval instr (Semantics.extend env va) l s₁ lbl v s') ∨
      (∃ va s₁, Semantics.Tm.Eval instr env a s (.inr va) s₁ ∧
        Semantics.Region.Eval instr (Semantics.extend env va) r s₁ lbl v s') := by
  cases h with
  | case_inl h₁ h₂ => exact Or.inl ⟨_, _, h₁, h₂⟩
  | case_inr h₁ h₂ => exact Or.inr ⟨_, _, h₁, h₂⟩

/-- A `cfg` runs its entry and then follows internal transfers. -/
theorem region_eval_cfg_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {entry : Region Φ} {n : Nat} {blocks : Fin n → Region Φ}
    {s s' : σ} {lbl : Nat} {v : Value Word}
    (h : Semantics.Region.Eval instr env (.cfg entry n blocks) s lbl v s') :
    ∃ first initial s₁, Semantics.Region.Eval instr env entry s first initial s₁ ∧
      Semantics.Region.Follow instr env blocks first initial s₁ lbl v s' := by
  cases h with | cfg h₁ h₂ => exact ⟨_, _, _, h₁, h₂⟩

/-! ### Projections, references and packs evaluate -/

/-- A packed tuple that is a pair has a first word and a shorter tail. -/
theorem packValues_eq_pair {ws : List Word} {a b : Value Word} (h : packValues ws = .pair a b) :
    ∃ w ws', ws = w :: ws' ∧ a = .atom w ∧ b = packValues ws' := by
  cases ws with
  | nil => simp [packValues] at h
  | cons w ws' =>
    rw [packValues_cons] at h
    obtain ⟨rfl, rfl⟩ := Isotope.Value.pair.inj h
    exact ⟨w, ws', rfl, rfl, rfl⟩

/-- **A projection reads one component of a packed tuple**: the `j`-th
elimination chain applied to a variable holding `packValues ws` evaluates exactly
to the atom at position `j`, leaving the state alone. -/
theorem eval_proj_var {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop} :
    ∀ (j : Nat) {env : Semantics.Env Word} {i : Nat} {ws : List Word} {s s' : σ}
      {v : Value Word}, env i = packValues ws →
      (Semantics.Tm.Eval instr env (proj j (.var i)) s v s' ↔
        s' = s ∧ ∃ w, ws[j]? = some w ∧ v = .atom w) := by
  intro j
  induction j with
  | zero =>
    intro env i ws s s' v hi
    constructor
    · intro h
      obtain ⟨va, vb, s₁, h₁, h₂⟩ := eval_let₂_inv h
      obtain ⟨hv, rfl⟩ := eval_var_inv h₁
      obtain ⟨w, ws', rfl, rfl, rfl⟩ := packValues_eq_pair (hv.trans hi).symm
      obtain ⟨rfl, rfl⟩ := eval_var_inv h₂
      exact ⟨rfl, w, rfl, rfl⟩
    · rintro ⟨rfl, w, hw, rfl⟩
      obtain ⟨ws', rfl⟩ : ∃ ws', ws = w :: ws' := by
        cases ws with
        | nil => simp at hw
        | cons w₀ ws' =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
          exact ⟨ws', by rw [hw]⟩
      exact .let₂ (Semantics.Tm.Eval.var_of_eq (by rw [hi]; rfl))
        (Semantics.Tm.Eval.var_of_eq rfl)
  | succ j ih =>
    intro env i ws s s' v hi
    constructor
    · intro h
      obtain ⟨va, vb, s₁, h₁, h₂⟩ := eval_let₂_inv h
      obtain ⟨hv, rfl⟩ := eval_var_inv h₁
      obtain ⟨w, ws', rfl, rfl, rfl⟩ := packValues_eq_pair (hv.trans hi).symm
      obtain ⟨rfl, w', hw', rfl⟩ := (ih (i := 0) (ws := ws') rfl).mp h₂
      exact ⟨rfl, w', by simpa using hw', rfl⟩
    · rintro ⟨rfl, w, hw, rfl⟩
      obtain ⟨w₀, ws', rfl⟩ : ∃ w₀ ws', ws = w₀ :: ws' := by
        cases ws with
        | nil => simp at hw
        | cons w₀ ws' => exact ⟨w₀, ws', rfl⟩
      refine .let₂ (Semantics.Tm.Eval.var_of_eq (by rw [hi]; rfl)) ?_
      exact (ih (i := 0) (ws := ws') rfl).mpr ⟨rfl, w, by simpa using hw, rfl⟩

/-- **A register reference denotes the frame's value for it**, for a register the
scope binds. -/
theorem Scope.eval_ref_iff {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R} (hag : sc.Agrees env fr)
    {r : R} (hr : sc.HasReg r) {w : Word} (hw : fr.get r = some w) {s s' : σ}
    {v : Value Word} :
    Semantics.Tm.Eval instr env (sc.ref r) s v s' ↔ (s' = s ∧ v = .atom w) := by
  obtain ⟨⟨i, j⟩, hij⟩ := Option.isSome_iff_exists.mp (Scope.findReg_isSome_of_hasReg hr)
  obtain ⟨w', ws, hw', he, hwj⟩ := hag.findReg hij
  obtain rfl : w' = w := Option.some.inj (hw'.symm.trans hw)
  rw [Scope.ref, hij, eval_proj_var j he]
  constructor
  · rintro ⟨rfl, w'', hw'', rfl⟩
    exact ⟨rfl, by rw [Option.some.inj (hw''.symm.trans hwj)]⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, _, hwj, rfl⟩

/-- **A packed register list denotes the frame's values for it**, for registers
the scope binds. -/
theorem Scope.eval_pack_iff {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R} (hag : sc.Agrees env fr) :
    ∀ {rs : List R}, sc.Covers rs → ∀ {ws : List Word}, fr.readAll rs = some ws →
      ∀ {s s' : σ} {v : Value Word},
        (Semantics.Tm.Eval instr env (sc.pack rs) s v s' ↔ (s' = s ∧ v = packValues ws)) := by
  intro rs
  induction rs with
  | nil =>
    intro _ ws hws s s' v
    obtain rfl : ws = [] := (Option.some.inj hws).symm
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := eval_unit_inv h
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact .unit
  | cons r rs ih =>
    intro hcov ws hws s s' v
    obtain ⟨w, ws', hw, hws', rfl⟩ := readAll_cons_eq_some.mp hws
    constructor
    · intro h
      obtain ⟨va, vb, s₁, h₁, h₂, rfl⟩ := eval_pair_inv h
      obtain ⟨rfl, rfl⟩ := (Scope.eval_ref_iff hag (hcov r (by simp)) hw).mp h₁
      obtain ⟨rfl, rfl⟩ :=
        (ih (hcov.mono (fun x hx => List.mem_cons_of_mem r hx)) hws').mp h₂
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact .pair ((Scope.eval_ref_iff hag (hcov r (by simp)) hw).mpr ⟨rfl, rfl⟩)
        ((ih (hcov.mono (fun x hx => List.mem_cons_of_mem r hx)) hws').mpr ⟨rfl, rfl⟩)

/-! ### One op

`Op.toTm` is a term that evaluates exactly when the op executes. A `move` is the
identity opcode, a `store` produces the empty tuple, and a `call` goes through
the oracle; the common shape is that the op writes `Op.defs` with the words the
term produces. -/

/-- A straight-line run splits at its first op. -/
theorem Ops.exec_cons_inv {oracle : CallOracle} {o : Op R} {os : List (Op R)}
    {fr fr₂ : Frame R} {m m₂ : Memory} (h : Ops.Exec oracle (o :: os) fr m fr₂ m₂) :
    ∃ fr₁ m₁, Ops.Exec oracle [o] fr m fr₁ m₁ ∧ Ops.Exec oracle os fr₁ m₁ fr₂ m₂ := by
  cases h with
  | op he hrest => exact ⟨_, _, .op he .nil, hrest⟩
  | call hr ho hw hrest => exact ⟨_, _, .call hr ho hw .nil, hrest⟩

omit [DecidableEq R] in
/-- Reading a single register. -/
theorem readAll_singleton {fr : Frame R} {r : R} {w : Word} (h : fr.get r = some w) :
    fr.readAll [r] = some [w] := readAll_cons_eq_some.mpr ⟨w, [], h, rfl, rfl⟩

omit [DecidableEq R] in
/-- Reading a pair of registers. -/
theorem readAll_pair {fr : Frame R} {r r' : R} {w w' : Word} (h : fr.get r = some w)
    (h' : fr.get r' = some w') : fr.readAll [r, r'] = some [w, w'] :=
  readAll_cons_eq_some.mpr ⟨w, [w'], h, readAll_singleton h', rfl⟩

/-- **An op's term evaluates when the op executes**, to the packed tuple of the
words the op writes. -/
theorem Op.eval_toTm_of_exec {sigs : List Signature} {oracle : CallOracle} {sc : Scope R}
    {env : Semantics.Env Word} {fr fr' : Frame R} (hag : sc.Agrees env fr) {o : Op R}
    (hcov : sc.Covers o.uses) {m m' : Memory} (hex : Ops.Exec oracle [o] fr m fr' m') :
    ∃ ws, fr.writeAll o.defs ws = some fr' ∧
      Semantics.Tm.Eval (Opcode.step (sigs := sigs) oracle) env (Op.toTm sigs sc o) m
        (packValues ws) m' := by
  cases o with
  | const d val =>
    cases hex with
    | op he hrest =>
      cases hrest
      simp only [Op.exec, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨[val], rfl, .op .unit .const⟩
  | move d s =>
    cases hex with
    | op he hrest =>
      cases hrest
      simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨x, hx, rfl, rfl⟩ := he
      refine ⟨[x], rfl, .op ?_ .move⟩
      exact (Scope.eval_pack_iff hag hcov (readAll_singleton hx)).mpr ⟨rfl, rfl⟩
  | unary op d s =>
    cases hex with
    | op he hrest =>
      cases hrest
      simp only [Op.exec, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨x, hx, rfl, rfl⟩ := he
      refine ⟨[op.eval x], rfl, .op ?_ .unary⟩
      exact (Scope.eval_pack_iff hag hcov (readAll_singleton hx)).mpr ⟨rfl, rfl⟩
  | binary op d a b =>
    cases hex with
    | op he hrest =>
      cases hrest
      simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨x, hx, y, hy, z, hz, rfl, rfl⟩ := he
      refine ⟨[z], rfl, .op ?_ (.binary hz)⟩
      exact (Scope.eval_pack_iff hag hcov (readAll_pair hx hy)).mpr ⟨rfl, rfl⟩
  | load w e d base off =>
    cases hex with
    | op he hrest =>
      cases hrest
      simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨a, ha, z, hz, rfl, rfl⟩ := he
      refine ⟨[z], rfl, .op ?_ (.load hz)⟩
      exact (Scope.eval_pack_iff hag hcov (readAll_singleton ha)).mpr ⟨rfl, rfl⟩
  | store w base off src =>
    cases hex with
    | op he hrest =>
      cases hrest
      simp only [Op.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at he
      obtain ⟨a, ha, x, hx, m₂, hm₂, rfl, rfl⟩ := he
      refine ⟨[], rfl, .op ?_ (.store hm₂)⟩
      exact (Scope.eval_pack_iff hag hcov (readAll_pair ha hx)).mpr ⟨rfl, rfl⟩
  | call f args results =>
    cases hex with
    | op he hrest => simp [Op.exec] at he
    | call hr ho hw hrest =>
      cases hrest
      refine ⟨_, hw, .op ?_ (.call ho)⟩
      exact (Scope.eval_pack_iff hag hcov hr).mpr ⟨rfl, rfl⟩

/-! ### A block's straight-line code -/

/-- **The `let₁` chain runs the block's ops.** Running the ops takes the scope
and the environment to a scope and an environment that still agree with the
frame, and the chain then runs whatever region follows it. The freshness
hypothesis is what single assignment supplies: an op writes registers the scope
has not already bound, so binding its results disturbs nothing. -/
theorem opsRegion_eval_of_exec {sigs : List Signature} {oracle : CallOracle} :
    ∀ (ops : List (Op R)) {sc : Scope R} {env : Semantics.Env Word} {fr fr₁ : Frame R}
      {m m₁ : Memory},
      sc.Agrees env fr →
      (∀ i o, ops[i]? = some o → (sc.afterOps (ops.take i)).Covers o.uses) →
      (∀ i o, ops[i]? = some o → (sc.afterOps (ops.take i)).Fresh o.defs ∧ o.defs.Nodup) →
      Ops.Exec oracle ops fr m fr₁ m₁ →
      ∃ env₁ : Semantics.Env Word, (sc.afterOps ops).Agrees env₁ fr₁ ∧
        (∀ i, env₁ (i + ops.length) = env i) ∧
        ∀ {k : Region (Opcode sigs)} {label : Nat} {value : Value Word} {m₂ : Memory},
          Semantics.Region.Eval (Opcode.step oracle) env₁ k m₁ label value m₂ →
          Semantics.Region.Eval (Opcode.step oracle) env (opsRegion sigs sc ops k) m
            label value m₂ := by
  intro ops
  induction ops with
  | nil =>
    intro sc env fr fr₁ m m₁ hag _ _ hex
    cases hex
    exact ⟨env, hag, fun _ => rfl, fun h => h⟩
  | cons o os ih =>
    intro sc env fr fr₁ m m₁ hag hcov hfresh hex
    obtain ⟨fr', m', hone, hrest⟩ := Ops.exec_cons_inv hex
    obtain ⟨hfr, hnd⟩ := hfresh 0 o rfl
    obtain ⟨ws, hw, heval⟩ := Op.eval_toTm_of_exec (sigs := sigs) hag (hcov 0 o rfl) hone
    have hsame : ∀ r, sc.HasReg r → fr'.get r = fr.get r := fun r hr =>
      get_writeAll_of_not_mem hw (fun hx => hfr r hx hr)
    have hag' : (sc.push o.defs).Agrees (Semantics.extend env (packValues ws)) fr' :=
      (hag.frame hsame).push (readAll_writeAll hw hnd)
    have hcov' : ∀ i o', os[i]? = some o' →
        ((sc.push o.defs).afterOps (os.take i)).Covers o'.uses := by
      intro i o' ho'
      exact hcov (i + 1) o' (by simpa using ho')
    have hfresh' : ∀ i o', os[i]? = some o' →
        ((sc.push o.defs).afterOps (os.take i)).Fresh o'.defs ∧ o'.defs.Nodup := by
      intro i o' ho'
      exact hfresh (i + 1) o' (by simpa using ho')
    obtain ⟨env₁, hag₁, hshift, hrun⟩ := ih hag' hcov' hfresh' hrest
    refine ⟨env₁, hag₁, ?_, ?_⟩
    · intro i
      have h := hshift (i + 1)
      rw [List.length_cons, show i + (os.length + 1) = i + 1 + os.length by omega]
      simpa using h
    · intro k label value m₂ hk
      exact .let₁ heval (hrun hk)

/-! ### Terminators -/

/-- A jump becomes a branch to the dominator-tree label of its target. -/
theorem Term.eval_toRegion_jump {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R} (hag : sc.Agrees env fr)
    {tgt : Label} {as : List R} (hcov : sc.Covers as) {vals : List Word}
    (hread : fr.readAll as = some vals) {m : Memory} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
      (Term.toRegion sigs fn sc (.jump tgt as)) m (fn.jumpLabel sc tgt) (packValues vals) m :=
  .br ((Scope.eval_pack_iff hag hcov hread).mpr ⟨rfl, rfl⟩)

/-- A conditional with a zero condition becomes a `case` taking the right
injection, so the second target. -/
theorem Term.eval_toRegion_cond_zero {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R} (hag : sc.Agrees env fr)
    {c : R} {t₁ t₂ : Label} {a₁ a₂ : List R} (hc : sc.Covers [c]) (hA : sc.Covers a₂)
    (hget : fr.get c = some 0) {vals : List Word} (hread : fr.readAll a₂ = some vals)
    {m : Memory} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
      (Term.toRegion sigs fn sc (.cond c t₁ a₁ t₂ a₂)) m
      (fn.jumpLabel sc t₂) (packValues vals) m := by
  have hscrut : Semantics.Tm.Eval (Opcode.step (sigs := sigs) oracle) env (sc.pack [c]) m
      (packValues [0]) m := (Scope.eval_pack_iff hag hc (readAll_singleton hget)).mpr ⟨rfl, rfl⟩
  refine .case_inr (va := (Value.unit : Value Word))
    (.op hscrut (Opcode.step_test_iff.mpr ⟨rfl, by simp⟩)) ?_
  exact Semantics.Region.Eval.renameVars
    (.br ((Scope.eval_pack_iff hag hA hread).mpr ⟨rfl, rfl⟩)) (fun _ => rfl)

/-- A conditional with a nonzero condition becomes a `case` taking the left
injection, so the first target. -/
theorem Term.eval_toRegion_cond_nonzero {sigs : List Signature} {oracle : CallOracle}
    {fn : Func R} {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R}
    (hag : sc.Agrees env fr) {c : R} {t₁ t₂ : Label} {a₁ a₂ : List R} {x : Word}
    (hc : sc.Covers [c]) (hA : sc.Covers a₁) (hx : x ≠ 0) (hget : fr.get c = some x)
    {vals : List Word} (hread : fr.readAll a₁ = some vals) {m : Memory} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
      (Term.toRegion sigs fn sc (.cond c t₁ a₁ t₂ a₂)) m
      (fn.jumpLabel sc t₁) (packValues vals) m := by
  have hscrut : Semantics.Tm.Eval (Opcode.step (sigs := sigs) oracle) env (sc.pack [c]) m
      (packValues [x]) m := (Scope.eval_pack_iff hag hc (readAll_singleton hget)).mpr ⟨rfl, rfl⟩
  refine .case_inl (va := (Value.unit : Value Word))
    (.op hscrut (Opcode.step_test_iff.mpr ⟨rfl, by simpa using hx⟩)) ?_
  exact Semantics.Region.Eval.renameVars
    (.br ((Scope.eval_pack_iff hag hA hread).mpr ⟨rfl, rfl⟩)) (fun _ => rfl)

/-- A return becomes a branch to the return label with the packed results. -/
theorem Term.eval_toRegion_ret {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R} (hag : sc.Agrees env fr)
    {regs : List R} (hcov : sc.Covers regs) {vals : List Word}
    (hread : fr.readAll regs = some vals) {m : Memory} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
      (Term.toRegion sigs fn sc (.ret regs)) m sc.depth (packValues vals) m :=
  .br ((Scope.eval_pack_iff hag hcov hread).mpr ⟨rfl, rfl⟩)

/-- A trap becomes a branch to the trap label with `unit`. -/
theorem Term.eval_toRegion_trap {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    {sc : Scope R} {env : Semantics.Env Word} {m : Memory} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
      (Term.toRegion sigs fn sc (Term.trap : Term R)) m (sc.depth + 1) .unit m := .br .unit

/-! ### The descent down the dominator tree

A `Region.Eval` of `blockRegion` ends either at the two external labels or at a
transfer the enclosing `cfg`s have to resolve, and that resolution is the
`Region.Follow` trampoline. The induction that matches it is on the number of
transfers the RTL run makes, so `Func.Exec` is first refined by that count. -/

/-- Big-step execution with a bound on the number of transfers it makes. The
count is what makes the descent a well-founded recursion: a `cfg`'s `Follow`
loop runs one transfer per step and so consumes it. -/
inductive Func.ExecIn (oracle : CallOracle) (fn : Func R) :
    Nat → Label → Frame R → Memory → Exit → Prop where
  | jump {n : Nat} {l t : Label} {b bt : Block R} {as : List R} {vals : List Word}
      {fr fr₁ fr₂ : Frame R} {m m₁ : Memory} {out : Exit} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .jump t as →
      fr₁.readAll as = some vals → fn.block? t = some bt →
      fr₁.writeAll bt.params vals = some fr₂ → ExecIn oracle fn n t fr₂ m₁ out →
      ExecIn oracle fn (n + 1) l fr m out
  | cond {n : Nat} {l t₁ t₂ : Label} {c : R} {a₁ a₂ : List R} {b bt : Block R} {x : Word}
      {vals : List Word} {fr fr₁ fr₂ : Frame R} {m m₁ : Memory} {out : Exit} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ →
      b.term = .cond c t₁ a₁ t₂ a₂ → fr₁.get c = some x →
      fr₁.readAll (if x = 0 then a₂ else a₁) = some vals →
      fn.block? (if x = 0 then t₂ else t₁) = some bt →
      fr₁.writeAll bt.params vals = some fr₂ →
      ExecIn oracle fn n (if x = 0 then t₂ else t₁) fr₂ m₁ out →
      ExecIn oracle fn (n + 1) l fr m out
  | ret {n : Nat} {l : Label} {b : Block R} {regs : List R} {vals : List Word}
      {fr fr₁ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .ret regs →
      fr₁.readAll regs = some vals → ExecIn oracle fn n l fr m (.returned vals m₁)
  | trap {n : Nat} {l : Label} {b : Block R} {fr fr₁ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .trap →
      ExecIn oracle fn n l fr m (.trapped m₁)

/-- Every big-step run makes finitely many transfers. -/
theorem Func.Exec.toExecIn {oracle : CallOracle} {fn : Func R} {l : Label} {fr : Frame R}
    {m : Memory} {out : Exit} (h : Func.Exec oracle fn l fr m out) :
    ∃ n, Func.ExecIn oracle fn n l fr m out := by
  induction h with
  | jump hb hops hterm hargs hbt hwrite _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .jump hb hops hterm hargs hbt hwrite hn⟩
  | cond hb hops hterm hget hargs hbt hwrite _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .cond hb hops hterm hget hargs hbt hwrite hn⟩
  | ret hb hops hterm hargs => exact ⟨0, .ret hb hops hterm hargs⟩
  | trap hb hops hterm => exact ⟨0, .trap hb hops hterm⟩

/-- A bounded run is a run. -/
theorem Func.ExecIn.toExec {oracle : CallOracle} {fn : Func R} {n : Nat} {l : Label}
    {fr : Frame R} {m : Memory} {out : Exit} (h : Func.ExecIn oracle fn n l fr m out) :
    Func.Exec oracle fn l fr m out := by
  induction h with
  | jump hb hops hterm hargs hbt hwrite _ ih => exact .jump hb hops hterm hargs hbt hwrite ih
  | cond hb hops hterm hget hargs hbt hwrite _ ih =>
    exact .cond hb hops hterm hget hargs hbt hwrite ih
  | ret hb hops hterm hargs => exact .ret hb hops hterm hargs
  | trap hb hops hterm => exact .trap hb hops hterm

/-- The semantic scope invariant: `EnterOk` together with the converse of its
`domDefs` field, which is what single assignment needs in order to see that a
definition is new. -/
structure EnterOkSem (fn : Func R) (sc : Scope R) (l : Label) : Prop where
  /-- The syntactic invariant the typing proof uses. -/
  base : EnterOk fn sc l
  /-- Every register in scope is defined by a strict dominator of `l`. -/
  domOnly : ∀ r, sc.HasReg r → ∃ a, fn.digraph.StrictlyDominates a l ∧ r ∈ fn.defsOf a

/-- What an exit out of a block's region means: the function returned at the
return label, it trapped at the trap label, or it is about to transfer to a
block whose `cfg` lies further out, carrying the frame the transfer writes into
and the rest of the run. -/
def ExitRepr (oracle : CallOracle) (fn : Func R) (out : Exit) (n : Nat) (sc : Scope R)
    (env : Semantics.Env Word) (lbl : Nat) (v : Value Word) (m : Memory) : Prop :=
  (∃ vs, out = .returned vs m ∧ lbl = sc.depth ∧ v = packValues vs) ∨
  (out = .trapped m ∧ lbl = sc.depth + 1 ∧ v = .unit) ∨
  (∃ (t : Label) (bt : Block R) (fr₁ fr₂ : Frame R) (vals : List Word) (k : Nat),
    fn.block? t = some bt ∧ fn.Reachable t ∧
    (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome ∧
    lbl = fn.jumpLabel sc t ∧ v = packValues vals ∧
    fr₁.writeAll bt.params vals = some fr₂ ∧ sc.Agrees env fr₁ ∧
    k < n ∧ Func.ExecIn oracle fn k t fr₂ m out)

/-- Raising the bound on the remaining transfers keeps an exit's meaning. -/
theorem ExitRepr.mono {oracle : CallOracle} {fn : Func R} {out : Exit} {n n' : Nat}
    {sc : Scope R} {env : Semantics.Env Word} {lbl : Nat} {v : Value Word} {m : Memory}
    (hn : n ≤ n') (h : ExitRepr oracle fn out n sc env lbl v m) :
    ExitRepr oracle fn out n' sc env lbl v m := by
  rcases h with h | h | ⟨t, bt, fr₁, fr₂, vals, k, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨t, bt, fr₁, fr₂, vals, k, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      Nat.lt_of_lt_of_le h₈ hn, h₉⟩)

omit [DecidableEq R] in
/-- The tuples in scope at a block's `cfg` are its ops' destinations, then its
parameters, then the tuples the enclosing `cfg` had. -/
theorem blockScope_vals_eq (fn : Func R) (sc : Scope R) (l : Label) (b : Block R) :
    (blockScope fn sc l b).vals = (b.ops.map Op.defs).reverse ++ b.params :: sc.vals := by
  rw [blockScope_vals, Scope.afterOps_vals, Scope.push_vals]

/-- Dropping a prefix of an append. -/
theorem drop_append_length {α : Type} (l₁ l₂ : List α) (i : Nat) :
    (l₁ ++ l₂).drop (l₁.length + i) = l₂.drop i := by
  induction l₁ with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, show as.length + 1 + i = (as.length + i) + 1 by omega,
      List.cons_append, List.drop_succ_cons]
    exact ih

omit [DecidableEq R] in
/-- Dropping a block's own tuples recovers the enclosing `cfg`'s scope. -/
theorem blockScope_vals_drop (fn : Func R) (sc : Scope R) (l : Label) (b : Block R) :
    (blockScope fn sc l b).vals.drop (b.ops.length + 1) = sc.vals := by
  rw [blockScope_vals_eq, show b.ops.length + 1 = (b.ops.map Op.defs).reverse.length + 1 by simp,
    drop_append_length]
  rfl

omit [DecidableEq R] in
/-- A `cfg` other than the block's own keeps the depth it had. -/
theorem labelDepth_blockScope_outer {fn : Func R} {sc : Scope R} {l : Label} {b : Block R}
    {a : Option Label} (hne : a ≠ some l) :
    Scope.labelDepth (blockScope fn sc l b).labels a = Scope.labelDepth sc.labels a := by
  rw [blockScope_labels, Scope.labelDepth]
  split
  · rename_i heq
    exact absurd heq.symm hne
  · rfl

omit [DecidableEq R] in
/-- A block's own `cfg` records its arity over the enclosing depth. -/
theorem labelDepth_blockScope_self {fn : Func R} {sc : Scope R} {l : Label} {b : Block R} :
    Scope.labelDepth (blockScope fn sc l b).labels (some l)
      = some ((fn.domChildren (some l)).length + sc.depth) := by
  rw [blockScope_labels, Scope.labelDepth]
  split
  · rfl
  · rename_i hne
    exact absurd rfl hne

omit [DecidableEq R] in
/-- Transferring to a dominator-tree child of the block names that child inside
the block's own `cfg`. -/
theorem jumpLabel_blockScope_child {fn : Func R} {sc : Scope R} {l : Label} {b : Block R}
    {t : Label} (hid : fn.digraph.idom t = some l) :
    ∃ k, k < (fn.domChildren (some l)).length ∧ (fn.domChildren (some l))[k]? = some t ∧
      fn.jumpLabel (blockScope fn sc l b) t = k := by
  have hmem : t ∈ fn.domChildren (some l) := Graph.Digraph.mem_domTreeChildren_iff.mpr hid
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (idxIn_isSome hmem)
  refine ⟨k, idxIn_lt hk, idxIn_getElem hk, ?_⟩
  simp only [Func.jumpLabel]
  rw [hid, labelDepth_blockScope_self, blockScope_depth, hk]
  simp

omit [DecidableEq R] in
/-- Transferring past the block's own `cfg` adds that `cfg`'s arity to the label
the enclosing scope would use. -/
theorem jumpLabel_blockScope_outer {fn : Func R} {sc : Scope R} {l : Label} {b : Block R}
    {t : Label} (hok : Scope.LabelsOk fn sc.labels) (hne : fn.digraph.idom t ≠ some l)
    (hd : (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome) :
    fn.jumpLabel (blockScope fn sc l b) t
      = (fn.domChildren (some l)).length + fn.jumpLabel sc t := by
  obtain ⟨d, hdd⟩ := Option.isSome_iff_exists.mp hd
  have hd2 : Scope.labelDepth (blockScope fn sc l b).labels (fn.digraph.idom t) = some d := by
    rw [labelDepth_blockScope_outer hne]
    exact hdd
  have hle : d ≤ sc.depth := Scope.labelDepth_le hok hdd
  have hL : fn.jumpLabel sc t
      = (sc.depth - d) + (idxIn (fn.domChildren (fn.digraph.idom t)) t).getD 0 := by
    simp only [Func.jumpLabel]
    rw [hdd]
  have hRv : fn.jumpLabel (blockScope fn sc l b) t
      = ((blockScope fn sc l b).depth - d)
        + (idxIn (fn.domChildren (fn.digraph.idom t)) t).getD 0 := by
    simp only [Func.jumpLabel]
    rw [hd2]
  rw [hL, hRv, blockScope_depth]
  omega

/-- A conditional becomes a `case` on the branch opcode, taking the target the
condition selects. -/
theorem Term.eval_toRegion_cond {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R} (hag : sc.Agrees env fr)
    {c : R} {t₁ t₂ : Label} {a₁ a₂ : List R} {x : Word} (hc : sc.Covers [c])
    (hA : sc.Covers (if x = 0 then a₂ else a₁)) (hget : fr.get c = some x) {vals : List Word}
    (hread : fr.readAll (if x = 0 then a₂ else a₁) = some vals) {m : Memory} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
      (Term.toRegion sigs fn sc (.cond c t₁ a₁ t₂ a₂)) m
      (fn.jumpLabel sc (if x = 0 then t₂ else t₁)) (packValues vals) m := by
  by_cases hx : x = 0
  · subst hx
    have h1 : (if (0 : Word) = 0 then a₂ else a₁) = a₂ := by
      split
      · rfl
      · rename_i h; exact absurd rfl h
    have h2 : (if (0 : Word) = 0 then t₂ else t₁) = t₂ := by
      split
      · rfl
      · rename_i h; exact absurd rfl h
    rw [h1] at hA hread
    rw [h2]
    exact Term.eval_toRegion_cond_zero hag hc hA hget hread
  · have h1 : (if x = 0 then a₂ else a₁) = a₁ := by
      split
      · rename_i h; exact absurd h hx
      · rfl
    have h2 : (if x = 0 then t₂ else t₁) = t₁ := by
      split
      · rename_i h; exact absurd h hx
      · rfl
    rw [h1] at hA hread
    rw [h2]
    exact Term.eval_toRegion_cond_nonzero hag hc hA hx hget hread

omit [DecidableEq R] in
/-- A target of the block's terminator has its `cfg` in scope inside the block's
own `cfg`: either it is a dominator-tree child of the block, or its immediate
dominator is a proper ancestor, which the scope invariant already records. -/
theorem labelDepth_blockScope_target {fn : Func R} {sc : Scope R} {l t : Label} {b : Block R}
    (hok : EnterOk fn sc l) (hedge : fn.Edge l t) :
    (Scope.labelDepth (blockScope fn sc l b).labels (fn.digraph.idom t)).isSome := by
  rw [blockScope_labels]
  cases hid : fn.digraph.idom t with
  | none =>
    rw [Scope.labelDepth]
    split
    · rfl
    · exact hok.root
  | some p =>
    have hdp : fn.digraph.Dominates p l := Graph.Digraph.idom_dominates_of_edge hedge hid
    rw [Scope.labelDepth]
    split
    · rfl
    · rename_i hne
      exact hok.ancestors p ⟨hdp, fun h => hne (by rw [h])⟩

/-- **The scope after a block's ops still agrees with the frame**, and the
`let₁` chain the ops became runs whatever follows it. Freshness of each op's
destinations comes from single assignment: every register already in scope is a
parameter of the block, an earlier op's destination or a definition of a strict
dominator, and none of those can be defined twice. -/
theorem block_ops_eval {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) {sc : Scope R} {l : Label} {b : Block R} (hb : fn.block? l = some b)
    (hok : EnterOkSem fn sc l) {envP env : Semantics.Env Word}
    (hshift : ∀ i, env (i + 1) = envP i) {fr fr₁ : Frame R} {m m₁ : Memory}
    (hag : (sc.push b.params).Agrees env fr) (hops : Ops.Exec oracle b.ops fr m fr₁ m₁) :
    ∃ env₂ : Semantics.Env Word, (blockScope fn sc l b).Agrees env₂ fr₁ ∧
      (∀ i, env₂ (i + (b.ops.length + 1)) = envP i) ∧
      ∀ {k : Region (Opcode sigs)} {label : Nat} {value : Value Word} {m₂ : Memory},
        Semantics.Region.Eval (Opcode.step oracle) env₂ k m₁ label value m₂ →
        Semantics.Region.Eval (Opcode.step oracle) env
          (opsRegion sigs (sc.push b.params) b.ops k) m label value m₂ := by
  have hcov : ∀ i o, b.ops[i]? = some o →
      ((sc.push b.params).afterOps (b.ops.take i)).Covers o.uses := by
    intro i o ho r hr
    exact covers_of_defined hb hok.base.domDefs
      (defined_of_usesDominated hwf.usesDominated hb ho hr)
  have hfresh : ∀ i o, b.ops[i]? = some o →
      ((sc.push b.params).afterOps (b.ops.take i)).Fresh o.defs ∧ o.defs.Nodup := by
    intro i o ho
    refine ⟨?_, op_defs_nodup hwf.singleAssignment hb ho⟩
    intro r hr hhas
    have hdl : r ∈ fn.defsOf l := by
      rw [defsOf_eq hb, Block.defs]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, List.mem_of_getElem? ho, hr⟩)
    obtain ⟨hnp, hno⟩ := op_defs_fresh_in_block hwf.singleAssignment hb ho hr
    rcases Scope.hasReg_afterOps.mp hhas with hin | ⟨o', ho', hr'⟩
    · rcases Scope.hasReg_push.mp hin with hp | hs
      · exact hnp hp
      · obtain ⟨a, hsd, hra⟩ := hok.domOnly r hs
        exact defsOf_disjoint hwf.singleAssignment hsd.2 hra hdl
    · exact hno o' ho' hr'
  obtain ⟨env₂, hag₂, hsh, hrun⟩ :=
    opsRegion_eval_of_exec (sigs := sigs) b.ops hag hcov hfresh hops
  refine ⟨env₂, hag₂, ?_, hrun⟩
  intro i
  rw [show i + (b.ops.length + 1) = (i + 1) + b.ops.length by omega, hsh (i + 1)]
  exact hshift i

/-- Every register the terminator reads is in scope at the block's `cfg`. -/
theorem covers_term_uses {fn : Func R} (hwf : fn.WellFormed) {sc : Scope R} {l : Label}
    {b : Block R} (hb : fn.block? l = some b) (hok : EnterOkSem fn sc l) :
    (blockScope fn sc l b).Covers b.term.uses := by
  intro r hr
  have h := covers_of_defined hb hok.base.domDefs
    (defined_of_usesDominated_term hwf.usesDominated hb hr)
  rwa [List.take_length] at h

omit [DecidableEq R] in
/-- Every register in scope at a block's `cfg` is defined by a dominator of the
block. -/
theorem blockScope_domOnly {fn : Func R} {sc : Scope R} {l : Label} {b : Block R}
    (hb : fn.block? l = some b) (hok : EnterOkSem fn sc l) {r : R}
    (hr : (blockScope fn sc l b).HasReg r) :
    ∃ a, fn.digraph.Dominates a l ∧ r ∈ fn.defsOf a := by
  have hr' : ((sc.push b.params).afterOps b.ops).HasReg r := hr
  rcases Scope.hasReg_afterOps.mp hr' with hin | ⟨o, ho, hro⟩
  · rcases Scope.hasReg_push.mp hin with hp | hs
    · exact ⟨l, Graph.Digraph.Dominates.refl _ _, by
        rw [defsOf_eq hb, Block.defs]; exact List.mem_append_left _ hp⟩
    · obtain ⟨a, hsd, hra⟩ := hok.domOnly r hs
      exact ⟨a, hsd.1, hra⟩
  · exact ⟨l, Graph.Digraph.Dominates.refl _ _, by
      rw [defsOf_eq hb, Block.defs]
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, ho, hro⟩)⟩

omit [DecidableEq R] in
/-- Entering a dominator-tree child keeps the scope invariant. -/
theorem enterOkSem_child {fn : Func R} {sc : Scope R} {l c : Label} {b : Block R}
    (hb : fn.block? l = some b) (hok : EnterOkSem fn sc l)
    (hid : fn.digraph.idom c = some l) : EnterOkSem fn (blockScope fn sc l b) c := by
  have hsd : fn.digraph.StrictlyDominates l c := Graph.Digraph.idom_strictlyDominates hid
  have hreach : fn.Reachable c := Graph.Digraph.reachable_of_idom hid
  refine ⟨⟨?_, ?_, ?_, ?_, hreach⟩, ?_⟩
  · rw [blockScope_labels]
    exact ⟨rfl, hok.base.labelsOk⟩
  · intro a ha
    have hdl : fn.digraph.Dominates a l := Graph.Digraph.dominates_idom hid ha
    rw [blockScope_labels, Scope.labelDepth]
    split
    · rfl
    · rename_i hne
      exact hok.base.ancestors a ⟨hdl, fun h => hne (by rw [h])⟩
  · rw [blockScope_labels, Scope.labelDepth]
    split
    · rfl
    · exact hok.base.root
  · intro a r hsda hra
    have hdl : fn.digraph.Dominates a l := Graph.Digraph.dominates_idom hid hsda
    by_cases hal : a = l
    · subst hal
      rw [defsOf_eq hb, Block.defs] at hra
      rcases List.mem_append.mp hra with hp | hp
      · exact Scope.hasReg_afterOps.mpr (Or.inl (Scope.hasReg_push.mpr (Or.inl hp)))
      · obtain ⟨o, ho, hro⟩ := List.mem_flatMap.mp hp
        exact Scope.hasReg_afterOps.mpr (Or.inr ⟨o, ho, hro⟩)
    · exact Scope.hasReg_afterOps.mpr
        (Or.inl (Scope.hasReg_push.mpr (Or.inr (hok.base.domDefs a r ⟨hdl, hal⟩ hra))))
  · intro r hr
    obtain ⟨a, hda, hra⟩ := blockScope_domOnly hb hok hr
    refine ⟨a, ⟨hda.trans hsd.1, ?_⟩, hra⟩
    intro hac
    subst hac
    exact hsd.2 (Graph.Digraph.Dominates.antisymm hreach hsd.1 hda)

/-- **A bounded run is its block's ops and then its terminator.** The transfer
case also records that the terminator's region evaluates to the label of the
target with the packed arguments, which spares the descent a second case
analysis on the terminator. -/
theorem Func.ExecIn.inv {oracle : CallOracle} {fn : Func R} {n : Nat} {l : Label}
    {fr : Frame R} {m : Memory} {out : Exit} (h : Func.ExecIn oracle fn n l fr m out) :
    ∃ (b : Block R) (fr₁ : Frame R) (m₁ : Memory),
      fn.block? l = some b ∧ Ops.Exec oracle b.ops fr m fr₁ m₁ ∧
      ((∃ regs vals, b.term = .ret regs ∧ fr₁.readAll regs = some vals ∧
          out = .returned vals m₁) ∨
       (b.term = .trap ∧ out = .trapped m₁) ∨
       (∃ (t : Label) (bt : Block R) (vals : List Word) (fr₂ : Frame R) (n' : Nat),
          t ∈ b.term.successors ∧ fn.block? t = some bt ∧
          fr₁.writeAll bt.params vals = some fr₂ ∧ n' < n ∧
          Func.ExecIn oracle fn n' t fr₂ m₁ out ∧
          ∀ (sigs : List Signature) (sc : Scope R) (env : Semantics.Env Word),
            sc.Agrees env fr₁ → sc.Covers b.term.uses →
            Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
              (Term.toRegion sigs fn sc b.term) m₁ (fn.jumpLabel sc t)
              (packValues vals) m₁)) := by
  cases h with
  | jump hb hops hterm hargs hbt hwrite hrest =>
    refine ⟨_, _, _, hb, hops, Or.inr (Or.inr ⟨_, _, _, _, _, ?_, hbt, hwrite,
      Nat.lt_succ_self _, hrest, ?_⟩)⟩
    · rw [hterm]
      simp [Term.successors]
    · intro sigs sc env hag hcov
      rw [hterm] at hcov ⊢
      exact Term.eval_toRegion_jump hag hcov hargs
  | cond hb hops hterm hget hargs hbt hwrite hrest =>
    refine ⟨_, _, _, hb, hops, Or.inr (Or.inr ⟨_, _, _, _, _, ?_, hbt, hwrite,
      Nat.lt_succ_self _, hrest, ?_⟩)⟩
    · rw [hterm]
      simp only [Term.successors]
      split <;> simp
    · intro sigs sc env hag hcov
      rw [hterm] at hcov ⊢
      refine Term.eval_toRegion_cond hag (hcov.mono ?_) (hcov.mono ?_) hget hargs
      · intro y hy
        rw [List.mem_singleton] at hy
        subst hy
        simp [Term.uses]
      · intro y hy
        simp only [Term.uses]
        split at hy <;> simp [hy]
  | ret hb hops hterm hargs => exact ⟨_, _, _, hb, hops, Or.inl ⟨_, _, hterm, hargs, rfl⟩⟩
  | trap hb hops hterm => exact ⟨_, _, _, hb, hops, Or.inr (Or.inl ⟨hterm, rfl⟩)⟩

/-- The statement of the descent at a block, parameterised by a bound on the
transfers still to come, so that it can be proved by induction on that bound. -/
def EntersAs (sigs : List Signature) (oracle : CallOracle) (fn : Func R) (n : Nat) : Prop :=
  ∀ (fuel : Nat) (sc : Scope R) (l : Label) (b : Block R) (envP env : Semantics.Env Word)
    (fr : Frame R) (m : Memory) (out : Exit),
    fn.block? l = some b → EnterOkSem fn sc l →
    fn.blocks.length - fn.digraph.domDepth l ≤ fuel →
    (∀ i, env (i + 1) = envP i) → (sc.push b.params).Agrees env fr →
    Func.ExecIn oracle fn n l fr m out →
    ∃ lbl v m', Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
        (blockRegion sigs fuel fn sc l) m lbl v m' ∧
      ExitRepr oracle fn out n sc envP lbl v m'

/-- The statement of the `cfg` trampoline at a block: it resolves an exit out of
one of the block's dominator-tree children into an exit out of the block. -/
def FollowsAs (sigs : List Signature) (oracle : CallOracle) (fn : Func R) (n : Nat) : Prop :=
  ∀ (fuel : Nat) (sc : Scope R) (l : Label) (b : Block R) (envP env₂ : Semantics.Env Word)
    (out : Exit) (lbl : Nat) (v : Value Word) (m : Memory),
    fn.block? l = some b → EnterOkSem fn sc l →
    fn.blocks.length - fn.digraph.domDepth l ≤ fuel + 1 →
    (∀ i, env₂ (i + (b.ops.length + 1)) = envP i) →
    ExitRepr oracle fn out n (blockScope fn sc l b) env₂ lbl v m →
    ∃ lbl' v' m', Semantics.Region.Follow (Opcode.step (sigs := sigs) oracle) env₂
        (fun i : Fin (fn.domChildren (some l)).length =>
          blockRegion sigs fuel fn (blockScope fn sc l b)
            ((fn.domChildren (some l))[i.val]'i.isLt)) lbl v m lbl' v' m' ∧
      ExitRepr oracle fn out n sc envP lbl' v' m'

/-- **The `cfg` of a block's dominator-tree children is the block-to-block
loop.** An exit that names the return label, the trap label or a `cfg` further
out leaves the loop, and an exit that names a child runs that child and goes
round again; the bound on the remaining transfers strictly decreases each time
round, which is what makes this an induction. -/
theorem followsAs_of_enters {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) :
    ∀ n : Nat, (∀ k, k < n → EntersAs sigs oracle fn k) → FollowsAs sigs oracle fn n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro henter fuel sc l b envP env₂ out lbl v m hb hok hfuel hshift hrep
    rcases hrep with ⟨vs, hout, hlbl, hv⟩ | ⟨hout, hlbl, hv⟩ |
      ⟨t, bt, fr₁, fr₂, vals, k, hbt, hreach, hdsome, hlbl, hv, hwrite, hag, hk, hexec⟩
    · subst hlbl
      subst hv
      have hge : (fn.domChildren (some l)).length ≤ (blockScope fn sc l b).depth := by
        rw [blockScope_depth]
        omega
      refine ⟨_, _, _, Semantics.Region.Follow.exit hge, Or.inl ⟨vs, hout, ?_, rfl⟩⟩
      rw [blockScope_depth]
      omega
    · subst hlbl
      subst hv
      have hge : (fn.domChildren (some l)).length ≤ (blockScope fn sc l b).depth + 1 := by
        rw [blockScope_depth]
        omega
      refine ⟨_, _, _, Semantics.Region.Follow.exit hge, Or.inr (Or.inl ⟨hout, ?_, rfl⟩)⟩
      rw [blockScope_depth]
      omega
    · by_cases hid : fn.digraph.idom t = some l
      · obtain ⟨j, hjlt, hjget, hjeq⟩ := jumpLabel_blockScope_child (sc := sc) (b := b) hid
        have hlblj : j = lbl := (hlbl.trans hjeq).symm
        subst hlblj
        subst hv
        have hjt : (fn.domChildren (some l))[j]'hjlt = t :=
          Option.some.inj ((List.getElem?_eq_getElem hjlt).symm.trans hjget)
        have hsd : fn.digraph.StrictlyDominates l t := Graph.Digraph.idom_strictlyDominates hid
        have hnotin : ∀ r, (blockScope fn sc l b).HasReg r → r ∉ bt.params := by
          intro r hr hp
          obtain ⟨a, hda, hra⟩ := blockScope_domOnly hb hok hr
          have hat : a ≠ t := by
            intro hat
            subst hat
            exact hsd.2 (Graph.Digraph.Dominates.antisymm hreach hsd.1 hda)
          refine defsOf_disjoint hwf.singleAssignment hat hra ?_
          rw [defsOf_eq hbt, Block.defs]
          exact List.mem_append_left _ hp
        have hagc : ((blockScope fn sc l b).push bt.params).Agrees
            (Semantics.extend env₂ (packValues vals)) fr₂ :=
          (hag.frame (fun r hr => get_writeAll_of_not_mem hwrite (hnotin r hr))).push
            (readAll_writeAll hwrite (params_nodup hwf.singleAssignment hbt))
        have hfuelc : fn.blocks.length - fn.digraph.domDepth t ≤ fuel := by
          have := Graph.Digraph.domDepth_lt_of_idom hid
          omega
        obtain ⟨next, middle, m₁, heval, hrep'⟩ :=
          henter k hk fuel (blockScope fn sc l b) t bt env₂
            (Semantics.extend env₂ (packValues vals)) fr₂ m out hbt
            (enterOkSem_child hb hok hid) hfuelc (fun _ => rfl) hagc hexec
        obtain ⟨lbl', v', m', hfollow, hrep''⟩ :=
          ih k hk (fun k' hk' => henter k' (Nat.lt_trans hk' hk))
            fuel sc l b envP env₂ out next middle m₁ hb hok hfuel hshift hrep'
        refine ⟨lbl', v', m', Semantics.Region.Follow.step hjlt ?_ hfollow,
          hrep''.mono (Nat.le_of_lt hk)⟩
        show Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle)
          (Semantics.extend env₂ (packValues vals))
          (blockRegion sigs fuel fn (blockScope fn sc l b)
            ((fn.domChildren (some l))[j]'hjlt)) m next middle m₁
        rw [hjt]
        exact heval
      · have hdsome' : (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome := by
          rwa [labelDepth_blockScope_outer hid] at hdsome
        have hjeq := jumpLabel_blockScope_outer (sc := sc) (b := b) hok.base.labelsOk hid hdsome'
        have hge : (fn.domChildren (some l)).length ≤ lbl := by
          rw [hlbl, hjeq]
          omega
        refine ⟨lbl - (fn.domChildren (some l)).length, v, m,
          Semantics.Region.Follow.exit hge, Or.inr (Or.inr ⟨t, bt, fr₁, fr₂, vals, k,
            hbt, hreach, hdsome', ?_, hv, hwrite, ?_, hk, hexec⟩)⟩
        · rw [hlbl, hjeq]
          omega
        · exact hag.drop (blockScope_vals_drop fn sc l b).symm (fun i => (hshift i).symm)

/-- **Every bounded run of a block is a run of its region.** The straight-line
code is the `let₁` chain, the terminator is the `cfg`'s entry, and the `cfg`'s
`Follow` resolves whatever the terminator transfers to. -/
theorem entersAs {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) : ∀ n : Nat, EntersAs sigs oracle fn n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fuel sc l b envP env fr m out hb hok hfuel hshift hag hex
    cases fuel with
    | zero =>
      exact absurd hfuel (by have := domDepth_lt hwf.sig hok.base.reachable; omega)
    | succ fuel =>
      obtain ⟨b', fr₁, m₁, hb', hops, hrest⟩ := hex.inv
      obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
      rw [blockRegion_succ hb]
      obtain ⟨env₂, hag₂, hsh₂, hrun⟩ := block_ops_eval (sigs := sigs) hwf hb hok hshift hag hops
      have hcovterm := covers_term_uses hwf hb hok
      obtain ⟨lbl₀, v₀, m₂, hentry, hrep₀⟩ :
          ∃ lbl₀ v₀ m₂, Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env₂
              (Term.toRegion sigs fn (blockScope fn sc l b) b.term) m₁ lbl₀ v₀ m₂ ∧
            ExitRepr oracle fn out n (blockScope fn sc l b) env₂ lbl₀ v₀ m₂ := by
        rcases hrest with ⟨regs, vals, hterm, hargs, rfl⟩ | ⟨hterm, rfl⟩ |
          ⟨t, bt, vals, fr₂, n', hsucc, hbt, hwrite, hn', hexec, heval⟩
        · rw [hterm] at hcovterm
          exact ⟨(blockScope fn sc l b).depth, packValues vals, m₁,
            by rw [hterm]; exact Term.eval_toRegion_ret hag₂ hcovterm hargs,
            Or.inl ⟨vals, rfl, rfl, rfl⟩⟩
        · exact ⟨(blockScope fn sc l b).depth + 1, .unit, m₁,
            by rw [hterm]; exact Term.eval_toRegion_trap, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
        · have hlt := lt_of_mem_successors hwf.sig hb hsucc
          have hedge : fn.Edge l t := Func.edge_of_term hb hsucc hlt
          exact ⟨fn.jumpLabel (blockScope fn sc l b) t, packValues vals, m₁,
            heval sigs (blockScope fn sc l b) env₂ hag₂ hcovterm,
            Or.inr (Or.inr ⟨t, bt, fr₁, fr₂, vals, n', hbt, hok.base.reachable.step hedge,
              labelDepth_blockScope_target hok.base hedge, rfl, rfl, hwrite, hag₂,
              hn', hexec⟩)⟩
      obtain ⟨lbl', v', m', hf, hrep⟩ :=
        followsAs_of_enters hwf n ih fuel sc l b envP env₂ out lbl₀ v₀ m₂ hb hok hfuel hsh₂ hrep₀
      exact ⟨lbl', v', m', hrun (.cfg hentry hf), hrep⟩

/-! ### The outermost `cfg` -/

/-- What an exit out of the whole translated region means: external label `0`
carries the packed returned values and external label `1` carries `unit`. -/
def RootExit (out : Exit) (lbl : Nat) (v : Value Word) (m : Memory) : Prop :=
  (∃ vs, out = .returned vs m ∧ lbl = 0 ∧ v = packValues vs) ∨
  (out = .trapped m ∧ lbl = 1 ∧ v = .unit)

omit [DecidableEq R] in
/-- The root scope binds no tuple, so it agrees with every environment and
frame. -/
theorem agrees_root {env : Semantics.Env Word} {fr : Frame R} :
    (⟨[], [(none, 1)]⟩ : Scope R).Agrees env fr := by
  intro i g hi
  rw [show (⟨[], [(none, 1)]⟩ : Scope R).vals = [] from rfl] at hi
  simp at hi

omit [DecidableEq R] in
/-- The artificial root above the entry block is a correct scope for entering
it: it binds nothing and records only its own `cfg`. -/
theorem enterOkSem_root {fn : Func R} :
    EnterOkSem fn ⟨[], [(none, 1)]⟩ fn.entry := by
  refine ⟨⟨⟨by simp [Func.domChildren], trivial⟩, ?_, by simp [Scope.labelDepth], ?_,
    Graph.Digraph.reachable_entry _⟩, ?_⟩
  · intro a hsd
    exact absurd (Graph.Digraph.Dominates.eq_entry hsd.1) hsd.2
  · intro a r hsd _
    exact absurd (Graph.Digraph.Dominates.eq_entry hsd.1) hsd.2
  · intro r hr
    exact absurd hr (by simp [Scope.HasReg])

/-- **The outermost `cfg` resolves every exit.** Its only block is the entry
block, so the one transfer it can take is a back edge to the entry; everything
else leaves at the return or the trap label. -/
theorem followsAsRoot {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) :
    ∀ (n : Nat) (env : Semantics.Env Word) (out : Exit) (lbl : Nat) (v : Value Word)
      (m : Memory),
      ExitRepr oracle fn out n ⟨[], [(none, 1)]⟩ env lbl v m →
      ∃ lbl' v' m', Semantics.Region.Follow (Opcode.step (sigs := sigs) oracle) env
          (fun _ : Fin 1 => blockRegion sigs fn.blocks.length fn ⟨[], [(none, 1)]⟩ fn.entry)
          lbl v m lbl' v' m' ∧ RootExit out lbl' v' m' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro env out lbl v m hrep
    rcases hrep with ⟨vs, hout, hlbl, hv⟩ | ⟨hout, hlbl, hv⟩ |
      ⟨t, bt, fr₁, fr₂, vals, k, hbt, hreach, hdsome, hlbl, hv, hwrite, hag, hk, hexec⟩
    · subst hlbl
      subst hv
      exact ⟨_, _, _, Semantics.Region.Follow.exit (Nat.le_refl 1), Or.inl ⟨vs, hout, rfl, rfl⟩⟩
    · subst hlbl
      subst hv
      exact ⟨_, _, _, Semantics.Region.Follow.exit (Nat.le_add_left 1 _),
        Or.inr ⟨hout, rfl, rfl⟩⟩
    · have hid : fn.digraph.idom t = none := by
        cases hidt : fn.digraph.idom t with
        | none => rfl
        | some a =>
          rw [hidt] at hdsome
          simp [Scope.labelDepth] at hdsome
      have ht : t = fn.entry := by
        by_contra hne
        obtain ⟨a, ha, -, -⟩ := Graph.Digraph.idom_spec hreach hne
        rw [hid] at ha
        exact absurd ha (by simp)
      subst ht
      have hlbl0 : lbl = 0 := by
        rw [hlbl]
        simp [Func.jumpLabel, hid, Scope.labelDepth, Scope.depth, Func.domChildren, idxIn]
      subst hlbl0
      subst hv
      have hagc : ((⟨[], [(none, 1)]⟩ : Scope R).push bt.params).Agrees
          (Semantics.extend env (packValues vals)) fr₂ :=
        agrees_root.push (readAll_writeAll hwrite (params_nodup hwf.singleAssignment hbt))
      obtain ⟨next, middle, m₁, heval, hrep'⟩ :=
        entersAs (sigs := sigs) hwf k fn.blocks.length ⟨[], [(none, 1)]⟩ fn.entry bt env
          (Semantics.extend env (packValues vals)) fr₂ m out hbt enterOkSem_root (by omega)
          (fun _ => rfl) hagc hexec
      obtain ⟨lbl', v', m', hfollow, hroot⟩ := ih k hk env out next middle m₁ hrep'
      exact ⟨lbl', v', m', Semantics.Region.Follow.step (by omega) heval hfollow, hroot⟩

/-- **A run of the function is a run of its region.** The outermost `cfg` hands
the entry block the function's packed argument, and the run leaves at external
label `0` with the packed results or at external label `1` with `unit`. -/
theorem toLambdaSSA_eval_of_exec {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) {args : List Word} {b : Block R} {fr : Frame R}
    (hb : fn.block? fn.entry = some b) (hfr : Frame.empty.writeAll b.params args = some fr)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m : Memory} {out : Exit}
    (hexec : Func.Exec oracle fn fn.entry fr m out) :
    ∃ lbl v m', Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
        (toLambdaSSA sigs fn) m lbl v m' ∧ RootExit out lbl v m' := by
  obtain ⟨n, hn⟩ := hexec.toExecIn
  have hagc : ((⟨[], [(none, 1)]⟩ : Scope R).push b.params).Agrees
      (Semantics.extend env (packValues args)) fr :=
    agrees_root.push (readAll_writeAll hfr (params_nodup hwf.singleAssignment hb))
  obtain ⟨next, middle, m₁, heval, hrep⟩ :=
    entersAs (sigs := sigs) hwf n fn.blocks.length ⟨[], [(none, 1)]⟩ fn.entry b env
      (Semantics.extend env (packValues args)) fr m out hb enterOkSem_root (by omega)
      (fun _ => rfl) hagc hn
  obtain ⟨lbl', v', m', hfollow, hroot⟩ := followsAsRoot hwf n env out next middle m₁ hrep
  refine ⟨lbl', v', m', .cfg (.br (.var_of_eq rfl)) ?_, hroot⟩
  refine Semantics.Region.Follow.step (by omega) ?_ hfollow
  rw [henv]
  exact heval

/-! ### Reflecting evaluation

The reverse direction needs each of the forward lemmas read backwards. Only the
call case asks for anything new: an abstract oracle may return any number of
words, while RTL writes a fixed list of result registers, so the oracle is
required to respect the signature table. -/

/-- Renaming the free variables of a term along a map the two environments agree
over reflects evaluation. -/
theorem eval_of_rename {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop} :
    ∀ (a : Tm Φ) {env env' : Semantics.Env Word} {ρ : Nat → Nat},
      (∀ i, env' (ρ i) = env i) → ∀ {s s' : σ} {v : Value Word},
        Semantics.Tm.Eval instr env' (a.rename ρ) s v s' →
        Semantics.Tm.Eval instr env a s v s' := by
  intro a
  induction a with
  | var i =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    obtain ⟨hv, rfl⟩ := eval_var_inv h
    exact Semantics.Tm.Eval.var_of_eq ((hρ i).symm.trans hv.symm)
  | op f x ih =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    obtain ⟨va, s₁, h₁, h₂⟩ := eval_op_inv h
    exact .op (ih hρ h₁) h₂
  | let₁ x y ihx ihy =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    cases h with
    | let₁ h₁ h₂ => exact .let₁ (ihx hρ h₁) (ihy (Semantics.extend_rename hρ _) h₂)
  | pair x y ihx ihy =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    obtain ⟨va, vb, s₁, h₁, h₂, rfl⟩ := eval_pair_inv h
    exact .pair (ihx hρ h₁) (ihy hρ h₂)
  | unit =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    obtain ⟨rfl, rfl⟩ := eval_unit_inv h
    exact .unit
  | let₂ x y ihx ihy =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    obtain ⟨va, vb, s₁, h₁, h₂⟩ := eval_let₂_inv h
    exact .let₂ (ihx hρ h₁)
      (ihy (Semantics.extend_rename (Semantics.extend_rename hρ _) _) h₂)
  | inl x ih =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    cases h with
    | inl h₁ => exact .inl (ih hρ h₁)
  | inr x ih =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    cases h with
    | inr h₁ => exact .inr (ih hρ h₁)
  | case x y z ihx ihy ihz =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    cases h with
    | case_inl h₁ h₂ => exact .case_inl (ihx hρ h₁) (ihy (Semantics.extend_rename hρ _) h₂)
    | case_inr h₁ h₂ => exact .case_inr (ihx hρ h₁) (ihz (Semantics.extend_rename hρ _) h₂)
  | abort x _ =>
    intro env env' ρ hρ s s' v h
    simp only [Tm.rename] at h
    cases h

/-- A call oracle agrees with the signature table when every transition it
allows produces the number of result words the table declares. RTL writes a
fixed list of result registers, so without this an abstract oracle could return
a tuple of the wrong width and the region would take a step the machine
cannot. -/
def CallOracle.MatchesSigs (oracle : CallOracle) (sigs : List Signature) : Prop :=
  ∀ f args m vs m', oracle f args m vs m' → vs.length = (sigAt sigs f).results

/-- **An op's term evaluates only when the op executes**, to the packed tuple of
the words the op writes. -/
theorem Op.exec_of_eval_toTm {sigs : List Signature} {oracle : CallOracle}
    (hsigs : CallOracle.MatchesSigs oracle sigs) {sc : Scope R}
    {env : Semantics.Env Word} {fr : Frame R}
    (hag : sc.Agrees env fr) {o : Op R} (hcov : sc.Covers o.uses)
    (hcall : ∀ f args results, o = .call f args results →
      results.length = (sigAt sigs f).results)
    {m m' : Memory} {v : Value Word}
    (h : Semantics.Tm.Eval (Opcode.step (sigs := sigs) oracle) env (Op.toTm sigs sc o) m v m') :
    ∃ ws fr', v = packValues ws ∧ fr.writeAll o.defs ws = some fr' ∧
      Ops.Exec oracle [o] fr m fr' m' := by
  cases o with
  | const d val =>
    obtain ⟨va, m₁, h₁, hstep⟩ := eval_op_inv h
    obtain ⟨rfl, rfl⟩ := eval_unit_inv h₁
    cases hstep
    exact ⟨[val], fr.set d val, rfl, rfl, .op rfl .nil⟩
  | move d s =>
    obtain ⟨x, hx⟩ := hag.get_isSome (hcov s (by simp [Op.uses]))
    obtain ⟨va, m₁, h₁, hstep⟩ := eval_op_inv h
    obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag hcov (readAll_singleton hx)).mp h₁
    cases hstep
    refine ⟨[x], fr.set d x, rfl, rfl, .op ?_ .nil⟩
    simp [Op.exec, hx]
  | unary op d s =>
    obtain ⟨x, hx⟩ := hag.get_isSome (hcov s (by simp [Op.uses]))
    obtain ⟨va, m₁, h₁, hstep⟩ := eval_op_inv h
    obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag hcov (readAll_singleton hx)).mp h₁
    cases hstep
    refine ⟨[op.eval x], fr.set d (op.eval x), rfl, rfl, .op ?_ .nil⟩
    simp [Op.exec, hx]
  | binary op d a c =>
    obtain ⟨x, hx⟩ := hag.get_isSome (hcov a (by simp [Op.uses]))
    obtain ⟨y, hy⟩ := hag.get_isSome (hcov c (by simp [Op.uses]))
    obtain ⟨va, m₁, h₁, hstep⟩ := eval_op_inv h
    obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag hcov (readAll_pair hx hy)).mp h₁
    cases hstep with
    | binary hz =>
      refine ⟨_, _, rfl, rfl, .op ?_ .nil⟩
      simp [Op.exec, hx, hy, hz]
  | load w e d base off =>
    obtain ⟨x, hx⟩ := hag.get_isSome (hcov base (by simp [Op.uses]))
    obtain ⟨va, m₁, h₁, hstep⟩ := eval_op_inv h
    obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag hcov (readAll_singleton hx)).mp h₁
    cases hstep with
    | load hz =>
      refine ⟨_, _, rfl, rfl, .op ?_ .nil⟩
      simp [Op.exec, hx, hz]
  | store w base off src =>
    obtain ⟨x, hx⟩ := hag.get_isSome (hcov base (by simp [Op.uses]))
    obtain ⟨y, hy⟩ := hag.get_isSome (hcov src (by simp [Op.uses]))
    obtain ⟨va, m₁, h₁, hstep⟩ := eval_op_inv h
    obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag hcov (readAll_pair hx hy)).mp h₁
    cases hstep with
    | store hm =>
      refine ⟨[], fr, rfl, rfl, .op ?_ .nil⟩
      simp [Op.exec, hx, hy, hm]
  | call f args results =>
    obtain ⟨vals, hvals⟩ := hag.readAll hcov
    obtain ⟨va, m₁, h₁, hstep⟩ := eval_op_inv h
    obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag hcov hvals).mp h₁
    obtain ⟨args', res', heq, rfl, horacle⟩ := Opcode.step_call_iff.mp hstep
    obtain rfl : vals = args' := packValues_injective heq
    have hlen : results.length = res'.length := by
      rw [hcall f args results rfl, hsigs f vals _ res' _ horacle]
    obtain ⟨fr', hfr'⟩ := writeAll_isSome fr (rs := results) (ws := res') hlen
    exact ⟨res', fr', rfl, hfr', .call hvals horacle hfr' .nil⟩

/-- **The `let₁` chain runs only when the block's ops do.** -/
theorem opsRegion_exec_of_eval {sigs : List Signature} {oracle : CallOracle}
    (hsigs : CallOracle.MatchesSigs oracle sigs) :
    ∀ (ops : List (Op R)) {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R}
      {m : Memory} {k : Region (Opcode sigs)} {lbl : Nat} {v : Value Word} {m' : Memory},
      sc.Agrees env fr →
      (∀ i o, ops[i]? = some o → (sc.afterOps (ops.take i)).Covers o.uses) →
      (∀ i o, ops[i]? = some o → (sc.afterOps (ops.take i)).Fresh o.defs ∧ o.defs.Nodup) →
      (∀ (i : Nat) (o : Op R), ops[i]? = some o → ∀ (f : FuncId) (args results : List R),
        o = Op.call f args results → results.length = (sigAt sigs f).results) →
      Semantics.Region.Eval (Opcode.step oracle) env (opsRegion sigs sc ops k) m lbl v m' →
      ∃ (fr₁ : Frame R) (m₁ : Memory) (env₂ : Semantics.Env Word),
        Ops.Exec oracle ops fr m fr₁ m₁ ∧ (sc.afterOps ops).Agrees env₂ fr₁ ∧
        (∀ i, env₂ (i + ops.length) = env i) ∧
        Semantics.Region.Eval (Opcode.step oracle) env₂ k m₁ lbl v m' := by
  intro ops
  induction ops with
  | nil =>
    intro sc env fr m k lbl v m' hag _ _ _ h
    exact ⟨fr, m, env, .nil, hag, fun _ => rfl, h⟩
  | cons o os ih =>
    intro sc env fr m k lbl v m' hag hcov hfresh hcalls h
    obtain ⟨va, m₁, h₁, h₂⟩ := region_eval_let₁_inv h
    obtain ⟨hfr, hnd⟩ := hfresh 0 o rfl
    obtain ⟨ws, fr', rfl, hw, hone⟩ :=
      Op.exec_of_eval_toTm hsigs hag (hcov 0 o rfl) (hcalls 0 o rfl) h₁
    have hsame : ∀ r, sc.HasReg r → fr'.get r = fr.get r := fun r hr =>
      get_writeAll_of_not_mem hw (fun hx => hfr r hx hr)
    have hag' : (sc.push o.defs).Agrees (Semantics.extend env (packValues ws)) fr' :=
      (hag.frame hsame).push (readAll_writeAll hw hnd)
    obtain ⟨fr₁, m₂, env₂, hexec, hag₂, hsh, hk⟩ :=
      ih hag' (fun i o' ho' => hcov (i + 1) o' (by simpa using ho'))
        (fun i o' ho' => hfresh (i + 1) o' (by simpa using ho'))
        (fun i o' ho' => hcalls (i + 1) o' (by simpa using ho')) h₂
    refine ⟨fr₁, m₂, env₂, hone.append hexec, hag₂, ?_, hk⟩
    intro i
    have hsh' := hsh (i + 1)
    rw [List.length_cons, show i + (os.length + 1) = i + 1 + os.length by omega]
    simpa using hsh'

/-- Every register an op of a block reads is in scope where the op runs. -/
theorem block_ops_covers {fn : Func R} (hwf : fn.WellFormed) {sc : Scope R} {l : Label}
    {b : Block R} (hb : fn.block? l = some b) (hok : EnterOkSem fn sc l) :
    ∀ (i : Nat) (o : Op R), b.ops[i]? = some o →
      ((sc.push b.params).afterOps (b.ops.take i)).Covers o.uses := by
  intro i o ho r hr
  exact covers_of_defined hb hok.base.domDefs (defined_of_usesDominated hwf.usesDominated hb ho hr)

/-- Every register an op of a block writes is new where the op runs. -/
theorem block_ops_fresh {fn : Func R} (hwf : fn.WellFormed) {sc : Scope R} {l : Label}
    {b : Block R} (hb : fn.block? l = some b) (hok : EnterOkSem fn sc l) :
    ∀ (i : Nat) (o : Op R), b.ops[i]? = some o →
      ((sc.push b.params).afterOps (b.ops.take i)).Fresh o.defs ∧ o.defs.Nodup := by
  intro i o ho
  refine ⟨?_, op_defs_nodup hwf.singleAssignment hb ho⟩
  intro r hr hhas
  have hdl : r ∈ fn.defsOf l := by
    rw [defsOf_eq hb, Block.defs]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨o, List.mem_of_getElem? ho, hr⟩)
  obtain ⟨hnp, hno⟩ := op_defs_fresh_in_block hwf.singleAssignment hb ho hr
  rcases Scope.hasReg_afterOps.mp hhas with hin | ⟨o', ho', hr'⟩
  · rcases Scope.hasReg_push.mp hin with hp | hs
    · exact hnp hp
    · obtain ⟨a, hsd, hra⟩ := hok.domOnly r hs
      exact defsOf_disjoint hwf.singleAssignment hsd.2 hra hdl
  · exact hno o' ho' hr'

omit [DecidableEq R] in
/-- Every call of a block names its callee's declared number of results. -/
theorem block_ops_calls {sigs : List Signature} {fn : Func R} (h : fn.CallsMatch sigs)
    {l : Label} {b : Block R} (hb : fn.block? l = some b) :
    ∀ (i : Nat) (o : Op R), b.ops[i]? = some o → ∀ (f : FuncId) (args results : List R),
      o = Op.call f args results → results.length = (sigAt sigs f).results :=
  fun _ o ho f args results heq =>
    (opsCallsMatch_of_callsMatch h hb o (List.mem_of_getElem? ho) f args results heq).2

/-- One block of an RTL run: its straight-line code and the transfer its
terminator makes. These are the two transfer constructors of `Func.Exec` and of
`Func.DivStep` factored out, so that the reflected descent can hand back a chain
of transfers and let its callers build either judgment from it. -/
inductive Transfers (oracle : CallOracle) (fn : Func R) : DivConfig R → DivConfig R → Prop where
  | jump {l t : Label} {b bt : Block R} {as : List R} {vals : List Word}
      {fr fr₁ fr₂ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .jump t as →
      fr₁.readAll as = some vals → fn.block? t = some bt →
      fr₁.writeAll bt.params vals = some fr₂ → Transfers oracle fn ⟨l, fr, m⟩ ⟨t, fr₂, m₁⟩
  | cond {l t₁ t₂ : Label} {c : R} {a₁ a₂ : List R} {b bt : Block R} {x : Word}
      {vals : List Word} {fr fr₁ fr₂ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ →
      b.term = .cond c t₁ a₁ t₂ a₂ → fr₁.get c = some x →
      fr₁.readAll (if x = 0 then a₂ else a₁) = some vals →
      fn.block? (if x = 0 then t₂ else t₁) = some bt →
      fr₁.writeAll bt.params vals = some fr₂ →
      Transfers oracle fn ⟨l, fr, m⟩ ⟨if x = 0 then t₂ else t₁, fr₂, m₁⟩

/-- The last block of an RTL run: its straight-line code and the exit its
terminator reaches. -/
inductive Finishes (oracle : CallOracle) (fn : Func R) : DivConfig R → Exit → Prop where
  | ret {l : Label} {b : Block R} {regs : List R} {vals : List Word} {fr fr₁ : Frame R}
      {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .ret regs →
      fr₁.readAll regs = some vals → Finishes oracle fn ⟨l, fr, m⟩ (.returned vals m₁)
  | trap {l : Label} {b : Block R} {fr fr₁ : Frame R} {m m₁ : Memory} :
      fn.block? l = some b → Ops.Exec oracle b.ops fr m fr₁ m₁ → b.term = .trap →
      Finishes oracle fn ⟨l, fr, m⟩ (.trapped m₁)

/-- A transfer prefixes a run. -/
theorem Transfers.exec {oracle : CallOracle} {fn : Func R} {c d : DivConfig R}
    (h : Transfers oracle fn c d) {out : Exit}
    (hout : Func.Exec oracle fn d.label d.frame d.mem out) :
    Func.Exec oracle fn c.label c.frame c.mem out := by
  cases h with
  | jump hb hops hterm hargs hbt hwrite => exact .jump hb hops hterm hargs hbt hwrite hout
  | cond hb hops hterm hget hargs hbt hwrite =>
    exact .cond hb hops hterm hget hargs hbt hwrite hout

/-- A chain of transfers prefixes a run. -/
theorem Transfers.exec_of_reflTransGen {oracle : CallOracle} {fn : Func R} {c d : DivConfig R}
    (h : Relation.ReflTransGen (Transfers oracle fn) c d) : ∀ {out : Exit},
      Func.Exec oracle fn d.label d.frame d.mem out →
      Func.Exec oracle fn c.label c.frame c.mem out := by
  induction h with
  | refl => exact fun hout => hout
  | tail _ hstep ih => exact fun hout => ih (hstep.exec hout)

/-- A finishing block is a run. -/
theorem Finishes.exec {oracle : CallOracle} {fn : Func R} {c : DivConfig R} {out : Exit}
    (h : Finishes oracle fn c out) : Func.Exec oracle fn c.label c.frame c.mem out := by
  cases h with
  | ret hb hops hterm hargs => exact .ret hb hops hterm hargs
  | trap hb hops hterm => exact .trap hb hops hterm

/-- A transfer unfolds one step of divergence. -/
theorem Transfers.divStep {oracle : CallOracle} {div : DivOracle} {fn : Func R}
    {S : DivConfig R → Prop} {c d : DivConfig R} (h : Transfers oracle fn c d) (hS : S d) :
    Func.DivStep oracle div fn S c := by
  cases h with
  | jump hb hops hterm hargs hbt hwrite => exact .jump hb hops hterm hargs hbt hwrite hS
  | cond hb hops hterm hget hargs hbt hwrite =>
    exact .cond hb hops hterm hget hargs hbt hwrite hS

/-- The reverse reading of an exit out of a block's region: the run from the
block either reaches a terminator that ends it with the exit's outcome, or
reaches the block the exit names and is about to enter it. -/
def ExitBack (oracle : CallOracle) (fn : Func R) (sc : Scope R) (env : Semantics.Env Word)
    (c : DivConfig R) (lbl : Nat) (v : Value Word) (m : Memory) : Prop :=
  (∃ (vs : List Word) (d : DivConfig R), lbl = sc.depth ∧ v = packValues vs ∧
      Relation.ReflTransGen (Transfers oracle fn) c d ∧
      Finishes oracle fn d (.returned vs m)) ∨
  (∃ d : DivConfig R, lbl = sc.depth + 1 ∧ v = .unit ∧
      Relation.ReflTransGen (Transfers oracle fn) c d ∧ Finishes oracle fn d (.trapped m)) ∨
  (∃ (t : Label) (bt : Block R) (fr₁ fr₂ : Frame R) (vals : List Word),
    fn.block? t = some bt ∧ fn.Reachable t ∧
    (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome ∧
    lbl = fn.jumpLabel sc t ∧ v = packValues vals ∧
    fr₁.writeAll bt.params vals = some fr₂ ∧ sc.Agrees env fr₁ ∧
    Relation.TransGen (Transfers oracle fn) c ⟨t, fr₂, m⟩)

/-- Prefixing the run with more transfers keeps an exit's meaning. -/
theorem ExitBack.prefix {oracle : CallOracle} {fn : Func R} {sc : Scope R}
    {env : Semantics.Env Word} {c c' : DivConfig R} {lbl : Nat} {v : Value Word} {m : Memory}
    (hcc : Relation.TransGen (Transfers oracle fn) c c')
    (h : ExitBack oracle fn sc env c' lbl v m) : ExitBack oracle fn sc env c lbl v m := by
  rcases h with ⟨vs, d, h₁, h₂, h₃, h₄⟩ | ⟨d, h₁, h₂, h₃, h₄⟩ |
    ⟨t, bt, fr₁, fr₂, vals, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  · exact Or.inl ⟨vs, d, h₁, h₂, hcc.to_reflTransGen.trans h₃, h₄⟩
  · exact Or.inr (Or.inl ⟨d, h₁, h₂, hcc.to_reflTransGen.trans h₃, h₄⟩)
  · exact Or.inr (Or.inr ⟨t, bt, fr₁, fr₂, vals, h₁, h₂, h₃, h₄, h₅, h₆, h₇, hcc.trans h₈⟩)

/-- The statement of the reflected descent at a block, parameterised by the fuel
of the region, so that it can be proved by induction on that fuel. -/
def EntersBack (sigs : List Signature) (oracle : CallOracle) (fn : Func R) (fuel : Nat) : Prop :=
  ∀ (sc : Scope R) (l : Label) (b : Block R) (envP env : Semantics.Env Word) (fr : Frame R)
    (m : Memory) (lbl : Nat) (v : Value Word) (m' : Memory),
    fn.block? l = some b → EnterOkSem fn sc l →
    fn.blocks.length - fn.digraph.domDepth l ≤ fuel →
    (∀ i, env (i + 1) = envP i) → (sc.push b.params).Agrees env fr →
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env
      (blockRegion sigs fuel fn sc l) m lbl v m' →
    ExitBack oracle fn sc envP ⟨l, fr, m⟩ lbl v m' 

/-- **The `cfg` trampoline reflected.** Reading the forward argument backwards:
an exit below the block's arity runs one of its dominator-tree children and goes
round again, and an exit at or above it leaves the loop unchanged. -/
theorem followsBack {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) (fuel : Nat) (hprev : EntersBack sigs oracle fn fuel) :
    ∀ {N : Nat} {blocks : Fin N → Region (Opcode sigs)} {env₂ : Semantics.Env Word}
      {lbl : Nat} {v : Value Word} {m : Memory} {lbl' : Nat} {v' : Value Word} {m' : Memory},
      Semantics.Region.Follow (Opcode.step oracle) env₂ blocks lbl v m lbl' v' m' →
      ∀ (sc : Scope R) (l : Label) (b : Block R) (envP : Semantics.Env Word)
        (cfg₀ : DivConfig R),
        fn.block? l = some b → EnterOkSem fn sc l →
        fn.blocks.length - fn.digraph.domDepth l ≤ fuel + 1 →
        (∀ i, env₂ (i + (b.ops.length + 1)) = envP i) →
        N = (fn.domChildren (some l)).length →
        (∀ (i : Fin N) (c : Label), (fn.domChildren (some l))[i.val]? = some c →
          blocks i = blockRegion sigs fuel fn (blockScope fn sc l b) c) →
        ExitBack oracle fn (blockScope fn sc l b) env₂ cfg₀ lbl v m →
        ExitBack oracle fn sc envP cfg₀ lbl' v' m' := by
  intro N blocks env₂ lbl v m lbl' v' m' h
  induction h using Semantics.Region.Follow.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | @exit e₂ n lbl₀ bs cur s outside =>
    intro sc l b envP cfg₀ hb hok hfuel hshift hN _ hrep
    subst hN
    rcases hrep with ⟨vs, d, hlbl, hv, hrt, hfin⟩ | ⟨d, hlbl, hv, hrt, hfin⟩ |
      ⟨t, bt, fr₁, fr₂, vals, hbt, hreach, hdsome, hlbl, hv, hwrite, hag, hcont⟩
    · refine Or.inl ⟨vs, d, ?_, hv, hrt, hfin⟩
      rw [hlbl, blockScope_depth]
      omega
    · refine Or.inr (Or.inl ⟨d, ?_, hv, hrt, hfin⟩)
      rw [hlbl, blockScope_depth]
      omega
    · by_cases hid : fn.digraph.idom t = some l
      · obtain ⟨j, hjlt, hjget, hjeq⟩ := jumpLabel_blockScope_child (sc := sc) (b := b) hid
        rw [hlbl, hjeq] at outside
        omega
      · have hdsome' : (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome := by
          rwa [labelDepth_blockScope_outer hid] at hdsome
        have hjeq := jumpLabel_blockScope_outer (sc := sc) (b := b) hok.base.labelsOk hid hdsome'
        refine Or.inr (Or.inr ⟨t, bt, fr₁, fr₂, vals, hbt, hreach, hdsome', ?_, hv, hwrite,
          hag.drop (blockScope_vals_drop fn sc l b).symm (fun i => (hshift i).symm), hcont⟩)
        rw [hlbl, hjeq]
        omega
  | @step e₂ n lbl₀ nxt fnl bs cur mid vfin s s₁ s₂ inside head tail _ ihTail =>
    intro sc l b envP cfg₀ hb hok hfuel hshift hN hblocks hrep
    subst hN
    rcases hrep with ⟨vs, d, hlbl, hv, hrt, hfin⟩ | ⟨d, hlbl, hv, hrt, hfin⟩ |
      ⟨t, bt, fr₁, fr₂, vals, hbt, hreach, hdsome, hlbl, hv, hwrite, hag, hcont⟩
    · rw [hlbl, blockScope_depth] at inside
      omega
    · rw [hlbl, blockScope_depth] at inside
      omega
    · by_cases hid : fn.digraph.idom t = some l
      · obtain ⟨j, hjlt, hjget, hjeq⟩ := jumpLabel_blockScope_child (sc := sc) (b := b) hid
        have hlblj : lbl₀ = j := hlbl.trans hjeq
        subst hv
        have hbody : bs ⟨lbl₀, inside⟩
            = blockRegion sigs fuel fn (blockScope fn sc l b) t :=
          hblocks ⟨lbl₀, inside⟩ t (by
            show (fn.domChildren (some l))[lbl₀]? = some t
            rw [hlblj]
            exact hjget)
        rw [hbody] at head
        have hsd : fn.digraph.StrictlyDominates l t := Graph.Digraph.idom_strictlyDominates hid
        have hnotin : ∀ r, (blockScope fn sc l b).HasReg r → r ∉ bt.params := by
          intro r hr hp
          obtain ⟨a, hda, hra⟩ := blockScope_domOnly hb hok hr
          have hat : a ≠ t := by
            intro hat
            subst hat
            exact hsd.2 (Graph.Digraph.Dominates.antisymm hreach hsd.1 hda)
          refine defsOf_disjoint hwf.singleAssignment hat hra ?_
          rw [defsOf_eq hbt, Block.defs]
          exact List.mem_append_left _ hp
        have hagc : ((blockScope fn sc l b).push bt.params).Agrees
            (Semantics.extend e₂ (packValues vals)) fr₂ :=
          (hag.frame (fun r hr => get_writeAll_of_not_mem hwrite (hnotin r hr))).push
            (readAll_writeAll hwrite (params_nodup hwf.singleAssignment hbt))
        have hfuelc : fn.blocks.length - fn.digraph.domDepth t ≤ fuel := by
          have := Graph.Digraph.domDepth_lt_of_idom hid
          omega
        have hchild := hprev (blockScope fn sc l b) t bt e₂
          (Semantics.extend e₂ (packValues vals)) fr₂ s nxt mid s₁ hbt
          (enterOkSem_child hb hok hid) hfuelc (fun _ => rfl) hagc head
        exact ihTail sc l b envP cfg₀ hb hok hfuel hshift rfl hblocks
          (ExitBack.prefix hcont hchild)
      · have hdsome' : (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome := by
          rwa [labelDepth_blockScope_outer hid] at hdsome
        have hjeq := jumpLabel_blockScope_outer (sc := sc) (b := b) hok.base.labelsOk hid hdsome'
        rw [hlbl, hjeq] at inside
        omega
  | _ => trivial

/-- What a block's terminator does, read off its region's exit: it either ends
the run or makes exactly one transfer. -/
def TermBack (oracle : CallOracle) (fn : Func R) (sc : Scope R) (env : Semantics.Env Word)
    (c : DivConfig R) (lbl : Nat) (v : Value Word) (m : Memory) : Prop :=
  (∃ vs : List Word, lbl = sc.depth ∧ v = packValues vs ∧
      Finishes oracle fn c (.returned vs m)) ∨
  (lbl = sc.depth + 1 ∧ v = .unit ∧ Finishes oracle fn c (.trapped m)) ∨
  (∃ (t : Label) (bt : Block R) (fr₁ fr₂ : Frame R) (vals : List Word),
    fn.block? t = some bt ∧ fn.Reachable t ∧
    (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome ∧
    lbl = fn.jumpLabel sc t ∧ v = packValues vals ∧
    fr₁.writeAll bt.params vals = some fr₂ ∧ sc.Agrees env fr₁ ∧
    Transfers oracle fn c ⟨t, fr₂, m⟩)

/-- A terminator's exit is an exit of the whole block's region. -/
theorem TermBack.toExitBack {oracle : CallOracle} {fn : Func R} {sc : Scope R}
    {env : Semantics.Env Word} {c : DivConfig R} {lbl : Nat} {v : Value Word} {m : Memory}
    (h : TermBack oracle fn sc env c lbl v m) : ExitBack oracle fn sc env c lbl v m := by
  rcases h with ⟨vs, h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ |
    ⟨t, bt, fr₁, fr₂, vals, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  · exact Or.inl ⟨vs, c, h₁, h₂, Relation.ReflTransGen.refl, h₃⟩
  · exact Or.inr (Or.inl ⟨c, h₁, h₂, Relation.ReflTransGen.refl, h₃⟩)
  · exact Or.inr (Or.inr ⟨t, bt, fr₁, fr₂, vals, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      Relation.TransGen.single h₈⟩)

/-- **A block's terminator makes the transition its region's entry does.** -/
theorem term_back {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) {sc : Scope R} {l : Label} {b : Block R}
    (hb : fn.block? l = some b) (hok : EnterOkSem fn sc l) {env₂ : Semantics.Env Word}
    {fr fr₁ : Frame R} {m m₁ : Memory} (hag₂' : (blockScope fn sc l b).Agrees env₂ fr₁)
    (hops : Ops.Exec oracle b.ops fr m fr₁ m₁) {first : Nat} {initial : Value Word}
    {m₂ : Memory}
    (hentry : Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env₂
      (Term.toRegion sigs fn (blockScope fn sc l b) b.term) m₁ first initial m₂) :
    TermBack oracle fn (blockScope fn sc l b) env₂ ⟨l, fr, m⟩ first initial m₂ := by
  have hcovterm := covers_term_uses hwf hb hok
  cases hterm : b.term with
  | ret regs =>
    rw [hterm] at hentry hcovterm
    have hcovregs : (blockScope fn sc l b).Covers regs := hcovterm
    obtain ⟨rfl, harg⟩ := region_eval_br_inv hentry
    obtain ⟨vals, hvals⟩ := hag₂'.readAll hcovregs
    obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag₂' hcovregs hvals).mp harg
    exact Or.inl ⟨vals, rfl, rfl, .ret hb hops hterm hvals⟩
  | trap =>
    rw [hterm] at hentry
    obtain ⟨rfl, harg⟩ := region_eval_br_inv hentry
    obtain ⟨rfl, rfl⟩ := eval_unit_inv harg
    exact Or.inr (Or.inl ⟨rfl, rfl, .trap hb hops hterm⟩)
  | jump tgt as =>
    rw [hterm] at hentry hcovterm
    have hcovas : (blockScope fn sc l b).Covers as := hcovterm
    obtain ⟨rfl, harg⟩ := region_eval_br_inv hentry
    obtain ⟨vals, hvals⟩ := hag₂'.readAll hcovas
    obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag₂' hcovas hvals).mp harg
    have hsucc : tgt ∈ b.term.successors := by rw [hterm]; simp [Term.successors]
    have hlt := lt_of_mem_successors hwf.sig hb hsucc
    have hedge : fn.Edge l tgt := Func.edge_of_term hb hsucc hlt
    obtain ⟨bt, hbt⟩ : ∃ bt, fn.block? tgt = some bt := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hlen : bt.params.length = vals.length := by
      have h1 := (params_length_of_argsMatch hwf.argsMatch hb
        (show (tgt, as) ∈ b.term.args by rw [hterm]; simp [Term.args])).1
      have h2 := readAll_length hvals
      have hpc : fn.paramCount tgt = bt.params.length := by rw [Func.paramCount, hbt]; rfl
      omega
    obtain ⟨fr₂, hwrite⟩ := writeAll_isSome fr₁ hlen
    exact Or.inr (Or.inr ⟨tgt, bt, fr₁, fr₂, vals, hbt, hok.base.reachable.step hedge,
      labelDepth_blockScope_target hok.base hedge, rfl, rfl, hwrite, hag₂',
      Transfers.jump hb hops hterm hvals hbt hwrite⟩)
  | cond c t₁ a₁ t₂ a₂ =>
    rw [hterm] at hentry hcovterm
    have hcovc : (blockScope fn sc l b).Covers [c] := by
      refine hcovterm.mono ?_
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      simp [Term.uses]
    obtain ⟨x, hx⟩ := hag₂'.get_isSome (hcovc c (by simp))
    have hmk : ∀ (tgt : Label) (as : List R), (tgt, as) ∈ b.term.args →
        tgt ∈ b.term.successors →
        ∀ (vals : List Word), fr₁.readAll as = some vals →
        (∀ (bt : Block R) (fr₂ : Frame R), fn.block? tgt = some bt →
          fr₁.writeAll bt.params vals = some fr₂ →
          Transfers oracle fn ⟨l, fr, m⟩ ⟨tgt, fr₂, m₁⟩) →
        TermBack oracle fn (blockScope fn sc l b) env₂ ⟨l, fr, m⟩
          (fn.jumpLabel (blockScope fn sc l b) tgt) (packValues vals) m₁ := by
      intro tgt as hargs hsucc vals hvals hcont
      have hlt := lt_of_mem_successors hwf.sig hb hsucc
      have hedge : fn.Edge l tgt := Func.edge_of_term hb hsucc hlt
      obtain ⟨bt, hbt⟩ : ∃ bt, fn.block? tgt = some bt := ⟨_, List.getElem?_eq_getElem hlt⟩
      have hlen : bt.params.length = vals.length := by
        have h1 := (params_length_of_argsMatch hwf.argsMatch hb hargs).1
        have h2 := readAll_length hvals
        have hpc : fn.paramCount tgt = bt.params.length := by rw [Func.paramCount, hbt]; rfl
        omega
      obtain ⟨fr₂, hwrite⟩ := writeAll_isSome fr₁ hlen
      exact Or.inr (Or.inr ⟨tgt, bt, fr₁, fr₂, vals, hbt, hok.base.reachable.step hedge,
        labelDepth_blockScope_target hok.base hedge, rfl, rfl, hwrite, hag₂',
        hcont bt fr₂ hbt hwrite⟩)
    rcases region_eval_case_inv hentry with ⟨va, mα, hs, hbr⟩ | ⟨va, mα, hs, hbr⟩
    · obtain ⟨vp, mβ, hp, hstep⟩ := eval_op_inv hs
      obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag₂' hcovc (readAll_singleton hx)).mp hp
      obtain ⟨rfl, hval⟩ := Opcode.step_test_iff.mp hstep
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0] at hval
        simp at hval
      have hifa : (if x = 0 then a₂ else a₁) = a₁ := by
        split
        · rename_i h0; exact absurd h0 hx0
        · rfl
      have hift : (if x = 0 then t₂ else t₁) = t₁ := by
        split
        · rename_i h0; exact absurd h0 hx0
        · rfl
      obtain ⟨rfl, harg⟩ := region_eval_br_inv hbr
      have hcova : (blockScope fn sc l b).Covers a₁ := by
        refine hcovterm.mono ?_
        intro y hy
        simp only [Term.uses]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ hy)
      obtain ⟨vals, hvals⟩ := hag₂'.readAll hcova
      have harg' := eval_of_rename ((blockScope fn sc l b).pack a₁) (fun _ => rfl) harg
      obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag₂' hcova hvals).mp harg'
      refine hmk t₁ a₁ (by rw [hterm]; simp [Term.args]) (by rw [hterm]; simp [Term.successors])
        vals hvals ?_
      intro bt fr₂ hbt hwrite
      rw [← hift]
      refine Transfers.cond hb hops hterm hx ?_ ?_ hwrite
      · rw [hifa]; exact hvals
      · rw [hift]; exact hbt
    · obtain ⟨vp, mβ, hp, hstep⟩ := eval_op_inv hs
      obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag₂' hcovc (readAll_singleton hx)).mp hp
      obtain ⟨rfl, hval⟩ := Opcode.step_test_iff.mp hstep
      have hx0 : x = 0 := by
        by_contra h0
        have : (if x = 0 then (Value.inr Value.unit : Value Word) else .inl .unit)
            = .inl .unit := by
          split
          · rename_i h; exact absurd h h0
          · rfl
        rw [this] at hval
        simp at hval
      have hifa : (if x = 0 then a₂ else a₁) = a₂ := by
        split
        · rfl
        · rename_i h0; exact absurd hx0 h0
      have hift : (if x = 0 then t₂ else t₁) = t₂ := by
        split
        · rfl
        · rename_i h0; exact absurd hx0 h0
      obtain ⟨rfl, harg⟩ := region_eval_br_inv hbr
      have hcova : (blockScope fn sc l b).Covers a₂ := by
        refine hcovterm.mono ?_
        intro y hy
        simp only [Term.uses]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hy)
      obtain ⟨vals, hvals⟩ := hag₂'.readAll hcova
      have harg' := eval_of_rename ((blockScope fn sc l b).pack a₂) (fun _ => rfl) harg
      obtain ⟨rfl, rfl⟩ := (Scope.eval_pack_iff hag₂' hcova hvals).mp harg'
      refine hmk t₂ a₂ (by rw [hterm]; simp [Term.args]) (by rw [hterm]; simp [Term.successors])
        vals hvals ?_
      intro bt fr₂ hbt hwrite
      rw [← hift]
      refine Transfers.cond hb hops hterm hx ?_ ?_ hwrite
      · rw [hifa]; exact hvals
      · rw [hift]; exact hbt

omit [DecidableEq R] in
/-- The entry block has no immediate dominator. -/
theorem idom_entry_none {fn : Func R} : fn.digraph.idom fn.entry = none :=
  Graph.Digraph.idom_none_entry fn.digraph

omit [DecidableEq R] in
/-- A transfer to the entry block names the outermost `cfg`'s only block. -/
theorem jumpLabel_root {fn : Func R} :
    fn.jumpLabel (⟨[], [(none, 1)]⟩ : Scope R) fn.entry = 0 := by
  rw [Func.jumpLabel, idom_entry_none]
  simp [Scope.labelDepth, Scope.depth, Func.domChildren, idxIn]

/-- **Every run of a block's region is a run of the block.** The `let₁` chain
forces the ops to execute, the `cfg`'s entry forces the terminator's transition,
and the `cfg`'s `Follow` resolves the transfer. -/
theorem entersBack {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) (hsigs : CallOracle.MatchesSigs oracle sigs)
    (hcalls : fn.CallsMatch sigs) : ∀ fuel : Nat, EntersBack sigs oracle fn fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro sc l b envP env fr m lbl v m' hb hok hfuel _ _ _
    exact absurd hfuel (by have := domDepth_lt hwf.sig hok.base.reachable; omega)
  | succ fuel ih =>
    intro sc l b envP env fr m lbl v m' hb hok hfuel hshift hag heval
    rw [blockRegion_succ hb] at heval
    obtain ⟨fr₁, m₁, env₂, hops, hag₂, hsh₂, hcfg⟩ :=
      opsRegion_exec_of_eval hsigs b.ops hag (block_ops_covers hwf hb hok)
        (block_ops_fresh hwf hb hok) (block_ops_calls hcalls hb) heval
    obtain ⟨first, initial, m₂, hentry, hfollow⟩ := region_eval_cfg_inv hcfg
    have hag₂' : (blockScope fn sc l b).Agrees env₂ fr₁ := hag₂
    have hsh₂' : ∀ i, env₂ (i + (b.ops.length + 1)) = envP i := by
      intro i
      rw [show i + (b.ops.length + 1) = (i + 1) + b.ops.length by omega, hsh₂ (i + 1)]
      exact hshift i
    exact followsBack hwf fuel ih hfollow sc l b envP _ hb hok hfuel hsh₂' rfl
      (fun i c hc => by
        have hic : (fn.domChildren (some l))[i.val]'i.isLt = c :=
          Option.some.inj ((List.getElem?_eq_getElem i.isLt).symm.trans hc)
        rw [hic])
      (term_back hwf hb hok hag₂' hops hentry).toExitBack

/-- A `Follow` whose label names a block takes a step. -/
theorem follow_step_inv {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {n : Nat} {blocks : Fin n → Region Φ} {lbl : Nat}
    {v : Value Word} {s : σ} {lbl' : Nat} {v' : Value Word} {s' : σ}
    (h : Semantics.Region.Follow instr env blocks lbl v s lbl' v' s') (hlt : lbl < n) :
    ∃ next mid s₁, Semantics.Region.Eval instr (Semantics.extend env v) (blocks ⟨lbl, hlt⟩) s
        next mid s₁ ∧ Semantics.Region.Follow instr env blocks next mid s₁ lbl' v' s' := by
  cases h with
  | exit outside => exact absurd hlt (Nat.not_lt_of_ge outside)
  | step inside head tail => exact ⟨_, _, _, head, tail⟩

/-- **The outermost `cfg` reflected.** Its only block is the entry block, so an
exit below its arity is a back edge to the entry and every other exit reports
the function's outcome. -/
theorem followsBackRoot {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) (hsigs : CallOracle.MatchesSigs oracle sigs)
    (hcalls : fn.CallsMatch sigs) {b : Block R} (hb : fn.block? fn.entry = some b) :
    ∀ {N : Nat} {blocks : Fin N → Region (Opcode sigs)} {env : Semantics.Env Word}
      {lbl : Nat} {v : Value Word} {m : Memory} {lbl' : Nat} {v' : Value Word} {m' : Memory},
      Semantics.Region.Follow (Opcode.step oracle) env blocks lbl v m lbl' v' m' →
      N = 1 →
      (∀ i : Fin N, blocks i = blockRegion sigs fn.blocks.length fn ⟨[], [(none, 1)]⟩ fn.entry) →
      ∀ cfg₀ : DivConfig R, ExitBack oracle fn ⟨[], [(none, 1)]⟩ env cfg₀ lbl v m →
        ∃ out, Func.Exec oracle fn cfg₀.label cfg₀.frame cfg₀.mem out ∧
          RootExit out lbl' v' m' := by
  intro N blocks env lbl v m lbl' v' m' h
  induction h using Semantics.Region.Follow.rec
      (motive_1 := fun _ _ _ _ _ _ _ => True) with
  | @exit e₂ n lbl₀ bs cur s outside =>
    intro hN _ cfg₀ hrep
    subst hN
    rcases hrep with ⟨vs, d, hlbl, hv, hrt, hfin⟩ | ⟨d, hlbl, hv, hrt, hfin⟩ |
      ⟨t, bt, fr₁, fr₂, vals, hbt, hreach, hdsome, hlbl, hv, hwrite, hag, hcont⟩
    · exact ⟨_, Transfers.exec_of_reflTransGen hrt hfin.exec,
        Or.inl ⟨vs, rfl, by rw [hlbl]; rfl, hv⟩⟩
    · exact ⟨_, Transfers.exec_of_reflTransGen hrt hfin.exec,
        Or.inr ⟨rfl, by rw [hlbl]; rfl, hv⟩⟩
    · exfalso
      have hid : fn.digraph.idom t = none := by
        cases hidt : fn.digraph.idom t with
        | none => rfl
        | some a =>
          rw [hidt] at hdsome
          simp [Scope.labelDepth] at hdsome
      have ht : t = fn.entry := by
        by_contra hne
        obtain ⟨a, ha, -, -⟩ := Graph.Digraph.idom_spec hreach hne
        rw [hid] at ha
        exact absurd ha (by simp)
      subst ht
      rw [hlbl, jumpLabel_root] at outside
      omega
  | @step e₂ n lbl₀ nxt fnl bs cur mid vfin s s₁ s₂ inside head tail _ ihTail =>
    intro hN hblocks cfg₀ hrep
    subst hN
    rcases hrep with ⟨vs, d, hlbl, hv, hrt, hfin⟩ | ⟨d, hlbl, hv, hrt, hfin⟩ |
      ⟨t, bt, fr₁, fr₂, vals, hbt, hreach, hdsome, hlbl, hv, hwrite, hag, hcont⟩
    · rw [hlbl] at inside
      exact absurd inside (by simp [Scope.depth])
    · rw [hlbl] at inside
      exact absurd inside (by simp [Scope.depth])
    · have hid : fn.digraph.idom t = none := by
        cases hidt : fn.digraph.idom t with
        | none => rfl
        | some a =>
          rw [hidt] at hdsome
          simp [Scope.labelDepth] at hdsome
      have ht : t = fn.entry := by
        by_contra hne
        obtain ⟨a, ha, -, -⟩ := Graph.Digraph.idom_spec hreach hne
        rw [hid] at ha
        exact absurd ha (by simp)
      subst ht
      subst hv
      obtain rfl : bt = b := Option.some.inj (hbt.symm.trans hb)
      rw [hblocks ⟨lbl₀, inside⟩] at head
      have hagc : ((⟨[], [(none, 1)]⟩ : Scope R).push bt.params).Agrees
          (Semantics.extend e₂ (packValues vals)) fr₂ :=
        agrees_root.push (readAll_writeAll hwrite (params_nodup hwf.singleAssignment hbt))
      have hchild := entersBack hwf hsigs hcalls fn.blocks.length ⟨[], [(none, 1)]⟩ fn.entry bt
        e₂ (Semantics.extend e₂ (packValues vals)) fr₂ s nxt mid s₁ hbt enterOkSem_root
        (by omega) (fun _ => rfl) hagc head
      exact ihTail rfl hblocks cfg₀ (ExitBack.prefix hcont hchild)
  | _ => trivial

/-- **A run of the region is a run of the function.** -/
theorem toLambdaSSA_exec_of_eval {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (hwf : fn.WellFormed) (hsigs : CallOracle.MatchesSigs oracle sigs)
    (hcalls : fn.CallsMatch sigs) {args : List Word} {b : Block R} {fr : Frame R}
    (hb : fn.block? fn.entry = some b) (hfr : Frame.empty.writeAll b.params args = some fr)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m : Memory} {lbl : Nat}
    {v : Value Word} {m' : Memory}
    (h : Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env (toLambdaSSA sigs fn) m
      lbl v m') :
    ∃ out, Func.Exec oracle fn fn.entry fr m out ∧ RootExit out lbl v m' := by
  obtain ⟨first, initial, m₁, hentry, hfollow⟩ := region_eval_cfg_inv h
  obtain ⟨rfl, harg⟩ := region_eval_br_inv hentry
  obtain ⟨hv, hm⟩ := eval_var_inv harg
  rw [hm] at hfollow
  obtain ⟨next, mid, m₂, head, tail⟩ := follow_step_inv hfollow (by omega)
  rw [hv, henv] at head
  have hagc : ((⟨[], [(none, 1)]⟩ : Scope R).push b.params).Agrees
      (Semantics.extend env (packValues args)) fr :=
    agrees_root.push (readAll_writeAll hfr (params_nodup hwf.singleAssignment hb))
  have hchild := entersBack hwf hsigs hcalls fn.blocks.length ⟨[], [(none, 1)]⟩ fn.entry b
    env (Semantics.extend env (packValues args)) fr m next mid m₂ hb enterOkSem_root
    (by omega) (fun _ => rfl) hagc head
  exact followsBackRoot hwf hsigs hcalls hb tail rfl (fun _ => rfl) ⟨fn.entry, fr, m⟩ hchild

/-- **Finite outcomes agree exactly.** The region reaches external label `0`
with the packed returned values exactly when the function returns them, and
external label `1` with `unit` exactly when it traps. The final memories
coincide and neither direction needs determinism or a typing hypothesis beyond
well-formedness. Two hypotheses are needed that the statement of
`toLambdaSSA_hasType` also needs: `fn.CallsMatch sigs` says each call names its
callee's declared arity, and `CallOracle.MatchesSigs` says the oracle returns
that many words — without the latter an abstract oracle could return a tuple of
the wrong width and the region would take a step the machine cannot. -/
theorem toLambdaSSA_eval_iff {sigs : List Signature} {oracle : CallOracle} {fn : Func R}
    (h : fn.WellFormed) (hsigs : CallOracle.MatchesSigs oracle sigs)
    (hcalls : fn.CallsMatch sigs) {args : List Word} {b : Block R} {fr : Frame R}
    (hb : fn.block? fn.entry = some b) (hfr : Frame.empty.writeAll b.params args = some fr)
    {env : Semantics.Env Word} (henv : env 0 = packValues args)
    {m m' : Memory} {label : Nat} {value : Value Word} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) oracle) env (toLambdaSSA sigs fn) m
        label value m' ↔
      (label = 0 ∧ ∃ vs, value = packValues vs ∧
          Func.Exec oracle fn fn.entry fr m (.returned vs m')) ∨
      (label = 1 ∧ value = .unit ∧ Func.Exec oracle fn fn.entry fr m (.trapped m')) := by
  constructor
  · intro heval
    obtain ⟨out, hexec, hroot⟩ := toLambdaSSA_exec_of_eval h hsigs hcalls hb hfr henv heval
    rcases hroot with ⟨vs, hout, hlbl, hv⟩ | ⟨hout, hlbl, hv⟩
    · exact Or.inl ⟨hlbl, vs, hv, hout ▸ hexec⟩
    · exact Or.inr ⟨hlbl, hv, hout ▸ hexec⟩
  · intro hcase
    rcases hcase with ⟨rfl, vs, rfl, hexec⟩ | ⟨rfl, rfl, hexec⟩
    · obtain ⟨lbl, v, m₁, heval, hroot⟩ :=
        toLambdaSSA_eval_of_exec (sigs := sigs) h hb hfr henv hexec
      rcases hroot with ⟨vs', hout, hlbl, hv⟩ | ⟨hout, -, -⟩
      · rw [Exit.returned.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        rw [hlbl, hv] at heval
        exact heval
      · exact absurd hout (by simp)
    · obtain ⟨lbl, v, m₁, heval, hroot⟩ :=
        toLambdaSSA_eval_of_exec (sigs := sigs) h hb hfr henv hexec
      rcases hroot with ⟨vs', hout, -, -⟩ | ⟨hout, hlbl, hv⟩
      · exact absurd hout (by simp)
      · obtain rfl : m₁ = m' := (Exit.trapped.inj hout).symm
        rw [hlbl, hv] at heval
        exact heval

/-! ### Terms the translation builds have no primitives

The only RTL construct that can diverge is a call, and the translation puts
calls nowhere except at the head of an op's term. Register references, packed
tuples and the arguments of a transfer are built from variables, pairs and pair
eliminations alone, so no divergent primitive can hide in them. -/

/-- A term with no operator application in it. -/
def OpFree {Φ : Type} : Tm Φ → Prop
  | .var _ => True
  | .op _ _ => False
  | .let₁ a b => OpFree a ∧ OpFree b
  | .pair a b => OpFree a ∧ OpFree b
  | .unit => True
  | .let₂ a b => OpFree a ∧ OpFree b
  | .inl a => OpFree a
  | .inr a => OpFree a
  | .case a l r => OpFree a ∧ OpFree l ∧ OpFree r
  | .abort a => OpFree a

/-- Renaming cannot introduce an operator application. -/
theorem OpFree.rename {Φ : Type} :
    ∀ {a : Tm Φ} {ρ : Nat → Nat}, OpFree a → OpFree (a.rename ρ) := by
  intro a
  induction a with
  | var i => intro _ _; trivial
  | op f x _ => intro _ h; exact h.elim
  | let₁ x y ihx ihy => intro _ h; exact ⟨ihx h.1, ihy h.2⟩
  | pair x y ihx ihy => intro _ h; exact ⟨ihx h.1, ihy h.2⟩
  | unit => intro _ _; trivial
  | let₂ x y ihx ihy => intro _ h; exact ⟨ihx h.1, ihy h.2⟩
  | inl x ihx => intro _ h; exact ihx h
  | inr x ihx => intro _ h; exact ihx h
  | case x y z ihx ihy ihz => intro _ h; exact ⟨ihx h.1, ihy h.2.1, ihz h.2.2⟩
  | abort x ihx => intro _ h; exact ihx h

/-- A term with no operator application has no primitive to diverge at. -/
theorem not_opFree_of_externalDiverges {Φ σ : Type}
    {instr : Φ → Value Word → σ → Value Word → σ → Prop} {prim : Φ → Value Word → σ → Prop}
    {env : Semantics.Env Word} {a : Tm Φ} {s : σ}
    (h : Semantics.Tm.ExternalDiverges instr prim env a s) : ¬ OpFree a := by
  induction h with
  | op_arg _ ih => exact fun hf => hf.elim
  | primitive _ _ => exact fun hf => hf.elim
  | let₁_arg _ ih => exact fun hf => ih hf.1
  | let₁_body _ _ ih => exact fun hf => ih hf.2
  | pair_left _ ih => exact fun hf => ih hf.1
  | pair_right _ _ ih => exact fun hf => ih hf.2
  | let₂_arg _ ih => exact fun hf => ih hf.1
  | let₂_body _ _ ih => exact fun hf => ih hf.2
  | inl _ ih => exact fun hf => ih hf
  | inr _ ih => exact fun hf => ih hf
  | case_arg _ ih => exact fun hf => ih hf.1
  | case_inl _ _ ih => exact fun hf => ih hf.2.1
  | case_inr _ _ ih => exact fun hf => ih hf.2.2
  | abort_arg _ ih => exact fun hf => ih hf

/-- Projections are built from variables and pair eliminations. -/
theorem proj_opFree {Φ : Type} : ∀ (j : Nat) {t : Tm Φ}, OpFree t → OpFree (proj j t)
  | 0, _, h => ⟨h, trivial⟩
  | _ + 1, _, h => ⟨h, proj_opFree _ trivial⟩

/-- A register reference has no operator application. -/
theorem Scope.ref_opFree {Φ : Type} (sc : Scope R) (r : R) : OpFree (sc.ref (Φ := Φ) r) := by
  rw [Scope.ref]
  split
  · exact proj_opFree _ trivial
  · exact trivial

/-- A packed register list has no operator application. -/
theorem Scope.pack_opFree {Φ : Type} (sc : Scope R) : ∀ (rs : List R), OpFree (sc.pack (Φ := Φ) rs)
  | [] => trivial
  | r :: rs => ⟨sc.ref_opFree r, sc.pack_opFree rs⟩

/-- A branch whose argument has no operator application does not diverge. -/
theorem br_not_diverges {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {prim : Φ → Value Word → σ → Prop} {env : Semantics.Env Word} {lbl : Nat} {arg : Tm Φ}
    {s : σ} (hf : OpFree arg) :
    ¬ Semantics.External.Diverges instr prim (.region env (.br lbl arg) s) := by
  intro h
  cases h.unfold with
  | core h' => cases h'
  | br hd => exact not_opFree_of_externalDiverges hd hf

/-- **A terminator's region never diverges.** Its branches carry packed tuples
and its condition is the branch opcode, and none of those is a divergent
primitive. -/
theorem Term.toRegion_not_diverges {sigs : List Signature} {oracle : CallOracle}
    {div : DivOracle} {fn : Func R} {sc : Scope R} {env : Semantics.Env Word} {t : Term R}
    {m : Memory} :
    ¬ Semantics.External.Diverges (Opcode.step (sigs := sigs) oracle) (Opcode.divergent div)
      (.region env (Term.toRegion sigs fn sc t) m) := by
  cases t with
  | jump tgt as => exact br_not_diverges (sc.pack_opFree as)
  | ret vs => exact br_not_diverges (sc.pack_opFree vs)
  | trap => exact br_not_diverges trivial
  | cond c t₁ a₁ t₂ a₂ =>
    intro h
    cases h.unfold with
    | core h' =>
      cases h' with
      | case_inl _ rest => exact br_not_diverges (OpFree.rename (sc.pack_opFree a₁)) rest
      | case_inr _ rest => exact br_not_diverges (OpFree.rename (sc.pack_opFree a₂)) rest
    | case_arg hd =>
      cases hd with
      | op_arg hd' => exact not_opFree_of_externalDiverges hd' (sc.pack_opFree [c])
      | primitive _ hdiv => cases hdiv

/-! ### Divergence -/

/-- A diverging `Follow` is inside its `cfg`'s blocks. -/
theorem follow_diverges_lt {Φ σ : Type} {instr : Φ → Value Word → σ → Value Word → σ → Prop}
    {prim : Φ → Value Word → σ → Prop} {env : Semantics.Env Word} {n : Nat}
    {blocks : Fin n → Region Φ} {lbl : Nat} {v : Value Word} {s : σ}
    (h : Semantics.External.Diverges instr prim (.follow env blocks lbl v s)) : lbl < n := by
  cases h.unfold with
  | core h' =>
    cases h' with
    | follow_body inside _ => exact inside
    | follow_next inside _ _ => exact inside

/-- Entering a dominator-tree child keeps the enclosing scope's agreement and
reads back the parameters just written. -/
theorem agrees_child {fn : Func R} (hwf : fn.WellFormed) {sc : Scope R} {l t : Label}
    {b bt : Block R} (hb : fn.block? l = some b) (hok : EnterOkSem fn sc l)
    (hbt : fn.block? t = some bt) (hid : fn.digraph.idom t = some l)
    {fr₁ fr₂ : Frame R} {vals : List Word} (hwrite : fr₁.writeAll bt.params vals = some fr₂)
    {env₂ : Semantics.Env Word} (hag : (blockScope fn sc l b).Agrees env₂ fr₁) :
    (blockScope fn sc l b).Agrees env₂ fr₂ ∧ fr₂.readAll bt.params = some vals := by
  have hsd := Graph.Digraph.idom_strictlyDominates hid
  have hreach := Graph.Digraph.reachable_of_idom hid
  have hnotin : ∀ r, (blockScope fn sc l b).HasReg r → r ∉ bt.params := by
    intro r hr hp
    obtain ⟨a, hda, hra⟩ := blockScope_domOnly hb hok hr
    have hat : a ≠ t := by
      intro hat
      subst hat
      exact hsd.2 (Graph.Digraph.Dominates.antisymm hreach hsd.1 hda)
    refine defsOf_disjoint hwf.singleAssignment hat hra ?_
    rw [defsOf_eq hbt, Block.defs]
    exact List.mem_append_left _ hp
  exact ⟨hag.frame (fun r hr => get_writeAll_of_not_mem hwrite (hnotin r hr)),
    readAll_writeAll hwrite (params_nodup hwf.singleAssignment hbt)⟩

/-- A divergent call primitive is the oracle diverging on packed arguments. -/
theorem Opcode.divergent_call_inv {sigs : List Signature} {div : DivOracle} {f : FuncId}
    {value : Value Word} {m : Memory}
    (h : Opcode.divergent (sigs := sigs) div (.call f) value m) :
    ∃ vals, value = packValues vals ∧ div f vals m := by
  cases h with | call hd => exact ⟨_, rfl, hd⟩

/-- **An op's term diverges only at a call whose callee runs forever.** -/
theorem Op.toTm_externalDiverges {sigs : List Signature} {oracle : CallOracle} {div : DivOracle}
    {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R} (hag : sc.Agrees env fr)
    {o : Op R} (hcov : sc.Covers o.uses) {m : Memory}
    (h : Semantics.Tm.ExternalDiverges (Opcode.step (sigs := sigs) oracle) (Opcode.divergent div)
      env (Op.toTm sigs sc o) m) :
    ∃ (f : FuncId) (args results : List R) (vals : List Word),
      o = Op.call f args results ∧ fr.readAll args = some vals ∧ div f vals m := by
  cases o with
  | const d val =>
    cases h with
    | op_arg h' => cases h'
    | primitive _ hdiv => cases hdiv
  | move d s =>
    cases h with
    | op_arg h' => exact absurd (sc.pack_opFree [s]) (not_opFree_of_externalDiverges h')
    | primitive _ hdiv => cases hdiv
  | unary op d s =>
    cases h with
    | op_arg h' => exact absurd (sc.pack_opFree [s]) (not_opFree_of_externalDiverges h')
    | primitive _ hdiv => cases hdiv
  | binary op d a c =>
    cases h with
    | op_arg h' => exact absurd (sc.pack_opFree [a, c]) (not_opFree_of_externalDiverges h')
    | primitive _ hdiv => cases hdiv
  | load w e d base off =>
    cases h with
    | op_arg h' => exact absurd (sc.pack_opFree [base]) (not_opFree_of_externalDiverges h')
    | primitive _ hdiv => cases hdiv
  | store w base off src =>
    cases h with
    | op_arg h' => exact absurd (sc.pack_opFree [base, src]) (not_opFree_of_externalDiverges h')
    | primitive _ hdiv => cases hdiv
  | call f args results =>
    obtain ⟨vals, hvals⟩ := hag.readAll hcov
    cases h with
    | op_arg h' => exact absurd (sc.pack_opFree args) (not_opFree_of_externalDiverges h')
    | primitive harg hdiv =>
      obtain ⟨vals', heqv, hd⟩ := Opcode.divergent_call_inv hdiv
      subst heqv
      obtain ⟨hmid, heq⟩ := (Scope.eval_pack_iff hag hcov hvals).mp harg
      obtain rfl : vals' = vals := packValues_injective heq
      rw [hmid] at hd
      exact ⟨f, args, results, _, rfl, hvals, hd⟩

/-- **A diverging `let₁` chain diverges at a call.** Either one of the block's
ops is a call whose callee runs forever, or every op runs and the region the
chain wraps diverges. -/
theorem opsRegion_divStep {sigs : List Signature} {oracle : CallOracle} {div : DivOracle}
    (hsigs : CallOracle.MatchesSigs oracle sigs) :
    ∀ (ops : List (Op R)) {sc : Scope R} {env : Semantics.Env Word} {fr : Frame R}
      {m : Memory} {K : Region (Opcode sigs)},
      sc.Agrees env fr →
      (∀ (i : Nat) (o : Op R), ops[i]? = some o → (sc.afterOps (ops.take i)).Covers o.uses) →
      (∀ (i : Nat) (o : Op R), ops[i]? = some o →
        (sc.afterOps (ops.take i)).Fresh o.defs ∧ o.defs.Nodup) →
      (∀ (i : Nat) (o : Op R), ops[i]? = some o → ∀ (f : FuncId) (args results : List R),
        o = Op.call f args results → results.length = (sigAt sigs f).results) →
      Semantics.External.Diverges (Opcode.step oracle) (Opcode.divergent div)
        (.region env (opsRegion sigs sc ops K) m) →
      (∃ (pre : List (Op R)) (f : FuncId) (args results : List R) (post : List (Op R))
          (fr₁ : Frame R) (m₁ : Memory) (vals : List Word),
          ops = pre ++ Op.call f args results :: post ∧ Ops.Exec oracle pre fr m fr₁ m₁ ∧
          fr₁.readAll args = some vals ∧ div f vals m₁) ∨
      (∃ (fr₁ : Frame R) (m₁ : Memory) (env₂ : Semantics.Env Word),
          Ops.Exec oracle ops fr m fr₁ m₁ ∧ (sc.afterOps ops).Agrees env₂ fr₁ ∧
          (∀ i, env₂ (i + ops.length) = env i) ∧
          Semantics.External.Diverges (Opcode.step oracle) (Opcode.divergent div)
            (.region env₂ K m₁)) := by
  intro ops
  induction ops with
  | nil =>
    intro sc env fr m K hag _ _ _ hdiv
    exact Or.inr ⟨fr, m, env, .nil, hag, fun _ => rfl, hdiv⟩
  | cons o os ih =>
    intro sc env fr m K hag hcov hfresh hcalls hdiv
    cases hdiv.unfold with
    | let₁_arg hd =>
      obtain ⟨f, args, results, vals, rfl, hargs, hdv⟩ :=
        Op.toTm_externalDiverges hag (hcov 0 o rfl) hd
      exact Or.inl ⟨[], f, args, results, os, fr, m, vals, rfl, .nil, hargs, hdv⟩
    | core h' =>
      cases h' with
      | let₁ harg hrest =>
        obtain ⟨ws, fr', hv, hw, hone⟩ :=
          Op.exec_of_eval_toTm hsigs hag (hcov 0 o rfl) (hcalls 0 o rfl) harg
        subst hv
        obtain ⟨hfr, hnd⟩ := hfresh 0 o rfl
        have hag' : (sc.push o.defs).Agrees (Semantics.extend env (packValues ws)) fr' :=
          (hag.frame (fun r hr => get_writeAll_of_not_mem hw (fun hx => hfr r hx hr))).push
            (readAll_writeAll hw hnd)
        rcases ih hag' (fun i o' ho' => hcov (i + 1) o' (by simpa using ho'))
            (fun i o' ho' => hfresh (i + 1) o' (by simpa using ho'))
            (fun i o' ho' => hcalls (i + 1) o' (by simpa using ho')) hrest with
          ⟨pre, f, args, results, post, fr₂, m₂, vals, heq, hpre, hargs, hdv⟩ |
          ⟨fr₂, m₂, env₂, hexec, hag₂, hsh, hK⟩
        · exact Or.inl ⟨o :: pre, f, args, results, post, fr₂, m₂, vals, by rw [heq]; rfl,
            hone.append hpre, hargs, hdv⟩
        · refine Or.inr ⟨fr₂, m₂, env₂, hone.append hexec, hag₂, ?_, hK⟩
          intro i
          have hsh' := hsh (i + 1)
          rw [List.length_cons, show i + (os.length + 1) = i + 1 + os.length by omega]
          simpa using hsh'

/-- A diverging RTL configuration sitting at the region of its own block. -/
def RegionDiv (sigs : List Signature) (oracle : CallOracle) (div : DivOracle) (fn : Func R)
    (l : Label) (fr : Frame R) (m : Memory) : Prop :=
  ∃ (sc : Scope R) (fuel : Nat) (b : Block R) (env : Semantics.Env Word),
    fn.block? l = some b ∧ EnterOkSem fn sc l ∧
    fn.blocks.length - fn.digraph.domDepth l ≤ fuel ∧
    (sc.push b.params).Agrees env fr ∧
    Semantics.External.Diverges (Opcode.step (sigs := sigs) oracle) (Opcode.divergent div)
      (.region env (blockRegion sigs fuel fn sc l) m)

/-- A diverging RTL configuration sitting at the `cfg` loop that is about to
enter its block. -/
def FollowDiv (sigs : List Signature) (oracle : CallOracle) (div : DivOracle) (fn : Func R)
    (t : Label) (fr : Frame R) (m : Memory) : Prop :=
  ∃ (sc : Scope R) (fuel : Nat) (l : Label) (b bt : Block R) (env₂ : Semantics.Env Word)
    (vals : List Word) (j : Nat),
    fn.block? l = some b ∧ EnterOkSem fn sc l ∧
    fn.blocks.length - fn.digraph.domDepth l ≤ fuel + 1 ∧
    (fn.domChildren (some l))[j]? = some t ∧ fn.block? t = some bt ∧
    fr.readAll bt.params = some vals ∧ (blockScope fn sc l b).Agrees env₂ fr ∧
    Semantics.External.Diverges (Opcode.step (sigs := sigs) oracle) (Opcode.divergent div)
      (.follow env₂ (fun i : Fin (fn.domChildren (some l)).length =>
        blockRegion sigs fuel fn (blockScope fn sc l b)
          ((fn.domChildren (some l))[i.val]'i.isLt)) j (packValues vals) m)

/-- A diverging RTL configuration sitting at the outermost `cfg` loop. -/
def RootDiv (sigs : List Signature) (oracle : CallOracle) (div : DivOracle) (fn : Func R)
    (le : Label) (fr : Frame R) (m : Memory) : Prop :=
  ∃ (b : Block R) (env : Semantics.Env Word) (vals : List Word),
    le = fn.entry ∧ fn.block? fn.entry = some b ∧ fr.readAll b.params = some vals ∧
    Semantics.External.Diverges (Opcode.step (sigs := sigs) oracle) (Opcode.divergent div)
      (.follow env (fun _ : Fin 1 =>
        blockRegion sigs fn.blocks.length fn ⟨[], [(none, 1)]⟩ fn.entry)
        0 (packValues vals) m)

/-- The configurations the translated region's divergence localises at, possibly
after finitely many transfers. This is the relation the coinduction uses. -/
def DivWitness (sigs : List Signature) (oracle : CallOracle) (div : DivOracle) (fn : Func R)
    (c : DivConfig R) : Prop :=
  ∃ d, Relation.ReflTransGen (Transfers oracle fn) c d ∧
    (RegionDiv sigs oracle div fn d.label d.frame d.mem ∨
      FollowDiv sigs oracle div fn d.label d.frame d.mem ∨
      RootDiv sigs oracle div fn d.label d.frame d.mem)

/-- **A diverging block region unfolds one step of the RTL divergence.** -/
theorem divStep_of_regionDiv {sigs : List Signature} {oracle : CallOracle} {div : DivOracle}
    {fn : Func R} (hwf : fn.WellFormed) (hsigs : CallOracle.MatchesSigs oracle sigs)
    (hcalls : fn.CallsMatch sigs) {l : Label} {fr : Frame R} {m : Memory}
    (h : RegionDiv sigs oracle div fn l fr m) :
    Func.DivStep oracle div fn (DivWitness sigs oracle div fn) ⟨l, fr, m⟩ := by
  obtain ⟨sc, fuel, b, env, hb, hok, hfuel, hag, hdiv⟩ := h
  cases fuel with
  | zero => exact absurd hfuel (by have := domDepth_lt hwf.sig hok.base.reachable; omega)
  | succ fuel =>
    rw [blockRegion_succ hb] at hdiv
    rcases opsRegion_divStep hsigs b.ops hag (block_ops_covers hwf hb hok)
        (block_ops_fresh hwf hb hok) (block_ops_calls hcalls hb) hdiv with
      ⟨pre, f, args, results, post, fr₁, m₁, vals, heq, hpre, hargs, hdv⟩ |
      ⟨fr₁, m₁, env₂, hops, hag₂, _, hK⟩
    · exact .call hb heq hpre hargs hdv
    · have hag₂' : (blockScope fn sc l b).Agrees env₂ fr₁ := hag₂
      cases hK.unfold with
      | core h' =>
        cases h' with
        | cfg_entry rest => exact absurd rest Term.toRegion_not_diverges
        | cfg_follow hentry rest =>
          rcases term_back hwf hb hok hag₂' hops hentry with
            ⟨vs, hlbl, hv, hfin⟩ | ⟨hlbl, hv, hfin⟩ |
            ⟨t, bt, fr₁', fr₂, vals, hbt, hreach, hdsome, hlbl, hv, hwrite, hag', htr⟩
          · exfalso
            have hlt := follow_diverges_lt rest
            rw [hlbl, blockScope_depth] at hlt
            omega
          · exfalso
            have hlt := follow_diverges_lt rest
            rw [hlbl, blockScope_depth] at hlt
            omega
          · by_cases hid : fn.digraph.idom t = some l
            · obtain ⟨j, hjlt, hjget, hjeq⟩ := jumpLabel_blockScope_child (sc := sc) (b := b) hid
              obtain ⟨hagc, hread⟩ := agrees_child hwf hb hok hbt hid hwrite hag'
              refine htr.divStep ⟨_, Relation.ReflTransGen.refl, Or.inr (Or.inl ?_)⟩
              exact ⟨sc, fuel, l, b, bt, env₂, vals, j, hb, hok, hfuel, hjget, hbt, hread, hagc,
                by rw [hlbl, hjeq, hv] at rest; exact rest⟩
            · exfalso
              have hdsome' : (Scope.labelDepth sc.labels (fn.digraph.idom t)).isSome := by
                rwa [labelDepth_blockScope_outer hid] at hdsome
              have hjeq :=
                jumpLabel_blockScope_outer (sc := sc) (b := b) hok.base.labelsOk hid hdsome'
              have hlt := follow_diverges_lt rest
              rw [hlbl, hjeq] at hlt
              omega

/-- **A diverging `cfg` loop unfolds one step of the RTL divergence.** -/
theorem divStep_of_followDiv {sigs : List Signature} {oracle : CallOracle} {div : DivOracle}
    {fn : Func R} (hwf : fn.WellFormed) (hsigs : CallOracle.MatchesSigs oracle sigs)
    (hcalls : fn.CallsMatch sigs) {t : Label} {fr : Frame R} {m : Memory}
    (h : FollowDiv sigs oracle div fn t fr m) :
    Func.DivStep oracle div fn (DivWitness sigs oracle div fn) ⟨t, fr, m⟩ := by
  obtain ⟨sc, fuel, l, b, bt, env₂, vals, j, hb, hok, hfuel, hjget, hbt, hread, hagc, hdiv⟩ := h
  have hjlt : j < (fn.domChildren (some l)).length := (List.getElem?_eq_some_iff.mp hjget).1
  have hjt : (fn.domChildren (some l))[j]'hjlt = t :=
    Option.some.inj ((List.getElem?_eq_getElem hjlt).symm.trans hjget)
  subst hjt
  have hid : fn.digraph.idom ((fn.domChildren (some l))[j]'hjlt) = some l :=
    Graph.Digraph.mem_domTreeChildren_iff.mp (List.getElem_mem hjlt)
  have hfuelc : fn.blocks.length
      - fn.digraph.domDepth ((fn.domChildren (some l))[j]'hjlt) ≤ fuel := by
    have := Graph.Digraph.domDepth_lt_of_idom hid
    omega
  cases hdiv.unfold with
  | core h' =>
    cases h' with
    | follow_body inside rest =>
      refine divStep_of_regionDiv hwf hsigs hcalls ?_
      exact ⟨blockScope fn sc l b, fuel, bt, Semantics.extend env₂ (packValues vals), hbt,
        enterOkSem_child hb hok hid, hfuelc, hagc.push hread, rest⟩
    | follow_next inside head rest =>
      have hexit := entersBack hwf hsigs hcalls fuel (blockScope fn sc l b)
        ((fn.domChildren (some l))[j]'hjlt) bt env₂
        (Semantics.extend env₂ (packValues vals)) fr m _ _ _ hbt
        (enterOkSem_child hb hok hid) hfuelc (fun _ => rfl) (hagc.push hread) head
      rcases hexit with ⟨vs, d, hlbl, hv, hrt, hfin⟩ | ⟨d, hlbl, hv, hrt, hfin⟩ |
        ⟨t', bt', fr₁', fr₂', vals', hbt', hreach', hdsome', hlbl, hv, hwrite', hag'', htg⟩
      · exfalso
        have hlt := follow_diverges_lt rest
        rw [hlbl, blockScope_depth] at hlt
        omega
      · exfalso
        have hlt := follow_diverges_lt rest
        rw [hlbl, blockScope_depth] at hlt
        omega
      · by_cases hid' : fn.digraph.idom t' = some l
        · obtain ⟨j', hjlt', hjget', hjeq'⟩ := jumpLabel_blockScope_child (sc := sc) (b := b) hid'
          obtain ⟨hagc', hread'⟩ := agrees_child hwf hb hok hbt' hid' hwrite' hag''
          obtain ⟨e, hce, hed⟩ := Relation.TransGen.head'_iff.mp htg
          refine hce.divStep ⟨_, hed, Or.inr (Or.inl ?_)⟩
          exact ⟨sc, fuel, l, b, bt', env₂, vals', j', hb, hok, hfuel, hjget', hbt', hread',
            hagc', by rw [hlbl, hjeq', hv] at rest; exact rest⟩
        · exfalso
          have hdsome'' : (Scope.labelDepth sc.labels (fn.digraph.idom t')).isSome := by
            rwa [labelDepth_blockScope_outer hid'] at hdsome'
          have hjeq :=
            jumpLabel_blockScope_outer (sc := sc) (b := b) hok.base.labelsOk hid' hdsome''
          have hlt := follow_diverges_lt rest
          rw [hlbl, hjeq] at hlt
          omega

/-- **A diverging outermost `cfg` unfolds one step of the RTL divergence.** -/
theorem divStep_of_rootDiv {sigs : List Signature} {oracle : CallOracle} {div : DivOracle}
    {fn : Func R} (hwf : fn.WellFormed) (hsigs : CallOracle.MatchesSigs oracle sigs)
    (hcalls : fn.CallsMatch sigs) {le : Label} {fr : Frame R} {m : Memory}
    (h : RootDiv sigs oracle div fn le fr m) :
    Func.DivStep oracle div fn (DivWitness sigs oracle div fn) ⟨le, fr, m⟩ := by
  obtain ⟨b, env, vals, hlab, hb, hread, hdiv⟩ := h
  subst hlab
  cases hdiv.unfold with
  | core h' =>
    cases h' with
    | follow_body inside rest =>
      refine divStep_of_regionDiv hwf hsigs hcalls ?_
      exact ⟨⟨[], [(none, 1)]⟩, fn.blocks.length, b, Semantics.extend env (packValues vals),
        hb, enterOkSem_root, by omega, agrees_root.push hread, rest⟩
    | follow_next inside head rest =>
      have hexit := entersBack hwf hsigs hcalls fn.blocks.length ⟨[], [(none, 1)]⟩ fn.entry b
        env (Semantics.extend env (packValues vals)) fr m _ _ _ hb enterOkSem_root (by omega)
        (fun _ => rfl) (agrees_root.push hread) head
      rcases hexit with ⟨vs, d, hlbl, hv, hrt, hfin⟩ | ⟨d, hlbl, hv, hrt, hfin⟩ |
        ⟨t', bt', fr₁', fr₂', vals', hbt', hreach', hdsome', hlbl, hv, hwrite', hag'', htg⟩
      · exfalso
        have hlt := follow_diverges_lt rest
        rw [hlbl] at hlt
        simp [Scope.depth] at hlt
      · exfalso
        have hlt := follow_diverges_lt rest
        rw [hlbl] at hlt
        simp [Scope.depth] at hlt
      · have hid : fn.digraph.idom t' = none := by
          cases hidt : fn.digraph.idom t' with
          | none => rfl
          | some a =>
            rw [hidt] at hdsome'
            simp [Scope.labelDepth] at hdsome'
        have ht : t' = fn.entry := by
          by_contra hne
          obtain ⟨a, ha, -, -⟩ := Graph.Digraph.idom_spec hreach' hne
          rw [hid] at ha
          exact absurd ha (by simp)
        subst ht
        obtain ⟨e, hce, hed⟩ := Relation.TransGen.head'_iff.mp htg
        refine hce.divStep ⟨_, hed, Or.inr (Or.inr ?_)⟩
        exact ⟨bt', env, vals', rfl, hbt',
          readAll_writeAll hwrite' (params_nodup hwf.singleAssignment hbt'),
          by rw [hlbl, jumpLabel_root, hv] at rest; exact rest⟩

/-- **Divergence is reflected.** An externally divergent run of the translated
region — one whose only infinite behaviour is a call the `DivOracle` says runs
forever, which is the only way RTL can diverge — is an infinite run of the
function.

Only this direction is proved. The converse, that an infinite RTL run makes the
region diverge, is not: `Semantics.Diverges` at a `cfg`'s `Follow` demands that
the loop at *that* level run forever, while an infinite RTL run may instead
localise at an inner or an outer `cfg`, and deciding which requires knowing
whether the run ever leaves the subtree the block dominates. That is a classical
fact about the infinite run and not something the coinduction can produce from
one unfolding, so it would need a separate development. The hypotheses are those
of `toLambdaSSA_eval_iff`. -/
theorem toLambdaSSA_diverges_of_external {sigs : List Signature} {oracle : CallOracle}
    {div : DivOracle} {fn : Func R} (h : fn.WellFormed)
    (hsigs : CallOracle.MatchesSigs oracle sigs) (hcalls : fn.CallsMatch sigs)
    {args : List Word} {b : Block R} {fr : Frame R} (hb : fn.block? fn.entry = some b)
    (hfr : Frame.empty.writeAll b.params args = some fr)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m : Memory}
    (hdiv : Semantics.External.Diverges (Opcode.step (sigs := sigs) oracle)
      (Opcode.divergent div) (.region env (toLambdaSSA sigs fn) m)) :
    Func.Diverges oracle div fn ⟨fn.entry, fr, m⟩ := by
  refine Func.Diverges.coinduct (DivWitness sigs oracle div fn) ?_ ?_
  · rintro c ⟨d, hrt, hd⟩
    rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨e, hce, hed⟩
    · obtain ⟨cl, cf, cm⟩ := c
      rcases hd with hr | hf | hro
      · exact divStep_of_regionDiv h hsigs hcalls hr
      · exact divStep_of_followDiv h hsigs hcalls hf
      · exact divStep_of_rootDiv h hsigs hcalls hro
    · exact hce.divStep ⟨d, hed, hd⟩
  · refine ⟨⟨fn.entry, fr, m⟩, Relation.ReflTransGen.refl, Or.inr (Or.inr ?_)⟩
    cases hdiv.unfold with
    | core h' =>
      cases h' with
      | cfg_entry rest => exact absurd rest (br_not_diverges trivial)
      | cfg_follow hentry rest =>
        obtain ⟨rfl, harg⟩ := region_eval_br_inv hentry
        obtain ⟨hv, hm⟩ := eval_var_inv harg
        rw [hm, hv, henv] at rest
        exact ⟨b, env, args, rfl, hb,
          readAll_writeAll hfr (params_nodup h.singleAssignment hb), rest⟩

/-- **Whole-program behaviour is preserved.** Combining `toLambdaSSA_eval_iff`
with the bridge of `Machine/RTL/BigStep.lean`, a run of the program from `f`
returns exactly what the translated region produces at its return label. The two
extra hypotheses are those of `toLambdaSSA_eval_iff`. -/
theorem toLambdaSSA_behaves_returned_iff {sigs : List Signature} {p : Prog R}
    {f : FuncId} {fn : Func R} (hfn : p.func? f = some fn) (h : fn.WellFormed)
    (hsigs : CallOracle.MatchesSigs p.oracle sigs) (hcalls : fn.CallsMatch sigs)
    {b : Block R} {fr : Frame R} (hb : fn.block? fn.entry = some b)
    {args vs : List Word} (hfr : Frame.empty.writeAll b.params args = some fr)
    {env : Semantics.Env Word} (henv : env 0 = packValues args) {m m' : Memory} :
    Semantics.Region.Eval (Opcode.step (sigs := sigs) p.oracle) env (toLambdaSSA sigs fn) m
        0 (packValues vs) m' ↔
      Behaves p ⟨⟨f, fn.entry, 0⟩, fr, [], m⟩ (.returned vs m') := by
  rw [← Func.exec_returned_iff_behaves hfn hb hfr]
  constructor
  · intro heval
    rcases (toLambdaSSA_eval_iff h hsigs hcalls hb hfr henv).mp heval with
      ⟨-, vs', hv, hexec⟩ | ⟨hlbl, -, -⟩
    · obtain rfl : vs = vs' := packValues_injective hv
      exact hexec
    · exact absurd hlbl (by simp)
  · intro hexec
    exact (toLambdaSSA_eval_iff h hsigs hcalls hb hfr henv).mpr (Or.inl ⟨rfl, vs, rfl, hexec⟩)

end Silmaril.Machine.RTL.SSA
