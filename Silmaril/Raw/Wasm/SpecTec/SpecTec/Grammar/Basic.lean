module

public import Silmaril.Encoding.Lattice
public import Silmaril.Wasm.Binary.Basic

/-!
# Attribute grammars over bytes

Phase 3 of `docs/projects/spectec/README.md`.  This file is deliberately independent
of `Silmaril.SpecTec.IL`: it is a generic framework of attribute grammars whose
terminals are bytes, set up so that SpecTec's `GramD`/`Sym` construct
(`spectec/src/il/ast.ml:101-110,154`) will be one instance of it, and so that
the hand-written binary relations of `Silmaril/Wasm/Binary/Basic.lean` can be
compared against a grammar in the framework.

A symbol denotes an `EncRel (List UInt8) α` (`Silmaril/Encoding/Relation.lean`),
so the whole vocabulary of `Silmaril/Encoding/Lattice.lean` — the complete
lattice order, `Functional`, `mapPartial` — applies verbatim.

## Design: where do the attributes live?

SpecTec answers this for us.  In `spectec/src/il/valid.ml:589-595`, `EpsG`,
`SeqG` and `AltG` all have type `TupT []`: **a sequence has no attribute of its
own**.  Values flow through `AttrG (e, g)` (`ast.ml:110`), which
`valid.ml:606-609` checks with `~side:`Lhs`` — it is a *binding pattern*, not a
computation — and the value of a whole production is a separate expression,
`ProdD (quants, sym, exp, prems)` (`ast.ml:154`, `valid.ml:753-757`), evaluated
after the premises.

So the attribute-producing data is a function, and the question is only where
to hang it.  The two candidates named in the design brief:

* *a function parameter on `seq`/`nt`* — a `seq` would combine its factors'
  attributes with some `f : List α → Option α`.  This is wrong on SpecTec's own
  evidence: `SeqG` is `()`-typed, and the combination that actually happens is
  always the same one (collect the bindings, in order).
* *a separate layer* — chosen here, in the two pieces SpecTec itself uses:
  1. `Attr α` below is the monoid in which a derivation accumulates bindings,
     with `Attr.ofByte` for terminals.  `Sym.seq` is its `app`, `Sym.eps` its
     `nil`.  The canonical instance is `Attr.list f`, "the list of what was
     bound, left to right", which is exactly SpecTec's `()`-typed `SeqG` plus
     an environment; `Attr.bytes` recovers the consumed byte string.
  2. `Sym.attr f g` is `AttrG`, restated as a *partial* map `f : α → Option α`:
     total where `AttrG` is a variable pattern, partial where it is a
     destructuring pattern or where `ProdD`'s `prems` impose a side condition.
     Its denotation is `EncRel.mapPartial f`, so "this production's value is
     given by this expression" is literally the `mapPartial` of the expression's
     denotation, and a production of `GramD` is just a `Sym` headed by `attr`.

The cost of (2) is that `Sym` carries a function field, so it has no
`DecidableEq` and no `Repr`.  That is the right trade here — this is a semantic
framework, and nothing downstream decides equality of grammars.  The escape
hatch, if a decidable syntax is ever wanted, is to defunctionalize: replace
`f : α → Option α` by an index into a table of actions carried by the
`Grammar`.  `Inhabited` is still derived (`Sym` is a nested inductive, so
`deriving DecidableEq` would not apply to it anyway).

## Correspondence with `IL.Sym`

| this file | `IL.Sym` | `spectec/src/il/ast.ml` |
| --- | --- | --- |
| `Sym.eps` | `epsG` | 105 |
| `Sym.byte b` | `numG n` (a byte terminal) | 103 |
| `Sym.range lo hi` | `rangeG (numG lo) (numG hi)` | 108 |
| `Sym.bytes bs` | `textG t` (a string terminal) | 104 |
| `Sym.nt x` | `varG x []` | 102 |
| `Sym.seq gs` | `seqG gs` | 106 |
| `Sym.alt gs` | `altG gs` | 107 |
| `Sym.star g` | `iterG g (List, _)` | 109, 18 |
| `Sym.plus g` | `iterG g (List1, _)` | 109, 19 |
| `Sym.opt g` | `iterG g (Opt, _)` | 109, 17 |
| `Sym.count g n` | `iterG g (ListN e _, _)` with `e` evaluating to `n` | 109, 20 |
| `Sym.attr f g` | `attrG e g` | 110 |

`IL.Sym.varG`'s argument list, `IL.Sym.numG`'s use as a Unicode scalar bound in
the UTF-8 grammar, and `rangeG` over non-terminal operands are the three places
where the IL is wider than this framework; parameterized nonterminals are
accommodated by letting `N` be a pair of a grammar identifier and its
arguments, and a scalar-valued `rangeG` belongs to a UTF-8 layer over code
points rather than to the byte grammar.

## What is proved here

* `denoteAt`/`denote`: a step-indexed least fixpoint, monotone in the index
  (`denoteAt_mono`) with `denote` its supremum (`denote_eq_iSup`), least among
  the prefixpoints of the one-step map (`denote_le_of_step`).
* Compositionality: `denote_seq` (append), `denote_alt` (lattice join),
  `denote_star` (Kleene closure), and one equation per constructor.
* Monotonicity in the grammar: `denote_mono_prods`.
* Sufficient conditions for `Functional`: `PrefixFree`, `Unambiguous`,
  `Separated`, closed under `Unambiguous.appendRel`/`appendAll` (every `seq`
  factor prefix-free) and `Unambiguous.supList` (every alternative separated),
  fed by a decidable syntactic leading-byte analysis `leadRange?`/`rangeDisjoint`
  /`altSeparated` (`separated_of_leadRange`, `unambiguous_denote_seq`,
  `unambiguous_denote_alt`, `unambiguous_denote_nt`, `functional_denote_star`).
* LEB128 as a worked instance: `lebGram`, the agreement theorem
  `denote_leb_nt_iff : denote lebGram (.nt W) bs [m] ↔ Wasm.Binary.UN W bs m`,
  the decidable check `altSeparated_lebProds`, `unambiguous_leb`, and
  `un_prefixFree`, which derives prefix-freeness of the hand-written `UN` from
  the framework's generic conditions.

## Not here

A generic decoder for a deterministic subclass (Brzozowski derivatives of a
`Sym`, with `denote` as its specification) and the UTF-8 layer — a carrier
change `EncRel (List Char) α → EncRel (List UInt8) α` in the sense of
`EncRel.push` — are the next step and are out of scope for this file.
-/

@[expose] public section

namespace Silmaril.SpecTec.Grammar

open Silmaril

/-- The terminals of the framework: byte strings, as in
`Silmaril/Wasm/Binary/Basic.lean`. -/
abbrev Bytes := List UInt8

/-! ## The attribute algebra -/

/-- The algebra in which a derivation accumulates its attribute.

`nil`/`app` is a monoid — `Sym.eps` denotes `nil` and `Sym.seq` denotes the
`app` of its factors, so associativity and unitality are exactly what makes
`Sym.seq` associative and `Sym.eps` its unit — and `ofByte` says what a
terminal contributes.  Attributes proper are then cut out of this monoid by
`Sym.attr`, whose action is an arbitrary partial map. -/
structure Attr (α : Type) where
  /-- The attribute of the empty derivation (SpecTec's `EpsG : TupT []`). -/
  nil : α
  /-- The attribute of a concatenation (SpecTec's `SeqG`). -/
  app : α → α → α
  /-- The attribute contributed by a terminal byte. -/
  ofByte : UInt8 → α
  /-- `nil` is a left unit for `app`. -/
  nil_app : ∀ a, app nil a = a
  /-- `nil` is a right unit for `app`. -/
  app_nil : ∀ a, app a nil = a
  /-- `app` is associative. -/
  app_assoc : ∀ a b c, app (app a b) c = app a (app b c)

namespace Attr

variable {α β : Type}

/-- The attribute of a literal byte string: the `app`-fold of its bytes. -/
def ofBytes (A : Attr α) (bs : Bytes) : α :=
  bs.foldr (fun b a => A.app (A.ofByte b) a) A.nil

/-- The canonical attribute algebra: a derivation accumulates the list of what
its terminals contributed, left to right.  This is SpecTec's `()`-typed `SeqG`
together with the environment its `AttrG` bindings build. -/
def list (f : UInt8 → β) : Attr (List β) where
  nil := []
  app := (· ++ ·)
  ofByte b := [f b]
  nil_app := List.nil_append
  app_nil := List.append_nil
  app_assoc a b c := (List.append_assoc a b c)

/-- The free attribute algebra: the attribute is the consumed byte string, so
`denote` becomes the language of the grammar together with its own spelling. -/
def bytes : Attr Bytes := Attr.list id

/-- The empty literal contributes the unit attribute. -/
@[simp] theorem ofBytes_nil (A : Attr α) : A.ofBytes [] = A.nil := rfl

/-- `ofBytes` is the `app`-fold of the literal's bytes. -/
@[simp] theorem ofBytes_cons (A : Attr α) (b : UInt8) (bs : Bytes) :
    A.ofBytes (b :: bs) = A.app (A.ofByte b) (A.ofBytes bs) := rfl

end Attr

/-! ## Syntax -/

/-- A grammar symbol over byte terminals, with nonterminals drawn from `N` and
attributes from `α`.  See the table in the module docstring for the
correspondence with `IL.Sym` (`spectec/src/il/ast.ml:101-110`). -/
inductive Sym (N : Type) (α : Type) where
  /-- `EpsG` (`ast.ml:105`): the empty byte string, attribute `Attr.nil`. -/
  | eps
  /-- `NumG n` used as a byte terminal (`ast.ml:103`). -/
  | byte (b : UInt8)
  /-- `RangeG (NumG lo, NumG hi)` (`ast.ml:108`): one byte in `[lo, hi]`. -/
  | range (lo hi : UInt8)
  /-- `TextG t` (`ast.ml:104`): a literal byte string. -/
  | bytes (bs : List UInt8)
  /-- `VarG (x, [])` (`ast.ml:102`): a nonterminal. -/
  | nt (n : N)
  /-- `SeqG gs` (`ast.ml:106`): concatenation. -/
  | seq (gs : List (Sym N α))
  /-- `AltG gs` (`ast.ml:107`): alternation. -/
  | alt (gs : List (Sym N α))
  /-- `IterG (g, (List, _))` (`ast.ml:109`, `ast.ml:18`). -/
  | star (g : Sym N α)
  /-- `IterG (g, (List1, _))` (`ast.ml:109`, `ast.ml:19`). -/
  | plus (g : Sym N α)
  /-- `IterG (g, (Opt, _))` (`ast.ml:109`, `ast.ml:17`). -/
  | opt (g : Sym N α)
  /-- `IterG (g, (ListN e _, _))` (`ast.ml:109`, `ast.ml:20`) with `e` already
  evaluated to `n`. -/
  | count (g : Sym N α) (n : Nat)
  /-- `AttrG (e, g)` (`ast.ml:110`): parse `g`, then compute this production's
  value with `f`.  `f a = none` is a failed side condition — a `ProdD` premise
  (`ast.ml:154`) or a `AttrG` pattern that does not match. -/
  | attr (f : α → Option α) (g : Sym N α)
  deriving Inhabited

/-- A grammar: the attribute algebra, and the alternative productions of each
nonterminal.  This is `GramD (x, ps, t, prods)` (`spectec/src/il/ast.ml:154`,
`valid.ml:797-801`) with the parameters `ps` already instantiated into `N` and
each `ProdD (qs, g, e, prems)` presented as `Sym.attr` over `g`.

Named `Gram` after SpecTec's `GramD`, since `Grammar` is the namespace. -/
structure Gram (N : Type) (α : Type) where
  /-- The attribute algebra. -/
  alg : Attr α
  /-- The productions of each nonterminal, as alternatives. -/
  prods : N → List (Sym N α)

/-! ## Combinators on encoding relations -/

section Combinators

variable {σ α : Type}

/-- The empty byte string with attribute `a₀`. -/
def epsRel (a₀ : α) : EncRel Bytes α := fun bs a => bs = [] ∧ a = a₀

/-- A single byte terminal. -/
def byteRel (A : Attr α) (b : UInt8) : EncRel Bytes α :=
  fun bs a => bs = [b] ∧ a = A.ofByte b

/-- One byte in the inclusive interval `[lo, hi]`. -/
def rangeRel (A : Attr α) (lo hi : UInt8) : EncRel Bytes α :=
  fun bs a => ∃ b, lo ≤ b ∧ b ≤ hi ∧ bs = [b] ∧ a = A.ofByte b

/-- A literal byte string. -/
def bytesRel (A : Attr α) (l : Bytes) : EncRel Bytes α :=
  fun bs a => bs = l ∧ a = A.ofBytes l

/-- Concatenation of two encoding relations: the byte strings append and the
attributes multiply in `A`.  This is the operation `Sym.seq` denotes. -/
def appendRel (A : Attr α) (E F : EncRel Bytes α) : EncRel Bytes α :=
  fun bs a => ∃ b₁ a₁ b₂ a₂, E b₁ a₁ ∧ F b₂ a₂ ∧ bs = b₁ ++ b₂ ∧ a = A.app a₁ a₂

/-- Concatenation of a list of encoding relations. -/
def appendAll (A : Attr α) : List (EncRel Bytes α) → EncRel Bytes α
  | [] => epsRel A.nil
  | E :: Es => appendRel A E (appendAll A Es)

/-- The supremum of a list of encoding relations, i.e. the lattice join; this
is the operation `Sym.alt` denotes. -/
def supList : List (EncRel σ α) → EncRel σ α
  | [] => ⊥
  | E :: Es => E ⊔ supList Es

/-- `E` repeated exactly `k` times. -/
def powRel (A : Attr α) (E : EncRel Bytes α) : Nat → EncRel Bytes α
  | 0 => epsRel A.nil
  | k + 1 => appendRel A E (powRel A E k)

/-- The Kleene closure of `E`: any finite number of repetitions. -/
def kleene (A : Attr α) (E : EncRel Bytes α) : EncRel Bytes α := ⨆ k, powRel A E k

end Combinators

/-! ## Laws of the combinators

`appendRel` makes `EncRel Bytes α` a monoid with unit `epsRel A.nil`, and every
combinator is monotone for the lattice order of `Silmaril/Encoding/Lattice.lean`.
-/

section Laws

variable {σ α β : Type} {A : Attr α}

/-- The join of a list holds exactly when one of its members does. -/
@[simp] theorem supList_apply {Es : List (EncRel σ α)} {s : σ} {a : α} :
    supList Es s a ↔ ∃ E ∈ Es, E s a := by
  induction Es with
  | nil => simp [supList]
  | cons E Es ih => simp [supList, ih, List.mem_cons, exists_eq_or_imp]

/-- The Kleene closure holds exactly at some finite power. -/
@[simp] theorem kleene_apply {E : EncRel Bytes α} {bs : Bytes} {a : α} :
    kleene A E bs a ↔ ∃ k, powRel A E k bs a := by
  simp [kleene]

/-- `epsRel A.nil` is a left unit for concatenation. -/
theorem appendRel_eps_left (E : EncRel Bytes α) :
    appendRel A (epsRel A.nil) E = E := by
  ext bs a
  constructor
  · rintro ⟨b₁, a₁, b₂, a₂, ⟨rfl, rfl⟩, hF, rfl, rfl⟩
    simpa [A.nil_app] using hF
  · intro h
    exact ⟨[], A.nil, bs, a, ⟨rfl, rfl⟩, h, rfl, (A.nil_app a).symm⟩

/-- `epsRel A.nil` is a right unit for concatenation. -/
theorem appendRel_eps_right (E : EncRel Bytes α) :
    appendRel A E (epsRel A.nil) = E := by
  ext bs a
  constructor
  · rintro ⟨b₁, a₁, b₂, a₂, hE, ⟨rfl, rfl⟩, rfl, rfl⟩
    simpa [A.app_nil] using hE
  · intro h
    exact ⟨bs, a, [], A.nil, h, ⟨rfl, rfl⟩, (List.append_nil bs).symm, (A.app_nil a).symm⟩

/-- Concatenation is associative, so `Sym.seq` is unambiguous as a tree. -/
theorem appendRel_assoc (E F H : EncRel Bytes α) :
    appendRel A (appendRel A E F) H = appendRel A E (appendRel A F H) := by
  ext bs a
  constructor
  · rintro ⟨_, _, b₃, a₃, ⟨b₁, a₁, b₂, a₂, hE, hF, rfl, rfl⟩, hH, rfl, rfl⟩
    exact ⟨b₁, a₁, b₂ ++ b₃, A.app a₂ a₃, hE, ⟨b₂, a₂, b₃, a₃, hF, hH, rfl, rfl⟩,
      List.append_assoc b₁ b₂ b₃, A.app_assoc a₁ a₂ a₃⟩
  · rintro ⟨b₁, a₁, _, _, hE, ⟨b₂, a₂, b₃, a₃, hF, hH, rfl, rfl⟩, rfl, rfl⟩
    exact ⟨b₁ ++ b₂, A.app a₁ a₂, b₃, a₃, ⟨b₁, a₁, b₂, a₂, hE, hF, rfl, rfl⟩, hH,
      (List.append_assoc b₁ b₂ b₃).symm, (A.app_assoc a₁ a₂ a₃).symm⟩

/-- The empty concatenation is the empty byte string. -/
@[simp] theorem appendAll_nil : appendAll A [] = epsRel A.nil := rfl

/-- `appendAll` is the right fold of `appendRel` over the factors. -/
@[simp] theorem appendAll_cons (E : EncRel Bytes α) (Es : List (EncRel Bytes α)) :
    appendAll A (E :: Es) = appendRel A E (appendAll A Es) := rfl

/-- A one-factor concatenation is that factor. -/
theorem appendAll_singleton (E : EncRel Bytes α) : appendAll A [E] = E :=
  appendRel_eps_right E

/-- `powRel` is `appendAll` of a constant list; in particular `Sym.count g k` is
`Sym.seq (List.replicate k g)`. -/
theorem powRel_eq_appendAll (E : EncRel Bytes α) (k : Nat) :
    powRel A E k = appendAll A (List.replicate k E) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [powRel, ih, List.replicate_succ]

/-- Concatenation is monotone in both factors. -/
theorem appendRel_mono {E E' F F' : EncRel Bytes α} (hE : E ≤ E') (hF : F ≤ F') :
    appendRel A E F ≤ appendRel A E' F' := by
  rintro bs a ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩
  exact ⟨b₁, a₁, b₂, a₂, hE _ _ h₁, hF _ _ h₂, rfl, rfl⟩

/-- `appendAll` is monotone in a pointwise-ordered family of factors. -/
theorem appendAll_map_mono {f f' : β → EncRel Bytes α} (h : ∀ x, f x ≤ f' x)
    (l : List β) : appendAll A (l.map f) ≤ appendAll A (l.map f') := by
  induction l with
  | nil => exact le_rfl
  | cons x l ih => exact appendRel_mono (h x) ih

/-- The join of a list is monotone in a pointwise-ordered family. -/
theorem supList_map_mono {f f' : β → EncRel σ α} (h : ∀ x, f x ≤ f' x) (l : List β) :
    supList (l.map f) ≤ supList (l.map f') := by
  intro s a ha
  simp only [supList_apply, List.mem_map] at ha ⊢
  obtain ⟨_, ⟨x, hx, rfl⟩, hv⟩ := ha
  exact ⟨f' x, ⟨x, hx, rfl⟩, h x _ _ hv⟩

/-- Each power is monotone. -/
theorem powRel_mono {E E' : EncRel Bytes α} (h : E ≤ E') (k : Nat) :
    powRel A E k ≤ powRel A E' k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact appendRel_mono h ih

/-- The Kleene closure is monotone. -/
theorem kleene_mono {E E' : EncRel Bytes α} (h : E ≤ E') : kleene A E ≤ kleene A E' := by
  intro bs a ha
  obtain ⟨k, hk⟩ := kleene_apply.mp ha
  exact kleene_apply.mpr ⟨k, powRel_mono h k _ _ hk⟩

/-- `EncRel.mapPartial` is monotone (`Sym.attr` is monotone). -/
theorem mapPartial_mono {f : α → Option β} {E E' : EncRel σ α} (h : E ≤ E') :
    EncRel.mapPartial f E ≤ EncRel.mapPartial f E' := by
  rintro s b ⟨a, ha, hf⟩
  exact ⟨a, h _ _ ha, hf⟩

/-- The Kleene closure is the least solution of `X = ε ⊔ E · X` above `epsRel`. -/
theorem kleene_unfold (E : EncRel Bytes α) :
    kleene A E = epsRel A.nil ⊔ appendRel A E (kleene A E) := by
  ext bs a
  simp only [kleene_apply, EncRel.sup_apply]
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact Or.inl hk
    | succ k =>
      obtain ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩ := hk
      exact Or.inr ⟨b₁, a₁, b₂, a₂, h₁, kleene_apply.mpr ⟨k, h₂⟩, rfl, rfl⟩
  · rintro (h | ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩)
    · exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := kleene_apply.mp h₂
      exact ⟨k + 1, ⟨b₁, a₁, b₂, a₂, h₁, hk, rfl, rfl⟩⟩

/-- A literal byte string is the concatenation of its bytes. -/
theorem bytesRel_eq_appendAll (l : Bytes) :
    bytesRel A l = appendAll A (l.map (byteRel A)) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    ext bs a
    simp only [List.map_cons, appendAll_cons, ← ih]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨[b], A.ofByte b, l, A.ofBytes l, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨b₁, a₁, b₂, a₂, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
      exact ⟨rfl, rfl⟩

end Laws

/-! ## Semantics

Nonterminals are recursive, so the denotation is a least fixpoint.  It is built
step-indexed: `step` is the one-step map, `denoteAt G n` is `step` iterated `n`
times from `⊥`, and `denote G` is their supremum.  The index bounds the depth of
the derivation tree, so it is the usual Kleene iteration of a monotone map on
the complete lattice `EncRel Bytes α`, and monotonicity in the index is free.
-/

section Semantics

variable {N α : Type}

/-- One unfolding step: interpret every constructor, using `D` for the
sub-symbols and for the productions of each nonterminal. -/
def step (G : Gram N α) (D : Sym N α → EncRel Bytes α) : Sym N α → EncRel Bytes α
  | .eps => epsRel G.alg.nil
  | .byte b => byteRel G.alg b
  | .range lo hi => rangeRel G.alg lo hi
  | .bytes l => bytesRel G.alg l
  | .nt x => supList ((G.prods x).map D)
  | .seq gs => appendAll G.alg (gs.map D)
  | .alt gs => supList (gs.map D)
  | .star g => kleene G.alg (D g)
  | .plus g => appendRel G.alg (D g) (kleene G.alg (D g))
  | .opt g => epsRel G.alg.nil ⊔ D g
  | .count g k => powRel G.alg (D g) k
  | .attr f g => EncRel.mapPartial f (D g)

/-- `step` iterated `n` times from `⊥`: the derivations of depth below `n`. -/
def denoteAt (G : Gram N α) : Nat → Sym N α → EncRel Bytes α
  | 0 => fun _ => ⊥
  | n + 1 => step G (denoteAt G n)

/-- The denotation of a symbol: the least fixpoint, as the supremum of the
step-indexed approximants. -/
def denote (G : Gram N α) (g : Sym N α) : EncRel Bytes α := ⨆ n, denoteAt G n g

/-- No derivation has depth zero. -/
@[simp] theorem denoteAt_zero (G : Gram N α) (g : Sym N α) : denoteAt G 0 g = ⊥ := rfl

/-- Each approximant is one `step` above its predecessor. -/
@[simp] theorem denoteAt_succ (G : Gram N α) (n : Nat) (g : Sym N α) :
    denoteAt G (n + 1) g = step G (denoteAt G n) g := rfl

/-- `denote` is the supremum of the approximants (the definition, restated as
the headline equation). -/
theorem denote_eq_iSup (G : Gram N α) (g : Sym N α) :
    denote G g = ⨆ n, denoteAt G n g := rfl

/-- A derivation is an approximant derivation at some finite index. -/
@[simp] theorem denote_apply {G : Gram N α} {g : Sym N α} {bs : Bytes} {a : α} :
    denote G g bs a ↔ ∃ n, denoteAt G n g bs a := by
  simp [denote]

/-- Every approximant lies below the denotation. -/
theorem denoteAt_le_denote (G : Gram N α) (n : Nat) (g : Sym N α) :
    denoteAt G n g ≤ denote G g := le_iSup (fun n => denoteAt G n g) n

/-- `step` is monotone in its argument, and in the production table: enlarging
either enlarges the result.  The two are proved together because the `nt` case
needs both at once. -/
theorem step_mono {A : Attr α} {P P' : N → List (Sym N α)}
    {D D' : Sym N α → EncRel Bytes α} (hP : ∀ x, ∀ g ∈ P x, g ∈ P' x)
    (hD : ∀ g, D g ≤ D' g) (g : Sym N α) :
    step ⟨A, P⟩ D g ≤ step ⟨A, P'⟩ D' g := by
  cases g with
  | eps => exact le_rfl
  | byte => exact le_rfl
  | range => exact le_rfl
  | bytes => exact le_rfl
  | nt x =>
    intro bs a ha
    simp only [step, supList_apply, List.mem_map] at ha ⊢
    obtain ⟨_, ⟨g, hg, rfl⟩, hv⟩ := ha
    exact ⟨D' g, ⟨g, hP x g hg, rfl⟩, hD g _ _ hv⟩
  | seq gs => exact appendAll_map_mono hD gs
  | alt gs => exact supList_map_mono hD gs
  | star g => exact kleene_mono (hD g)
  | plus g => exact appendRel_mono (hD g) (kleene_mono (hD g))
  | opt g => exact sup_le_sup_left (hD g) _
  | count g k => exact powRel_mono (hD g) k
  | attr f g => exact mapPartial_mono (hD g)

/-- Monotonicity of `step` in its argument alone. -/
theorem step_mono_arg (G : Gram N α) {D D' : Sym N α → EncRel Bytes α}
    (hD : ∀ g, D g ≤ D' g) (g : Sym N α) : step G D g ≤ step G D' g :=
  step_mono (P := G.prods) (fun _ _ h => h) hD g

/-- The approximants increase with the index. -/
theorem denoteAt_mono_succ (G : Gram N α) (n : Nat) (g : Sym N α) :
    denoteAt G n g ≤ denoteAt G (n + 1) g := by
  induction n generalizing g with
  | zero => exact bot_le
  | succ n ih => exact step_mono_arg G (fun g => ih g) g

/-- The approximants increase with the index. -/
theorem denoteAt_mono (G : Gram N α) {m n : Nat} (h : m ≤ n) (g : Sym N α) :
    denoteAt G m g ≤ denoteAt G n g := by
  induction n with
  | zero =>
    have hm : m = 0 := Nat.le_zero.mp h
    subst hm
    exact le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · exact le_trans (ih (Nat.lt_succ_iff.mp hm)) (denoteAt_mono_succ G n g)
    · have : m = n + 1 := Nat.le_antisymm h hm
      subst this
      exact le_rfl

/-- `denote` is the *least* prefixpoint of `step`: any `D` closed under one
unfolding step already contains every derivation. -/
theorem denote_le_of_step (G : Gram N α) {D : Sym N α → EncRel Bytes α}
    (h : ∀ g, step G D g ≤ D g) (g : Sym N α) : denote G g ≤ D g := by
  have key : ∀ n g, denoteAt G n g ≤ D g := by
    intro n
    induction n with
    | zero => intro g; exact bot_le
    | succ n ih => intro g; exact le_trans (step_mono_arg G ih g) (h g)
  intro bs a ha
  obtain ⟨n, hn⟩ := denote_apply.mp ha
  exact key n g _ _ hn

end Semantics

/-! ## Compositionality

Each constructor's denotation is the corresponding operation applied to the
denotations of its parts: `seq` is concatenation, `alt` is the lattice join,
`star` is the Kleene closure.  The one thing to check in each case is that the
operation commutes with the supremum over the index, which it does because a
derivation mentions only finitely many sub-derivations, so their indices have a
maximum.
-/

section Compositionality

variable {N α : Type} (G : Gram N α)

/-- A concatenation of denotations uses finitely many sub-derivations, so one
index serves for all of them. -/
theorem exists_index_appendAll (gs : List (Sym N α)) {bs : Bytes} {a : α}
    (h : appendAll G.alg (gs.map (denote G)) bs a) :
    ∃ n, appendAll G.alg (gs.map (denoteAt G n)) bs a := by
  induction gs generalizing bs a with
  | nil => exact ⟨0, h⟩
  | cons g gs ih =>
    obtain ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩ := h
    obtain ⟨n₁, hn₁⟩ := denote_apply.mp h₁
    obtain ⟨n₂, hn₂⟩ := ih h₂
    exact ⟨max n₁ n₂, b₁, a₁, b₂, a₂, denoteAt_mono G (le_max_left n₁ n₂) g _ _ hn₁,
      appendAll_map_mono (fun g => denoteAt_mono G (le_max_right n₁ n₂) g) gs _ _ hn₂,
      rfl, rfl⟩

/-- A join of denotations is witnessed at a single index. -/
theorem exists_index_supList (gs : List (Sym N α)) {bs : Bytes} {a : α}
    (h : supList (gs.map (denote G)) bs a) :
    ∃ n, supList (gs.map (denoteAt G n)) bs a := by
  simp only [supList_apply, List.mem_map] at h ⊢
  obtain ⟨_, ⟨g, hg, rfl⟩, hv⟩ := h
  obtain ⟨n, hn⟩ := denote_apply.mp hv
  exact ⟨n, denoteAt G n g, ⟨g, hg, rfl⟩, hn⟩

/-- A `k`-fold repetition of denotations is witnessed at a single index. -/
theorem exists_index_powRel (g : Sym N α) (k : Nat) {bs : Bytes} {a : α}
    (h : powRel G.alg (denote G g) k bs a) :
    ∃ n, powRel G.alg (denoteAt G n g) k bs a := by
  induction k generalizing bs a with
  | zero => exact ⟨0, h⟩
  | succ k ih =>
    obtain ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩ := h
    obtain ⟨n₁, hn₁⟩ := denote_apply.mp h₁
    obtain ⟨n₂, hn₂⟩ := ih h₂
    exact ⟨max n₁ n₂, b₁, a₁, b₂, a₂, denoteAt_mono G (le_max_left n₁ n₂) g _ _ hn₁,
      powRel_mono (denoteAt_mono G (le_max_right n₁ n₂) g) k _ _ hn₂, rfl, rfl⟩

/-- A Kleene-closure derivation is witnessed at a single index. -/
theorem exists_index_kleene (g : Sym N α) {bs : Bytes} {a : α}
    (h : kleene G.alg (denote G g) bs a) :
    ∃ n, kleene G.alg (denoteAt G n g) bs a := by
  obtain ⟨k, hk⟩ := kleene_apply.mp h
  obtain ⟨n, hn⟩ := exists_index_powRel G g k hk
  exact ⟨n, kleene_apply.mpr ⟨k, hn⟩⟩

/-- The workhorse behind every equation below: if the one-step image of `g` is
`F D`, with `F` monotone and commuting with the index supremum, then
`denote G g = F (denote G)`. -/
theorem denote_eq_of_step {g : Sym N α} (F : (Sym N α → EncRel Bytes α) → EncRel Bytes α)
    (hstep : ∀ D, step G D g = F D)
    (hmono : ∀ D D' : Sym N α → EncRel Bytes α, (∀ g, D g ≤ D' g) → F D ≤ F D')
    (hcont : ∀ bs a, F (denote G) bs a → ∃ n, F (denoteAt G n) bs a) :
    denote G g = F (denote G) := by
  apply le_antisymm
  · intro bs a ha
    obtain ⟨n, hn⟩ := denote_apply.mp ha
    cases n with
    | zero => exact absurd hn (by simp)
    | succ n =>
      rw [denoteAt_succ, hstep] at hn
      exact hmono _ _ (denoteAt_le_denote G n) _ _ hn
  · intro bs a ha
    obtain ⟨n, hn⟩ := hcont bs a ha
    refine denote_apply.mpr ⟨n + 1, ?_⟩
    rw [denoteAt_succ, hstep]
    exact hn

/-- A symbol whose one-step image is independent of the argument denotes it. -/
theorem denote_eq_of_step_const {g : Sym N α} {E : EncRel Bytes α}
    (h : ∀ D, step G D g = E) : denote G g = E :=
  denote_eq_of_step G (fun _ => E) h (fun _ _ _ => le_rfl) (fun _ _ ha => ⟨0, ha⟩)

/-- `eps` denotes the empty byte string with the unit attribute. -/
@[simp] theorem denote_eps : denote G .eps = epsRel G.alg.nil :=
  denote_eq_of_step_const G (fun _ => rfl)

/-- `byte b` denotes the one-byte terminal `b`. -/
@[simp] theorem denote_byte (b : UInt8) : denote G (.byte b) = byteRel G.alg b :=
  denote_eq_of_step_const G (fun _ => rfl)

/-- `range lo hi` denotes one byte in the inclusive interval. -/
@[simp] theorem denote_range (lo hi : UInt8) :
    denote G (.range lo hi) = rangeRel G.alg lo hi :=
  denote_eq_of_step_const G (fun _ => rfl)

/-- `bytes l` denotes the literal byte string `l`. -/
@[simp] theorem denote_bytes (l : Bytes) : denote G (.bytes l) = bytesRel G.alg l :=
  denote_eq_of_step_const G (fun _ => rfl)

/-- The fixpoint equation: a nonterminal denotes the join of its productions. -/
theorem denote_nt (x : N) :
    denote G (.nt x) = supList ((G.prods x).map (denote G)) :=
  denote_eq_of_step G _ (fun _ => rfl) (fun _ _ h => supList_map_mono h _)
    (fun _ _ h => exists_index_supList G _ h)

/-- `seq` is concatenation. -/
theorem denote_seq (gs : List (Sym N α)) :
    denote G (.seq gs) = appendAll G.alg (gs.map (denote G)) :=
  denote_eq_of_step G _ (fun _ => rfl) (fun _ _ h => appendAll_map_mono h _)
    (fun _ _ h => exists_index_appendAll G _ h)

/-- `alt` is the supremum in the lattice of encodings. -/
theorem denote_alt (gs : List (Sym N α)) :
    denote G (.alt gs) = supList (gs.map (denote G)) :=
  denote_eq_of_step G _ (fun _ => rfl) (fun _ _ h => supList_map_mono h _)
    (fun _ _ h => exists_index_supList G _ h)

/-- `star` is the Kleene closure. -/
theorem denote_star (g : Sym N α) :
    denote G (.star g) = kleene G.alg (denote G g) :=
  denote_eq_of_step G _ (fun _ => rfl) (fun _ _ h => kleene_mono (h g))
    (fun _ _ h => exists_index_kleene G g h)

/-- `plus` is one copy followed by the Kleene closure. -/
theorem denote_plus (g : Sym N α) :
    denote G (.plus g) = appendRel G.alg (denote G g) (kleene G.alg (denote G g)) := by
  refine denote_eq_of_step G _ (fun _ => rfl)
    (fun _ _ h => appendRel_mono (h g) (kleene_mono (h g))) ?_
  rintro bs a ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩
  obtain ⟨n₁, hn₁⟩ := denote_apply.mp h₁
  obtain ⟨n₂, hn₂⟩ := exists_index_kleene G g h₂
  exact ⟨max n₁ n₂, b₁, a₁, b₂, a₂, denoteAt_mono G (le_max_left n₁ n₂) g _ _ hn₁,
    kleene_mono (denoteAt_mono G (le_max_right n₁ n₂) g) _ _ hn₂, rfl, rfl⟩

/-- `opt` is the join of `ε` with the symbol. -/
theorem denote_opt (g : Sym N α) :
    denote G (.opt g) = epsRel G.alg.nil ⊔ denote G g := by
  refine denote_eq_of_step G _ (fun _ => rfl) (fun _ _ h => sup_le_sup_left (h g) _) ?_
  rintro bs a (h | h)
  · exact ⟨0, Or.inl h⟩
  · obtain ⟨n, hn⟩ := denote_apply.mp h
    exact ⟨n, Or.inr hn⟩

/-- `count g k` is the `k`-fold power. -/
theorem denote_count (g : Sym N α) (k : Nat) :
    denote G (.count g k) = powRel G.alg (denote G g) k :=
  denote_eq_of_step G _ (fun _ => rfl) (fun _ _ h => powRel_mono (h g) k)
    (fun _ _ h => exists_index_powRel G g k h)

/-- `attr` is `EncRel.mapPartial`: "this production's value is given by this
expression", with `none` for a failed side condition. -/
theorem denote_attr (f : α → Option α) (g : Sym N α) :
    denote G (.attr f g) = EncRel.mapPartial f (denote G g) := by
  refine denote_eq_of_step G _ (fun _ => rfl) (fun _ _ h => mapPartial_mono (h g)) ?_
  rintro bs a ⟨a', h, hf⟩
  obtain ⟨n, hn⟩ := denote_apply.mp h
  exact ⟨n, a', hn, hf⟩

/-- `count g k` is `seq` of `k` copies of `g`. -/
theorem denote_count_eq_seq (g : Sym N α) (k : Nat) :
    denote G (.count g k) = denote G (.seq (List.replicate k g)) := by
  rw [denote_count, denote_seq, List.map_replicate, powRel_eq_appendAll]

/-- `plus g` is `g` followed by `star g`. -/
theorem denote_plus_eq_seq (g : Sym N α) :
    denote G (.plus g) = denote G (.seq [g, .star g]) := by
  rw [denote_plus, denote_seq]
  simp [appendAll, denote_star, appendRel_eps_right]

end Compositionality

/-! ## Monotonicity in the grammar -/

section GrammarMono

variable {N α : Type}

/-- Enlarging the set of productions of each nonterminal enlarges the
denotation of every symbol. -/
theorem denote_mono_prods {A : Attr α} {P P' : N → List (Sym N α)}
    (h : ∀ x, ∀ g ∈ P x, g ∈ P' x) (g : Sym N α) :
    denote ⟨A, P⟩ g ≤ denote ⟨A, P'⟩ g := by
  have key : ∀ n g, denoteAt (⟨A, P⟩ : Gram N α) n g ≤ denoteAt (⟨A, P'⟩ : Gram N α) n g := by
    intro n
    induction n with
    | zero => intro g; exact bot_le
    | succ n ih => intro g; exact step_mono h ih g
  intro bs a ha
  obtain ⟨n, hn⟩ := denote_apply.mp ha
  exact denote_apply.mpr ⟨n, key n g _ _ hn⟩

end GrammarMono

/-! ## Sufficient conditions for functionality

`EncRel.Functional` (`Silmaril/Encoding/Relation.lean`) says the bytes determine
the attribute.  It is not compositional on its own — a concatenation of
functional relations need not be functional, because the split point is not
determined — so the working notion is `Unambiguous`: prefix-free *and*
functional, which is exactly `Silmaril.Wasm.Binary.PrefixFree`, split into its
two halves.  `Unambiguous` is closed under concatenation, and under joins of
pairwise `Separated` relations.
-/

section Functionality

variable {α : Type} {A : Attr α}

/-- No spelling is a proper prefix of another. -/
def PrefixFree (E : EncRel Bytes α) : Prop :=
  ∀ ⦃b b' : Bytes⦄ ⦃a a' : α⦄ ⦃r : Bytes⦄, E b a → E b' a' → b' = b ++ r → r = []

/-- Prefix-free and functional: a byte string that *begins* with a spelling
determines both the spelling and its attribute.  This is the hypothesis under
which the parse of a factor of a concatenation is determined. -/
def Unambiguous (E : EncRel Bytes α) : Prop := PrefixFree E ∧ E.Functional

/-- No spelling is empty. -/
def NonNullable (E : EncRel Bytes α) : Prop := ∀ a, ¬ E [] a

/-- The spellings of `E` and of `F` never begin with the same byte: "distinct
first bytes", the condition under which an alternation stays functional. -/
def Separated (E F : EncRel Bytes α) : Prop :=
  ∀ ⦃b b' : Bytes⦄ ⦃a a' : α⦄, E b a → F b' a' → b.head? ≠ b'.head?

/-- An unambiguous relation is functional: the bytes determine the attribute. -/
theorem Unambiguous.functional {E : EncRel Bytes α} (h : Unambiguous E) : E.Functional := h.2

/-- An unambiguous relation is prefix-free. -/
theorem Unambiguous.prefixFree {E : EncRel Bytes α} (h : Unambiguous E) : PrefixFree E := h.1

/-- The form in which `Unambiguous` is used: a concatenation splits uniquely at
the end of the first factor.  This is `Silmaril.Wasm.Binary.PrefixFree`. -/
theorem Unambiguous.split {E : EncRel Bytes α} (h : Unambiguous E) {b b' r r' : Bytes}
    {a a' : α} (hb : E b a) (hb' : E b' a') (he : b ++ r = b' ++ r') :
    b = b' ∧ a = a' ∧ r = r' := by
  have hbb : b = b' := by
    rcases List.append_eq_append_iff.mp he with ⟨c, hc, _⟩ | ⟨c, hc, _⟩
    · rw [h.1 hb hb' hc, List.append_nil] at hc; exact hc.symm
    · rw [h.1 hb' hb hc, List.append_nil] at hc; exact hc
  subst hbb
  exact ⟨rfl, h.2 hb hb', List.append_cancel_left he⟩

/-- `Separated` is symmetric. -/
theorem Separated.symm {E F : EncRel Bytes α} (h : Separated E F) : Separated F E :=
  fun _ _ _ _ hb hb' => (h hb' hb).symm

/-! ### Terminals -/

/-- `ε` is unambiguous. -/
theorem unambiguous_epsRel (a₀ : α) : Unambiguous (epsRel a₀) := by
  constructor
  · rintro b b' a a' r ⟨rfl, rfl⟩ ⟨hb', rfl⟩ hr
    simpa using hr.symm.trans hb'
  · rintro b a a' ⟨-, rfl⟩ ⟨-, rfl⟩; rfl

/-- A byte terminal is unambiguous. -/
theorem unambiguous_byteRel (A : Attr α) (b : UInt8) : Unambiguous (byteRel A b) := by
  constructor
  · rintro c c' a a' r ⟨rfl, rfl⟩ ⟨hc, rfl⟩ hr
    have := congrArg List.length (hr.symm.trans hc)
    simpa using this
  · rintro c a a' ⟨-, rfl⟩ ⟨-, rfl⟩; rfl

/-- A byte terminal derives no empty string. -/
theorem nonNullable_byteRel (A : Attr α) (b : UInt8) : NonNullable (byteRel A b) := by
  rintro a ⟨h, -⟩; exact absurd h (by simp)

/-- A byte-interval terminal is unambiguous. -/
theorem unambiguous_rangeRel (A : Attr α) (lo hi : UInt8) :
    Unambiguous (rangeRel A lo hi) := by
  constructor
  · rintro c c' a a' r ⟨b, -, -, rfl, rfl⟩ ⟨b', -, -, rfl, rfl⟩ hr
    have := congrArg List.length hr
    simpa using this.symm
  · rintro c a a' ⟨b, -, -, rfl, rfl⟩ ⟨b', -, -, hc, rfl⟩
    simp only [List.cons.injEq] at hc
    rw [hc.1]

/-- A byte-interval terminal derives no empty string. -/
theorem nonNullable_rangeRel (A : Attr α) (lo hi : UInt8) :
    NonNullable (rangeRel A lo hi) := by
  rintro a ⟨b, -, -, h, -⟩; exact absurd h (by simp)

/-- A literal byte string is unambiguous. -/
theorem unambiguous_bytesRel (A : Attr α) (l : Bytes) : Unambiguous (bytesRel A l) := by
  constructor
  · rintro c c' a a' r ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ hr
    simpa using hr
  · rintro c a a' ⟨-, rfl⟩ ⟨-, rfl⟩; rfl

/-! ### Concatenation -/

/-- A concatenation whose first factor is non-nullable is non-nullable. -/
theorem NonNullable.appendRel {E F : EncRel Bytes α} (hE : NonNullable E) :
    NonNullable (appendRel A E F) := by
  rintro a ⟨b₁, a₁, b₂, a₂, h₁, -, hb, -⟩
  exact hE a₁ (by simpa using (List.append_eq_nil_iff.mp hb.symm).1 ▸ h₁)

/-- Concatenation preserves unambiguity: this is the compositional engine of
every functionality proof below. -/
theorem Unambiguous.appendRel {E F : EncRel Bytes α} (hE : Unambiguous E)
    (hF : Unambiguous F) : Unambiguous (appendRel A E F) := by
  constructor
  · rintro c c' a a' r ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩
      ⟨b₁', a₁', b₂', a₂', h₁', h₂', rfl, rfl⟩ hr
    rw [List.append_assoc] at hr
    obtain ⟨rfl, -, hrest⟩ := hE.split h₁' h₁ hr
    exact hF.1 h₂ h₂' hrest
  · rintro c a a' ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩
      ⟨b₁', a₁', b₂', a₂', h₁', h₂', hc, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ := hE.split h₁ h₁' hc
    rw [hF.2 h₂ h₂']

/-- A concatenation of unambiguous factors is unambiguous: "every `seq` factor
is prefix-free". -/
theorem Unambiguous.appendAll {Es : List (EncRel Bytes α)}
    (h : ∀ E ∈ Es, Unambiguous E) : Unambiguous (appendAll A Es) := by
  induction Es with
  | nil => exact unambiguous_epsRel A.nil
  | cons E Es ih =>
    exact (h E (List.mem_cons_self ..)).appendRel
      (ih (fun F hF => h F (List.mem_cons_of_mem E hF)))

/-- `Sym.attr` preserves unambiguity: a value expression cannot create
ambiguity, only discard derivations. -/
theorem Unambiguous.mapPartial {β : Type} {E : EncRel Bytes α} (h : Unambiguous E)
    (f : α → Option β) : Unambiguous (EncRel.mapPartial f E) := by
  constructor
  · rintro b b' a a' r ⟨c, hc, -⟩ ⟨c', hc', -⟩ hr
    exact h.1 hc hc' hr
  · rintro b a a' ⟨c, hc, hf⟩ ⟨c', hc', hf'⟩
    rw [h.2 hc hc'] at hf
    exact Option.some.inj (hf.symm.trans hf')

/-! ### Alternation -/

/-- Distinct first bytes make a join of functional relations functional. -/
theorem functional_sup_of_separated {E F : EncRel Bytes α} (hE : E.Functional)
    (hF : F.Functional) (hs : Separated E F) : (E ⊔ F).Functional := by
  rintro b a a' (h | h) (h' | h')
  · exact hE h h'
  · exact absurd rfl (hs h h')
  · exact absurd rfl (hs h' h)
  · exact hF h h'

/-- Distinct first bytes make a join of prefix-free, non-nullable relations
prefix-free. -/
theorem prefixFree_sup_of_separated {E F : EncRel Bytes α} (hE : PrefixFree E)
    (hF : PrefixFree F) (hs : Separated E F) (hnE : NonNullable E)
    (hnF : NonNullable F) : PrefixFree (E ⊔ F) := by
  have cross : ∀ {X Y : EncRel Bytes α}, NonNullable X → Separated X Y →
      ∀ ⦃b b' : Bytes⦄ ⦃a a' : α⦄ ⦃r : Bytes⦄, X b a → Y b' a' → b' = b ++ r → r = [] := by
    rintro X Y hn hsep b b' a a' r hb hb' rfl
    cases b with
    | nil => exact absurd hb (hn a)
    | cons x bs => exact ((hsep hb hb') rfl).elim
  rintro b b' a a' r (h | h) (h' | h') hr
  · exact hE h h' hr
  · exact cross hnE hs h h' hr
  · exact cross hnF hs.symm h h' hr
  · exact hF h h' hr

/-- A join of two separated, unambiguous, non-nullable relations is unambiguous. -/
theorem Unambiguous.sup {E F : EncRel Bytes α} (hE : Unambiguous E) (hF : Unambiguous F)
    (hs : Separated E F) (hnE : NonNullable E) (hnF : NonNullable F) :
    Unambiguous (E ⊔ F) :=
  ⟨prefixFree_sup_of_separated hE.1 hF.1 hs hnE hnF,
    functional_sup_of_separated hE.2 hF.2 hs⟩

/-- A join of non-nullable relations is non-nullable. -/
theorem NonNullable.supList {Es : List (EncRel Bytes α)} (h : ∀ E ∈ Es, NonNullable E) :
    NonNullable (supList Es) := by
  intro a ha
  obtain ⟨E, hE, hv⟩ := supList_apply.mp ha
  exact h E hE a hv

/-- Being separated from each member is being separated from the join. -/
theorem Separated.supList {E : EncRel Bytes α} {Es : List (EncRel Bytes α)}
    (h : ∀ F ∈ Es, Separated E F) : Separated E (supList Es) := by
  intro b b' a a' hb hb'
  obtain ⟨F, hF, hv⟩ := supList_apply.mp hb'
  exact h F hF hb hv

/-- A join of pairwise separated, individually unambiguous and non-nullable
relations is unambiguous.  Applied to `denote_alt`, this is "every alternative
has a distinct first byte". -/
theorem Unambiguous.supList {Es : List (EncRel Bytes α)}
    (hu : ∀ E ∈ Es, Unambiguous E) (hn : ∀ E ∈ Es, NonNullable E)
    (hs : Es.Pairwise Separated) : Unambiguous (supList Es) := by
  induction Es with
  | nil => exact ⟨fun _ _ _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
  | cons E Es ih =>
    have hmem : ∀ F ∈ Es, F ∈ E :: Es := fun F hF => List.mem_cons_of_mem E hF
    refine (hu E (List.mem_cons_self ..)).sup
      (ih (fun F hF => hu F (hmem F hF)) (fun F hF => hn F (hmem F hF))
        (List.Pairwise.of_cons hs))
      (Separated.supList (fun F hF => (List.pairwise_cons.mp hs).1 F hF))
      (hn E (List.mem_cons_self ..))
      (NonNullable.supList (fun F hF => hn F (hmem F hF)))

/-! ### Iteration -/

/-- The Kleene closure of an unambiguous, non-nullable relation is functional.
Prefix-freeness is **not** available in general — `[]` is always a spelling, so
any non-empty spelling has it as a proper prefix — and that is as far as the
`star` case goes.  (The one exception is degenerate: if `E` derives nothing
then `kleene A E = epsRel A.nil`, whose only spelling is `[]`, and that *is*
prefix-free.) -/
theorem functional_kleene {E : EncRel Bytes α} (hu : Unambiguous E)
    (hn : NonNullable E) : (kleene A E).Functional := by
  have key : ∀ j k b a a', powRel A E j b a → powRel A E k b a' → a = a' := by
    intro j
    induction j with
    | zero =>
      rintro k b a a' ⟨rfl, rfl⟩ hk
      cases k with
      | zero => exact hk.2.symm
      | succ k =>
        obtain ⟨b₁, a₁, b₂, a₂, h₁, -, hb, -⟩ := hk
        exact absurd (((List.append_eq_nil_iff.mp hb.symm).1 ▸ h₁)) (hn a₁)
    | succ j ih =>
      rintro k b a a' ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩ hk
      cases k with
      | zero =>
        obtain ⟨hb, -⟩ := hk
        exact absurd (((List.append_eq_nil_iff.mp hb).1 ▸ h₁)) (hn a₁)
      | succ k =>
        obtain ⟨b₁', a₁', b₂', a₂', h₁', h₂', hb, rfl⟩ := hk
        obtain ⟨rfl, rfl, rfl⟩ := hu.split h₁ h₁' hb
        rw [ih k b₂ a₂ a₂' h₂ h₂']
  intro b a a' ha ha'
  obtain ⟨j, hj⟩ := kleene_apply.mp ha
  obtain ⟨k, hk⟩ := kleene_apply.mp ha'
  exact key j k b a a' hj hk

end Functionality

/-! ## A decidable leading-byte analysis

`Separated` and `NonNullable` are statements about a denotation, hence not
decidable as they stand.  `leadRange?` is a decidable syntactic analysis that
implies both: it reads off, by structural recursion alone, an interval that
contains the first byte of every string a symbol derives.  It answers `none`
for a nonterminal, for `eps`, `star`, `opt`, `count _ 0` and for an `alt` (a
hull of several intervals would be sound but is not needed: flatten the `alt`
and use `altSeparated` on its branches), so every `some` answer is a certificate
that the symbol is non-nullable.
-/

section Lead

variable {N α : Type}

/-- The interval containing the first byte of every string `g` derives, when it
can be read off structurally; `none` means "unknown".

`range lo hi` with `lo > hi` derives nothing, so answering `some (lo, hi)` for
it is vacuously sound and saves a check. -/
def leadRange? : Sym N α → Option (UInt8 × UInt8)
  | .eps => none
  | .byte b => some (b, b)
  | .range lo hi => some (lo, hi)
  | .bytes [] => none
  | .bytes (b :: _) => some (b, b)
  | .nt _ => none
  | .seq [] => none
  | .seq (g :: _) => leadRange? g
  | .alt _ => none
  | .star _ => none
  | .plus g => leadRange? g
  | .opt _ => none
  | .count _ 0 => none
  | .count g (_ + 1) => leadRange? g
  | .attr _ g => leadRange? g

/-- Two byte intervals are disjoint. -/
def rangeDisjoint (p q : UInt8 × UInt8) : Bool := p.2 < q.1 || q.2 < p.1

/-- `leadRange?` is sound: a `some` answer bounds the first byte of every string
the symbol derives, and in particular says there is one. -/
theorem leadRange?_sound (G : Gram N α) {g : Sym N α} {lo hi : UInt8}
    (h : leadRange? g = some (lo, hi)) {bs : Bytes} {a : α} (hd : denote G g bs a) :
    ∃ b bs', bs = b :: bs' ∧ lo ≤ b ∧ b ≤ hi := by
  induction g using leadRange?.induct generalizing bs a with
  | case1 => simp [leadRange?] at h
  | case2 b =>
    rw [denote_byte] at hd
    obtain ⟨rfl, -⟩ := hd
    simp only [leadRange?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, [], rfl, UInt8.le_refl b, UInt8.le_refl b⟩
  | case3 lo' hi' =>
    rw [denote_range] at hd
    obtain ⟨b, hlo, hhi, rfl, -⟩ := hd
    simp only [leadRange?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, [], rfl, hlo, hhi⟩
  | case4 => simp [leadRange?] at h
  | case5 b l =>
    rw [denote_bytes] at hd
    obtain ⟨rfl, -⟩ := hd
    simp only [leadRange?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, l, rfl, UInt8.le_refl b, UInt8.le_refl b⟩
  | case6 => simp [leadRange?] at h
  | case7 => simp [leadRange?] at h
  | case8 g gs ih =>
    rw [denote_seq] at hd
    obtain ⟨b₁, a₁, b₂, a₂, h₁, -, rfl, -⟩ := hd
    obtain ⟨b, bs', rfl, hlo, hhi⟩ := ih h h₁
    exact ⟨b, bs' ++ b₂, rfl, hlo, hhi⟩
  | case9 => simp [leadRange?] at h
  | case10 => simp [leadRange?] at h
  | case11 g ih =>
    rw [denote_plus] at hd
    obtain ⟨b₁, a₁, b₂, a₂, h₁, -, rfl, -⟩ := hd
    obtain ⟨b, bs', rfl, hlo, hhi⟩ := ih h h₁
    exact ⟨b, bs' ++ b₂, rfl, hlo, hhi⟩
  | case12 => simp [leadRange?] at h
  | case13 => simp [leadRange?] at h
  | case14 g k ih =>
    rw [denote_count] at hd
    obtain ⟨b₁, a₁, b₂, a₂, h₁, -, rfl, -⟩ := hd
    obtain ⟨b, bs', rfl, hlo, hhi⟩ := ih h h₁
    exact ⟨b, bs' ++ b₂, rfl, hlo, hhi⟩
  | case15 f g ih =>
    rw [denote_attr] at hd
    obtain ⟨a', hd', -⟩ := hd
    exact ih h hd'

/-- A known leading-byte range certifies non-nullability. -/
theorem nonNullable_of_leadRange (G : Gram N α) {g : Sym N α} {p : UInt8 × UInt8}
    (h : leadRange? g = some p) : NonNullable (denote G g) := by
  obtain ⟨lo, hi⟩ := p
  intro a ha
  obtain ⟨b, bs', hbs, -, -⟩ := leadRange?_sound G h ha
  exact absurd hbs (by simp)

/-- Disjoint leading-byte ranges imply distinct first bytes. -/
theorem separated_of_leadRange (G : Gram N α) {g g' : Sym N α} {p q : UInt8 × UInt8}
    (h : leadRange? g = some p) (h' : leadRange? g' = some q)
    (hd : rangeDisjoint p q = true) : Separated (denote G g) (denote G g') := by
  obtain ⟨plo, phi⟩ := p
  obtain ⟨qlo, qhi⟩ := q
  intro bs bs' a a' hb hb'
  obtain ⟨b, c, rfl, hlo, hhi⟩ := leadRange?_sound G h hb
  obtain ⟨b', c', rfl, hlo', hhi'⟩ := leadRange?_sound G h' hb'
  simp only [List.head?_cons, ne_eq, Option.some.injEq]
  rintro rfl
  simp only [rangeDisjoint, Bool.or_eq_true, decide_eq_true_eq] at hd
  rw [UInt8.le_iff_toNat_le] at hlo hhi hlo' hhi'
  rcases hd with hd | hd <;> rw [UInt8.lt_iff_toNat_lt] at hd <;> omega

/-- Every symbol of `gs` has a known leading-byte range, and the ranges are
pairwise disjoint: a decidable sufficient condition for an `alt` (or for the
productions of a nonterminal) to be unambiguous. -/
def altSeparated : List (Sym N α) → Bool
  | [] => true
  | g :: gs =>
    (match leadRange? g with
      | some p => gs.all (fun g' => match leadRange? g' with
          | some q => rangeDisjoint p q
          | none => false)
      | none => false) && altSeparated gs

/-- `altSeparated` certifies that every branch has a known leading-byte range. -/
theorem altSeparated_leadRange {gs : List (Sym N α)} (h : altSeparated gs = true)
    {g : Sym N α} (hg : g ∈ gs) : ∃ p, leadRange? g = some p := by
  induction gs with
  | nil => exact absurd hg (by simp)
  | cons g' gs ih =>
    simp only [altSeparated, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hg with rfl | hg
    · revert h; split
      · rintro ⟨-, -⟩; exact ⟨_, by assumption⟩
      · rintro ⟨h, -⟩; exact absurd h (by simp)
    · exact ih h.2 hg

/-- `altSeparated` certifies that the branches are pairwise separated. -/
theorem altSeparated_pairwise (G : Gram N α) {gs : List (Sym N α)}
    (h : altSeparated gs = true) :
    gs.Pairwise (fun g g' => Separated (denote G g) (denote G g')) := by
  induction gs with
  | nil => exact List.Pairwise.nil
  | cons g gs ih =>
    simp only [altSeparated, Bool.and_eq_true] at h
    refine List.Pairwise.cons ?_ (ih h.2)
    intro g' hg'
    revert h
    split
    · rintro ⟨hall, -⟩
      rename_i p hp
      have := (List.all_eq_true.mp hall) g' hg'
      revert this
      split
      · rename_i q hq
        intro hdisj
        exact separated_of_leadRange G hp hq hdisj
      · intro hfalse; exact absurd hfalse (by simp)
    · rintro ⟨hfalse, -⟩; exact absurd hfalse (by simp)

end Lead

/-! ## Functionality of a denotation -/

section SymFunctionality

variable {N α : Type} (G : Gram N α)

/-- Every factor prefix-free (and functional) makes a `seq` unambiguous. -/
theorem unambiguous_denote_seq {gs : List (Sym N α)}
    (hu : ∀ g ∈ gs, Unambiguous (denote G g)) : Unambiguous (denote G (.seq gs)) := by
  rw [denote_seq]
  refine Unambiguous.appendAll ?_
  intro E hE
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
  exact hu g hg

/-- Distinct first bytes across the alternatives, each alternative unambiguous:
the `alt` is unambiguous, hence `Functional`. -/
theorem unambiguous_denote_alt {gs : List (Sym N α)} (hsep : altSeparated gs = true)
    (hu : ∀ g ∈ gs, Unambiguous (denote G g)) : Unambiguous (denote G (.alt gs)) := by
  rw [denote_alt]
  refine Unambiguous.supList ?_ ?_ ?_
  · intro E hE
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
    exact hu g hg
  · intro E hE
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
    obtain ⟨p, hp⟩ := altSeparated_leadRange hsep hg
    exact nonNullable_of_leadRange G hp
  · exact List.Pairwise.map _ (fun _ _ h => h) (altSeparated_pairwise G hsep)

/-- The same for a nonterminal, whose productions are its alternatives. -/
theorem unambiguous_denote_nt {x : N} (hsep : altSeparated (G.prods x) = true)
    (hu : ∀ g ∈ G.prods x, Unambiguous (denote G g)) :
    Unambiguous (denote G (.nt x)) := by
  have h := unambiguous_denote_alt G (gs := G.prods x) hsep hu
  rwa [denote_alt, ← denote_nt] at h

/-- An iteration of an unambiguous, non-nullable symbol is functional.  No
prefix-freeness is claimed: `ε` is always a spelling, so `denote G (.star g)`
is prefix-free only in the degenerate case where `g` derives nothing — which
these hypotheses do not exclude, since `leadRange?` answers `some (lo, hi)` for
an inverted `range lo hi` that derives nothing at all. -/
theorem functional_denote_star {g : Sym N α} (hu : Unambiguous (denote G g))
    {p : UInt8 × UInt8} (hp : leadRange? g = some p) :
    (denote G (.star g)).Functional := by
  rw [denote_star]
  exact functional_kleene hu (nonNullable_of_leadRange G hp)

end SymFunctionality

/-! ## LEB128 as a worked instance

`Silmaril/Wasm/Binary/Basic.lean` transcribes `BuN(N)`
(`5.1-binary.values.spectec:9-11`) as the hand-written inductive relation
`Silmaril.Wasm.Binary.UN`.  Here is the same production written in this
framework, and the proof that the two agree.

The nonterminals are the bit widths, the attribute algebra is `Attr.list`
over `UInt8.toNat` — a derivation accumulates the numbers its terminals and
nonterminals contributed — and each production's value expression is a
`Sym.attr` returning a one-element list, so the agreement statement is
`denote lebGram (.nt W) bs [m] ↔ UN W bs m`.
-/

section Leb

open Silmaril.Wasm.Binary

/-- The attribute algebra of the LEB128 grammar. -/
def lebAlg : Attr (List Nat) := Attr.list UInt8.toNat

/-- The value expression of `n:Bbyte => n -- if n < 2^7 ∧ n < 2^N`: the side
condition `n < 2^N` is the partiality. -/
def lebAct1 (W : Nat) : List Nat → Option (List Nat)
  | [n] => if n < 2 ^ W then some [n] else none
  | _ => none

/-- The value expression of `n:Bbyte m:BuN(N-7) => 2^7 * m + (n - 2^7)`. -/
def lebAct2 : List Nat → Option (List Nat)
  | [n, m] => some [2 ^ 7 * m + (n - 2 ^ 7)]
  | _ => none

/-- `n:Bbyte => n -- if n < 2^7 ∧ n < 2^N`.  The bound `n < 2^7` is the
terminal range; `n < 2^N` is the side condition inside `lebAct1`. -/
def lebP1 (W : Nat) : Sym Nat (List Nat) :=
  .attr (lebAct1 W) (.range 0x00 0x7F)

/-- `n:Bbyte m:BuN(N-7) => 2^7 * m + (n - 2^7) -- if n ≥ 2^7 ∧ N > 7`.  The
bound `n ≥ 2^7` is the terminal range; `N > 7` gates the production itself. -/
def lebP2 (W : Nat) : Sym Nat (List Nat) :=
  .attr lebAct2 (.seq [.range 0x80 0xFF, .nt (W - 7)])

/-- The productions of `BuN(W)`. -/
def lebProds (W : Nat) : List (Sym Nat (List Nat)) :=
  lebP1 W :: (if 7 < W then [lebP2 W] else [])

/-- The LEB128 grammar. -/
def lebGram : Gram Nat (List Nat) := ⟨lebAlg, lebProds⟩

/-- A two-factor concatenation, in the form the LEB128 productions need. -/
theorem appendAll_pair {α : Type} {A : Attr α} (E F : EncRel Bytes α) :
    appendAll A [E, F] = appendRel A E F := by
  rw [appendAll_cons, appendAll_singleton]

/-- The denotation of the one-byte production. -/
theorem denote_lebP1 (W : Nat) :
    denote lebGram (lebP1 W)
      = EncRel.mapPartial (lebAct1 W) (rangeRel lebAlg 0x00 0x7F) := by
  rw [lebP1, denote_attr, denote_range]
  rfl

/-- The denotation of the continuation production, in terms of the denotation of
the narrower width. -/
theorem denote_lebP2 (W : Nat) :
    denote lebGram (lebP2 W)
      = EncRel.mapPartial lebAct2
          (appendRel lebAlg (rangeRel lebAlg 0x80 0xFF)
            (denote lebGram (.nt (W - 7)))) := by
  rw [lebP2, denote_attr, denote_seq]
  simp only [List.map_cons, List.map_nil, appendAll_pair, denote_range]
  rfl

/-- The one-byte production is always available. -/
theorem lebP1_mem (W : Nat) : lebP1 W ∈ lebProds W := List.mem_cons_self ..

/-- The continuation production is available exactly when `7 < W`. -/
theorem lebP2_mem {W : Nat} (h : 7 < W) : lebP2 W ∈ lebProds W := by
  simp [lebProds, h]

/-- `BuN(W)` has only these two productions. -/
theorem mem_lebProds {W : Nat} {g : Sym Nat (List Nat)} (h : g ∈ lebProds W) :
    g = lebP1 W ∨ (7 < W ∧ g = lebP2 W) := by
  simp only [lebProds, List.mem_cons] at h
  rcases h with rfl | h
  · exact Or.inl rfl
  · by_cases hw : 7 < W
    · simp only [hw, ite_true, List.mem_singleton] at h
      exact Or.inr ⟨hw, h⟩
    · simp only [hw, ite_false, List.not_mem_nil] at h

/-- The terminal range `[0x00, 0x7F]` is SpecTec's side condition `n < 2^7`. -/
theorem toNat_le_of_le_7F {b : UInt8} (h : b ≤ 0x7F) : b.toNat < 2 ^ 7 := by
  have := UInt8.le_iff_toNat_le.mp h
  have hc : (0x7F : UInt8).toNat = 127 := by decide
  omega

/-- Converse of `toNat_le_of_le_7F`. -/
theorem le_7F_of_toNat_lt {b : UInt8} (h : b.toNat < 2 ^ 7) : b ≤ 0x7F := by
  have hc : (0x7F : UInt8).toNat = 127 := by decide
  exact UInt8.le_iff_toNat_le.mpr (by omega)

/-- The terminal range `[0x80, 0xFF]` is SpecTec's side condition `n ≥ 2^7`. -/
theorem le_toNat_of_80_le {b : UInt8} (h : (0x80 : UInt8) ≤ b) : 2 ^ 7 ≤ b.toNat := by
  have := UInt8.le_iff_toNat_le.mp h
  have hc : (0x80 : UInt8).toNat = 128 := by decide
  omega

/-- Converse of `le_toNat_of_80_le`. -/
theorem le_80_of_le_toNat {b : UInt8} (h : 2 ^ 7 ≤ b.toNat) : (0x80 : UInt8) ≤ b := by
  have hc : (0x80 : UInt8).toNat = 128 := by decide
  exact UInt8.le_iff_toNat_le.mpr (by omega)

/-- `0x00` is the least byte. -/
theorem zero_le_uint8 (b : UInt8) : (0x00 : UInt8) ≤ b := by
  have hc : (0x00 : UInt8).toNat = 0 := by decide
  exact UInt8.le_iff_toNat_le.mpr (by omega)

/-- `0xFF` is the greatest byte. -/
theorem le_FF_uint8 (b : UInt8) : b ≤ 0xFF := by
  have hc : (0xFF : UInt8).toNat = 255 := by decide
  have hb : b.toNat < 256 := UInt8.toNat_lt_size b
  exact UInt8.le_iff_toNat_le.mpr (by omega)

/-- Every byte string `UN W` accepts is accepted by the grammar, with the same
value. -/
theorem denote_leb_of_un {W : Nat} {bs : Bytes} {m : Nat} (h : UN W bs m) :
    denote lebGram (.nt W) bs [m] := by
  induction h with
  | @byte W n h₁ h₂ =>
    rw [denote_nt]
    refine supList_apply.mpr ⟨denote lebGram (lebP1 W),
      List.mem_map.mpr ⟨lebP1 W, lebP1_mem W, rfl⟩, ?_⟩
    rw [denote_lebP1]
    refine ⟨[n.toNat], ⟨n, zero_le_uint8 n, le_7F_of_toNat_lt h₁, rfl, rfl⟩, ?_⟩
    simp [lebAct1, h₂]
  | @cont W n b m h₁ h₂ _ ih =>
    rw [denote_nt]
    refine supList_apply.mpr ⟨denote lebGram (lebP2 W),
      List.mem_map.mpr ⟨lebP2 W, lebP2_mem h₂, rfl⟩, ?_⟩
    rw [denote_lebP2]
    refine ⟨[n.toNat, m], ⟨[n], [n.toNat], b, [m],
      ⟨n, le_80_of_le_toNat h₁, le_FF_uint8 n, rfl, rfl⟩, ih, rfl, rfl⟩, ?_⟩
    simp [lebAct2]

/-- Every byte string the grammar accepts is accepted by `UN W`, with the same
value.  The induction is on the width: the recursive production is gated by
`7 < W` and recurses at `W - 7`. -/
theorem un_of_denote_leb (W : Nat) {bs : Bytes} {m : Nat}
    (h : denote lebGram (.nt W) bs [m]) : UN W bs m := by
  induction W using Nat.strong_induction_on generalizing bs m with
  | _ W ih =>
    rw [denote_nt] at h
    obtain ⟨E, hE, hv⟩ := supList_apply.mp h
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
    rcases mem_lebProds hg with rfl | ⟨hw, rfl⟩
    · rw [denote_lebP1] at hv
      obtain ⟨a', ⟨b, -, hhi, rfl, rfl⟩, hact⟩ := hv
      simp only [lebAct1, lebAlg, Attr.list] at hact
      split at hact
      · simp only [Option.some.injEq, List.cons.injEq] at hact
        obtain ⟨rfl, -⟩ := hact
        rename_i hb
        exact UN.byte b (toNat_le_of_le_7F hhi) hb
      · exact absurd hact (by simp)
    · rw [denote_lebP2] at hv
      obtain ⟨a', ⟨b₁, a₁, b₂, a₂, ⟨b, hlo, -, rfl, rfl⟩, hnt, rfl, rfl⟩, hact⟩ := hv
      simp only [lebAlg, Attr.list, List.singleton_append] at hact
      match a₂, hact with
      | [m'], hact =>
        simp only [lebAct2, Option.some.injEq, List.cons.injEq] at hact
        obtain ⟨rfl, -⟩ := hact
        exact UN.cont b (le_toNat_of_80_le hlo) hw (ih (W - 7) (by omega) hnt)

/-- The framework's denotation of the LEB128 grammar is the hand-written
relation of `Silmaril/Wasm/Binary/Basic.lean`. -/
theorem denote_leb_nt_iff (W : Nat) (bs : Bytes) (m : Nat) :
    denote lebGram (.nt W) bs [m] ↔ UN W bs m :=
  ⟨un_of_denote_leb W, denote_leb_of_un⟩

/-- The decidable leading-byte condition really does apply: the continuation
bit separates the two productions of `BuN(W)` for every width. -/
theorem altSeparated_lebProds (W : Nat) : altSeparated (lebProds W) = true := by
  by_cases h : 7 < W <;>
    simp [altSeparated, lebProds, lebP1, lebP2, leadRange?, rangeDisjoint, h]

/-- `BuN(W)` is unambiguous, by the framework's generic conditions alone:
`unambiguous_denote_nt` on the separated productions, `Unambiguous.appendRel`
for the recursive one, and `Unambiguous.mapPartial` for the value
expressions. -/
theorem unambiguous_leb (W : Nat) : Unambiguous (denote lebGram (.nt W)) := by
  induction W using Nat.strong_induction_on with
  | _ W ih =>
    refine unambiguous_denote_nt lebGram (altSeparated_lebProds W) ?_
    intro g hg
    rcases mem_lebProds hg with rfl | ⟨hw, rfl⟩
    · rw [denote_lebP1]
      exact (unambiguous_rangeRel lebAlg 0x00 0x7F).mapPartial _
    · rw [denote_lebP2]
      exact ((unambiguous_rangeRel lebAlg 0x80 0xFF).appendRel
        (ih (W - 7) (by omega))).mapPartial _

/-- The payoff: the generic framework proves prefix-freeness of the
hand-written `Silmaril.Wasm.Binary.UN`, in that file's own sense. -/
theorem un_prefixFree (W : Nat) : Wasm.Binary.PrefixFree (UN W) := by
  intro b b' r r' a a' hb hb' he
  obtain ⟨hbb, ha, -⟩ :=
    (unambiguous_leb W).split (denote_leb_of_un hb) (denote_leb_of_un hb') he
  exact ⟨hbb, by simpa using ha⟩

end Leb

end Silmaril.SpecTec.Grammar
