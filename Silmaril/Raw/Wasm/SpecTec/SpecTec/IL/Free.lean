module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Ast

/-!
# Free and bound identifiers of the internal language

A transcription of `spectec/src/il/free.ml` and of the generic data structure
it includes, `spectec/src/xl/gen_free.ml`, at
`608711107b7f1edb13efd57b7d79b49477462d36`.  This is the analysis the IL
validator (`spectec/src/il/valid.ml`) and the recursion grouping
(`spectec/src/frontend/elab.ml:2864`, `recursify_defs`) are built on, so it is
the first piece of the IL semantics.

## The representation of an identifier set

OCaml uses `Set.Make(String)` (`spectec/src/xl/gen_free.ml:6`), a balanced
tree of strings.  Here a set is a `Finset String`.  The alternative — a
`List String` kept sorted — would make `union`, `diff` and `subset` partial
functions on the *shape* of the input (they are only correct on sorted,
duplicate-free lists), so every lemma would carry a sortedness side condition
and `Sets` would not have an extensional equality.  `Finset` has exactly the
algebra `gen_free.ml` assumes — `∪` is associative, commutative and
idempotent, `\` and `⊆` are the lattice operations — all of it already proved
in Mathlib, and `DecidableEq (Finset String)` makes the examples at the end of
this file close by `decide`.  The identifiers that occur in a `--ast` stream
are short, so the kernel cost of `String.decEq` is not a concern here.

## What the `--ast` erasure costs

`Silmaril/SpecTec/IL/Ast.lean` is the image of `spectec/src/il/ast.ml` under
`spectec/src/backend-ast/print.ml`, so some fields `free.ml` reads are simply
not there.  Three of its functions are therefore not transcriptions:

* `free_prem (LetPr (qs, e1, e2))` (`free.ml:113`) is
  `(free_exp e1 -- bound_quants qs) ++ free_exp e2`, and
  `bound_prem (LetPr (qs, _, _))` (`free.ml:119`) is `bound_quants qs`.
  `IL.Prem.letPr` has no `qs` (`print.ml:165` drops it), so `freePrem` of a
  `letPr` is `freeExp e₁ ∪ freeExp e₂` and `boundPrem` of a `letPr` is
  `Sets.empty`.  See `freePrem` and `boundPrem` for the exact consequences.
* `free_typfield` and `free_typcase` (`free.ml:49,51`) ignore the trailing
  `hint list`, which `IL.TypField`/`IL.TypCase` also drop, so those two are
  unaffected.
* `free_hintdef` (`free.ml:181`) and the `HintD` branches of `free_def` and
  `bound_def` (`free.ml:203,212`) have no counterpart: `IL.Def` has no `hintD`
  constructor at all (see `Silmaril/SpecTec/IL/Ast.lean` and
  `Silmaril/SpecTec/IL/Hint.lean`).  Note that `bound_def (HintD _)` is
  `empty`, which is what `IL.Def`'s docstring uses to show a `HintD` can never
  be nested inside a `RecD`; dropping the constructor loses nothing here.

## Shape of the transcription

`free.ml:9-159` is one `let rec … and …` group.  Most of it has to stay one
group in Lean too, but not all: `bound_iter`, `bound_iterexp`, `bound_typbind`,
`bound_typbinds`, `bound_typ`, `bound_param`, `bound_params` and `bound_prem`
never call a `free_*` function and never descend into a type or an expression
— they only read the identifiers immediately under the node — so they are
defined *before* the mutual block, which keeps that block to the `free_*`
family.  `bound_def` (`free.ml:205`) recurses only through `Def`, so it is its
own small group afterwards.

`gen_free.ml:84`'s `free_list` is a left fold over `++`.  `freeList` below is
the usual right recursion; `freeList_eq_foldl` proves the two agree, which is
where associativity and unitality of `union` are used.  Inside the mutual
block the higher-order `freeList`/`freeListDep` cannot be used directly
(Lean's structural recursion needs the recursive call to sit on a subterm), so
each syntactic class gets its own specialised list traversal, exactly as
`Silmaril/SpecTec/IL/Print.lean` does; the `*_eq` simp lemmas below identify
them with the generic ones.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

/-! ## The data structure (`spectec/src/xl/gen_free.ml`) -/

/-- `module Set = Set.Make(String)` (`spectec/src/xl/gen_free.ml:6`): a finite
set of identifiers.  `IL.Id` is `String` with the source region dropped. -/
abbrev IdSet := Finset Id

/-- `type sets` (`spectec/src/xl/gen_free.ml:10-11`): one identifier set per
namespace.  The field order is OCaml's. -/
structure Sets where
  /-- `typid : Set.t` — type and syntax names. -/
  typid : IdSet
  /-- `relid : Set.t` — relation names. -/
  relid : IdSet
  /-- `varid : Set.t` — term variables. -/
  varid : IdSet
  /-- `defid : Set.t` — function (definition) names. -/
  defid : IdSet
  /-- `gramid : Set.t` — grammar names. -/
  gramid : IdSet
  deriving DecidableEq, Inhabited

namespace Sets

/-- `empty` (`spectec/src/xl/gen_free.ml:13-19`). -/
def empty : Sets := ⟨∅, ∅, ∅, ∅, ∅⟩

/-- `union`, written `( ++ )` (`spectec/src/xl/gen_free.ml:21-27,45`). -/
def union (s₁ s₂ : Sets) : Sets :=
  ⟨s₁.typid ∪ s₂.typid, s₁.relid ∪ s₂.relid, s₁.varid ∪ s₂.varid,
    s₁.defid ∪ s₂.defid, s₁.gramid ∪ s₂.gramid⟩

/-- `inter`, written `( ** )` (`spectec/src/xl/gen_free.ml:29-35,46`).
`free.ml` itself never uses it; `spectec/src/il/valid.ml` does. -/
def inter (s₁ s₂ : Sets) : Sets :=
  ⟨s₁.typid ∩ s₂.typid, s₁.relid ∩ s₂.relid, s₁.varid ∩ s₂.varid,
    s₁.defid ∩ s₂.defid, s₁.gramid ∩ s₂.gramid⟩

/-- `diff`, written `( -- )` (`spectec/src/xl/gen_free.ml:37-43,47`). -/
def diff (s₁ s₂ : Sets) : Sets :=
  ⟨s₁.typid \ s₂.typid, s₁.relid \ s₂.relid, s₁.varid \ s₂.varid,
    s₁.defid \ s₂.defid, s₁.gramid \ s₂.gramid⟩

/-- `subset` (`spectec/src/xl/gen_free.ml:49-54`): containment in every
component.  OCaml returns a `bool`; this is the corresponding `Prop`, and
`Sets.instDecidableSubset` recovers the decision procedure. -/
protected def Subset (s₁ s₂ : Sets) : Prop :=
  s₁.typid ⊆ s₂.typid ∧ s₁.relid ⊆ s₂.relid ∧ s₁.varid ⊆ s₂.varid ∧
    s₁.defid ⊆ s₂.defid ∧ s₁.gramid ⊆ s₂.gramid

/-- `⊆` on `Sets` is `gen_free.ml:49`'s `subset`. -/
instance : HasSubset Sets := ⟨Sets.Subset⟩

/-- `gen_free.ml:49`'s `subset` is decidable, as the OCaml `bool` says. -/
instance instDecidableSubset (s₁ s₂ : Sets) : Decidable (s₁ ⊆ s₂) :=
  inferInstanceAs (Decidable (s₁.typid ⊆ s₂.typid ∧ s₁.relid ⊆ s₂.relid ∧
    s₁.varid ⊆ s₂.varid ∧ s₁.defid ⊆ s₂.defid ∧ s₁.gramid ⊆ s₂.gramid))

/-- `disjoint` (`spectec/src/xl/gen_free.ml:56-61`): disjointness in every
component.  `spectec/src/frontend/elab.ml:2895` uses it to decide whether a
singleton strongly connected component needs a `RecD` wrapper. -/
protected def Disjoint (s₁ s₂ : Sets) : Prop :=
  _root_.Disjoint s₁.typid s₂.typid ∧ _root_.Disjoint s₁.relid s₂.relid ∧
    _root_.Disjoint s₁.varid s₂.varid ∧ _root_.Disjoint s₁.defid s₂.defid ∧
    _root_.Disjoint s₁.gramid s₂.gramid

/-- `gen_free.ml:56`'s `disjoint` is decidable, as the OCaml `bool` says. -/
instance instDecidableDisjoint (s₁ s₂ : Sets) : Decidable (s₁.Disjoint s₂) :=
  inferInstanceAs (Decidable (_root_.Disjoint s₁.typid s₂.typid ∧
    _root_.Disjoint s₁.relid s₂.relid ∧ _root_.Disjoint s₁.varid s₂.varid ∧
    _root_.Disjoint s₁.defid s₂.defid ∧ _root_.Disjoint s₁.gramid s₂.gramid))

end Sets

/-! ## Identifiers (`spectec/src/xl/gen_free.ml:64-76`)

`free_*id x` is the singleton `{x}` in the matching component.  `bound_*id x`
is the same thing except that the wildcard `"_"` binds nothing. -/

/-- `free_typid` (`spectec/src/xl/gen_free.ml:66`). -/
def freeTypid (x : Id) : Sets := { Sets.empty with typid := {x} }

/-- `free_relid` (`spectec/src/xl/gen_free.ml:67`). -/
def freeRelid (x : Id) : Sets := { Sets.empty with relid := {x} }

/-- `free_varid` (`spectec/src/xl/gen_free.ml:68`). -/
def freeVarid (x : Id) : Sets := { Sets.empty with varid := {x} }

/-- `free_defid` (`spectec/src/xl/gen_free.ml:69`). -/
def freeDefid (x : Id) : Sets := { Sets.empty with defid := {x} }

/-- `free_gramid` (`spectec/src/xl/gen_free.ml:70`). -/
def freeGramid (x : Id) : Sets := { Sets.empty with gramid := {x} }

/-- `bound_typid` (`spectec/src/xl/gen_free.ml:72`). -/
def boundTypid (x : Id) : Sets := if x = "_" then Sets.empty else freeTypid x

/-- `bound_relid` (`spectec/src/xl/gen_free.ml:73`). -/
def boundRelid (x : Id) : Sets := if x = "_" then Sets.empty else freeRelid x

/-- `bound_varid` (`spectec/src/xl/gen_free.ml:74`). -/
def boundVarid (x : Id) : Sets := if x = "_" then Sets.empty else freeVarid x

/-- `bound_defid` (`spectec/src/xl/gen_free.ml:75`). -/
def boundDefid (x : Id) : Sets := if x = "_" then Sets.empty else freeDefid x

/-- `bound_gramid` (`spectec/src/xl/gen_free.ml:76`). -/
def boundGramid (x : Id) : Sets := if x = "_" then Sets.empty else freeGramid x

/-! ## Aggregates (`spectec/src/xl/gen_free.ml:79-90`) -/

/-- `free_empty` (`spectec/src/xl/gen_free.ml:81`). -/
def freeEmpty {α : Type _} (_ : α) : Sets := Sets.empty

/-- `free_pair` (`spectec/src/xl/gen_free.ml:82`). -/
def freePair {α β : Type _} (f : α → Sets) (g : β → Sets) : α × β → Sets
  | (x, y) => (f x).union (g y)

/-- `free_opt` (`spectec/src/xl/gen_free.ml:83`). -/
def freeOpt {α : Type _} (f : α → Sets) : Option α → Sets
  | none => Sets.empty
  | some x => f x

/-- `free_list` (`spectec/src/xl/gen_free.ml:84`), which is also `bound_list`
(`gen_free.ml:90`).

OCaml folds from the left, `List.fold_left (++) empty (List.map free_x xs)`;
this recurses from the right.  `freeList_eq_foldl` proves they agree. -/
def freeList {α : Type _} (f : α → Sets) : List α → Sets
  | [] => Sets.empty
  | x :: xs => (f x).union (freeList f xs)

/-- `free_list_dep` (`spectec/src/xl/gen_free.ml:86-88`): a fold in which each
element binds, for the elements after it, the identifiers `bound_x` reports.
This is what makes a tuple type, a premise list and a parameter list scope
left to right. -/
def freeListDep {α : Type _} (f b : α → Sets) : List α → Sets
  | [] => Sets.empty
  | x :: xs => (f x).union ((freeListDep f b xs).diff (b x))

/-! ## The non-recursive `bound_*` functions

Every function in this section is a branch of the `let rec … and …` group at
`free.ml:9-159`, but none of them calls a `free_*` function or descends past
the identifiers immediately under the node, so none of them needs to be part
of the mutual block below. -/

/-- `bound_iter` (`spectec/src/il/free.ml:14-17`).  Only `ListN`'s optional
index variable binds. -/
def boundIter : Iter → Sets
  | .opt | .list | .list1 => Sets.empty
  | .listN _ xo => freeOpt boundVarid xo

/-- `bound_varid ∘ fst` on one entry of an `iterexp`'s `(id * exp) list`
(`spectec/src/il/free.ml:92`).  `IL.Dom` is that pair. -/
def boundDom : Dom → Sets
  | .mk x _ => boundVarid x

/-- `free_list bound_varid (List.map fst xes)`
(`spectec/src/il/free.ml:92`). -/
def boundDoms : List Dom → Sets
  | [] => Sets.empty
  | d :: ds => (boundDom d).union (boundDoms ds)

/-- `bound_iterexp` (`spectec/src/il/free.ml:91-92`). -/
def boundIterExp : IterExp → Sets
  | .mk it doms => (boundIter it).union (boundDoms doms)

/-- `bound_typbind (x, _) = bound_varid x`
(`spectec/src/il/free.ml:39`). -/
def boundTypBind : TypBind → Sets
  | .mk x _ => boundVarid x

/-- `bound_typbinds = free_list bound_typbind`
(`spectec/src/il/free.ml:41`). -/
def boundTypBinds : List TypBind → Sets
  | [] => Sets.empty
  | b :: bs => (boundTypBind b).union (boundTypBinds bs)

/-- `bound_typ` (`spectec/src/il/free.ml:33-36`): only a tuple type binds, and
only the names of its components. -/
def boundTyp : Typ → Sets
  | .tupT binds => boundTypBinds binds
  | _ => Sets.empty

/-- `bound_param` (`spectec/src/il/free.ml:145-150`). -/
def boundParam : Param → Sets
  | .expP x _ => boundVarid x
  | .typP x => boundTypid x
  | .defP x _ _ => boundDefid x
  | .gramP x _ _ => boundGramid x

/-- `bound_params = free_list bound_param` (`spectec/src/il/free.ml:158`). -/
def boundParams : List Param → Sets
  | [] => Sets.empty
  | p :: ps => (boundParam p).union (boundParams ps)

/-- `bound_quant = bound_param` (`spectec/src/il/free.ml:153`).  `quant` is an
abbreviation for `param` (`spectec/src/il/ast.ml:129`), and `IL.Param` is used
for both. -/
def boundQuant : Param → Sets := boundParam

/-- `bound_quants = free_list bound_quant` (`spectec/src/il/free.ml:159`),
which is `bound_params`. -/
def boundQuants : List Param → Sets := boundParams

/-- `bound_prem` (`spectec/src/il/free.ml:117-120`).

**This is not a transcription.**  OCaml reads the quantifiers of a `LetPr`:
`bound_prem (LetPr (qs, _, _)) = bound_quants qs`.  `IL.Prem.letPr` has no
`qs` — `spectec/src/backend-ast/print.ml:165` prints a `LetPr` as
`(let e₁ e₂)` and drops them — so the only faithful reading of a decoded
`letPr` is `qs = []`, and `bound_quants [] = empty`.  Every branch therefore
returns `Sets.empty`; `boundPrem_eq_empty` records that, and
`freePrems_eq_freeList` records the one place it is observable, namely that
`freePrems` degenerates from `free_list_dep` to `free_list`.

The under-approximation is invisible at the top level, which is where the
recursion grouping looks: `bound_def` (`free.ml:205-212`) never calls
`bound_prem` or `free_prem` — it reads the name of a `TypD`/`RelD`/`DecD`/
`GramD` and recurses into a `RecD` — so `boundDef` below *is* a transcription.
What can change is `freeDef`: see its docstring. -/
def boundPrem : Prem → Sets
  | .letPr _ _ => Sets.empty
  | _ => Sets.empty

/-! ## The `let rec` group (`spectec/src/il/free.ml:9-159`)

Each `free_list f` and `free_list_dep f b` in `free.ml` becomes a specialised
traversal here, because Lean's structural recursion cannot see through a
higher-order call.  The `*_eq` lemmas below identify them with `freeList` and
`freeListDep`. -/

mutual

/-- `free_iter` (`spectec/src/il/free.ml:9-12`). -/
def freeIter : Iter → Sets
  | .opt | .list | .list1 => Sets.empty
  | .listN e _ => freeExp e

/-- `free_typ` (`spectec/src/il/free.ml:22-31`). -/
def freeTyp : Typ → Sets
  | .varT x args => (freeTypid x).union (freeArgs args)
  | .boolT => Sets.empty
  | .numT _ => Sets.empty
  | .textT => Sets.empty
  | .tupT binds => freeTypBinds binds
  | .iterT t it => (freeTyp t).union (freeIter it)

/-- `free_typbind (_, t) = free_typ t` (`spectec/src/il/free.ml:38`). -/
def freeTypBind : TypBind → Sets
  | .mk _ t => freeTyp t

/-- `free_typbinds = free_list_dep free_typbind bound_typbind`
(`spectec/src/il/free.ml:40`): a tuple type scopes left to right. -/
def freeTypBinds : List TypBind → Sets
  | [] => Sets.empty
  | b :: bs => (freeTypBind b).union ((freeTypBinds bs).diff (boundTypBind b))

/-- `free_deftyp` (`spectec/src/il/free.ml:43-47`). -/
def freeDefTyp : DefTyp → Sets
  | .aliasT t => freeTyp t
  | .structT fields => freeTypFields fields
  | .variantT cases => freeTypCases cases

/-- `free_typfield` (`spectec/src/il/free.ml:49-50`).  The OCaml reads
`free_typ t ++ (free_quants qs ++ (free_prems prems -- bound_quants qs) --
bound_typ t)`; `++` and `--` are left-associative and of equal precedence, so
`bound_typ t` is subtracted from the quantifiers as well as from the premises.
The trailing `hint list` that `free.ml:49` ignores is not in `IL.TypField`
either (`spectec/src/backend-ast/print.ml:89`). -/
def freeTypField : TypField → Sets
  | .mk _ t qs prems =>
    (freeTyp t).union
      (((freeParams qs).union ((freePrems prems).diff (boundParams qs))).diff (boundTyp t))

/-- `free_list free_typfield` (`spectec/src/il/free.ml:46`). -/
def freeTypFields : List TypField → Sets
  | [] => Sets.empty
  | f :: fs => (freeTypField f).union (freeTypFields fs)

/-- `free_typcase` (`spectec/src/il/free.ml:51-52`), which is `free_typfield`
on a `mixop` instead of an `atom`. -/
def freeTypCase : TypCase → Sets
  | .mk _ t qs prems =>
    (freeTyp t).union
      (((freeParams qs).union ((freePrems prems).diff (boundParams qs))).diff (boundTyp t))

/-- `free_list free_typcase` (`spectec/src/il/free.ml:47`). -/
def freeTypCases : List TypCase → Sets
  | [] => Sets.empty
  | c :: cs => (freeTypCase c).union (freeTypCases cs)

/-- `free_exp` (`spectec/src/il/free.ml:57-77`).

Two branches are spelled out rather than transcribed letter for letter, with
no change of meaning:

* `SliceE (e1, e2, e3) -> free_list free_exp [e1; e2; e3]` (`free.ml:68`)
  becomes the explicit `(freeExp e₁ ∪ freeExp e₂) ∪ freeExp e₃`, because a
  freshly built list is not a structural subterm; `freeExp_sliceE` proves the
  two equal.
* `CaseE (_, e1, _)` and `StrE (efs, _)` (`free.ml:72-73`) read a `check`
  flag that `IL.Exp` drops (`spectec/src/backend-ast/print.ml:111,120`), but
  `free_exp` ignores it, so nothing is lost. -/
def freeExp : Exp → Sets
  | .varE x => freeVarid x
  | .boolE _ => Sets.empty
  | .numE _ => Sets.empty
  | .textE _ => Sets.empty
  | .unE _ _ e => freeExp e
  | .liftE e => freeExp e
  | .lenE e => freeExp e
  | .projE e _ => freeExp e
  | .theE e => freeExp e
  | .binE _ _ e₁ e₂ => (freeExp e₁).union (freeExp e₂)
  | .cmpE _ _ e₁ e₂ => (freeExp e₁).union (freeExp e₂)
  | .idxE e₁ e₂ => (freeExp e₁).union (freeExp e₂)
  | .compE e₁ e₂ => (freeExp e₁).union (freeExp e₂)
  | .memE e₁ e₂ => (freeExp e₁).union (freeExp e₂)
  | .catE e₁ e₂ => (freeExp e₁).union (freeExp e₂)
  | .sliceE e₁ e₂ e₃ => ((freeExp e₁).union (freeExp e₂)).union (freeExp e₃)
  | .optE eo => freeExpOpt eo
  | .tupE es => freeExps es
  | .listE es => freeExps es
  | .updE e₁ p e₂ => ((freeExp e₁).union (freePath p)).union (freeExp e₂)
  | .extE e₁ p e₂ => ((freeExp e₁).union (freePath p)).union (freeExp e₂)
  | .strE fields => freeExpFields fields
  | .dotE e _ => freeExp e
  | .caseE _ e => freeExp e
  | .uncaseE e _ => freeExp e
  | .callE x args => (freeDefid x).union (freeArgs args)
  | .iterE e it => ((freeExp e).diff (boundIterExp it)).union (freeIterExp it)
  | .cvtE e _ _ => freeExp e
  | .subE e t₁ t₂ => ((freeExp e).union (freeTyp t₁)).union (freeTyp t₂)

/-- `free_opt free_exp` (`spectec/src/il/free.ml:69`). -/
def freeExpOpt : Option Exp → Sets
  | none => Sets.empty
  | some e => freeExp e

/-- `free_list free_exp` (`spectec/src/il/free.ml:68,70,89`). -/
def freeExps : List Exp → Sets
  | [] => Sets.empty
  | e :: es => (freeExp e).union (freeExps es)

/-- `free_expfield (_, e) = free_exp e` (`spectec/src/il/free.ml:79`). -/
def freeExpField : ExpField → Sets
  | .mk _ e => freeExp e

/-- `free_list free_expfield` (`spectec/src/il/free.ml:72`). -/
def freeExpFields : List ExpField → Sets
  | [] => Sets.empty
  | f :: fs => (freeExpField f).union (freeExpFields fs)

/-- `free_path` (`spectec/src/il/free.ml:81-86`). -/
def freePath : Path → Sets
  | .rootP => Sets.empty
  | .idxP p e => (freePath p).union (freeExp e)
  | .sliceP p e₁ e₂ => ((freePath p).union (freeExp e₁)).union (freeExp e₂)
  | .dotP p _ => freePath p

/-- `free_exp ∘ snd` on one entry of an `iterexp`'s `(id * exp) list`
(`spectec/src/il/free.ml:89`). -/
def freeDom : Dom → Sets
  | .mk _ e => freeExp e

/-- `free_list free_exp (List.map snd xes)`
(`spectec/src/il/free.ml:89`). -/
def freeDoms : List Dom → Sets
  | [] => Sets.empty
  | d :: ds => (freeDom d).union (freeDoms ds)

/-- `free_iterexp` (`spectec/src/il/free.ml:88-89`). -/
def freeIterExp : IterExp → Sets
  | .mk it doms => (freeIter it).union (freeDoms doms)

/-- `free_sym` (`spectec/src/il/free.ml:97-104`). -/
def freeSym : Sym → Sets
  | .varG x args => (freeGramid x).union (freeArgs args)
  | .numG _ => Sets.empty
  | .textG _ => Sets.empty
  | .epsG => Sets.empty
  | .seqG gs => freeSyms gs
  | .altG gs => freeSyms gs
  | .rangeG g₁ g₂ => (freeSym g₁).union (freeSym g₂)
  | .iterG g it => ((freeSym g).diff (boundIterExp it)).union (freeIterExp it)
  | .attrG e g => (freeExp e).union (freeSym g)

/-- `free_list free_sym` (`spectec/src/il/free.ml:101`). -/
def freeSyms : List Sym → Sets
  | [] => Sets.empty
  | g :: gs => (freeSym g).union (freeSyms gs)

/-- `free_prem` (`spectec/src/il/free.ml:109-115`).

**The `letPr` branch is not a transcription.**  OCaml has
`LetPr (qs, e1, e2) -> (free_exp e1 -- bound_quants qs) ++ free_exp e2`
(`free.ml:113`); `IL.Prem.letPr` carries no `qs`
(`spectec/src/backend-ast/print.ml:165`), so this computes with `qs = []` and
returns `freeExp e₁ ∪ freeExp e₂`.  Since `bound_quants qs ⊆` anything only
ever *removes* identifiers, `freePrem` is an **over**-approximation: for a
`LetPr` whose quantifiers are nonempty, our answer is OCaml's answer plus some
subset of `bound_quants qs`.  Exactly the same reading appears in SpecTec
itself at `spectec/src/il2al/free.ml:86`,
`| LetPr (_qs, e1, e2) -> f e1 ++ f e2`.

Whether it can matter: `free_def` *does* reach `free_prem`, so `freeDef` can
report identifiers OCaml's `free_def` does not, and
`spectec/src/frontend/elab.ml:2879-2887` builds the dependency graph out of
`free_def`, so in principle a spurious edge could merge two strongly connected
components, and the guard at `elab.ml:2895`,
`Il.Free.disjoint bounds.(i) frees.(i)`, could fail spuriously and wrap a
singleton in a `RecD`.  In practice it cannot arise from a `--ast` stream:
nothing in `src/frontend` or `src/middlend` builds a `LetPr`, so no printed
script contains one (the pinned streams in `specs/spectec/` have none).  Every
`LetPr` in SpecTec is built by the IL-to-AL passes — `il2al/animate.ml:303`,
`il2al/encode.ml:90,100,106,137,152` — which run after `--ast` printing.
And `bound_def` is unaffected either way; see `boundPrem`. -/
def freePrem : Prem → Sets
  | .rulePr x args _ e => ((freeRelid x).union (freeArgs args)).union (freeExp e)
  | .ifPr e => freeExp e
  | .letPr e₁ e₂ => (freeExp e₁).union (freeExp e₂)
  | .elsePr => Sets.empty
  | .iterPr pr it => ((freePrem pr).diff (boundIterExp it)).union (freeIterExp it)

/-- `free_prems = free_list_dep free_prem bound_prem`
(`spectec/src/il/free.ml:122`).  Because `boundPrem` is constantly
`Sets.empty` here (see its docstring), this is really a plain `free_list`;
`freePrems_eq_freeList` proves that. -/
def freePrems : List Prem → Sets
  | [] => Sets.empty
  | pr :: prs => (freePrem pr).union ((freePrems prs).diff (boundPrem pr))

/-- `free_arg` (`spectec/src/il/free.ml:127-132`). -/
def freeArg : Arg → Sets
  | .expA e => freeExp e
  | .typA t => freeTyp t
  | .defA x => freeDefid x
  | .gramA g => freeSym g

/-- `free_args = free_list free_arg` (`spectec/src/il/free.ml:155`). -/
def freeArgs : List Arg → Sets
  | [] => Sets.empty
  | a :: as_ => (freeArg a).union (freeArgs as_)

/-- `free_param` (`spectec/src/il/free.ml:134-143`).  A `DefP`/`GramP`
parameter is itself a binder: its own parameters scope over its result type. -/
def freeParam : Param → Sets
  | .expP _ t => freeTyp t
  | .typP _ => Sets.empty
  | .defP _ ps t => (freeParams ps).union ((freeTyp t).diff (boundParams ps))
  | .gramP _ ps t => (freeParams ps).union ((freeTyp t).diff (boundParams ps))

/-- `free_params = free_list_dep free_param bound_param`
(`spectec/src/il/free.ml:156`).  This is also `free_quants`
(`free.ml:152,157`): `free_quant = free_param`, so the two OCaml functions are
equal, and the mutual block above calls this one wherever `free.ml` writes
`free_quants`. -/
def freeParams : List Param → Sets
  | [] => Sets.empty
  | p :: ps => (freeParam p).union ((freeParams ps).diff (boundParam p))

end

/-! ## The definition level (`spectec/src/il/free.ml:161-203`)

`free_inst`, `free_rule`, `free_clause` and `free_prod` are separate `let`s in
OCaml, after the `let rec` group, because they only *call* it; the same holds
here.  `free_def` recurses through `RecD`, so it forms a two-element group
with its own list traversal. -/

/-- `free_inst` (`spectec/src/il/free.ml:161-164`). -/
def freeInst : Inst → Sets
  | .instD qs args dt =>
    (freeParams qs).union (((freeArgs args).union (freeDefTyp dt)).diff (boundParams qs))

/-- `free_list free_inst` (`spectec/src/il/free.ml:192`). -/
def freeInsts : List Inst → Sets
  | [] => Sets.empty
  | i :: is => (freeInst i).union (freeInsts is)

/-- `free_rule` (`spectec/src/il/free.ml:166-169`).  The rule's own name `_x`
is not reported, matching OCaml. -/
def freeRule : Rule → Sets
  | .ruleD _ qs _ e prems =>
    (freeParams qs).union (((freeExp e).union (freePrems prems)).diff (boundParams qs))

/-- `free_list free_rule` (`spectec/src/il/free.ml:195`). -/
def freeRules : List Rule → Sets
  | [] => Sets.empty
  | r :: rs => (freeRule r).union (freeRules rs)

/-- `free_clause` (`spectec/src/il/free.ml:171-174`). -/
def freeClause : Clause → Sets
  | .defD qs args e prems =>
    (freeParams qs).union
      ((((freeArgs args).union (freeExp e)).union (freePrems prems)).diff (boundParams qs))

/-- `free_list free_clause` (`spectec/src/il/free.ml:198`). -/
def freeClauses : List Clause → Sets
  | [] => Sets.empty
  | c :: cs => (freeClause c).union (freeClauses cs)

/-- `free_prod` (`spectec/src/il/free.ml:176-179`). -/
def freeProd : Prod → Sets
  | .prodD qs g e prems =>
    (freeParams qs).union
      ((((freeSym g).union (freeExp e)).union (freePrems prems)).diff (boundParams qs))

/-- `free_list free_prod` (`spectec/src/il/free.ml:201`). -/
def freeProds : List Prod → Sets
  | [] => Sets.empty
  | p :: ps => (freeProd p).union (freeProds ps)

mutual

/-- `free_def` (`spectec/src/il/free.ml:189-203`), without the `HintD` branch
(`free.ml:203`), which `IL.Def` has no constructor for.  In every branch the
definition's own name is *not* reported; that is what `bound_def` is for.

This is a transcription except through `freePrems`: see `freePrem` for the
`LetPr` deviation and for why it cannot be triggered by a `--ast` stream. -/
def freeDef : Def → Sets
  | .typD _ ps insts => (freeParams ps).union ((freeInsts insts).diff (boundParams ps))
  | .relD _ ps _ t rules =>
    (freeParams ps).union (((freeTyp t).union (freeRules rules)).diff (boundParams ps))
  | .decD _ ps t clauses =>
    (freeParams ps).union (((freeTyp t).union (freeClauses clauses)).diff (boundParams ps))
  | .gramD _ ps t prods =>
    (freeParams ps).union (((freeTyp t).union (freeProds prods)).diff (boundParams ps))
  | .recD ds => freeDefs ds

/-- `free_list free_def` (`spectec/src/il/free.ml:202`). -/
def freeDefs : List Def → Sets
  | [] => Sets.empty
  | d :: ds => (freeDef d).union (freeDefs ds)

end

/-! ## `bound_def` (`spectec/src/il/free.ml:205-212`)

Its own group: it recurses only through `Def`. -/

mutual

/-- `bound_def` (`spectec/src/il/free.ml:205-212`), without the `HintD` branch
(`free.ml:212`), which returns `empty` and which `IL.Def` has no constructor
for.  This *is* a transcription: `bound_def` never calls `bound_prem`, so the
`LetPr` erasure described in `boundPrem` cannot reach it. -/
def boundDef : Def → Sets
  | .typD x _ _ => boundTypid x
  | .relD x _ _ _ _ => boundRelid x
  | .decD x _ _ _ => boundDefid x
  | .gramD x _ _ _ => boundGramid x
  | .recD ds => boundDefs ds

/-- `free_list bound_def` (`spectec/src/il/free.ml:211`). -/
def boundDefs : List Def → Sets
  | [] => Sets.empty
  | d :: ds => (boundDef d).union (boundDefs ds)

end

/-- `free_quant = free_param` (`spectec/src/il/free.ml:152`). -/
def freeQuant : Param → Sets := freeParam

/-- `free_quants = free_list_dep free_quant bound_quant`
(`spectec/src/il/free.ml:157`), which is `free_params`. -/
def freeQuants : List Param → Sets := freeParams

/-! ## The algebra of `Sets`

Everything here is `Finset` componentwise, so the proofs are one `simp` each.
`union` is an idempotent commutative monoid with unit `Sets.empty`, `⊆` is a
preorder (in fact a partial order, inherited from `Finset`), and
`Sets.Disjoint` is symmetric. -/

namespace Sets

@[simp] theorem union_empty (s : Sets) : s.union empty = s := by
  cases s; simp [union, empty]

@[simp] theorem empty_union (s : Sets) : empty.union s = s := by
  cases s; simp [union, empty]

/-- `( ++ )` (`spectec/src/xl/gen_free.ml:45`) is associative. -/
theorem union_assoc (s₁ s₂ s₃ : Sets) :
    (s₁.union s₂).union s₃ = s₁.union (s₂.union s₃) := by
  simp [union, Finset.union_assoc]

/-- `( ++ )` (`spectec/src/xl/gen_free.ml:45`) is commutative. -/
theorem union_comm (s₁ s₂ : Sets) : s₁.union s₂ = s₂.union s₁ := by
  simp [union, Finset.union_comm]

/-- `( ++ )` (`spectec/src/xl/gen_free.ml:45`) is idempotent. -/
@[simp] theorem union_self (s : Sets) : s.union s = s := by
  simp [union]

/-- Left commutativity, the third lemma `simp` needs to normalise unions. -/
theorem union_left_comm (s₁ s₂ s₃ : Sets) :
    s₁.union (s₂.union s₃) = s₂.union (s₁.union s₃) := by
  rw [← union_assoc, ← union_assoc, union_comm s₁ s₂]

@[simp] theorem diff_empty (s : Sets) : s.diff empty = s := by
  simp [diff, empty]

@[simp] theorem empty_diff (s : Sets) : empty.diff s = empty := by
  simp [diff, empty]

@[simp] theorem inter_empty (s : Sets) : s.inter empty = empty := by
  simp [inter, empty]

/-- `subset` (`spectec/src/xl/gen_free.ml:49`) unfolded. -/
theorem subset_def {s₁ s₂ : Sets} :
    s₁ ⊆ s₂ ↔ s₁.typid ⊆ s₂.typid ∧ s₁.relid ⊆ s₂.relid ∧ s₁.varid ⊆ s₂.varid ∧
      s₁.defid ⊆ s₂.defid ∧ s₁.gramid ⊆ s₂.gramid := Iff.rfl

/-- `subset` (`spectec/src/xl/gen_free.ml:49`) is reflexive. -/
@[refl, simp] theorem Subset.refl (s : Sets) : s ⊆ s := by
  simp [subset_def]

/-- `subset` (`spectec/src/xl/gen_free.ml:49`) is transitive. -/
theorem Subset.trans {s₁ s₂ s₃ : Sets} (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₃) : s₁ ⊆ s₃ := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := subset_def.mp h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := subset_def.mp h₂
  exact subset_def.mpr ⟨a₁.trans a₂, b₁.trans b₂, c₁.trans c₂, d₁.trans d₂, e₁.trans e₂⟩

@[simp] theorem empty_subset (s : Sets) : empty ⊆ s := by
  simp [subset_def, empty]

@[simp] theorem subset_union_left (s₁ s₂ : Sets) : s₁ ⊆ s₁.union s₂ := by
  simp [subset_def, union]

@[simp] theorem subset_union_right (s₁ s₂ : Sets) : s₂ ⊆ s₁.union s₂ := by
  simp [subset_def, union]

/-- `( ++ )` (`gen_free.ml:45`) is monotone in both arguments. -/
theorem union_subset_union {s₁ s₂ s₃ s₄ : Sets} (h₁ : s₁ ⊆ s₂) (h₂ : s₃ ⊆ s₄) :
    s₁.union s₃ ⊆ s₂.union s₄ := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := subset_def.mp h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := subset_def.mp h₂
  exact subset_def.mpr ⟨Finset.union_subset_union a₁ a₂, Finset.union_subset_union b₁ b₂,
    Finset.union_subset_union c₁ c₂, Finset.union_subset_union d₁ d₂,
    Finset.union_subset_union e₁ e₂⟩

/-- `( -- )` (`gen_free.ml:47`) only ever removes identifiers. -/
@[simp] theorem diff_subset (s₁ s₂ : Sets) : s₁.diff s₂ ⊆ s₁ := by
  simp [subset_def, diff]

/-- `( -- )` (`gen_free.ml:47`) is monotone in its first argument. -/
theorem diff_subset_diff {s₁ s₂ : Sets} (s₃ : Sets) (h : s₁ ⊆ s₂) :
    s₁.diff s₃ ⊆ s₂.diff s₃ := by
  obtain ⟨a, b, c, d, e⟩ := subset_def.mp h
  exact subset_def.mpr ⟨Finset.sdiff_subset_sdiff a (le_refl _),
    Finset.sdiff_subset_sdiff b (le_refl _), Finset.sdiff_subset_sdiff c (le_refl _),
    Finset.sdiff_subset_sdiff d (le_refl _), Finset.sdiff_subset_sdiff e (le_refl _)⟩

/-- `disjoint` (`spectec/src/xl/gen_free.ml:56`) unfolded. -/
theorem disjoint_def {s₁ s₂ : Sets} :
    s₁.Disjoint s₂ ↔ _root_.Disjoint s₁.typid s₂.typid ∧ _root_.Disjoint s₁.relid s₂.relid ∧
      _root_.Disjoint s₁.varid s₂.varid ∧ _root_.Disjoint s₁.defid s₂.defid ∧
      _root_.Disjoint s₁.gramid s₂.gramid := Iff.rfl

/-- `disjoint` (`spectec/src/xl/gen_free.ml:56`) is symmetric. -/
theorem Disjoint.symm {s₁ s₂ : Sets} (h : s₁.Disjoint s₂) : s₂.Disjoint s₁ := by
  obtain ⟨a, b, c, d, e⟩ := disjoint_def.mp h
  exact disjoint_def.mpr ⟨a.symm, b.symm, c.symm, d.symm, e.symm⟩

/-- `disjoint` (`spectec/src/xl/gen_free.ml:56`) is symmetric. -/
theorem disjoint_comm {s₁ s₂ : Sets} : s₁.Disjoint s₂ ↔ s₂.Disjoint s₁ :=
  ⟨Disjoint.symm, Disjoint.symm⟩

@[simp] theorem empty_disjoint (s : Sets) : empty.Disjoint s := by
  simp [disjoint_def, empty]

@[simp] theorem disjoint_empty (s : Sets) : s.Disjoint empty := by
  simp [disjoint_def, empty]

end Sets

/-! ## `freeList` and `freeListDep` -/

@[simp] theorem freeList_nil {α : Type _} (f : α → Sets) : freeList f [] = Sets.empty := rfl

@[simp] theorem freeList_cons {α : Type _} (f : α → Sets) (x : α) (xs : List α) :
    freeList f (x :: xs) = (f x).union (freeList f xs) := rfl

@[simp] theorem freeListDep_nil {α : Type _} (f b : α → Sets) :
    freeListDep f b [] = Sets.empty := rfl

@[simp] theorem freeListDep_cons {α : Type _} (f b : α → Sets) (x : α) (xs : List α) :
    freeListDep f b (x :: xs) = (f x).union ((freeListDep f b xs).diff (b x)) := rfl

theorem freeList_append {α : Type _} (f : α → Sets) (xs ys : List α) :
    freeList f (xs ++ ys) = (freeList f xs).union (freeList f ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Sets.union_assoc]

/-- The accumulator form of `gen_free.ml:84`'s left fold. -/
theorem foldl_union_map {α : Type _} (f : α → Sets) (s : Sets) (xs : List α) :
    (xs.map f).foldl Sets.union s = s.union (freeList f xs) := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp [ih, Sets.union_assoc]

/-- `freeList` really is `gen_free.ml:84`'s
`List.fold_left (++) empty (List.map free_x xs)`.  The right recursion used
here is the same function because `union` is associative with unit
`Sets.empty`. -/
theorem freeList_eq_foldl {α : Type _} (f : α → Sets) (xs : List α) :
    freeList f xs = (xs.map f).foldl Sets.union Sets.empty := by
  rw [foldl_union_map, Sets.empty_union]

/-- `freeList` is monotone in its element function. -/
theorem freeList_mono {α : Type _} {f g : α → Sets} (h : ∀ x, f x ⊆ g x) (xs : List α) :
    freeList f xs ⊆ freeList g xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => exact Sets.union_subset_union (h x) ih

/-- `freeList` is monotone in its list: dropping elements can only shrink the
result. -/
theorem freeList_mono_sublist {α : Type _} (f : α → Sets) {xs ys : List α}
    (h : xs.Sublist ys) : freeList f xs ⊆ freeList f ys := by
  induction h with
  | slnil => simp
  | cons y _ ih => exact Sets.Subset.trans ih (Sets.subset_union_right _ _)
  | cons_cons x _ ih => exact Sets.union_subset_union (Sets.Subset.refl _) ih

/-- Appending to a list only grows `freeList`. -/
theorem freeList_subset_append_left {α : Type _} (f : α → Sets) (xs ys : List α) :
    freeList f xs ⊆ freeList f (xs ++ ys) :=
  freeList_mono_sublist f (List.sublist_append_left xs ys)

/-- `free_list_dep` (`gen_free.ml:86`) only ever removes identifiers that
`free_list` (`gen_free.ml:84`) would have reported. -/
theorem freeListDep_subset_freeList {α : Type _} (f b : α → Sets) (xs : List α) :
    freeListDep f b xs ⊆ freeList f xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact Sets.union_subset_union (Sets.Subset.refl _)
      (Sets.Subset.trans (Sets.diff_subset _ _) ih)

/-- `free_list_dep free_x bound_x` is `free_list free_x` whenever nothing
binds.  This is what the `--ast` erasure of `LetPr`'s quantifiers does to
`free_prems`; see `freePrems_eq_freeList`. -/
theorem freeListDep_eq_freeList {α : Type _} (f b : α → Sets)
    (hb : ∀ x, b x = Sets.empty) (xs : List α) : freeListDep f b xs = freeList f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [hb x, ih]

/-! ## The specialised list traversals are `freeList` and `freeListDep`

Each lemma discharges one of the specialisations the mutual block needed. -/

@[simp] theorem boundDoms_eq (ds : List Dom) : boundDoms ds = freeList boundDom ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [boundDoms, ih]

@[simp] theorem boundTypBinds_eq (bs : List TypBind) :
    boundTypBinds bs = freeList boundTypBind bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [boundTypBinds, ih]

@[simp] theorem boundParams_eq (ps : List Param) : boundParams ps = freeList boundParam ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [boundParams, ih]

@[simp] theorem freeTypBinds_eq (bs : List TypBind) :
    freeTypBinds bs = freeListDep freeTypBind boundTypBind bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [freeTypBinds, ih]

@[simp] theorem freeTypFields_eq (fs : List TypField) :
    freeTypFields fs = freeList freeTypField fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [freeTypFields, ih]

@[simp] theorem freeTypCases_eq (cs : List TypCase) :
    freeTypCases cs = freeList freeTypCase cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [freeTypCases, ih]

@[simp] theorem freeExps_eq (es : List Exp) : freeExps es = freeList freeExp es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [freeExps, ih]

@[simp] theorem freeExpOpt_eq (eo : Option Exp) : freeExpOpt eo = freeOpt freeExp eo := by
  cases eo <;> rfl

@[simp] theorem freeExpFields_eq (fs : List ExpField) :
    freeExpFields fs = freeList freeExpField fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [freeExpFields, ih]

@[simp] theorem freeDoms_eq (ds : List Dom) : freeDoms ds = freeList freeDom ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [freeDoms, ih]

@[simp] theorem freeSyms_eq (gs : List Sym) : freeSyms gs = freeList freeSym gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [freeSyms, ih]

@[simp] theorem freePrems_eq (prs : List Prem) :
    freePrems prs = freeListDep freePrem boundPrem prs := by
  induction prs with
  | nil => rfl
  | cons pr prs ih => simp [freePrems, ih]

@[simp] theorem freeArgs_eq (as_ : List Arg) : freeArgs as_ = freeList freeArg as_ := by
  induction as_ with
  | nil => rfl
  | cons a as_ ih => simp [freeArgs, ih]

@[simp] theorem freeParams_eq (ps : List Param) :
    freeParams ps = freeListDep freeParam boundParam ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [freeParams, ih]

@[simp] theorem freeInsts_eq (is : List Inst) : freeInsts is = freeList freeInst is := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [freeInsts, ih]

@[simp] theorem freeRules_eq (rs : List Rule) : freeRules rs = freeList freeRule rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [freeRules, ih]

@[simp] theorem freeClauses_eq (cs : List Clause) :
    freeClauses cs = freeList freeClause cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [freeClauses, ih]

@[simp] theorem freeProds_eq (ps : List Prod) : freeProds ps = freeList freeProd ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [freeProds, ih]

@[simp] theorem freeDefs_eq (ds : List Def) : freeDefs ds = freeList freeDef ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [freeDefs, ih]

@[simp] theorem boundDefs_eq (ds : List Def) : boundDefs ds = freeList boundDef ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [boundDefs, ih]

/-- `free_quants = free_params` (`spectec/src/il/free.ml:152,157`). -/
theorem freeQuants_eq_freeParams : freeQuants = freeParams := rfl

/-- `bound_quants = bound_params` (`spectec/src/il/free.ml:153,159`). -/
theorem boundQuants_eq_boundParams : boundQuants = boundParams := rfl

/-- `free.ml:68`'s `free_list free_exp [e1; e2; e3]`, which `freeExp` spells
out because a freshly built list is not a structural subterm. -/
theorem freeExp_sliceE (e₁ e₂ e₃ : Exp) :
    freeExp (.sliceE e₁ e₂ e₃) = freeExps [e₁, e₂, e₃] := by
  simp [freeExp, Sets.union_assoc]

/-! ## What the erasure of `LetPr`'s quantifiers does -/

/-- `boundPrem` is constantly `Sets.empty`, because `IL.Prem.letPr` has no
quantifiers to report (`spectec/src/backend-ast/print.ml:165`).  OCaml's
`bound_prem` (`free.ml:117-120`) is `bound_quants qs` on a `LetPr` and `empty`
everywhere else. -/
@[simp] theorem boundPrem_eq_empty (pr : Prem) : boundPrem pr = Sets.empty := by
  cases pr <;> rfl

/-- Consequently `free_prems`, which OCaml defines as a `free_list_dep`
(`free.ml:122`), degenerates to a plain `free_list` here: no premise can bind
anything for the premises after it. -/
theorem freePrems_eq_freeList (prs : List Prem) : freePrems prs = freeList freePrem prs := by
  simp [freeListDep_eq_freeList freePrem boundPrem boundPrem_eq_empty]

/-- The `letPr` branch of `freePrem`, stated on its own: OCaml computes
`(free_exp e1 -- bound_quants qs) ++ free_exp e2` (`free.ml:113`), and with
the quantifiers gone this is the `qs = []` instance. -/
theorem freePrem_letPr (e₁ e₂ : Exp) :
    freePrem (.letPr e₁ e₂) = (freeExp e₁).union (freeExp e₂) := rfl

/-! ## `bound_def`, computed (`spectec/src/il/free.ml:205-212`)

These five equations are the whole of `bound_def`, and they are what
`spectec/src/frontend/elab.ml:2872` feeds to the recursion grouping.  None of
them mentions a premise, an expression or a type, so the `LetPr` erasure
cannot reach them. -/

@[simp] theorem boundDef_typD (x : Id) (ps : List Param) (insts : List Inst) :
    boundDef (.typD x ps insts) = boundTypid x := rfl

@[simp] theorem boundDef_relD (x : Id) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) : boundDef (.relD x ps op t rules) = boundRelid x := rfl

@[simp] theorem boundDef_decD (x : Id) (ps : List Param) (t : Typ) (clauses : List Clause) :
    boundDef (.decD x ps t clauses) = boundDefid x := rfl

@[simp] theorem boundDef_gramD (x : Id) (ps : List Param) (t : Typ) (prods : List Prod) :
    boundDef (.gramD x ps t prods) = boundGramid x := rfl

@[simp] theorem boundDef_recD (ds : List Def) :
    boundDef (.recD ds) = freeList boundDef ds := by
  simp [boundDef]

/-! ## Examples

`Silmaril.SpecTec.Import`'s `spectec_def%` could build these from concrete
syntax, but it is a `meta` module and importing it here would make every
downstream user of `Free` depend on the elaborator, so the three definitions
below are written by hand.  Each equation is checked by `decide`, i.e. by the
kernel, through `DecidableEq (Finset String)`. -/

/-- `syntax valtype = I32 | REF reftype`, as a `TypD` with no parameters and a
single instance.  Its only free identifier is the type `reftype`. -/
def exValtype : Def :=
  .typD "valtype" []
    [.instD [] []
      (.variantT [.mk "I32" (.tupT []) [] [], .mk "REF" (.varT "reftype" []) [] []])]

/-- `def f(x : nat) : nat` with the single clause `f(x) = g(x)`.  `x` is bound
by the parameter list, so it is not free; `nat` and `g` are. -/
def exDec : Def :=
  .decD "f" [.expP "x" (.varT "nat" [])] (.varT "nat" [])
    [.defD [] [.expA (.varE "x")] (.callE "g" [.expA (.varE "x")]) []]

/-- The two definitions above as one recursive group. -/
def exRec : Def := .recD [exValtype, exDec]

example : boundDef exValtype = freeTypid "valtype" := by decide

example : freeDef exValtype = freeTypid "reftype" := by decide

example : boundDef exDec = freeDefid "f" := by decide

example : freeDef exDec = (freeTypid "nat").union (freeDefid "g") := by decide

example : boundDef exRec = (freeTypid "valtype").union (freeDefid "f") := by decide

example :
    freeDef exRec = (freeTypid "reftype").union ((freeTypid "nat").union (freeDefid "g")) := by
  decide

/-- The wildcard binds nothing (`spectec/src/xl/gen_free.ml:72-76`). -/
example : boundDef (.typD "_" [] []) = Sets.empty := by decide

/-- The `letPr` deviation, made concrete: OCaml would subtract the premise's
quantifiers from `freeExp e₁` and report them as bound. -/
example : freePrem (.letPr (.varE "x") (.varE "y")) = (freeVarid "x").union (freeVarid "y") := by
  decide

example : boundPrem (.letPr (.varE "x") (.varE "y")) = Sets.empty := by decide

end Silmaril.SpecTec.IL
