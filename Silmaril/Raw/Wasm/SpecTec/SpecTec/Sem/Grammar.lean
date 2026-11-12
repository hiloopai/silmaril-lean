module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Grammar.Basic
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval
public import Silmaril.Encoding.Unicode
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
-- `import all` is what lets the kernel see the *values* of the constants
-- `spectec_import` added, which is what `findGram_bbyte_wasm30` and
-- `findGram_bun_wasm30` are checked by.
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# SpecTec's `GramD` as an instance of the byte attribute-grammar framework

Step 5 of `docs/projects/spectec/README.md`.  `Silmaril/SpecTec/Grammar/Basic.lean`
is a generic framework of attribute grammars over byte terminals; this file
translates SpecTec's `sym'` (`spectec/src/il/ast.ml:101-110`) and `prod'`
(`ast.ml:153-154`) into it, so that an `IL.Script`'s grammars get a denotation
as an `EncRel (List UInt8) Value` and every theorem of the framework applies
to it verbatim.

## What a symbol denotes, according to `il/valid.ml`

`valid_sym` (`spectec/src/il/valid.ml:575-608`) gives every symbol a *type*:

| symbol | `valid_sym` | line |
| --- | --- | --- |
| `VarG (x, as)` | the grammar's type, with `as` substituted | 578-581 |
| `NumG _` | `NumT NatT` | 582-587 |
| `TextG _` | `TextT` | 588 |
| `EpsG` | `TupT []` | 589 |
| `SeqG gs` | `TupT []` | 590-592 |
| `AltG gs` | `TupT []` | 593-595 |
| `RangeG (g₁, g₂)` | `NumT NatT`, both operands `NumT NatT` | 596-601 |
| `IterG (g, ite)` | `IterT (t₁, it)`, `ite` checked `~side:`Lhs`` | 602-605 |
| `AttrG (e, g)` | `g`'s type, with `e` checked `~side:`Lhs`` | 606-608 |

Two things are decisive.  `AttrG`'s expression is checked as a **binding
pattern**, not as a computation, so its denotation uses `Sem/Eval.lean`'s
`matchExp`, not `evalExp`.  And an `IterG`'s `iterexp` domains are checked
`~side:`Lhs`` too (`valid.ml:207-221`): a domain `(x, e)` binds `x` *inside*
each round and matches the collected column against the pattern `e`
*outside*.

A production `ProdD (quants, g, e, prems)` (`ast.ml:154`) is validated by
`valid_prod` (`valid.ml:747-757`) in the order: derive `g` (755), check the
premises (756), evaluate the value expression `e` (757).  The denotation
below follows exactly that order.

## The impedance: attributes must be environment transformers

The framework's `Attr α` is a monoid `(nil, app)` with `ofByte`, and a
derivation's attribute is *synthesised*: in `appendRel`, the two factors'
attributes are chosen independently.  A naive choice of `α := Value` does not
work, because SpecTec grammars are genuinely **L-attributed**.  The witness is
`Blist` (`specification/wasm-3.0/5.1-binary.values.spectec:40-41`):

```
grammar Blist(grammar BX : el) : el* =
  | n:Bu32 (el:BX)^n => el^n
```

The repetition count of the second factor is bound by the first.  No
assignment of *values* to subderivations can express that, because the
framework's concatenation picks the second factor's byte string without
seeing the first factor's attribute.

The fix is to take the attribute to be an **environment transformer**:

```lean
abbrev Act : Type := VarEnv → List Value → VarEnv → Prop
```

`a ρ l ρ'` reads "started in scope `ρ`, this derivation contributes the values
`l` and leaves the scope `ρ'`".  `actApp` composes two of them by threading
the scope left to right and appending the value lists, and `actNil` is the
identity; those are a monoid (`actAlg`), so `Attr Act` is a legal instance of
the framework.  The dependency is then *resolved inside the attribute*: the
second factor's `Act` is a function of the scope the first factor produced, so
`(el:BX)^n` denotes an `Act` that is defined only at scopes where `n` has the
matching value, and `appendRel`'s independent choice of byte strings is
filtered by `actApp`.

The value list is a list rather than a single value because `SeqG` is
`TupT []`-typed: a sequence carries no value of its own, only the values its
factors contributed, in order.  `AttrG` and a `ProdD`'s value expression are
the two places that demand exactly one, and both check for it.

## Nonterminals

The framework's nonterminal type `N` is a parameter, so
`IL.Sym.varG x args` becomes `Sym.nt (x, args)` with

```lean
abbrev NT : Type := IL.Id × List IL.Arg
```

the identifier together with its **unevaluated** argument list.  The
arguments cannot be evaluated at translation time — `BuN(N-7)` names the
enclosing production's parameter — so each production's `Act` evaluates them
itself, in the scope it is applied at.  That is what makes the fixed,
syntactic production table of `Gram NT Act` correct for a parameterised
grammar: `Sym.nt ("BuN", [N-7])` is one nonterminal whose *meaning* at each
unfolding depends on the scope threaded into it.

Grammar-valued parameters are the one thing this cannot do, because
`Sym.nt`'s production list may not depend on the scope.  They are handled
syntactically instead, by `substSym`: `prodsOf` substitutes a call's `GramA`
arguments into the body before translating it, so `Blist(Bbyte)` has
`Sym.nt ("Bbyte", [])` where its body says `BX`.

## What fits, and what does not

The correspondence table in `Silmaril/SpecTec/Grammar/Basic.lean`'s module
docstring is accurate: every `IL.Sym` constructor maps to a framework
constructor, and the framework's `Sym` really was shaped to receive it.  The
places where the IL is wider, and what is done about each:

* `NumG n` with `n > 0xFF` — the Unicode scalar bounds of the UTF-8 grammar
  (`specs/spectec/wasm-3.0.ast` has `(num 0x10FFFF)`).  A byte grammar cannot
  derive one, so `transSym` sends it to `Sym.alt []`, which denotes `⊥`.
* `RangeG` over operands that are not `NumG` — likewise `⊥`.
* `TextG t` denotes the UTF-8 bytes of `t`, but contributes the *numerals* of
  those bytes rather than `TextT`'s text value, because the framework's
  `bytesRel` folds `Attr.ofByte`.  Nothing in the pinned corpus binds a
  `TextG` with an `AttrG`.
* `EpsG`, `SeqG` and `AltG` contribute *no* value rather than `TupT []`'s
  unit, since the empty list is the monoid unit.  So `AttrG (e, SeqG gs)`
  has no derivation.  It does not occur in the pinned corpus either.
* `ListN (e, Some x)`, an iteration whose counter is named, is not supported:
  the framework's `kleene` does not index its rounds, so there is nowhere to
  bind `x`.  `iterCount` requires the name to be absent.
* `substSym` descends through symbols and through the `GramA` arguments of a
  `VarG`, but not into the `Exp` or `Typ` arguments of one; a grammar passed
  inside a type-family argument would not be substituted.  No pinned
  specification does that.

## What is proved

* `gramRel` is the framework's `denoteAt` of the translated grammar, so
  `gramRel_mono` (monotone in the index) is `denoteAt_mono` and
  `gramRelSup_eq_iSup` is `denote_eq_iSup`.
* One compositionality equation per `IL.Sym` constructor (`symDen_epsG`,
  `symDen_numG`, …, `symDen_varG`), each an instance of the framework's.
* `symDen_mono_prods`: enlarging the production list of every grammar in the
  script enlarges every symbol's denotation — the lattice statement, with the
  evaluation environment held fixed so that only the production table varies.
* The worked instance: the pinned `Bbyte`/`BuN` definitions are taken out of
  `Specs.wasm30` (`findGram_bbyte_wasm30`, `findGram_bun_wasm30`, both by
  `rfl` against the imported stream), and
  `bun_iff_un : gramRelSup env ρ (BuN(W)) bs v ↔ ∃ m, UN W bs m ∧ v = %(m)`
  is proved **in both directions** (`bun_of_un`, `un_of_bun`), whence
  `bun_iff_lebGram`: the pinned grammar and `Grammar/Basic.lean`'s
  hand-written `lebGram` denote the same relation, and `unambiguous_bun`.

  `docs/projects/spectec-divergences.md` records errata #654, #655 and #656 against
  wasm-3.0 §5.1; the one it spells out, #655, is the continuation-byte range
  of the `$cont` function in the UTF-8 encoder, which is not part of `BuN`.
  Clause by clause the two `BuN` productions' premises *are* `UN`'s two
  constructors, so no erratum intervenes here and the equality holds as
  pinned — the brief's warning does not bite for this particular production.
-/

@[expose] public section

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Grammar

/-! ## The attribute algebra

`Act` is the attribute carried by a derivation: a relation between the scope
it starts in, the values it contributes, and the scope it leaves.  `actNil`
and `actApp` make it a monoid, which is what `Attr` asks for; `actByte` says
that a terminal contributes its own numeral, which is `valid_sym`'s
`NumG _ -> NumT NatT` (`spectec/src/il/valid.ml:582-587`). -/

/-- The attribute of a derivation: an environment transformer that also
reports the values its sub-derivations bound, in order. -/
abbrev Act : Type := VarEnv → List Value → VarEnv → Prop

/-- The attribute of the empty derivation: no values, no change of scope.
This is `EpsG : TupT []` (`spectec/src/il/valid.ml:589`). -/
def actNil : Act := fun ρ l ρ' => l = [] ∧ ρ' = ρ

/-- The attribute of a concatenation: thread the scope left to right and
append the value lists.  This is `SeqG : TupT []`
(`spectec/src/il/valid.ml:590-592`) together with the fact that the bindings
of an earlier factor are in scope for a later one. -/
def actApp (a b : Act) : Act :=
  fun ρ l ρ' => ∃ l₁ ρ₁ l₂, a ρ l₁ ρ₁ ∧ b ρ₁ l₂ ρ' ∧ l = l₁ ++ l₂

/-- The attribute of a terminal byte: the numeral of the byte, and no change
of scope (`spectec/src/il/valid.ml:582-587`). -/
def actByte (b : UInt8) : Act := fun ρ l ρ' => l = [.num (.natN b.toNat)] ∧ ρ' = ρ

/-- `actNil` is a left unit. -/
theorem actNil_app (a : Act) : actApp actNil a = a := by
  funext ρ l ρ'
  simp only [actApp, actNil, eq_iff_iff]
  constructor
  · rintro ⟨l₁, ρ₁, l₂, ⟨rfl, rfl⟩, h, rfl⟩
    simpa using h
  · intro h
    exact ⟨[], ρ, l, ⟨rfl, rfl⟩, h, rfl⟩

/-- `actNil` is a right unit. -/
theorem actApp_nil (a : Act) : actApp a actNil = a := by
  funext ρ l ρ'
  simp only [actApp, actNil, eq_iff_iff]
  constructor
  · rintro ⟨l₁, ρ₁, l₂, h, ⟨rfl, rfl⟩, rfl⟩
    simpa using h
  · intro h
    exact ⟨l, ρ', [], h, ⟨rfl, rfl⟩, by simp⟩

/-- `actApp` is associative. -/
theorem actApp_assoc (a b c : Act) : actApp (actApp a b) c = actApp a (actApp b c) := by
  funext ρ l ρ'
  simp only [actApp, eq_iff_iff]
  constructor
  · rintro ⟨_, ρ₂, l₃, ⟨l₁, ρ₁, l₂, h₁, h₂, rfl⟩, h₃, rfl⟩
    exact ⟨l₁, ρ₁, l₂ ++ l₃, h₁, ⟨l₂, ρ₂, l₃, h₂, h₃, rfl⟩, List.append_assoc ..⟩
  · rintro ⟨l₁, ρ₁, _, h₁, ⟨l₂, ρ₂, l₃, h₂, h₃, rfl⟩, rfl⟩
    exact ⟨l₁ ++ l₂, ρ₂, l₃, ⟨l₁, ρ₁, l₂, h₁, h₂, rfl⟩, h₃, (List.append_assoc ..).symm⟩

/-- The attribute algebra of every SpecTec grammar. -/
def actAlg : Attr Act where
  nil := actNil
  app := actApp
  ofByte := actByte
  nil_app := actNil_app
  app_nil := actApp_nil
  app_assoc := actApp_assoc

/-! ## Nonterminals -/

/-- A nonterminal of the translated grammar: a `gramid` together with the
*unevaluated* argument list of the `VarG` that named it
(`spectec/src/il/ast.ml:102`).  See the module docstring for why the
arguments stay syntactic. -/
abbrev NT : Type := IL.Id × List IL.Arg

/-! ## Grammar-valued parameters, as a syntactic substitution

`Sym.nt`'s production list may not depend on the scope, so a `GramP`
parameter (`spectec/src/il/ast.ml:127`) cannot be resolved at derivation
time.  It is resolved at translation time instead, by the same substitution
`spectec/src/il/subst.ml:210-228` performs. -/

/-- The grammar substitution a call's arguments induce: each `GramP`
parameter (`spectec/src/il/ast.ml:127`) paired with the `GramA` argument
(`ast.ml:119`) passed for it, positionally.  Parameters and arguments of the
other three forms are skipped — they are handled dynamically, by evaluating
the argument list in `prodAct`. -/
def gramArgSubst : List Param → List IL.Arg → List (IL.Id × IL.Sym)
  | .gramP x _ _ :: ps, .gramA g :: as => (x, g) :: gramArgSubst ps as
  | _ :: ps, _ :: as => gramArgSubst ps as
  | _, _ => []

/-- `Subst.subst_gramid` (`spectec/src/il/subst.ml:71-76`), total: a
parameterised nonterminal whose head is substituted keeps only the new head
name.  `subst.ml:75` raises `Invalid_argument` when the symbol bound to the
head is not a bare `VarG`; here the head is left alone instead, which cannot
happen for a well-formed script. -/
def substGramId (σ : List (IL.Id × IL.Sym)) (x : IL.Id) : IL.Id :=
  match List.lookup x σ with
  | some (.varG x' []) => x'
  | _ => x

mutual

/-- `Subst.subst_sym` (`spectec/src/il/subst.ml:210-228`), restricted to the
`gramid` namespace: `VarG (x, [])` with `x` substituted becomes the symbol
bound to it (`subst.ml:212-216`), and every other form is traversed.  The
`exp` of an `AttrG` and the `iterexp` of an `IterG` are *not* traversed,
because a grammar identifier cannot occur in either. -/
def substSym (σ : List (IL.Id × IL.Sym)) : IL.Sym → IL.Sym
  | .varG x [] =>
      match List.lookup x σ with
      | some g => g
      | none => .varG x []
  | .varG x args => .varG (substGramId σ x) (substArgs σ args)
  | .numG n => .numG n
  | .textG t => .textG t
  | .epsG => .epsG
  | .seqG gs => .seqG (substSyms σ gs)
  | .altG gs => .altG (substSyms σ gs)
  | .rangeG g₁ g₂ => .rangeG (substSym σ g₁) (substSym σ g₂)
  | .iterG g it => .iterG (substSym σ g) it
  | .attrG e g => .attrG e (substSym σ g)

/-- `Subst.subst_list Subst.subst_sym` (`spectec/src/il/subst.ml:220`). -/
def substSyms (σ : List (IL.Id × IL.Sym)) : List IL.Sym → List IL.Sym
  | [] => []
  | g :: gs => substSym σ g :: substSyms σ gs

/-- `List.map (Subst.subst_arg s)` (`spectec/src/il/subst.ml:217`), restricted
to the `GramA` arguments (`ast.ml:119`).  A grammar passed inside an `ExpA` or
`TypA` argument is left alone; see the module docstring. -/
def substArgs (σ : List (IL.Id × IL.Sym)) : List IL.Arg → List IL.Arg
  | [] => []
  | .gramA g :: as => .gramA (substSym σ g) :: substArgs σ as
  | a :: as => a :: substArgs σ as

end

/-! ## The actions

Each of the four actions below is the `f : α → Option α` of one `Sym.attr`
node.  They are total — `some` of a relation — because the partiality of
SpecTec's side conditions is expressed inside the `Act`, which is a relation
and may simply be empty at a given scope. -/

/-- `AttrG (e, g)` (`spectec/src/il/ast.ml:110`): derive `g`, which must
contribute exactly one value, pass that value on as this symbol's own
(`valid.ml:606-608`), and *match* `e` against it as a binding pattern
(`valid.ml:607`, `~side:`Lhs``), extending the scope. -/
def attrActFn (env : Env) (e : Exp) (a : Act) : Act :=
  fun ρ l ρ' => ∃ v ρ₁, a ρ [v] ρ₁ ∧ l = [v] ∧ MatchExp env ρ₁ e v ρ'

/-- `attrAct` is total: the partiality of a failed match lives in the `Act`,
which is a relation and may simply be empty. -/
def attrAct (env : Env) (e : Exp) (a : Act) : Option Act := some (attrActFn env e a)

/-- The value an iteration contributes: a list, or an option for `Opt`
(`spectec/src/il/valid.ml:602-605`, `IterT (t₁, it)`). -/
def iterValue : Iter → List Value → Value
  | .opt, vs => .opt vs.head?
  | _, vs => .list vs

/-- How many rounds an iterator admits in a given scope
(`spectec/src/il/ast.ml:16-20`).  `ListN (e, x)` evaluates its count in the
scope the iteration starts in — which, inside a `SeqG`, already contains the
bindings of the earlier factors; that is the L-attributed dependency the
module docstring describes.  A *named* `ListN` counter is not supported, so
`x` is required to be absent. -/
def IterCount (env : Env) (ρ : VarEnv) : Iter → Nat → Prop
  | .opt, k => k ≤ 1
  | .list, _ => True
  | .list1, k => 1 ≤ k
  | .listN e x, k => x = none ∧ ∃ v, EvalExp env ρ e v ∧ v.asNat? = some k

/-- One round of an `IterG` (`spectec/src/il/ast.ml:109`).  The round runs in
the scope the iteration starts in and *restores* it, so the rounds are
independent, as `eval.ml:406-415`'s substitution semantics makes them; what it
contributes instead is a single tuple of its own value together with the value
each `iterexp` domain variable (`ast.ml:95`) was bound to in that round. -/
def roundActFn (ds : List Dom) (a : Act) : Act :=
  fun ρ l ρ' => ρ' = ρ ∧ ∃ v ρ₁ vs, a ρ [v] ρ₁ ∧
    ds.mapM (fun d => ρ₁.findVal? (domVar d)) = some vs ∧ l = [.tuple (v :: vs)]

/-- `roundActFn`, as the action of a `Sym.attr`. -/
def roundAct (ds : List Dom) (a : Act) : Option Act := some (roundActFn ds a)

/-- The outward half of an `iterexp` (`spectec/src/il/ast.ml:95`): for each
domain `(x, e)`, the column of the values `x` took in the successive rounds is
collected into a list — or an option — and *matched* against the pattern `e`,
which `valid.ml:207-221` checks with `~side:`Lhs``.  The domains are threaded
left to right. -/
def BindDoms (env : Env) (it : Iter) :
    List Dom → List (List Value) → VarEnv → VarEnv → Prop
  | [], _, ρ, ρ' => ρ' = ρ
  | d :: ds, rows, ρ, ρ' =>
      ∃ ρ₁, MatchExp env ρ (domSrc d) (iterValue it (rows.filterMap (·.head?))) ρ₁ ∧
        BindDoms env it ds (rows.map List.tail) ρ₁ ρ'

/-- `IterG (g, (it, ds))` (`spectec/src/il/ast.ml:109`), as the action over
the framework's `Sym.star`: read the rounds off the Kleene closure's
attribute, check that there are as many as the iterator allows
(`IterCount`), contribute the list of their values, and bind the domains
outwards (`BindDoms`). -/
def iterActFn (env : Env) (it : Iter) (ds : List Dom) (a : Act) : Act :=
  fun ρ l ρ' => ∃ rows : List (Value × List Value),
    a ρ (rows.map fun r => .tuple (r.1 :: r.2)) ρ ∧
    IterCount env ρ it rows.length ∧
    l = [iterValue it (rows.map Prod.fst)] ∧
    BindDoms env it ds (rows.map Prod.snd) ρ ρ'

/-- `iterActFn`, as the action of a `Sym.attr`. -/
def iterAct (env : Env) (it : Iter) (ds : List Dom) (a : Act) : Option Act :=
  some (iterActFn env it ds a)

/-- `ProdD (quants, g, e, prems)` (`spectec/src/il/ast.ml:154`), in the order
`valid_prod` (`spectec/src/il/valid.ml:747-757`) checks it: evaluate the
call's arguments in the caller's scope, bind them to the grammar's parameters
in a *fresh* scope (`valid.ml:754`, where the quantifiers only declare the
types of the pattern variables), derive the symbol (`valid.ml:755`), check the
premises (`valid.ml:756`), and evaluate the value expression
(`valid.ml:757`).  The caller's scope is restored: a nonterminal binds
nothing outside itself. -/
def prodActFn (env : Env) (ps : List Param) (args : List IL.Arg) (e : Exp)
    (prems : List Prem) (a : Act) : Act :=
  fun ρ l ρ' => ρ' = ρ ∧ ∃ ws ρ₀ l₀ ρ₁ ρ₂ v,
    EvalArgs env ρ args ws ∧ bindParams VarEnv.empty ps ws = some ρ₀ ∧
    a ρ₀ l₀ ρ₁ ∧ PremsHold env ρ₁ prems ρ₂ ∧ EvalExp env ρ₂ e v ∧ l = [v]

/-- `prodActFn`, as the action of a `Sym.attr`. -/
def prodAct (env : Env) (ps : List Param) (args : List IL.Arg) (e : Exp)
    (prems : List Prem) (a : Act) : Option Act :=
  some (prodActFn env ps args e prems a)

/-! ## The translation -/

/-- `NumG n` (`spectec/src/il/ast.ml:103`) as a byte terminal.  `valid.ml:584`
would reject a value outside `[0x00, 0xFF]`, but that check is commented out
at this pin and the pinned UTF-8 grammar relies on it being absent; a
non-byte `NumG` denotes `⊥` here. -/
def byteSym (n : Nat) : Sym NT Act :=
  if n < 256 then .byte (UInt8.ofNat n) else .alt []

/-- `RangeG (g₁, g₂)` (`spectec/src/il/ast.ml:108`).  `valid.ml:596-601`
requires both operands to have type `NumT NatT` but not to be literals; only
the literal, byte-valued case is a byte terminal, and anything else denotes
`⊥`. -/
def rangeSym : IL.Sym → IL.Sym → Sym NT Act
  | .numG lo, .numG hi =>
      if lo < 256 ∧ hi < 256 then .range (UInt8.ofNat lo) (UInt8.ofNat hi) else .alt []
  | _, _ => .alt []

mutual

/-- `sym'` (`spectec/src/il/ast.ml:101-110`) as a symbol of the framework.
Constructor for constructor, this is the correspondence table in
`Silmaril/SpecTec/Grammar/Basic.lean`'s module docstring. -/
def transSym (env : Env) : IL.Sym → Sym NT Act
  | .varG x args => .nt (x, args)
  | .numG n => byteSym n
  | .textG t => .bytes (Unicode.utf8 t)
  | .epsG => .eps
  | .seqG gs => .seq (transSyms env gs)
  | .altG gs => .alt (transSyms env gs)
  | .rangeG g₁ g₂ => rangeSym g₁ g₂
  | .iterG g (.mk it ds) =>
      .attr (iterAct env it ds) (.star (.attr (roundAct ds) (transSym env g)))
  | .attrG e g => .attr (attrAct env e) (transSym env g)

/-- `List.map sym` (`spectec/src/il/ast.ml:106-107`). -/
def transSyms (env : Env) : List IL.Sym → List (Sym NT Act)
  | [] => []
  | g :: gs => transSym env g :: transSyms env gs

end

/-- `ProdD` (`spectec/src/il/ast.ml:154`) as a symbol: the production's body
headed by its `prodAct`, with the call's grammar arguments substituted in
first. -/
def transProd (env : Env) (ps : List Param) (args : List IL.Arg) :
    IL.Prod → Sym NT Act
  | .prodD _ g e prems =>
      .attr (prodAct env ps args e prems) (transSym env (substSym (gramArgSubst ps args) g))

/-- The production table of the translated grammar: the alternatives of the
nonterminal `(x, args)` are the `ProdD`s of the `GramD` named `x`
(`spectec/src/il/ast.ml:136`), translated.  A nonterminal the script does not
define has no productions and denotes `⊥`.

The table is taken from `envG` and the actions from `envE`, so that
`symDen_mono_prods` can vary the productions with the evaluation environment
held fixed. -/
def prodsOf (envE envG : Env) (n : NT) : List (Sym NT Act) :=
  match envG.findGram? n.1 with
  | none => []
  | some (ps, _, prods) => prods.map (transProd envE ps n.2)

/-- The translated grammar of a pair of environments; see `prodsOf`. -/
def gramOfEnvs (envE envG : Env) : Gram NT Act := ⟨actAlg, prodsOf envE envG⟩

/-- The translated grammar of a script's environment
(`Silmaril/SpecTec/Sem/Env.lean`'s `envOfScript`). -/
def gramOf (env : Env) : Gram NT Act := gramOfEnvs env env

/-! ## The denotation -/

/-- The denotation of an IL grammar symbol as an attribute relation: the
framework's `denote` of its translation. -/
def symDen (env : Env) (g : IL.Sym) : EncRel Bytes Act :=
  denote (gramOf env) (transSym env g)

/-- The denotation of an IL grammar symbol at derivation depth `n`:
`gramRel n env ρ g bs v` says that `g`, started in the scope `ρ`, derives the
byte string `bs` with value `v` by a derivation of depth below `n`.

This is the framework's `denoteAt` of the translation, applied at `ρ`, so
every theorem of `Silmaril/SpecTec/Grammar/Basic.lean` is available for it;
`gramRelSup` is the denotation proper. -/
def gramRel (n : Nat) (env : Env) (ρ : VarEnv) (g : IL.Sym) : EncRel Bytes Value :=
  fun bs v => ∃ (a : Act) (ρ' : VarEnv),
    denoteAt (gramOf env) n (transSym env g) bs a ∧ a ρ [v] ρ'

/-- The denotation of an IL grammar symbol: `gramRel` at any depth. -/
def gramRelSup (env : Env) (ρ : VarEnv) (g : IL.Sym) : EncRel Bytes Value :=
  fun bs v => ∃ (a : Act) (ρ' : VarEnv), symDen env g bs a ∧ a ρ [v] ρ'


/-- The denotation relative to a pair of environments, with the production
table taken from `envG`; `gramRelSup env = gramRelEnvs env env`.  This is the
form `gramRelEnvs_mono_prods` varies. -/
def gramRelEnvs (envE envG : Env) (ρ : VarEnv) (g : IL.Sym) : EncRel Bytes Value :=
  fun bs v => ∃ (a : Act) (ρ' : VarEnv),
    denote (gramOfEnvs envE envG) (transSym envE g) bs a ∧ a ρ [v] ρ'

/-- `gramRelSup` is `gramRelEnvs` with both environments the same. -/
theorem gramRelSup_eq_envs (env : Env) (ρ : VarEnv) (g : IL.Sym) :
    gramRelSup env ρ g = gramRelEnvs env env ρ g := rfl

/-! ## Monotonicity in the derivation depth -/

/-- `transSyms` is `List.map transSym`. -/
@[simp] theorem transSyms_eq_map (env : Env) (gs : List IL.Sym) :
    transSyms env gs = gs.map (transSym env) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [transSyms, ih]

/-- A deeper budget admits every derivation a shallower one does; this is the
framework's `denoteAt_mono`. -/
theorem gramRel_mono {m n : Nat} (h : m ≤ n) (env : Env) (ρ : VarEnv) (g : IL.Sym) :
    gramRel m env ρ g ≤ gramRel n env ρ g := by
  rintro bs v ⟨a, ρ', ha, hv⟩
  exact ⟨a, ρ', denoteAt_mono (gramOf env) h _ _ _ ha, hv⟩

/-- Every bounded-depth derivation is a derivation. -/
theorem gramRel_le_gramRelSup (n : Nat) (env : Env) (ρ : VarEnv) (g : IL.Sym) :
    gramRel n env ρ g ≤ gramRelSup env ρ g := by
  rintro bs v ⟨a, ρ', ha, hv⟩
  exact ⟨a, ρ', denoteAt_le_denote (gramOf env) n _ _ _ ha, hv⟩

/-- The denotation is the supremum of its bounded-depth approximants. -/
theorem gramRelSup_eq_iSup (env : Env) (ρ : VarEnv) (g : IL.Sym) :
    gramRelSup env ρ g = ⨆ n, gramRel n env ρ g := by
  apply le_antisymm
  · rintro bs v ⟨a, ρ', ha, hv⟩
    obtain ⟨n, hn⟩ := denote_apply.mp ha
    exact le_iSup (fun n => gramRel n env ρ g) n bs v ⟨a, ρ', hn, hv⟩
  · exact iSup_le fun n => gramRel_le_gramRelSup n env ρ g

/-! ## Compositionality

One equation per `sym'` constructor (`spectec/src/il/ast.ml:101-110`), each an
instance of the corresponding theorem of
`Silmaril/SpecTec/Grammar/Basic.lean`.  That they are instances rather than
fresh inductions is the point of translating into the framework instead of
defining the denotation directly. -/

/-- `EpsG` (`spectec/src/il/ast.ml:105`) derives the empty byte string. -/
theorem symDen_epsG (env : Env) : symDen env .epsG = epsRel actNil :=
  denote_eps (gramOf env)

/-- `NumG n` with `n` a byte (`spectec/src/il/ast.ml:103`) is a byte
terminal. -/
theorem symDen_numG (env : Env) {n : Nat} (h : n < 256) :
    symDen env (.numG n) = byteRel actAlg (UInt8.ofNat n) := by
  have hb : byteSym n = (Grammar.Sym.byte (UInt8.ofNat n) : Grammar.Sym NT Act) := by
    simp [byteSym, h]
  show denote (gramOf env) (byteSym n) = _
  rw [hb]
  exact denote_byte (gramOf env) _

/-- `NumG n` with `n` outside the byte range — a Unicode scalar bound of the
UTF-8 grammar — has no byte derivation. -/
theorem symDen_numG_of_not_lt (env : Env) {n : Nat} (h : ¬ n < 256) :
    symDen env (.numG n) = ⊥ := by
  have hb : byteSym n = (Grammar.Sym.alt [] : Grammar.Sym NT Act) := by
    simp [byteSym, h]
  show denote (gramOf env) (byteSym n) = _
  rw [hb, denote_alt]
  rfl

/-- `TextG t` (`spectec/src/il/ast.ml:104`) is the literal UTF-8 byte string
of `t`. -/
theorem symDen_textG (env : Env) (t : Text) :
    symDen env (.textG t) = bytesRel actAlg (Unicode.utf8 t) :=
  denote_bytes (gramOf env) _

/-- `SeqG gs` (`spectec/src/il/ast.ml:106`) is concatenation, which by the
choice of `actAlg` threads the scope left to right. -/
theorem symDen_seqG (env : Env) (gs : List IL.Sym) :
    symDen env (.seqG gs) = appendAll actAlg (gs.map (symDen env)) := by
  show denote (gramOf env) (.seq (transSyms env gs)) = _
  rw [denote_seq, transSyms_eq_map, List.map_map]
  rfl

/-- `AltG gs` (`spectec/src/il/ast.ml:107`) is the join in the lattice of
encodings. -/
theorem symDen_altG (env : Env) (gs : List IL.Sym) :
    symDen env (.altG gs) = supList (gs.map (symDen env)) := by
  show denote (gramOf env) (.alt (transSyms env gs)) = _
  rw [denote_alt, transSyms_eq_map, List.map_map]
  rfl

/-- `RangeG (NumG lo, NumG hi)` (`spectec/src/il/ast.ml:108`) with byte
bounds is a byte interval. -/
theorem symDen_rangeG (env : Env) {lo hi : Nat} (h : lo < 256 ∧ hi < 256) :
    symDen env (.rangeG (.numG lo) (.numG hi))
      = rangeRel actAlg (UInt8.ofNat lo) (UInt8.ofNat hi) := by
  have hb : rangeSym (.numG lo) (.numG hi)
      = (Grammar.Sym.range (UInt8.ofNat lo) (UInt8.ofNat hi) : Grammar.Sym NT Act) := by
    simp [rangeSym, h.1, h.2]
  show denote (gramOf env) (rangeSym (.numG lo) (.numG hi)) = _
  rw [hb]
  exact denote_range (gramOf env) _ _

/-- `AttrG (e, g)` (`spectec/src/il/ast.ml:110`) is `EncRel.mapPartial` of its
binding action. -/
theorem symDen_attrG (env : Env) (e : Exp) (g : IL.Sym) :
    symDen env (.attrG e g) = EncRel.mapPartial (attrAct env e) (symDen env g) :=
  denote_attr (gramOf env) _ _

/-- `IterG (g, (it, ds))` (`spectec/src/il/ast.ml:109`) is the Kleene closure
of one round, cut down by the iterator's arity and the outward binding of the
domains. -/
theorem symDen_iterG (env : Env) (g : IL.Sym) (it : Iter) (ds : List Dom) :
    symDen env (.iterG g (.mk it ds))
      = EncRel.mapPartial (iterAct env it ds)
          (kleene actAlg (EncRel.mapPartial (roundAct ds) (symDen env g))) := by
  show denote (gramOf env) (.attr (iterAct env it ds)
    (.star (.attr (roundAct ds) (transSym env g)))) = _
  rw [denote_attr, denote_star, denote_attr]
  rfl

/-- `VarG (x, args)` (`spectec/src/il/ast.ml:102`) is the join of the
translated productions of the grammar it names: the fixpoint equation. -/
theorem symDen_varG (env : Env) (x : IL.Id) (args : List IL.Arg) :
    symDen env (.varG x args)
      = supList ((prodsOf env env (x, args)).map (denote (gramOf env))) :=
  denote_nt (gramOf env) (x, args)

/-- `VarG (x, args)` unfolded against a `GramD` the script defines: the join
of its `ProdD`s, each headed by its `prodAct`. -/
theorem symDen_varG_of_findGram (env : Env) (x : IL.Id) (args : List IL.Arg)
    {ps : List Param} {t : Typ} {prods : List IL.Prod}
    (h : env.findGram? x = some (ps, t, prods)) :
    symDen env (.varG x args)
      = supList (prods.map fun p => denote (gramOf env) (transProd env ps args p)) := by
  rw [symDen_varG, prodsOf, h, List.map_map]
  rfl

/-- A nonterminal the script does not define has no derivation. -/
theorem symDen_varG_of_none (env : Env) (x : IL.Id) (args : List IL.Arg)
    (h : env.findGram? x = none) : symDen env (.varG x args) = ⊥ := by
  rw [symDen_varG, prodsOf, h]
  rfl

/-! ## Monotonicity in the script's productions

The lattice statement `docs/projects/spectec/README.md` asks for.  The production
table and the evaluation environment are separated by `gramOfEnvs`, so that
"more productions" can be said without also changing what `evalExp` and
`matchExp` see. -/

/-- `envG'` has at least the productions of `envG`, for every grammar, with
the same parameters and type. -/
def ProdsLe (envG envG' : Env) : Prop :=
  ∀ x ps t prods, envG.findGram? x = some (ps, t, prods) →
    ∃ prods', envG'.findGram? x = some (ps, t, prods') ∧ ∀ p ∈ prods, p ∈ prods'

/-- `ProdsLe` is reflexive. -/
theorem ProdsLe.refl (envG : Env) : ProdsLe envG envG :=
  fun _ _ _ prods h => ⟨prods, h, fun _ hp => hp⟩

/-- `ProdsLe` enlarges the translated production table pointwise. -/
theorem prodsOf_mono {envE envG envG' : Env} (h : ProdsLe envG envG') (n : NT) :
    ∀ g ∈ prodsOf envE envG n, g ∈ prodsOf envE envG' n := by
  intro g hg
  rw [prodsOf] at hg ⊢
  cases hfind : envG.findGram? n.1 with
  | none => rw [hfind] at hg; simp at hg
  | some d =>
    obtain ⟨ps, t, prods⟩ := d
    rw [hfind] at hg
    obtain ⟨prods', hfind', hsub⟩ := h n.1 ps t prods hfind
    rw [hfind']
    simp only [List.mem_map] at hg ⊢
    obtain ⟨p, hp, rfl⟩ := hg
    exact ⟨p, hsub p hp, rfl⟩

/-- Enlarging every grammar's production list enlarges every symbol's
denotation: the framework's `denote_mono_prods`, transported. -/
theorem symDen_mono_prods {envE envG envG' : Env} (h : ProdsLe envG envG')
    (g : IL.Sym) :
    denote (gramOfEnvs envE envG) (transSym envE g)
      ≤ denote (gramOfEnvs envE envG') (transSym envE g) :=
  denote_mono_prods (fun n => prodsOf_mono h n) _

/-- `gramRelEnvs` is monotone in the script's productions. -/
theorem gramRelEnvs_mono_prods {envE envG envG' : Env} (h : ProdsLe envG envG')
    (ρ : VarEnv) (g : IL.Sym) :
    gramRelEnvs envE envG ρ g ≤ gramRelEnvs envE envG' ρ g := by
  rintro bs v ⟨a, ρ', ha, hv⟩
  exact ⟨a, ρ', symDen_mono_prods h g _ _ ha, hv⟩


/-! ## Derivations, elementwise

`symDen` is an `EncRel Bytes Act`, which is the right thing for the framework
and an awkward thing to reason with: the `Act` is a function, so every
statement about a derivation carries an existential over it.  `SymDerives`
packages the existential together with the application, and the lemmas below
are the compositionality equations of `symDen` read at that level.  They are
what the worked instance is proved with. -/

/-- `SymDerives env ρ g bs l ρ'`: started in the scope `ρ`, the symbol `g`
derives the byte string `bs`, contributes the values `l`, and leaves the scope
`ρ'`. -/
def SymDerives (env : Env) (ρ : VarEnv) (g : IL.Sym) (bs : Bytes) (l : List Value)
    (ρ' : VarEnv) : Prop :=
  ∃ a : Act, symDen env g bs a ∧ a ρ l ρ'

/-- `gramRelSup` is `SymDerives` with a single contributed value. -/
theorem gramRelSup_iff {env : Env} {ρ : VarEnv} {g : IL.Sym} {bs : Bytes} {v : Value} :
    gramRelSup env ρ g bs v ↔ ∃ ρ', SymDerives env ρ g bs [v] ρ' := by
  constructor
  · rintro ⟨a, ρ', ha, hv⟩; exact ⟨ρ', a, ha, hv⟩
  · rintro ⟨ρ', a, ha, hv⟩; exact ⟨a, ρ', ha, hv⟩

/-- `EpsG`. -/
theorem symDerives_epsG {env : Env} {ρ ρ' : VarEnv} {bs : Bytes} {l : List Value} :
    SymDerives env ρ .epsG bs l ρ' ↔ bs = [] ∧ l = [] ∧ ρ' = ρ := by
  rw [SymDerives, symDen_epsG]
  constructor
  · rintro ⟨a, ⟨rfl, rfl⟩, hl, hρ⟩
    exact ⟨rfl, hl, hρ⟩
  · rintro ⟨rfl, hl, hρ⟩
    exact ⟨actNil, ⟨rfl, rfl⟩, hl, hρ⟩

/-- A byte terminal `NumG n`. -/
theorem symDerives_numG {env : Env} {ρ ρ' : VarEnv} {bs : Bytes} {l : List Value}
    {n : Nat} (h : n < 256) :
    SymDerives env ρ (.numG n) bs l ρ' ↔
      bs = [UInt8.ofNat n] ∧ l = [.num (.natN (UInt8.ofNat n).toNat)] ∧ ρ' = ρ := by
  rw [SymDerives, symDen_numG env h]
  constructor
  · rintro ⟨a, ⟨rfl, rfl⟩, hl, hρ⟩
    exact ⟨rfl, hl, hρ⟩
  · rintro ⟨rfl, hl, hρ⟩
    exact ⟨actByte (UInt8.ofNat n), ⟨rfl, rfl⟩, hl, hρ⟩

/-- A byte range `RangeG (NumG lo, NumG hi)`. -/
theorem symDerives_rangeG {env : Env} {ρ ρ' : VarEnv} {bs : Bytes} {l : List Value}
    {lo hi : Nat} (h : lo < 256 ∧ hi < 256) :
    SymDerives env ρ (.rangeG (.numG lo) (.numG hi)) bs l ρ' ↔
      ∃ b : UInt8, UInt8.ofNat lo ≤ b ∧ b ≤ UInt8.ofNat hi ∧ bs = [b] ∧
        l = [.num (.natN b.toNat)] ∧ ρ' = ρ := by
  rw [SymDerives, symDen_rangeG env h]
  constructor
  · rintro ⟨a, ⟨b, hlo, hhi, rfl, rfl⟩, hl, hρ⟩
    exact ⟨b, hlo, hhi, rfl, hl, hρ⟩
  · rintro ⟨b, hlo, hhi, rfl, hl, hρ⟩
    exact ⟨actByte b, ⟨b, hlo, hhi, rfl, rfl⟩, hl, hρ⟩

/-- The empty sequence. -/
theorem symDerives_seqG_nil {env : Env} {ρ ρ' : VarEnv} {bs : Bytes} {l : List Value} :
    SymDerives env ρ (.seqG []) bs l ρ' ↔ bs = [] ∧ l = [] ∧ ρ' = ρ := by
  rw [SymDerives, symDen_seqG]
  simp only [List.map_nil, appendAll_nil]
  constructor
  · rintro ⟨a, ⟨rfl, rfl⟩, hl, hρ⟩
    exact ⟨rfl, hl, hρ⟩
  · rintro ⟨rfl, hl, hρ⟩
    exact ⟨actNil, ⟨rfl, rfl⟩, hl, hρ⟩

/-- A nonempty sequence: the scope threads from the head into the tail, and
that is where SpecTec's L-attributed dependency lives. -/
theorem symDerives_seqG_cons {env : Env} {ρ ρ' : VarEnv} {bs : Bytes} {l : List Value}
    {g : IL.Sym} {gs : List IL.Sym} :
    SymDerives env ρ (.seqG (g :: gs)) bs l ρ' ↔
      ∃ b₁ l₁ ρ₁ b₂ l₂, SymDerives env ρ g b₁ l₁ ρ₁ ∧
        SymDerives env ρ₁ (.seqG gs) b₂ l₂ ρ' ∧ bs = b₁ ++ b₂ ∧ l = l₁ ++ l₂ := by
  rw [SymDerives, symDen_seqG]
  simp only [List.map_cons, appendAll_cons, ← symDen_seqG]
  constructor
  · rintro ⟨a, ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩, hl⟩
    obtain ⟨l₁, ρ₁, l₂, k₁, k₂, rfl⟩ := hl
    exact ⟨b₁, l₁, ρ₁, b₂, l₂, ⟨a₁, h₁, k₁⟩, ⟨a₂, h₂, k₂⟩, rfl, rfl⟩
  · rintro ⟨b₁, l₁, ρ₁, b₂, l₂, ⟨a₁, h₁, k₁⟩, ⟨a₂, h₂, k₂⟩, rfl, rfl⟩
    exact ⟨actApp a₁ a₂, ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩, l₁, ρ₁, l₂, k₁, k₂, rfl⟩

/-- An alternation. -/
theorem symDerives_altG {env : Env} {ρ ρ' : VarEnv} {bs : Bytes} {l : List Value}
    {gs : List IL.Sym} :
    SymDerives env ρ (.altG gs) bs l ρ' ↔ ∃ g ∈ gs, SymDerives env ρ g bs l ρ' := by
  rw [SymDerives, symDen_altG]
  constructor
  · rintro ⟨a, ha, hv⟩
    obtain ⟨E, hE, hb⟩ := supList_apply.mp ha
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
    exact ⟨g, hg, a, hb, hv⟩
  · rintro ⟨g, hg, a, ha, hv⟩
    exact ⟨a, supList_apply.mpr ⟨symDen env g, List.mem_map.mpr ⟨g, hg, rfl⟩, ha⟩, hv⟩

/-- `AttrG (e, g)`: derive `g`, which must contribute exactly one value, then
match `e` against it. -/
theorem symDerives_attrG {env : Env} {ρ ρ' : VarEnv} {bs : Bytes} {l : List Value}
    {e : Exp} {g : IL.Sym} :
    SymDerives env ρ (.attrG e g) bs l ρ' ↔
      ∃ v ρ₁, SymDerives env ρ g bs [v] ρ₁ ∧ l = [v] ∧ MatchExp env ρ₁ e v ρ' := by
  rw [SymDerives, symDen_attrG]
  constructor
  · rintro ⟨a, ⟨a₀, h₀, hf⟩, hv⟩
    rw [attrAct, Option.some_inj] at hf
    subst hf
    rw [attrActFn] at hv
    obtain ⟨v, ρ₁, hb, hl, hm⟩ := hv
    exact ⟨v, ρ₁, ⟨a₀, h₀, hb⟩, hl, hm⟩
  · rintro ⟨v, ρ₁, ⟨a₀, h₀, hb⟩, hl, hm⟩
    exact ⟨attrActFn env e a₀, ⟨a₀, h₀, rfl⟩, v, ρ₁, hb, hl, hm⟩

/-- One `ProdD` (`spectec/src/il/ast.ml:154`), read as a derivation: see
`prodAct`. -/
def ProdDerives (env : Env) (ρ : VarEnv) (ps : List Param) (args : List IL.Arg) :
    IL.Prod → Bytes → List Value → Prop
  | .prodD _ g e prems, bs, l =>
      ∃ ws ρ₀ l₀ ρ₁ ρ₂ v, EvalArgs env ρ args ws ∧
        bindParams VarEnv.empty ps ws = some ρ₀ ∧
        SymDerives env ρ₀ (substSym (gramArgSubst ps args) g) bs l₀ ρ₁ ∧
        PremsHold env ρ₁ prems ρ₂ ∧ EvalExp env ρ₂ e v ∧ l = [v]

/-- `VarG (x, args)`: the join of the grammar's productions, each run in a
fresh scope and leaving the caller's scope untouched. -/
theorem symDerives_varG {env : Env} {ρ ρ' : VarEnv} {bs : Bytes} {l : List Value}
    {x : IL.Id} {args : List IL.Arg} {ps : List Param} {t : Typ} {prods : List IL.Prod}
    (h : env.findGram? x = some (ps, t, prods)) :
    SymDerives env ρ (.varG x args) bs l ρ' ↔
      ρ' = ρ ∧ ∃ p ∈ prods, ProdDerives env ρ ps args p bs l := by
  rw [SymDerives, symDen_varG_of_findGram env x args h]
  constructor
  · rintro ⟨a, ha, hv⟩
    obtain ⟨E, hE, hb⟩ := supList_apply.mp ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hE
    obtain ⟨qs, g, e, prems⟩ := p
    rw [transProd, denote_attr] at hb
    obtain ⟨a₀, h₀, hf⟩ := hb
    rw [prodAct, Option.some_inj] at hf
    subst hf
    rw [prodActFn] at hv
    obtain ⟨hρ, ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, hb₀, hpr, hev, hl⟩ := hv
    exact ⟨hρ, _, hp, ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, ⟨a₀, h₀, hb₀⟩, hpr, hev, hl⟩
  · rintro ⟨hρ, p, hp, hd⟩
    obtain ⟨qs, g, e, prems⟩ := p
    obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, ⟨a₀, h₀, hb₀⟩, hpr, hev, hl⟩ := hd
    refine ⟨prodActFn env ps args e prems a₀,
      supList_apply.mpr ⟨_, List.mem_map.mpr ⟨_, hp, rfl⟩, ?_⟩, ?_⟩
    · rw [transProd, denote_attr]
      exact ⟨a₀, h₀, rfl⟩
    · exact ⟨hρ, ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, hb₀, hpr, hev, hl⟩


/-! ## Small inversions and constructions for the evaluator

`Silmaril/SpecTec/Sem/Eval.lean` states one `iff` per `evalExp` clause but
none for `evalExps`, `evalArgs`, `premsHold` or `matchExp`.  The worked
instance below needs only the handful of shapes the pinned grammar uses. -/

/-- `evalExps` of the empty list. -/
theorem evalExps_nil_eq (env : Env) (ρ : VarEnv) (n : Nat) :
    (evalExps (n + 1) env ρ [] : Res (List Value)) = .ok [] := by
  simp only [evalExps, List.mapM_nil]; rfl

/-- `evalExps` of a one-element list. -/
theorem evalExps_singleton_eq (env : Env) (ρ : VarEnv) (n : Nat) (e : Exp) :
    (evalExps (n + 1) env ρ [e] : Res (List Value)) = (fun v => [v]) <$> evalExp n env ρ e := by
  simp [evalExps, List.mapM_cons]

/-- A one-element tuple denotes the tuple of its component's denotation. -/
theorem evalExps_singleton {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ e v) : EvalExps env ρ [e] [v] := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by rw [evalExps_singleton_eq, h]; rfl⟩

/-- `evalArgs` of the empty list. -/
theorem evalArgs_nil_eq (env : Env) (ρ : VarEnv) (n : Nat) :
    (evalArgs (n + 1) env ρ [] : Res (List ArgV)) = .ok [] := by
  simp only [evalArgs, List.mapM_nil]; rfl

/-- An empty argument list evaluates to the empty list. -/
theorem evalArgs_nil (env : Env) (ρ : VarEnv) : EvalArgs env ρ [] [] :=
  ⟨1, evalArgs_nil_eq env ρ 0⟩

/-- `evalArgs` of a one-element `ExpA` list (`spectec/src/il/eval.ml:635`). -/
theorem evalArgs_expA_eq (env : Env) (ρ : VarEnv) (n : Nat) (e : Exp) :
    (evalArgs (n + 2) env ρ [.expA e] : Res (List ArgV))
      = (fun v => [ArgV.val v]) <$> evalExp n env ρ e := by
  simp [evalArgs, List.mapM_cons, evalArg]

/-- A one-element `ExpA` argument list evaluates its expression. -/
theorem evalArgs_expA {env : Env} {ρ : VarEnv} {e : Exp} {v : Value}
    (h : EvalExp env ρ e v) : EvalArgs env ρ [.expA e] [.val v] := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 2, by rw [evalArgs_expA_eq, h]; rfl⟩

/-- An empty argument list evaluates to the empty list, and only to it. -/
theorem evalArgs_nil_iff {env : Env} {ρ : VarEnv} {ws : List ArgV} :
    EvalArgs env ρ [] ws ↔ ws = [] := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [evalArgs] at h
    | succ n => rw [evalArgs_nil_eq] at h; exact (Except.ok.inj h).symm
  · rintro rfl; exact evalArgs_nil env _

/-- A one-element `ExpA` argument list, inverted. -/
theorem evalArgs_expA_iff {env : Env} {ρ : VarEnv} {e : Exp} {ws : List ArgV} :
    EvalArgs env ρ [.expA e] ws ↔ ∃ v, EvalExp env ρ e v ∧ ws = [.val v] := by
  constructor
  · rintro ⟨n, h⟩
    match n, h with
    | 0, h => simp [evalArgs] at h
    | 1, h => simp [evalArgs, List.mapM_cons, evalArg] at h
    | (n + 2), h =>
        rw [evalArgs_expA_eq] at h
        obtain ⟨v, hv, hw⟩ := Res.map_eq_ok.mp h
        exact ⟨v, ⟨n, hv⟩, hw.symm⟩
  · rintro ⟨v, hv, rfl⟩; exact evalArgs_expA hv

/-- No premises bind nothing, and nothing else. -/
theorem premsHold_nil_iff {env : Env} {ρ ρ' : VarEnv} : PremsHold env ρ [] ρ' ↔ ρ' = ρ := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => simp [premsHold] at h
    | succ n => rw [premsHold_nil_eq] at h; exact (Except.ok.inj h).symm
  · rintro rfl; exact premsHold_nil

/-- A single `IfPr` side condition, inverted. -/
theorem premsHold_ifPr_iff {env : Env} {ρ ρ' : VarEnv} {e : Exp} :
    PremsHold env ρ [.ifPr e] ρ' ↔ EvalExp env ρ e (.bool true) ∧ ρ' = ρ := by
  constructor
  · rintro ⟨n, h⟩
    match n, h with
    | 0, h => simp [premsHold] at h
    | 1, h => simp [premsHold_singleton_eq, premHolds] at h
    | (n + 2), h =>
        rw [premsHold_singleton_eq, premHolds] at h
        obtain ⟨v, hv, h⟩ := Res.bind_eq_ok.mp h
        rcases Decidable.em (v = Value.bool true) with hb | hb
        · subst hb
          rw [Res.assert_pos rfl] at h
          exact ⟨⟨n, hv⟩, (Except.ok.inj h).symm⟩
        · rw [Res.assert_neg hb] at h; simp at h
  · rintro ⟨hv, rfl⟩; exact premsHold_ifPr hv

/-- Matching a fresh variable binds it (`spectec/src/il/eval.ml:887-895`). -/
theorem matchExp_varE_of_none {env : Env} {ρ : VarEnv} {x : IL.Id} {v : Value}
    (h : ρ.findVal? x = none) : MatchExp env ρ (.varE x) v (ρ.bindVal x v) :=
  ⟨1, by simp [matchExp, h]⟩

/-- Matching the pattern `%(x)` against `%(w)` with `x` fresh
(`spectec/src/il/eval.ml:955-957,919`). -/
theorem matchExp_case_var {env : Env} {ρ : VarEnv} {op : MixopS} {x : IL.Id} {w : Value}
    (h : ρ.findVal? x = none) :
    MatchExp env ρ (.caseE op (.tupE [.varE x])) (.case op (.tuple [w])) (ρ.bindVal x w) :=
  ⟨4, by simp [matchExp, matchExps, Value.asCase?, Value.asTuple?, h]⟩

/-- Inverting the pattern `%(x)`: the value must be a `%`-injection of a
one-element tuple, and `x` is matched against its single field
(`spectec/src/il/eval.ml:955-957,919`).

The fuel is raised to `n + 4` first (`matchExp_ok_of_le`) so that all four
levels — `CaseE`, `TupE`, the list traversal and the variable — unfold at
once. -/
theorem matchExp_case_var_elim {env : Env} {ρ ρ' : VarEnv} {op : MixopS} {x : IL.Id}
    {v : Value} (h : MatchExp env ρ (.caseE op (.tupE [.varE x])) v ρ') :
    ∃ w, v = .case op (.tuple [w]) ∧ MatchExp env ρ (.varE x) w ρ' := by
  obtain ⟨n, h⟩ := h
  have h4 : matchExp (n + 4) env ρ (.caseE op (.tupE [.varE x])) v = .ok ρ' :=
    matchExp_ok_of_le (by omega) h
  clear h
  simp only [matchExp, Res.bind_eq_ok, Res.ofOption_eq_ok, Res.assert_eq_ok,
    Value.asTuple?_eq_some] at h4
  obtain ⟨⟨op', u⟩, hc, hop, vs, hu, h4⟩ := h4
  rw [Value.asCase?_eq_some] at hc
  subst hc
  subst hop
  subst hu
  rcases vs with _ | ⟨w, ws⟩
  · simp [matchExps] at h4
  · rcases ws with _ | ⟨w', ws⟩
    · simp only [matchExps, Res.bind_eq_ok] at h4
      obtain ⟨σ, hσ, h4⟩ := h4
      exact ⟨w, rfl, n + 1, by rw [show σ = ρ' from Except.ok.inj h4] at hσ; exact hσ⟩
    · simp [matchExps] at h4

/-- The value of the pinned `%(x)` expression. -/
theorem evalExp_case_var {env : Env} {ρ : VarEnv} {op : MixopS} {x : IL.Id} {w : Value}
    (h : ρ.findVal? x = some w) :
    EvalExp env ρ (.caseE op (.tupE [.varE x])) (.case op (.tuple [w])) :=
  evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr
    ⟨_, evalExps_singleton (evalExp_varE_iff.mpr h), rfl⟩, rfl⟩

/-- A numeric comparison, with the comparison itself supplied. -/
theorem evalExp_cmpE_num {env : Env} {ρ : VarEnv} {op : CmpOp} {t : OpTyp} {e₁ e₂ : Exp}
    {m₁ m₂ : Num} {r : Bool} (h₁ : EvalExp env ρ e₁ (.num m₁)) (h₂ : EvalExp env ρ e₂ (.num m₂))
    (hr : cmpValues op (.num m₁) (.num m₂) = .ok (.bool r)) :
    EvalExp env ρ (.cmpE op t e₁ e₂) (.bool r) := by
  rw [evalExp_cmpE_iff]
  exact ⟨.num m₁, .num m₂, h₁, h₂, hr⟩

/-- A numeric binary operation, with the operation itself supplied. -/
theorem evalExp_binE_num {env : Env} {ρ : VarEnv} {op : BinOp} {t : OpTyp} {e₁ e₂ : Exp}
    {m₁ m₂ m : Num} (h₁ : EvalExp env ρ e₁ (.num m₁)) (h₂ : EvalExp env ρ e₂ (.num m₂))
    (hr : Num.bin op m₁ m₂ = some m) :
    EvalExp env ρ (.binE op t e₁ e₂) (.num m) := by
  rw [evalExp_binE_iff]
  refine ⟨.num m₁, h₁, Or.inr ⟨?_, .num m₂, h₂, ?_⟩⟩
  · cases op <;> rfl
  · simp [binValues, hr]

/-- A numeric conversion, with the conversion itself supplied. -/
theorem evalExp_cvtE_num {env : Env} {ρ : VarEnv} {e : Exp} {t₁ t₂ : NumTyp} {m m' : Num}
    (h : EvalExp env ρ e (.num m)) (hr : Num.cvt t₂ m = some m') :
    EvalExp env ρ (.cvtE e t₁ t₂) (.num m') :=
  evalExp_cvtE_iff.mpr ⟨m, m', h, hr, rfl⟩


/-! ## A worked instance: the pinned LEB128 grammar

`specification/wasm-3.0/5.1-binary.values.spectec:7-11` at the pin is

```
grammar Bbyte : byte = 0x00 | ... | 0xFF

grammar BuN(N) : uN(N) =
  | n:Bbyte                 => n                       -- if $(n < 2^7 /\ n < 2^N)
  | n:Bbyte m:BuN(($(N-7))) => $(2^7 * m + (n - 2^7))  -- if $(n >= 2^7 /\ N > 7)
```

`Silmaril/SpecTec/Grammar/Basic.lean` writes that grammar by hand as `lebGram`
and proves `denote lebGram (.nt W) bs [m] ↔ Wasm.Binary.UN W bs m`.  Here the
*pinned* definitions are taken out of `Specs.wasm30`, translated by `transSym`,
and compared with the same `UN`.

The two are not translations of each other symbol for symbol, and `lebGram` is
not wrong about it — it is a deliberate flattening:

* `lebP1`'s terminal is `Sym.range 0x00 0x7F`, where the pinned production
  derives the *nonterminal* `Bbyte`, whose own production is the full range
  `0x00 | ... | 0xFF`, and puts `n < 2^7` in the premise instead;
* `lebGram`'s nonterminals are the widths `W`, where the pinned grammar has one
  nonterminal `BuN` with `N` an `ExpP` parameter, so that `BuN(N-7)` is the
  *same* `Sym.nt` with a different scope;
* `lebGram`'s attributes are `List Nat`, where the pinned grammar's value is
  `uN(N)`'s `%(n)`, i.e. `numCase n`.

So the comparison is semantic, and the statement below is that of
`denote_leb_nt_iff` transported along `numCase`. -/

section Leb

open Silmaril.Wasm.Binary

set_option maxRecDepth 1000000

/-- `2 ^ e`, the IL expression the pinned productions use for the bounds. -/
def twoPowE (e : Exp) : Exp := .binE .powOp (.numT .natT) (.numE (.natN 2)) e

/-- SpecTec's `%(k)`: the value of the one-field variant `byte` and `uN(N)`
both are at this pin. -/
def numCase (k : Nat) : Value := .case "%" (.tuple [.num (.natN k)])

/-- The sole production of `grammar Bbyte : byte = 0x00 | ... | 0xFF`
(`specification/wasm-3.0/5.1-binary.values.spectec:7`), as elaborated. -/
def bbyteProds : List IL.Prod :=
  [ .prodD [.expP "<implicit-prod-result>" (.numT .natT)]
      (.attrG (.varE "<implicit-prod-result>") (.rangeG (.numG 0x00) (.numG 0xFF)))
      (.caseE "%" (.tupE [.varE "<implicit-prod-result>"])) [] ]

/-- The parameter list of `grammar BuN(N)`
(`specification/wasm-3.0/5.1-binary.values.spectec:9`). -/
def bunParams : List Param := [.expP "N" (.varT "N" [])]

/-- The type of `grammar BuN(N) : uN(N)`. -/
def bunTyp : Typ := .varT "uN" [.expA (.varE "N")]

/-- The two productions of `grammar BuN(N)`
(`specification/wasm-3.0/5.1-binary.values.spectec:10-11`), as elaborated. -/
def bunProds : List IL.Prod :=
  [ .prodD [.expP "n" (.varT "n" [])]
      (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" []))
      (.caseE "%" (.tupE [.varE "n"]))
      [ .ifPr (.binE .andOp .boolT
          (.cmpE .ltOp (.numT .natT) (.varE "n") (twoPowE (.numE (.natN 7))))
          (.cmpE .ltOp (.numT .natT) (.varE "n") (twoPowE (.varE "N")))) ],
    .prodD [.expP "m" (.varT "m" []), .expP "n" (.varT "n" [])]
      (.seqG [ .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])],
               .seqG [.attrG (.caseE "%" (.tupE [.varE "m"]))
                        (.varG "BuN" [.expA (.cvtE (.binE .subOp (.numT .intT)
                            (.cvtE (.varE "N") .natT .intT)
                            (.cvtE (.numE (.natN 7)) .natT .intT)) .intT .natT)])] ])
      (.caseE "%" (.tupE [ .binE .addOp (.numT .natT)
          (.binE .mulOp (.numT .natT) (twoPowE (.numE (.natN 7))) (.varE "m"))
          (.cvtE (.binE .subOp (.numT .intT)
            (.cvtE (.varE "n") .natT .intT)
            (.cvtE (twoPowE (.numE (.natN 7))) .natT .intT)) .intT .natT) ]))
      [ .ifPr (.binE .andOp .boolT
          (.cmpE .geOp (.numT .natT) (.varE "n") (twoPowE (.numE (.natN 7))))
          (.cmpE .gtOp (.numT .natT) (.varE "N") (.numE (.natN 7)))) ] ]

/-- Provenance: `bbyteProds` is what the pinned wasm-3.0 stream contains.  The
`rfl` is checked by the kernel against `Specs.wasm30`, whose 749th definition
is the `GramD` for `Bbyte`. -/
private theorem findGram_bbyte_wasm30 :
    (envOfScript Specs.wasm30).findGram? "Bbyte"
      = some ([], .varT "byte" [], bbyteProds) := rfl

/-- Provenance: `bunParams`, `bunTyp` and `bunProds` are what the pinned
wasm-3.0 stream contains; the `GramD` for `BuN` is the sole member of the
750th top-level definition, a `RecD` group. -/
private theorem findGram_bun_wasm30 :
    (envOfScript Specs.wasm30).findGram? "BuN" = some (bunParams, bunTyp, bunProds) := rfl

/-- The hypotheses the comparison needs of an environment: it defines `Bbyte`
and `BuN` as the pinned stream does.  `envOfScript Specs.wasm30` satisfies
them (`hasLeb_wasm30`), and stating the results this way keeps the proofs
independent of the other 974 definitions. -/
structure HasLeb (env : Env) : Prop where
  /-- `Bbyte` is the pinned one. -/
  bbyte : env.findGram? "Bbyte" = some ([], .varT "byte" [], bbyteProds)
  /-- `BuN` is the pinned one. -/
  bun : env.findGram? "BuN" = some (bunParams, bunTyp, bunProds)

/-- The pinned wasm-3.0 environment has the pinned LEB128 grammar. -/
theorem hasLeb_wasm30 : HasLeb (envOfScript Specs.wasm30) :=
  ⟨findGram_bbyte_wasm30, findGram_bun_wasm30⟩

/-- `Bbyte` derives every single byte, with the `byte` value of that byte, and
binds nothing outside itself. -/
theorem bbyte_derives {env : Env} (h : HasLeb env) (ρ : VarEnv) (b : UInt8) :
    SymDerives env ρ (.varG "Bbyte" []) [b] [numCase b.toNat] ρ := by
  rw [symDerives_varG h.bbyte]
  refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
  refine ⟨[], VarEnv.empty, [Value.num (.natN b.toNat)],
    VarEnv.empty.bindVal "<implicit-prod-result>" (.num (.natN b.toNat)),
    VarEnv.empty.bindVal "<implicit-prod-result>" (.num (.natN b.toNat)),
    numCase b.toNat, evalArgs_nil env ρ, rfl, ?_, premsHold_nil, ?_, rfl⟩
  · show SymDerives env VarEnv.empty
      (.attrG (.varE "<implicit-prod-result>") (.rangeG (.numG 0x00) (.numG 0xFF))) _ _ _
    rw [symDerives_attrG]
    refine ⟨.num (.natN b.toNat), VarEnv.empty, ?_, rfl, matchExp_varE_of_none rfl⟩
    rw [symDerives_rangeG ⟨by omega, by omega⟩]
    refine ⟨b, ?_, ?_, rfl, rfl, rfl⟩
    · show (0x00 : UInt8) ≤ b
      exact Grammar.zero_le_uint8 b
    · show b ≤ (0xFF : UInt8)
      exact Grammar.le_FF_uint8 b
  · exact evalExp_case_var rfl

/-- `Xl.Num.cvt` back from `int` to `nat` on a non-negative integer
(`spectec/src/xl/num.ml:86`). -/
theorem cvt_natT_intN {i : Int} {k : Nat} (h : 0 ≤ i) (hk : i.toNat = k) :
    Num.cvt .natT (.intN i) = some (.natN k) := by
  subst hk
  simp [Num.cvt, h]

/-- `2 ^ e` denotes `2 ^ k` when `e` denotes `k`. -/
theorem evalExp_twoPowE {env : Env} {ρ : VarEnv} {e : Exp} {k : Nat}
    (h : EvalExp env ρ e (.num (.natN k))) :
    EvalExp env ρ (twoPowE e) (.num (.natN (2 ^ k))) :=
  evalExp_binE_num (evalExp_numE_iff.mpr rfl) h rfl

/-- The fresh scope a `BuN(N)` production is derived in: its one parameter,
bound to the width. -/
def bunScope (W : Nat) : VarEnv := VarEnv.empty.bindVal "N" (.num (.natN W))

/-- `bunScope` after the first factor has bound `n`. -/
def bunScopeN (W k : Nat) : VarEnv := (bunScope W).bindVal "n" (.num (.natN k))

/-- `bunScopeN` after the second factor has bound `m`. -/
def bunScopeM (W k m : Nat) : VarEnv := (bunScopeN W k).bindVal "m" (.num (.natN m))

/-- `N` is in scope throughout. -/
theorem findVal_bunScope_N (W : Nat) : (bunScope W).findVal? "N" = some (.num (.natN W)) := rfl

/-- `n` is not yet bound when the first factor runs. -/
theorem findVal_bunScope_n (W : Nat) : (bunScope W).findVal? "n" = none := rfl

/-- `N` is still in scope after `n` is bound. -/
theorem findVal_bunScopeN_N (W k : Nat) :
    (bunScopeN W k).findVal? "N" = some (.num (.natN W)) := rfl

/-- `n` is in scope after the first factor. -/
theorem findVal_bunScopeN_n (W k : Nat) :
    (bunScopeN W k).findVal? "n" = some (.num (.natN k)) := rfl

/-- `m` is not yet bound when the second factor runs. -/
theorem findVal_bunScopeN_m (W k : Nat) : (bunScopeN W k).findVal? "m" = none := rfl

/-- `N` is still in scope after `m` is bound. -/
theorem findVal_bunScopeM_N (W k m : Nat) :
    (bunScopeM W k m).findVal? "N" = some (.num (.natN W)) := rfl

/-- `n` is still in scope after `m` is bound. -/
theorem findVal_bunScopeM_n (W k m : Nat) :
    (bunScopeM W k m).findVal? "n" = some (.num (.natN k)) := rfl

/-- `m` is in scope after the second factor. -/
theorem findVal_bunScopeM_m (W k m : Nat) :
    (bunScopeM W k m).findVal? "m" = some (.num (.natN m)) := rfl

/-- `Bbyte` derives *nothing but* single bytes, and the value it gives is the
`byte` value of the byte it read. -/
theorem bbyte_elim {env : Env} (h : HasLeb env) {ρ ρ' : VarEnv} {bs : Grammar.Bytes}
    {l : List Value} (hd : SymDerives env ρ (.varG "Bbyte" []) bs l ρ') :
    ∃ b : UInt8, bs = [b] ∧ l = [numCase b.toNat] ∧ ρ' = ρ := by
  rw [symDerives_varG h.bbyte] at hd
  obtain ⟨hρ, p, hp, hpd⟩ := hd
  simp only [bbyteProds, List.mem_singleton] at hp
  subst hp
  obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v, hargs, hbp, hbody, hprems, heval, hl⟩ := hpd
  rw [evalArgs_nil_iff] at hargs
  subst hargs
  have hρ₀ : ρ₀ = VarEnv.empty := by
    have hb : (some VarEnv.empty : Option VarEnv) = some ρ₀ := hbp
    exact (Option.some_inj.mp hb).symm
  subst hρ₀
  replace hbody : SymDerives env VarEnv.empty
      (.attrG (.varE "<implicit-prod-result>") (.rangeG (.numG 0x00) (.numG 0xFF)))
      bs l₀ ρ₁ := hbody
  rw [symDerives_attrG] at hbody
  obtain ⟨v₁, ρa, hrange, -, hm⟩ := hbody
  rw [symDerives_rangeG ⟨by omega, by omega⟩] at hrange
  obtain ⟨b, -, -, rfl, hv₁, rfl⟩ := hrange
  have hv₁' : v₁ = .num (.natN b.toNat) := by simpa using hv₁
  subst hv₁'
  have hρ₁ : ρ₁ = VarEnv.empty.bindVal "<implicit-prod-result>" (.num (.natN b.toNat)) :=
    MatchExp.unique hm (matchExp_varE_of_none rfl)
  subst hρ₁
  rw [premsHold_nil_iff] at hprems
  subst hprems
  have hv : v = numCase b.toNat := EvalExp.unique heval (evalExp_case_var rfl)
  exact ⟨b, rfl, by rw [hl, hv], hρ⟩

/-- The argument expression of the recursive call `BuN($(N-7))`
(`specification/wasm-3.0/5.1-binary.values.spectec:11`), as elaborated. -/
def bunRecArg : Exp :=
  .cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "N") .natT .intT)
    (.cvtE (.numE (.natN 7)) .natT .intT)) .intT .natT

/-- `N` survives an arbitrary binding of `m`. -/
theorem findVal_bindM_N (W k : Nat) (w : Value) :
    ((bunScopeN W k).bindVal "m" w).findVal? "N" = some (.num (.natN W)) := rfl

/-- `n` survives an arbitrary binding of `m`. -/
theorem findVal_bindM_n (W k : Nat) (w : Value) :
    ((bunScopeN W k).bindVal "m" w).findVal? "n" = some (.num (.natN k)) := rfl

/-- Every byte string the hand-written `Silmaril.Wasm.Binary.UN` accepts is
derived by the *pinned* `BuN`, with the matching `uN(N)` value `%(m)`.

The width is carried by an arbitrary expression `eN` denoting it rather than
by a literal, because the recursive production calls `BuN($(N-7))` and the
induction has to apply the hypothesis to that expression. -/
theorem bun_of_un {env : Env} (h : HasLeb env) :
    ∀ {W : Nat} {bs : Grammar.Bytes} {m : Nat}, UN W bs m →
      ∀ (ρ : VarEnv) (eN : Exp), EvalExp env ρ eN (.num (.natN W)) →
        SymDerives env ρ (.varG "BuN" [.expA eN]) bs [numCase m] ρ := by
  intro W bs m hu
  induction hu with
  | @byte W n h₁ h₂ =>
      intro ρ eN heN
      rw [symDerives_varG h.bun]
      refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
      refine ⟨[.val (.num (.natN W))], bunScope W, [numCase n.toNat],
        bunScopeN W n.toNat, bunScopeN W n.toNat, numCase n.toNat,
        evalArgs_expA heN, rfl, ?_, ?_, ?_, rfl⟩
      · show SymDerives env (bunScope W)
          (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])) _ _ _
        rw [symDerives_attrG]
        exact ⟨numCase n.toNat, bunScope W, bbyte_derives h _ n, rfl,
          matchExp_case_var (findVal_bunScope_n W)⟩
      · refine premsHold_ifPr (evalExp_and_true ?_ ?_)
        · refine evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat))
            (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) ?_
          simp [cmpValues, Num.cmp, h₁]
        · refine evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat))
            (evalExp_twoPowE (evalExp_varE_iff.mpr (findVal_bunScopeN_N W n.toNat))) ?_
          simp [cmpValues, Num.cmp, h₂]
      · rw [numCase, evalExp_caseE_iff]
        exact ⟨_, evalExp_tupE_iff.mpr ⟨_,
          evalExps_singleton (evalExp_varE_iff.mpr (findVal_bunScopeN_n W n.toNat)), rfl⟩, rfl⟩
  | @cont W n b m h₁ h₂ _rest ih =>
      intro ρ eN heN
      have hW : 7 < W := h₂
      have hcvt : EvalExp env (bunScopeN W n.toNat)
          (.cvtE (.binE .subOp (.numT .intT) (.cvtE (.varE "N") .natT .intT)
            (.cvtE (.numE (.natN 7)) .natT .intT)) .intT .natT) (.num (.natN (W - 7))) :=
        evalExp_cvtE_num (evalExp_binE_num
          (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_N W n.toNat)) rfl)
          (evalExp_cvtE_num (evalExp_numE_iff.mpr rfl) rfl) rfl)
          (cvt_natT_intN (by omega) (by omega))
      rw [symDerives_varG h.bun]
      refine ⟨rfl, _, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
      refine ⟨[.val (.num (.natN W))], bunScope W, [numCase n.toNat, numCase m],
        bunScopeM W n.toNat m, bunScopeM W n.toNat m, _,
        evalArgs_expA heN, rfl, ?_, ?_, ?_, rfl⟩
      · show SymDerives env (bunScope W)
          (.seqG [ .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])],
                   .seqG [.attrG (.caseE "%" (.tupE [.varE "m"]))
                            (.varG "BuN" [.expA (.cvtE (.binE .subOp (.numT .intT)
                                (.cvtE (.varE "N") .natT .intT)
                                (.cvtE (.numE (.natN 7)) .natT .intT)) .intT .natT)])] ])
          _ _ _
        rw [symDerives_seqG_cons]
        refine ⟨[n], [numCase n.toNat], bunScopeN W n.toNat, b, [numCase m], ?_, ?_, rfl, rfl⟩
        · rw [symDerives_seqG_cons]
          refine ⟨[n], [numCase n.toNat], bunScopeN W n.toNat, [], [], ?_,
            symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, rfl, rfl⟩
          rw [symDerives_attrG]
          exact ⟨numCase n.toNat, bunScope W, bbyte_derives h _ n, rfl,
            matchExp_case_var (findVal_bunScope_n W)⟩
        · refine symDerives_seqG_cons.mpr ⟨b, [numCase m], bunScopeM W n.toNat m, [], [], ?_,
            symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil b).symm,
            (List.append_nil _).symm⟩
          refine symDerives_seqG_cons.mpr ⟨b, [numCase m], bunScopeM W n.toNat m, [], [], ?_,
            symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, (List.append_nil b).symm,
            (List.append_nil _).symm⟩
          exact symDerives_attrG.mpr ⟨numCase m, bunScopeN W n.toNat, ih _ _ hcvt, rfl,
            matchExp_case_var (findVal_bunScopeN_m W n.toNat)⟩
      · refine premsHold_ifPr (evalExp_and_true ?_ ?_)
        · refine evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeM_n W n.toNat m))
            (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) ?_
          simp [cmpValues, Num.cmp, h₁]
        · refine evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeM_N W n.toNat m))
            (evalExp_numE_iff.mpr rfl) ?_
          simp [cmpValues, Num.cmp, hW]
      · rw [numCase, evalExp_caseE_iff]
        have hsub : EvalExp env (bunScopeM W n.toNat m)
            (.cvtE (.binE .subOp (.numT .intT)
              (.cvtE (.varE "n") .natT .intT)
              (.cvtE (twoPowE (.numE (.natN 7))) .natT .intT)) .intT .natT)
            (.num (.natN (n.toNat - 2 ^ 7))) :=
          evalExp_cvtE_num (evalExp_binE_num
            (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeM_n W n.toNat m)) rfl)
            (evalExp_cvtE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl) rfl)
            (cvt_natT_intN (by omega) (by omega))
        refine ⟨_, evalExp_tupE_iff.mpr ⟨_, evalExps_singleton ?_, rfl⟩, rfl⟩
        exact evalExp_binE_num
          (evalExp_binE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl))
            (evalExp_varE_iff.mpr (findVal_bunScopeM_m W n.toNat m)) rfl) hsub rfl

/-- Every byte string the pinned `BuN` derives is one the hand-written
`Silmaril.Wasm.Binary.UN` accepts, with the matching value: the converse of
`bun_of_un`.

The induction is on the width, as in `Grammar/Basic.lean`'s
`un_of_denote_leb`: the recursive production is gated by `N > 7` and calls
`BuN($(N-7))`. -/
theorem un_of_bun {env : Env} (h : HasLeb env) :
    ∀ (W : Nat) {bs : Grammar.Bytes} {v : Value} {ρ ρ' : VarEnv} {eN : Exp},
      EvalExp env ρ eN (.num (.natN W)) →
      SymDerives env ρ (.varG "BuN" [.expA eN]) bs [v] ρ' →
      ∃ m, UN W bs m ∧ v = numCase m := by
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ih =>
    intro bs v ρ ρ' eN heN hd
    rw [symDerives_varG h.bun] at hd
    obtain ⟨-, p, hp, hpd⟩ := hd
    simp only [bunProds, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, heval, hl⟩ := hpd
      rw [evalArgs_expA_iff] at hargs
      obtain ⟨vA, hvA, rfl⟩ := hargs
      have hvAW : vA = Value.num (.natN W) := EvalExp.unique hvA heN
      subst hvAW
      have hρ₀ : ρ₀ = bunScope W := by
        have hb : (some (bunScope W) : Option VarEnv) = some ρ₀ := hbp
        exact (Option.some_inj.mp hb).symm
      subst hρ₀
      replace hbody : SymDerives env (bunScope W)
          (.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])) bs l₀ ρ₁ := hbody
      rw [symDerives_attrG] at hbody
      obtain ⟨v₁, ρa, hbb, -, hm⟩ := hbody
      obtain ⟨b, rfl, hv₁, rfl⟩ := bbyte_elim h hbb
      have hv₁' : v₁ = numCase b.toNat := by simpa using hv₁
      subst hv₁'
      have hρ₁ : ρ₁ = bunScopeN W b.toNat :=
        MatchExp.unique hm (matchExp_case_var (findVal_bunScope_n W))
      subst hρ₁
      rw [premsHold_ifPr_iff] at hprems
      obtain ⟨hcond, rfl⟩ := hprems
      have hc := (EvalExp.unique hcond (evalExp_and
        (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat))
          (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl)
        (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_n W b.toNat))
          (evalExp_twoPowE (evalExp_varE_iff.mpr (findVal_bunScopeN_N W b.toNat)))
          rfl))).symm
      simp only [Value.bool.injEq, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hvv : v' = numCase b.toNat :=
        EvalExp.unique heval (evalExp_case_var (findVal_bunScopeN_n W b.toNat))
      exact ⟨b.toNat, UN.byte b hc.1 hc.2, by simpa [hvv] using hl⟩
    · obtain ⟨ws, ρ₀, l₀, ρ₁, ρ₂, v', hargs, hbp, hbody, hprems, heval, hl⟩ := hpd
      rw [evalArgs_expA_iff] at hargs
      obtain ⟨vA, hvA, rfl⟩ := hargs
      have hvAW : vA = Value.num (.natN W) := EvalExp.unique hvA heN
      subst hvAW
      have hρ₀ : ρ₀ = bunScope W := by
        have hb : (some (bunScope W) : Option VarEnv) = some ρ₀ := hbp
        exact (Option.some_inj.mp hb).symm
      subst hρ₀
      replace hbody : SymDerives env (bunScope W)
          (.seqG [ .seqG [.attrG (.caseE "%" (.tupE [.varE "n"])) (.varG "Bbyte" [])],
                   .seqG [.attrG (.caseE "%" (.tupE [.varE "m"]))
                            (.varG "BuN" [.expA bunRecArg])] ]) bs l₀ ρ₁ := hbody
      rw [symDerives_seqG_cons] at hbody
      obtain ⟨b₁, l₁, σ₁, b₂, l₂, hA, hB, rfl, rfl⟩ := hbody
      rw [symDerives_seqG_cons] at hA
      obtain ⟨b₁', l₁', σ₁', b₁'', l₁'', hA1, hA2, rfl, rfl⟩ := hA
      rw [symDerives_seqG_nil] at hA2
      obtain ⟨rfl, rfl, rfl⟩ := hA2
      rw [symDerives_attrG] at hA1
      obtain ⟨vn, ρa, hbb, -, hmn⟩ := hA1
      obtain ⟨b, rfl, hvn, rfl⟩ := bbyte_elim h hbb
      have hvn' : vn = numCase b.toNat := by simpa using hvn
      subst hvn'
      have hσ₁ : σ₁ = bunScopeN W b.toNat :=
        MatchExp.unique hmn (matchExp_case_var (findVal_bunScope_n W))
      subst hσ₁
      rw [symDerives_seqG_cons] at hB
      obtain ⟨b₃, l₃, σ₂, b₄, l₄, hB1, hB2, rfl, rfl⟩ := hB
      rw [symDerives_seqG_nil] at hB2
      obtain ⟨rfl, rfl, rfl⟩ := hB2
      rw [symDerives_seqG_cons] at hB1
      obtain ⟨b₅, l₅, σ₃, b₆, l₆, hC1, hC2, rfl, rfl⟩ := hB1
      rw [symDerives_seqG_nil] at hC2
      obtain ⟨rfl, rfl, rfl⟩ := hC2
      rw [symDerives_attrG] at hC1
      obtain ⟨vm, ρb, hrec, -, hmm⟩ := hC1
      obtain ⟨w, rfl, hmw⟩ := matchExp_case_var_elim hmm
      have hρb : ρb = bunScopeN W b.toNat := ((symDerives_varG h.bun).mp hrec).1
      subst hρb
      have hσ₃ : ρ₁ = (bunScopeN W b.toNat).bindVal "m" w :=
        MatchExp.unique hmw (matchExp_varE_of_none (findVal_bunScopeN_m W b.toNat))
      subst hσ₃
      rw [premsHold_ifPr_iff] at hprems
      obtain ⟨hcond, rfl⟩ := hprems
      have hc := (EvalExp.unique hcond (evalExp_and
        (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bindM_n W b.toNat w))
          (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl)
        (evalExp_cmpE_num (evalExp_varE_iff.mpr (findVal_bindM_N W b.toNat w))
          (evalExp_numE_iff.mpr rfl) rfl))).symm
      simp only [Value.bool.injEq, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hcvt : EvalExp env (bunScopeN W b.toNat) bunRecArg (.num (.natN (W - 7))) :=
        evalExp_cvtE_num (evalExp_binE_num
          (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeN_N W b.toNat)) rfl)
          (evalExp_cvtE_num (evalExp_numE_iff.mpr rfl) rfl) rfl)
          (cvt_natT_intN (by omega) (by omega))
      obtain ⟨m, hun, hvm⟩ := ih (W - 7) (by omega) hcvt hrec
      have hw : w = Value.num (.natN m) := by simpa [numCase] using hvm
      subst hw
      have hsub : EvalExp env (bunScopeM W b.toNat m)
          (.cvtE (.binE .subOp (.numT .intT)
            (.cvtE (.varE "n") .natT .intT)
            (.cvtE (twoPowE (.numE (.natN 7))) .natT .intT)) .intT .natT)
          (.num (.natN (b.toNat - 2 ^ 7))) :=
        evalExp_cvtE_num (evalExp_binE_num
          (evalExp_cvtE_num (evalExp_varE_iff.mpr (findVal_bunScopeM_n W b.toNat m)) rfl)
          (evalExp_cvtE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl)) rfl) rfl)
          (cvt_natT_intN (by omega) (by omega))
      have hvv : v' = numCase (2 ^ 7 * m + (b.toNat - 2 ^ 7)) :=
        EvalExp.unique heval (evalExp_caseE_iff.mpr ⟨_, evalExp_tupE_iff.mpr ⟨_,
          evalExps_singleton (evalExp_binE_num
            (evalExp_binE_num (evalExp_twoPowE (evalExp_numE_iff.mpr rfl))
              (evalExp_varE_iff.mpr (findVal_bunScopeM_m W b.toNat m)) rfl) hsub rfl),
          rfl⟩, rfl⟩)
      refine ⟨2 ^ 7 * m + (b.toNat - 2 ^ 7), ?_, by simpa [hvv] using hl⟩
      simpa using UN.cont b hc.1 hc.2 hun

/-- **The pinned `BuN(N)` and the hand-written `UN N` are the same relation.**
Both directions, so the comparison the brief asks for comes out as an
equality; no erratum intervenes, because the two productions' premises are
exactly `UN`'s two clauses. -/
theorem bun_iff_un {env : Env} (h : HasLeb env) (W : Nat) (bs : Grammar.Bytes) (v : Value)
    (ρ : VarEnv) :
    gramRelSup env ρ (.varG "BuN" [.expA (.numE (.natN W))]) bs v ↔
      ∃ m, UN W bs m ∧ v = numCase m := by
  constructor
  · intro hd
    obtain ⟨ρ', hd⟩ := gramRelSup_iff.mp hd
    exact un_of_bun h W (evalExp_numE_iff.mpr rfl) hd
  · rintro ⟨m, hm, rfl⟩
    exact gramRelSup_iff.mpr ⟨ρ, bun_of_un h hm ρ _ (evalExp_numE_iff.mpr rfl)⟩

/-- **The bridge.**  The pinned wasm-3.0 `BuN` and `Grammar/Basic.lean`'s
hand-written `lebGram` denote the same byte-string/value relation, modulo the
change of attribute domain: the framework's `List Nat` attribute `[m]` is the
IL's `uN(N)` value `numCase m`. -/
theorem bun_iff_lebGram {env : Env} (h : HasLeb env) (W : Nat) (bs : Grammar.Bytes)
    (m : Nat) (ρ : VarEnv) :
    gramRelSup env ρ (.varG "BuN" [.expA (.numE (.natN W))]) bs (numCase m) ↔
      Grammar.denote Grammar.lebGram (.nt W) bs [m] := by
  rw [bun_iff_un h, Grammar.denote_leb_nt_iff]
  constructor
  · rintro ⟨m', hm', he⟩
    have hmm : m' = m := by simpa [numCase] using he.symm
    exact hmm ▸ hm'
  · intro hm
    exact ⟨m, hm, rfl⟩

/-- The bridge at the pinned wasm-3.0 script itself. -/
theorem bun_iff_lebGram_wasm30 (W : Nat) (bs : Grammar.Bytes) (m : Nat) (ρ : VarEnv) :
    gramRelSup (envOfScript Specs.wasm30) ρ (.varG "BuN" [.expA (.numE (.natN W))]) bs
        (numCase m)
      ↔ Grammar.denote Grammar.lebGram (.nt W) bs [m] :=
  bun_iff_lebGram hasLeb_wasm30 W bs m ρ

/-- The payoff: the pinned `BuN(N)` is unambiguous — prefix-free and
functional — which comes from the framework's `unambiguous_leb` through the
bridge rather than from a fresh argument. -/
theorem unambiguous_bun {env : Env} (h : HasLeb env) (W : Nat) (ρ : VarEnv) :
    Grammar.Unambiguous (gramRelSup env ρ (.varG "BuN" [.expA (.numE (.natN W))])) := by
  constructor
  · intro b b' a a' r hb hb' he
    obtain ⟨m, hm, rfl⟩ := (bun_iff_un h W b a ρ).mp hb
    obtain ⟨m', hm', rfl⟩ := (bun_iff_un h W b' a' ρ).mp hb'
    exact (Grammar.unambiguous_leb W).1 (Grammar.denote_leb_of_un hm)
      (Grammar.denote_leb_of_un hm') he
  · intro b a a' hb hb'
    obtain ⟨m, hm, rfl⟩ := (bun_iff_un h W b a ρ).mp hb
    obtain ⟨m', hm', rfl⟩ := (bun_iff_un h W b a' ρ).mp hb'
    have hl : [m] = [m'] := (Grammar.unambiguous_leb W).2 (Grammar.denote_leb_of_un hm)
      (Grammar.denote_leb_of_un hm')
    simp_all

/-- `Bu32 = BuN(32)` (`specification/wasm-3.0/5.1-binary.values.spectec:26`)
is `Silmaril.Wasm.Binary.U32`, in the pinned wasm-3.0 script itself. -/
theorem bu32_iff_u32 (bs : Grammar.Bytes) (v : Value) (ρ : VarEnv) :
    gramRelSup (envOfScript Specs.wasm30) ρ (.varG "BuN" [.expA (.numE (.natN 32))]) bs v ↔
      ∃ m, U32 bs m ∧ v = numCase m :=
  bun_iff_un hasLeb_wasm30 32 bs v ρ


end Leb


end Silmaril.SpecTec.Sem
