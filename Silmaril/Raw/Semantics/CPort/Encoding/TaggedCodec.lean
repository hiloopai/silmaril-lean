module

public import Silmaril.Formats.SExp.Tagged
public import Silmaril.Encoding.Codec
public import Std.Data.String.ToInt
public import Std.Data.String.ToNat
public meta import Lean.Elab.Term

/-!
# Codecs between values and tagged S-expressions

A `Codec α` pairs an encoder `α → Tree` with a decoder `Tree → Option α` and
carries both round-trip laws:

* `canonical`: a successful decode re-encodes to exactly the input tree, so a
  decoder accepts one spelling per value;
* `complete`: decoding an encoding returns the value.

Every combinator in this file proves both laws once, so a codec assembled from
them needs no proof of its own beyond the obligations of `ofAlts`, which are
about the hand-written encoder of one type.

Recursive types are decoded with fuel. `fix` ties the knot: the decoder at
fuel `k` is complete for encodings of depth at most `k`, and the top-level
decoder spends the depth of its input. The `budget` field records such a
depth bound; it is `none` for every codec that is not an approximant.

`decode` exposes child paths through `Except DecodeError`. It uses the same
`dec` that the laws cover. Combinators locate a failed child only on the error
path, so successful decoding makes one traversal. Primitive failures default
to the current node; applications may replace their diagnostic messages.
-/

@[expose] public section

namespace Silmaril.TaggedCodec

open Formats


/-- Tagged S-expressions with string tags and atoms. -/
abbrev Tree := TExpr String String

/-- A tagged node with a list of children. -/
abbrev node (tag : String) (children : List Tree) : Tree := TExpr.ofList tag children

/-- Nesting depth; atoms have depth one. -/
def depth : Tree → Nat
  | .atom _ => 1
  | .tag _ _ children => (List.ofFn fun i => depth (children i)).foldr max 0 + 1

theorem one_le_depth (t : Tree) : 1 ≤ depth t := by
  cases t <;> simp [depth]

theorem node_ofFn (tag : String) (n : Nat) (children : Fin n → Tree) :
    node tag (List.ofFn children) = .tag tag n children :=
  TExpr.ofNode_node (.tag tag n children)

theorem foldr_max_le {xs : List Nat} {k : Nat} :
    xs.foldr max 0 ≤ k ↔ ∀ x ∈ xs, x ≤ k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem depth_node_le {tag : String} {children : List Tree} {k : Nat} :
    depth (node tag children) ≤ k + 1 ↔ ∀ t ∈ children, depth t ≤ k := by
  have h : (List.ofFn fun i => depth (children.get i)) = children.map depth := by
    apply List.ext_getElem <;> simp
  simp only [node, TExpr.ofList, depth, h, Nat.add_le_add_iff_right, foldr_max_le, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- Structural equality of tagged trees. -/
def treeEq : (a b : Tree) → Decidable (a = b)
  | .atom a, .atom b => decidable_of_iff (a = b) (by simp)
  | .atom _, .tag _ _ _ => .isFalse (by intro h; cases h)
  | .tag _ _ _, .atom _ => .isFalse (by intro h; cases h)
  | .tag a n cs, .tag b m ds =>
    if ht : a = b then
      if hn : n = m then by
        subst ht hn
        letI : DecidablePred (fun i => cs i = ds i) := fun i => treeEq (cs i) (ds i)
        exact if hc : ∀ i, cs i = ds i then .isTrue (by congr; funext i; exact hc i)
          else .isFalse (by intro h; cases h; exact hc fun _ => rfl)
      else .isFalse (by intro h; cases h; exact hn rfl)
    else .isFalse (by intro h; cases h; exact ht rfl)

instance : DecidableEq Tree := treeEq

/-! ## Depth budgets -/

/-- A depth bound; `none` is unbounded. -/
abbrev Budget := Option Nat

namespace Budget

/-- Whether depth `d` is within the budget. -/
def allows : Budget → Nat → Prop
  | none, _ => True
  | some n, d => d ≤ n

/-- The budget of a node whose children have budget `b`. -/
def succ (b : Budget) : Budget := b.map (· + 1)

/-- The tighter of two budgets. -/
def meet : Budget → Budget → Budget
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

@[simp] theorem allows_none (d : Nat) : allows none d := trivial
@[simp] theorem allows_some (n d : Nat) : allows (some n) d ↔ d ≤ n := Iff.rfl
@[simp] theorem succ_none : succ none = none := rfl
@[simp] theorem succ_some (n : Nat) : succ (some n) = some (n + 1) := rfl
@[simp] theorem meet_none (b : Budget) : meet none b = b := rfl
@[simp] theorem meet_none_right (b : Budget) : meet b none = b := by cases b <;> rfl
@[simp] theorem meet_some (a b : Nat) : meet (some a) (some b) = some (min a b) := rfl

theorem allows_meet {a b : Budget} {d : Nat} :
    allows (meet a b) d ↔ allows a d ∧ allows b d := by
  cases a <;> cases b <;> simp [meet, allows]

theorem allows_succ {b : Budget} {d : Nat} :
    allows (succ b) (d + 1) ↔ allows b d := by
  cases b <;> simp [succ, allows]

/-- A node within `succ b` has children within `b`. -/
theorem allows_children {b : Budget} {tag : String} {children : List Tree}
    (h : allows (succ b) (depth (node tag children))) :
    ∀ t ∈ children, allows b (depth t) := by
  cases b with
  | none => simp
  | some n =>
    intro t ht
    exact depth_node_le.mp h t ht

theorem allows_mono {b : Budget} {d e : Nat} (h : allows b e) (hde : d ≤ e) : allows b d := by
  cases b <;> simp_all [allows]; omega

end Budget

/-! ## Codecs and field lists -/

/-- A decoding failure, with a zero-based path through children. -/
structure DecodeError where
  path : List Nat := []
  message : String := "invalid encoding"
  deriving DecidableEq, Repr

/-- Locate a failure in child `i`. -/
def DecodeError.atChild (i : Nat) (e : DecodeError) : DecodeError :=
  { e with path := i :: e.path }

/-- An encoder, a decoder, and their round-trip laws. Diagnostics are consulted
only after the decoder fails; they do not change the accepted language. -/
structure Codec (α : Type) where
  enc : α → Tree
  dec : Tree → Option α
  error : Tree → DecodeError := fun _ => {}
  /-- The depth up to which `dec` is complete. -/
  budget : Budget := none
  canonical : EncRel.DecoderSound (fun t x => enc x = t) dec
  complete : EncRel.EncoderCorrectOn (fun t x => dec t = some x)
    (fun x => budget.allows (depth (enc x))) enc

/-- A fixed-arity sequence of children, decoded by position. -/
structure Fields (α : Type) where
  enc : α → List Tree
  dec : List Tree → Option α
  error : List Tree → DecodeError := fun _ => ⟨[], "wrong number of children"⟩
  budget : Budget := none
  canonical : EncRel.DecoderSound (fun t x => enc x = t) dec
  complete : EncRel.EncoderCorrectOn (fun t x => dec t = some x)
    (fun x => ∀ t ∈ enc x, budget.allows (depth t)) enc

namespace Codec

variable {α β : Type}

/-- Decode with a diagnostic on failure. -/
def decode (c : Codec α) (t : Tree) : Except DecodeError α :=
  match c.dec t with
  | some x => .ok x
  | none => .error (c.error t)

/-- The diagnostic entry point succeeds exactly when `dec` does. -/
theorem decode_eq_ok {c : Codec α} {t : Tree} {x : α} :
    c.decode t = .ok x ↔ c.dec t = some x := by
  unfold decode
  cases c.dec t <;> simp

/-- A codec without a depth budget is complete everywhere. -/
theorem complete_of_budget {c : Codec α} (h : c.budget = none) (x : α) :
    c.dec (c.enc x) = some x :=
  c.complete x (by rw [h]; trivial)

/-- The specification is the encoder graph in the shared theory. -/
def toEncRel (c : Codec α) : EncRel Tree α := EncRel.ofFun c.enc

/-- The bounded round trip is exactly completeness on the encoder graph. -/
theorem decoderCompleteOn (c : Codec α) :
    c.toEncRel.DecoderCompleteOn (fun x => c.budget.allows (depth (c.enc x))) c.dec :=
  (EncRel.ofFun_decoderCompleteOn_iff c.enc c.dec _).2 c.complete

/-- An unbounded codec decides its specification. -/
theorem decoderComplete (c : Codec α) (h : c.budget = none) :
    c.toEncRel.DecoderComplete c.dec := by
  intro t x hx
  exact c.decoderCompleteOn t x (by rw [h]; trivial) hx

/-- Soundness and completeness identify the executable graph. -/
theorem toEncRel_eq_ofDecoder (c : Codec α) (h : c.budget = none) :
    c.toEncRel = EncRel.ofDecoder c.dec :=
  EncRel.eq_ofDecoder c.dec c.canonical (c.decoderComplete h)

/-- Every unbounded codec has a functional specification. -/
theorem functional (c : Codec α) (h : c.budget = none) : c.toEncRel.Functional :=
  EncRel.functional_iff_le_ofDecoder.2 ⟨c.dec, c.decoderComplete h⟩

/-- Encoder injectivity follows from functionality of its graph. -/
theorem enc_injective {c : Codec α} (h : c.budget = none) : Function.Injective c.enc :=
  EncRel.ofFun_functional_iff.1 (c.functional h)

/-- Replace the encoder by one that is provably equal to it. -/
def withEnc (c : Codec α) (enc : α → Tree) (h : c.enc = enc) : Codec α where
  enc := enc
  dec := c.dec
  error := c.error
  budget := c.budget
  canonical t x hx := h ▸ c.canonical t x hx
  complete x hx := by subst h; exact c.complete x hx

/-- Lower the budget of a codec. -/
def weaken (c : Codec α) (b : Budget) (h : ∀ d, b.allows d → c.budget.allows d) : Codec α where
  enc := c.enc
  dec := c.dec
  error := c.error
  budget := b
  canonical := c.canonical
  complete x hx := c.complete x (h _ hx)

/-- Transport a codec along a bijection. -/
def iso (c : Codec β) (f : β → α) (g : α → β)
    (hfg : ∀ a, f (g a) = a) (hgf : ∀ b, g (f b) = b) : Codec α where
  enc a := c.enc (g a)
  dec t := f <$> c.dec t
  error := c.error
  budget := c.budget
  canonical t a h := by
    cases hb : c.dec t with
    | none => simp [hb] at h
    | some b =>
      simp only [hb, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
      subst h
      rw [hgf]
      exact c.canonical t b hb
  complete a ha := by
    simp [c.complete (g a) ha, hfg]

/-- Transport of executable syntax agrees with relational reindexing. -/
theorem iso_toEncRel (c : Codec β) (f : β → α) (g : α → β) (hfg hgf) :
    (c.iso f g hfg hgf).toEncRel = c.toEncRel.comap g := rfl

/-- Budget weakening preserves the syntax specification. -/
theorem weaken_toEncRel (c : Codec α) (b : Budget) (h) :
    (c.weaken b h).toEncRel = c.toEncRel := rfl

/-- The codec of an uninhabited type. -/
def empty : Codec Empty where
  enc x := nomatch x
  dec _ := none
  canonical _ x := nomatch x
  complete x := nomatch x

/-- A bare atom holding its string. -/
def atom : Codec String where
  enc := .atom
  dec
    | .atom s => some s
    | .tag .. => none
  canonical t x h := by
    cases t <;> simp_all
  complete _ _ := rfl

/-- A decimal integer atom in the unique spelling `0|-?[1-9][0-9]*`. -/
def int : Codec Int where
  enc n := .atom n.repr
  dec
    | .atom s => match s.toInt? with
      | some n => if n.repr = s then some n else none
      | none => none
    | .tag .. => none
  canonical t x h := by
    cases t with
    | tag => simp at h
    | atom s =>
      simp only at h
      split at h
      · split at h
        · cases h; simp_all
        · simp at h
      · simp at h
  complete n _ := by simp

/-- A non-negative decimal atom in the unique spelling `0|[1-9][0-9]*`. -/
def nat : Codec Nat where
  enc n := .atom n.repr
  dec
    | .atom s => match s.toNat? with
      | some n => if n.repr = s then some n else none
      | none => none
    | .tag .. => none
  canonical t x h := by
    cases t with
    | tag => simp at h
    | atom s =>
      simp only at h
      split at h
      · split at h
        · cases h; simp_all
        · simp at h
      · simp at h
  complete n _ := by simp [Nat.toNat?_repr]

/-- Decode the children of a node tagged `tag`. -/
def children? (tag : String) : Tree → Option (List Tree)
  | .atom _ => none
  | .tag s _ cs => if s = tag then some (List.ofFn cs) else none

@[simp] theorem children?_node (tag : String) (ts : List Tree) :
    children? tag (node tag ts) = some ts := by
  simp [children?, node, TExpr.ofList]

theorem node_of_children? {tag : String} {t : Tree} {ts : List Tree}
    (h : children? tag t = some ts) : node tag ts = t := by
  cases t with
  | atom => simp [children?] at h
  | tag s n cs =>
    simp only [children?] at h
    split at h
    · cases h; subst s; exact node_ofFn _ _ _
    · simp at h

/-- A node with a fixed tag and positional children. -/
def tagged (tag : String) (fs : Fields α) : Codec α where
  enc x := node tag (fs.enc x)
  dec t := children? tag t >>= fs.dec
  error t := match children? tag t with
    | some ts => fs.error ts
    | none => ⟨[], "expected tag " ++ tag⟩
  budget := fs.budget.succ
  canonical t x h := by
    cases hc : children? tag t with
    | none => simp [hc] at h
    | some ts =>
      simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
      rw [fs.canonical ts x h]
      exact node_of_children? hc
  complete x hx := by
    simp only [children?_node, Option.bind_eq_bind, Option.bind_some]
    exact fs.complete x (Budget.allows_children hx)

theorem mapM_canonical (c : Codec α) :
    ∀ (ts : List Tree) (xs : List α), ts.mapM c.dec = some xs → xs.map c.enc = ts
  | [], xs, h => by simp at h; simp [← h]
  | t :: ts, xs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind] at h
    cases hx : c.dec t with
    | none => simp [hx] at h
    | some x =>
      cases hxs : ts.mapM c.dec with
      | none => simp [hx, hxs] at h
      | some ys =>
        simp [hx, hxs] at h
        subst h
        simp [c.canonical t x hx, mapM_canonical c ts ys hxs]

theorem mapM_complete (c : Codec α) :
    ∀ xs : List α, (∀ x ∈ xs, c.budget.allows (depth (c.enc x))) →
      (xs.map c.enc).mapM c.dec = some xs
  | [], _ => rfl
  | x :: xs, h => by
    simp [c.complete x (h x (by simp)),
      mapM_complete c xs (fun y hy => h y (by simp [hy]))]

/-- Find the first failing child in a sequence. -/
def sequenceError (c : Codec α) : Nat → List Tree → DecodeError
  | _, [] => ⟨[], "invalid sequence"⟩
  | i, t :: ts => match c.dec t with
    | none => (c.error t).atChild i
    | some _ => sequenceError c (i + 1) ts

/-- A variable-length node such as `($list x1 … xN)`. -/
def seq (tag : String) (c : Codec α) : Codec (List α) where
  enc xs := node tag (xs.map c.enc)
  dec t := children? tag t >>= fun ts => ts.mapM c.dec
  error t := match children? tag t with
    | some ts => sequenceError c 0 ts
    | none => ⟨[], "expected tag " ++ tag⟩
  budget := c.budget.succ
  canonical t xs h := by
    cases hc : children? tag t with
    | none => simp [hc] at h
    | some ts =>
      simp only [hc, Option.bind_eq_bind, Option.bind_some] at h
      rw [mapM_canonical c ts xs h]
      exact node_of_children? hc
  complete xs hxs := by
    simp only [children?_node, Option.bind_eq_bind, Option.bind_some]
    apply mapM_complete
    intro x hx
    exact Budget.allows_children hxs _ (List.mem_map_of_mem hx)

@[simp] theorem tagged_budget (tag : String) (fs : Fields α) :
    (tagged tag fs).budget = fs.budget.succ := rfl
@[simp] theorem seq_budget (tag : String) (c : Codec α) :
    (seq tag c).budget = c.budget.succ := rfl
@[simp] theorem weaken_budget (c : Codec α) (b : Budget) (h) : (c.weaken b h).budget = b := rfl
@[simp] theorem withEnc_budget (c : Codec α) (enc : α → Tree) (h : c.enc = enc) :
    (c.withEnc enc h).budget = c.budget := rfl
@[simp] theorem iso_budget (c : Codec β) (f : β → α) (g hfg hgf) :
    (c.iso f g hfg hgf).budget = c.budget := rfl
@[simp] theorem atom_budget : atom.budget = none := rfl
@[simp] theorem int_budget : int.budget = none := rfl
@[simp] theorem nat_budget : nat.budget = none := rfl
@[simp] theorem empty_budget : empty.budget = none := rfl

end Codec

namespace Fields

/-- Field lists use the same encoder graph with a list carrier. -/
def toEncRel {α : Type} (fs : Fields α) : EncRel (List Tree) α := EncRel.ofFun fs.enc

/-- Field-list round trips are completeness on the permitted encodings. -/
theorem decoderCompleteOn {α : Type} (fs : Fields α) :
    fs.toEncRel.DecoderCompleteOn
      (fun x => ∀ t ∈ fs.enc x, fs.budget.allows (depth t)) fs.dec :=
  (EncRel.ofFun_decoderCompleteOn_iff fs.enc fs.dec _).2 fs.complete


variable {α β : Type}

/-- No children. -/
def nil : Fields Unit where
  enc _ := []
  dec
    | [] => some ()
    | _ :: _ => none
  canonical ts _ h := by cases ts <;> simp_all
  complete _ _ := rfl

/-- Exactly one child. -/
def one (c : Codec α) : Fields α where
  enc x := [c.enc x]
  dec
    | [t] => c.dec t
    | _ => none
  error
    | [t] => (c.error t).atChild 0
    | _ => ⟨[], "expected one child"⟩
  budget := c.budget
  canonical ts x h := by
    match ts, h with
    | [t], h => simp [c.canonical t x h]
  complete x hx := c.complete x (hx _ (by simp))

/-- A first child followed by the remaining fields. -/
def cons (c : Codec α) (fs : Fields β) : Fields (α × β) where
  enc p := c.enc p.1 :: fs.enc p.2
  dec
    | [] => none
    | t :: ts => do
      let a ← c.dec t
      let b ← fs.dec ts
      pure (a, b)
  error
    | [] => ⟨[], "missing child"⟩
    | t :: ts => match c.dec t with
      | none => (c.error t).atChild 0
      | some _ =>
        let e := fs.error ts
        { e with path := match e.path with | [] => [] | i :: rest => (i + 1) :: rest }
  budget := Budget.meet c.budget fs.budget
  canonical ts p h := by
    match ts, h with
    | t :: ts, h =>
      simp only [Option.bind_eq_bind, Option.pure_def] at h
      cases ha : c.dec t with
      | none => simp [ha] at h
      | some a =>
        cases hb : fs.dec ts with
        | none => simp [ha, hb] at h
        | some b =>
          simp [ha, hb] at h
          subst h
          simp [c.canonical t a ha, fs.canonical ts b hb]
  complete p hp := by
    have h1 := hp _ (List.mem_cons_self ..)
    have h2 : ∀ t ∈ fs.enc p.2, fs.budget.allows (depth t) := fun t ht =>
      (Budget.allows_meet.mp (hp t (List.mem_cons_of_mem _ ht))).2
    simp [c.complete p.1 (Budget.allows_meet.mp h1).1, fs.complete p.2 h2]

/-- A codec used as a field list stands for exactly one child. -/
class ToFields (γ : Type) (α : outParam Type) where
  toFields : γ → Fields α

instance : ToFields (Codec α) α := ⟨one⟩
instance : ToFields (Fields α) α := ⟨id⟩

@[simp] theorem toFields_codec (c : Codec α) : ToFields.toFields c = one c := rfl
@[simp] theorem toFields_fields (fs : Fields α) : ToFields.toFields fs = fs := rfl

@[simp] theorem nil_budget : nil.budget = none := rfl
@[simp] theorem one_budget (c : Codec α) : (one c).budget = c.budget := rfl
@[simp] theorem cons_budget (c : Codec α) (fs : Fields β) :
    (cons c fs).budget = Budget.meet c.budget fs.budget := rfl

end Fields

/-- `c ⊗ fs`: the child `c` followed by `fs`, which may be one codec. -/
infixr:67 " ⊗ " => fun c fs => Fields.cons c (Fields.ToFields.toFields fs)

/-! ## Alternatives by tag -/

/-- One constructor: its tag, the codec of its fields, and the constructor. -/
structure Alt (α : Type) where
  tag : String
  {β : Type}
  fields : Fields β
  ctor : β → α

/-- An alternative; the payload type is inferred from `fields`. -/
abbrev alt {α β γ : Type} [Fields.ToFields γ β] (tag : String) (fields : γ) (mk : β → α) : Alt α :=
  ⟨tag, Fields.ToFields.toFields fields, mk⟩

/-- A nullary alternative. -/
abbrev leaf {α : Type} (tag : String) (x : α) : Alt α := ⟨tag, .nil, fun _ => x⟩

/-! Constructor-bound alternatives. The explicit tag may come from an application's
name map. Payload fields are unpacked in constructor order from right-nested
products; a single tuple argument stays a single field. -/
meta section

open Lean Elab Term

/-- Resolve a constructor for alternative syntax, rejecting other declarations. -/
public def constructorInfo (ctor : Syntax) : TermElabM ConstructorVal := do
  let name ← realizeGlobalConstNoOverloadWithInfo ctor
  let .ctorInfo info ← getConstInfo name | throwError "{name} is not a constructor"
  return info

elab "ctorAlt% " ctor:ident tag:term:max fields:term:max : term <= expectedType => do
  let info ← constructorInfo ctor
  if info.numFields == 0 then throwError "use ctorLeaf% for a nullary constructor"
  let x := Lean.mkIdent `payload
  let mut tail : Lean.TSyntax `term := ⟨x⟩
  let mut app : Lean.TSyntax `term := ⟨ctor⟩
  for i in [:info.numFields] do
    let arg ← if i + 1 == info.numFields then pure tail else `(term| ($tail).1)
    app ← `(term| $app $arg)
    tail ← `(term| ($tail).2)
  let mk ← `(term| fun $x => $app)
  elabTerm (← `(term| alt $tag $fields $mk)) expectedType

elab "ctorLeaf% " ctor:ident tag:term:max : term <= expectedType => do
  let info ← constructorInfo ctor
  unless info.numFields == 0 do throwError "{ctor} has payload fields"
  elabTerm (← `(term| leaf $tag $ctor)) expectedType

/-- A constructor-bound entry for `Codec.ofLeaves`. -/
elab "ctorPair% " ctor:ident tag:term:max : term <= expectedType => do
  let info ← constructorInfo ctor
  unless info.numFields == 0 do throwError "{ctor} has payload fields"
  elabTerm (← `(term| ($tag, $ctor))) expectedType

end

namespace Alt

variable {α : Type}

/-- The tightest budget of a list of alternatives. -/
def budget : List (Alt α) → Budget
  | [] => none
  | a :: as => Budget.meet a.fields.budget (budget as)

theorem allows_budget {as : List (Alt α)} {a : Alt α} (ha : a ∈ as) {d : Nat}
    (h : (budget as).allows d) : a.fields.budget.allows d := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact (Budget.allows_meet.mp h).1
    · exact ih ha (Budget.allows_meet.mp h).2

@[simp] theorem budget_nil : budget ([] : List (Alt α)) = none := rfl
@[simp] theorem budget_cons (a : Alt α) (as : List (Alt α)) :
    budget (a :: as) = Budget.meet a.fields.budget (budget as) := rfl

/-- The first alternative with a tag. -/
def lookup (as : List (Alt α)) (tag : String) : Option (Alt α) := as.find? (·.tag == tag)

theorem lookup_tag {as : List (Alt α)} {tag : String} {a : Alt α}
    (h : lookup as tag = some a) : a.tag = tag := by
  simpa using List.find?_some h

theorem lookup_of_mem {as : List (Alt α)} (hnd : (as.map Alt.tag).Nodup) {a : Alt α}
    (ha : a ∈ as) : lookup as a.tag = some a := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [lookup]
    · have hne : b.tag ≠ a.tag := fun h => hnd.1 ⟨a, ha, h.symm⟩
      have h := ih hnd.2 ha
      simp only [lookup] at h ⊢
      rwa [List.find?_cons_of_neg (by simpa using hne)]

end Alt

namespace Alt

variable {α : Type}

theorem forall_cons {P : Alt α → Prop} {a : Alt α} {as : List (Alt α)}
    (h : P a) (t : ∀ x ∈ as, P x) : ∀ x ∈ a :: as, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  exacts [h, t x hx]

theorem forall_nil {P : Alt α → Prop} : ∀ x ∈ ([] : List (Alt α)), P x := by simp

theorem exists_head {a : Alt α} {as : List (Alt α)} {x : α} (b : a.β) (h : a.ctor b = x) :
    ∃ a' ∈ a :: as, ∃ b, a'.ctor b = x := ⟨a, List.mem_cons_self .., b, h⟩

theorem exists_tail {a : Alt α} {as : List (Alt α)} {x : α}
    (h : ∃ a' ∈ as, ∃ b, a'.ctor b = x) : ∃ a' ∈ a :: as, ∃ b, a'.ctor b = x :=
  let ⟨a', ha, b, hb⟩ := h
  ⟨a', List.mem_cons_of_mem _ ha, b, hb⟩

end Alt

/-- The distinct-tag obligation of `ofAlts`. -/
macro "codec_nodup" : tactic =>
  `(tactic| first
    | decide +kernel
    | (simp only [List.map_cons, List.map_nil]; decide))

/-- The encoder obligation of `ofAlts`, one alternative at a time. The
optional lemmas unfold an encoder defined by well-founded recursion. -/
syntax "codec_enc" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| codec_enc) => `(tactic|
      (repeat (refine Alt.forall_cons ?_ ?_; (intro _; rfl))
       exact Alt.forall_nil))
  | `(tactic| codec_enc [$ls,*]) => `(tactic|
      (repeat (refine Alt.forall_cons ?_ ?_; ((try simp only [Prod.forall]); intros; (try simp only [$ls,*]) <;> rfl))
       exact Alt.forall_nil))

/-- The coverage obligation of `ofLeaves`: nullary constructors by evaluation,
the others as for `ofAlts`. -/
macro "codec_leaf_cover" : tactic => `(tactic|
  (intro x; cases x <;> first
    | exact Or.inl (by decide +kernel)
    | (refine Or.inr ?_
       repeat (first
        | exact Alt.exists_head _ (by rfl)
        | exact Alt.exists_head (Prod.mk _ _) (by rfl)
        | exact Alt.exists_head (Prod.mk _ (Prod.mk _ _)) (by rfl)
        | apply Alt.exists_tail))))

/-- The coverage obligation of `ofAlts`: find the alternative of each
constructor by unification, trying payloads of up to six fields, and fall back
to `simp` for wider records. -/
macro "codec_cover" : tactic => `(tactic|
  (intro x; cases x <;> first
   | (repeat (first
      | exact Alt.exists_head () rfl
      | exact Alt.exists_head _ (by rfl)
      | exact Alt.exists_head (Prod.mk _ _) (by rfl)
      | exact Alt.exists_head (Prod.mk _ (Prod.mk _ _)) (by rfl)
      | exact Alt.exists_head (Prod.mk _ (Prod.mk _ (Prod.mk _ _))) (by rfl)
      | exact Alt.exists_head (Prod.mk _ (Prod.mk _ (Prod.mk _ (Prod.mk _ _)))) (by rfl)
      | exact Alt.exists_head (Prod.mk _ (Prod.mk _ (Prod.mk _ (Prod.mk _ (Prod.mk _ _))))) (by rfl)
      | apply Alt.exists_tail)
      done)
   | simp))

namespace Codec

variable {α : Type}

/-- Decode by tag through a list of alternatives, against a hand-written
encoder. `henc` says the encoder writes each alternative's tag and fields;
`cover` says every value is built by some alternative. -/
def ofAlts (enc : α → Tree) (alts : List (Alt α)) (nodup : (alts.map Alt.tag).Nodup)
    (henc : ∀ a ∈ alts, ∀ b, enc (a.ctor b) = node a.tag (a.fields.enc b))
    (cover : ∀ x, ∃ a ∈ alts, ∃ b, a.ctor b = x) : Codec α where
  enc := enc
  dec
    | .atom _ => none
    | .tag s _ cs => (Alt.lookup alts s).bind fun a => a.ctor <$> a.fields.dec (List.ofFn cs)
  error
    | .atom _ => ⟨[], "expected a tagged node"⟩
    | .tag s _ cs => match Alt.lookup alts s with
      | none => ⟨[], "unknown tag " ++ s⟩
      | some a => a.fields.error (List.ofFn cs)
  budget := (Alt.budget alts).succ
  canonical t x h := by
    cases t with
    | atom => simp at h
    | tag s n cs =>
      simp only [Option.bind_eq_some_iff, Option.map_eq_map, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      have hmem : a ∈ alts := List.mem_of_find?_eq_some ha
      rw [henc a hmem, a.fields.canonical _ b hb, Alt.lookup_tag ha]
      exact node_ofFn s n cs
  complete x hx := by
    obtain ⟨a, ha, b, rfl⟩ := cover x
    rw [henc a ha b] at hx ⊢
    have hch := Budget.allows_children hx
    change (Alt.lookup alts a.tag).bind
      (fun a' => a'.ctor <$> a'.fields.dec (List.ofFn (a.fields.enc b).get)) = _
    rw [List.ofFn_get, Alt.lookup_of_mem nodup ha]
    simp [a.fields.complete b fun t ht => Alt.allows_budget ha (hch t ht)]

/-- `ofAlts` for a type with many nullary constructors: `leaves` lists their
tags and values, and the obligations about them are decidable, so large
enumerations are checked by evaluation (`decide +kernel`) rather than by
per-constructor tactics. -/
def ofLeaves (enc : α → Tree) (leaves : List (String × α)) (alts : List (Alt α))
    (nodup : (leaves.map Prod.fst ++ alts.map Alt.tag).Nodup)
    (hleaf : ∀ p ∈ leaves, enc p.2 = node p.1 [])
    (henc : ∀ a ∈ alts, ∀ b, enc (a.ctor b) = node a.tag (a.fields.enc b))
    (cover : ∀ x, x ∈ leaves.map Prod.snd ∨ ∃ a ∈ alts, ∃ b, a.ctor b = x) : Codec α :=
  ofAlts enc (leaves.map (fun p => leaf p.1 p.2) ++ alts)
    (by simpa [List.map_append, List.map_map, Function.comp_def] using nodup)
    (by
      intro a ha b
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        exact hleaf p hp
      · exact henc a ha b)
    (by
      intro x
      rcases cover x with hx | ⟨a, ha, b, hb⟩
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact ⟨leaf p.1 p.2, List.mem_append_left _ (List.mem_map_of_mem hp), (), rfl⟩
      · exact ⟨a, List.mem_append_right _ ha, b, hb⟩)

theorem _root_.Silmaril.TaggedCodec.Alt.budget_append (as bs : List (Alt α)) :
    Alt.budget (as ++ bs) = Budget.meet (Alt.budget as) (Alt.budget bs) := by
  induction as with
  | nil => rfl
  | cons a as ih => cases h : a.fields.budget <;> cases h' : Alt.budget as <;>
      cases h'' : Alt.budget bs <;> simp_all [Budget.meet, Nat.min_assoc]

theorem _root_.Silmaril.TaggedCodec.Alt.budget_leaves (leaves : List (String × α)) :
    Alt.budget (leaves.map fun p => leaf p.1 p.2) = none := by
  induction leaves with
  | nil => rfl
  | cons p ps ih => simpa using ih

@[simp] theorem ofLeaves_budget (enc : α → Tree) (leaves : List (String × α))
    (alts : List (Alt α)) (nodup hleaf henc cover) :
    (ofLeaves enc leaves alts nodup hleaf henc cover).budget = (Alt.budget alts).succ := by
  change (Alt.budget _).succ = _
  rw [Alt.budget_append, Alt.budget_leaves]
  rfl

@[simp] theorem ofAlts_budget (enc : α → Tree) (alts : List (Alt α)) (nodup henc cover) :
    (ofAlts enc alts nodup henc cover).budget = (Alt.budget alts).succ := rfl

/-! ## Standard wire forms -/

/-- Exactly the tree `t`, such as a format version. -/
def lit (t : Tree) : Codec Unit where
  enc _ := t
  dec t' := if t' = t then some () else none
  canonical t' _ h := by
    by_cases ht : t' = t
    · exact ht.symm
    · simp [ht] at h
  complete _ _ := by
    simp

/-- `($str "…")`. -/
def str : Codec String := tagged "$str" (.one atom)

/-- `($list x1 … xN)`. -/
def list (c : Codec α) : Codec (List α) := seq "$list" c

/-- `($tuple a b …)`, flat. -/
def tuple {γ : Type} [Fields.ToFields γ α] (fs : γ) : Codec α := tagged "$tuple" (Fields.ToFields.toFields fs)

/-- `($map ($tuple k1 v1) …)` as an association list. Key order and
uniqueness are document well-formedness, not syntax. -/
def map {κ ν : Type} (k : Codec κ) (v : Codec ν) : Codec (List (κ × ν)) :=
  seq "$map" (tuple (k ⊗ v))

/-- `($unit)`. -/
def unit : Codec Unit := tagged "$unit" .nil

/-- `($true)` or `($false)`. -/
def boolean : Codec Bool :=
  ofAlts (fun b => if b then node "$true" [] else node "$false" [])
    [leaf "$true" true, leaf "$false" false]
    (by codec_nodup) (by codec_enc) (by codec_cover)

/-- `($none)` or `($some x)`. -/
def option (c : Codec α) : Codec (Option α) :=
  ofAlts (fun | none => node "$none" [] | some x => node "$some" [c.enc x])
    [leaf "$none" none, alt "$some" c some]
    (by codec_nodup) (by codec_enc) (by codec_cover)

@[simp] theorem str_budget : str.budget = none := rfl
@[simp] theorem lit_budget (t : Tree) : (lit t).budget = none := rfl
@[simp] theorem unit_budget : unit.budget = none := rfl
@[simp] theorem boolean_budget : boolean.budget = none := rfl
@[simp] theorem list_budget (c : Codec α) : (list c).budget = c.budget.succ := rfl
@[simp] theorem tuple_budget (fs : Fields α) : (tuple fs).budget = fs.budget.succ := rfl
@[simp] theorem tuple_one_budget (c : Codec α) : (tuple c).budget = c.budget.succ := rfl
@[simp] theorem map_budget {κ ν : Type} (k : Codec κ) (v : Codec ν) :
    (map k v).budget = (Budget.meet k.budget v.budget).succ.succ := rfl
@[simp] theorem option_budget (c : Codec α) :
    (option c).budget = (Budget.meet c.budget none).succ := rfl

/-! ## Recursive types -/

/-- The approximant at fuel zero decodes nothing. -/
def bottom (enc : α → Tree) : Codec α where
  enc := enc
  dec _ := none
  budget := some 0
  canonical _ _ h := nomatch h
  complete x h := absurd (one_le_depth (enc x)) (by simp_all)

/-- A `layer` builds a codec from an approximant of the same type. `guard`
says the layer consumes at least one tag before the recursive position. -/
structure Layer (α : Type) (enc : α → Tree) where
  build : (c : Codec α) → c.enc = enc → Codec α
  build_enc : ∀ c h, (build c h).enc = enc
  guard : ∀ c h k, c.budget = some k → ∀ d, d ≤ k + 1 → (build c h).budget.allows d

namespace Layer

variable {enc : α → Tree}

/-- The approximant at fuel `k`, complete up to depth `k`. -/
def approx (L : Layer α enc) : (k : Nat) → {c : Codec α // c.enc = enc ∧ c.budget = some k}
  | 0 => ⟨bottom enc, rfl, rfl⟩
  | k + 1 =>
    let prev := approx L k
    let c := L.build prev.1 prev.2.1
    ⟨(c.weaken (some (k + 1)) fun d hd => L.guard prev.1 prev.2.1 k prev.2.2 d hd).withEnc enc
      (L.build_enc _ _), rfl, rfl⟩

end Layer

/-- The fixed point of a layer; decoding spends the depth of its input. -/
def fix (enc : α → Tree) (L : Layer α enc) : Codec α where
  enc := enc
  dec t := (L.approx (depth t)).1.dec t
  error t := (L.approx (depth t)).1.error t
  canonical t x h := (L.approx (depth t)).2.1 ▸ (L.approx (depth t)).1.canonical t x h
  complete x _ := by
    have ⟨henc, hb⟩ := (L.approx (depth (enc x))).2
    have h := (L.approx (depth (enc x))).1.complete x (by rw [hb, henc]; exact Nat.le_refl _)
    rwa [henc] at h

@[simp] theorem fix_budget (enc : α → Tree) (L : Layer α enc) : (fix enc L).budget = none := rfl

/-- The recursive position inside a layer: the approximant with the final encoder. -/
abbrev slot (c : Codec α) (enc : α → Tree) (h : c.enc = enc) : Codec α := c.withEnc enc h

/-- Decidable equality from a codec without a depth budget. -/
def decEq (c : Codec α) (h : c.budget = none) : DecidableEq α :=
  fun x y => decidable_of_iff (c.enc x = c.enc y) (enc_injective h).eq_iff

end Codec

/-! ## Termination of encoders for nested types -/

theorem sizeOf_lt_of_mem_fst {α β : Type} [SizeOf α] [SizeOf β]
    {p : α × β} {ps : List (α × β)} (h : p ∈ ps) : sizeOf p.1 < sizeOf ps := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨a, b⟩ := p
  simp only [Prod.mk.sizeOf_spec] at this ⊢
  omega

theorem sizeOf_lt_of_mem_snd {α β : Type} [SizeOf α] [SizeOf β]
    {p : α × β} {ps : List (α × β)} (h : p ∈ ps) : sizeOf p.2 < sizeOf ps := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨a, b⟩ := p
  simp only [Prod.mk.sizeOf_spec] at this ⊢
  omega

theorem sizeOf_lt_of_mem_mid {α β γ : Type} [SizeOf α] [SizeOf β] [SizeOf γ]
    {p : α × β × γ} {ps : List (α × β × γ)} (h : p ∈ ps) : sizeOf p.2.1 < sizeOf ps := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨a, b, c⟩ := p
  simp only [Prod.mk.sizeOf_spec] at this ⊢
  omega

/-- Termination of an encoder that recurses through lists and products. -/
macro "codec_decreasing" : tactic => `(tactic|
  (all_goals simp_wf
   all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
    | (have := sizeOf_lt_of_mem_fst ‹_ ∈ _›; omega)
    | (have := sizeOf_lt_of_mem_snd ‹_ ∈ _›; omega)
    | (have := sizeOf_lt_of_mem_mid ‹_ ∈ _›; omega)))

/-! ## Examples -/

example : (ctorLeaf% Bool.true "$true" : Alt Bool).ctor () = true := rfl
example : (ctorPair% Bool.false "$false" : String × Bool) = ("$false", false) := rfl
example : (ctorAlt% Option.some "$some" Codec.atom : Alt (Option String)).ctor "x" =
    some "x" := rfl
example : (ctorAlt% Prod.mk "$pair" (Codec.atom ⊗ Codec.boolean) : Alt (String × Bool)).ctor
    ("x", true) = ("x", true) := rfl
-- A tuple payload is one constructor argument, rather than two fields.
example : (ctorAlt% Option.some "$some" (Codec.tuple (Codec.atom ⊗ Codec.boolean)) :
    Alt (Option (String × Bool))).ctor ("x", true) = some ("x", true) := rfl

example : Codec.boolean.dec (node "$true" [.atom "extra"]) = none := by rfl
example : (Codec.list Codec.atom).dec (node "$list" [.atom "a", .atom "b"]) = some ["a", "b"] := by
  rfl
example : (Codec.tuple (Codec.atom ⊗ Codec.option Codec.str)).dec
    (node "$tuple" [.atom "a", node "$some" [node "$str" [.atom "text"]]]) =
    some ("a", some "text") := by rfl
example : (Codec.map Codec.atom Codec.boolean).dec
    (node "$map" [node "$tuple" [.atom "a", node "$false" []]]) = some [("a", false)] := by
  rfl
example : (Codec.tuple (Codec.atom ⊗ Codec.boolean)).decode
    (node "$tuple" [.atom "a", node "$unknown" []]) =
    .error ⟨[1], "unknown tag $unknown"⟩ := by rfl
example : (Codec.list (Codec.list Codec.boolean)).decode
    (node "$list" [node "$list" [node "$true" [], node "$unknown" []]]) =
    .error ⟨[0, 1], "unknown tag $unknown"⟩ := by rfl
example (xs : List (Nat × Option String)) :
    (Codec.list (Codec.tuple (Codec.nat ⊗ Codec.option Codec.str))).dec
      ((Codec.list (Codec.tuple (Codec.nat ⊗ Codec.option Codec.str))).enc xs) = some xs :=
  Codec.complete_of_budget rfl xs

end Silmaril.TaggedCodec
