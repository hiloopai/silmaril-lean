module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Type
public import Silmaril.Encoding.Relation

/-!
# The bridge: Silmaril's Lean ASTs inside SpecTec's value domain

`Silmaril/SpecTec/Sem/Value.lean` gives the universal domain `Value` that
SpecTec's internal language denotes into, and `Silmaril/SpecTec/Sem/Type.lean`
says which `Value`s an IL type admits.  Silmaril's hand-written Wasm semantics
is written over ordinary Lean datatypes instead.  Every equivalence statement
between the two worlds therefore has to name a *correspondence* first, and
this file is that correspondence.

Everything is relative to the pin `608711107b7f1edb13efd57b7d79b49477462d36`.

## A class, not a relation — and why both

`Silmaril/Encoding/Relation.lean` already has the vocabulary for an encoding
as a value: `EncRel Value α` with `Functional`, `Deterministic`, `Bijective`,
`DecoderSound`, `DecoderComplete`.  That vocabulary is the right one to *state*
results in, but it is the wrong one to *build* the correspondence with, because
the correspondence has to compose: the encoding of `List (Option (α × β))` is
determined by the encodings of `α` and `β`, and instance resolution is what
makes that composition free.

So the primitive here is a class, and the `EncRel` is derived:

```lean
class Encode (α : Type) where
  toValue : α → Value
  ofValue : Value → Option α
  ofValue_toValue : ∀ a, ofValue (toValue a) = some a
  toValue_ofValue : ∀ v a, ofValue v = some a → toValue a = v
```

`encRel α := EncRel.ofFun Encode.toValue` is then `Bijective` (`encRel_bijective`),
`Encode.ofValue` is a sound and complete decoder for it (`encRel_decoderSound`,
`encRel_decoderComplete`), and `encRel_eq_ofDecoder` says the two descriptions
— "the graph of `toValue`" and "the graph of `ofValue`" — are the *same*
relation.  That last equation is exactly what the second law buys: with
`ofValue_toValue` alone, `ofValue` could accept junk outside the image of
`toValue` and still round-trip, and the induced `EncRel.ofDecoder` would be
strictly larger.  Two laws, and the pair is an isomorphism onto its image.

## The conventions

Everything downstream depends on these, so they are stated once, here, with
the IL type former each one matches.  `t ⟶ α` below reads "the SpecTec type
`t` and the Lean type `α` correspond", which is `Denotes env ρ t α` at the end
of this file.

| SpecTec type | `Sem.Value` | Lean type |
| --- | --- | --- |
| `bool` (`BoolT`) | `Value.bool b` | `Bool` |
| `nat` (`NumT NatT`) | `Value.num (natN n)` | `Nat` |
| `int` (`NumT IntT`) | `Value.num (intN i)` | `Int` |
| `text` (`TextT`) | `Value.text s` | `String` |
| `t*` (`IterT t List`) | `Value.list` | `List α` |
| `t?` (`IterT t Opt`) | `Value.opt` | `Option α` |
| `(t₁, t₂)` (`TupT`) | `Value.tuple [v₁, v₂]` | `α × β` |
| a variant (`VariantT`) | `Value.case op v` | an inductive |
| a record (`StructT`) | `Value.struct fs` | a structure |

### The variant convention — the important one

A `VariantT` (`spectec/src/il/ast.ml:41`) is a list of `typcase`s
(`ast.ml:44`), each a *mixop* paired with a single `typ`, and `CaseE`
(`ast.ml:65`) injects a single `exp`.  So a `Value.case op v` has exactly two
pieces, and the convention is:

> A Lean constructor `C a₁ … aₙ` of an inductive corresponding to a variant
> maps to `Value.case op v`, where
>
> * `op` is **the `IL.MixopS` rendering** of the `typcase`'s mixop — the string
>   `Silmaril/SpecTec/IL/Mixop.lean`'s `Mixop.toString` produces, which is what
>   `backend-ast/print.ml:14` writes into the `--ast` stream and hence what
>   `IL.Decode` reads back; and
> * `v` is **the value of the `typcase`'s declared `typ`**, *not* automatically
>   a tuple.

The second half is where it is easy to go wrong, because the pinned stream
does both.  `uN(N)` is
`(case "%" (tup (bind "i" nat)) (if …))`
(`specs/spectec/wasm-3.0.ast`, the `uN` definition), so its payload is a
*one*-component tuple and the value is
`Value.case "%" (Value.tuple [Value.num (natN n)])`; whereas `externidx` is
`(case "FUNC" (var "funcidx"))`, so *its* payload is not wrapped at all and the
value is `Value.case "FUNC" (funcidxValue)`.  The rule "the payload is the
value of the declared `typ`" covers both, and `caseV op vs` is the helper for
the `TupT` spelling, which is the one an `n`-ary surface case elaborates to.

`percentV` names the `%`-wrapping specifically: every "a numeral with a side
condition" type in the pinned specifications — `bit`, `byte`, `char`, `uN(N)`,
`sN(N)` — is a one-case variant whose mixop renders as `%`, and
`Encode.ofPercentNat` builds an `Encode` for such a type from nothing but a
`Nat`-valued injection and its partial inverse.  `instEncodeUInt8` (SpecTec
`byte`) and `instEncodeChar` (SpecTec `char`) are the two instances of it this
file provides.

### The record convention

A `StructT` (`ast.ml:40`) is a list of `typfield`s (`ast.ml:43`) keyed by an
*atom*, and `match_exp'`'s `StrE` case (`eval.ml:948-949`) matches a record's
fields **positionally**: it is a `match_list` down the two field lists, and
`match_expfield` (`eval.ml:1072-1074`) only *asserts* that the two atoms at a
position are equal rather than looking either up.  So the order is the
declaration order.  So:

> A Lean structure corresponding to a record maps to `Value.struct fs` with
> `fs` listing the field atoms **in the record's declaration order**, each
> atom being the `IL.AtomS` rendering (`IL/Atom.lean`).

`Encode.ofStruct` builds such an instance.  Nothing reorders fields: an
association list in a different order is a *different* value, and
`hasTypFields` rejects it (`Sem/Type.lean`, `hasTypFields_cons_iff`).

### Products are binary

`Prod`'s instance is `Value.tuple [v₁, v₂]`, which matches a `TupT` with two
binders.  **It does not flatten**: `α × β × γ` encodes as
`Value.tuple [a, Value.tuple [b, c]]`, which is a `TupT` of *two* binders whose
second is itself a `TupT`, not a `TupT` of three.  An `n`-ary SpecTec tuple
needs an `n`-ary Lean encoding, which `Encode.ofStruct`/`Encode.ofCase` or a
bespoke instance supplies; the `Prod` instance is deliberately not a trap
disguised as a convenience, so this is stated rather than worked around.

## What this file does not do

It does not *derive* instances from an `IL.DefTyp`: there is no elaborator here
that reads a `VariantT` out of a script and emits a Lean inductive.  Each
instance is written by hand and justified against the pinned stream by the file
that uses it.  `Denotes` is the statement that a hand-written instance lands in
the right subset of the domain, and the lemmas at the end of this file are the
closure properties that let a user discharge it compositionally.
-/

@[expose] public section

namespace Silmaril.SpecTec.Sem

open Silmaril.SpecTec.IL hiding Id Prod

/-! ## The class -/

/-- A correspondence between a Lean type `α` and SpecTec's value domain.

`toValue` is the encoding, `ofValue` its partial inverse.  The two laws make
the pair an isomorphism of `α` with the image of `toValue`: `ofValue_toValue`
says the inverse is defined on that image, and `toValue_ofValue` says it is
defined *nowhere else* — any `v` the decoder accepts really is `toValue` of
what it returns.  See the module docstring for why both are wanted. -/
class Encode (α : Type) where
  /-- The `Sem.Value` that represents an `α`. -/
  toValue : α → Value
  /-- The partial inverse of `toValue`. -/
  ofValue : Value → Option α
  /-- `ofValue` is defined on the image of `toValue`, and inverts it there. -/
  ofValue_toValue (a : α) : ofValue (toValue a) = some a
  /-- `ofValue` is defined only on the image of `toValue`. -/
  toValue_ofValue (v : Value) (a : α) : ofValue v = some a → toValue a = v

namespace Encode

variable {α β : Type}

/-- The encoding is injective: a value determines the `α` it encodes. -/
theorem toValue_injective [Encode α] : Function.Injective (toValue (α := α)) := by
  intro a b h
  have h₁ : ofValue (toValue a) = some a := ofValue_toValue a
  rw [h, ofValue_toValue b] at h₁
  exact (Option.some_inj.mp h₁).symm

/-- Decoding succeeds exactly on the image of `toValue`, and names the
preimage: the two laws, packaged as the characterisation of `ofValue`. -/
theorem ofValue_eq_some_iff [Encode α] {v : Value} {a : α} :
    ofValue v = some a ↔ toValue a = v := by
  constructor
  · exact toValue_ofValue v a
  · rintro rfl; exact ofValue_toValue a

/-- `toValue` is determined by `ofValue`. -/
theorem toValue_eq_of_ofValue [Encode α] {v : Value} {a : α} (h : ofValue v = some a) :
    toValue a = v :=
  toValue_ofValue v a h

end Encode

/-! ## The induced encoding relation

`Silmaril/Encoding/Relation.lean`'s vocabulary, instantiated.  The carrier is
`Value` and the syntax is `α`, so `encRel α v a` reads "`v` is the SpecTec
value of `a`". -/

section Rel

variable {α : Type}

/-- The `EncRel` an `Encode` instance induces: the graph of `toValue`. -/
def encRel (α : Type) [Encode α] : EncRel Value α := EncRel.ofFun Encode.toValue

/-- Unfolding `encRel`. -/
@[simp] theorem encRel_apply [Encode α] (v : Value) (a : α) :
    encRel α v a ↔ Encode.toValue a = v := Iff.rfl

/-- **The graph of the encoder and the graph of the decoder coincide.**  This
is the equation the second law of `Encode` exists for. -/
theorem encRel_eq_ofDecoder [Encode α] : encRel α = EncRel.ofDecoder Encode.ofValue := by
  ext v a
  exact ⟨fun h => Encode.ofValue_eq_some_iff.mpr h, fun h => Encode.ofValue_eq_some_iff.mp h⟩

/-- A value encodes at most one `α` — because `toValue` is injective. -/
theorem encRel_functional [Encode α] : (encRel α).Functional := by
  intro v a a' h h'
  exact Encode.toValue_injective (h.trans h'.symm)

/-- An `α` has at most one value — because `toValue` is a function. -/
theorem encRel_deterministic [Encode α] : (encRel α).Deterministic :=
  EncRel.ofFun_deterministic _

/-- Every `α` has a value. -/
theorem encRel_total [Encode α] : (encRel α).Total := EncRel.ofFun_total _

/-- **The bridge is a bijective encoding.**  `Bijective` in
`Silmaril/Encoding/Relation.lean` is `Functional ∧ Deterministic`, so an
injective `toValue` with a partial inverse is exactly a `Bijective` `EncRel`. -/
theorem encRel_bijective [Encode α] : (encRel α).Bijective :=
  ⟨encRel_functional, encRel_deterministic⟩

/-- `ofValue` never lies: everything it accepts really is an encoding. -/
theorem encRel_decoderSound [Encode α] : (encRel α).DecoderSound Encode.ofValue :=
  fun _ _ h => Encode.ofValue_eq_some_iff.mp h

/-- `ofValue` never refuses an encoding. -/
theorem encRel_decoderComplete [Encode α] : (encRel α).DecoderComplete Encode.ofValue :=
  fun _ _ h => Encode.ofValue_eq_some_iff.mpr h

/-- `toValue` is a correct encoder for the relation it induces. -/
theorem encRel_encoderCorrect [Encode α] : (encRel α).EncoderCorrect Encode.toValue :=
  fun _ => rfl

end Rel

/-! ## The scalar instances

`nat`, `int`, `bool` and `text` are `NumT NatT`, `NumT IntT`, `BoolT` and
`TextT` (`spectec/src/il/ast.ml:31-33`), and `Sem/Value.lean` has exactly one
constructor for each. -/

/-- SpecTec's `nat` (`NumT NatT`). -/
instance instEncodeNat : Encode Nat where
  toValue n := .num (.natN n)
  ofValue := Value.asNat?
  ofValue_toValue _ := rfl
  toValue_ofValue _ _ h := (Value.asNat?_eq_some.mp h).symm

/-- SpecTec's `int` (`NumT IntT`).  A `Nat` is *not* encoded as an `intN`:
`Xl.Num` keeps the two apart (`spectec/src/xl/num.ml:174`), and `Sem/Value.lean`'s
`Value.asInt?` rejects a `natN` for that reason. -/
instance instEncodeInt : Encode Int where
  toValue i := .num (.intN i)
  ofValue := Value.asInt?
  ofValue_toValue _ := rfl
  toValue_ofValue _ _ h := (Value.asInt?_eq_some.mp h).symm

/-- SpecTec's `bool` (`BoolT`). -/
instance instEncodeBool : Encode Bool where
  toValue b := .bool b
  ofValue := Value.asBool?
  ofValue_toValue _ := rfl
  toValue_ofValue _ _ h := (Value.asBool?_eq_some.mp h).symm

/-- SpecTec's `text` (`TextT`).  Note that the Wasm type `name` is **not**
`text`: it is a one-case variant over `char*` (see `Encode.ofPercentNat`), so a
Wasm name corresponds to a `List Char`, not to a `String`. -/
instance instEncodeString : Encode String where
  toValue s := .text s
  ofValue := Value.asText?
  ofValue_toValue _ := rfl
  toValue_ofValue _ _ h := (Value.asText?_eq_some.mp h).symm

@[simp] theorem toValue_nat (n : Nat) : Encode.toValue n = Value.num (.natN n) := rfl
@[simp] theorem toValue_int (i : Int) : Encode.toValue i = Value.num (.intN i) := rfl
@[simp] theorem toValue_bool (b : Bool) : Encode.toValue b = Value.bool b := rfl
@[simp] theorem toValue_string (s : String) : Encode.toValue s = Value.text s := rfl

/-! ## The structural instances

`IterT t Opt`, `IterT t List` and `TupT` (`spectec/src/il/ast.ml:34-35`). -/

section Structural

variable {α β : Type}

/-- The encoding of a list, elementwise (`IterT t List`). -/
def listToValue [Encode α] (as : List α) : Value := .list (as.map Encode.toValue)

/-- Decode a list of values elementwise.  Written with explicit recursion
rather than `List.mapM`, so that the round-trip proofs are two inductions. -/
def valuesOf [Encode α] : List Value → Option (List α)
  | [] => some []
  | v :: vs =>
      match Encode.ofValue v, valuesOf vs with
      | some a, some as => some (a :: as)
      | _, _ => none

/-- The decoder for `listToValue`. -/
def listOfValue [Encode α] (v : Value) : Option (List α) := v.asList?.bind valuesOf

/-- `valuesOf` inverts the elementwise encoding. -/
theorem valuesOf_map_toValue [Encode α] (as : List α) :
    valuesOf (as.map Encode.toValue) = some as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [valuesOf, Encode.ofValue_toValue a, ih]

/-- `valuesOf` is defined only on elementwise encodings. -/
theorem map_toValue_of_valuesOf [Encode α] :
    ∀ {vs : List Value} {as : List α}, valuesOf vs = some as → as.map Encode.toValue = vs := by
  intro vs
  induction vs with
  | nil => intro as h; cases h; rfl
  | cons v vs ih =>
      intro as h
      simp only [valuesOf] at h
      split at h
      · rename_i a as' ha has
        cases h
        simp [Encode.toValue_ofValue v a ha, ih has]
      · exact absurd h (by simp)

/-- SpecTec's `t*` (`IterT t List`), elementwise. -/
instance instEncodeList [Encode α] : Encode (List α) where
  toValue := listToValue
  ofValue := listOfValue
  ofValue_toValue as := by simp [listToValue, listOfValue, valuesOf_map_toValue]
  toValue_ofValue v as h := by
    match v with
    | .list vs =>
        simp only [listOfValue, Value.asList?_list, Option.bind_some] at h
        simp [listToValue, map_toValue_of_valuesOf h]
    | .bool _ | .num _ | .text _ | .tuple _ | .case _ _ | .struct _ | .opt _ =>
        simp [listOfValue, Value.asList?] at h

/-- The encoding of an option (`IterT t Opt`). -/
def optToValue [Encode α] (o : Option α) : Value := .opt (o.map Encode.toValue)

/-- The decoder for `optToValue`. -/
def optOfValue [Encode α] (v : Value) : Option (Option α) :=
  v.asOpt?.bind fun o =>
    match o with
    | none => some none
    | some w =>
        match Encode.ofValue w with
        | some a => some (some a)
        | none => none

/-- SpecTec's `t?` (`IterT t Opt`). -/
instance instEncodeOption [Encode α] : Encode (Option α) where
  toValue := optToValue
  ofValue := optOfValue
  ofValue_toValue o := by
    cases o with
    | none => rfl
    | some a => simp [optToValue, optOfValue, Encode.ofValue_toValue a]
  toValue_ofValue v o h := by
    match v with
    | .opt none => simp only [optOfValue, Value.asOpt?_opt, Option.bind_some] at h
                   cases h; rfl
    | .opt (some w) =>
        simp only [optOfValue, Value.asOpt?_opt, Option.bind_some] at h
        split at h
        · rename_i a ha
          cases h
          simp [optToValue, Encode.toValue_ofValue w a ha]
        · exact absurd h (by simp)
    | .bool _ | .num _ | .text _ | .tuple _ | .case _ _ | .struct _ | .list _ =>
        simp [optOfValue, Value.asOpt?] at h

/-- The encoding of a pair: a **binary** `TupT`.  See the module docstring —
this does not flatten nested products. -/
def prodToValue [Encode α] [Encode β] (p : α × β) : Value :=
  .tuple [Encode.toValue p.1, Encode.toValue p.2]

/-- The decoder for `prodToValue`. -/
def prodOfValue [Encode α] [Encode β] (v : Value) : Option (α × β) :=
  v.asTuple?.bind fun vs =>
    match vs with
    | [v₁, v₂] =>
        match Encode.ofValue v₁, Encode.ofValue v₂ with
        | some a, some b => some (a, b)
        | _, _ => none
    | _ => none

/-- SpecTec's two-binder `TupT`. -/
instance instEncodeProd [Encode α] [Encode β] : Encode (α × β) where
  toValue := prodToValue
  ofValue := prodOfValue
  ofValue_toValue p := by
    simp [prodToValue, prodOfValue, Encode.ofValue_toValue p.1, Encode.ofValue_toValue p.2]
  toValue_ofValue v p h := by
    match v with
    | .tuple [v₁, v₂] =>
        simp only [prodOfValue, Value.asTuple?_tuple, Option.bind_some] at h
        split at h
        · rename_i a b ha hb
          cases h
          simp [prodToValue, Encode.toValue_ofValue v₁ a ha, Encode.toValue_ofValue v₂ b hb]
        · exact absurd h (by simp)
    | .tuple [] | .tuple [_] | .tuple (_ :: _ :: _ :: _) =>
        simp [prodOfValue, Value.asTuple?_tuple] at h
    | .bool _ | .num _ | .text _ | .case _ _ | .struct _ | .list _ | .opt _ =>
        simp [prodOfValue, Value.asTuple?] at h

@[simp] theorem toValue_list [Encode α] (as : List α) :
    Encode.toValue as = Value.list (as.map Encode.toValue) := rfl

@[simp] theorem toValue_option [Encode α] (o : Option α) :
    Encode.toValue o = Value.opt (o.map Encode.toValue) := rfl

@[simp] theorem toValue_prod [Encode α] [Encode β] (a : α) (b : β) :
    Encode.toValue (a, b) = Value.tuple [Encode.toValue a, Encode.toValue b] := rfl

end Structural

/-! ## The variant convention

See the module docstring.  `caseV` is the `TupT`-payload spelling, `percentV`
the one-field `%` injection that every "numeral with a side condition" type in
the pinned specifications uses. -/

section Variant

variable {α : Type}

/-- `Value.case op (Value.tuple vs)`: the injection by the mixop whose
rendering is `op`, with the `n` components an `n`-ary surface case elaborates
to a `TupT` of. -/
def caseV (op : MixopS) (vs : List Value) : Value := .case op (.tuple vs)

/-- `%(v)`, the one-case variant that `bit`, `byte`, `char`, `uN(N)` and
`sN(N)` all elaborate to (`specs/spectec/wasm-3.0.ast`, the `byte` and `uN`
definitions: `(case "%" (tup (bind "i" nat)) (if …))`). -/
def percentV (v : Value) : Value := caseV "%" [v]

/-- `percentV` unfolded. -/
theorem percentV_eq (v : Value) : percentV v = .case "%" (.tuple [v]) := rfl

/-- `caseV` is injective in both arguments. -/
theorem caseV_inj {op op' : MixopS} {vs vs' : List Value}
    (h : caseV op vs = caseV op' vs') : op = op' ∧ vs = vs' := by
  simp only [caseV, Value.case.injEq, Value.tuple.injEq] at h
  exact h

/-- **The generic variant instance builder.**  `view` reads a Lean value as a
mixop rendering plus a payload, `unview` is its partial inverse, and the two
laws are the round trips.  Both are usually `by rintro ⟨⟩ <;> rfl`-shaped,
which is the minimal boilerplate the brief asks for: one line per constructor
in `view`, one in `unview`, and two tactic blocks for the whole inductive. -/
@[instance_reducible]
def Encode.ofCase (view : α → MixopS × Value) (unview : MixopS → Value → Option α)
    (h₁ : ∀ a, unview (view a).1 (view a).2 = some a)
    (h₂ : ∀ op v a, unview op v = some a → view a = (op, v)) : Encode α where
  toValue a := .case (view a).1 (view a).2
  ofValue v := v.asCase?.bind fun p => unview p.1 p.2
  ofValue_toValue a := by simpa using h₁ a
  toValue_ofValue v a h := by
    match v with
    | .case op w =>
        simp only [Value.asCase?_case, Option.bind_some] at h
        rw [h₂ op w a h]
    | .bool _ | .num _ | .text _ | .tuple _ | .struct _ | .list _ | .opt _ =>
        simp [Value.asCase?] at h

/-- **The `%`-wrapper instance builder.**  A Lean type that corresponds to a
one-case `%` variant over a numeral is determined by the numeral map and its
partial inverse. -/
@[instance_reducible]
def Encode.ofPercentNat (toNat : α → Nat) (ofNat? : Nat → Option α)
    (h₁ : ∀ a, ofNat? (toNat a) = some a)
    (h₂ : ∀ n a, ofNat? n = some a → toNat a = n) : Encode α where
  toValue a := percentV (.num (.natN (toNat a)))
  ofValue v :=
    v.asCase?.bind fun p =>
      if p.1 = "%" then
        p.2.asTuple?.bind fun vs =>
          match vs with
          | [w] => w.asNat?.bind ofNat?
          | _ => none
      else none
  ofValue_toValue a := by simpa [percentV, caseV] using h₁ a
  toValue_ofValue v a h := by
    match v with
    | .case op w =>
        simp only [Value.asCase?_case, Option.bind_some] at h
        split at h
        · rename_i hop
          subst hop
          match w with
          | .tuple [u] =>
              simp only [Value.asTuple?_tuple, Option.bind_some] at h
              match u with
              | .num (.natN n) =>
                  simp only [Value.asNat?_num_natN, Option.bind_some] at h
                  simp [percentV, caseV, h₂ n a h]
              | .num (.intN _) | .num (.ratN _) | .num (.realN _)
              | .bool _ | .text _ | .tuple _ | .case _ _ | .struct _ | .list _ | .opt _ =>
                  simp [Value.asNat?] at h
          | .tuple [] | .tuple (_ :: _ :: _) =>
              simp only [Value.asTuple?_tuple, Option.bind_some] at h
              exact absurd h (by simp)
          | .bool _ | .num _ | .text _ | .case _ _ | .struct _ | .list _ | .opt _ =>
              simp [Value.asTuple?] at h
        · exact absurd h (by simp)
    | .bool _ | .num _ | .text _ | .tuple _ | .struct _ | .list _ | .opt _ =>
        simp [Value.asCase?] at h

/-- `Nat`-valued injection of `UInt8`, inverted by a guarded `UInt8.ofNat`. -/
def uint8OfNat? (n : Nat) : Option UInt8 :=
  let b := UInt8.ofNat n
  if b.toNat = n then some b else none

/-- SpecTec's `byte`, which is `%(i)` with `0 ≤ i ≤ 255`
(`specification/wasm-3.0/1.1-syntax.values.spectec:8`). -/
instance instEncodeUInt8 : Encode UInt8 :=
  Encode.ofPercentNat UInt8.toNat uint8OfNat?
    (fun b => by simp [uint8OfNat?, UInt8.ofNat_toNat])
    (fun n b h => by
      simp only [uint8OfNat?] at h
      split at h
      · rename_i hb; cases h; exact hb
      · exact absurd h (by simp))

/-- `Nat`-valued injection of `Char`, inverted by a guarded `Char.ofNat`.  The
guard is the round trip itself rather than `Nat.isValidChar`, which keeps the
two laws free of any reasoning about `Char`'s representation. -/
def charOfNat? (n : Nat) : Option Char :=
  let c := Char.ofNat n
  if c.toNat = n then some c else none

/-- SpecTec's `char`, which is `%(i)` with `i ≤ 0xD7FF ∨ 0xE000 ≤ i ≤ 0x10FFFF`
(`specs/spectec/wasm-3.0.ast`, the `char` definition) — exactly Lean's
`Nat.isValidChar`. -/
instance instEncodeChar : Encode Char :=
  Encode.ofPercentNat Char.toNat charOfNat?
    (fun c => by simp [charOfNat?, Char.ofNat_toNat])
    (fun n c h => by
      simp only [charOfNat?] at h
      split at h
      · rename_i hc; cases h; exact hc
      · exact absurd h (by simp))

@[simp] theorem toValue_uint8 (b : UInt8) :
    Encode.toValue b = percentV (.num (.natN b.toNat)) := rfl

@[simp] theorem toValue_char (c : Char) :
    Encode.toValue c = percentV (.num (.natN c.toNat)) := rfl

end Variant

/-! ## The record convention -/

section Record

variable {α : Type}

/-- **The record instance builder.**  `toFields` must list the field atoms in
the record's *declaration* order: `match_exp'` matches record fields
positionally (`eval.ml:948-949`, with the atom equality only asserted in
`match_expfield`, `eval.ml:1072-1074`), and `Sem/Type.lean`'s
`hasTypFields_cons_iff` rejects any other order. -/
@[instance_reducible]
def Encode.ofStruct (toFields : α → List (AtomS × Value))
    (ofFields : List (AtomS × Value) → Option α)
    (h₁ : ∀ a, ofFields (toFields a) = some a)
    (h₂ : ∀ fs a, ofFields fs = some a → toFields a = fs) : Encode α where
  toValue a := .struct (toFields a)
  ofValue v := v.asStruct?.bind ofFields
  ofValue_toValue a := by simpa using h₁ a
  toValue_ofValue v a h := by
    match v with
    | .struct fs =>
        simp only [Value.asStruct?_struct, Option.bind_some] at h
        rw [h₂ fs a h]
    | .bool _ | .num _ | .text _ | .tuple _ | .case _ _ | .list _ | .opt _ =>
        simp [Value.asStruct?] at h

end Record

/-! ## The typing lemma

The point of the bridge is to let an equivalence proof move between the two
worlds, and that needs the encoded values to be *well typed* in SpecTec's
sense: `HasTyp env ρ t (toValue a)`.  `Denotes` is that statement, and the
lemmas below are its closure properties, one per type former, so that a user
discharges it the way the type is built. -/

section Typing

variable {α β : Type} {env : Env} {ρ : VarEnv}

/-- "`α` corresponds to the SpecTec type `t`": every encoded `α` inhabits `t`.

This is the `Encode`-level reading of `Sem/Type.lean`'s `HasTyp`, and the
hypothesis every equivalence statement between the two worlds carries. -/
def Denotes (env : Env) (ρ : VarEnv) (t : Typ) (α : Type) [Encode α] : Prop :=
  ∀ a : α, HasTyp env ρ t (Encode.toValue a)

/-- `Bool ⟶ bool`. -/
theorem denotes_boolT : Denotes env ρ .boolT Bool :=
  fun b => hasTyp_boolT_iff.mpr ⟨b, rfl⟩

/-- `String ⟶ text`. -/
theorem denotes_textT : Denotes env ρ .textT String :=
  fun s => hasTyp_textT_iff.mpr ⟨s, rfl⟩

/-- `Nat ⟶ nat`, and — by `Xl.Num.sub` (`spectec/src/xl/num.ml:52-57`), which
`Sem/Type.lean` keeps — `Nat ⟶ int`, `rat`, `real` as well. -/
theorem denotes_numT_nat {t : NumTyp} (h : Num.subTyp .natT t) : Denotes env ρ (.numT t) Nat :=
  fun n => hasTyp_numT_iff.mpr ⟨.natN n, rfl, h⟩

/-- `Nat ⟶ nat`. -/
theorem denotes_natT : Denotes env ρ (.numT .natT) Nat := denotes_numT_nat rfl

/-- `Int ⟶ int`, and by subsumption `Int ⟶ rat`, `real`. -/
theorem denotes_numT_int {t : NumTyp} (h : Num.subTyp .intT t) : Denotes env ρ (.numT t) Int :=
  fun i => hasTyp_numT_iff.mpr ⟨.intN i, rfl, h⟩

/-- `Int ⟶ int`. -/
theorem denotes_intT : Denotes env ρ (.numT .intT) Int := denotes_numT_int rfl

/-- `List α ⟶ t*` whenever `α ⟶ t`. -/
theorem denotes_iterT_list [Encode α] {t : Typ} (h : Denotes env ρ t α) :
    Denotes env ρ (.iterT t .list) (List α) := by
  intro as
  refine hasTyp_iterT_list_iff.mpr ⟨as.map Encode.toValue, rfl, hasTypList_iff.mpr ?_⟩
  intro w hw
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hw
  exact h a

/-- `Option α ⟶ t?` whenever `α ⟶ t`. -/
theorem denotes_iterT_opt [Encode α] {t : Typ} (h : Denotes env ρ t α) :
    Denotes env ρ (.iterT t .opt) (Option α) := by
  intro o
  cases o with
  | none => exact hasTyp_iterT_opt_iff.mpr (Or.inl rfl)
  | some a => exact hasTyp_iterT_opt_iff.mpr (Or.inr ⟨_, rfl, h a⟩)

/-- `α × β ⟶ (x : t₁, y : t₂)` for a two-binder `TupT`.  The second component's
hypothesis is taken in the scope the first binder extends, because `TupT`'s
binders are dependent (`valid_typ_bind`, `spectec/src/il/valid.ml:243-245`);
for a `t₂` that does not mention `x` it is discharged uniformly in `ρ`. -/
theorem denotes_tupT_prod [Encode α] [Encode β] {x y : IL.Id} {t₁ t₂ : Typ}
    (h₁ : Denotes env ρ t₁ α)
    (h₂ : ∀ a : α, Denotes env (ρ.bindVal x (Encode.toValue a)) t₂ β) :
    Denotes env ρ (.tupT [.mk x t₁, .mk y t₂]) (α × β) := by
  rintro ⟨a, b⟩
  refine hasTyp_tupT_iff.mpr ⟨_, rfl, hasTypTup_cons_iff.mpr ⟨_, _, rfl, h₁ a, ?_⟩⟩
  exact hasTypTup_cons_iff.mpr ⟨_, _, rfl, h₂ a b, hasTypTup_nil_iff.mpr rfl⟩

/-- The empty tuple inhabits the empty tuple type. -/
theorem hasTyp_tupT_nil : HasTyp env ρ (.tupT []) (.tuple []) :=
  hasTyp_tupT_iff.mpr ⟨[], rfl, hasTypTup_nil_iff.mpr rfl⟩

/-- **A `case` inhabits a monomorphic variant type name.**  This is the step a
variant instance's `Denotes` proof goes through: resolve the name through the
environment, match the single instance's argument patterns, and hit the right
`typcase`.  Stated for an arbitrary instance list so that the caller supplies
`HasTypInsts` however the declaration demands. -/
theorem hasTyp_varT_of_insts {x : IL.Id} {args : List Arg} {td : TypDef} {ws : List ArgV}
    {v : Value} (hl : localTyp? ρ x args = none) (htd : env.findTyp? x = some td)
    (hargs : EvalArgs env ρ args ws) (hi : HasTypInsts env td.2 ws v) :
    HasTyp env ρ (.varT x args) v :=
  (hasTyp_varT_global_iff hl).mpr ⟨td, ws, htd, hargs, hi⟩

/-- The single-instance case of `hasTyp_varT_of_insts`, specialised to a
variant: the shape every `Encode.ofCase` instance is justified at. -/
theorem hasTyp_varT_case {x : IL.Id} {args : List Arg} {qs qs' : List Param}
    {pats : List Arg} {cs : List TypCase} {ws : List ArgV} {σ : VarEnv}
    {op : MixopS} {w : Value}
    (hl : localTyp? ρ x args = none)
    (htd : env.findTyp? x = some (qs, [.instD qs' pats (.variantT cs)]))
    (hargs : EvalArgs env ρ args ws) (hm : MatchArgs env VarEnv.empty pats ws σ)
    (hc : HasTypCase env σ cs op w) :
    HasTyp env ρ (.varT x args) (.case op w) :=
  hasTyp_varT_of_insts hl htd hargs
    (hasTypInsts_head hm (hasTypDef_variantT_iff.mpr ⟨op, w, rfl, hc⟩))

/-- The single-instance case of `hasTyp_varT_of_insts`, specialised to a
record: the shape every `Encode.ofStruct` instance is justified at. -/
theorem hasTyp_varT_struct {x : IL.Id} {args : List Arg} {qs qs' : List Param}
    {pats : List Arg} {fs : List TypField} {ws : List ArgV} {σ : VarEnv}
    {gs : List (AtomS × Value)}
    (hl : localTyp? ρ x args = none)
    (htd : env.findTyp? x = some (qs, [.instD qs' pats (.structT fs)]))
    (hargs : EvalArgs env ρ args ws) (hm : MatchArgs env VarEnv.empty pats ws σ)
    (hf : HasTypFields env σ fs gs) :
    HasTyp env ρ (.varT x args) (.struct gs) :=
  hasTyp_varT_of_insts hl htd hargs
    (hasTypInsts_head hm (hasTypDef_structT_iff.mpr ⟨gs, rfl, hf⟩))

/-- An argument list is irrelevant to `localTyp?` as soon as it is non-empty
(`Sem/Type.lean`'s `localTyp?`), which is what makes `hasTyp_varT_case` usable
for a parameterised type name such as `uN(N)` with no side condition on `ρ`. -/
theorem localTyp?_cons (x : IL.Id) (a : Arg) (args : List Arg) :
    localTyp? ρ x (a :: args) = none := rfl

/-- `Denotes` transports along the `EncRel`: if `α ⟶ t` then every value in the
image of the bridge inhabits `t`.  This is the form an equivalence proof uses,
where the value is given by the grammar denotation rather than by an `a`. -/
theorem hasTyp_of_encRel [Encode α] {t : Typ} {v : Value} {a : α}
    (hd : Denotes env ρ t α) (h : encRel α v a) : HasTyp env ρ t v := by
  rw [encRel_apply] at h
  exact h ▸ hd a

end Typing

end Silmaril.SpecTec.Sem
