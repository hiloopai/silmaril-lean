module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Text
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.BinaryModule
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Text6x

/-!
# The carrier change, pinned: where the two denotations agree

`Equiv/Text.lean` gives §6 a denotation `charRel` over `List Nat`, because
`Sem/Grammar.lean`'s `gramRelSup` — whose carrier is `List UInt8` — is empty
on the whole of the text format (`gramRelSup_tchar_eq_bot`).  That file closes
by naming the theorem it does not prove:

> `Derives` is *not* proved to agree with `Sem.gramRelSup` on grammars where
> both are non-trivial.  It cannot be, as stated: the two differ on the arity
> question by design.  Pinning the exact relationship — `push utf8Codes` of
> `charRel` versus `gramRelSup`, for the ASCII, unit-free fragment — is the
> obvious next theorem and is not here.

This file is that theorem.

## The two differences, and the fragment that avoids them

`Derives` departs from `Sem.SymDerives` in exactly two places.

* **The carrier.**  `Sem.byteSym` sends `NumG n` with `n ≥ 0x100` to
  `Sym.alt []`, and `Sem.rangeSym` does the same to a range with a non-byte
  endpoint; `Derives` reads both as scalars.  The two agree on a terminal
  exactly when it is a *byte* terminal and, since the bridge is UTF-8, when
  that byte is its own encoding — that is, below `0x80`.
* **The arity.**  `Sem.Act` makes a symbol contribute a *list* of values and
  gives `EpsG`, `SeqG` and `AltG` the concatenation of their factors', where
  `il/valid.ml:588-595` types all three at `TupT []`.  `Derives` contributes
  one value of the symbol's own type.  The list is *discarded* in two of the
  three places a symbol is used — a `ProdD` body (`prodActFn`, whose value is
  `EvalExp` of the production's expression) and nowhere else — and *consumed*
  in the other two: `attrActFn` and `roundActFn` both demand a one-element
  list.  So the two denotations agree on a symbol exactly when every `AttrG`
  and every `IterG` in it stands over a symbol that contributes one value,
  which `EpsG`, `SeqG`, `AltG` and `TextG` never do.

`Agree` and `Scoped` below cut out that fragment: `Agree g` says `g`
contributes a single value and the two denotations give the *same* one;
`Scoped g` says only that they derive the same byte strings and leave the
same scope, which is all a `ProdD` body needs.  `Scoped` is the weaker, and
`Scoped.agree` embeds one in the other.

Both are relative to a set `S` of nonterminals, because the condition is not
a property of `env` as a whole: `envPinned` also holds §5, every byte of
which is outside the fragment.  `GramsOk env S` is the hypothesis that `S` is
closed — each of its grammars is parameterless, and each of its production
bodies is `Scoped`.

## What is proved

* `fwd` and `bwd`: the two implications, by induction on the derivation and
  on `denoteAt`'s step index respectively.  Both carry the `Agree`/`Scoped`
  pair simultaneously, since each calls the other at a `ProdD` body.
* `textByteRel_eq_gramRelSup`: on the fragment the two are **equal** as
  `EncRel`s — `EncRel.push utf8Codes (charRel env ρ g) = gramRelSup env ρ g`.
  It is stated for `Agree` symbols only, and must be: at a `Scoped`-only
  symbol `Sem.Act` contributes a value list of length other than one and
  `gramRelSup` is empty where `charRel` is not.
* `textByteRel_tidchar_eq_gramRelSup_pinned` and `…_corrected`: the pinned
  `Tidchar` is in the fragment — all twenty-six of its terminals are below
  `0x80` — so the equality holds of a grammar of the stream, not only of a
  hypothetical one.  `Tchar` is not, and `gramRelSup_tchar_eq_bot` is why.
* `gramRelSup_tidchar_pinned_iff`: the resulting byte relation in closed form.
  It is the first non-trivial statement about `Sem.gramRelSup` anywhere in §6.

## What is not proved

* The fragment excludes every grammar with a grammar *parameter*.  None of §6
  has one, but `GramsOk` asserts it rather than deriving it, because
  `gramArgSubst` would otherwise substitute a caller's symbol into the body
  and no structural condition on the body alone can control that.
* `Tchar`, `Tnewline`, `Tspace`, `Tblockcomment` and the rest of §6.0 are
  outside the fragment — the first by its carrier, the others by their arity.
  For them `Equiv/Text.lean`'s `charRel` remains the only denotation, and the
  equation above says nothing.  Nothing here weakens the two obstacles; it
  delimits them.
-/

@[expose] public section

namespace Silmaril.SpecTec.Equiv.Text

open Silmaril.SpecTec.IL hiding Id Prod Sym
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Grammar
open Silmaril.SpecTec.Equiv.BinaryModule (Rounds symDerives_iterG tupleRow_injective)

set_option maxRecDepth 100000

/-! ## ASCII

Below `0x80` a scalar is its own UTF-8 encoding, which is what makes
`utf8Codes` a bijection on the fragment's strings. -/

/-- A scalar below `0x80`. -/
abbrev IsAscii (n : Nat) : Prop := n < 0x80

/-- An ASCII scalar is its own UTF-8 encoding. -/
theorem utf8Codes_singleton_ascii {n : Nat} (h : IsAscii n) :
    utf8Codes [n] = [UInt8.ofNat n] := by
  have hn : (Char.ofNat n).val.toNat = n := Unicode.charToNat_ofNat (Or.inl (by omega))
  simp only [utf8Codes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    String.utf8EncodeChar, hn]
  split
  · rfl
  · omega

/-! ## The fragment

`Agree` and `Scoped` are mutually inductive because `Scoped.agree` embeds the
first in the second and every other `Scoped` form has `Scoped` children.
Both are relative to a set `S` of nonterminals; see the module docstring. -/

mutual

/-- `g` contributes **one** value, and `Sem.SymDerives` gives the same one.
Every terminal is a byte below `0x80`, so that the carrier change is the
identity on it, and every `AttrG`/`IterG` stands over a symbol that is itself
single-valued — which is what `attrActFn` and `roundActFn` demand. -/
inductive Agree (S : IL.Id → Prop) : IL.Sym → Prop where
  /-- An ASCII literal terminal. -/
  | numG {n : Nat} (h : IsAscii n) : Agree S (.numG n)
  /-- An ASCII range. -/
  | rangeG {lo hi : Nat} (hlo : IsAscii lo) (hhi : IsAscii hi) :
      Agree S (.rangeG (.numG lo) (.numG hi))
  /-- `AttrG (e, g)`: both sides pass `g`'s one value to `e`. -/
  | attrG {e : Exp} {g : IL.Sym} (hg : Agree S g) : Agree S (.attrG e g)
  /-- `IterG (g, (it, ds))`: both sides collect one value per round. -/
  | iterG {g : IL.Sym} {it : Iter} {ds : List Dom} (hg : Agree S g) :
      Agree S (.iterG g (.mk it ds))
  /-- A nonterminal of `S`, called without arguments.  Both sides take the
  value from the production's expression, so nothing is required of the body
  beyond `Scoped`. -/
  | varG {x : IL.Id} (hx : S x) : Agree S (.varG x [])

/-- `g` derives the same byte strings and leaves the same scope, with no claim
about the value — which is all a `ProdD` body needs, since `prodActFn`
discards it.  `EpsG`, `TextG`, `SeqG` and `AltG` live here and nowhere else:
`Sem.Act` gives them a value *list* where `Derives` gives the unit of
`TupT []`. -/
inductive Scoped (S : IL.Id → Prop) : IL.Sym → Prop where
  /-- `EpsG`. -/
  | epsG : Scoped S .epsG
  /-- A literal string.  No ASCII condition: `utf8Codes_codes` says the two
  carriers spell a literal the same way at every scalar, and a `TextG` never
  stands under an `AttrG` or an `IterG` in the fragment, so its value list is
  always discarded. -/
  | textG {t : Text} : Scoped S (.textG t)
  /-- `SeqG`. -/
  | seqG {gs : List IL.Sym} (h : ScopedAll S gs) : Scoped S (.seqG gs)
  /-- `AltG`. -/
  | altG {gs : List IL.Sym} (h : ScopedAll S gs) : Scoped S (.altG gs)
  /-- Everything single-valued is in particular scope-faithful. -/
  | agree {g : IL.Sym} (h : Agree S g) : Scoped S g

/-- `Scoped`, factor by factor. -/
inductive ScopedAll (S : IL.Id → Prop) : List IL.Sym → Prop where
  /-- The empty sequence. -/
  | nil : ScopedAll S []
  /-- One factor, then the rest. -/
  | cons {g : IL.Sym} {gs : List IL.Sym} (h : Scoped S g) (hs : ScopedAll S gs) :
      ScopedAll S (g :: gs)

end

/-- A member of a `ScopedAll` list is `Scoped`. -/
theorem ScopedAll.mem {S : IL.Id → Prop} :
    ∀ {gs : List IL.Sym}, ScopedAll S gs → ∀ {g : IL.Sym}, g ∈ gs → Scoped S g
  | _, .nil, _, hm => absurd hm (List.not_mem_nil)
  | _, .cons h hs, _, hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h
      · exact hs.mem hm

/-- The grammars of `S` are closed and parameterless: this is the hypothesis
that makes `Agree.varG` sound.  A `GramD` with grammar parameters is excluded
outright — `gramArgSubst` would then substitute arbitrary symbols into the
body, which no structural condition on the body alone can control, and no
grammar of §6 has any. -/
def GramsOk (env : Env) (S : IL.Id → Prop) : Prop :=
  ∀ x, S x → ∃ t prods, env.findGram? x = some ([], t, prods) ∧
    ∀ qs g e prems, IL.Prod.prodD qs g e prems ∈ prods → Scoped S g

/-! ### The substitution is trivial on the fragment

`Derives.varG` and `ProdDerives` both derive `substSym (gramArgSubst ps args) g`.
`GramsOk` forces `ps = []` and `Agree.varG` forces `args = []`, so the
substitution is empty — and empty substitution is the identity on the
fragment, where no `VarG` carries arguments. -/

/-- `gramArgSubst` of two empty lists. -/
@[simp] theorem gramArgSubst_nil_nil : gramArgSubst [] [] = [] := rfl

mutual

/-- The empty substitution is the identity on a single-valued symbol. -/
theorem Agree.substSym_nil {S : IL.Id → Prop} :
    ∀ {g : IL.Sym}, Agree S g → substSym [] g = g
  | _, .numG _ => rfl
  | _, .rangeG _ _ => rfl
  | _, .attrG hg => by rw [substSym, hg.substSym_nil]
  | _, .iterG hg => by rw [substSym, hg.substSym_nil]
  | _, .varG _ => rfl

/-- The empty substitution is the identity on a scope-faithful symbol. -/
theorem Scoped.substSym_nil {S : IL.Id → Prop} :
    ∀ {g : IL.Sym}, Scoped S g → substSym [] g = g
  | _, .epsG => rfl
  | _, .textG => rfl
  | _, .seqG h => by rw [substSym, h.substSyms_nil]
  | _, .altG h => by rw [substSym, h.substSyms_nil]
  | _, .agree h => h.substSym_nil

/-- …and on a list of them. -/
theorem ScopedAll.substSyms_nil {S : IL.Id → Prop} :
    ∀ {gs : List IL.Sym}, ScopedAll S gs → substSyms [] gs = gs
  | _, .nil => rfl
  | _, .cons h hs => by rw [substSyms, h.substSym_nil, hs.substSyms_nil]

end

/-! ## The value list of a literal

`Sem.transSym` sends `TextG t` to `Sym.bytes (Unicode.utf8 t)`, whose
attribute is the `app`-fold `actAlg.ofBytes`.  It contributes one value per
*byte*, where `Derives` contributes the single `Value.text t`; that is the
arity difference, in the one place where it is harmless, since a `TextG` is
never the child of an `AttrG` or an `IterG` in the fragment. -/

/-- The value list a literal byte string contributes. -/
def byteValues (bs : Grammar.Bytes) : List Value :=
  bs.map fun b => .num (.natN b.toNat)

/-- `actAlg.ofBytes` holds of exactly that list, and changes no scope. -/
theorem actAlg_ofBytes_apply (bs : Grammar.Bytes) (ρ : VarEnv) :
    actAlg.ofBytes bs ρ (byteValues bs) ρ := by
  induction bs with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
      refine ⟨[.num (.natN b.toNat)], ρ, byteValues bs, ⟨rfl, rfl⟩, ih, rfl⟩

/-- `TextG t`, as a `SymDerives`. -/
theorem symDerives_textG {env : Env} {ρ : VarEnv} {t : Text} :
    SymDerives env ρ (.textG t) (Unicode.utf8 t) (byteValues (Unicode.utf8 t)) ρ :=
  ⟨actAlg.ofBytes (Unicode.utf8 t), by rw [symDen_textG]; exact ⟨rfl, rfl⟩,
    actAlg_ofBytes_apply _ ρ⟩

/-! ### Inverting `Scoped`

`EpsG`, `TextG`, `SeqG` and `AltG` are the only forms `Scoped` admits outside
`Scoped.agree`, so for every other form the two predicates coincide. -/

/-- `Scoped` at a literal terminal. -/
theorem Scoped.agree_numG {S : IL.Id → Prop} {n : Nat} (h : Scoped S (.numG n)) :
    Agree S (.numG n) := by cases h with | agree h => exact h

/-- `Scoped` at a range. -/
theorem Scoped.agree_rangeG {S : IL.Id → Prop} {g₁ g₂ : IL.Sym}
    (h : Scoped S (.rangeG g₁ g₂)) : Agree S (.rangeG g₁ g₂) := by
  cases h with | agree h => exact h

/-- `Scoped` at an `AttrG`. -/
theorem Scoped.agree_attrG {S : IL.Id → Prop} {e : Exp} {g : IL.Sym}
    (h : Scoped S (.attrG e g)) : Agree S (.attrG e g) := by
  cases h with | agree h => exact h

/-- `Scoped` at an `IterG`. -/
theorem Scoped.agree_iterG {S : IL.Id → Prop} {g : IL.Sym} {it : IterExp}
    (h : Scoped S (.iterG g it)) : Agree S (.iterG g it) := by
  cases h with | agree h => exact h

/-- `Scoped` at a nonterminal. -/
theorem Scoped.agree_varG {S : IL.Id → Prop} {x : IL.Id} {args : List IL.Arg}
    (h : Scoped S (.varG x args)) : Agree S (.varG x args) := by
  cases h with | agree h => exact h

/-- `Scoped` at a `SeqG`. -/
theorem Scoped.all_seqG {S : IL.Id → Prop} {gs : List IL.Sym}
    (h : Scoped S (.seqG gs)) : ScopedAll S gs := by
  cases h with
  | seqG h => exact h
  | agree h => cases h

/-- `Scoped` at an `AltG`. -/
theorem Scoped.all_altG {S : IL.Id → Prop} {gs : List IL.Sym}
    (h : Scoped S (.altG gs)) : ScopedAll S gs := by
  cases h with
  | altG h => exact h
  | agree h => cases h

/-- An ASCII scalar is the byte it encodes to. -/
theorem toNat_ofNat_ascii {n : Nat} (h : IsAscii n) : (UInt8.ofNat n).toNat = n := by
  simp only [UInt8.toNat_ofNat']
  omega

/-! ## `Derives` implies `SymDerives`

The first half of the agreement: on the fragment the character denotation
derives nothing the byte denotation does not.  By induction on the derivation,
using the `symDerives_*` inversions of `Sem/Grammar.lean` and
`Equiv/BinaryModule.lean`'s `symDerives_iterG`. -/

/-- The claim at a symbol: its single value if it has one, and in any case the
same bytes and the same scope. -/
def Fwd (env : Env) (S : IL.Id → Prop) (ρ : VarEnv) (g : IL.Sym) (cs : Codes)
    (v : Value) (ρ' : VarEnv) : Prop :=
  (Agree S g → SymDerives env ρ g (utf8Codes cs) [v] ρ') ∧
  (Scoped S g → ∃ l, SymDerives env ρ g (utf8Codes cs) l ρ')

/-- The claim at a `SeqG`'s factor list. -/
def FwdSeq (env : Env) (S : IL.Id → Prop) (ρ : VarEnv) (gs : List IL.Sym) (cs : Codes)
    (ρ' : VarEnv) : Prop :=
  ScopedAll S gs → ∃ l, SymDerives env ρ (.seqG gs) (utf8Codes cs) l ρ'

/-- The claim at an `IterG`'s rounds. -/
def FwdRounds (env : Env) (S : IL.Id → Prop) (ρ : VarEnv) (ds : List Dom) (g : IL.Sym)
    (rows : List (Value × List Value)) (cs : Codes) : Prop :=
  Agree S g → Rounds env ρ g ds (utf8Codes cs) rows

/-- `Fwd` from the single-valued half alone, for a form `Scoped` only reaches
through `Scoped.agree`. -/
theorem Fwd.of_agree {env : Env} {S : IL.Id → Prop} {ρ : VarEnv} {g : IL.Sym} {cs : Codes}
    {v : Value} {ρ' : VarEnv} (h : Agree S g → SymDerives env ρ g (utf8Codes cs) [v] ρ')
    (hinv : Scoped S g → Agree S g) : Fwd env S ρ g cs v ρ' :=
  ⟨h, fun hS => ⟨[v], h (hinv hS)⟩⟩

/-- **The forward half.**  On the fragment, every character derivation is a
byte derivation of the UTF-8 encoding, with the same value and the same
scope.

The recursor is applied with named holes rather than `induction … with`,
because `DerivesSeq` and `DerivesRounds` both have constructors called `nil`
and `cons` and the case tags would be ambiguous. -/
theorem fwd {env : Env} {S : IL.Id → Prop} (hE : GramsOk env S) {ρ : VarEnv} {g : IL.Sym}
    {cs : Codes} {v : Value} {ρ' : VarEnv} (h : Derives env ρ g cs v ρ') :
    Fwd env S ρ g cs v ρ' := by
  refine Derives.rec (motive_1 := fun ρ g cs v ρ' _ => Fwd env S ρ g cs v ρ')
    (motive_2 := fun ρ gs cs ρ' _ => FwdSeq env S ρ gs cs ρ')
    (motive_3 := fun ρ ds g rows cs _ => FwdRounds env S ρ ds g rows cs)
    ?epsG ?numG ?textG ?rangeG ?seqG ?altG ?iterG ?attrG ?varG
    ?seqNil ?seqCons ?roundNil ?roundCons h
  case epsG =>
      intro ρ
      refine ⟨fun hA => (by cases hA), fun _ => ⟨[], ?_⟩⟩
      exact symDerives_epsG.mpr ⟨by simp [utf8Codes], rfl, rfl⟩
  case numG =>
      intro ρ n
      refine Fwd.of_agree (fun hA => ?_) Scoped.agree_numG
      cases hA with
      | numG h =>
          refine (symDerives_numG (by omega)).mpr ⟨utf8Codes_singleton_ascii h, ?_, rfl⟩
          rw [toNat_ofNat_ascii h]
  case textG =>
      intro ρ t
      refine ⟨fun hA => (by cases hA), fun _ => ?_⟩
      rw [utf8Codes_codes]
      exact ⟨_, symDerives_textG⟩
  case rangeG =>
      intro ρ lo hi n h₁ h₂
      refine Fwd.of_agree (fun hA => ?_) Scoped.agree_rangeG
      cases hA with
      | rangeG hlo hhi =>
          have hn : IsAscii n := by unfold IsAscii at hhi ⊢; omega
          refine (symDerives_rangeG ⟨by omega, by omega⟩).mpr
            ⟨UInt8.ofNat n, ?_, ?_, utf8Codes_singleton_ascii hn, ?_, rfl⟩
          · rw [UInt8.le_iff_toNat_le, toNat_ofNat_ascii hlo, toNat_ofNat_ascii hn]
            exact h₁
          · rw [UInt8.le_iff_toNat_le, toNat_ofNat_ascii hhi, toNat_ofNat_ascii hn]
            exact h₂
          · rw [toNat_ofNat_ascii hn]
  case seqG =>
      intro ρ ρ' gs cs _ ih
      exact ⟨fun hA => (by cases hA), fun hS => ih (Scoped.all_seqG hS)⟩
  case altG =>
      intro ρ ρ' g gs cs v hm _ ih
      refine ⟨fun hA => (by cases hA), fun hS => ?_⟩
      obtain ⟨l, hl⟩ := ih.2 (ScopedAll.mem (Scoped.all_altG hS) hm)
      exact ⟨l, symDerives_altG.mpr ⟨g, hm, hl⟩⟩
  case iterG =>
      intro ρ ρ' g it ds cs rows _ hc hb ih
      refine Fwd.of_agree (fun hA => ?_) Scoped.agree_iterG
      cases hA with
      | iterG hg => exact symDerives_iterG.mpr ⟨rows, ih hg, hc, rfl, hb⟩
  case attrG =>
      intro ρ ρ₁ ρ' e g cs v _ hm ih
      refine Fwd.of_agree (fun hA => ?_) Scoped.agree_attrG
      cases hA with
      | attrG hg => exact symDerives_attrG.mpr ⟨v, ρ₁, ih.1 hg, rfl, hm⟩
  case varG =>
      intro ρ ρ₀ ρ₁ ρ₂ x args ps t prods qs g e prems ws cs v v₀ hg hp hw hbp _ hpr he ih
      refine Fwd.of_agree (fun hA => ?_) Scoped.agree_varG
      cases hA with
      | varG hx =>
          obtain ⟨t', prods', hg', hsc⟩ := hE x hx
          rw [hg] at hg'
          have hinj := Option.some.inj hg'
          have hps : ps = [] := congrArg Prod.fst hinj
          have hprods : prods = prods' := congrArg (fun p => p.2.2) hinj
          subst hps
          subst hprods
          have hgs : Scoped S g := hsc qs g e prems hp
          rw [gramArgSubst_nil_nil, hgs.substSym_nil] at ih
          obtain ⟨l₀, hl₀⟩ := ih.2 hgs
          refine (symDerives_varG hg).mpr
            ⟨rfl, .prodD qs g e prems, hp, ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, ?_, hpr, he, rfl⟩
          rw [gramArgSubst_nil_nil, hgs.substSym_nil]
          exact hl₀
  case seqNil =>
      intro ρ _
      exact ⟨[], symDerives_seqG_nil.mpr ⟨by simp [utf8Codes], rfl, rfl⟩⟩
  case seqCons =>
      intro ρ ρ₁ ρ' g gs cs₁ cs₂ v _ _ ih₁ ih₂ hall
      cases hall with
      | cons hg hgs =>
          obtain ⟨l₁, h₁⟩ := ih₁.2 hg
          obtain ⟨l₂, h₂⟩ := ih₂ hgs
          exact ⟨l₁ ++ l₂, symDerives_seqG_cons.mpr
            ⟨utf8Codes cs₁, l₁, ρ₁, utf8Codes cs₂, l₂, h₁, h₂, utf8Codes_append .., rfl⟩⟩
  case roundNil =>
      intro ρ ds g _
      simpa [utf8Codes] using Rounds.nil
  case roundCons =>
      intro ρ ρ₁ ds g cs₁ cs₂ v vs rows _ hv _ ih₁ ih₂ hA
      rw [utf8Codes_append]
      exact Rounds.cons (ih₁.1 hA) hv (ih₂ hA)

/-! ## Eliminating a step-indexed derivation

`denoteAt G (n + 1) = step G (denoteAt G n)`, so every sub-symbol — including
the factors of a `Sym.seq` and the branches of a `Sym.alt`, which `step`
interprets with `D` as well — sits at a *strictly smaller* index.  One
elimination lemma per constructor makes that bookkeeping explicit, so the
induction below is on the index alone. -/

section Elim

variable {N α : Type} {G : Gram N α} {n : Nat} {bs : Grammar.Bytes} {a : α}

/-- Nothing is derived at index zero. -/
theorem denoteAt_zero_elim (h : denoteAt G 0 .eps bs a) : False := h.elim

/-- `Sym.eps`. -/
theorem denoteAt_eps_elim (h : denoteAt G n .eps bs a) : bs = [] ∧ a = G.alg.nil := by
  cases n with
  | zero => exact h.elim
  | succ _ => exact h

/-- `Sym.byte`. -/
theorem denoteAt_byte_elim {b : UInt8} (h : denoteAt G n (.byte b) bs a) :
    bs = [b] ∧ a = G.alg.ofByte b := by
  cases n with
  | zero => exact h.elim
  | succ _ => exact h

/-- `Sym.range`. -/
theorem denoteAt_range_elim {lo hi : UInt8} (h : denoteAt G n (.range lo hi) bs a) :
    ∃ b, lo ≤ b ∧ b ≤ hi ∧ bs = [b] ∧ a = G.alg.ofByte b := by
  cases n with
  | zero => exact h.elim
  | succ _ => exact h

/-- `Sym.bytes`. -/
theorem denoteAt_bytes_elim {l : Grammar.Bytes} (h : denoteAt G n (.bytes l) bs a) :
    bs = l ∧ a = G.alg.ofBytes l := by
  cases n with
  | zero => exact h.elim
  | succ _ => exact h

/-- `Sym.seq`: the factors are one index down. -/
theorem denoteAt_seq_elim {gs : List (Grammar.Sym N α)} (h : denoteAt G n (.seq gs) bs a) :
    ∃ m, m < n ∧ appendAll G.alg (gs.map (denoteAt G m)) bs a := by
  cases n with
  | zero => exact h.elim
  | succ m => exact ⟨m, Nat.lt_succ_self m, h⟩

/-- `Sym.alt`: so are the branches. -/
theorem denoteAt_alt_elim {gs : List (Grammar.Sym N α)} (h : denoteAt G n (.alt gs) bs a) :
    ∃ m, m < n ∧ ∃ g ∈ gs, denoteAt G m g bs a := by
  cases n with
  | zero => exact h.elim
  | succ m =>
      obtain ⟨E, hE, hb⟩ := supList_apply.mp h
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
      exact ⟨m, Nat.lt_succ_self m, g, hg, hb⟩

/-- `Sym.star`: the body is one index down, under a Kleene closure. -/
theorem denoteAt_star_elim {g : Grammar.Sym N α} (h : denoteAt G n (.star g) bs a) :
    ∃ m, m < n ∧ ∃ k, powRel G.alg (denoteAt G m g) k bs a := by
  cases n with
  | zero => exact h.elim
  | succ m => exact ⟨m, Nat.lt_succ_self m, kleene_apply.mp h⟩

/-- `Sym.attr`. -/
theorem denoteAt_attr_elim {f : α → Option α} {g : Grammar.Sym N α}
    (h : denoteAt G n (.attr f g) bs a) :
    ∃ m a₀, m < n ∧ denoteAt G m g bs a₀ ∧ f a₀ = some a := by
  cases n with
  | zero => exact h.elim
  | succ m =>
      obtain ⟨a₀, h₀, hf⟩ := h
      exact ⟨m, a₀, Nat.lt_succ_self m, h₀, hf⟩

/-- `Sym.nt`: the productions are one index down. -/
theorem denoteAt_nt_elim {x : N} (h : denoteAt G n (.nt x) bs a) :
    ∃ m, m < n ∧ ∃ P ∈ G.prods x, denoteAt G m P bs a := by
  cases n with
  | zero => exact h.elim
  | succ m =>
      obtain ⟨E, hE, hb⟩ := supList_apply.mp h
      obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hE
      exact ⟨m, Nat.lt_succ_self m, P, hP, hb⟩

end Elim

/-- A literal's attribute changes no scope. -/
theorem actAlg_ofBytes_scope : ∀ (bs : Grammar.Bytes) {ρ ρ' : VarEnv} {l : List Value},
    actAlg.ofBytes bs ρ l ρ' → ρ' = ρ := by
  intro bs
  induction bs with
  | nil => intro _ _ _ h; exact h.2
  | cons b bs ih =>
      intro ρ ρ' l h
      obtain ⟨l₁, ρ₁, l₂, h₁, h₂, -⟩ := h
      obtain ⟨-, rfl⟩ := h₁
      exact ih h₂

/-! ## `SymDerives` implies `Derives`

The converse, by strong induction on the step index.  `Sem.transSym` is a
`mutual def`, so a few of its clauses are restated as rewrites first. -/

/-- `transSyms` is `List.map transSym`. -/
theorem transSyms_eq_map (env : Env) :
    ∀ gs : List IL.Sym, transSyms env gs = gs.map (transSym env)
  | [] => rfl
  | g :: gs => by rw [transSyms, List.map_cons, transSyms_eq_map env gs]

/-- `byteSym` on the fragment: an ASCII literal is a byte terminal. -/
theorem byteSym_ascii {n : Nat} (h : IsAscii n) : byteSym n = .byte (UInt8.ofNat n) := by
  rw [byteSym, ite_eq_left_of_eq_true _ _ (eq_true (show n < 256 by omega))]

/-- `rangeSym` on the fragment. -/
theorem rangeSym_ascii {lo hi : Nat} (hlo : IsAscii lo) (hhi : IsAscii hi) :
    rangeSym (.numG lo) (.numG hi) = .range (UInt8.ofNat lo) (UInt8.ofNat hi) := by
  rw [rangeSym, ite_eq_left_of_eq_true _ _ (eq_true (show lo < 256 ∧ hi < 256 by omega))]

/-- `ScopedAll` at a cons. -/
theorem ScopedAll.cons_inv {S : IL.Id → Prop} {g : IL.Sym} {gs : List IL.Sym}
    (h : ScopedAll S (g :: gs)) : Scoped S g ∧ ScopedAll S gs := by
  cases h with | cons h hs => exact ⟨h, hs⟩

/-- The claim at step index `n`.  The single-valued half also records that the
byte denotation contributes **exactly one** value at an `Agree` symbol, which
is what lets the scope-faithful half quote it through `Scoped.agree`. -/
def Bwd (env : Env) (S : IL.Id → Prop) (n : Nat) : Prop :=
  (∀ {ρ ρ' : VarEnv} {g : IL.Sym} {bs : Grammar.Bytes} {a : Act} {l : List Value},
      Agree S g → denoteAt (gramOf env) n (transSym env g) bs a → a ρ l ρ' →
      ∃ cs v, l = [v] ∧ utf8Codes cs = bs ∧ Derives env ρ g cs v ρ') ∧
  (∀ {ρ ρ' : VarEnv} {g : IL.Sym} {bs : Grammar.Bytes} {a : Act} {l : List Value},
      Scoped S g → denoteAt (gramOf env) n (transSym env g) bs a → a ρ l ρ' →
      ∃ cs v, utf8Codes cs = bs ∧ Derives env ρ g cs v ρ')

/-- A `SeqG`'s factors, left to right.  The induction is on the factor list;
every factor sits one step index down, which is where `IH` applies. -/
theorem bwdSeq {env : Env} {S : IL.Id → Prop} {m : Nat} (IH : Bwd env S m) :
    ∀ (gs : List IL.Sym), ScopedAll S gs →
      ∀ {bs : Grammar.Bytes} {a : Act} {ρ ρ' : VarEnv} {l : List Value},
        appendAll actAlg ((transSyms env gs).map (denoteAt (gramOf env) m)) bs a →
        a ρ l ρ' → ∃ cs, utf8Codes cs = bs ∧ DerivesSeq env ρ gs cs ρ' := by
  intro gs
  induction gs with
  | nil =>
      intro _ bs a ρ ρ' l hd ha
      simp only [transSyms, List.map_nil, appendAll] at hd
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨rfl, rfl⟩ := ha
      exact ⟨[], rfl, .nil⟩
  | cons g gs ih =>
      intro hall bs a ρ ρ' l hd ha
      obtain ⟨hg, hgs⟩ := hall.cons_inv
      simp only [transSyms, List.map_cons, appendAll] at hd
      obtain ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩ := hd
      obtain ⟨l₁, ρ₁, l₂, k₁, k₂, rfl⟩ := ha
      obtain ⟨cs₁, v₁, hcs₁, hd₁⟩ := IH.2 hg h₁ k₁
      obtain ⟨cs₂, hcs₂, hd₂⟩ := ih hgs h₂ k₂
      exact ⟨cs₁ ++ cs₂, by rw [utf8Codes_append, hcs₁, hcs₂], .cons hd₁ hd₂⟩

/-- An `IterG`'s rounds, read off the Kleene closure.  The round relation is
abstract, so that the index arithmetic stays in the caller: at index zero it
is `⊥` and the hypothesis is vacuous. -/
theorem bwdRounds {env : Env} {g : IL.Sym} {ds : List Dom}
    (E : EncRel Grammar.Bytes Act)
    (hE : ∀ {bs : Grammar.Bytes} {a : Act} {ρ ρ' : VarEnv} {l : List Value},
      E bs a → a ρ l ρ' → ∃ cs v vs ρ₁, utf8Codes cs = bs ∧ Derives env ρ g cs v ρ₁ ∧
        ds.mapM (fun d => ρ₁.findVal? (domVar d)) = some vs ∧
        l = [Value.tuple (v :: vs)] ∧ ρ' = ρ) :
    ∀ (k : Nat) {bs : Grammar.Bytes} {a : Act} {ρ ρ' : VarEnv} {l : List Value},
      powRel actAlg E k bs a → a ρ l ρ' →
      ∃ cs rows, utf8Codes cs = bs ∧ DerivesRounds env ρ ds g rows cs ∧
        l = rows.map (fun r => Value.tuple (r.1 :: r.2)) ∧ ρ' = ρ := by
  intro k
  induction k with
  | zero =>
      intro bs a ρ ρ' l hd ha
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨rfl, rfl⟩ := ha
      exact ⟨[], [], rfl, .nil, rfl, rfl⟩
  | succ k ih =>
      intro bs a ρ ρ' l hd ha
      obtain ⟨b₁, a₁, b₂, a₂, h₁, h₂, rfl, rfl⟩ := hd
      obtain ⟨l₁, ρ₁, l₂, k₁, k₂, rfl⟩ := ha
      obtain ⟨cs₁, v, vs, ρ₂, hcs₁, hder, hvs, rfl, rfl⟩ := hE h₁ k₁
      obtain ⟨cs₂, rows, hcs₂, hrounds, rfl, rfl⟩ := ih h₂ k₂
      exact ⟨cs₁ ++ cs₂, (v, vs) :: rows, by rw [utf8Codes_append, hcs₁, hcs₂],
        .cons hder hvs hrounds, rfl, rfl⟩

/-- **The backward half.**  Whatever the byte denotation derives from a
symbol of the fragment, the character denotation derives from some scalar
string whose UTF-8 encoding it is — with the same value and the same scope. -/
theorem bwd {env : Env} {S : IL.Id → Prop} (hE : GramsOk env S) : ∀ n, Bwd env S n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  have key : ∀ {ρ ρ' : VarEnv} {g : IL.Sym} {bs : Grammar.Bytes} {a : Act} {l : List Value},
      Agree S g → denoteAt (gramOf env) n (transSym env g) bs a → a ρ l ρ' →
      ∃ cs v, l = [v] ∧ utf8Codes cs = bs ∧ Derives env ρ g cs v ρ' := by
    intro ρ ρ' g bs a l hA hd ha
    cases hA with
    | @numG k h =>
        rw [transSym, byteSym_ascii h] at hd
        obtain ⟨rfl, rfl⟩ := denoteAt_byte_elim hd
        obtain ⟨rfl, rfl⟩ := ha
        exact ⟨[k], .num (.natN k), by rw [toNat_ofNat_ascii h],
          utf8Codes_singleton_ascii h, .numG⟩
    | @rangeG lo hi hlo hhi =>
        rw [transSym, rangeSym_ascii hlo hhi] at hd
        obtain ⟨b, h₁, h₂, rfl, rfl⟩ := denoteAt_range_elim hd
        obtain ⟨rfl, rfl⟩ := ha
        rw [UInt8.le_iff_toNat_le, toNat_ofNat_ascii hlo] at h₁
        rw [UInt8.le_iff_toNat_le, toNat_ofNat_ascii hhi] at h₂
        have hb : IsAscii b.toNat := by unfold IsAscii at hhi ⊢; omega
        exact ⟨[b.toNat], .num (.natN b.toNat), rfl,
          by rw [utf8Codes_singleton_ascii hb]; simp, .rangeG h₁ h₂⟩
    | @attrG e g₀ hg =>
        rw [transSym] at hd
        obtain ⟨m, a₀, hm, hd₀, hf⟩ := denoteAt_attr_elim hd
        rw [attrAct, Option.some.injEq] at hf
        subst hf
        obtain ⟨v₁, ρ₁, hv₁, rfl, hmatch⟩ := ha
        obtain ⟨cs, w, hlw, hcs, hder⟩ := (IH m hm).1 hg hd₀ hv₁
        obtain rfl : v₁ = w := by simpa using hlw
        exact ⟨cs, v₁, rfl, hcs, .attrG hder hmatch⟩
    | @iterG g₀ it ds hg =>
        rw [transSym] at hd
        obtain ⟨m, a₀, hm, hd₀, hf⟩ := denoteAt_attr_elim hd
        rw [iterAct, Option.some.injEq] at hf
        subst hf
        obtain ⟨rows, hk, hc, rfl, hb⟩ := ha
        obtain ⟨p, hp, k, hpow⟩ := denoteAt_star_elim hd₀
        obtain ⟨cs, rows', hcs, hrounds, hrows, -⟩ :=
          bwdRounds (g := g₀) (ds := ds)
            (denoteAt (gramOf env) p (.attr (roundAct ds) (transSym env g₀)))
            (by
              intro bs' a' σ σ' l' hz hz'
              obtain ⟨q, a₁, hq, hd₁, hf₁⟩ := denoteAt_attr_elim hz
              rw [roundAct, Option.some.injEq] at hf₁
              subst hf₁
              obtain ⟨rfl, v₁, ρ₁, vs, hv₁, hvs, rfl⟩ := hz'
              obtain ⟨cs₁, w, hlw, hcs₁, hder⟩ := (IH q (by omega)).1 hg hd₁ hv₁
              obtain rfl : v₁ = w := by simpa using hlw
              exact ⟨cs₁, v₁, vs, ρ₁, hcs₁, hder, hvs, rfl, rfl⟩)
            k hpow hk
        obtain rfl : rows = rows' := List.map_injective_iff.mpr tupleRow_injective hrows
        exact ⟨cs, _, rfl, hcs, .iterG hrounds hc hb⟩
    | @varG x hx =>
        obtain ⟨t, prods, hgram, hsc⟩ := hE x hx
        rw [transSym] at hd
        obtain ⟨m, hm, P, hP, hdP⟩ := denoteAt_nt_elim hd
        simp only [gramOf, gramOfEnvs, prodsOf, hgram] at hP
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hP
        obtain ⟨qs, g₀, e, prems⟩ := p
        rw [transProd] at hdP
        obtain ⟨m', a₀, hm', hd₀, hf⟩ := denoteAt_attr_elim hdP
        rw [prodAct, Option.some.injEq] at hf
        subst hf
        obtain ⟨rfl, ws, ρ₀, l₀, ρ₁, ρ₂, v, hw, hbp, ha₀, hpr, he, rfl⟩ := ha
        have hgs : Scoped S g₀ := hsc qs g₀ e prems hp
        rw [gramArgSubst_nil_nil, hgs.substSym_nil] at hd₀
        obtain ⟨cs, v₀, hcs, hder⟩ := (IH m' (by omega)).2 hgs hd₀ ha₀
        refine ⟨cs, v, rfl, hcs, Derives.varG (v₀ := v₀) hgram hp hw hbp ?_ hpr he⟩
        rw [gramArgSubst_nil_nil, hgs.substSym_nil]
        exact hder
  refine ⟨key, ?_⟩
  intro ρ ρ' g bs a l hS hd ha
  cases hS with
  | epsG =>
      rw [transSym] at hd
      obtain ⟨rfl, rfl⟩ := denoteAt_eps_elim hd
      obtain ⟨rfl, rfl⟩ := ha
      exact ⟨[], .tuple [], rfl, .epsG⟩
  | @textG t =>
      rw [transSym] at hd
      obtain ⟨rfl, rfl⟩ := denoteAt_bytes_elim hd
      obtain rfl := actAlg_ofBytes_scope _ ha
      exact ⟨codes t, .text t, utf8Codes_codes t, .textG⟩
  | @seqG gs hall =>
      rw [transSym] at hd
      obtain ⟨m, hm, hseq⟩ := denoteAt_seq_elim hd
      obtain ⟨cs, hcs, hds⟩ := bwdSeq (IH m hm) gs hall hseq ha
      exact ⟨cs, .tuple [], hcs, .seqG hds⟩
  | @altG gs hall =>
      rw [transSym] at hd
      obtain ⟨m, hm, X, hX, hdX⟩ := denoteAt_alt_elim hd
      rw [transSyms_eq_map] at hX
      obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hX
      obtain ⟨cs, v, hcs, hder⟩ := (IH m hm).2 (hall.mem hg₀) hdX ha
      exact ⟨cs, .tuple [], hcs, .altG hg₀ hder⟩
  | agree hA =>
      obtain ⟨cs, v, -, hcs, hder⟩ := key hA hd ha
      exact ⟨cs, v, hcs, hder⟩

/-! ## The agreement

Both halves, as one equation between `EncRel`s.  It is stated for `Agree`
symbols only, and must be: a `Scoped`-but-not-`Agree` symbol is one where
`Sem.Act` contributes a value *list* of length other than one, and
`gramRelSup` — which asks for `a ρ [v] ρ'` — is then empty where `charRel` is
not.  `not_gramRelSup_tnewline_crlf` is that phenomenon at `Tnewline`; here it
is the reason the fragment is cut where it is. -/

/-- **The two denotations agree on the fragment.**  `EncRel.push utf8Codes` of
the character denotation of `Equiv/Text.lean` is exactly `Sem.gramRelSup`. -/
theorem textByteRel_eq_gramRelSup {env : Env} {S : IL.Id → Prop} (hE : GramsOk env S)
    {g : IL.Sym} (hA : Agree S g) (ρ : VarEnv) :
    textByteRel env ρ g = gramRelSup env ρ g := by
  ext bs v
  constructor
  · rintro ⟨cs, rfl, ρ', hder⟩
    exact gramRelSup_iff.mpr ⟨ρ', (fwd hE hder).1 hA⟩
  · rintro ⟨a, ρ', ha, hv⟩
    obtain ⟨n, hn⟩ := denote_apply.mp ha
    obtain ⟨cs, w, hl, hcs, hder⟩ := (bwd hE n).1 hA hn hv
    obtain rfl : v = w := by simpa using hl
    exact ⟨cs, hcs, ρ', hder⟩

/-- The same, as the two-sided statement about derivations. -/
theorem gramRelSup_iff_charRel {env : Env} {S : IL.Id → Prop} (hE : GramsOk env S)
    {g : IL.Sym} (hA : Agree S g) {ρ : VarEnv} {bs : Grammar.Bytes} {v : Value} :
    gramRelSup env ρ g bs v ↔ ∃ cs, utf8Codes cs = bs ∧ charRel env ρ g cs v := by
  rw [← textByteRel_eq_gramRelSup hE hA ρ]
  exact textByteRel_iff

/-! ## At a grammar of the stream: the pinned `Tidchar`

`Tidchar` is the one §6.0 lexical class whose terminals are all below `0x80`:
three ranges and twenty-three single characters, the largest `U+7E`
(`6.1-text.values.spectec:123-128`).  So it is in the fragment, and the
agreement is a statement about the pinned script rather than a hypothetical
one.  `Tchar` is *not* — its ranges run to `U+10FFFF` — and
`gramRelSup_tchar_eq_bot` is the consequence. -/

/-- A terminal all of whose scalars are ASCII. -/
def Term.Ascii : Term → Prop
  | .lit n => IsAscii n
  | .range lo hi => IsAscii lo ∧ IsAscii hi

instance (τ : Term) : Decidable τ.Ascii := by
  cases τ <;> unfold Term.Ascii <;> infer_instance

/-- An ASCII terminal is a single-valued symbol of the fragment. -/
theorem agree_term_sym {S : IL.Id → Prop} : ∀ {τ : Term}, τ.Ascii → Agree S τ.sym
  | .lit _, h => .numG h
  | .range _ _, h => .rangeG h.1 h.2

/-- All twenty-six `Tidchar` terminals are ASCII. -/
theorem tidcharTerms_ascii : ∀ τ ∈ tidcharTerms, τ.Ascii := by decide

/-- Every identifier character is ASCII. -/
theorem isAscii_of_isIdChar {n : Nat} (h : IsIdChar n) : IsAscii n := by
  simp only [IsIdChar, tidcharTerms, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Term.Mem] at h
  simp only [IsAscii]
  omega

/-- The bodies of a `charProdsOf` grammar are `Scoped` when its terminals are
ASCII: each is an `AttrG` over the terminal, binding the implicit result. -/
theorem scoped_charProdsOf {S : IL.Id → Prop} {τs : List Term} (hτ : ∀ τ ∈ τs, τ.Ascii)
    {qs : List Param} {g : IL.Sym} {e : Exp} {prems : List Prem}
    (hp : IL.Prod.prodD qs g e prems ∈ charProdsOf τs) : Scoped S g := by
  simp only [charProdsOf, List.mem_map] at hp
  obtain ⟨τ, hmem, hq⟩ := hp
  rw [charProd, IL.Prod.prodD.injEq] at hq
  obtain ⟨-, rfl, -, -⟩ := hq
  exact .agree (.attrG (agree_term_sym (hτ τ hmem)))

/-- `Tidchar` is closed and parameterless at the pinned script. -/
theorem gramsOk_tidchar_pinned : GramsOk envPinned (· = "Tidchar") := by
  rintro x rfl
  exact ⟨.varT "char" [], tidcharProds, rfl,
    fun _ _ _ _ hp => scoped_charProdsOf tidcharTerms_ascii hp⟩

/-- …and at the corrected one: `#677` does not touch `Tidchar`. -/
theorem gramsOk_tidchar_corrected : GramsOk envCorrected (· = "Tidchar") := by
  rintro x rfl
  exact ⟨.varT "char" [], tidcharProds, rfl,
    fun _ _ _ _ hp => scoped_charProdsOf tidcharTerms_ascii hp⟩

/-- **The pinned `Tidchar`, both ways.**  The byte denotation of
`Sem/Grammar.lean` and the character denotation of `Equiv/Text.lean` are the
same relation, carried across UTF-8. -/
theorem textByteRel_tidchar_eq_gramRelSup_pinned (ρ : VarEnv) :
    textByteRel envPinned ρ (.varG "Tidchar" [])
      = gramRelSup envPinned ρ (.varG "Tidchar" []) :=
  textByteRel_eq_gramRelSup gramsOk_tidchar_pinned (.varG rfl) ρ

/-- The same at the corrected script. -/
theorem textByteRel_tidchar_eq_gramRelSup_corrected (ρ : VarEnv) :
    textByteRel envCorrected ρ (.varG "Tidchar" [])
      = gramRelSup envCorrected ρ (.varG "Tidchar" []) :=
  textByteRel_eq_gramRelSup gramsOk_tidchar_corrected (.varG rfl) ρ

/-- Composed with `tidchar_wasm30_iff`, the byte denotation of the pinned
`Tidchar` in closed form: the twenty-six single-byte spellings, with the value
`%(n)`.  Unlike `Tchar`, which denotes `⊥` over bytes, this one is a *real*
byte relation, and it is the one the `.spectec` source describes. -/
theorem gramRelSup_tidchar_pinned_iff {ρ : VarEnv} {bs : Grammar.Bytes} {v : Value} :
    gramRelSup envPinned ρ (.varG "Tidchar" []) bs v ↔
      ∃ n, IsIdChar n ∧ bs = [UInt8.ofNat n] ∧ v = numCase n := by
  rw [← textByteRel_tidchar_eq_gramRelSup_pinned, textByteRel_iff]
  constructor
  · rintro ⟨cs, rfl, ρ', hder⟩
    obtain ⟨-, n, hn, rfl, rfl⟩ := tidchar_wasm30_iff.mp hder
    exact ⟨n, hn, utf8Codes_singleton_ascii (isAscii_of_isIdChar hn), rfl⟩
  · rintro ⟨n, hn, rfl, rfl⟩
    exact ⟨[n], utf8Codes_singleton_ascii (isAscii_of_isIdChar hn), ρ,
      tidchar_wasm30_iff.mpr ⟨rfl, n, hn, rfl, rfl⟩⟩

end Silmaril.SpecTec.Equiv.Text
