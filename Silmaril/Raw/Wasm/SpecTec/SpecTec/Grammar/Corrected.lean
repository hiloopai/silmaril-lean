module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Grammar.Decoder
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Grammar
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Errata.Binary51
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The corrected wasm-3.0 binary grammar in the attribute-grammar framework

`Silmaril/SpecTec/Grammar/Basic.lean` is a framework of byte attribute
grammars, `Silmaril/SpecTec/Grammar/Decoder.lean` gives it a verified
recursive-descent decoder on a decidable prefix-deterministic subclass, and
`Silmaril/SpecTec/Sem/Grammar.lean` embeds SpecTec's `GramD` into it.  This
file puts the three together on the real thing: the binary format of
WebAssembly 3.0, as the *corrected* specification
`Errata.Binary51.wasm30binary51` spells it.

Everything here is relative to the pin
`608711107b7f1edb13efd57b7d79b49477462d36`; the `.spectec` line numbers are in
`specification/wasm-3.0/`.

## What is extracted

`binGram` is `Sem.gramOf (Sem.envOfScript Errata.Binary51.wasm30binary51)` —
*all* of the corrected script's `GramD`s, not a subset, since `Sem.prodsOf`
reads the production table out of the environment on demand.  What has to be
enumerated is the set of *nonterminals*, because `Sem.NT` is an identifier
paired with an unevaluated argument list and a parameterised grammar
contributes one nonterminal per syntactically distinct argument list.
`binNTs` is the worklist closure from `Bmodule`, and `binNTs_length` says it
has **125** members, using 87 of the corrected script's 232 grammar
declarations; 44 of the 125 carry a non-empty argument list.

All of the file's numerical claims are kernel computations over that value:
`binNTs`, the counts, and every `altSeparated`/`firstOk` check below reduce
`Sem.prodsOf` over `Errata.Binary51.wasm30binary51` itself.  They were
cross-checked against an independent implementation of the same analysis
written directly over `IL.Sym` and run at elaboration time on the `--ast`
stream with the four `spectec_erratum` patches re-applied textually; the two
agree on 125, 109 and 26.

## The class-membership verdict: **no**

`Decoder.Det` fails, and `not_det_binGram` proves it.  The survey is

| check | fails at | of |
| --- | --- | --- |
| `Basic.altSeparated` (disjoint leading byte ranges) | 109 | 125 |
| `Decoder.detSymList` (no unbounded iteration) | 26 | 125 |

and the failures fall into three structurally different classes.

**(i) `leadRange?` gives up at a nonterminal.**  `Bvaltype`'s three
productions are `nt:Bnumtype`, `vt:Bvectype` and `rt:Breftype`
(`5.2-binary.types.spectec:39-42`), so `leadRange?` answers `none` for all
three (`leadRange_Bvaltype`).  This is a limitation of the decidable
approximation and *not* an ambiguity: the three alternatives really do have
disjoint first bytes, which is exactly what the FIRST-set analysis below
proves.  This class is the large one, and it is what a FIRST computation
fixes.

**(ii) Genuinely overlapping leading bytes.**  Twelve nonterminals have a
known FIRST set for every production and the sets still overlap:
`BuN`, `BsN` (three nonterminals each: the recursive call `BuN($(N-7))` is a
distinct nonterminal from `BuN(32)` and `BuN(64)`), `Bheaptype`,
`Bblocktype`, `Belem`, `Bdata`, `Bmemarg` and `Binstr`.  All but the last are
disambiguated by a **premise**, not by the grammar: `BuN`'s two productions
are both `n:Bbyte …`, separated by `-- if $(n < 2^7)` versus
`-- if $(n >= 2^7)` (`5.1-binary.values.spectec:10-11`), and `Bheaptype`'s
two by `-- if x33 >= 0` (`5.2-binary.types.spectec:31-32`); `Bmemarg`'s two by
`$(n < 2^6)` versus `$(2^6 <= n < 2^7)` (`5.3-binary.instructions.spectec:
101-102`); and `Belem`'s and `Bdata`'s by a *literal pattern* on the decoded
`Bu32` — `0:Bu32`, `1:Bu32`, `2:Bu32` (`5.4-binary.modules.spectec:143-145`),
which is a value test and not a byte test, since a `u32` has many
spellings.  No FIRST-set
computation can see a side condition on a decoded *value*, so these need a
premise-aware analysis — and note that the framework's decoder cannot act on
them either, because `Sem.prodAct` is total: the partiality of a SpecTec
premise lives *inside* the `Sem.Act` attribute, which is a relation and may
simply be empty, so `run` never consults it.  `Binstr` is the one case of a
different kind: every one of its 498 productions has a known leading byte
(`leadRange_Binstr_all_known`) and they still collide, because the `0xFB`,
`0xFC` and `0xFD` prefixes are shared by whole opcode families that continue
into a following `Bu32`.  That needs two-byte lookahead, not FIRST sets.

**(iii) Nullable or iteration-headed productions.**  Thirty-three of the 125
have no FIRST set at all.  `Bsection_(N, BX)` has the production `| eps => eps`
(`5.4-binary.modules.spectec:9-11`), so sections are optional and every
`B…sec` inherits that; `Bexpr` and `BfN(N)` begin with an iteration.  These
need FOLLOW sets, which `Decoder.lean`'s own "Not here" section already
identifies as the missing ingredient for greedy iteration.  Separately,
*every* `IL.Sym.iterG` becomes a framework `Sym.star` — `Sem.transSym` cannot
use `Sym.count` even for a `ListN` iterator, because `Blist`'s repetition
count is bound by the `Bu32` in front of it and so is not known at translation
time — and `Decoder.detSym` excludes `star` outright.  That is the whole of
the 26 `detSymList` failures.

## The FIRST-set fixpoint

Since class (i) is the largest, the main construction here is the FIRST-set
strengthening the brief asks for.  It is *generic* — stated for an arbitrary
`Gram N α`, so it belongs to the framework and not to WebAssembly — and it is
phrased as a **certificate** rather than as a least fixpoint:

* `ByteSet` is a union of inclusive intervals, with decidable `subset` and
  `disjoint` (`leadRange?`'s single interval is not enough: `Bvaltype`'s
  third alternative has FIRST `{0x63, 0x64} ∪ [0x69, 0x74]`);
* `firstOf F g` is `leadRange?` with the nonterminal case answered from `F`;
* `firstOk G F x s` is the decidable obligation at one nonterminal, and
  `FirstSound G F` is that obligation wherever `F` commits;
* `firstOf_sound` is the theorem: under `FirstSound`, every byte string `g`
  derives is non-empty and begins with a byte of `firstOf F g`.

Computing a fixpoint and *checking* it is strictly more flexible than
constructing a least fixpoint: an assignment may cover any part of a grammar,
`none` degrades gracefully to `leadRange?`'s behaviour, and the check is one
`rfl`.  `firstOf_of_leadRange?` records that nothing is lost — a `leadRange?`
answer is a one-interval FIRST set.  On top of it, `altSepFirst`,
`altSepFirst_pairwise`, `altSepFirst_nonNullable`,
`unambiguous_denote_altFirst` and `unambiguous_denote_ntFirst` are the
FIRST-set forms of `Basic.altSeparated` and its consequences.

`binFirst` is a certificate for the §5.1 values and §5.2 types nonterminals —
23 entries, all unparameterised, closed under "what a production *begins*
with" — and `firstSound_binFirst` checks it against the corrected grammar.
It raises the number of nonterminals with pairwise separated productions from
**16** (`countP_not_altSeparated`) to **29** (`countP_altSepFirst`).  The
headline consequences are `separated_Bvaltype` — *the three cases of a value
type are distinguished by their first byte*, which `Basic.altSeparated` cannot
see at all — and the FIRST sets of `Bvaltype`, `Breftype` and `Brectype` as
statements about the corrected specification, at the framework level
(`first_Bvaltype`) and at the level of `Sem.gramRelSup`, the specification's
own grammar relation (`first_Bvaltype_gramRel`).

A certificate for all 125 would be a table of 125 entries with explicit
argument lists for the 44 parameterised nonterminals, which is not worth
writing by hand; the same analysis run with a full least-fixpoint assignment
separates 80 of the 125 and leaves 45, the 33 of class (iii) plus the 12 of
class (ii).  That measurement is *not* certified in this file — only the
23-entry certificate is.

## Decoding a real module prefix

`binGramDet` is `binGram` restricted to the 16 nonterminals that do pass both
`Decoder.Det` conditions.  Restricting rather than extending is what makes
`Det` reachable without any closure computation, since `altSeparated []` and
`detSymList []` are both `true`; `det_binGramDet` is the proof, and
`denote_binGramDet_le` says every derivation it admits is a derivation of the
corrected grammar.  `Decoder.lean`'s completeness theory therefore applies to
it verbatim: `encodes_iff_denote_headerSym` is the decoder as a decision
procedure.

`decode_wasmHeader_value` is the worked example.  The eight bytes
`00 61 73 6D 01 00 00 00` — the magic number and the version word, the first
two factors of `Bmodule` (`5.4-binary.modules.spectec:175-176`) — are decoded
by `Decoder.decode` with 32 units of fuel, consuming all of them, and the
attribute it returns assigns them the value `((), ())`, which is what the two
productions' value expressions compute.  All of it is kernel-checked.
`bmagic_derives` and `bversion_derives` state the same two values through
`Sem.gramRelSup` instead, built from `Sem/Grammar.lean`'s compositionality
lemmas.

## What is *not* proved here

* **No decoder for the FIRST class.**  `Decoder.run_mono` and
  `Decoder.run_complete` take `Det G`, which is phrased with
  `Basic.altSeparated`; strengthening them to `altSepFirst` means re-proving
  them, and `Decoder.lean` is not a file this one may edit.  So the FIRST-set
  work here buys unambiguity and separation theorems, not a verified decoder,
  for `Bvaltype` and its 28 companions.  It would buy one, and the work is
  bounded: `Det` enters those proofs in two ways, through
  `run_alt_cons_head_none` — whose content is pairwise separation, which
  `altSepFirst_pairwise` supplies verbatim — and through `Decoder.detJob` of
  the `alt` job a nonterminal unfolds to, which would have to carry
  `altSepFirst` in place of `altSeparated`.
* **No premise-aware analysis**, so class (ii) is untouched, and no FOLLOW
  sets, so class (iii) is untouched.  In particular nothing here decodes a
  `Bu32`, a section, or an instruction.  `Sem/Grammar.lean`'s `bun_iff_un`
  already relates `BuN` to `Wasm.Binary.UN` by hand, which is the shape a
  premise-aware treatment would have to generalise.
* **The 80-of-125 figure is a measurement, not a theorem** (see above).
* **`Unambiguous` is not established for any nonterminal.**
  `unambiguous_denote_ntFirst` needs every alternative to be unambiguous, and
  an alternative is a `Sym.attr` over `Sem.prodAct`, whose action is not
  injective; `Basic.Unambiguous.mapPartial` therefore does not apply, and
  functionality of a SpecTec grammar's `Sem.Act` denotation is open.  What is
  proved is the separation and non-nullability half, which is the LL(1)
  statement.
* **The classification of the 45 remaining failures into classes (ii) and
  (iii) is by inspection**, not by a Lean theorem: the counts 109 and 26 and
  the two named witnesses `Bvaltype` and `Binstr` are machine-checked, the
  attribution of each remaining nonterminal to a cause is not.
-/

@[expose] public section

namespace Silmaril.SpecTec.Grammar

open Silmaril

/-! ## Byte sets -/

/-- A set of bytes, as a list of inclusive intervals.  Intervals rather than a
bitmask because every set the analysis below produces is a union of a handful
of them, and because `Sym.range` contributes one directly. -/
abbrev ByteSet := List (UInt8 × UInt8)

namespace ByteSet

/-- The full byte set. -/
def univ : ByteSet := [(0x00, 0xFF)]

/-- Membership, as a `Bool`. -/
def has (s : ByteSet) (b : UInt8) : Bool := s.any fun p => p.1 ≤ b && b ≤ p.2

/-- Every byte, as an explicit list; the domain the two decidable checks below
quantify over. -/
def all : List UInt8 := (List.range 256).map UInt8.ofNat

/-- `ByteSet.all` really is every byte. -/
theorem mem_all (b : UInt8) : b ∈ ByteSet.all :=
  List.mem_map.mpr ⟨b.toNat, List.mem_range.mpr b.toNat_lt_size, UInt8.ofNat_toNat⟩

/-- `s ⊆ t`, decided by running over all 256 bytes. -/
def subset (s t : ByteSet) : Bool := ByteSet.all.all fun b => !s.has b || t.has b

/-- `s ∩ t = ∅`, decided by running over all 256 bytes. -/
def disjoint (s t : ByteSet) : Bool := ByteSet.all.all fun b => !(s.has b && t.has b)

/-- `subset` is sound. -/
theorem has_of_subset {s t : ByteSet} {b : UInt8} (h : subset s t = true)
    (hb : s.has b = true) : t.has b = true := by
  have := (List.all_eq_true.mp h) b (mem_all b)
  simpa [hb] using this

/-- `disjoint` is sound. -/
theorem not_has_of_disjoint {s t : ByteSet} {b : UInt8} (h : disjoint s t = true)
    (hs : s.has b = true) : t.has b = false := by
  have := (List.all_eq_true.mp h) b (mem_all b)
  simpa [hs] using this

/-- `univ` contains every byte. -/
@[simp] theorem has_univ (b : UInt8) : univ.has b = true := by
  simp only [univ, has, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨UInt8.le_iff_toNat_le.mpr ?_, UInt8.le_iff_toNat_le.mpr ?_⟩
  · simp
  · simpa using Nat.lt_succ_iff.mp b.toNat_lt_size

/-- The singleton `{b}`. -/
theorem has_singleton (b : UInt8) : ByteSet.has [(b, b)] b = true := by
  simp [has]

/-- An interval contains its members. -/
theorem has_interval {lo hi b : UInt8} (h₁ : lo ≤ b) (h₂ : b ≤ hi) :
    ByteSet.has [(lo, hi)] b = true := by
  simp [has, h₁, h₂]

end ByteSet

/-! ## The FIRST analysis -/

section First

variable {N α : Type}

/-- The leading bytes of a symbol, relative to an assignment `F` of a byte set
to each nonterminal.  `none` means "unknown", and is also what a possibly
nullable symbol gets: a `some` answer is a certificate that *every* byte string
the symbol derives is non-empty and starts with a byte in the set.

This is `Basic.leadRange?` with two changes, and only two: a nonterminal is
answered from `F` rather than with `none`, and the answer is a union of
intervals rather than a single interval.  Both are needed — see the module
docstring.  `alt` is still answered `none`; the reachable binary grammar of
`Errata.Binary51.wasm30binary51` contains no `Sym.alt` node at all (every
alternation in it is a production list, which `firstOk` handles), so the union
that would be sound there buys nothing. -/
def firstOf (F : N → Option ByteSet) : Sym N α → Option ByteSet
  | .eps => none
  | .byte b => some [(b, b)]
  | .range lo hi => some [(lo, hi)]
  | .bytes [] => none
  | .bytes (b :: _) => some [(b, b)]
  | .nt x => F x
  | .seq [] => none
  | .seq (g :: _) => firstOf F g
  | .alt _ => none
  | .star _ => none
  | .plus g => firstOf F g
  | .opt _ => none
  | .count _ 0 => none
  | .count g (_ + 1) => firstOf F g
  | .attr _ g => firstOf F g

/-- The certificate condition at one nonterminal: every production of `x` has a
known leading-byte set, and it is contained in the set `F` assigns to `x`.
Decidable, and that is the point: a FIRST assignment is *computed* however one
likes and then *checked*, rather than constructed as a least fixpoint. -/
def firstOk (G : Gram N α) (F : N → Option ByteSet) (x : N) (s : ByteSet) : Bool :=
  (G.prods x).all fun g =>
    match firstOf F g with
    | some t => ByteSet.subset t s
    | none => false

/-- A FIRST assignment is *sound for `G`* when `firstOk` holds wherever it
commits to a set.  Nonterminals it answers `none` for carry no obligation, so
an assignment may cover any part of a grammar, and `firstOf` degrades to
`Basic.leadRange?`'s `none` outside it. -/
def FirstSound (G : Gram N α) (F : N → Option ByteSet) : Prop :=
  ∀ x s, F x = some s → firstOk G F x s = true

/-- **Soundness of the FIRST analysis, at a fixed derivation depth.**  The
induction is on the depth alone: every clause of `step` puts its sub-symbols
one level down, so the nonterminal case can appeal to the induction hypothesis
at the productions, which is exactly what makes a FIRST *fixpoint* work where
`Basic.leadRange?`'s structural recursion has to give up. -/
theorem firstOf_soundAt (G : Gram N α) {F : N → Option ByteSet} (hF : FirstSound G F) :
    ∀ (n : Nat) (g : Sym N α) (s : ByteSet), firstOf F g = some s →
      ∀ (bs : Bytes) (a : α), denoteAt G n g bs a →
        ∃ b bs', bs = b :: bs' ∧ s.has b = true := by
  intro n
  induction n with
  | zero => intro g s _ bs a h; exact absurd h (by simp)
  | succ n ih =>
    intro g s hs bs a hd
    rw [denoteAt_succ] at hd
    match g with
    | .eps => simp [firstOf] at hs
    | .byte b =>
      obtain ⟨rfl, -⟩ := hd
      obtain rfl : s = [(b, b)] := by simpa [firstOf] using hs.symm
      exact ⟨b, [], rfl, ByteSet.has_singleton b⟩
    | .range lo hi =>
      obtain ⟨c, h₁, h₂, rfl, -⟩ := hd
      obtain rfl : s = [(lo, hi)] := by simpa [firstOf] using hs.symm
      exact ⟨c, [], rfl, ByteSet.has_interval h₁ h₂⟩
    | .bytes [] => simp [firstOf] at hs
    | .bytes (b :: l) =>
      obtain ⟨rfl, -⟩ := hd
      obtain rfl : s = [(b, b)] := by simpa [firstOf] using hs.symm
      exact ⟨b, l, rfl, ByteSet.has_singleton b⟩
    | .nt x =>
      obtain ⟨E, hE, hv⟩ := supList_apply.mp hd
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hE
      have hok := (List.all_eq_true.mp (hF x s hs)) g' hg'
      revert hok
      match hfg : firstOf F g' with
      | none => intro hok; exact absurd hok (by simp)
      | some t =>
        intro hsub
        obtain ⟨b, bs', rfl, hb⟩ := ih g' t hfg bs a hv
        exact ⟨b, bs', rfl, ByteSet.has_of_subset (by simpa using hsub) hb⟩
    | .seq [] => simp [firstOf] at hs
    | .seq (g' :: gs) =>
      obtain ⟨b₁, a₁, b₂, a₂, h₁, -, rfl, -⟩ := hd
      obtain ⟨b, bs', rfl, hb⟩ := ih g' s (by simpa [firstOf] using hs) b₁ a₁ h₁
      exact ⟨b, bs' ++ b₂, rfl, hb⟩
    | .alt gs => simp [firstOf] at hs
    | .star g' => simp [firstOf] at hs
    | .plus g' =>
      obtain ⟨b₁, a₁, b₂, a₂, h₁, -, rfl, -⟩ := hd
      obtain ⟨b, bs', rfl, hb⟩ := ih g' s (by simpa [firstOf] using hs) b₁ a₁ h₁
      exact ⟨b, bs' ++ b₂, rfl, hb⟩
    | .opt g' => simp [firstOf] at hs
    | .count g' 0 => simp [firstOf] at hs
    | .count g' (k + 1) =>
      obtain ⟨b₁, a₁, b₂, a₂, h₁, -, rfl, -⟩ := hd
      obtain ⟨b, bs', rfl, hb⟩ := ih g' s (by simpa [firstOf] using hs) b₁ a₁ h₁
      exact ⟨b, bs' ++ b₂, rfl, hb⟩
    | .attr f g' =>
      obtain ⟨a', hd', -⟩ := hd
      exact ih g' s (by simpa [firstOf] using hs) bs a' hd'

/-- **Soundness of the FIRST analysis.**  Every byte string a symbol derives is
non-empty and begins with a byte in its FIRST set. -/
theorem firstOf_sound (G : Gram N α) {F : N → Option ByteSet} (hF : FirstSound G F)
    {g : Sym N α} {s : ByteSet} (h : firstOf F g = some s) {bs : Bytes} {a : α}
    (hd : denote G g bs a) : ∃ b bs', bs = b :: bs' ∧ s.has b = true := by
  obtain ⟨n, hn⟩ := denote_apply.mp hd
  exact firstOf_soundAt G hF n g s h bs a hn

/-- A known FIRST set certifies non-nullability, exactly as
`Basic.nonNullable_of_leadRange` does for `leadRange?`. -/
theorem nonNullable_of_first (G : Gram N α) {F : N → Option ByteSet} (hF : FirstSound G F)
    {g : Sym N α} {s : ByteSet} (h : firstOf F g = some s) : NonNullable (denote G g) := by
  intro a ha
  obtain ⟨b, bs', hbs, -⟩ := firstOf_sound G hF h ha
  exact absurd hbs (by simp)

/-- Disjoint FIRST sets imply distinct first bytes. -/
theorem separated_of_first (G : Gram N α) {F : N → Option ByteSet} (hF : FirstSound G F)
    {g g' : Sym N α} {s t : ByteSet} (h : firstOf F g = some s) (h' : firstOf F g' = some t)
    (hd : ByteSet.disjoint s t = true) : Separated (denote G g) (denote G g') := by
  intro bs bs' a a' hb hb'
  obtain ⟨b, c, rfl, hbs⟩ := firstOf_sound G hF h hb
  obtain ⟨b', c', rfl, hbs'⟩ := firstOf_sound G hF h' hb'
  simp only [List.head?_cons, ne_eq, Option.some.injEq]
  rintro rfl
  rw [ByteSet.not_has_of_disjoint hd hbs] at hbs'
  exact absurd hbs' (by simp)

/-- Every alternative has a known FIRST set and the sets are pairwise disjoint:
the FIRST-set strengthening of `Basic.altSeparated`, and the decidable
sufficient condition for an alternation to be unambiguous. -/
def altSepFirst (F : N → Option ByteSet) : List (Sym N α) → Bool
  | [] => true
  | g :: gs =>
    (match firstOf F g with
      | some s => gs.all (fun g' => match firstOf F g' with
          | some t => ByteSet.disjoint s t
          | none => false)
      | none => false) && altSepFirst F gs

/-- `altSepFirst` certifies that every branch has a known FIRST set. -/
theorem altSepFirst_first {F : N → Option ByteSet} {gs : List (Sym N α)}
    (h : altSepFirst F gs = true) {g : Sym N α} (hg : g ∈ gs) :
    ∃ s, firstOf F g = some s := by
  induction gs with
  | nil => exact absurd hg (by simp)
  | cons g' gs ih =>
    simp only [altSepFirst, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hg with rfl | hg
    · revert h; split
      · rintro ⟨-, -⟩; exact ⟨_, by assumption⟩
      · rintro ⟨h, -⟩; exact absurd h (by simp)
    · exact ih h.2 hg

/-- `altSepFirst` certifies that the branches are pairwise separated. -/
theorem altSepFirst_pairwise (G : Gram N α) {F : N → Option ByteSet} (hF : FirstSound G F)
    {gs : List (Sym N α)} (h : altSepFirst F gs = true) :
    gs.Pairwise (fun g g' => Separated (denote G g) (denote G g')) := by
  induction gs with
  | nil => exact List.Pairwise.nil
  | cons g gs ih =>
    simp only [altSepFirst, Bool.and_eq_true] at h
    refine List.Pairwise.cons ?_ (ih h.2)
    intro g' hg'
    revert h
    split
    · rintro ⟨hall, -⟩
      rename_i s hsg
      have hmem := (List.all_eq_true.mp hall) g' hg'
      revert hmem
      split
      · rename_i t hsg'
        intro hdisj
        exact separated_of_first G hF hsg hsg' hdisj
      · intro hfalse; exact absurd hfalse (by simp)
    · rintro ⟨hfalse, -⟩; exact absurd hfalse (by simp)

/-- Every alternative is non-nullable, under `altSepFirst`. -/
theorem altSepFirst_nonNullable (G : Gram N α) {F : N → Option ByteSet} (hF : FirstSound G F)
    {gs : List (Sym N α)} (h : altSepFirst F gs = true) {g : Sym N α} (hg : g ∈ gs) :
    NonNullable (denote G g) := by
  obtain ⟨s, hs⟩ := altSepFirst_first h hg
  exact nonNullable_of_first G hF hs

/-- The FIRST-set form of `Basic.unambiguous_denote_alt`: distinct first bytes
across the alternatives, each alternative unambiguous, makes the alternation
unambiguous. -/
theorem unambiguous_denote_altFirst (G : Gram N α) {F : N → Option ByteSet}
    (hF : FirstSound G F) {gs : List (Sym N α)} (hsep : altSepFirst F gs = true)
    (hu : ∀ g ∈ gs, Unambiguous (denote G g)) : Unambiguous (denote G (.alt gs)) := by
  rw [denote_alt]
  refine Unambiguous.supList ?_ ?_ ?_
  · intro E hE
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
    exact hu g hg
  · intro E hE
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
    exact altSepFirst_nonNullable G hF hsep hg
  · exact List.Pairwise.map _ (fun _ _ h => h) (altSepFirst_pairwise G hF hsep)

/-- The same for a nonterminal, whose productions are its alternatives. -/
theorem unambiguous_denote_ntFirst (G : Gram N α) {F : N → Option ByteSet}
    (hF : FirstSound G F) {x : N} (hsep : altSepFirst F (G.prods x) = true)
    (hu : ∀ g ∈ G.prods x, Unambiguous (denote G g)) :
    Unambiguous (denote G (.nt x)) := by
  have h := unambiguous_denote_altFirst G hF (gs := G.prods x) hsep hu
  rwa [denote_alt, ← denote_nt] at h

/-- `altSepFirst` subsumes `Basic.altSeparated` whenever the latter applies: a
`leadRange?` answer is a one-interval FIRST set.  This is the formal statement
that the strengthening loses nothing. -/
theorem firstOf_of_leadRange? {F : N → Option ByteSet} {g : Sym N α} {lo hi : UInt8}
    (h : leadRange? g = some (lo, hi)) : firstOf F g = some [(lo, hi)] := by
  induction g using leadRange?.induct <;>
    simp_all [leadRange?, firstOf] <;> exact h.1.symm.trans h.2

end First

/-! ## The corrected wasm-3.0 binary grammar -/

section Corrected

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- The environment of the corrected wasm-3.0 specification. -/
noncomputable def binEnv : Sem.Env := Sem.envOfScript IL.Binary51.wasm30binary51

/-- The corrected wasm-3.0 grammar. -/
noncomputable def binGram : Gram Sem.NT Sem.Act := Sem.gramOf binEnv

/-- An unparameterised nonterminal. -/
def bnt (x : IL.Id) : Sem.NT := (x, [])

/-! ## The reachable nonterminals -/

mutual

/-- The nonterminals a symbol mentions.  `Sem.transSym` sends `IL.Sym.varG x
args` to `Sym.nt (x, args)` and is the identity on the argument list, so this
is the set of `Sym.nt` nodes of the translated symbol. -/
def ntsOfSym : IL.Sym → List Sem.NT
  | .varG x args => [(x, args)]
  | .numG _ => []
  | .textG _ => []
  | .epsG => []
  | .seqG gs => ntsOfSyms gs
  | .altG gs => ntsOfSyms gs
  | .rangeG g₁ g₂ => ntsOfSym g₁ ++ ntsOfSym g₂
  | .iterG g _ => ntsOfSym g
  | .attrG _ g => ntsOfSym g

/-- `ntsOfSym` over a list. -/
def ntsOfSyms : List IL.Sym → List Sem.NT
  | [] => []
  | g :: gs => ntsOfSym g ++ ntsOfSyms gs

end

/-- The nonterminals the productions of `n` mention, after the grammar-argument
substitution `Sem.prodsOf` performs. -/
def ntChildren (env : Sem.Env) (n : Sem.NT) : List Sem.NT :=
  match env.findGram? n.1 with
  | none => []
  | some (ps, _, prods) =>
      prods.flatMap fun p => match p with
        | .prodD _ g _ _ => ntsOfSym (Sem.substSym (Sem.gramArgSubst ps n.2) g)

/-- Equality of nonterminals, decided through the `--ast` printer: `IL.Arg` is
in `IL.Ast`'s nested mutually recursive group, so `deriving DecidableEq` cannot
reach it, and `IL.argsS` is injective because `IL.decodeArgs?` inverts it
(`IL.decodeArgs?_argsS`). -/
def ntEq (n m : Sem.NT) : Bool := n.1 == m.1 && IL.argsS n.2 == IL.argsS m.2

/-- `ntEq` decides equality. -/
theorem ntEq_iff {n m : Sem.NT} : ntEq n m = true ↔ n = m := by
  constructor
  · intro h
    simp only [ntEq, Bool.and_eq_true, beq_iff_eq] at h
    have : IL.decodeArgs? (IL.argsS n.2) = IL.decodeArgs? (IL.argsS m.2) := by rw [h.2]
    rw [IL.decodeArgs?_argsS, IL.decodeArgs?_argsS, Option.some.injEq] at this
    exact Prod.ext h.1 this
  · rintro rfl; simp [ntEq]

/-- The worklist closure of a set of nonterminals under `ntChildren`, with
explicit fuel: a nonterminal's own productions may name it again, so there is
nothing structural to recurse on. -/
def ntClose (env : Sem.Env) : Nat → List Sem.NT → List Sem.NT → List Sem.NT
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | f + 1, seen, n :: rest =>
      if seen.any (ntEq n) then ntClose env f seen rest
      else ntClose env f (seen ++ [n]) (ntChildren env n ++ rest)

/-- The nonterminals of the corrected wasm-3.0 binary grammar reachable from
`Bmodule`, in the order a breadth-ish traversal finds them. -/
noncomputable def binNTs : List Sem.NT := ntClose binEnv 100000 [] [bnt "Bmodule"]

/-- The binary format of wasm-3.0 has 125 reachable nonterminals.  Counting
*nonterminals* and not *grammar declarations*: a parameterised grammar
contributes one nonterminal per syntactically distinct argument list, so the 84
`B`-prefixed `GramD`s of the corrected script give 125. -/
theorem binNTs_length : binNTs.length = 125 := by rfl

/-! ### `binNTs` really is the reachable set

`binNTs` is computed with *fuel*, so its length alone does not say that the
worklist ran to exhaustion: a list that fuel cut short would also have a
length.  The two facts below close that gap by certifying the result rather
than the computation.  Together they say `binNTs` contains `Bmodule` and is
closed under `ntChildren`, hence contains every nonterminal reachable from
`Bmodule`; `binNTs_length` then makes "the 125 reachable nonterminals" — and
the denominators of every count in this section — a proved statement. -/

/-- **`binNTs` is closed under `ntChildren`**, checked by the kernel. -/
theorem binNTs_closed :
    binNTs.all (fun n => (ntChildren binEnv n).all (fun m => binNTs.any (ntEq m)))
      = true := by rfl

/-- `Bmodule`, the start symbol, is in `binNTs`. -/
theorem bmodule_mem_binNTs : bnt "Bmodule" ∈ binNTs := by
  have h : binNTs.any (ntEq (bnt "Bmodule")) = true := by rfl
  obtain ⟨m, hm, he⟩ := List.any_eq_true.mp h
  exact ntEq_iff.mp he ▸ hm

/-- The propositional form of `binNTs_closed`: every child of a member is a
member.  With `bmodule_mem_binNTs` this is the fixpoint property that makes
`binNTs` an over-approximation-free enumeration of the reachable set. -/
theorem mem_binNTs_of_mem_ntChildren {n m : Sem.NT} (hn : n ∈ binNTs)
    (hm : m ∈ ntChildren binEnv n) : m ∈ binNTs := by
  have h := List.all_eq_true.mp binNTs_closed n hn
  obtain ⟨m', hm', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h m hm)
  exact ntEq_iff.mp he ▸ hm'

/-! ## The class-membership verdict -/

/-- **The corrected wasm-3.0 binary grammar is not prefix-deterministic.**
`Basic.altSeparated` fails at 109 of the 125 reachable nonterminals. -/
theorem countP_not_altSeparated :
    binNTs.countP (fun n => !altSeparated (binGram.prods n)) = 109 := by rfl

/-- `Decoder.detSymList` fails at 26 of the 125: every `IL.Sym.iterG` becomes a
`Sym.star`, which `detSym` excludes outright.  `Sym.count` is unavailable even
for a `ListN` iterator, because the repetition count of `Blist`'s body is bound
by the `Bu32` in front of it and so is not known at translation time. -/
theorem countP_not_detSymList :
    binNTs.countP (fun n => !detSymList (binGram.prods n)) = 26 := by rfl

/-- The witness, class (i): `Bvaltype`.  Each of its three productions begins
with a nonterminal, so `leadRange?` answers `none` for all three and
`altSeparated` fails — although the three *are* distinguished by their first
byte, as `altSepFirst_Bvaltype` below shows.  This is a limitation of the
decidable approximation, not an ambiguity. -/
theorem leadRange_Bvaltype :
    (binGram.prods (bnt "Bvaltype")).map leadRange? = [none, none, none] := by rfl

/-- `altSeparated` therefore fails at `Bvaltype`. -/
theorem altSeparated_Bvaltype : altSeparated (binGram.prods (bnt "Bvaltype")) = false := by rfl

/-- **The verdict.**  `Decoder.Det` does not hold of the corrected wasm-3.0
binary grammar. -/
theorem not_det_binGram : ¬ Det binGram := by
  intro h
  have := h.sep (bnt "Bvaltype")
  rw [altSeparated_Bvaltype] at this
  exact absurd this (by simp)

/-- The witness, class (ii): `Binstr`.  Every one of its 498 productions has a
known leading byte range — `leadRange?` is *exact* here — and they are still not
pairwise disjoint, because the `0xFB`, `0xFC` and `0xFD` prefixes are shared by
whole families of instructions whose opcode continues into a following `Bu32`.
No FIRST-set computation can help: the information `leadRange?` is missing is
not about nonterminals but about the *second* byte. -/
theorem leadRange_Binstr_all_known :
    (binGram.prods (bnt "Binstr")).all (fun g => (leadRange? g).isSome) = true := by rfl

/-- …and `altSeparated` fails at `Binstr` all the same. -/
theorem altSeparated_Binstr : altSeparated (binGram.prods (bnt "Binstr")) = false := by rfl

/-! ## What the FIRST certificate buys -/

/-- A FIRST assignment for the §5.1 values and §5.2 types nonterminals of the
corrected wasm-3.0 binary grammar.

Every entry is a nonterminal with no grammar arguments, and the table is closed
in the only direction that matters: whenever a production of a listed
nonterminal *begins* with a nonterminal, that one is listed too.  Everything
else — in particular `Bu32`, `BuN(N)`, `BsN(N)`, `Blist(BX)` and the section
grammars — is answered `none`, which costs nothing here because the productions
that mention them do not *begin* with them.

The sets are written as tidy interval unions; `firstOk` only asks for
containment, so they may be, and in a few places are, larger than the exact
union of the per-production sets. -/
def binFirst : Sem.NT → Option ByteSet
  | ("Bbyte", []) => some [(0x00, 0xFF)]
  | ("Bnumtype", []) => some [(0x7C, 0x7F)]
  | ("Bvectype", []) => some [(0x7B, 0x7B)]
  | ("Babsheaptype", []) => some [(0x69, 0x74)]
  | ("Breftype", []) => some [(0x63, 0x64), (0x69, 0x74)]
  | ("Bvaltype", []) => some [(0x63, 0x64), (0x69, 0x74), (0x7B, 0x7F)]
  | ("Bpacktype", []) => some [(0x77, 0x78)]
  | ("Bstoragetype", []) => some [(0x63, 0x64), (0x69, 0x74), (0x77, 0x78), (0x7B, 0x7F)]
  | ("Bfieldtype", []) => some [(0x63, 0x64), (0x69, 0x74), (0x77, 0x78), (0x7B, 0x7F)]
  | ("Bcomptype", []) => some [(0x5E, 0x60)]
  | ("Bsubtype", []) => some [(0x4F, 0x50), (0x5E, 0x60)]
  | ("Brectype", []) => some [(0x4E, 0x50), (0x5E, 0x60)]
  | ("Btype", []) => some [(0x4E, 0x50), (0x5E, 0x60)]
  | ("Bmut", []) => some [(0x00, 0x01)]
  | ("Blimits", []) => some [(0x00, 0x01), (0x04, 0x05)]
  | ("Bexterntype", []) => some [(0x00, 0x04)]
  | ("Btagtype", []) => some [(0x00, 0x00)]
  | ("Belemkind", []) => some [(0x00, 0x00)]
  | ("Bcastop", []) => some [(0x00, 0x03)]
  | ("Bexternidx", []) => some [(0x00, 0x04)]
  | ("Bcatch", []) => some [(0x00, 0x03)]
  | ("Bmagic", []) => some [(0x00, 0x00)]
  | ("Bversion", []) => some [(0x01, 0x01)]
  | _ => none

/-- **The FIRST certificate checks out.**  Every entry of `binFirst` passes
`firstOk` against the corrected grammar, so the analysis is sound for it. -/
theorem firstSound_binFirst : FirstSound binGram binFirst := by
  intro x s hx
  unfold binFirst at hx
  split at hx <;> first
    | (obtain rfl := Option.some.inj hx; rfl)
    | simp at hx

/-- With `leadRange?`, 16 of the 125 reachable nonterminals have pairwise
separated productions (`countP_not_altSeparated` counts the other 109).  With
the 23-entry FIRST certificate above, 29 do.  The 13 new ones are
`Bvaltype`, `Breftype`, `Bstoragetype`, `Bfieldtype`, `Bsubtype`, `Brectype`,
`Btype`, `Bglobaltype`, `Bmemtype`, `Btabletype`, `Blaneidx`, `Btag` and —
because a lone production needs only a FIRST set of its own, not a disjointness
check — `Bmodule`. -/
theorem countP_altSepFirst :
    binNTs.countP (fun n => altSepFirst binFirst (binGram.prods n)) = 29 := by rfl

/-- The 26 nonterminals of §5.1–§5.2 the certificate separates, in one check. -/
theorem altSepFirst_types :
    ["Bbyte", "Bnumtype", "Bvectype", "Babsheaptype", "Breftype", "Bvaltype", "Bpacktype",
      "Bstoragetype", "Bfieldtype", "Bcomptype", "Bsubtype", "Brectype", "Btype", "Bmut",
      "Blimits", "Bexterntype", "Btagtype", "Belemkind", "Bcastop", "Bexternidx", "Bcatch",
      "Bmagic", "Bversion", "Bglobaltype", "Bmemtype", "Btabletype"].all
      (fun x => altSepFirst binFirst (binGram.prods (bnt x))) = true := by rfl

/-- `Bvaltype` is FIRST-separated where `altSeparated` fails. -/
theorem altSepFirst_Bvaltype : altSepFirst binFirst (binGram.prods (bnt "Bvaltype")) = true := by
  rfl

/-- **The three cases of a value type are distinguished by their first byte.**
No two productions of `Bvaltype` derive byte strings that begin alike, so a
`valtype` is parsed deterministically once that byte is read.  This is not
obtainable from `Basic.altSeparated`: `leadRange_Bvaltype` above says it
answers `none` for all three. -/
theorem separated_Bvaltype :
    (binGram.prods (bnt "Bvaltype")).Pairwise
      (fun g g' => Separated (denote binGram g) (denote binGram g')) :=
  altSepFirst_pairwise binGram firstSound_binFirst altSepFirst_Bvaltype

/-- The FIRST set of `Bvaltype`, as a theorem about the corrected
specification: every byte string a `valtype` derives begins with one of
`0x63`, `0x64`, `0x69`–`0x74`, `0x7B`–`0x7F`. -/
theorem first_Bvaltype {bs : Bytes} {a : Sem.Act}
    (h : denote binGram (.nt (bnt "Bvaltype")) bs a) :
    ∃ b bs', bs = b :: bs' ∧
      ByteSet.has [(0x63, 0x64), (0x69, 0x74), (0x7B, 0x7F)] b = true :=
  firstOf_sound binGram firstSound_binFirst (g := .nt (bnt "Bvaltype")) rfl h

/-- The same statement at the level of `Sem/Grammar.lean`'s grammar relation,
which is where the specification's own `GramD` lives. -/
theorem first_Bvaltype_gramRel {ρ : Sem.VarEnv} {bs : Bytes} {v : Sem.Value}
    (h : Sem.gramRelSup binEnv ρ (.varG "Bvaltype" []) bs v) :
    ∃ b bs', bs = b :: bs' ∧
      ByteSet.has [(0x63, 0x64), (0x69, 0x74), (0x7B, 0x7F)] b = true := by
  obtain ⟨a, -, ha, -⟩ := h
  exact first_Bvaltype ha

/-- `Breftype` likewise: `0x63`, `0x64` and the twelve abstract heap types. -/
theorem first_Breftype {bs : Bytes} {a : Sem.Act}
    (h : denote binGram (.nt (bnt "Breftype")) bs a) :
    ∃ b bs', bs = b :: bs' ∧ ByteSet.has [(0x63, 0x64), (0x69, 0x74)] b = true :=
  firstOf_sound binGram firstSound_binFirst (g := .nt (bnt "Breftype")) rfl h

/-- `Brectype`, hence a type-section entry: `0x4E`–`0x50` and `0x5E`–`0x60`. -/
theorem first_Brectype {bs : Bytes} {a : Sem.Act}
    (h : denote binGram (.nt (bnt "Brectype")) bs a) :
    ∃ b bs', bs = b :: bs' ∧ ByteSet.has [(0x4E, 0x50), (0x5E, 0x60)] b = true :=
  firstOf_sound binGram firstSound_binFirst (g := .nt (bnt "Brectype")) rfl h

/-! ## A deterministic sub-grammar, and a verified decoder for it -/

/-- The nonterminals of the corrected binary grammar whose productions pass
`Basic.altSeparated` *and* `Decoder.detSymList`: the 16 of the 125 that
`Decoder.Det` admits.  All of them are unparameterised. -/
def detNames : List IL.Id :=
  ["Bbyte", "Bnumtype", "Bvectype", "Babsheaptype", "Bpacktype", "Bmut", "Blimits",
    "Bexterntype", "Btagtype", "Belemkind", "Bcastop", "Bexternidx", "Bcatch", "Bcomptype",
    "Bmagic", "Bversion"]

/-- The corrected binary grammar restricted to `detNames`: every other
nonterminal is given no productions, hence denotes `⊥`.  Restricting rather
than enlarging is what makes `Det` reachable without a closure computation —
`altSeparated []` and `detSymList []` are both `true`. -/
noncomputable def binGramDet : Gram Sem.NT Sem.Act :=
  ⟨Sem.actAlg, fun n => if detNames.contains n.1 && n.2.isEmpty then binGram.prods n else []⟩

/-- The production table of `binGramDet`, by definition. -/
theorem binGramDet_prods (n : Sem.NT) :
    binGramDet.prods n =
      if detNames.contains n.1 && n.2.isEmpty then binGram.prods n else [] := rfl

/-- The 16 names really do pass both checks; one kernel computation for all of
them. -/
theorem detNames_ok :
    detNames.all (fun x => altSeparated (binGram.prods (bnt x)) &&
      detSymList (binGram.prods (bnt x))) = true := by rfl

/-- **`binGramDet` is prefix-deterministic.** -/
theorem det_binGramDet : Det binGramDet := by
  have key : ∀ n : Sem.NT, altSeparated (binGramDet.prods n) = true ∧
      detSymList (binGramDet.prods n) = true := by
    intro n
    rw [binGramDet_prods]
    split
    · next h =>
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨hc, he⟩ := h
      have hn : n = bnt n.1 := Prod.ext rfl he
      have := (List.all_eq_true.mp detNames_ok) n.1 (by simpa using hc)
      simp only [Bool.and_eq_true] at this
      rw [hn]
      exact this
    · exact ⟨rfl, rfl⟩
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

/-- Restricting the production table only shrinks the denotation, so every
derivation of `binGramDet` is a derivation of the corrected grammar itself. -/
theorem denote_binGramDet_le (g : Sym Sem.NT Sem.Act) :
    denote binGramDet g ≤ denote binGram g := by
  refine denote_mono_prods (A := Sem.actAlg) (P := binGramDet.prods)
    (P' := binGram.prods) (fun x g' hg' => ?_) g
  rw [binGramDet_prods] at hg'
  split at hg'
  · exact hg'
  · exact absurd hg' (by simp)

/-! ## Decoding a real module prefix -/

/-- The eight bytes every WebAssembly module begins with: `\0asm` and the
version word (`5.4-binary.modules.spectec:173-174`). -/
def wasmHeader : Bytes := [0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00]

/-- `Bmagic Bversion`, the first two factors of `Bmodule`
(`5.4-binary.modules.spectec:175-176`). -/
def headerSym : Sym Sem.NT Sem.Act := .seq [.nt (bnt "Bmagic"), .nt (bnt "Bversion")]

/-- The header symbol is in the deterministic class. -/
theorem detSym_headerSym : detSym headerSym = true := by rfl

/-- **The verified decoder accepts the module header.**  One kernel
computation: `run` descends through `Bmagic` and `Bversion`, matches all eight
bytes, and leaves nothing over. -/
theorem decode_wasmHeader :
    ∃ a : Sem.Act, decode binGramDet 32 headerSym wasmHeader = some (a, []) :=
  ⟨_, rfl⟩

/-- …so the header is derived by the corrected wasm-3.0 grammar, through
`decode_sound` (which needs no hypothesis at all) and
`denote_binGramDet_le`. -/
theorem denote_wasmHeader : ∃ a : Sem.Act, denote binGram headerSym wasmHeader a := by
  obtain ⟨a, ha⟩ := decode_wasmHeader
  obtain ⟨pre, hpre, hd⟩ := decode_sound binGramDet ha
  rw [List.append_nil] at hpre
  subst hpre
  exact ⟨a, denote_binGramDet_le headerSym _ _ hd⟩

/-- And on `binGramDet` the decoder is a *decision procedure*: `Encodes` and
`denote` are the same relation, by `Decoder.encodes_iff_denote` at
`det_binGramDet`. -/
theorem encodes_iff_denote_headerSym (a : Sem.Act) (bs : Bytes) :
    Encodes binGramDet headerSym a bs ↔ denote binGramDet headerSym bs a :=
  encodes_iff_denote binGramDet det_binGramDet detSym_headerSym a bs

/-! ### …with the expected value

`Sem.Act` is an environment transformer, so "the decoder produced the expected
value" is the statement that the attribute it returns relates the empty scope
to the value list the production's own value expression computes.  For
`Bmagic Bversion` that is `((), ())`: both productions are `… => ()`
(`5.4-binary.modules.spectec:173-174`), and the elaborated value expression is
`(proj (tup (tup) (tup)) 1)`, the second component of a pair of empty tuples. -/

/-- The attribute of a four-byte literal production, applied: it relates the
empty scope to the four numerals its terminals contributed.  `actApp _ actNil`
is what `Sym.seq [Sym.byte b]` contributes, and the outer `actNil` is the end
of the sequence. -/
theorem act_four (b₁ b₂ b₃ b₄ : UInt8) :
    Sem.actApp (Sem.actApp (Sem.actByte b₁) Sem.actNil)
      (Sem.actApp (Sem.actApp (Sem.actByte b₂) Sem.actNil)
        (Sem.actApp (Sem.actApp (Sem.actByte b₃) Sem.actNil)
          (Sem.actApp (Sem.actApp (Sem.actByte b₄) Sem.actNil) Sem.actNil)))
      Sem.VarEnv.empty
      [.num (.natN b₁.toNat), .num (.natN b₂.toNat), .num (.natN b₃.toNat),
        .num (.natN b₄.toNat)] Sem.VarEnv.empty := by
  simp only [Sem.actApp_nil]
  exact ⟨_, Sem.VarEnv.empty, _, ⟨rfl, rfl⟩, ⟨_, Sem.VarEnv.empty, _, ⟨rfl, rfl⟩,
    ⟨_, Sem.VarEnv.empty, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- **The verified decoder produces the expected value.**  Run on the corrected
wasm-3.0 grammar's `Bmagic Bversion`, with 32 units of fuel, it consumes all
eight bytes of the header and returns an attribute that assigns them the two
unit values — and `decode_sound` turns that into a derivation of the corrected
grammar itself.

Every component is kernel-checked: the `rfl` reduces `run` over the production
tables `Sem.prodsOf` reads out of `Errata.Binary51.wasm30binary51`, and the
`Sem.EvalExp` obligations are discharged by the equation lemmas of
`Sem/Eval.lean`'s fuel-indexed evaluator (`evalExp` is defined by well-founded
recursion, so it does not reduce; `simp` with its equations does). -/
theorem decode_wasmHeader_value (ρ : Sem.VarEnv) :
    ∃ a : Sem.Act, decode binGramDet 32 headerSym wasmHeader = some (a, []) ∧
      denote binGram headerSym wasmHeader a ∧
      a ρ [.tuple [], .tuple []] ρ := by
  refine ⟨_, rfl, ?_, ?_⟩
  · obtain ⟨pre, hpre, hd⟩ := decode_sound binGramDet (rfl : decode binGramDet 32 headerSym
      wasmHeader = some _)
    rw [List.append_nil] at hpre
    subst hpre
    exact denote_binGramDet_le headerSym _ _ hd
  refine ⟨[.tuple []], ρ, [.tuple []], ?_, ⟨[.tuple []], ρ, [], ?_, ⟨rfl, rfl⟩, rfl⟩, rfl⟩
  · exact ⟨rfl, [], Sem.VarEnv.empty,
      [.num (.natN 0x00), .num (.natN 0x61), .num (.natN 0x73), .num (.natN 0x6D)],
      Sem.VarEnv.empty, Sem.VarEnv.empty, .tuple [], Sem.evalArgs_nil .., rfl,
      act_four 0x00 0x61 0x73 0x6D, Sem.premsHold_nil ..,
      ⟨10, by simp [Sem.evalExp, Sem.evalExps]⟩, rfl⟩
  · exact ⟨rfl, [], Sem.VarEnv.empty,
      [.num (.natN 0x01), .num (.natN 0x00), .num (.natN 0x00), .num (.natN 0x00)],
      Sem.VarEnv.empty, Sem.VarEnv.empty, .tuple [], Sem.evalArgs_nil .., rfl,
      act_four 0x01 0x00 0x00 0x00, Sem.premsHold_nil ..,
      ⟨10, by simp [Sem.evalExp, Sem.evalExps]⟩, rfl⟩

/-! ### The same value, in the specification's own terms

`Sem.gramRelSup` is the relation `docs/projects/spectec/README.md` names as the
denotation of a `GramD`.  The two theorems below say the corrected wasm-3.0
specification gives the magic number and the version word the value `()`,
built from `Sem/Grammar.lean`'s compositionality lemmas rather than through the
decoder. -/

/-- The `GramD` the corrected script declares for `Bmagic`
(`5.4-binary.modules.spectec:173`), read off `binEnv` by the kernel. -/
theorem findGram_Bmagic :
    binEnv.findGram? "Bmagic" = some ([], .tupT [],
      [.prodD [] (.seqG [.seqG [.numG 0x00], .seqG [.numG 0x61], .seqG [.numG 0x73],
        .seqG [.numG 0x6D]]) (.projE (.tupE [.tupE [], .tupE []]) 1) []]) := by rfl

/-- The `GramD` for `Bversion` (`5.4-binary.modules.spectec:174`). -/
theorem findGram_Bversion :
    binEnv.findGram? "Bversion" = some ([], .tupT [],
      [.prodD [] (.seqG [.seqG [.numG 0x01], .seqG [.numG 0x00], .seqG [.numG 0x00],
        .seqG [.numG 0x00]]) (.projE (.tupE [.tupE [], .tupE []]) 1) []]) := by rfl

/-- A one-byte factor of a literal sequence. -/
theorem derives_byte (ρ : Sem.VarEnv) (n : Nat) (h : n < 256) :
    Sem.SymDerives binEnv ρ (.seqG [.numG n]) [UInt8.ofNat n]
      [.num (.natN (UInt8.ofNat n).toNat)] ρ := by
  rw [Sem.symDerives_seqG_cons]
  exact ⟨[UInt8.ofNat n], _, ρ, [], [], (Sem.symDerives_numG h).mpr ⟨rfl, rfl, rfl⟩,
    Sem.symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩, by simp, by simp⟩

/-- A four-byte literal production of an unparameterised, premise-free grammar
whose value expression denotes `()`. -/
theorem derives_four (ρ : Sem.VarEnv) (x : IL.Id) (b₁ b₂ b₃ b₄ : Nat)
    (h₁ : b₁ < 256) (h₂ : b₂ < 256) (h₃ : b₃ < 256) (h₄ : b₄ < 256)
    (h : binEnv.findGram? x = some ([], .tupT [],
      [.prodD [] (.seqG [.seqG [.numG b₁], .seqG [.numG b₂], .seqG [.numG b₃],
        .seqG [.numG b₄]]) (.projE (.tupE [.tupE [], .tupE []]) 1) []])) :
    Sem.gramRelSup binEnv ρ (.varG x [])
      [UInt8.ofNat b₁, UInt8.ofNat b₂, UInt8.ofNat b₃, UInt8.ofNat b₄] (.tuple []) := by
  rw [Sem.gramRelSup_iff]
  refine ⟨ρ, ?_⟩
  rw [Sem.symDerives_varG h]
  refine ⟨rfl, _, List.mem_cons_self .., ?_⟩
  refine ⟨[], Sem.VarEnv.empty,
    [.num (.natN (UInt8.ofNat b₁).toNat), .num (.natN (UInt8.ofNat b₂).toNat),
      .num (.natN (UInt8.ofNat b₃).toNat), .num (.natN (UInt8.ofNat b₄).toNat)],
    Sem.VarEnv.empty, Sem.VarEnv.empty, .tuple [], Sem.evalArgs_nil .., rfl, ?_,
    Sem.premsHold_nil .., ⟨10, by simp [Sem.evalExp, Sem.evalExps]⟩, rfl⟩
  show Sem.SymDerives binEnv Sem.VarEnv.empty
    (.seqG [.seqG [.numG b₁], .seqG [.numG b₂], .seqG [.numG b₃], .seqG [.numG b₄]]) _ _ _
  rw [Sem.symDerives_seqG_cons]
  refine ⟨_, _, Sem.VarEnv.empty, _, _, derives_byte _ b₁ h₁, ?_, rfl, rfl⟩
  rw [Sem.symDerives_seqG_cons]
  refine ⟨_, _, Sem.VarEnv.empty, _, _, derives_byte _ b₂ h₂, ?_, rfl, rfl⟩
  rw [Sem.symDerives_seqG_cons]
  refine ⟨_, _, Sem.VarEnv.empty, _, _, derives_byte _ b₃ h₃, ?_, rfl, rfl⟩
  rw [Sem.symDerives_seqG_cons]
  refine ⟨_, _, Sem.VarEnv.empty, [], [], derives_byte _ b₄ h₄, ?_, rfl, rfl⟩
  exact Sem.symDerives_seqG_nil.mpr ⟨rfl, rfl, rfl⟩

/-- **`Bmagic` derives `\0asm` with the value `()`**, in the corrected
wasm-3.0 specification. -/
theorem bmagic_derives (ρ : Sem.VarEnv) :
    Sem.gramRelSup binEnv ρ (.varG "Bmagic" []) [0x00, 0x61, 0x73, 0x6D] (.tuple []) :=
  derives_four ρ "Bmagic" 0x00 0x61 0x73 0x6D (by decide) (by decide) (by decide) (by decide)
    findGram_Bmagic

/-- **`Bversion` derives the version word with the value `()`.** -/
theorem bversion_derives (ρ : Sem.VarEnv) :
    Sem.gramRelSup binEnv ρ (.varG "Bversion" []) [0x01, 0x00, 0x00, 0x00] (.tuple []) :=
  derives_four ρ "Bversion" 0x01 0x00 0x00 0x00 (by decide) (by decide) (by decide) (by decide)
    findGram_Bversion

end Corrected

end Silmaril.SpecTec.Grammar
