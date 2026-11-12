module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Grammar.Basic
public import Silmaril.Raw.Wasm.SpecTec.Wasm.Binary.RefInterp
public import Mathlib.Data.Fintype.Basic

/-!
# A generic decoder for byte attribute grammars

`Silmaril/SpecTec/Grammar/Basic.lean` gives a `Sym N α` a denotation as an
`EncRel Bytes α` and proves the compositionality and functionality theory.  It
leaves open what its own module docstring calls "a generic decoder for a
deterministic subclass", and this file supplies it: a recursive-descent decoder
`decode`, unconditional soundness, completeness on a decidable deterministic
subclass, the encoder story, and LEB128 as the worked instance.

## Shape of the decoder

`decode G fuel g bs` consumes a *prefix* of `bs` and returns the attribute
together with the unconsumed rest, so it composes: the decoder for a factor of
a `seq` is run on the whole remaining input and hands the tail to its
successor.  This is the shape of the reference interpreter's own decoders —
`uN n s` (`interpreter/binary/decode.ml:85-90`) reads from a mutable stream and
leaves the rest — and of `Silmaril.Wasm.Binary.RefInterp.refUN`, which is that
transcription.

### Fuel, not well-founded recursion

The recursion is structural in an explicit `Nat` of fuel.  Nothing else is
available: a nonterminal unfolds to its productions without consuming a byte
first, so neither the input nor the symbol decreases, and `decode` would need
well-founded recursion — which does not reduce in the kernel, so no `decide`,
`rfl` or `simp` on a closed grammar would ever fire.  Every recursive call
spends exactly one unit, so the fuel bounds the *depth of the derivation tree*,
not the length of the input.

### One function, not five

`seq`, `alt`, `star` and `count` each need a recursion over a *list* of symbols
or a *number* of repetitions, which in the obvious presentation makes `decode`
one of five mutually recursive functions.  Instead there is a single function
`run` over a `Job`, the disjoint union of the five things the decoder can be
asked to do.  The payoff is that soundness, fuel monotonicity and completeness
are each *one* induction on the fuel with a `cases` on the job, rather than
five mutually recursive inductions, and that `Job.rel` gives the five
specifications in one definition.

### Why recursive descent and not Brzozowski derivatives

A derivative formulation `∂_b : Sym N α → Sym N α` would be prettier, but it
cannot be written here at all: `Sym` carries attribute actions as *functions*
(`Sym.attr (f : α → Option α)`, `Basic.lean`'s deliberate design choice), and
the derivative of `attr f g` must postcompose `f` with the attribute that the
already-consumed bytes contributed.  That is a `Sym` whose action depends on
the consumed prefix, i.e. a closure, so the derivative is not a `Sym` but a
`Bytes → Sym`; and the derivative of a nonterminal re-enters the grammar, so
the construction needs its own fuel anyway.  Recursive descent keeps the
attribute algebra where `Basic.lean` put it and costs nothing in the proofs.

## The deterministic subclass

`decode` makes a choice in exactly three places: which branch of an `alt` (and
hence which production of a nonterminal) to take, and whether to go round again
in a `star`/`plus`/`opt`.  `Det` rules both out:

* every `alt`, and the production list of every nonterminal, passes
  `Basic.lean`'s decidable `altSeparated` — the branches have disjoint leading
  byte ranges;
* `star`, `plus` and `opt` do not occur.  `count g k` does: a fixed repetition
  count is not a choice.

`Det G` is therefore `decidable` for a grammar with finitely many nonterminals
(`detGram`, below, is the `Bool` that decides it from an explicit list of
nonterminals; an explicit list rather than `[Fintype N]` because the LEB128
instance has `N = Nat` — the bit widths — of which only the finitely many
reachable ones matter, and because the IL's nonterminals are identifiers paired
with argument lists, which are not a `Fintype` either).

**Left recursion needs no separate check.**  `altSeparated gs` demands
`leadRange? g = some _` for *every* branch `g` (`Basic.altSeparated_leadRange`),
and `leadRange?` answers `none` for `nt`, for `eps`, and for any `seq` whose
first factor is one of those.  So under `Det` every production of every
nonterminal begins with a byte terminal, hence consumes a byte before reaching
any nonterminal: the productivity condition is *implied* by the separation
condition, and `Det.nonNullable_nt` below is the proof.  This is a happy
accident of `leadRange?` being a leading-*terminal* analysis rather than a
FIRST-set fixpoint, and it is why no reachability computation over the grammar
appears in this file.

## What is proved

* `run_sound`/`decode_sound`, with **no** hypothesis on the grammar: a
  successful decode exhibits a derivation of the consumed prefix.
  `decode_sound_take` is the `List.take`/`List.drop` restatement.
* `run_mono`/`decode_mono`: more fuel never changes a successful answer, on the
  deterministic class.  This needs `Det`, and not only for termination: at an
  `alt`, a branch that failed for lack of fuel could succeed with more and
  steal the parse, and it is separation that rules that out.
* `run_complete`/`decode_complete`: on the deterministic class, every
  derivation is found, for *any* continuation `rest`.
* `decode_eq_some_iff`: the two directions combined, the decoder as a decision
  procedure for `denote`.
* `Encodes`, `denote_of_encodes`, `encodes_iff_denote` and `encoder_sound`: an
  encoder is a right inverse of the decoder, and on the deterministic class
  "`bs` encodes `a`" and "`denote` derives `a` from `bs`" are the same
  statement.  `encodeOf` is the classical encoder, `encodeOf_isSome_iff` and
  `encodeOf_total` say exactly when it is defined — on the image of the
  denotation, no more and no less.
* LEB128: `det_lebGram`, `decode_leb_iff`, and the headline
  `decode_leb_iff_refUN`, which says that this generic decoder, run on
  `Basic.lebGram`, accepts exactly what the hand-written `refUN` of
  `Silmaril/Wasm/Binary/RefInterp.lean` accepts, with the same value and the
  same leftover bytes; `leb_encodable` is the encoder's totality, for every
  `m < 2 ^ W`.

## Not here

* `star`, `plus` and `opt` are *decoded* (greedily, with a progress check that
  refuses a nullable body) and their decodes are *sound*, but they are outside
  `Det`, so completeness does not cover them.  Greedy iteration is complete
  only against a FOLLOW condition — `seq [star (byte 0), byte 0]` is the
  counterexample — and FOLLOW is a fixpoint over the whole grammar, unlike
  `leadRange?`.  `decode_star_complete_eof` is the one case that needs no
  FOLLOW set: a `star` at the end of the input.
* An explicit fuel *bound* as a function of the input length.  `Det` makes one
  exist (every production consumes a byte before recursing), but the accounting
  is a separate development; completeness is stated with `∃ fuel` and
  `decode_mono`.
-/

@[expose] public section

namespace Silmaril.SpecTec.Grammar

open Silmaril

variable {N α : Type}

/-! ## Byte-string prefixes -/

/-- Strip a literal prefix: `stripPrefix l bs` is the rest of `bs` after `l`,
or `none` if `bs` does not begin with `l`.  Spelled out rather than taken from
`List.isPrefixOf` plus `List.drop` so that both directions below are one
structural induction. -/
def stripPrefix : Bytes → Bytes → Option Bytes
  | [], bs => some bs
  | _ :: _, [] => none
  | c :: l, b :: bs => if c = b then stripPrefix l bs else none

/-- `stripPrefix` is sound: a `some` answer splits the input. -/
theorem stripPrefix_eq_some {l bs r : Bytes} (h : stripPrefix l bs = some r) :
    bs = l ++ r := by
  induction l generalizing bs with
  | nil => simpa [stripPrefix] using h
  | cons c l ih =>
    cases bs with
    | nil => simp [stripPrefix] at h
    | cons b bs =>
      simp only [stripPrefix] at h
      split at h
      · next hcb => subst hcb; simpa using ih h
      · simp at h

/-- `stripPrefix` is complete: it strips a prefix that is there. -/
@[simp] theorem stripPrefix_append (l r : Bytes) : stripPrefix l (l ++ r) = some r := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [stripPrefix, ih]

/-! ## Jobs -/

/-- What the decoder can be asked to do.  `Job` is the disjoint union of the
five recursions that a recursive-descent decoder for `Sym` needs, packaged so
that `run` is a single function, structurally recursive in its fuel. -/
inductive Job (N : Type) (α : Type) where
  /-- Decode one symbol. -/
  | sym (g : Sym N α)
  /-- Decode a list of symbols in sequence (`Sym.seq`, and the productions of a
  nonterminal after the branch is chosen). -/
  | seq (gs : List (Sym N α))
  /-- Try a list of symbols in order and take the first that succeeds
  (`Sym.alt`, and the production list of a nonterminal). -/
  | alt (gs : List (Sym N α))
  /-- Iterate a symbol greedily (`Sym.star`). -/
  | star (g : Sym N α)
  /-- Iterate a symbol a fixed number of times (`Sym.count`). -/
  | count (g : Sym N α) (k : Nat)
  deriving Inhabited

/-- The specification of a job: the encoding relation it is meant to decode.
Each clause is the right-hand side of the corresponding compositionality
theorem of `Basic.lean` (`denote_seq`, `denote_alt`, `denote_star`,
`denote_count`). -/
def Job.rel (G : Gram N α) : Job N α → EncRel Bytes α
  | .sym g => denote G g
  | .seq gs => appendAll G.alg (gs.map (denote G))
  | .alt gs => supList (gs.map (denote G))
  | .star g => kleene G.alg (denote G g)
  | .count g k => powRel G.alg (denote G g) k

/-! ## The decoder -/

/-- The decoder.  `run G n j bs` spends at most `n` units of fuel decoding the
job `j` from `bs`, and on success returns the attribute and the unconsumed
rest.

The `star` clause is greedy and refuses to loop: if the body derives the empty
string it has made no progress, and the iteration fails rather than diverging
(the grammar is outside `Det` in that case anyway). -/
def run (G : Gram N α) : Nat → Job N α → Bytes → Option (α × Bytes)
  | 0, _, _ => none
  | _ + 1, .sym .eps, bs => some (G.alg.nil, bs)
  | _ + 1, .sym (.byte _), [] => none
  | _ + 1, .sym (.byte b), c :: r => if c = b then some (G.alg.ofByte c, r) else none
  | _ + 1, .sym (.range _ _), [] => none
  | _ + 1, .sym (.range lo hi), c :: r =>
      if lo ≤ c ∧ c ≤ hi then some (G.alg.ofByte c, r) else none
  | _ + 1, .sym (.bytes l), bs =>
      match stripPrefix l bs with
      | none => none
      | some r => some (G.alg.ofBytes l, r)
  | n + 1, .sym (.nt x), bs => run G n (.alt (G.prods x)) bs
  | n + 1, .sym (.seq gs), bs => run G n (.seq gs) bs
  | n + 1, .sym (.alt gs), bs => run G n (.alt gs) bs
  | n + 1, .sym (.star g), bs => run G n (.star g) bs
  | n + 1, .sym (.plus g), bs =>
      match run G n (.sym g) bs with
      | none => none
      | some (a, r) =>
        match run G n (.star g) r with
        | none => none
        | some (a', r') => some (G.alg.app a a', r')
  | n + 1, .sym (.opt g), bs =>
      match run G n (.sym g) bs with
      | none => some (G.alg.nil, bs)
      | some (a, r) => some (a, r)
  | n + 1, .sym (.count g k), bs => run G n (.count g k) bs
  | n + 1, .sym (.attr f g), bs =>
      match run G n (.sym g) bs with
      | none => none
      | some (a, r) =>
        match f a with
        | none => none
        | some b => some (b, r)
  | _ + 1, .seq [], bs => some (G.alg.nil, bs)
  | n + 1, .seq (g :: gs), bs =>
      match run G n (.sym g) bs with
      | none => none
      | some (a, r) =>
        match run G n (.seq gs) r with
        | none => none
        | some (a', r') => some (G.alg.app a a', r')
  | _ + 1, .alt [], _ => none
  | n + 1, .alt (g :: gs), bs =>
      match run G n (.sym g) bs with
      | some (a, r) => some (a, r)
      | none => run G n (.alt gs) bs
  | n + 1, .star g, bs =>
      match run G n (.sym g) bs with
      | none => some (G.alg.nil, bs)
      | some (a, r) =>
        if r.length < bs.length then
          match run G n (.star g) r with
          | none => none
          | some (a', r') => some (G.alg.app a a', r')
        else none
  | _ + 1, .count _ 0, bs => some (G.alg.nil, bs)
  | n + 1, .count g (k + 1), bs =>
      match run G n (.sym g) bs with
      | none => none
      | some (a, r) =>
        match run G n (.count g k) r with
        | none => none
        | some (a', r') => some (G.alg.app a a', r')

/-- The decoder, specialised to a symbol: consume a prefix of `bs` and return
the attribute and the rest. -/
def decode (G : Gram N α) (n : Nat) (g : Sym N α) (bs : Bytes) : Option (α × Bytes) :=
  run G n (.sym g) bs

/-- Out of fuel is failure. -/
@[simp] theorem run_zero (G : Gram N α) (j : Job N α) (bs : Bytes) :
    run G 0 j bs = none := rfl

/-- `decode` is `run` on a `sym` job. -/
theorem decode_eq_run (G : Gram N α) (n : Nat) (g : Sym N α) (bs : Bytes) :
    decode G n g bs = run G n (.sym g) bs := rfl

/-! ## Soundness

Unconditional: a successful decode exhibits a derivation of the bytes it
consumed.  Nothing about the grammar is assumed — not determinism, not
productivity — because `run` only ever *reports* a parse it has built.
-/

/-- **Soundness.**  If `run` succeeds it has consumed a prefix of its input,
and the job's specification derives that prefix with the reported attribute. -/
theorem run_sound (G : Gram N α) :
    ∀ (n : Nat) (j : Job N α) (bs : Bytes) (a : α) (rest : Bytes),
      run G n j bs = some (a, rest) → ∃ pre, bs = pre ++ rest ∧ j.rel G pre a := by
  intro n
  induction n with
  | zero => intro j bs a rest h; simp at h
  | succ n ih =>
    intro j bs a rest h
    cases j with
    | sym g =>
      cases g with
      | eps =>
        simp only [run, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, by rw [Job.rel, denote_eps]; exact ⟨rfl, rfl⟩⟩
      | byte b =>
        cases bs with
        | nil => simp [run] at h
        | cons c r =>
          simp only [run] at h
          split at h
          · next hcb =>
            subst hcb
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨[c], rfl, by rw [Job.rel, denote_byte]; exact ⟨rfl, rfl⟩⟩
          · simp at h
      | range lo hi =>
        cases bs with
        | nil => simp [run] at h
        | cons c r =>
          simp only [run] at h
          split at h
          · next hr =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨[c], rfl, by
              rw [Job.rel, denote_range]; exact ⟨c, hr.1, hr.2, rfl, rfl⟩⟩
          · simp at h
      | bytes l =>
        simp only [run] at h
        split at h
        · simp at h
        · next r hr =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨l, stripPrefix_eq_some hr, by rw [Job.rel, denote_bytes]; exact ⟨rfl, rfl⟩⟩
      | nt x =>
        simp only [run] at h
        obtain ⟨pre, rfl, hd⟩ := ih _ _ _ _ h
        exact ⟨pre, rfl, by rw [Job.rel, denote_nt]; exact hd⟩
      | seq gs =>
        simp only [run] at h
        obtain ⟨pre, rfl, hd⟩ := ih _ _ _ _ h
        exact ⟨pre, rfl, by rw [Job.rel, denote_seq]; exact hd⟩
      | alt gs =>
        simp only [run] at h
        obtain ⟨pre, rfl, hd⟩ := ih _ _ _ _ h
        exact ⟨pre, rfl, by rw [Job.rel, denote_alt]; exact hd⟩
      | star g =>
        simp only [run] at h
        obtain ⟨pre, rfl, hd⟩ := ih _ _ _ _ h
        exact ⟨pre, rfl, by rw [Job.rel, denote_star]; exact hd⟩
      | plus g =>
        simp only [run] at h
        split at h
        · simp at h
        · next a₁ r₁ h₁ =>
          split at h
          · simp at h
          · next a₂ r₂ h₂ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨p₁, rfl, hd₁⟩ := ih _ _ _ _ h₁
            obtain ⟨p₂, rfl, hd₂⟩ := ih _ _ _ _ h₂
            refine ⟨p₁ ++ p₂, by simp, ?_⟩
            rw [Job.rel, denote_plus]
            exact ⟨p₁, a₁, p₂, a₂, hd₁, hd₂, rfl, rfl⟩
      | opt g =>
        simp only [run] at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨[], rfl, by rw [Job.rel, denote_opt]; exact Or.inl ⟨rfl, rfl⟩⟩
        · next a₁ r₁ h₁ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨p₁, rfl, hd₁⟩ := ih _ _ _ _ h₁
          exact ⟨p₁, rfl, by rw [Job.rel, denote_opt]; exact Or.inr hd₁⟩
      | count g k =>
        simp only [run] at h
        obtain ⟨pre, rfl, hd⟩ := ih _ _ _ _ h
        exact ⟨pre, rfl, by rw [Job.rel, denote_count]; exact hd⟩
      | attr f g =>
        simp only [run] at h
        split at h
        · simp at h
        · next a₁ r₁ h₁ =>
          split at h
          · simp at h
          · next b hb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨p₁, rfl, hd₁⟩ := ih _ _ _ _ h₁
            exact ⟨p₁, rfl, by rw [Job.rel, denote_attr]; exact ⟨a₁, hd₁, hb⟩⟩
    | seq gs =>
      cases gs with
      | nil =>
        simp only [run, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, ⟨rfl, rfl⟩⟩
      | cons g gs =>
        simp only [run] at h
        split at h
        · simp at h
        · next a₁ r₁ h₁ =>
          split at h
          · simp at h
          · next a₂ r₂ h₂ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨p₁, rfl, hd₁⟩ := ih _ _ _ _ h₁
            obtain ⟨p₂, rfl, hd₂⟩ := ih _ _ _ _ h₂
            exact ⟨p₁ ++ p₂, by simp, ⟨p₁, a₁, p₂, a₂, hd₁, hd₂, rfl, rfl⟩⟩
    | alt gs =>
      cases gs with
      | nil => simp [run] at h
      | cons g gs =>
        simp only [run] at h
        split at h
        · next a₁ r₁ h₁ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨p₁, rfl, hd₁⟩ := ih _ _ _ _ h₁
          refine ⟨p₁, rfl, supList_apply.mpr ⟨denote G g, ?_, hd₁⟩⟩
          exact List.mem_map.mpr ⟨g, List.mem_cons_self .., rfl⟩
        · next h₁ =>
          obtain ⟨p₁, rfl, hd₁⟩ := ih _ _ _ _ h
          obtain ⟨E, hE, hv⟩ := supList_apply.mp hd₁
          obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hE
          refine ⟨p₁, rfl, supList_apply.mpr ⟨denote G g', ?_, hv⟩⟩
          exact List.mem_map.mpr ⟨g', List.mem_cons_of_mem g hg', rfl⟩
    | star g =>
      simp only [run] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, kleene_apply.mpr ⟨0, rfl, rfl⟩⟩
      · next a₁ r₁ h₁ =>
        split at h
        · split at h
          · simp at h
          · next a₂ r₂ h₂ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨p₁, rfl, hd₁⟩ := ih _ _ _ _ h₁
            obtain ⟨p₂, rfl, hd₂⟩ := ih _ _ _ _ h₂
            obtain ⟨k, hk⟩ := kleene_apply.mp hd₂
            exact ⟨p₁ ++ p₂, by simp,
              kleene_apply.mpr ⟨k + 1, ⟨p₁, a₁, p₂, a₂, hd₁, hk, rfl, rfl⟩⟩⟩
        · simp at h
    | count g k =>
      cases k with
      | zero =>
        simp only [run, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, ⟨rfl, rfl⟩⟩
      | succ k =>
        simp only [run] at h
        split at h
        · simp at h
        · next a₁ r₁ h₁ =>
          split at h
          · simp at h
          · next a₂ r₂ h₂ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨p₁, rfl, hd₁⟩ := ih _ _ _ _ h₁
            obtain ⟨p₂, rfl, hd₂⟩ := ih _ _ _ _ h₂
            exact ⟨p₁ ++ p₂, by simp, ⟨p₁, a₁, p₂, a₂, hd₁, hd₂, rfl, rfl⟩⟩

/-- **Soundness of `decode`.**  A successful decode consumes a prefix and
derives it. -/
theorem decode_sound (G : Gram N α) {n : Nat} {g : Sym N α} {bs : Bytes} {a : α}
    {rest : Bytes} (h : decode G n g bs = some (a, rest)) :
    ∃ pre, bs = pre ++ rest ∧ denote G g pre a :=
  run_sound G n (.sym g) bs a rest h

/-- The `List.take`/`List.drop` restatement of `decode_sound`, in the form the
task statement asks for: the consumed prefix is the first
`bs.length - rest.length` bytes, and `rest` is what follows them. -/
theorem decode_sound_take (G : Gram N α) {n : Nat} {g : Sym N α} {bs : Bytes} {a : α}
    {rest : Bytes} (h : decode G n g bs = some (a, rest)) :
    denote G g (bs.take (bs.length - rest.length)) a ∧
      rest = bs.drop (bs.length - rest.length) := by
  obtain ⟨pre, rfl, hd⟩ := decode_sound G h
  have hlen : (pre ++ rest).length - rest.length = pre.length := by simp
  rw [hlen, List.take_left, List.drop_left]
  exact ⟨hd, rfl⟩

/-! ## The deterministic subclass

`decode` guesses in exactly three places: which branch of an `alt` (hence which
production of a nonterminal) to take, and whether to iterate once more in a
`star`, `plus` or `opt`.  `detSym` rules out the second kind outright and
discharges the first with `Basic.lean`'s decidable `altSeparated`.
-/

mutual

/-- The symbols a recursive-descent decoder handles: every `alt` has branches
with disjoint leading byte ranges, and no unbounded or optional iteration
occurs.  `count g k` is allowed — a fixed repetition count is not a choice.

This does not descend through `nt`; the condition on nonterminals is `Det`. -/
def detSym : Sym N α → Bool
  | .eps => true
  | .byte _ => true
  | .range _ _ => true
  | .bytes _ => true
  | .nt _ => true
  | .seq gs => detSymList gs
  | .alt gs => altSeparated gs && detSymList gs
  | .star _ => false
  | .plus _ => false
  | .opt _ => false
  | .count g _ => detSym g
  | .attr _ g => detSym g

/-- `detSym` on every member of a list. -/
def detSymList : List (Sym N α) → Bool
  | [] => true
  | g :: gs => detSym g && detSymList gs

end

/-- `detSymList` is `detSym` on every member. -/
theorem detSymList_iff {gs : List (Sym N α)} :
    detSymList gs = true ↔ ∀ g ∈ gs, detSym g = true := by
  induction gs with
  | nil => simp [detSymList]
  | cons g gs ih => simp [detSymList, ih]

/-- A nonterminal is always in `detSym`: the condition on what it expands to
lives in `Det`, not in `detSym`. -/
theorem detSym_nt (x : N) : detSym (Sym.nt x : Sym N α) = true := rfl

/-- **Prefix-determinism.**  A grammar a recursive-descent decoder handles: the
productions of every nonterminal have pairwise disjoint leading byte ranges,
and every production is in `detSym`.

No separate left-recursion check appears, and none is needed: `altSeparated`
forces `leadRange? g = some _` for every production `g`
(`Basic.altSeparated_leadRange`), and `leadRange?` answers `none` for `nt` and
for any `seq` headed by one, so every production begins with a byte terminal
and consumes a byte before reaching a nonterminal.  `Det.nonNullable_nt` is
that argument. -/
structure Det (G : Gram N α) : Prop where
  /-- The productions of each nonterminal have disjoint leading byte ranges. -/
  sep : ∀ x : N, altSeparated (G.prods x) = true
  /-- Every production is in `detSym`. -/
  det : ∀ x : N, detSymList (G.prods x) = true

/-- Productivity comes for free: under `Det` no nonterminal derives the empty
byte string, so no production can re-enter its own nonterminal without
consuming a byte first.  This is the no-left-recursion condition, obtained from
the separation condition rather than from a reachability computation. -/
theorem Det.nonNullable_nt {G : Gram N α} (hG : Det G) (x : N) :
    NonNullable (denote G (.nt x)) := by
  intro a ha
  rw [denote_nt] at ha
  obtain ⟨E, hE, hv⟩ := supList_apply.mp ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hE
  obtain ⟨p, hp⟩ := altSeparated_leadRange (hG.sep x) hg
  exact nonNullable_of_leadRange G hp a hv

/-- `Det` is a `Bool` check against an explicit list of nonterminals.

An explicit list rather than `[Fintype N]`: the LEB128 instance below has
`N = Nat` — the bit widths — and SpecTec's own nonterminals are a grammar
identifier paired with an argument list (`spectec/src/il/ast.ml:102`), neither
of which is a `Fintype`.  What matters is that the nonterminals *reachable*
from the start symbol are finitely many and can be listed. -/
def detGram (G : Gram N α) (ns : List N) : Bool :=
  ns.all fun x => altSeparated (G.prods x) && detSymList (G.prods x)

/-- `detGram` decides `Det` once the list exhausts the nonterminals. -/
theorem det_of_detGram {G : Gram N α} {ns : List N} (hns : ∀ x : N, x ∈ ns)
    (h : detGram G ns = true) : Det G := by
  simp only [detGram, List.all_eq_true, Bool.and_eq_true] at h
  exact ⟨fun x => (h x (hns x)).1, fun x => (h x (hns x)).2⟩

/-- For a nonterminal type that really is finite, `Det` is decidable outright. -/
instance Det.instDecidable [Fintype N] (G : Gram N α) : Decidable (Det G) :=
  decidable_of_iff
    (∀ x : N, altSeparated (G.prods x) = true ∧ detSymList (G.prods x) = true)
    ⟨fun h => ⟨fun x => (h x).1, fun x => (h x).2⟩, fun h x => ⟨h.sep x, h.det x⟩⟩

/-- `detSym`, transported to jobs: a `star` job is never deterministic, and an
`alt` job carries the separation condition its branches need. -/
def detJob : Job N α → Bool
  | .sym g => detSym g
  | .seq gs => detSymList gs
  | .alt gs => altSeparated gs && detSymList gs
  | .star _ => false
  | .count g _ => detSym g

/-! ## The separation argument

The one place where `Det` does real work: under `altSeparated (g :: gs)`, if
some later branch parses the input then `g` cannot parse it at *any* fuel.
This is what makes the first-match-wins `alt` clause both fuel-monotone and
complete.
-/

/-- If a later alternative decodes the input, the head alternative fails on it,
at every fuel.  Proved from unconditional soundness plus disjoint leading byte
ranges: both parses would have to begin at the first byte of `bs`. -/
theorem run_alt_cons_head_none (G : Gram N α) {g : Sym N α} {gs : List (Sym N α)}
    (hsep : altSeparated (g :: gs) = true) {bs : Bytes} {n : Nat} {r : α × Bytes}
    (hn : run G n (.alt gs) bs = some r) (m : Nat) : run G m (.sym g) bs = none := by
  rcases hm : run G m (.sym g) bs with _ | ⟨a', rest'⟩
  · rfl
  · exfalso
    obtain ⟨p', hb', hd'⟩ := run_sound G m _ _ _ _ hm
    obtain ⟨p'', hb'', hd''⟩ := run_sound G n _ _ _ _ hn
    obtain ⟨E, hE, hv⟩ := supList_apply.mp hd''
    obtain ⟨g₂, hg₂, rfl⟩ := List.mem_map.mp hE
    obtain ⟨pg, hpg⟩ := altSeparated_leadRange hsep (List.mem_cons_self ..)
    obtain ⟨pg₂, hpg₂⟩ :=
      altSeparated_leadRange hsep (List.mem_cons_of_mem g hg₂)
    obtain ⟨b', t', rfl, -, -⟩ := leadRange?_sound G hpg hd'
    obtain ⟨b'', t'', rfl, -, -⟩ := leadRange?_sound G hpg₂ hv
    have hbb : b' = b'' := by
      rw [hb''] at hb'
      simp only [List.cons_append, List.cons.injEq] at hb'
      exact hb'.1.symm
    have hsepa := (List.pairwise_cons.mp (altSeparated_pairwise G hsep)).1 g₂ hg₂
    exact hsepa hd' hv (by simp [hbb])

/-! ## Fuel monotonicity -/

/-- **Monotonicity in the fuel.**  On the deterministic class, a successful
decode stays successful, with the same answer, when given more fuel.

`Det` is genuinely needed, and not only for termination: at an `alt`, a branch
that failed for want of fuel could succeed with more fuel and steal the parse
from a later branch.  Separation is what rules that out, via
`run_alt_cons_head_none`. -/
theorem run_mono (G : Gram N α) (hG : Det G) :
    ∀ (n : Nat) (j : Job N α) (bs : Bytes) (r : α × Bytes) (m : Nat),
      detJob j = true → n ≤ m → run G n j bs = some r → run G m j bs = some r := by
  intro n
  induction n with
  | zero => intro j bs r m _ _ h; simp at h
  | succ n ih =>
    intro j bs r m hj hnm h
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hnm' : n ≤ m := by omega
    cases j with
    | sym g =>
      cases g with
      | eps => simpa only [run] using h
      | byte b =>
        cases bs with
        | nil => simp [run] at h
        | cons c r' => simpa only [run] using h
      | range lo hi =>
        cases bs with
        | nil => simp [run] at h
        | cons c r' => simpa only [run] using h
      | bytes l => simpa only [run] using h
      | nt x =>
        have hd : detJob (Job.alt (G.prods x)) = true := by
          simp [detJob, hG.sep x, hG.det x]
        simp only [run] at h ⊢
        exact ih _ _ _ _ hd hnm' h
      | seq gs =>
        have hd : detJob (Job.seq gs) = true := by simpa [detJob, detSym] using hj
        simp only [run] at h ⊢
        exact ih _ _ _ _ hd hnm' h
      | alt gs =>
        have hd : detJob (Job.alt gs) = true := by simpa [detJob, detSym] using hj
        simp only [run] at h ⊢
        exact ih _ _ _ _ hd hnm' h
      | star g => simp [detJob, detSym] at hj
      | plus g => simp [detJob, detSym] at hj
      | opt g => simp [detJob, detSym] at hj
      | count g k =>
        have hd : detJob (Job.count g k) = true := by simpa [detJob, detSym] using hj
        simp only [run] at h ⊢
        exact ih _ _ _ _ hd hnm' h
      | attr f g =>
        have hd : detJob (Job.sym g) = true := by simpa [detJob, detSym] using hj
        simp only [run] at h ⊢
        split at h
        · simp at h
        · next a₁ r₁ h₁ =>
          simp only [ih _ _ _ _ hd hnm' h₁]
          exact h
    | seq gs =>
      cases gs with
      | nil => simpa only [run] using h
      | cons g gs =>
        simp only [detJob, detSymList, Bool.and_eq_true] at hj
        have hd₁ : detJob (Job.sym g) = true := hj.1
        have hd₂ : detJob (Job.seq gs) = true := hj.2
        simp only [run] at h ⊢
        split at h
        · simp at h
        · next a₁ r₁ h₁ =>
          split at h
          · simp at h
          · next a₂ r₂ h₂ =>
            simp only [ih _ _ _ _ hd₁ hnm' h₁, ih _ _ _ _ hd₂ hnm' h₂]
            exact h
    | alt gs =>
      cases gs with
      | nil => simp [run] at h
      | cons g gs =>
        simp only [detJob, detSymList, altSeparated, Bool.and_eq_true] at hj
        obtain ⟨hsep0, hdg, hdgs⟩ := hj
        have hsep : altSeparated (g :: gs) = true := by
          simp only [altSeparated, Bool.and_eq_true]
          exact ⟨hsep0.1, hsep0.2⟩
        have hd₁ : detJob (Job.sym g) = true := hdg
        have hd₂ : detJob (Job.alt gs) = true := by
          simp [detJob, hsep0.2, hdgs]
        simp only [run] at h ⊢
        split at h
        · next a₁ r₁ h₁ =>
          simp only [ih _ _ _ _ hd₁ hnm' h₁]
          exact h
        · next h₁ =>
          have hnone := run_alt_cons_head_none G hsep h m
          simp only [hnone]
          exact ih _ _ _ _ hd₂ hnm' h
    | star g => simp [detJob] at hj
    | count g k =>
      cases k with
      | zero => simpa only [run] using h
      | succ k =>
        have hd₁ : detJob (Job.sym g) = true := hj
        have hd₂ : detJob (Job.count g k) = true := hj
        simp only [run] at h ⊢
        split at h
        · simp at h
        · next a₁ r₁ h₁ =>
          split at h
          · simp at h
          · next a₂ r₂ h₂ =>
            simp only [ih _ _ _ _ hd₁ hnm' h₁, ih _ _ _ _ hd₂ hnm' h₂]
            exact h

/-- Monotonicity in the fuel, for `decode`. -/
theorem decode_mono (G : Gram N α) (hG : Det G) {n m : Nat} {g : Sym N α} {bs : Bytes}
    {r : α × Bytes} (hg : detSym g = true) (hnm : n ≤ m)
    (h : decode G n g bs = some r) : decode G m g bs = some r :=
  run_mono G hG n (.sym g) bs r m hg hnm h

/-! ## Completeness

Every derivation is found, for *any* continuation: `decode G f g (pre ++ rest)`
returns `(a, rest)` whenever `denote G g pre a`.  Quantifying over the
continuation is what makes the `seq` case go through with no extra hypothesis —
the factors of a concatenation are decoded against the rest of the input, and
the induction hypothesis already says the right thing about them.

The induction is on the derivation *depth* (`denoteAt`'s index), with an inner
induction on the list of alternatives or factors; `Job.relAt` is `Job.rel` at a
fixed depth.
-/

/-- `Job.rel` at a bounded derivation depth. -/
def Job.relAt (G : Gram N α) (n : Nat) : Job N α → EncRel Bytes α
  | .sym g => denoteAt G n g
  | .seq gs => appendAll G.alg (gs.map (denoteAt G n))
  | .alt gs => supList (gs.map (denoteAt G n))
  | .star g => kleene G.alg (denoteAt G n g)
  | .count g k => powRel G.alg (denoteAt G n g) k

/-- **Completeness at a bounded depth.**  On the deterministic class, a
derivation of depth below `n` is found by `run` with enough fuel, leaving the
continuation untouched. -/
theorem run_complete_at (G : Gram N α) (hG : Det G) :
    ∀ (n : Nat) (j : Job N α), detJob j = true → ∀ (pre rest : Bytes) (a : α),
      j.relAt G n pre a → ∃ f, run G f j (pre ++ rest) = some (a, rest) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n Pn =>
    have hsym : ∀ g : Sym N α, detSym g = true → ∀ (pre rest : Bytes) (a : α),
        denoteAt G n g pre a → ∃ f, run G f (.sym g) (pre ++ rest) = some (a, rest) := by
      intro g hg pre rest a hd
      cases n with
      | zero => exact absurd hd (by simp)
      | succ m =>
        cases g with
        | eps =>
          obtain ⟨rfl, rfl⟩ := hd
          exact ⟨1, rfl⟩
        | byte b =>
          obtain ⟨rfl, rfl⟩ := hd
          exact ⟨1, by simp [run]⟩
        | range lo hi =>
          obtain ⟨c, hlo, hhi, rfl, rfl⟩ := hd
          exact ⟨1, by simp [run, hlo, hhi]⟩
        | bytes l =>
          obtain ⟨rfl, rfl⟩ := hd
          exact ⟨1, by simp [run]⟩
        | nt x =>
          have hdj : detJob (Job.alt (G.prods x)) = true := by
            simp [detJob, hG.sep x, hG.det x]
          obtain ⟨f, hf⟩ := Pn m (by omega) (.alt (G.prods x)) hdj pre rest a hd
          exact ⟨f + 1, hf⟩
        | seq gs =>
          have hdj : detJob (Job.seq gs) = true := by simpa [detJob, detSym] using hg
          obtain ⟨f, hf⟩ := Pn m (by omega) (.seq gs) hdj pre rest a hd
          exact ⟨f + 1, hf⟩
        | alt gs =>
          have hdj : detJob (Job.alt gs) = true := by simpa [detJob, detSym] using hg
          obtain ⟨f, hf⟩ := Pn m (by omega) (.alt gs) hdj pre rest a hd
          exact ⟨f + 1, hf⟩
        | star g => simp [detSym] at hg
        | plus g => simp [detSym] at hg
        | opt g => simp [detSym] at hg
        | count g k =>
          have hdj : detJob (Job.count g k) = true := by simpa [detJob, detSym] using hg
          obtain ⟨f, hf⟩ := Pn m (by omega) (.count g k) hdj pre rest a hd
          exact ⟨f + 1, hf⟩
        | attr f g =>
          obtain ⟨a', hd', hfa⟩ := hd
          have hdj : detJob (Job.sym g) = true := by simpa [detJob, detSym] using hg
          obtain ⟨f₀, hf₀⟩ := Pn m (by omega) (.sym g) hdj pre rest a' hd'
          exact ⟨f₀ + 1, by simp only [run, hf₀, hfa]⟩
    have hseq : ∀ gs : List (Sym N α), detSymList gs = true →
        ∀ (pre rest : Bytes) (a : α), appendAll G.alg (gs.map (denoteAt G n)) pre a →
        ∃ f, run G f (.seq gs) (pre ++ rest) = some (a, rest) := by
      intro gs
      induction gs with
      | nil =>
        intro _ pre rest a hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨1, rfl⟩
      | cons g gs ihs =>
        intro hdet pre rest a hd
        simp only [detSymList, Bool.and_eq_true] at hdet
        obtain ⟨p₁, a₁, p₂, a₂, h₁, h₂, rfl, rfl⟩ := hd
        obtain ⟨f₁, hf₁⟩ := hsym g hdet.1 p₁ (p₂ ++ rest) a₁ h₁
        obtain ⟨f₂, hf₂⟩ := ihs hdet.2 p₂ rest a₂ h₂
        have e₁ := run_mono G hG f₁ (.sym g) (p₁ ++ (p₂ ++ rest)) _ (max f₁ f₂)
          hdet.1 (le_max_left _ _) hf₁
        have e₂ := run_mono G hG f₂ (.seq gs) (p₂ ++ rest) _ (max f₁ f₂)
          hdet.2 (le_max_right _ _) hf₂
        refine ⟨max f₁ f₂ + 1, ?_⟩
        rw [List.append_assoc]
        simp only [run, e₁, e₂]
    have halt : ∀ gs : List (Sym N α), altSeparated gs = true → detSymList gs = true →
        ∀ (pre rest : Bytes) (a : α), supList (gs.map (denoteAt G n)) pre a →
        ∃ f, run G f (.alt gs) (pre ++ rest) = some (a, rest) := by
      intro gs
      induction gs with
      | nil =>
        intro _ _ pre rest a hd
        exact absurd hd (by simp)
      | cons g gs ihs =>
        intro hsep hdet pre rest a hd
        simp only [detSymList, Bool.and_eq_true] at hdet
        simp only [List.map_cons, supList, EncRel.sup_apply] at hd
        have hsep' : altSeparated gs = true := by
          simp only [altSeparated, Bool.and_eq_true] at hsep
          exact hsep.2
        rcases hd with hd | hd
        · obtain ⟨f, hf⟩ := hsym g hdet.1 pre rest a hd
          exact ⟨f + 1, by simp only [run, hf]⟩
        · obtain ⟨f, hf⟩ := ihs hsep' hdet.2 pre rest a hd
          have hnone := run_alt_cons_head_none G hsep hf f
          exact ⟨f + 1, by simp only [run, hnone, hf]⟩
    have hcount : ∀ (g : Sym N α) (k : Nat), detSym g = true →
        ∀ (pre rest : Bytes) (a : α), powRel G.alg (denoteAt G n g) k pre a →
        ∃ f, run G f (.count g k) (pre ++ rest) = some (a, rest) := by
      intro g k hg
      induction k with
      | zero =>
        intro pre rest a hd
        obtain ⟨rfl, rfl⟩ := hd
        exact ⟨1, rfl⟩
      | succ k ihk =>
        intro pre rest a hd
        obtain ⟨p₁, a₁, p₂, a₂, h₁, h₂, rfl, rfl⟩ := hd
        obtain ⟨f₁, hf₁⟩ := hsym g hg p₁ (p₂ ++ rest) a₁ h₁
        obtain ⟨f₂, hf₂⟩ := ihk p₂ rest a₂ h₂
        have e₁ := run_mono G hG f₁ (.sym g) (p₁ ++ (p₂ ++ rest)) _ (max f₁ f₂)
          hg (le_max_left _ _) hf₁
        have e₂ := run_mono G hG f₂ (.count g k) (p₂ ++ rest) _ (max f₁ f₂)
          hg (le_max_right _ _) hf₂
        refine ⟨max f₁ f₂ + 1, ?_⟩
        rw [List.append_assoc]
        simp only [run, e₁, e₂]
    intro j hj pre rest a hd
    cases j with
    | sym g => exact hsym g hj pre rest a hd
    | seq gs => exact hseq gs hj pre rest a hd
    | alt gs =>
      simp only [detJob, Bool.and_eq_true] at hj
      exact halt gs hj.1 hj.2 pre rest a hd
    | star g => simp [detJob] at hj
    | count g k => exact hcount g k hj pre rest a hd

/-- **Completeness.**  On the deterministic class, every derivation is decoded,
whatever follows it in the input. -/
theorem run_complete (G : Gram N α) (hG : Det G) {j : Job N α} (hj : detJob j = true)
    {pre rest : Bytes} {a : α} (hd : j.rel G pre a) :
    ∃ f, run G f j (pre ++ rest) = some (a, rest) := by
  have key : ∃ n, j.relAt G n pre a := by
    cases j with
    | sym g => exact denote_apply.mp hd
    | seq gs => exact exists_index_appendAll G gs hd
    | alt gs => exact exists_index_supList G gs hd
    | star g => exact exists_index_kleene G g hd
    | count g k => exact exists_index_powRel G g k hd
  obtain ⟨n, hn⟩ := key
  exact run_complete_at G hG n j hj pre rest a hn

/-- **Completeness of `decode`**: `denote G g pre a` implies
`decode G f g (pre ++ rest) = some (a, rest)` for all large enough `f`. -/
theorem decode_complete (G : Gram N α) (hG : Det G) {g : Sym N α} (hg : detSym g = true)
    {pre rest : Bytes} {a : α} (hd : denote G g pre a) :
    ∃ f, decode G f g (pre ++ rest) = some (a, rest) :=
  run_complete G hG (j := .sym g) hg hd

/-- The decoder as a decision procedure: with enough fuel, `decode` succeeds on
`pre ++ rest` with answer `(a, rest)` exactly when `denote` derives `a` from
`pre`.  Soundness supplies `→` at every fuel, completeness `←` at some. -/
theorem decode_eq_some_iff (G : Gram N α) (hG : Det G) {g : Sym N α}
    (hg : detSym g = true) (pre rest : Bytes) (a : α) :
    (∃ f, decode G f g (pre ++ rest) = some (a, rest)) ↔ denote G g pre a := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨pre', he, hd⟩ := decode_sound G hf
    rw [List.append_cancel_right he]
    exact hd
  · exact decode_complete G hG hg

/-! ### Greedy iteration at the end of the input

`star` is outside `Det` because greedy iteration is complete only against a
FOLLOW condition, which `leadRange?` cannot supply.  There is one case that
needs no FOLLOW set at all: a `star` with nothing after it.  The body's leading
byte range certifies non-nullability, and the decoder stops because there is no
byte left for another iteration.
-/

/-- Greedy iteration is complete at the end of the input: if the body has a
known leading byte range (hence derives no empty string) and is itself in the
deterministic class, a `star` job consuming the whole remaining input is found.

The conclusion is `∀ f ≥ f₀` rather than `∃ f`: `star` is outside `detJob`, so
`run_mono` does not apply to a `star` job, and the fuels of the iterations have
to be aligned inside the induction instead. -/
theorem run_star_complete_eof (G : Gram N α) (hG : Det G) {g : Sym N α}
    (hg : detSym g = true) {p : UInt8 × UInt8} (hp : leadRange? g = some p) :
    ∀ (k : Nat) (pre : Bytes) (a : α), powRel G.alg (denote G g) k pre a →
      ∃ f₀, ∀ f, f₀ ≤ f → run G f (.star g) pre = some (a, []) := by
  have hnn : NonNullable (denote G g) := nonNullable_of_leadRange G hp
  have hnil : ∀ f : Nat, run G f (.sym g) [] = none := by
    intro f
    rcases hf : run G f (.sym g) [] with _ | ⟨a', rest'⟩
    · rfl
    · obtain ⟨p', he, hd'⟩ := run_sound G f _ _ _ _ hf
      have hp' : p' = [] := (List.append_eq_nil_iff.mp he.symm).1
      exact absurd (hp' ▸ hd') (hnn a')
  intro k
  induction k with
  | zero =>
    intro pre a hk
    obtain ⟨rfl, rfl⟩ := hk
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := ⟨f - 1, by omega⟩
    simp only [run, hnil F]
  | succ k ihk =>
    intro pre a hk
    obtain ⟨p₁, a₁, p₂, a₂, h₁, h₂, rfl, rfl⟩ := hk
    obtain ⟨f₁, hf₁⟩ := decode_complete G hG hg (rest := p₂) h₁
    obtain ⟨f₂, hf₂⟩ := ihk p₂ a₂ h₂
    have hlen : p₂.length < (p₁ ++ p₂).length := by
      cases p₁ with
      | nil => exact absurd h₁ (hnn a₁)
      | cons b t =>
        simp only [List.cons_append, List.length_cons, List.length_append]
        omega
    refine ⟨max f₁ f₂ + 1, fun f hf => ?_⟩
    obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := ⟨f - 1, by omega⟩
    have e₁ := run_mono G hG f₁ (.sym g) (p₁ ++ p₂) _ F hg
      (le_trans (le_max_left f₁ f₂) (by omega)) hf₁
    have e₂ := hf₂ F (le_trans (le_max_right f₁ f₂) (by omega))
    simp only [run, e₁, hlen, ite_true, e₂]

/-- `decode` at a `star` with nothing after it: the greedy decoder finds every
derivation of the whole input. -/
theorem decode_star_complete_eof (G : Gram N α) (hG : Det G) {g : Sym N α}
    (hg : detSym g = true) {p : UInt8 × UInt8} (hp : leadRange? g = some p)
    {pre : Bytes} {a : α} (hd : denote G (.star g) pre a) :
    ∃ f₀, ∀ f, f₀ ≤ f → decode G f (.star g) pre = some (a, []) := by
  rw [denote_star] at hd
  obtain ⟨k, hk⟩ := kleene_apply.mp hd
  obtain ⟨f₀, hf₀⟩ := run_star_complete_eof G hG hg hp k pre a hk
  refine ⟨f₀ + 1, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F, f = F + 1 := ⟨f - 1, by omega⟩
  simpa only [decode, run] using hf₀ F (by omega)

/-! ## Encoding

An *encoder* is a right inverse of the decoder: `enc a = some bs` should mean
"`bs` spells `a`".  That is `Encodes` below, and the content of this section is
that on the deterministic class `Encodes G g a bs` and `denote G g bs a` are
the same statement — so an encoder is correct as soon as its output decodes
back, and it is total exactly on the image of the denotation.

There is no *generic* way to compute one.  `Sym.attr` carries its action as an
arbitrary `f : α → Option α` (`Basic.lean`'s design choice), and nothing
inverts an arbitrary partial function; `encodeOf` is therefore the classical
choice of a spelling, with `encodeOf_isSome_iff` saying precisely when it is
defined.  A grammar that wants a *computable* encoder must supply inverses for
its actions, and `encoder_sound` is then the only proof obligation.  The
LEB128 section below is the worked case: `Wasm.Binary.UN.exists_of_lt` supplies
the spellings, and the side condition `m < 2 ^ W` is exactly totality.
-/

/-- `bs` encodes `a` for `g`: the decoder consumes all of `bs` and returns `a`. -/
def Encodes (G : Gram N α) (g : Sym N α) (a : α) (bs : Bytes) : Prop :=
  ∃ f, decode G f g bs = some (a, [])

/-- Unconditionally, an encoding is a derivation: this is `decode_sound` with
an empty remainder, and it is the correctness half of any encoder. -/
theorem denote_of_encodes (G : Gram N α) {g : Sym N α} {a : α} {bs : Bytes}
    (h : Encodes G g a bs) : denote G g bs a := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨pre, he, hd⟩ := decode_sound G hf
  rw [List.append_nil] at he
  rw [he]
  exact hd

/-- On the deterministic class, "encodes" and "derives" coincide. -/
theorem encodes_iff_denote (G : Gram N α) (hG : Det G) {g : Sym N α}
    (hg : detSym g = true) (a : α) (bs : Bytes) :
    Encodes G g a bs ↔ denote G g bs a := by
  constructor
  · exact denote_of_encodes G
  · intro hd
    have h := decode_complete G hG hg (pre := bs) (rest := []) hd
    simpa [Encodes] using h

/-- **Encoder correctness.**  Any `enc` whose output the decoder accepts is a
sound partial encoder for the denotation, in the sense of
`Silmaril/Encoding/Relation.lean`.  No hypothesis on the grammar: this is
soundness of the decoder. -/
theorem encoder_sound (G : Gram N α) {g : Sym N α} {enc : α → Option Bytes}
    (h : ∀ a bs, enc a = some bs → Encodes G g a bs) :
    (denote G g).PartialEncoderSound enc :=
  fun a bs he => denote_of_encodes G (h a bs he)

open Classical in
/-- The canonical encoder: *a* spelling of `a`, chosen classically.  It is the
only encoder available generically, because `Sym.attr` carries an arbitrary
partial function and nothing inverts one. -/
noncomputable def encodeOf (G : Gram N α) (g : Sym N α) (a : α) : Option Bytes :=
  if h : ∃ bs, denote G g bs a then some h.choose else none

/-- `encodeOf` is defined exactly on the attributes the grammar can spell: this
is the totality criterion. -/
theorem encodeOf_isSome_iff (G : Gram N α) (g : Sym N α) (a : α) :
    (encodeOf G g a).isSome = true ↔ ∃ bs, denote G g bs a := by
  unfold encodeOf
  split
  · next hx => simpa using hx
  · next hx => simpa using hx

/-- `encodeOf` is correct where it is defined. -/
theorem encodeOf_sound (G : Gram N α) (g : Sym N α) :
    (denote G g).PartialEncoderSound (encodeOf G g) := by
  intro a bs h
  unfold encodeOf at h
  split at h
  · next hx =>
    have hb : hx.choose = bs := Option.some.inj h
    rw [← hb]
    exact hx.choose_spec
  · exact absurd h (by simp)

/-- `encodeOf` is total exactly when the denotation is `EncRel.Total`, i.e.
when every attribute has a spelling. -/
theorem encodeOf_total (G : Gram N α) (g : Sym N α) (h : (denote G g).Total) (a : α) :
    (encodeOf G g a).isSome = true :=
  (encodeOf_isSome_iff G g a).mpr (h a)

/-- On the deterministic class the decoder recovers whatever `encodeOf`
produces: the round trip closes. -/
theorem encodes_encodeOf (G : Gram N α) (hG : Det G) {g : Sym N α}
    (hg : detSym g = true) {a : α} {bs : Bytes} (h : encodeOf G g a = some bs) :
    Encodes G g a bs :=
  (encodes_iff_denote G hG hg a bs).mpr (encodeOf_sound G g a bs h)

/-! ## LEB128, the worked instance

`Basic.lean` builds `lebGram` for `BuN(N)` (`5.1-binary.values.spectec:9-11`)
and proves `denote_leb_nt_iff : denote lebGram (.nt W) bs [m] ↔ Wasm.Binary.UN W bs m`.
Here that grammar is shown to be in the deterministic class, so the *generic*
decoder of this file decodes it — and decodes exactly what the hand-written
`Silmaril.Wasm.Binary.RefInterp.refUN` decodes.

### How this relates to the existing LEB128 decoders

`Silmaril/Wasm/Binary/` has one: `RefInterp.refUN`, a direct transcription of
the reference interpreter's `uN n s` (`interpreter/binary/decode.ml:85-90`),
proved to accept exactly `UN N` by `RefInterp.refUN_eq_some_iff`.  It is a
hand-written recursive function over the byte list, specific to LEB128, with
its own correctness proof.

`decode lebGram` is the opposite: a single decoder, written once for *all*
grammars, proved sound and complete once, and *instantiated* at LEB128 by
checking a `Bool` (`det_lebGram`).  `decode_leb_iff_refUN` is the bridge — the
two agree on acceptance, on the value, and on the leftover bytes.  Neither
subsumes the other: `refUN` is the executable one (no fuel, linear in the
input, and it is what the conformance runner uses), while `decode lebGram` is
evidence that the generic machinery is strong enough to reproduce it, and is
what a SpecTec `GramD` will be decoded by once `Sem/Grammar.lean` maps the IL's
grammars into this framework.
-/

section Leb

open Silmaril.Wasm.Binary
open Silmaril.Wasm.Binary.RefInterp

/-- Both productions of `BuN(W)` are in `detSym`: no iteration occurs, and the
only `alt` is the production list itself. -/
theorem detSymList_lebProds (W : Nat) : detSymList (lebProds W) = true := by
  by_cases h : 7 < W <;>
    simp [lebProds, lebP1, lebP2, detSym, detSymList, h]

/-- **`lebGram` is prefix-deterministic.**  The two components are
`Basic.altSeparated_lebProds` — the continuation bit separates the two
productions — and `detSymList_lebProds`. -/
theorem det_lebGram : Det lebGram :=
  ⟨altSeparated_lebProds, detSymList_lebProds⟩

/-- **The generic decoder decodes `BuN(W)`.**  Run on `Basic.lebGram`, it
accepts exactly the byte strings of `Silmaril.Wasm.Binary.UN W`, with the same
value, leaving whatever follows them untouched. -/
theorem decode_leb_iff (W : Nat) (bs rest : Bytes) (m : Nat) :
    (∃ f, decode lebGram f (.nt W) (bs ++ rest) = some ([m], rest)) ↔ UN W bs m := by
  rw [decode_eq_some_iff lebGram det_lebGram (detSym_nt W)]
  exact denote_leb_nt_iff W bs m

/-- **The generic decoder is the hand-written one.**  For every width `W > 0`,
`decode lebGram (.nt W)` and `Silmaril.Wasm.Binary.RefInterp.refUN W` succeed on
exactly the same inputs, with the same value and the same leftover bytes.  This
is the point of the exercise: a decoder derived from a grammar, agreeing with a
transcription of `interpreter/binary/decode.ml:85-90`. -/
theorem decode_leb_iff_refUN {W : Nat} (hW : 0 < W) (bs r : Bytes) (m : Nat) :
    (∃ f, decode lebGram f (.nt W) bs = some ([m], r)) ↔ refUN W bs = some (m, r) := by
  rw [refUN_eq_some_iff hW]
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨pre, rfl, hd⟩ := decode_sound lebGram hf
    exact ⟨pre, rfl, (denote_leb_nt_iff W pre m).mp hd⟩
  · rintro ⟨pre, rfl, hun⟩
    exact (decode_leb_iff W pre r m).mpr hun

/-- **Totality of the LEB128 encoder.**  Every `m < 2 ^ W` has a spelling, and
the generic decoder recovers it in front of any continuation.  The spelling
comes from `Wasm.Binary.UN.exists_of_lt`, so the side condition is exactly the
bound SpecTec's own premise `n < 2^N` imposes. -/
theorem leb_encodable {W m : Nat} (hW : 0 < W) (hm : m < 2 ^ W) :
    ∃ bs, UN W bs m ∧ ∀ rest : Bytes,
      ∃ f, decode lebGram f (.nt W) (bs ++ rest) = some ([m], rest) := by
  obtain ⟨bs, hbs⟩ := UN.exists_of_lt hW hm
  exact ⟨bs, hbs, fun rest => (decode_leb_iff W bs rest m).mpr hbs⟩

/-- `encodeOf` is total on `lebGram` for every value in range. -/
theorem encodeOf_leb_isSome {W m : Nat} (hW : 0 < W) (hm : m < 2 ^ W) :
    (encodeOf lebGram (.nt W) [m]).isSome = true := by
  obtain ⟨bs, hbs⟩ := UN.exists_of_lt hW hm
  exact (encodeOf_isSome_iff lebGram (.nt W) [m]).mpr ⟨bs, denote_leb_of_un hbs⟩

/-- The decoder reduces in the kernel: `0xE5 0x8E 0x26` is `624485` as a `u32`,
with no bytes left over.  This is the point of the explicit fuel — a
well-founded `decode` would leave this `rfl` stuck. -/
example : decode lebGram 40 (Sym.nt 32) [0xE5, 0x8E, 0x26] = some ([624485], []) := by
  rfl

/-- …and the same bytes followed by a tail leave the tail alone. -/
example : decode lebGram 40 (Sym.nt 32) [0xE5, 0x8E, 0x26, 0x0B] =
    some ([624485], [0x0B]) := by
  rfl

end Leb

end Silmaril.SpecTec.Grammar
