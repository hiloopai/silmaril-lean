module

/-!
# A generic fuzzer, mutator and shrinker API

The interface of the seeded program generators, mutators and shrinkers of the Wasm tools: the
`smith`, `mutate`, `shrink` and `wit-smith` subcommands of `wasm-tools` and the measurements of
`wasm-tools-gen-check` are instances of it (`docs/projects/wasm-components.md`). Everything is pure and
seeded: a run is a function of its seed. The header needs only Lean's core library; the reading
of a Wasm model as a language, and the instances for Wasm 1.0, 2.0, 3.0, Lime1 and WasmFX, are
`Silmaril.Wasm.Tools.Gen.Model`.

* `Rng`: SplitMix64 (Steele, Lea and Flood, OOPSLA 2014), a splittable 64-bit generator;
  `Rand := StateM Rng` with `Rand.nat`, `Rand.bool`, `Rand.pick`;
* `Lang`: syntax and validity; `DecLang`: a language with a Boolean checker equivalent to
  validity;
* `Generator L`: a seeded, sized generator whose every output is valid (`Generator.valid`);
* `Mutator L`: a seeded rewrite that preserves validity;
* `SemMutator L Eqv`: a mutator whose output is `Eqv`-equivalent to its (valid) input;
* `Shrinker L`: a size measure and a candidate list; `Shrinker.shrink p x` greedily replaces
  `x` by its first strictly smaller candidate satisfying `p`, by well-founded recursion on the
  size (so it terminates for every candidate function);
* the checked combinators `Generator.guarded`, `Mutator.guarded`, `SemMutator.guarded` turn an
  unverified raw function into a verified one by testing its output with the checker and
  falling back to a valid default (for a mutator: to the input). What they compute is
  `Generator.guardedRun` and `Mutator.guardedRun`, which take the checker as a plain function:
  an executable runs these and needs no proof;
* the byte-seeded shapes of the `wasm-tools` subcommands: `Seed`/`G` (a byte string read as a
  stream of choices), `ByteGen L` (`smith`), `PMutator L` and `PMutator.Preserving` (`mutate`,
  with `none` when no mutation applies), their checked forms `ByteGen.guarded`,
  `PMutator.guarded`, and their readings as API objects (`ByteGen.toGenerator`,
  `PMutator.toMutator`); `findM?` (the monadic search of `shrinkM`).

`Thms`: the shrinker's specification (`shrink_pred`, `shrink_size_le`, `shrink_local_min`),
the fuel-bounded monadic shrinker `shrinkM` agreeing with `shrink` (`shrinkM_id`), the guard
laws, and composition.

New definitions.
-/
@[expose] public section

namespace Silmaril.Wasm.Tools.Gen

/-! ## Randomness -/

/-- The SplitMix64 increment (the golden ratio in 64 bits). -/
def golden : UInt64 := 0x9E3779B97F4A7C15

/-- The SplitMix64 output function. -/
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- A SplitMix64 state. -/
structure Rng where
  state : UInt64
  deriving Repr, Inhabited, DecidableEq

namespace Rng

/-- The generator of a seed. -/
def ofSeed (n : Nat) : Rng := ⟨mix64 (UInt64.ofNat n)⟩

/-- The next 64-bit output and state. -/
def next (r : Rng) : UInt64 × Rng :=
  let s := r.state + golden
  (mix64 s, ⟨s⟩)

/-- Two independent generators. -/
def split (r : Rng) : Rng × Rng :=
  let (a, r') := r.next
  (⟨mix64 (a ^^^ 0x5851F42D4C957F2D)⟩, r')

end Rng

/-- Seeded computations. -/
abbrev Rand := StateM Rng

namespace Rand

/-- A number below `n` (`0` when `n = 0`). -/
def nat (n : Nat) : Rand Nat := fun r =>
  let (x, r') := r.next
  (if n = 0 then 0 else x.toNat % n, r')

/-- A number in `[lo, hi]`. -/
def range (lo hi : Nat) : Rand Nat := do
  return lo + (← nat (hi + 1 - lo))

/-- A fair coin. -/
def bool : Rand Bool := do
  return (← nat 2) == 1

/-- `true` with probability `k / n`. -/
def chance (k n : Nat) : Rand Bool := do
  return (← nat n) < k

/-- An element of a list, `d` for the empty list. -/
def pick {α : Type} (xs : List α) (d : α) : Rand α := do
  return xs.getD (← nat xs.length) d

/-- `n` draws. -/
def list {α : Type} (n : Nat) (g : Rand α) : Rand (List α) :=
  (List.range n).mapM fun _ => g

/-- Run from a generator state. -/
def run {α : Type} (g : Rand α) (r : Rng) : α := (g r).1

end Rand

/-! ## Byte seeds

The input of `wasm-tools smith` is a byte string read as a stream of choices, as the Rust
`arbitrary` crate's `Unstructured` does (an exhausted seed answers `0`). `Seed` and the monad
`G` are that reading; `rngBytes` draws a byte seed from a SplitMix64 state, so that a
byte-seeded generator is a generator of the API (`ByteGen.toGenerator`). -/

/-- A seed: the input bytes and a read position. -/
structure Seed where
  data : ByteArray
  pos : Nat := 0

namespace Seed

/-- A seed reading `b` from its start. -/
def ofBytes (b : ByteArray) : Seed := { data := b }

/-- The next byte (`0` once exhausted). -/
def byte (s : Seed) : UInt8 × Seed :=
  if h : s.pos < s.data.size then (s.data[s.pos], { s with pos := s.pos + 1 }) else (0, s)

/-- The bytes not read yet. -/
def remaining (s : Seed) : Nat := s.data.size - s.pos

/-- Read `k` bytes as a little-endian number. -/
def bytesLE : Nat → Seed → Nat × Seed
  | 0, s => (0, s)
  | k + 1, s =>
    let (b, s) := s.byte
    let (r, s) := bytesLE k s
    (b.toNat + 256 * r, s)

/-- A choice in `[0, n)`: as many bytes as `n - 1` needs, reduced modulo `n` (`0` for `n ≤ 1`
or an exhausted seed). -/
def choose (n : Nat) (s : Seed) : Nat × Seed :=
  if n ≤ 1 then (0, s) else
    let k := if n ≤ 0x100 then 1 else if n ≤ 0x10000 then 2 else if n ≤ 0x1000000 then 3 else 8
    let (r, s) := bytesLE k s
    (r % n, s)

end Seed

/-- The byte-seeded generation monad: a state over the seed. -/
abbrev G := StateM Seed

namespace G

/-- A choice in `[0, n)`. -/
def choose (n : Nat) : G Nat := modifyGet fun s => s.choose n

/-- A choice in `[lo, hi]` (`lo` when `hi < lo`). -/
def range (lo hi : Nat) : G Nat := do
  if hi < lo then return lo
  return lo + (← choose (hi - lo + 1))

/-- A coin. -/
def bool : G Bool := return (← choose 2) == 1

/-- `k` raw bytes. -/
def bytes (k : Nat) : G Nat := modifyGet fun s => s.bytesLE k

/-- One of the list (the default for an empty list). -/
def pick {α : Type} (d : α) (l : List α) : G α := do
  return l.getD (← choose l.length) d

/-- Is the seed exhausted? -/
def exhausted : G Bool := return (← get).remaining == 0

/-- Run on a seed. -/
def run' {α : Type} (g : G α) (b : ByteArray) : α := (g.run (Seed.ofBytes b)).1

end G

/-- `n` bytes drawn from a SplitMix64 state. -/
def rngBytes (r : Rng) (n : Nat) : ByteArray :=
  ⟨(Rand.run (Rand.list n (Rand.nat 256)) r).toArray.map (·.toUInt8)⟩

/-! ## Languages -/

/-- A language: syntax and validity. -/
structure Lang where
  /-- Syntax. -/
  Syn : Type
  /-- Validity. -/
  Valid : Syn → Prop

/-- A language with a Boolean checker equivalent to validity. -/
structure DecLang extends Lang where
  /-- The checker. -/
  check : Syn → Bool
  /-- It decides validity. -/
  check_iff : ∀ x, check x = true ↔ Valid x

/-! ## Generators, mutators, shrinkers -/

/-- **A generator**: from a seed and a size, a valid program. -/
structure Generator (L : Lang) where
  /-- The generator. -/
  run : Rng → Nat → L.Syn
  /-- Every output is valid. -/
  valid : ∀ r n, L.Valid (run r n)

/-- **A mutator**: a seeded rewrite preserving validity. -/
structure Mutator (L : Lang) where
  /-- The rewrite. -/
  run : Rng → L.Syn → L.Syn
  /-- Validity is preserved. -/
  valid : ∀ r x, L.Valid x → L.Valid (run r x)

/-- **A semantics-preserving mutator**: its output is `Eqv`-equivalent to its valid input. -/
structure SemMutator (L : Lang) (Eqv : L.Syn → L.Syn → Prop) extends Mutator L where
  /-- The output is equivalent to the input. -/
  equiv : ∀ r x, L.Valid x → Eqv (run r x) x

/-- **A shrinker**: a size and candidate replacements. Only strictly smaller candidates are
ever taken, so no property of `cands` is needed for termination. -/
structure Shrinker (S : Type) where
  /-- The size. -/
  size : S → Nat
  /-- Candidates, in preference order. -/
  cands : S → List S

/-- **A byte-seeded generator** (the shape of `wasm-tools smith`, whose seed is the input
file): every output is valid. `ByteGen.toGenerator` reads it as a `Generator`. -/
structure ByteGen (L : Lang) where
  /-- The generator. -/
  gen : ByteArray → L.Syn
  /-- Every output is valid. -/
  valid : ∀ seed, L.Valid (gen seed)

/-- **A partial mutator** (the shape of `wasm-tools mutate`): `none` when no mutation applies
(upstream's exit status 3); every output of a valid input is valid.
`PMutator.toMutator` reads it as a `Mutator` (the input when nothing applies). -/
structure PMutator (L : Lang) where
  /-- The mutation. -/
  mutate : UInt64 → L.Syn → Option L.Syn
  /-- Validity is preserved. -/
  valid : ∀ seed x x', L.Valid x → mutate seed x = some x' → L.Valid x'

/-- A partial mutator in the **class preserving `R`**: each output is `R`-related to its
input. -/
structure PMutator.Preserving (L : Lang) (R : L.Syn → L.Syn → Prop) extends PMutator L where
  /-- Each output is related to its input. -/
  preserves : ∀ seed x x', mutate seed x = some x' → R x x'

namespace Shrinker

variable {S : Type}

/-- The test a candidate `c` of `x` must pass. -/
def accept (sh : Shrinker S) (p : S → Bool) (x c : S) : Bool :=
  decide (sh.size c < sh.size x) && p c

/-- The first acceptable candidate. -/
def step (sh : Shrinker S) (p : S → Bool) (x : S) : Option S :=
  (sh.cands x).find? (sh.accept p x)

theorem step_lt {sh : Shrinker S} {p : S → Bool} {x c : S} (h : sh.step p x = some c) :
    sh.size c < sh.size x := by
  have := List.find?_some h
  simp only [accept, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- **Greedy shrinking**: take the first acceptable candidate until there is none. -/
def shrink (sh : Shrinker S) (p : S → Bool) (x : S) : S :=
  match h : sh.step p x with
  | none => x
  | some c =>
    have : sh.size c < sh.size x := step_lt h
    sh.shrink p c
termination_by sh.size x

/-- The same loop with a fuel bound and a monadic predicate (an external oracle, such as a
run of another tool). -/
def shrinkM {m : Type → Type} [Monad m] (sh : Shrinker S) (p : S → m Bool) :
    Nat → S → m S
  | 0, x => pure x
  | fuel + 1, x => do
    let rec first : List S → m (Option S)
      | [] => pure none
      | c :: cs => do
        if sh.size c < sh.size x then
          if ← p c then return some c
        first cs
    match ← first (sh.cands x) with
    | none => pure x
    | some c => shrinkM sh p fuel c

end Shrinker

/-- The first element of a list on which a monadic predicate answers `true`. -/
def findM? {m : Type → Type} [Monad m] {α : Type} (P : α → m Bool) : List α → m (Option α)
  | [] => pure none
  | a :: l => do if ← P a then pure (some a) else findM? P l

/-! ## Checked constructions -/

namespace Generator

variable {L : Lang}

/-- **The output of a checked generator**: the raw generator's output when it passes `check`,
else the default `d`. This is all a checked generator computes (`guarded`). -/
def guardedRun {α : Type} (check : α → Bool) (raw : Rng → Nat → α) (d : α) (r : Rng) (n : Nat) :
    α :=
  if check (raw r n) then raw r n else d

/-- **A checked generator**: a raw generator's output when it passes the checker, else the
valid default `d`. -/
def guarded (L : DecLang) (raw : Rng → Nat → L.Syn) (d : L.Syn) (hd : L.Valid d) :
    Generator L.toLang where
  run := guardedRun L.check raw d
  valid r n := by
    unfold guardedRun
    by_cases h : L.check (raw r n) = true
    · simp only [h, ite_true]; exact (L.check_iff _).1 h
    · simp only [h]; exact hd

/-- Uniform choice between generators (`g` when the list is empty). -/
def oneOf (gs : List (Generator L)) (g : Generator L) : Generator L where
  run r n :=
    let r₁ := r.split.1
    let r₂ := r.split.2
    (gs.getD (Rand.run (Rand.nat gs.length) r₁) g).run r₂ n
  valid _ n := (gs.getD _ g).valid _ n

/-- Post-compose a validity-preserving map. -/
def mapValid {L' : Lang} (g : Generator L) (f : L.Syn → L'.Syn) (hf : ∀ x, L.Valid x → L'.Valid (f x)) :
    Generator L' where
  run r n := f (g.run r n)
  valid r n := hf _ (g.valid r n)

/-- Post-compose a mutator. -/
def andThen (g : Generator L) (μ : Mutator L) : Generator L where
  run r n :=
    let r₁ := r.split.1
    let r₂ := r.split.2
    μ.run r₂ (g.run r₁ n)
  valid _ n := μ.valid _ _ (g.valid _ n)

end Generator

namespace Mutator

variable {L : Lang}

/-- The identity mutator. -/
def id (L : Lang) : Mutator L := ⟨fun _ x => x, fun _ _ h => h⟩

/-- Sequencing, with independent seeds. -/
def seq (μ ν : Mutator L) : Mutator L where
  run r x :=
    let r₁ := r.split.1
    let r₂ := r.split.2
    ν.run r₂ (μ.run r₁ x)
  valid _ _ h := ν.valid _ _ (μ.valid _ _ h)

/-- `n` rounds. -/
def iter (μ : Mutator L) : Nat → Mutator L
  | 0 => id L
  | n + 1 => μ.seq (μ.iter n)

/-- Uniform choice between mutators. -/
def oneOf (μs : List (Mutator L)) (μ : Mutator L) : Mutator L where
  run r x :=
    let r₁ := r.split.1
    let r₂ := r.split.2
    (μs.getD (Rand.run (Rand.nat μs.length) r₁) μ).run r₂ x
  valid _ x h := (μs.getD _ μ).valid _ x h

/-- **The output of a checked mutator**: the raw rewrite's output when it passes `check`, else
the input. This is all a checked mutator computes (`guarded`). -/
def guardedRun {α : Type} (check : α → Bool) (raw : Rng → α → α) (r : Rng) (x : α) : α :=
  if check (raw r x) then raw r x else x

/-- **A checked mutator**: a raw rewrite's output when it passes the checker, else the input. -/
def guarded (L : DecLang) (raw : Rng → L.Syn → L.Syn) : Mutator L.toLang where
  run := guardedRun L.check raw
  valid r x hx := by
    unfold guardedRun
    by_cases h : L.check (raw r x) = true
    · simp only [h, ite_true]; exact (L.check_iff _).1 h
    · simp only [h]; exact hx

end Mutator

namespace ByteGen

variable {L : Lang}

/-- The checked output of a raw byte-seeded generator: its output when it passes the checker,
else `d`. -/
def guardedRun (L : DecLang) (raw : ByteArray → L.Syn) (d : L.Syn) (seed : ByteArray) : L.Syn :=
  if L.check (raw seed) then raw seed else d

/-- **A checked byte-seeded generator.** -/
def guarded (L : DecLang) (raw : ByteArray → L.Syn) (d : L.Syn) (hd : L.Valid d) :
    ByteGen L.toLang where
  gen := guardedRun L raw d
  valid seed := by
    unfold guardedRun
    by_cases h : L.check (raw seed) = true
    · simp only [h, ite_true]; exact (L.check_iff _).1 h
    · simp only [h]; exact hd

/-- A byte-seeded generator as a generator of the API: the seed is `n` bytes of the state. -/
def toGenerator (g : ByteGen L) : Generator L where
  run r n := g.gen (rngBytes r n)
  valid _ _ := g.valid _

/-- Post-compose a validity-preserving map. -/
def mapValid {L' : Lang} (g : ByteGen L) (f : L.Syn → L'.Syn)
    (hf : ∀ x, L.Valid x → L'.Valid (f x)) : ByteGen L' :=
  ⟨fun s => f (g.gen s), fun s => hf _ (g.valid s)⟩

end ByteGen

namespace PMutator

variable {L : Lang}

/-- A partial mutator as a mutator of the API: the input when no mutation applies. -/
def toMutator (μ : PMutator L) : Mutator L where
  run r x := (μ.mutate r.state x).getD x
  valid r x hx := by
    cases h : μ.mutate r.state x with
    | none => exact hx
    | some x' => exact μ.valid _ _ _ hx h

/-- The checked output of a raw partial mutation: kept only when it passes the checker. -/
def guardedRun (L : DecLang) (raw : UInt64 → L.Syn → Option L.Syn) (seed : UInt64)
    (x : L.Syn) : Option L.Syn :=
  match raw seed x with
  | some x' => if L.check x' then some x' else none
  | none => none

/-- **A checked partial mutator.** -/
def guarded (L : DecLang) (raw : UInt64 → L.Syn → Option L.Syn) : PMutator L.toLang where
  mutate := guardedRun L raw
  valid seed x x' _ h := by
    unfold guardedRun at h
    split at h
    · split at h
      · cases h; exact (L.check_iff _).1 ‹_›
      · cases h
    · cases h

end PMutator

namespace SemMutator

variable {L : Lang} {Eqv : L.Syn → L.Syn → Prop}

/-- The identity is semantics-preserving for a reflexive `Eqv`. -/
def id (L : Lang) (Eqv : L.Syn → L.Syn → Prop) (hr : ∀ x, Eqv x x) : SemMutator L Eqv :=
  ⟨Mutator.id L, fun _ x _ => hr x⟩

/-- Sequencing, for a transitive `Eqv`. -/
def seq (ht : ∀ {x y z}, Eqv x y → Eqv y z → Eqv x z) (μ ν : SemMutator L Eqv) :
    SemMutator L Eqv where
  run r x := ν.run r.split.2 (μ.run r.split.1 x)
  valid _ _ hx := ν.valid _ _ (μ.valid _ _ hx)
  equiv _ _ hx := ht (ν.equiv _ _ (μ.valid _ _ hx)) (μ.equiv _ _ hx)

/-- Uniform choice between semantics-preserving mutators. -/
def oneOf (μs : List (SemMutator L Eqv)) (μ : SemMutator L Eqv) : SemMutator L Eqv where
  run r x :=
    let r₁ := r.split.1
    let r₂ := r.split.2
    (μs.getD (Rand.run (Rand.nat μs.length) r₁) μ).run r₂ x
  valid _ x h := (μs.getD _ μ).valid _ x h
  equiv _ x h := (μs.getD _ μ).equiv _ x h

/-- **A checked semantics-preserving mutator**: the output of `μ` (sound for a weaker
validity `V`) when it passes the checker of `L`, else the input. -/
def guarded (L : DecLang) {V : L.Syn → Prop} {Eqv : L.Syn → L.Syn → Prop}
    (hr : ∀ x, Eqv x x) (μ : SemMutator ⟨L.Syn, V⟩ Eqv) (hw : ∀ x, L.Valid x → V x) :
    SemMutator L.toLang Eqv where
  run r x := if L.check (μ.run r x) then μ.run r x else x
  valid r x hx := by
    by_cases h : L.check (μ.run r x) = true
    · simp only [h, ite_true]; exact (L.check_iff _).1 h
    · simp only [h]; exact hx
  equiv r x hx := by
    by_cases h : L.check (μ.run r x) = true
    · simp only [h, ite_true]; exact μ.equiv r x (hw x hx)
    · simp only [h]; exact hr x

end SemMutator

end Silmaril.Wasm.Tools.Gen
