module

public import Mathlib.Logic.Relation

/-!
# Cut-point simulation between a source semantics and a deterministic machine

The generic layer of "this C compiles to this x86 code" (`Silmaril.Project.Shapes.C`): a source
semantics (`Source`: steps, the states that have gone wrong, the final states with their results)
and a deterministic target machine share numbered **program points**; a correspondence (`Corr`)
relates source and target states at each point, with the target's entry state as a ghost
argument. `Corr.Segment C k` is one segment goal, `Corr.Whole C k` the end-to-end statement, and
`Corr.whole_of_segments` (in `Thms`) proves the second from the first for every point, once.

* The source run of a segment is existential (the prover picks one), so the goals stay true for
  a correct compiler when the source is nondeterministic.
* `Source.Safe s`: no run from `s` goes wrong and every run is finite. Segment and whole
  statements assume it: a source that can go wrong (undefined behaviour) permits any target
  behaviour, and a source that may diverge is not covered.

It depends on Lean core and `Mathlib.Logic.Relation` only.
-/

@[expose] public section

namespace Silmaril.Compiler.CompilesTo

/-! ## Cut-point runs -/

section Generic

variable {σ τ R : Type}

/-- `s` runs to `t` in one or more `step`s whose intermediate states all lie outside `cut`. -/
inductive Hop (step : σ → σ → Prop) (cut : σ → Prop) : σ → σ → Prop where
  | one {s t : σ} : step s t → Hop step cut s t
  | more {s u t : σ} : step s u → ¬ cut u → Hop step cut u t → Hop step cut s t

/-- **A segment run**: from `s`, one or more steps to the first state `t` in `cut`. -/
def Seg (step : σ → σ → Prop) (cut : σ → Prop) (s t : σ) : Prop :=
  Hop step cut s t ∧ cut t

/-- A source semantics: its steps (possibly nondeterministic), the states that have gone wrong
and the final states with their results. -/
structure Source (σ R : Type) where
  step : σ → σ → Prop
  wrong : σ → Prop
  final : σ → R → Prop

/-- **No undefined behaviour and termination from `s`**: no state reachable from `s` has gone
wrong, and every run from `s` is finite. -/
def Source.Safe (S : Source σ R) (s : σ) : Prop :=
  (∀ t, Relation.ReflTransGen S.step s t → ¬ S.wrong t) ∧ Acc (fun t u => S.step u t) s

/-- **A correspondence of program points** between a source semantics and a deterministic target
machine `tgt`. `srcAt k`/`tgtAt k` are the states at point `k`; `rel k x0 s x` relates a source
state `s` and a target state `x` at point `k`, where `x0` is the target's entry state (a ghost:
frame facts are stated relative to it); `tgtFinal x0 x` is the target's return and
`result x0 r x` relates the source result `r` with the returned target state. -/
structure Corr (σ τ R : Type) where
  src : Source σ R
  tgt : τ → Option τ
  srcAt : Nat → σ → Prop
  tgtAt : Nat → τ → Prop
  rel : Nat → τ → σ → τ → Prop
  tgtFinal : τ → τ → Prop
  result : τ → R → τ → Prop

namespace Corr

variable (C : Corr σ τ R)

/-- The source's cut points: the program points and the final states. -/
def srcCut (s : σ) : Prop := (∃ k, C.srcAt k s) ∨ ∃ r, C.src.final s r

/-- The target's cut points, from the entry state `x0`: the program points and the return. -/
def tgtCut (x0 x : τ) : Prop := (∃ k, C.tgtAt k x) ∨ C.tgtFinal x0 x

/-- The target's step relation. -/
def tgtStep (x y : τ) : Prop := C.tgt x = some y

/-- **The segment at point `k` is simulated.** From every source state `s` and target state `x`
at point `k` that correspond (from the target entry `x0`), if the source cannot go wrong from
`s` and terminates, the target runs to its *next* cut point `y` (the first one: the segment's
code is exactly what it executes), the source runs in one or more steps to a cut point `t`
(along *some* run: the prover picks it), and either both are at one point `j` and correspond
there, or both are final with corresponding results. -/
def Segment (k : Nat) : Prop :=
  ∀ x0 s x, C.srcAt k s → C.tgtAt k x → C.rel k x0 s x → C.src.Safe s →
    ∃ t y, (Relation.TransGen C.src.step s t ∧ C.srcCut t) ∧ Seg C.tgtStep (C.tgtCut x0) x y ∧
      ((∃ j, C.srcAt j t ∧ C.tgtAt j y ∧ C.rel j x0 t y) ∨
        (∃ r, C.src.final t r ∧ C.tgtFinal x0 y ∧ C.result x0 r y))

/-- **End to end from point `k`**: from corresponding states at `k`, if the source cannot go
wrong and terminates, the source runs to a final state with result `r`, and the target runs to
its return, whose state corresponds to `r`. -/
def Whole (k : Nat) : Prop :=
  ∀ x0 s x, C.srcAt k s → C.tgtAt k x → C.rel k x0 s x → C.src.Safe s →
    ∃ t r y, Relation.ReflTransGen C.src.step s t ∧ C.src.final t r ∧
      Relation.ReflTransGen C.tgtStep x y ∧ C.tgtFinal x0 y ∧ C.result x0 r y

/-- **Not vacuous at point `k`**: some corresponding states at `k` have a safe source. -/
def Inhabited (k : Nat) : Prop :=
  ∃ x0 s x, C.srcAt k s ∧ C.tgtAt k x ∧ C.rel k x0 s x ∧ C.src.Safe s

end Corr

end Generic

end Silmaril.Compiler.CompilesTo

end
