module

public import Silmaril.Games.Div.Defs
public import Silmaril.Games.Abstract.HostRunInf.Defs

/-!
# From function observations to divergence-observing strategies

An abstract function is observed by a triple `t : ObsTriple E S A B`: its
finished call behaviours (`AFun`), its pending calls (`Pending`) and its
productive runs (`PInf`), the data of `hostObsFull`. This module sends such a
triple to the canonical play object, a `DStrategy E (funSig S A B)`.

**The function interface.** `funSig S A B` has one question `(s, a)` per
state and argument. Its answers are a return with its final state
(`.inl (b, s')`) or a trap (`.inr ()`); the trap payload is erased, as in
`End.trap`.

**Plays.** A play of `toDStrat t` is a sequence of rounds. A round starts with
an Opponent question `(s, a)`, continues with the import calls of a behaviour
(each call `⟨m, n⟩` is a Proponent `ask m` followed by the Opponent `ans m n`),
and ends with the Proponent answer of a finished behaviour of `t.1 s a`. The
last round may be incomplete. The plays are given by an automaton (`AStep`,
`ARun`) whose states (`St`) refine the positions `Pos` by the calls of the
current round:

* Opponent moves are always accepted (receptiveness): a question when idle,
  and every answer `ans m n` to the pending call `m`;
* Proponent may call `m` after the calls `c` when `(c, m)` is a call prefix
  of the triple (`satP t`): a pending call, or a call forced by a finished or
  divergent behaviour, by a pending call, or by a productive stream;
* Proponent may answer `r` after the calls `c` when `(c, ansEnd r)` is a
  finished behaviour.

Prefix closure is automatic: a run of the automaton passes through every
prefix.

**Divergence.** The plays ending at `run (s, a) c` with `(c, .div) ∈ t.1 s a`.

**Infinite plays.** The infinite plays (`IsInfPlay` prefix sets of plays) of
two kinds:

* finitely many completed rounds, then a question `q` and the calls of a
  productive stream `ω ∈ t.2.2 q.1 q.2` (`streamPlay`);
* infinitely many completed rounds: every member extends, within the play, to
  a member ending idle.

**Saturation.** The plays only see the call prefixes `satP t`, so pending
calls forced by the other components (and the prefixes of pending calls) are
invisible as separate data. `sat t` replaces the pending calls by `satP t`;
`Saturated t` says nothing is added. The theorems
(`Silmaril.Games.Abstract.StratObs.Thms`) show `toDStrat t = toDStrat t' ↔
sat t = sat t'`.

The automaton is used rather than `Strategy.generate` of maximal plays
because it makes prefix closure and receptiveness structural and the state
after a play unique (`ARun.det`). The characterisations in `Thms` give the
"prefix of a behaviour" reading.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

/-- The interface of an abstract function: a question carries the state and
the argument; an answer is a return with its final state, or a trap. -/
abbrev funSig (S A B : Type u) : Sig.{u} := ⟨S × A, fun _ => (B × S) ⊕ PUnit⟩

/-- The observations of a function: finished behaviours, pending calls and
productive runs. -/
abbrev ObsTriple (E : Sig.{u}) (S A B : Type u) : Type u :=
  AFun E S A B × Pending E S A × PInf E S A

namespace StratObs

variable {E : Sig.{u}} {S A B : Type u}

/-- The end of a function given by an answer at the function interface. -/
def ansEnd : (B × S) ⊕ PUnit.{u + 1} → End S B
  | .inl (b, s) => .ret b s
  | .inr _ => .trap

/-- The moves of import calls with their answers. -/
def callMoves {F : Sig.{u}} (c : List (Call E)) : List (Move E F) :=
  c.flatMap fun x => [.inl (.ask x.1), .inl (.ans x.1 x.2)]

/-- `c` followed by a call of `m` is a prefix of the call list `d`. -/
def CallPre (c : List (Call E)) (m : E.Op) (d : List (Call E)) : Prop :=
  ∃ n c', d = c ++ ⟨m, n⟩ :: c'

/-- The call prefixes of a triple: its pending calls, and the calls forced by
pending calls, by behaviours (of any end) and by productive streams. -/
def satP (t : ObsTriple E S A B) : Pending E S A := fun s a =>
  {x | x ∈ t.2.1 s a ∨ (∃ d m', (d, m') ∈ t.2.1 s a ∧ CallPre x.1 x.2 d) ∨
    (∃ d e, (d, e) ∈ t.1 s a ∧ CallPre x.1 x.2 d) ∨
    ∃ ω ∈ t.2.2 s a, ∃ k, streamTake ω k = x.1 ∧ (ω k).1 = x.2}

/-- Saturation: the pending calls closed under the call prefixes forced by
the triple. -/
def sat (t : ObsTriple E S A B) : ObsTriple E S A B := (t.1, satP t, t.2.2)

/-- A triple whose pending calls are already closed. -/
def Saturated (t : ObsTriple E S A B) : Prop := sat t = t

/-! ## The automaton -/

/-- States of the play automaton: idle, running the question `q` after the
calls `c`, or waiting for the answer to the call `m` after the calls `c`. -/
inductive St (E : Sig.{u}) (S A : Type u) : Type u
  | idle
  | run (q : S × A) (c : List (Call E))
  | wait (q : S × A) (c : List (Call E)) (m : E.Op)

/-- The game position of a state. -/
def St.pos {B : Type u} : St E S A → Pos E (funSig S A B)
  | .idle => .idle
  | .run q _ => .run q
  | .wait q _ m => .wait q m

/-- One move of the automaton for finished behaviours `f` and call prefixes
`P`. -/
inductive AStep (f : AFun E S A B) (P : Pending E S A) :
    St E S A → Move E (funSig S A B) → St E S A → Prop
  /-- Opponent asks `q`. -/
  | ask (q : S × A) : AStep f P .idle (.inr (.ask q)) (.run q [])
  /-- Proponent calls `m` after the calls `c`. -/
  | call (q : S × A) (c : List (Call E)) (m : E.Op) :
      (c, m) ∈ P q.1 q.2 → AStep f P (.run q c) (.inl (.ask m)) (.wait q c m)
  /-- Opponent answers the call `m` with any `n`. -/
  | reply (q : S × A) (c : List (Call E)) (m : E.Op) (n : E.Ar m) :
      AStep f P (.wait q c m) (.inl (.ans m n)) (.run q (c ++ [⟨m, n⟩]))
  /-- Proponent answers `q` at the end of a finished behaviour. -/
  | ret (q : S × A) (c : List (Call E)) (r : (B × S) ⊕ PUnit) :
      (c, ansEnd r) ∈ f q.1 q.2 → AStep f P (.run q c) (.inr (.ans q r)) .idle

/-- Runs of the automaton. -/
inductive ARun (f : AFun E S A B) (P : Pending E S A) :
    St E S A → List (Move E (funSig S A B)) → St E S A → Prop
  | nil (x : St E S A) : ARun f P x [] x
  | cons {x y z : St E S A} {o : Move E (funSig S A B)} {s : List (Move E (funSig S A B))} :
      AStep f P x o y → ARun f P y s z → ARun f P x (o :: s) z

/-! ## Basic facts

Stated with the definitions because the strategy below needs them in its
proof fields.
-/

section Basic

variable {f : AFun E S A B} {P : Pending E S A}

/-- Automaton steps are game steps. -/
theorem AStep.pos {x y : St E S A} {o : Move E (funSig S A B)} (h : AStep f P x o y) :
    Step x.pos o y.pos := by
  cases h <;> constructor

/-- The automaton is deterministic. -/
theorem AStep.det {x y z : St E S A} {o : Move E (funSig S A B)} (h₁ : AStep f P x o y)
    (h₂ : AStep f P x o z) : y = z := by
  cases h₁ <;> cases h₂ <;> rfl

/-- Automaton runs are game paths. -/
theorem ARun.pos {x y : St E S A} {s : List (Move E (funSig S A B))} (h : ARun f P x s y) :
    Path x.pos s y.pos := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons h.pos ih

/-- Runs are deterministic. -/
theorem ARun.det {x y z : St E S A} {s : List (Move E (funSig S A B))} (h₁ : ARun f P x s y)
    (h₂ : ARun f P x s z) : y = z := by
  induction h₁ generalizing z with
  | nil => cases h₂; rfl
  | cons h _ ih => cases h₂ with | cons h' hr => exact ih ((h.det h') ▸ hr)

/-- Runs compose along concatenation. -/
theorem ARun.append {x y z : St E S A} {s u : List (Move E (funSig S A B))}
    (h₁ : ARun f P x s y) (h₂ : ARun f P y u z) : ARun f P x (s ++ u) z := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

/-- A run through `s ++ u` passes through some state after `s`. -/
theorem ARun.of_append {x z : St E S A} {s u : List (Move E (funSig S A B))}
    (h : ARun f P x (s ++ u) z) : ∃ y, ARun f P x s y ∧ ARun f P y u z := by
  induction s generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons o s ih =>
    cases h with
    | cons h hr => obtain ⟨y, h₁, h₂⟩ := ih hr; exact ⟨y, .cons h h₁, h₂⟩

/-- Every legal Opponent move is accepted. -/
theorem ARun.receptive {y : St E S A} {s : List (Move E (funSig S A B))}
    {x x' : Pos E (funSig S A B)} {o : Move E (funSig S A B)} (h : ARun f P .idle s y)
    (hx : Path .idle s x) (hs : Step x o x') (ho : o.IsO) : ∃ z, ARun f P .idle (s ++ [o]) z := by
  have hy : y.pos = x := Path.det h.pos hx
  cases hs with
  | ask q =>
    cases y <;> simp [St.pos] at hy
    exact ⟨_, h.append (.cons (.ask q) (.nil _))⟩
  | reply q m n =>
    cases y <;> simp [St.pos] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨_, h.append (.cons (.reply _ _ _ n) (.nil _))⟩
  | call => simp [Move.IsO] at ho
  | ret => simp [Move.IsO] at ho

end Basic

/-! ## The strategy -/

/-- The finite plays: the moves the automaton accepts from idle. -/
def plays (f : AFun E S A B) (P : Pending E S A) : Set (List (Move E (funSig S A B))) :=
  {s | ∃ y, ARun f P .idle s y}

/-- The divergent plays: those that reach `run q c` with `(c, .div)` a
behaviour at `q`. -/
def divs (f : AFun E S A B) (P : Pending E S A) : Set (List (Move E (funSig S A B))) :=
  {s | ∃ q c, ARun f P .idle s (.run q c) ∧ (c, .div) ∈ f q.1 q.2}

/-- The infinite play of the rounds `pre`, then the question `q` and the calls
of the stream `ω`. -/
def streamPlay (pre : List (Move E (funSig S A B))) (q : S × A) (ω : ℕ → Call E) :
    Set (List (Move E (funSig S A B))) :=
  {p | ∃ k, p <+: pre ++ .inr (.ask q) :: callMoves (streamTake ω k)}

/-- The infinite plays: infinite traces of plays that end in a productive
stream after finitely many completed rounds, or that complete infinitely many
rounds. -/
def infs (f : AFun E S A B) (P : Pending E S A) (Q : PInf E S A) :
    Set (Set (List (Move E (funSig S A B)))) :=
  {I | IsInfPlay I ∧ I ⊆ plays f P ∧
    ((∃ pre q ω, ARun f P .idle pre .idle ∧ ω ∈ Q q.1 q.2 ∧ I = streamPlay pre q ω) ∨
      ∀ p ∈ I, ∃ p' ∈ I, p <+: p' ∧ ARun f P .idle p' .idle)}

/-- The strategy of finished behaviours `f` and call prefixes `P`. -/
def strat (f : AFun E S A B) (P : Pending E S A) : Strategy E (funSig S A B) where
  plays := plays f P
  nil_mem := ⟨_, .nil _⟩
  legal := fun ⟨_, h⟩ => ⟨_, h.pos⟩
  of_prefix := by
    rintro s t ⟨y, h⟩ ⟨u, rfl⟩
    obtain ⟨z, hz, -⟩ := h.of_append
    exact ⟨z, hz⟩
  receptive := fun ⟨_, h⟩ hx hs ho => h.receptive hx hs ho

/-- The divergence-observing strategy of finished behaviours `f`, call
prefixes `P` and productive runs `Q`. -/
def build (f : AFun E S A B) (P : Pending E S A) (Q : PInf E S A) :
    DStrategy E (funSig S A B) where
  toStrategy := strat f P
  div := divs f P
  inf := infs f P Q
  div_mem := fun ⟨_, _, h, _⟩ => ⟨_, h⟩
  div_run := fun ⟨q, _, h, _⟩ => ⟨q, h.pos⟩
  inf_isInf h := h.1
  inf_sub h := h.2.1

/-- **The play object of a triple.** -/
def toDStrat (t : ObsTriple E S A B) : DStrategy E (funSig S A B) := build t.1 (satP t) t.2.2

end StratObs

end Silmaril.Games.Abstract
