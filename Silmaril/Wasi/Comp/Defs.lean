module

public import Silmaril.Wasi.World.Defs
public import Silmaril.Games.Handler.Defs
public import Silmaril.Games.Play.Thms

@[expose] public section

/-!
# Components with uninterpreted imports

A component of a world is given by its **body**: a finite program over the imports for every
export call (`Body I X`, a `Silmaril.Games.Handler`). Its strategy `ofBody h` is described play by
play: `CSt` is its control state (idle, running the program of the current export call, or
waiting for the answer of an import), `CStep` its moves and `Reach h s c` says that the play `s`
leads to the state `c`. The plays of `ofBody h` are the reachable ones.

The imports are **uninterpreted**: in the waiting state every answer is accepted
(`CStep.reply`), so the strategy is receptive. A host is not part of the component; it is
linked below it (`Silmaril.Wasi.Host`).

* `CSt.pos`: the game position of a control state; `CStep.step`: a move of the control state is
  a move of the game, so reachable plays are legal (`Reach.path`).
* `Reach.of_prefix`, `Reach.receptive`: prefix closure and receptiveness.
* `ofBody h : Strategy (nsig I) (nsig X)`.

`ofBody` is a direct play-level description of the stateless strategy of a handler. That it
equals `Silmaril.Games.Strategy.ofHandler h` is not proved here (see `docs/projects/wasm-wasi.md`).

A Silmaril addition.
-/

namespace Silmaril.Wasi

open Silmaril.Games
open Silmaril.Wasm.Component (Val)

variable {I X : Set FnName}

/-- The body of a component: a program over the imports for every export call. -/
abbrev Body (I X : Set FnName) : Type := Handler (nsig I) (nsig X)

/-- The programs of a body. -/
abbrev BProg (I : Set FnName) : Type := Prog (nsig I) (Option (List Val))

/-- The control state of a component. -/
inductive CSt (I X : Set FnName) : Type where
  /-- No export call is running. -/
  | idle
  /-- The export call `q` runs the program `p`. -/
  | run (q : (nsig X).Op) (p : BProg I)
  /-- The export call `q` waits for the answer of the import call `m`. -/
  | wait (q : (nsig X).Op) (m : (nsig I).Op) (k : Option (List Val) → BProg I)

/-- The game position of a control state. -/
def CSt.pos : CSt I X → Pos (nsig I) (nsig X)
  | .idle => .idle
  | .run q _ => .run q
  | .wait q m _ => .wait q m

/-- The moves of a component. -/
inductive CStep (h : Body I X) : CSt I X → Move (nsig I) (nsig X) → CSt I X → Prop
  /-- An export call starts its program. -/
  | ask (q : (nsig X).Op) : CStep h .idle (.inr (.ask q)) (.run q (h q))
  /-- The program calls an import. -/
  | call (q : (nsig X).Op) (m : (nsig I).Op) (k : Option (List Val) → BProg I) :
      CStep h (.run q (.call m k)) (.inl (.ask m)) (.wait q m k)
  /-- Any answer of the import is accepted (the import is uninterpreted). -/
  | reply (q : (nsig X).Op) (m : (nsig I).Op) (k : Option (List Val) → BProg I)
      (n : Option (List Val)) : CStep h (.wait q m k) (.inl (.ans m n)) (.run q (k n))
  /-- The program returns. -/
  | ret (q : (nsig X).Op) (r : Option (List Val)) :
      CStep h (.run q (.pure r)) (.inr (.ans q r)) .idle

/-- `Reach h s c`: the play `s` leads the component from `idle` to `c`. -/
inductive Reach (h : Body I X) : List (Move (nsig I) (nsig X)) → CSt I X → Prop
  /-- The empty play. -/
  | nil : Reach h [] .idle
  /-- One more move. -/
  | snoc {s : List (Move (nsig I) (nsig X))} {c c' : CSt I X} {o : Move (nsig I) (nsig X)} :
      Reach h s c → CStep h c o c' → Reach h (s ++ [o]) c'

variable {h : Body I X}

/-- A move of the control state is a move of the game. -/
theorem CStep.step {c c' : CSt I X} {o : Move (nsig I) (nsig X)} (hc : CStep h c o c') :
    Step c.pos o c'.pos := by
  cases hc
  · exact .ask _
  · exact .call _ _
  · exact .reply _ _ _
  · exact .ret _ _

/-- Reachable plays are legal, ending at the position of their state. -/
theorem Reach.path {s : List (Move (nsig I) (nsig X))} {c : CSt I X} (hs : Reach h s c) :
    Path .idle s c.pos := by
  induction hs with
  | nil => exact .nil _
  | snoc _ hc ih => exact ih.append (Path.single hc.step)

/-- Reachable plays are closed under prefixes. -/
theorem Reach.of_prefix {s t : List (Move (nsig I) (nsig X))} {c : CSt I X} (ht : Reach h t c)
    (hst : s <+: t) : ∃ c', Reach h s c' := by
  induction ht with
  | nil =>
    have hs : s = [] := List.prefix_nil.1 hst
    exact ⟨.idle, hs ▸ Reach.nil⟩
  | snoc ht' hc ih =>
    rcases List.prefix_concat_iff.1 hst with h' | h'
    · exact ⟨_, h' ▸ ht'.snoc hc⟩
    · exact ih h'

/-- Every legal Opponent move extends a reachable play. -/
theorem Reach.receptive {s : List (Move (nsig I) (nsig X))} {c : CSt I X}
    {x y : Pos (nsig I) (nsig X)} {o : Move (nsig I) (nsig X)} (hs : Reach h s c)
    (hx : Path .idle s x) (hxy : Step x o y) (ho : o.IsO) : ∃ c', Reach h (s ++ [o]) c' := by
  have hxc : x = c.pos := Path.det hx hs.path
  cases c with
  | idle =>
    have h' : Step .idle o y := by rw [hxc] at hxy; exact hxy
    cases h' with | ask q => exact ⟨_, hs.snoc (.ask q)⟩
  | run q p =>
    have h' : Step (.run q) o y := by rw [hxc] at hxy; exact hxy
    cases h' <;> exact False.elim ho
  | wait q m k =>
    have h' : Step (.wait q m) o y := by rw [hxc] at hxy; exact hxy
    cases h' with | reply _ _ n => exact ⟨_, hs.snoc (.reply q m k n)⟩

/-- **The strategy of a component body**: its reachable plays. -/
def ofBody (h : Body I X) : Strategy (nsig I) (nsig X) where
  plays := {s | ∃ c, Reach h s c}
  nil_mem := ⟨_, .nil⟩
  legal := fun ⟨_, hc⟩ => ⟨_, hc.path⟩
  of_prefix := fun ⟨_, hc⟩ hp => hc.of_prefix hp
  receptive := fun ⟨_, hc⟩ hx hxy ho => hc.receptive hx hxy ho

/-- The plays of `ofBody h`. -/
theorem mem_ofBody {s : List (Move (nsig I) (nsig X))} : s ∈ ofBody h ↔ ∃ c, Reach h s c :=
  Iff.rfl

end Silmaril.Wasi
