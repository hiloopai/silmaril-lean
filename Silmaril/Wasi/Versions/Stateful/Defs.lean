module

public import Silmaril.Wasi.Host.Defs
public import Silmaril.Games.Handler.Defs
public import Silmaril.Games.Play.Thms

@[expose] public section

/-!
# Stateful components with uninterpreted imports

`Silmaril.Wasi.Comp` describes components whose export calls are independent programs
(`Body I X`, a stateless `Handler`). An adapter between WASI versions keeps state across calls:
the preview1 adapter keeps a descriptor table, cached streams and file positions. This module
adds a component **with a state** `S`: a body `SBody S I X` maps the current state and an export
call to a program over the imports that returns the next state with the result.

* `SCSt`, `SStep`, `SReach`: control states (idle in a state, running, waiting), moves and
  reachable plays; `ofSBody h s₀` is the strategy (the imports stay uninterpreted: every answer
  is accepted).
* `Wp T p Q qT`: the weakest precondition of a program `p` under the theory `T` on the host's
  answers: whatever answers `T` accepts from the state `qT`, the result and final theory state
  satisfy `Q`.
* `retG P`: a guarantee stated as a theory `P` on host answers, read on the component's export
  *returns*: a return `ret f a r` is read as the answer `imp f a r`. This is how the composite of
  an adapter and a host is a host of the adapter's exports (`Silmaril.Wasi.Versions.Stateful.Thms`,
  `link_model`).
* `retAsImp`: the export returns of an event list, as answers.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-- A program of a stateful component: it returns the next state and the result. -/
abbrev SProg (S : Type) (I : Set FnName) : Type := Prog (nsig I) (S × Option (List Val))

/-- The body of a stateful component. -/
abbrev SBody (S : Type) (I X : Set FnName) : Type := S → (nsig X).Op → SProg S I

/-- The control state of a stateful component. -/
inductive SCSt (S : Type) (I X : Set FnName) : Type where
  /-- No export call is running; the state is `s`. -/
  | idle (s : S)
  /-- The export call `q` runs the program `p`. -/
  | run (q : (nsig X).Op) (p : SProg S I)
  /-- The export call `q` waits for the answer of the import call `m`. -/
  | wait (q : (nsig X).Op) (m : (nsig I).Op) (k : Option (List Val) → SProg S I)

variable {S : Type} {I X : Set FnName}

/-- The game position of a control state. -/
def SCSt.pos : SCSt S I X → Pos (nsig I) (nsig X)
  | .idle _ => .idle
  | .run q _ => .run q
  | .wait q m _ => .wait q m

/-- The moves of a stateful component. -/
inductive SStep (h : SBody S I X) : SCSt S I X → Move (nsig I) (nsig X) → SCSt S I X → Prop
  /-- An export call starts its program in the current state. -/
  | ask (s : S) (q : (nsig X).Op) : SStep h (.idle s) (.inr (.ask q)) (.run q (h s q))
  /-- The program calls an import. -/
  | call (q : (nsig X).Op) (m : (nsig I).Op) (k : Option (List Val) → SProg S I) :
      SStep h (.run q (.call m k)) (.inl (.ask m)) (.wait q m k)
  /-- Any answer of the import is accepted. -/
  | reply (q : (nsig X).Op) (m : (nsig I).Op) (k : Option (List Val) → SProg S I)
      (n : Option (List Val)) : SStep h (.wait q m k) (.inl (.ans m n)) (.run q (k n))
  /-- The program returns `r` and the next state `s`. -/
  | ret (q : (nsig X).Op) (s : S) (r : Option (List Val)) :
      SStep h (.run q (.pure (s, r))) (.inr (.ans q r)) (.idle s)

/-- `SReach h s₀ t c`: the play `t` leads the component from `idle s₀` to `c`. -/
inductive SReach (h : SBody S I X) (s₀ : S) : List (Move (nsig I) (nsig X)) → SCSt S I X → Prop
  /-- The empty play. -/
  | nil : SReach h s₀ [] (.idle s₀)
  /-- One more move. -/
  | snoc {t : List (Move (nsig I) (nsig X))} {c c' : SCSt S I X} {o : Move (nsig I) (nsig X)} :
      SReach h s₀ t c → SStep h c o c' → SReach h s₀ (t ++ [o]) c'

variable {h : SBody S I X} {s₀ : S}

/-- A move of the control state is a move of the game. -/
theorem SStep.step {c c' : SCSt S I X} {o : Move (nsig I) (nsig X)} (hc : SStep h c o c') :
    Step c.pos o c'.pos := by
  cases hc
  · exact .ask _
  · exact .call _ _
  · exact .reply _ _ _
  · exact .ret _ _

/-- Reachable plays are legal. -/
theorem SReach.path {t : List (Move (nsig I) (nsig X))} {c : SCSt S I X} (ht : SReach h s₀ t c) :
    Path .idle t c.pos := by
  induction ht with
  | nil => exact .nil _
  | snoc _ hc ih => exact ih.append (Path.single hc.step)

/-- Reachable plays are closed under prefixes. -/
theorem SReach.of_prefix {t u : List (Move (nsig I) (nsig X))} {c : SCSt S I X}
    (hu : SReach h s₀ u c) (htu : t <+: u) : ∃ c', SReach h s₀ t c' := by
  induction hu with
  | nil => exact ⟨_, (List.prefix_nil.1 htu) ▸ SReach.nil⟩
  | snoc hu' hc ih =>
    rcases List.prefix_concat_iff.1 htu with h' | h'
    · exact ⟨_, h' ▸ hu'.snoc hc⟩
    · exact ih h'

/-- Every legal Opponent move extends a reachable play. -/
theorem SReach.receptive {t : List (Move (nsig I) (nsig X))} {c : SCSt S I X}
    {x y : Pos (nsig I) (nsig X)} {o : Move (nsig I) (nsig X)} (ht : SReach h s₀ t c)
    (hx : Path .idle t x) (hxy : Step x o y) (ho : o.IsO) : ∃ c', SReach h s₀ (t ++ [o]) c' := by
  have hxc : x = c.pos := Path.det hx ht.path
  cases c with
  | idle s =>
    have h' : Step .idle o y := by rw [hxc] at hxy; exact hxy
    cases h' with | ask q => exact ⟨_, ht.snoc (.ask s q)⟩
  | run q p =>
    have h' : Step (.run q) o y := by rw [hxc] at hxy; exact hxy
    cases h' <;> exact False.elim ho
  | wait q m k =>
    have h' : Step (.wait q m) o y := by rw [hxc] at hxy; exact hxy
    cases h' with | reply _ _ n => exact ⟨_, ht.snoc (.reply q m k n)⟩

/-- **The strategy of a stateful component** from the initial state `s₀`. -/
def ofSBody (h : SBody S I X) (s₀ : S) : Strategy (nsig I) (nsig X) where
  plays := {t | ∃ c, SReach h s₀ t c}
  nil_mem := ⟨_, .nil⟩
  legal := fun ⟨_, hc⟩ => ⟨_, hc.path⟩
  of_prefix := fun ⟨_, hc⟩ hp => hc.of_prefix hp
  receptive := fun ⟨_, hc⟩ hx hxy ho => hc.receptive hx hxy ho

/-- The weakest precondition of a program under the theory `T` on the host's answers. -/
def Wp {A ST : Type} (T : Protocol ST WEv) : Prog (nsig I) A → (A → ST → Prop) → ST → Prop
  | .pure a, Q, qT => Q a qT
  | .call m k, Q, qT =>
    ∀ n qT', T.step qT (.imp m.1.1 m.2 n) = some qT' → Wp T (k n) Q qT'

/-- A return read as the answer of a host. -/
def retImp : WEv → Option WEv
  | .ret f a r => some (.imp f a r)
  | _ => none

/-- The export returns of an event list, read as answers. -/
def retAsImp (t : List WEv) : List WEv := t.filterMap retImp

/-- A guarantee on export returns: the theory `P` of a host, read on the returns. -/
def retG {SG : Type} (P : Protocol SG WEv) : Protocol SG WEv :=
  ⟨P.init, fun q e => match e with
    | .ret f a r => P.step q (.imp f a r)
    | _ => some q⟩

/-- Every export call `q` in a state satisfying `J` runs a program that, under `T`, returns
to a state satisfying `J`, with a return that `P` accepts. -/
structure WpInv {ST SG : Type} (h : SBody S I X) (s₀ : S) (T : Protocol ST WEv)
    (P : Protocol SG WEv) (J : S → ST → SG → Prop) : Prop where
  /-- The invariant holds initially. -/
  init : J s₀ T.init P.init
  /-- Every export call preserves it. -/
  call : ∀ s qT qG (q : (nsig X).Op), J s qT qG →
    Wp T (h s q) (fun a qT' => ∃ qG', P.step qG (.imp q.1.1 q.2 a.2) = some qG' ∧
      J a.1 qT' qG') qT

end Silmaril.Wasi.Versions
