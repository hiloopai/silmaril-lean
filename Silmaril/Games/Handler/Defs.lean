module

public import Silmaril.Games.Composition.Defs
public import Silmaril.Games.LTS.Defs

/-!
# Deterministic implementations: programs and handlers

* `Prog E A`: finite programs calling the operations of `E` and returning an
  `A` (the free monad of the signature, as an inductive type; every run
  terminates after finitely many calls).
* `Handler E F`: an implementation of each operation of `F` by a program
  over `E`. Handlers compose by interpretation (`Handler.comp`, diagrammatic
  order: `h₁.comp h₂` runs `h₂` and serves its calls with `h₁`); `Handler.id`
  forwards each operation; `Handler.ofHom` implements a renaming.
* `Strategy.ofHandler h`: the strategy of `h`, through the reduction
  semantics `Handler.toReduction h` in which each `F`-question runs its
  program afresh. `Silmaril.Games.Handler.Thms` shows that it maps handler
  composition to strategy composition.

The interaction trees of `Silmaril.Semantics.ITree` would give possibly infinite
programs; they are not used here. A possibly diverging program can be given a
strategy through `Strategy.ofLTS`/`Strategy.ofReduction` instead.
-/

@[expose] public section

namespace Silmaril.Games

universe u

/-- Finite programs over the signature `E` returning an `A`. -/
inductive Prog (E : Sig.{u}) (A : Type u) : Type u
  /-- Return a value. -/
  | pure (a : A)
  /-- Call `m` and continue with the answer. -/
  | call (m : E.Op) (k : E.Ar m → Prog E A)

namespace Prog

variable {E F : Sig.{u}} {A B : Type u}

/-- Sequential composition of programs. -/
def bind : Prog E A → (A → Prog E B) → Prog E B
  | pure a, f => f a
  | call m k, f => call m fun n => (k n).bind f

/-- Programs form a monad (the free monad of `E`). -/
instance : Monad (Prog E) where
  pure := pure
  bind := bind

/-- The program calling one operation and returning its answer. -/
def lift (m : E.Op) : Prog E (E.Ar m) := call m pure

end Prog

/-- An implementation of every operation of `F` by a program over `E`. -/
def Handler (E F : Sig.{u}) : Type u := (q : F.Op) → Prog E (F.Ar q)

/-- Run a program over `F`, implementing its calls with a handler. -/
def Prog.interp {E F : Sig.{u}} {A : Type u} (h : Handler E F) : Prog F A → Prog E A
  | pure a => pure a
  | call m k => (h m).bind fun n => (k n).interp h

namespace Handler

variable {E F G : Sig.{u}}

/-- Composition of handlers (diagrammatic order): run `h₂`, serving its calls
with `h₁`. -/
def comp (h₁ : Handler E F) (h₂ : Handler F G) : Handler E G := fun g => (h₂ g).interp h₁

/-- The forwarding handler. -/
protected def id (E : Sig.{u}) : Handler E E := fun m => Prog.lift m

/-- The handler implementing `E` by renaming its operations into `F`. -/
def ofHom (ρ : Sig.Hom E F) : Handler F E := fun m => .call (ρ.op m) fun n => .pure (ρ.ar m n)

/-- The copairing of two handlers with a common lower interface: each side
of the sum is implemented by its own handler. -/
def copair {F₁ F₂ : Sig.{u}} (h₁ : Handler E F₁) (h₂ : Handler E F₂) : Handler E (F₁ ⊕ₛ F₂)
  | .inl q => h₁ q
  | .inr q => h₂ q

/-- The sum of two handlers: each side is implemented on its own side. -/
def sumMap {F₁ F₂ G₁ G₂ : Sig.{u}} (h₁ : Handler F₁ G₁) (h₂ : Handler F₂ G₂) :
    Handler (F₁ ⊕ₛ F₂) (G₁ ⊕ₛ G₂)
  | .inl q => (h₁ q).interp (Handler.ofHom (Sig.Hom.inl F₁ F₂))
  | .inr q => (h₂ q).interp (Handler.ofHom (Sig.Hom.inr F₁ F₂))

/-- The reduction semantics of a handler: each question runs its program; a
program `call m k` calls `m` and continues with `k`, a program `pure r`
returns `r`. There are no internal steps. -/
def toReduction (h : Handler E F) : Reduction E F where
  Conf q := Prog E (F.Ar q)
  start := h
  step _ _ := False
  call P m k := P = .call m k
  done P r := P = .pure r

end Handler

/-- The strategy of a handler. -/
def Strategy.ofHandler {E F : Sig.{u}} (h : Handler E F) : Strategy E F :=
  Strategy.ofReduction h.toReduction

/-- Restriction of a strategy along a renaming `ρ : E → F`: only the
operations in the image of `ρ` are offered, renamed back. This is
post-composition with the strategy of `Handler.ofHom ρ`. -/
def Strategy.restrict {X E F : Sig.{u}} (σ : Strategy X F) (ρ : Sig.Hom E F) : Strategy X E :=
  σ.comp (Strategy.ofHandler (Handler.ofHom ρ))

end Silmaril.Games
