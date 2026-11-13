module

public import Silmaril.Wasi.Versions.P2OverP3.Comp.Defs
public import Silmaril.Wasi.Versions.Stateful.Thms

/-!
# Proofs: the results of a program, whatever the answers

`Leaves p P`: every result `p` can return (for any answers of its calls) satisfies `P`.
`Wp.of_leaves`: a postcondition that only needs the result, and a predicate on the theory
state that every accepted answer preserves, give the weakest precondition.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Resource (Protocol)

/-- Every result of the program satisfies `P`, whatever the answers. -/
def Leaves {E : Sig.{0}} {A : Type} : Prog E A → (A → Prop) → Prop
  | .pure a, P => P a
  | .call _ k, P => ∀ n, Leaves (k n) P

variable {E : Sig.{0}} {A B : Type}

theorem leaves_pure {a : A} {P : A → Prop} (h : P a) : Leaves (E := E) (.pure a) P := h

/-- A predicate true of every value holds at every result. -/
theorem leaves_of {P : A → Prop} (h : ∀ a, P a) : ∀ p : Prog E A, Leaves p P
  | .pure a => h a
  | .call _ k => fun n => leaves_of h (k n)

/-- Monotonicity. -/
theorem Leaves.mono {P Q : A → Prop} (h : ∀ a, P a → Q a) :
    ∀ {p : Prog E A}, Leaves p P → Leaves p Q
  | .pure _, hp => h _ hp
  | .call _ _, hp => fun n => Leaves.mono h (hp n)

/-- Sequencing. -/
theorem leaves_bind {P : B → Prop} (f : A → Prog E B) :
    ∀ p : Prog E A, Leaves p (fun a => Leaves (f a) P) → Leaves (p.bind f) P
  | .pure _, h => h
  | .call _ k, h => fun n => leaves_bind f (k n) (h n)

/-- Sequencing after any program. -/
theorem leaves_bind_of {P : B → Prop} {f : A → Prog E B} (h : ∀ a, Leaves (f a) P)
    (p : Prog E A) : Leaves (p.bind f) P :=
  leaves_bind f p (leaves_of h p)

/-- **Weakest preconditions from results.** -/
theorem Wp.of_leaves {I : Set FnName} {ST : Type} {T : Protocol ST WEv} {R : ST → Prop}
    (hR : ∀ q e q', R q → T.step q e = some q' → R q') {P : A → Prop} {Q : A → ST → Prop}
    (hQ : ∀ a q, R q → P a → Q a q) :
    ∀ (p : Prog (nsig I) A) {qT : ST}, Leaves p P → R qT → Wp T p Q qT
  | .pure a, _, hp, hq => hQ a _ hq hp
  | .call _ k, _, hp, hq => fun n _ hn => Wp.of_leaves hR hQ (k n) (hp n) (hR _ _ _ hq hn)

end Silmaril.Wasi.Versions.P2OverP3
