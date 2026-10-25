module

public import Silmaril.Logic.SetTheory.Formula

@[expose] public section

/-!
# The set-theoretic axioms of set.mm

Each axiom of set.mm is transcribed connective for connective as a semantic
formula over an arbitrary membership structure. Set variables are parameters of
an arbitrary variable type, and the wff metavariable of a scheme is an arbitrary
predicate on valuations. The disjoint-variable conditions of set.mm become
distinctness of variables and `Wff.NotFree` side conditions.

set.mm writes some axioms with defined connectives: `<->`, `/\`, `\/`, `E.`,
restricted quantifiers (`df-ral`, `df-rex`), and `C_` (`df-ss`). These are
interpreted by their definitions. The equinumerosity relation `~~` of `ax-groth`
is a parameter, since its set.mm definition goes through ordered pairs and
functions; `Silmaril.Logic.SetTheory.Equinumerous` identifies the intended
relation on `ZFSet`.

`ZF` bundles the axioms of ZF as stated in set.mm, `ZFC` adds `ax-ac`.
-/

namespace Silmaril.Logic.SetTheory

universe u v

namespace Axioms

open Wff

variable {M : Type u} [Membership M M] {V : Type v} [DecidableEq V]

/-- `ax-ext`: `|- ( A. z ( z e. x <-> z e. y ) -> x = y )`. -/
def ext (x y z : V) : Wff M V := imp (all z (iff (mem z x) (mem z y))) (eq x y)

/-- `ax-rep`: `|- ( A. w E. y A. z ( A. y ph -> z = y ) ->
E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) )`. -/
def rep (x y z w : V) (φ : Wff M V) : Wff M V :=
  imp (all w (ex y (all z (imp (all y φ) (eq z y)))))
    (ex y (all z (iff (mem z y) (ex w (and (mem w x) (all y φ))))))

/-- `ax-sep`: `|- E. y A. x ( x e. y <-> ( x e. z /\ ph ) )`. -/
def sep (x y z : V) (φ : Wff M V) : Wff M V :=
  ex y (all x (iff (mem x y) (and (mem x z) φ)))

/-- `ax-nul`: `|- E. x A. y -. y e. x`. -/
def nul (x y : V) : Wff M V := ex x (all y (not (mem y x)))

/-- `ax-pow`: `|- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y )`. -/
def pow (x y z w : V) : Wff M V :=
  ex y (all z (imp (all w (imp (mem w z) (mem w x))) (mem z y)))

/-- `ax-pr`: `|- E. z A. w ( ( w = x \/ w = y ) -> w e. z )`. -/
def pr (x y z w : V) : Wff M V := ex z (all w (imp (or (eq w x) (eq w y)) (mem w z)))

/-- `ax-un`: `|- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y )`. -/
def un (x y z w : V) : Wff M V :=
  ex y (all z (imp (ex w (and (mem z w) (mem w x))) (mem z y)))

/-- `ax-reg`: `|- ( E. y y e. x -> E. y ( y e. x /\ A. z ( z e. y -> -. z e. x ) ) )`. -/
def reg (x y z : V) : Wff M V :=
  imp (ex y (mem y x)) (ex y (and (mem y x) (all z (imp (mem z y) (not (mem z x))))))

/-- `ax-inf`: `|- E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) )`. -/
def inf (x y z w : V) : Wff M V :=
  ex y (and (mem x y) (all z (imp (mem z y) (ex w (and (mem z w) (mem w y))))))

/-- `ax-inf2`: `|- E. x ( E. y ( y e. x /\ A. z -. z e. y ) /\
A. y ( y e. x -> E. z ( z e. x /\ A. w ( w e. z <-> ( w e. y \/ w = y ) ) ) ) )`. -/
def inf2 (x y z w : V) : Wff M V :=
  ex x (and (ex y (and (mem y x) (all z (not (mem z y)))))
    (all y (imp (mem y x)
      (ex z (and (mem z x) (all w (iff (mem w z) (or (mem w y) (eq w y)))))))))

/-- `ax-ac`: `|- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t
( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) )`. -/
def ac (x y z w v u t : V) : Wff M V :=
  ex y (all z (all w (imp (and (mem z w) (mem w x))
    (ex v (all u (iff (ex t (and (and (mem u w) (mem w t)) (and (mem u t) (mem t y))))
      (eq u v)))))))

/-- `ax-ac2`: `|- E. y A. z E. v A. u ( ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\
z e. v ) ) ) \/ ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\
( ( u e. z /\ u e. y ) -> u = v ) ) ) ) )`. -/
def ac2 (x y z v u : V) : Wff M V :=
  ex y (all z (ex v (all u (or
    (and (mem y x) (imp (mem z y) (and (and (mem v x) (not (eq y v))) (mem z v))))
    (and (not (mem y x)) (imp (mem z x)
      (and (and (mem v z) (mem v y)) (imp (and (mem u z) (mem u y)) (eq u v)))))))))

/-- The body of `ax-groth` after `E. y`: `y` contains `x` and is a Tarski class,
with `~~` interpreted by `en`. -/
def grothBody (en : M → M → Prop) (x y z w v : V) : Wff M V :=
  and (and (mem x y)
      (ral z y (and (all w (imp (ss w z) (mem w y)))
        (rex w y (all v (imp (ss v z) (mem v w)))))))
    (all z (imp (ss z y) (or (rel en z y) (mem z y))))

/-- `ax-groth`: `|- E. y ( x e. y /\ A. z e. y ( A. w ( w C_ z -> w e. y ) /\
E. w e. y A. v ( v C_ z -> v e. w ) ) /\ A. z ( z C_ y -> ( z ~~ y \/ z e. y ) ) )`. -/
def groth (en : M → M → Prop) (x y z w v : V) : Wff M V := ex y (grothBody en x y z w v)

end Axioms

open Axioms

variable (M : Type u) [Membership M M] (V : Type v) [DecidableEq V]

/-- ZF as axiomatized by set.mm: every instance of its axiom schemes allowed by the
disjoint-variable conditions is valid. The restatement `ax-inf2` is included since set.mm
states it with `$a`. -/
structure ZF : Prop where
  ext : ∀ x y z : V, [x, y, z].Nodup → Valid (ext (M := M) x y z)
  rep : ∀ (x y z w : V) (φ : Wff M V), [x, y, z, w].Nodup → Valid (rep x y z w φ)
  sep : ∀ (x y z : V) (φ : Wff M V), [x, y, z].Nodup → Wff.NotFree y φ → Wff.NotFree z φ →
    Valid (sep x y z φ)
  nul : ∀ x y : V, Valid (nul (M := M) x y)
  pow : ∀ x y z w : V, [x, y, z, w].Nodup → Valid (pow (M := M) x y z w)
  pr : ∀ x y z w : V, [x, z, w].Nodup → [y, z, w].Nodup → Valid (pr (M := M) x y z w)
  un : ∀ x y z w : V, [x, y, z, w].Nodup → Valid (un (M := M) x y z w)
  reg : ∀ x y z : V, [x, y, z].Nodup → Valid (reg (M := M) x y z)
  inf : ∀ x y z w : V, [x, y, z, w].Nodup → Valid (inf (M := M) x y z w)
  inf2 : ∀ x y z w : V, [x, y, z, w].Nodup → Valid (inf2 (M := M) x y z w)

/-- ZFC as axiomatized by set.mm, with both `ax-ac` and its restatement `ax-ac2`. -/
structure ZFC : Prop extends ZF M V where
  ac : ∀ x y z w v u t : V, [x, y, z, w, v, u, t].Nodup → Valid (ac (M := M) x y z w v u t)
  ac2 : ∀ x y z v u : V, [x, y, z, v, u].Nodup → Valid (ac2 (M := M) x y z v u)

end Silmaril.Logic.SetTheory
