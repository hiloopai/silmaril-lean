module

public import Silmaril.Wasm.Behaviour.Relations
public import Silmaril.Wasm.Behaviour.Semantics.V1
public import Silmaril.Wasm.Behaviour.Semantics.Core

/-!
# Function equivalence and refinement inside a fixed store

The definitions of the module-refinement contract: two function addresses of one store
are *related* when invoking them on the same arguments gives `R`-related
behaviour sets, for `R` from the behavior-refinement hierarchy lattice
(`Silmaril/Wasm/Behaviour/Relations.lean`).

## One definition, two machines

V1 and Core 3.0 have different stores, different address types and different
value types, but the invocation boundary they expose is the same shape: a
well-formedness premise on an invocation and a behaviour set for it. That pair
is packaged as `Equiv.EntryPoints`, every definition and theorem below is stated
once over it, and `V1.Execution.entryPoints` / `Execution.Core.entryPoints`
instantiate it. The `V1.Execution.FunRefines` and `Execution.Core.FunRefines`
abbreviations at the end of the file give the per-machine spellings asked for in
the issue, with the shared proofs.

## The arity/type side condition is a hypothesis, not a field

`FunRefines` quantifies over the arguments accepted by `a`, so it says nothing
about arguments only `b` accepts. Reflexivity and `R`-monotonicity need nothing,
but **transitivity does**: chaining `a ⊑ b` with `b ⊑ c` needs `b` to accept the
arguments `a` accepts. That single premise is isolated as `OkMono`, and
`SameFuncType` (equal `FuncInst.type` at the two addresses) implies it on both
machines.

Keeping it a hypothesis rather than a field of `FunRefines` is what makes
`FunRefines` monotone in `R` by a bare `Behaviours.Refines.mono`, and keeps the
inclusion lattice free of side conditions. For the places where a genuine
preorder is wanted, `TypedFunRefines` bundles the two and *is* a preorder with no
side conditions at all.

## The kernel of the demonic lifting is coarser than equality

`Behaviour.trapRefines_antisymm` says `TrapRefines ∩ TrapRefinesᵒᵖ = Eq` on
single behaviours. **This does not lift to behaviour sets.** The demonic (∀∃)
lifting of an antisymmetric relation need not be antisymmetric:
`{returns vs, traps}` and `{returns vs}` refine each other but are different sets
(`Behaviours.not_antisymm_refines_trapRefines`). What is true is an exact
characterisation, `Behaviours.refines_trapRefines_iff_diff`, from which the kernel
comes out as *equality modulo traps*,
`Behaviours.refines_trapRefines_antisymm`, and equality on the nose only under a
determinism hypothesis (`Behaviours.eq_of_refines_trapRefines_of_subsingleton`).
The same holds one level up for `TrapRefinesDiv`, whose kernel is equality of the
*result-producing* behaviours — exactly partial correctness.

## Reachability

The issue asks for "∀ args, store states reachable in `M`". `Reach : S → Prop`
is left as a parameter, so a caller can instantiate it with "reachable from
instantiating `M`", with a typing judgement, or with `True`;
`FunRefinesOn`/`FunEquivOn` quantify over it and `FunRefinesOn.mono` records
that shrinking `Reach` *weakens* the relation.
-/

@[expose] public section

namespace Silmaril.Wasm

universe u v w

/-! ## The kernel of the demonic lifting

These are statements about `Behaviours.Refines` alone; they are what the
function-level antisymmetry results below are built from. -/

namespace Behaviours

open Behaviour

variable {V : Type u} {s t : Set (Behaviour V)}

/-- **Exact characterisation of set-level trap-insertion refinement.** `s`
refines `t` iff every non-trapping behaviour of `s` is already a behaviour of
`t`, and `t` has *something* to be refined to if `s` can trap. -/
theorem refines_trapRefines_iff_diff :
    Refines TrapRefines s t ↔ s \ {Behaviour.traps} ⊆ t ∧ (Behaviour.traps ∈ s → t.Nonempty) := by
  constructor
  · intro h
    refine ⟨fun b hb => ?_, fun hb => ?_⟩
    · obtain ⟨b', hb', hr⟩ := h b hb.1
      rcases hr with rfl | rfl
      · exact absurd rfl hb.2
      · exact hb'
    · obtain ⟨b', hb', _⟩ := h _ hb
      exact ⟨b', hb'⟩
  · rintro ⟨hsub, hne⟩ b hb
    by_cases hbt : b = Behaviour.traps
    · subst hbt
      obtain ⟨b', hb'⟩ := hne hb
      exact ⟨b', hb', Or.inl rfl⟩
    · exact ⟨b, hsub ⟨hb, hbt⟩, Or.inr rfl⟩

/-- **The kernel of set-level trap insertion is equality modulo traps.** This is
the honest lift of `Behaviour.trapRefines_antisymm`: antisymmetry survives only
after quotienting out the trap. -/
theorem refines_trapRefines_antisymm (h : Refines TrapRefines s t)
    (h' : Refines TrapRefines t s) :
    s \ {Behaviour.traps} = t \ {Behaviour.traps} := by
  rw [refines_trapRefines_iff_diff] at h h'
  exact Set.Subset.antisymm (fun b hb => ⟨h.1 hb, hb.2⟩) (fun b hb => ⟨h'.1 hb, hb.2⟩)

/-- Trap-insertion refinement is *not* antisymmetric on behaviour sets: the
demonic lifting of an antisymmetric relation need not be antisymmetric. -/
theorem not_antisymm_refines_trapRefines :
    ∃ s t : Set (Behaviour V), Refines TrapRefines s t ∧ Refines TrapRefines t s ∧ s ≠ t := by
  refine ⟨{Behaviour.returns [], Behaviour.traps}, {Behaviour.returns []}, ?_, ?_, ?_⟩
  · rintro b (rfl | rfl)
    · exact ⟨_, rfl, Or.inr rfl⟩
    · exact ⟨_, rfl, Or.inl rfl⟩
  · rintro b rfl
    exact ⟨_, Or.inl rfl, Or.inr rfl⟩
  · intro h
    have : (Behaviour.traps : Behaviour V) ∈ ({Behaviour.returns []} : Set (Behaviour V)) := by
      rw [← h]; exact Or.inr rfl
    cases this

/-- Antisymmetry *is* recovered on deterministic behaviour sets: two singletons
that refine each other are equal. -/
theorem eq_of_refines_trapRefines_of_subsingleton (hs : s.Subsingleton)
    (ht : t.Subsingleton) (h : Refines TrapRefines s t) (h' : Refines TrapRefines t s) :
    s = t := by
  refine Set.Subset.antisymm (fun b hb => ?_) (fun b hb => ?_)
  · obtain ⟨b', hb', hr⟩ := h b hb
    obtain ⟨b'', hb'', hr'⟩ := h' b' hb'
    cases hs hb hb''
    cases Behaviour.trapRefines_antisymm hr hr'
    exact hb'
  · obtain ⟨b', hb', hr⟩ := h' b hb
    obtain ⟨b'', hb'', hr'⟩ := h b' hb'
    cases ht hb hb''
    cases Behaviour.trapRefines_antisymm hr hr'
    exact hb'

/-- **Exact characterisation of set-level trap insertion modulo divergence.**
Only the result-producing behaviours are constrained. -/
theorem refines_trapRefinesDiv_iff :
    Refines TrapRefinesDiv s t ↔
      {b ∈ s | ¬ b.NoResult} ⊆ t ∧ ((∃ b ∈ s, b.NoResult) → t.Nonempty) := by
  constructor
  · intro h
    refine ⟨fun b hb => ?_, fun ⟨b, hb, _⟩ => ?_⟩
    · obtain ⟨b', hb', hr⟩ := h b hb.1
      rcases hr with hr | rfl
      · exact absurd hr hb.2
      · exact hb'
    · obtain ⟨b', hb', _⟩ := h b hb
      exact ⟨b', hb'⟩
  · rintro ⟨hsub, hne⟩ b hb
    by_cases hbn : b.NoResult
    · obtain ⟨b', hb'⟩ := hne ⟨b, hb, hbn⟩
      exact ⟨b', hb', Or.inl hbn⟩
    · exact ⟨b, hsub ⟨hb, hbn⟩, Or.inr rfl⟩

/-- **The kernel of set-level trap insertion modulo divergence is agreement on
results**: exactly the partial-correctness equivalence. -/
theorem refines_trapRefinesDiv_antisymm (h : Refines TrapRefinesDiv s t)
    (h' : Refines TrapRefinesDiv t s) :
    {b ∈ s | ¬ b.NoResult} = {b ∈ t | ¬ b.NoResult} := by
  rw [refines_trapRefinesDiv_iff] at h h'
  exact Set.Subset.antisymm (fun b hb => ⟨h.1 hb, hb.2⟩) (fun b hb => ⟨h'.1 hb, hb.2⟩)

end Behaviours

/-! ## Entry points -/

namespace Equiv

variable {S : Type u} {A : Type v} {V : Type w}

/-- The invocation boundary an interpretation exposes: which invocations are
well formed, and what they may do. V1 and Core 3.0 both instantiate it, and
every definition in this file is stated over it once. -/
structure EntryPoints (S : Type u) (A : Type v) (V : Type w) where
  /-- The well-formedness premise of an invocation (`InvokeOk`). -/
  Ok : S → A → List V → Prop
  /-- The behaviours of an invocation (`behaviours`). -/
  beh : S → A → List V → Set (Behaviour V)

variable (E : EntryPoints S A V) (R R' : Behaviour V → Behaviour V → Prop)

/-- `b` accepts every argument list `a` accepts. This is the arity/type side
condition in the exact form the theorems need. -/
def OkMono (s : S) (a b : A) : Prop := ∀ vs, E.Ok s a vs → E.Ok s b vs

variable {E} in
theorem OkMono.refl (s : S) (a : A) : OkMono E s a a := fun _ h => h

variable {E} in
theorem OkMono.trans {s : S} {a b c : A} (h : OkMono E s a b) (h' : OkMono E s b c) :
    OkMono E s a c := fun vs hv => h' vs (h vs hv)

/-! ## Function refinement and equivalence at a fixed store -/

/-- **Function refinement.** Every behaviour of invoking `a` in `s` is
`R`-related to one of invoking `b`, on every argument list `a` accepts. -/
def FunRefines (s : S) (a b : A) : Prop :=
  ∀ vs, E.Ok s a vs → Behaviours.Refines R (E.beh s a vs) (E.beh s b vs)

/-- **Function equivalence**: the two-sided version, in the shape of
`Behaviours.Equiv`. -/
def FunEquiv (s : S) (a b : A) : Prop :=
  FunRefines E R s a b ∧ FunRefines E (fun x y => R y x) s b a

variable {E R R'}

/-- A reading of `FunEquiv` as `Behaviours.Equiv` at every argument list, under
the side condition that `a` and `b` accept the same arguments. -/
theorem funEquiv_iff_behavioursEquiv {s : S} {a b : A} (hok : ∀ vs, E.Ok s a vs ↔ E.Ok s b vs) :
    FunEquiv E R s a b ↔ ∀ vs, E.Ok s a vs → Behaviours.Equiv R (E.beh s a vs) (E.beh s b vs) := by
  constructor
  · rintro ⟨h₁, h₂⟩ vs hv
    exact ⟨h₁ vs hv, h₂ vs ((hok vs).mp hv)⟩
  · intro h
    exact ⟨fun vs hv => (h vs hv).1, fun vs hv => (h vs ((hok vs).mpr hv)).2⟩

/-- When `R` is symmetric, `FunEquiv R` is literally `FunRefines R` intersected
with its opposite. -/
theorem funEquiv_iff_of_symm (hR : ∀ x y, R x y → R y x) {s : S} {a b : A} :
    FunEquiv E R s a b ↔ FunRefines E R s a b ∧ FunRefines E R s b a := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩ <;>
    exact fun vs hv => Behaviours.Refines.mono (fun _ _ => hR _ _) (h.2 vs hv)

/-! ### Order-theoretic structure -/

/-- Reflexivity, from reflexivity of `R`. -/
theorem FunRefines.refl (hR : ∀ b, R b b) (s : S) (a : A) : FunRefines E R s a a :=
  fun _ _ b hb => ⟨b, hb, hR b⟩

/-- Transitivity, from transitivity of `R` — **and** the side condition that `b`
accepts the arguments `a` accepts. -/
theorem FunRefines.trans (hR : ∀ x y z, R x y → R y z → R x z) {s : S} {a b c : A}
    (hok : OkMono E s a b) (h : FunRefines E R s a b) (h' : FunRefines E R s b c) :
    FunRefines E R s a c :=
  fun vs hv => Behaviours.Refines.trans hR (h vs hv) (h' vs (hok vs hv))

/-- **Monotonicity in the relation**: the behavior-refinement hierarchy lattice lifts to functions. -/
theorem FunRefines.mono (hRR' : ∀ x y, R x y → R' x y) {s : S} {a b : A}
    (h : FunRefines E R s a b) : FunRefines E R' s a b :=
  fun vs hv => Behaviours.Refines.mono hRR' (h vs hv)

/-- `FunEquiv` projects to `FunRefines`. -/
theorem FunEquiv.refines {s : S} {a b : A} (h : FunEquiv E R s a b) : FunRefines E R s a b := h.1

/-- The opposite half of `FunEquiv`. -/
theorem FunEquiv.refines_op {s : S} {a b : A} (h : FunEquiv E R s a b) :
    FunRefines E (fun x y => R y x) s b a := h.2

/-- Reflexivity of `FunEquiv`. -/
theorem FunEquiv.refl (hR : ∀ b, R b b) (s : S) (a : A) : FunEquiv E R s a a :=
  ⟨FunRefines.refl hR s a, FunRefines.refl (R := fun x y => R y x) hR s a⟩

/-- Symmetry of `FunEquiv`, with **no** side condition: swapping the two halves
is exactly swapping `R` for its opposite. -/
theorem FunEquiv.symm {s : S} {a b : A} (h : FunEquiv E R s a b) :
    FunEquiv E (fun x y => R y x) s b a := ⟨h.2, h.1⟩

/-- Symmetry of `FunEquiv` for a symmetric `R`. -/
theorem FunEquiv.symm' (hR : ∀ x y, R x y → R y x) {s : S} {a b : A}
    (h : FunEquiv E R s a b) : FunEquiv E R s b a :=
  (funEquiv_iff_of_symm hR).mpr ((funEquiv_iff_of_symm hR).mp h).symm

/-- Transitivity of `FunEquiv`, from transitivity of `R` and the side condition
in both directions. -/
theorem FunEquiv.trans (hR : ∀ x y z, R x y → R y z → R x z) {s : S} {a b c : A}
    (hab : OkMono E s a b) (hcb : OkMono E s c b) (h : FunEquiv E R s a b)
    (h' : FunEquiv E R s b c) : FunEquiv E R s a c :=
  ⟨FunRefines.trans hR hab h.1 h'.1,
   FunRefines.trans (fun x y z hxy hyz => hR z y x hyz hxy) hcb h'.2 h.2⟩

/-- Monotonicity of `FunEquiv` in the relation. -/
theorem FunEquiv.mono (hRR' : ∀ x y, R x y → R' x y) {s : S} {a b : A}
    (h : FunEquiv E R s a b) : FunEquiv E R' s a b :=
  ⟨h.1.mono hRR', h.2.mono (fun x y h => hRR' y x h)⟩

/-- `FunEquiv Eq` is behaviour-set equality at every accepted argument list. -/
theorem funEquiv_eq_iff {s : S} {a b : A} (hok : ∀ vs, E.Ok s a vs ↔ E.Ok s b vs) :
    FunEquiv E (· = ·) s a b ↔ ∀ vs, E.Ok s a vs → E.beh s a vs = E.beh s b vs := by
  rw [funEquiv_iff_behavioursEquiv hok]
  exact forall_congr' fun vs => imp_congr_right fun _ => Behaviours.equiv_eq_iff

/-- `FunRefines Eq` is behaviour-set inclusion at every accepted argument list. -/
theorem funRefines_eq_iff {s : S} {a b : A} :
    FunRefines E (· = ·) s a b ↔ ∀ vs, E.Ok s a vs → E.beh s a vs ⊆ E.beh s b vs :=
  forall_congr' fun _ => imp_congr_right fun _ => Behaviours.refines_eq_iff

/-! ### The bundled preorder

`TypedFunRefines` carries the side condition, and is a preorder with no
hypotheses beyond those on `R`. -/

variable (E R) in
/-- `FunRefines` together with its arity side condition. -/
def TypedFunRefines (s : S) (a b : A) : Prop := OkMono E s a b ∧ FunRefines E R s a b

/-- `TypedFunRefines` is reflexive. -/
theorem TypedFunRefines.refl (hR : ∀ b, R b b) (s : S) (a : A) : TypedFunRefines E R s a a :=
  ⟨OkMono.refl s a, FunRefines.refl hR s a⟩

/-- `TypedFunRefines` is transitive, with **no** extra side condition. -/
theorem TypedFunRefines.trans (hR : ∀ x y z, R x y → R y z → R x z) {s : S} {a b c : A}
    (h : TypedFunRefines E R s a b) (h' : TypedFunRefines E R s b c) :
    TypedFunRefines E R s a c :=
  ⟨h.1.trans h'.1, FunRefines.trans hR h.1 h.2 h'.2⟩

/-- `TypedFunRefines` is monotone in the relation. -/
theorem TypedFunRefines.mono (hRR' : ∀ x y, R x y → R' x y) {s : S} {a b : A}
    (h : TypedFunRefines E R s a b) : TypedFunRefines E R' s a b := ⟨h.1, h.2.mono hRR'⟩

/-! ### The inclusion lattice of the behavior-refinement hierarchy

```
          FunRefines Eq  ⊆  FunRefines TrapRefines
                ∩                     ∩
       FunRefines TrapDiv ⊆ FunRefines TrapRefinesDiv
```
Each inclusion is `FunRefines.mono` applied to the corresponding inclusion of
`Silmaril/Wasm/Behaviour/Relations.lean`. -/

variable (E) in
/-- `Eq ⊆ TrapRefines`. -/
theorem funRefines_trapRefines_of_eq {s : S} {a b : A} (h : FunRefines E (· = ·) s a b) :
    FunRefines E Behaviour.TrapRefines s a b :=
  h.mono fun _ _ => Behaviour.TrapRefines.of_eq

variable (E) in
/-- `Eq ⊆ TrapDiv`. -/
theorem funRefines_trapDiv_of_eq {s : S} {a b : A} (h : FunRefines E (· = ·) s a b) :
    FunRefines E Behaviour.TrapDiv s a b :=
  h.mono fun _ _ => Behaviour.TrapDiv.of_eq

variable (E) in
/-- `TrapRefines ⊆ TrapRefinesDiv`. -/
theorem funRefines_trapRefinesDiv_of_trapRefines {s : S} {a b : A}
    (h : FunRefines E Behaviour.TrapRefines s a b) :
    FunRefines E Behaviour.TrapRefinesDiv s a b :=
  h.mono fun _ _ => Behaviour.TrapRefines.trapRefinesDiv

variable (E) in
/-- `TrapDiv ⊆ TrapRefinesDiv`. -/
theorem funRefines_trapRefinesDiv_of_trapDiv {s : S} {a b : A}
    (h : FunRefines E Behaviour.TrapDiv s a b) :
    FunRefines E Behaviour.TrapRefinesDiv s a b :=
  h.mono fun _ _ => Behaviour.TrapDiv.trapRefinesDiv

variable (E) in
/-- `Eq ⊆ TrapRefinesDiv`, the diagonal of the square. -/
theorem funRefines_trapRefinesDiv_of_eq {s : S} {a b : A} (h : FunRefines E (· = ·) s a b) :
    FunRefines E Behaviour.TrapRefinesDiv s a b :=
  funRefines_trapRefinesDiv_of_trapRefines E (funRefines_trapRefines_of_eq E h)

variable (E) in
/-- `FunEquiv Eq ⊆ FunRefines TrapRefines`: an equivalence of functions is in
particular a refinement. -/
theorem funRefines_trapRefines_of_funEquiv_eq {s : S} {a b : A}
    (h : FunEquiv E (· = ·) s a b) : FunRefines E Behaviour.TrapRefines s a b :=
  funRefines_trapRefines_of_eq E h.1

variable (E) in
/-- `FunEquiv Eq ⊆ FunEquiv TrapDiv`. -/
theorem funEquiv_trapDiv_of_eq {s : S} {a b : A} (h : FunEquiv E (· = ·) s a b) :
    FunEquiv E Behaviour.TrapDiv s a b :=
  h.mono fun _ _ => Behaviour.TrapDiv.of_eq

/-! ### Antisymmetry

The honest lift of `Behaviour.trapRefines_antisymm`: two-sided trap-insertion
refinement of functions identifies their behaviour sets *modulo traps*, not on
the nose. See the module docstring. -/

/-- The kernel of `FunRefines TrapRefines` is agreement modulo traps. -/
theorem FunRefines.trapRefines_antisymm {s : S} {a b : A} (hok : OkMono E s a b)
    (h : FunRefines E Behaviour.TrapRefines s a b)
    (h' : FunRefines E Behaviour.TrapRefines s b a) (vs : List V) (hv : E.Ok s a vs) :
    E.beh s a vs \ {Behaviour.traps} = E.beh s b vs \ {Behaviour.traps} :=
  Behaviours.refines_trapRefines_antisymm (h vs hv) (h' vs (hok vs hv))

/-- The kernel of `FunRefines TrapRefinesDiv` is agreement on results. -/
theorem FunRefines.trapRefinesDiv_antisymm {s : S} {a b : A} (hok : OkMono E s a b)
    (h : FunRefines E Behaviour.TrapRefinesDiv s a b)
    (h' : FunRefines E Behaviour.TrapRefinesDiv s b a) (vs : List V) (hv : E.Ok s a vs) :
    {x ∈ E.beh s a vs | ¬ x.NoResult} = {x ∈ E.beh s b vs | ¬ x.NoResult} :=
  Behaviours.refines_trapRefinesDiv_antisymm (h vs hv) (h' vs (hok vs hv))

/-- On deterministic entry points, two-sided trap-insertion refinement **is**
behaviour-set equality. -/
theorem FunRefines.eq_of_trapRefines_antisymm {s : S} {a b : A} (hok : OkMono E s a b)
    (hdet : ∀ vs, (E.beh s a vs).Subsingleton ∧ (E.beh s b vs).Subsingleton)
    (h : FunRefines E Behaviour.TrapRefines s a b)
    (h' : FunRefines E Behaviour.TrapRefines s b a) (vs : List V) (hv : E.Ok s a vs) :
    E.beh s a vs = E.beh s b vs :=
  Behaviours.eq_of_refines_trapRefines_of_subsingleton (hdet vs).1 (hdet vs).2
    (h vs hv) (h' vs (hok vs hv))

/-! ### The bottom element: a function that always traps -/

variable (E) in
/-- The address `a` can only trap, on every argument list it accepts. -/
def AlwaysTraps (s : S) (a : A) : Prop :=
  ∀ vs, E.Ok s a vs → E.beh s a vs ⊆ Behaviours.alwaysTraps

/-- **Bottom.** An always-trapping function refines every function that accepts
its arguments and has *some* behaviour on them. The nonemptiness premise is
real: a stuck configuration has an empty behaviour set, and nothing refines the
empty set under the demonic lifting. -/
theorem AlwaysTraps.funRefines {s : S} {a b : A} (h : AlwaysTraps E s a)
    (hok : OkMono E s a b) (hne : ∀ vs, E.Ok s b vs → (E.beh s b vs).Nonempty) :
    FunRefines E Behaviour.TrapRefines s a b := by
  intro vs hv x hx
  cases h vs hv hx
  exact Behaviours.trapRefines_alwaysTraps (hne vs (hok vs hv)) _ rfl

/-! ## Quantifying over reachable stores

The issue's "∀ args, store states reachable in `M`". `Reach` is a parameter so
that the caller fixes the meaning of "reachable". -/

variable (E R)

/-- `FunRefines` at every store satisfying `Reach`. -/
def FunRefinesOn (Reach : S → Prop) (a b : A) : Prop := ∀ s, Reach s → FunRefines E R s a b

/-- `FunEquiv` at every store satisfying `Reach`. -/
def FunEquivOn (Reach : S → Prop) (a b : A) : Prop := ∀ s, Reach s → FunEquiv E R s a b

variable {E R}

/-- **Shrinking `Reach` weakens the relation.** -/
theorem FunRefinesOn.mono {Reach Reach' : S → Prop} (hle : ∀ s, Reach' s → Reach s) {a b : A}
    (h : FunRefinesOn E R Reach a b) : FunRefinesOn E R Reach' a b :=
  fun s hs => h s (hle s hs)

/-- **Shrinking `Reach` weakens the relation**, two-sided version. -/
theorem FunEquivOn.mono {Reach Reach' : S → Prop} (hle : ∀ s, Reach' s → Reach s) {a b : A}
    (h : FunEquivOn E R Reach a b) : FunEquivOn E R Reach' a b :=
  fun s hs => h s (hle s hs)

/-- `FunRefinesOn` is monotone in the relation too. -/
theorem FunRefinesOn.mono_rel (hRR' : ∀ x y, R x y → R' x y) {Reach : S → Prop} {a b : A}
    (h : FunRefinesOn E R Reach a b) : FunRefinesOn E R' Reach a b :=
  fun s hs => (h s hs).mono hRR'

/-- Reflexivity at every reachable store. -/
theorem FunRefinesOn.refl (hR : ∀ b, R b b) (Reach : S → Prop) (a : A) :
    FunRefinesOn E R Reach a a := fun s _ => FunRefines.refl hR s a

/-- Transitivity at every reachable store. -/
theorem FunRefinesOn.trans (hR : ∀ x y z, R x y → R y z → R x z) {Reach : S → Prop} {a b c : A}
    (hok : ∀ s, Reach s → OkMono E s a b) (h : FunRefinesOn E R Reach a b)
    (h' : FunRefinesOn E R Reach b c) : FunRefinesOn E R Reach a c :=
  fun s hs => FunRefines.trans hR (hok s hs) (h s hs) (h' s hs)

/-- `FunRefinesOn` at the trivially true `Reach` is `FunRefines` at every
store. -/
theorem funRefinesOn_true_iff {a b : A} :
    FunRefinesOn E R (fun _ => True) a b ↔ ∀ s, FunRefines E R s a b :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

end Equiv

/-! ## The WebAssembly 1.0 instance -/

namespace V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type}

/-- The V1 invocation boundary: `InvokeOk` and `behaviours`. -/
def entryPoints (host : HostSemantics H) :
    Equiv.EntryPoints (Store H) FuncAddr Runtime.Value where
  Ok := InvokeOk
  beh := behaviours host

@[simp] theorem entryPoints_Ok (host : HostSemantics H) (s : Store H) (a : FuncAddr)
    (vs : List Runtime.Value) : (entryPoints host).Ok s a vs = InvokeOk s a vs := rfl

@[simp] theorem entryPoints_beh (host : HostSemantics H) (s : Store H) (a : FuncAddr)
    (vs : List Runtime.Value) : (entryPoints host).beh s a vs = behaviours host s a vs := rfl

/-- The two addresses hold function instances of the same type (or both hold
none). This is the side condition of the issue, in the form the theorems use. -/
def SameFuncType (s : Store H) (a b : FuncAddr) : Prop :=
  (s.funcs[a.value]?.map FuncInst.type) = (s.funcs[b.value]?.map FuncInst.type)

theorem SameFuncType.refl (s : Store H) (a : FuncAddr) : SameFuncType s a a := rfl

theorem SameFuncType.symm {s : Store H} {a b : FuncAddr} (h : SameFuncType s a b) :
    SameFuncType s b a := Eq.symm h

theorem SameFuncType.trans {s : Store H} {a b c : FuncAddr} (h : SameFuncType s a b)
    (h' : SameFuncType s b c) : SameFuncType s a c := Eq.trans h h'

/-- Equal function types means equal accepted argument lists: the side condition
of `Equiv.FunRefines.trans`. -/
theorem SameFuncType.invokeOk {s : Store H} {a b : FuncAddr} (h : SameFuncType s a b)
    {vs : List Runtime.Value} (hv : InvokeOk s a vs) : InvokeOk s b vs := by
  obtain ⟨fn, hfn, ht⟩ := hv
  rw [SameFuncType, hfn] at h
  simp only [Option.map_some] at h
  obtain ⟨fn', hfn', ht'⟩ := Option.map_eq_some_iff.mp h.symm
  exact ⟨fn', hfn', ht.trans (congrArg FuncType.params ht'.symm)⟩

/-- `SameFuncType` gives the `OkMono` premise. -/
theorem SameFuncType.okMono {host : HostSemantics H} {s : Store H} {a b : FuncAddr}
    (h : SameFuncType s a b) : Equiv.OkMono (entryPoints host) s a b :=
  fun _ hv => h.invokeOk hv

/-- **Function refinement in V1**, in the spelling of the module-refinement contract. -/
abbrev FunRefines (R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop)
    (host : HostSemantics H) (s : Store H) (a b : FuncAddr) : Prop :=
  Equiv.FunRefines (entryPoints host) R s a b

/-- **Function equivalence in V1**, in the spelling of the module-refinement contract. -/
abbrev FunEquiv (R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop)
    (host : HostSemantics H) (s : Store H) (a b : FuncAddr) : Prop :=
  Equiv.FunEquiv (entryPoints host) R s a b

/-- **Function refinement in V1 at every reachable store.** -/
abbrev FunRefinesOn (R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop)
    (host : HostSemantics H) (Reach : Store H → Prop) (a b : FuncAddr) : Prop :=
  Equiv.FunRefinesOn (entryPoints host) R Reach a b

/-- **Function equivalence in V1 at every reachable store.** -/
abbrev FunEquivOn (R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop)
    (host : HostSemantics H) (Reach : Store H → Prop) (a b : FuncAddr) : Prop :=
  Equiv.FunEquivOn (entryPoints host) R Reach a b

/-- Unfolding `FunRefines` to the statement of the issue. -/
theorem funRefines_iff {R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop}
    {host : HostSemantics H} {s : Store H} {a b : FuncAddr} :
    FunRefines R host s a b ↔
      ∀ vs, InvokeOk s a vs →
        Behaviours.Refines R (behaviours host s a vs) (behaviours host s b vs) := Iff.rfl

/-- V1 transitivity, with the type side condition. -/
theorem FunRefines.trans' {R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop}
    (hR : ∀ x y z, R x y → R y z → R x z) {host : HostSemantics H} {s : Store H}
    {a b c : FuncAddr} (hab : SameFuncType s a b) (h : FunRefines R host s a b)
    (h' : FunRefines R host s b c) : FunRefines R host s a c :=
  Equiv.FunRefines.trans hR hab.okMono h h'

/-- V1 `FunEquiv` is transitive, with the type side condition. -/
theorem FunEquiv.trans' {R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop}
    (hR : ∀ x y z, R x y → R y z → R x z) {host : HostSemantics H} {s : Store H}
    {a b c : FuncAddr} (hab : SameFuncType s a b) (hcb : SameFuncType s c b)
    (h : FunEquiv R host s a b) (h' : FunEquiv R host s b c) : FunEquiv R host s a c :=
  Equiv.FunEquiv.trans hR hab.okMono hcb.okMono h h'

/-- V1 `FunEquiv Eq` is behaviour-set equality on every well-typed argument
list. This is the form the demo of separate function-equivalence examples (not included in this package) proves. -/
theorem funEquiv_eq_iff' {host : HostSemantics H} {s : Store H} {a b : FuncAddr}
    (hab : SameFuncType s a b) :
    FunEquiv (· = ·) host s a b ↔
      ∀ vs, InvokeOk s a vs → behaviours host s a vs = behaviours host s b vs :=
  Equiv.funEquiv_eq_iff
    (fun _ => ⟨fun h => hab.invokeOk h, fun h => hab.symm.invokeOk h⟩)

/-- Equal behaviour sets give refinement at any reflexive relation: the bridge
from a concrete execution theorem to `FunRefines`. -/
theorem funRefines_of_behaviours_eq {R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop}
    (hR : ∀ b, R b b) {host : HostSemantics H} {s : Store H} {a b : FuncAddr}
    (h : ∀ vs, InvokeOk s a vs → behaviours host s a vs = behaviours host s b vs) :
    FunRefines R host s a b := by
  intro vs hv x hx
  refine ⟨x, ?_, hR x⟩
  show x ∈ behaviours host s b vs
  rw [← h vs hv]
  exact hx

end V1.Execution

/-! ## The Core 3.0 instance -/

namespace Execution.Core

open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- The Core 3.0 invocation boundary: `InvokeOk` and `behaviours`. -/
def entryPoints (P : Profile) (host : HostSemantics H) :
    Equiv.EntryPoints (Store H) Nat Val where
  Ok := InvokeOk
  beh := behaviours P host

@[simp] theorem entryPoints_Ok (P : Profile) (host : HostSemantics H) (s : Store H) (a : Nat)
    (vs : List Val) : (entryPoints P host).Ok s a vs = InvokeOk s a vs := rfl

@[simp] theorem entryPoints_beh (P : Profile) (host : HostSemantics H) (s : Store H) (a : Nat)
    (vs : List Val) : (entryPoints P host).beh s a vs = behaviours P host s a vs := rfl

/-- The two addresses hold function instances of the same `DefType`. -/
def SameFuncType (s : Store H) (a b : Nat) : Prop :=
  (s.funcs[a]?.map FuncInst.type) = (s.funcs[b]?.map FuncInst.type)

theorem SameFuncType.refl (s : Store H) (a : Nat) : SameFuncType s a a := rfl

theorem SameFuncType.symm {s : Store H} {a b : Nat} (h : SameFuncType s a b) :
    SameFuncType s b a := Eq.symm h

theorem SameFuncType.trans {s : Store H} {a b c : Nat} (h : SameFuncType s a b)
    (h' : SameFuncType s b c) : SameFuncType s a c := Eq.trans h h'

/-- Equal `DefType`s means equal accepted argument lists. -/
theorem SameFuncType.invokeOk {s : Store H} {a b : Nat} (h : SameFuncType s a b)
    {vs : List Val} (hv : InvokeOk s a vs) : InvokeOk s b vs := by
  obtain ⟨fi, ps, rs, hfi, hex, hok⟩ := hv
  rw [SameFuncType, hfi] at h
  simp only [Option.map_some] at h
  obtain ⟨fi', hfi', ht'⟩ := Option.map_eq_some_iff.mp h.symm
  exact ⟨fi', ps, rs, hfi', by rw [ht']; exact hex, hok⟩

/-- `SameFuncType` gives the `OkMono` premise. -/
theorem SameFuncType.okMono {P : Profile} {host : HostSemantics H} {s : Store H} {a b : Nat}
    (h : SameFuncType s a b) : Equiv.OkMono (entryPoints P host) s a b :=
  fun _ hv => h.invokeOk hv

/-- **Function refinement in Core 3.0.** -/
abbrev FunRefines (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (s : Store H) (a b : Nat) : Prop :=
  Equiv.FunRefines (entryPoints P host) R s a b

/-- **Function equivalence in Core 3.0.** -/
abbrev FunEquiv (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (s : Store H) (a b : Nat) : Prop :=
  Equiv.FunEquiv (entryPoints P host) R s a b

/-- **Function refinement in Core 3.0 at every reachable store.** -/
abbrev FunRefinesOn (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (Reach : Store H → Prop) (a b : Nat) : Prop :=
  Equiv.FunRefinesOn (entryPoints P host) R Reach a b

/-- **Function equivalence in Core 3.0 at every reachable store.** -/
abbrev FunEquivOn (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (Reach : Store H → Prop) (a b : Nat) : Prop :=
  Equiv.FunEquivOn (entryPoints P host) R Reach a b

/-- Unfolding `FunRefines` to the statement of the issue. -/
theorem funRefines_iff {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {host : HostSemantics H} {s : Store H} {a b : Nat} :
    FunRefines R P host s a b ↔
      ∀ vs, InvokeOk s a vs →
        Behaviours.Refines R (behaviours P host s a vs) (behaviours P host s b vs) := Iff.rfl

/-- Core transitivity, with the type side condition. -/
theorem FunRefines.trans' {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ x y z, R x y → R y z → R x z) {P : Profile} {host : HostSemantics H} {s : Store H}
    {a b c : Nat} (hab : SameFuncType s a b) (h : FunRefines R P host s a b)
    (h' : FunRefines R P host s b c) : FunRefines R P host s a c :=
  Equiv.FunRefines.trans hR hab.okMono h h'

/-- Core `FunEquiv` is transitive, with the type side condition. -/
theorem FunEquiv.trans' {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ x y z, R x y → R y z → R x z) {P : Profile} {host : HostSemantics H} {s : Store H}
    {a b c : Nat} (hab : SameFuncType s a b) (hcb : SameFuncType s c b)
    (h : FunEquiv R P host s a b) (h' : FunEquiv R P host s b c) : FunEquiv R P host s a c :=
  Equiv.FunEquiv.trans hR hab.okMono hcb.okMono h h'

/-- Core `FunEquiv Eq` is behaviour-set equality on every well-typed argument
list. -/
theorem funEquiv_eq_iff' {P : Profile} {host : HostSemantics H} {s : Store H} {a b : Nat}
    (hab : SameFuncType s a b) :
    FunEquiv (· = ·) P host s a b ↔
      ∀ vs, InvokeOk s a vs → behaviours P host s a vs = behaviours P host s b vs :=
  Equiv.funEquiv_eq_iff
    (fun _ => ⟨fun h => hab.invokeOk h, fun h => hab.symm.invokeOk h⟩)

end Execution.Core

end Silmaril.Wasm
