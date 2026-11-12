module

public import Silmaril.Libc.Contract.Sig.Defs

/-!
# Contracts, models, and contracts relative to an invariant

**A contract** for a signature `S` (`Contract S`) speaks about the ghost state `S.G` only:

* `init g`: the abstract states a valid start may show (the empty heap, nothing written yet);
* `pre f hf g a`: the call `f a` from the abstract state `g` is a **valid use** (POSIX-use
  preconditions: `free` of a live block or null, a power-of-two alignment, a format of the
  supported subset). Outside `pre` nothing is promised: after undefined behaviour, anything;
* `post f hf g a r g'`: the call may return `r` and leave the abstract state `g'`.

**A model** (`Model S`) is an implementation as a state machine: its states `St`, the valid start
states `init` (what loading and the C runtime set up), and for each function of `S` the outcomes
of a call: `some (t, r)` (it returns `r` in the state `t`) or `none` (a crash: a fault, an abort,
undefined behaviour inside the library). No outcome at all is a call that does not return:
**correctness only, not liveness** (`Returns` is the separate progress property used for
non-vacuity).

**A contract relative to an invariant** (`Holds M C I`): `I g s` relates the abstract state `g` to
the implementation state `s` (glibc's bins, a bump pointer, a `FILE` buffer). It holds when

* **setup**: every valid start state is related to some allowed initial abstract state;
* **safety**: under the invariant and the precondition, the call does not crash;
* **correctness and preservation**: every return keeps the invariant, for an abstract state the
  postcondition allows.

**Satisfaction** `Sat M C` hides the invariant: `∃ I, Holds M C I`. A client sees the signature
and the contract only, so any two models are interchangeable for it (`Inst`).

**Reducts and translations** along `σ : S ⟶ T`:

* `Contract.restrict σ : Contract T → Contract S`: the contract of the bigger signature,
  restricted to the smaller one (the functions of `S`; on the ghost: the precondition must hold
  for every bigger state that projects onto `g`, the postcondition for some). It is functorial
  (`Thms.restrict_id`, `Thms.restrict_comp`), and the restriction of a model's contract is met by
  the model's reduct (`Thms.Holds.restrict`).
* `Contract.map σ : Contract S → Contract T`: the institution's sentence translation (the same
  claims, read through the projection; nothing about the functions of `T` not in `S`).
* `Model.reduct σ : Model T → Model S`: forget the functions not in `S`.

**Tensor.** `Contract.tensor C D` and `Model.tensor M N` put two libraries side by side over
`Sig.tensor S T`: a call of `S` behaves as `C` says on the first ghost component and leaves the
second unchanged (the call does not touch the other library's state). `Thms.Holds.tensor`: for
disjoint function sets, the tensor of models meets the tensor of contracts, with the product of
the invariants.
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

variable {A : Api}

/-- **A contract** for the signature `S`: the allowed initial abstract states, and per function
a precondition (valid use) and a postcondition (result and new abstract state). -/
structure Contract (S : Sig A) : Type where
  /-- The abstract states a valid start may show. -/
  init : S.G → Prop
  /-- Valid use of `f` with the argument `a` from the abstract state `g`. -/
  pre : (f : A.Fn) → f ∈ S.F → S.G → A.Arg f → Prop
  /-- `post f hf g a r g'`: the call may return `r` and leave `g'`. -/
  post : (f : A.Fn) → f ∈ S.F → S.G → A.Arg f → A.Ret f → S.G → Prop

/-- **A model**: an implementation as a state machine. `step f hf s a o`: the call `f a` from
`s` may have the outcome `o` (`none`: a crash). -/
structure Model (S : Sig A) : Type 1 where
  /-- Implementation states. -/
  St : Type
  /-- Valid start states (after loading and the C runtime's setup). -/
  init : St → Prop
  /-- The outcomes of a call. -/
  step : (f : A.Fn) → f ∈ S.F → St → A.Arg f → Option (St × A.Ret f) → Prop

variable {S T : Sig A}

/-- **The contract `C` holds for `M` relative to the invariant `I`** (module doc): setup,
safety, correctness and preservation of the invariant. -/
structure Holds (M : Model S) (C : Contract S) (I : S.G → M.St → Prop) : Prop where
  /-- Setup: a valid start establishes the invariant for an allowed initial abstract state. -/
  init : ∀ s, M.init s → ∃ g, C.init g ∧ I g s
  /-- Safety: a valid use does not crash. -/
  safe : ∀ f hf g s a, I g s → C.pre f hf g a → ¬ M.step f hf s a none
  /-- Correctness and preservation of the invariant. -/
  post : ∀ f hf g s a t r, I g s → C.pre f hf g a → M.step f hf s a (some (t, r)) →
    ∃ g', I g' t ∧ C.post f hf g a r g'

/-- **Satisfaction**: the contract holds relative to some invariant, which stays hidden. -/
def Sat (M : Model S) (C : Contract S) : Prop := ∃ I, Holds M C I

/-- **Progress** (not part of the contract; used for non-vacuity): every valid use returns. -/
def Returns (M : Model S) (C : Contract S) (I : S.G → M.St → Prop) : Prop :=
  ∀ f hf g s a, I g s → C.pre f hf g a → ∃ t r, M.step f hf s a (some (t, r))

/-- **A non-vacuous contract**: some model with a start state meets it and always returns. -/
def Contract.NonVacuous (C : Contract S) : Prop :=
  ∃ (M : Model S) (I : S.G → M.St → Prop), Holds M C I ∧ Returns M C I ∧ ∃ s, M.init s

/-- The image of an invariant under a ghost projection: `g` is related to `s` when some bigger
abstract state projecting onto `g` is. -/
def push {St : Type} {G G' : Type} (p : G' → G) (I : G' → St → Prop) : G → St → Prop :=
  fun g s => ∃ g', p g' = g ∧ I g' s

namespace Contract

/-- **Refinement** `C ≤ D` (`Le C D`): `D` is at least as strong as `C` (fewer initial states, a
weaker precondition, a stronger postcondition where `C` makes a claim). -/
def Le (C D : Contract S) : Prop :=
  (∀ g, D.init g → C.init g) ∧ (∀ f hf g a, C.pre f hf g a → D.pre f hf g a) ∧
    ∀ f hf g a r g', C.pre f hf g a → D.post f hf g a r g' → C.post f hf g a r g'

/-- **The reduct of a contract** along `σ : S ⟶ T`: the contract of `T` on the functions of `S`.
The precondition must hold at every bigger abstract state over `g`, the initial states and the
postcondition are those of some bigger abstract state. -/
def restrict (σ : Sig.Hom S T) (C : Contract T) : Contract S where
  init g := ∃ g', σ.proj g' = g ∧ C.init g'
  pre f hf g a := ∀ g', σ.proj g' = g → C.pre f (σ.le hf) g' a
  post f hf g a r h := ∃ g' h', σ.proj g' = g ∧ σ.proj h' = h ∧ C.post f (σ.le hf) g' a r h'

/-- **Sentence translation** along `σ : S ⟶ T`: the claims of `C`, read through the projection;
no claim about the functions of `T` outside `S` (their precondition is false). -/
def map (σ : Sig.Hom S T) (C : Contract S) : Contract T where
  init g := C.init (σ.proj g)
  pre f _ g a := ∃ hf : f ∈ S.F, C.pre f hf (σ.proj g) a
  post f _ g a r h := ∀ hf : f ∈ S.F, C.post f hf (σ.proj g) a r (σ.proj h)

/-- **The tensor of contracts**: a call of one side behaves as its contract says on its ghost
component and leaves the other unchanged. -/
def tensor (C : Contract S) (D : Contract T) : Contract (Sig.tensor S T) where
  init g := C.init g.1 ∧ D.init g.2
  pre f _ g a := (∀ hf : f ∈ S.F, C.pre f hf g.1 a) ∧ (∀ hf : f ∈ T.F, D.pre f hf g.2 a)
  post f _ g a r h :=
    (∀ hf : f ∈ S.F, C.post f hf g.1 a r h.1) ∧ (f ∉ S.F → h.1 = g.1) ∧
      (∀ hf : f ∈ T.F, D.post f hf g.2 a r h.2) ∧ (f ∉ T.F → h.2 = g.2)

/-- The contract is **feasible**: some initial abstract state, and every valid use has a result
the postcondition allows. -/
def Feasible (C : Contract S) : Prop :=
  (∃ g, C.init g) ∧ ∀ f hf g a, C.pre f hf g a → ∃ r g', C.post f hf g a r g'

/-- **The canonical model** of a contract: its states are the abstract states, a valid use returns
as the postcondition allows, an invalid use may do anything. -/
def canon (C : Contract S) : Model S where
  St := S.G
  init := C.init
  step f hf g a o := ¬ C.pre f hf g a ∨ ∃ h r, o = some (h, r) ∧ C.post f hf g a r h

/-- **The contract of one function** over the ghost state `G`. -/
structure _root_.Silmaril.Libc.Contracts.FnSpec (A : Api) (G : Type) (f : A.Fn) : Type where
  /-- Valid use. -/
  pre : G → A.Arg f → Prop
  /-- Result and new abstract state. -/
  post : G → A.Arg f → A.Ret f → G → Prop

/-- **The contract of a table of function contracts** on the functions `F` (the table covers
every function of the API; only those of `F` count). The contracts of a hierarchy of signatures
over one ghost state are the same table on bigger and bigger sets (`Thms.restrict_ofTable`). -/
def ofTable (F : Set A.Fn) (G : Type) [Nonempty G] (init : G → Prop)
    (t : (f : A.Fn) → FnSpec A G f) : Contract (Sig.mk' F G) where
  init := init
  pre f _ := (t f).pre
  post f _ := (t f).post

end Contract

namespace Model

/-- **The reduct of a model** along `σ : S ⟶ T`: the functions of `S` only. -/
def reduct (σ : Sig.Hom S T) (M : Model T) : Model S where
  St := M.St
  init := M.init
  step f hf := M.step f (σ.le hf)

/-- **The tensor of models**: both states side by side; a call of `S` runs `M` and keeps `N`'s
state, a call of `T` only runs `N` and keeps `M`'s. -/
def tensor (M : Model S) (N : Model T) : Model (Sig.tensor S T) where
  St := M.St × N.St
  init s := M.init s.1 ∧ N.init s.2
  step f _ s a o :=
    (∃ hf : f ∈ S.F, ∃ o1, M.step f hf s.1 a o1 ∧ o = o1.map fun x => ((x.1, s.2), x.2)) ∨
      (f ∉ S.F ∧ ∃ hf : f ∈ T.F, ∃ o2, N.step f hf s.2 a o2 ∧ o = o2.map fun x => ((s.1, x.1), x.2))

end Model

end Silmaril.Libc.Contracts
