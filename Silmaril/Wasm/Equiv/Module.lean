module

public import Silmaril.Wasm.Equiv.Function
public import Silmaril.Wasm.V1.Execution.Inversion
public import Silmaril.Wasm.V1.Execution.Properties

/-!
# Module-level equivalence and the replacement congruence

The store-level half of the module-refinement contract, which is the closed-program
instance of the contextual-refinement contract: `ModuleRefines R host s s'` says that every
behaviour of every well-formed invocation in `s` is `R`-related to one in `s'`.
It is stated once over `Equiv.EntryPoints` and instantiated for V1 and Core 3.0,
exactly as `Silmaril/Wasm/Equiv/Function.lean` does for function addresses.

## Replacement

`Store.replaceFunc s a b` is the store in which the function instance at address
`a` is the one at address `b`. Three honest points about the definition:

* It moves the **whole instance**, not just its `code` field. A Wasm body is
  meaningless without the `ModuleInst` it is closed over — its `funcs`,
  `globals`, `memories` and `tables` index spaces — so "the code of `b`" is only
  well defined together with `b`'s module instance.
* If `b` names a **host** function instance, the result is a host instance at
  `a`. The operation is total and the branch is definable; under the closed-host
  instantiation `H := Empty` it is vacuous, because `FuncInst.host` needs an
  inhabitant of `Empty`.
* If `b` is **out of range** the store is returned unchanged, which keeps
  `replaceFunc` total; `SameFuncType s a b` rules the case out whenever `a` is in
  range.

The type side condition is `V1.Execution.SameFuncType s a b`
(`Silmaril/Wasm/Equiv/Function.lean`); under it the replacement preserves the
whole table of function types, hence `InvokeOk` (`invokeOk_replaceFunc`).

## The congruence, and why the statement in the issue is false

the module-refinement contract asks for

> if `f ≈ g` in `M`, then replacing `f`'s body by `g`'s gives `M ≈ M[f := g]`.

That statement, with `≈` taken to be `FunEquiv`/`ModuleEquiv` over the
*result-only* `Behaviour` type, is **not true**. It is recorded below as the
proposition `NaiveReplacementCongruence`, and it fails for two independent
reasons.

**(i) Recursion through the replaced address.** Let `a` be `i32.const 0` and let
`b` be `call 0`, i.e. a call to `a`. In `s` both return `0`, so
`FunEquiv Eq host s a b` holds. In `s[a := b]` the instance at address `0` is
`call 0`, which calls itself: invoking `a` now diverges. So
`returns [0] ∈ behaviours host s a []` while
`behaviours host (s.replaceFunc a b) a [] = {diverges}`, and `ModuleEquiv` fails.
The hypothesis `FunEquiv R host s a b` is about `b`'s meaning *in `s`*, and the
replacement changes it.

**(ii) `Behaviour` does not observe the store.** Let `a` write `1` to a global
and return, and let `b` write `2` to the same global and return. Their behaviour
sets are equal — `Behaviour` records returned values, traps and divergence, and
nothing about the final store — but a third function that calls one of them and
then reads the global tells them apart. Equivalence at the result level is not
preserved by sequential composition in the presence of mutable state.
the contextual-refinement contract anticipates this: it lists "the final memory/global state"
as a separate choice of observation `Obs`.

Both counterexamples are stated here in prose only; formalising either needs a
concrete divergence proof or a concrete three-function store, and neither is
attempted.

## What is stated instead

The corrected milestone, `moduleRefines_replace`, takes the hypothesis at the
place where it is actually needed: `CallSim`, an *effect-aware* simulation at the
call boundary, at **every** store, saying that invoking `a` before the
replacement is matched by invoking `a` after it, ending in the correspondingly
replaced store. That hypothesis is not derivable from `FunEquiv` — counterexample
(i) shows the quantification over stores is needed and counterexample (ii) shows
the store effect is needed — and it is exactly what a logical relation or
bisimulation for this problem would establish.

## The store quantifier of this file is too strong, and these statements are vacuous

The statements in *this* file quantify `CallSim` over **every** store of the
type `Store H`, not over the stores reachable in the module.
`eq_of_forall_callSim` refutes that hypothesis for every `a ≠ b`, with no
assumption on the host: in the store `refutingStore a b`, which gives `a` a
unary function and `b` a nullary one, the nullary invocation `invoke s₁ a []`
is **stuck** before the replacement and returns after it, and the second clause
of `CallSim` — the clause that was added precisely to stop a replacement
turning a stuck invocation into a returning one — forbids exactly that.

So `∀ s₁, CallSim host a b s₁` holds only for `a = b`, where
`Store.replaceFunc_self` makes the replacement the identity.
`behavioursOf_replace`, `moduleRefines_replace` and `moduleEquiv_replace` are
therefore true and `sorryAx`-free, and **vacuous**. They are kept, unchanged, as
the record of why the unrestricted form is wrong; `eq_of_forall_callSim` is the
refutation itself.

## The contentful form, and where it lives

The fix is not to weaken `CallSim` — its three clauses are all needed — but to
restrict its store quantifier to the stores reachable in `M`, which is what
the module-refinement contract asks for ("store states reachable in `M`"). That is done
in two files that sit on top of this one:

* a separate reachable-store refinement development (not included in this package) defines `V1.Execution.Reachable` — the
  `prepare?` image closed under reduction — together with `StepClosed`,
  `CallSimOn` (this file's `CallSim`, asked only at the `Reach` stores) and
  `HostRespectsReplace`. The last of these closes the second gap: `Runtime.
  HostSemantics` is an unconstrained relation on the whole store, so a host
  function could otherwise read the function table (observing the replacement
  from a configuration that never invokes `a`) and write it (destroying
  `SameFuncType` part-way through a run). It holds vacuously for the closed host
  `H := Empty`.
* a separate congruence development (not included in this package) proves
  `V1.Execution.moduleEquiv_replaceOn`, the congruence itself, by a bisimulation
  that is step-for-step everywhere except at an invocation of `a`, where
  `CallSim` jumps the whole callee run.

separate function-replacement examples (not included in this package) instantiates that congruence at
`a ≠ b` holding two *different* function instances, which is what
`eq_of_forall_callSim` shows is impossible for the unrestricted form.

## The inversion the proof needs is now available

The obstruction recorded in the original version of this file — that V1 had no
evaluation-context type and no inversion lemma for `Step.context`, `Step.label`
or `Step.frame`, so the call-boundary decomposition could not even be stated —
is gone. `Silmaril/Wasm/V1/Execution/Inversion.lean` supplies it:
`V1.Execution.Rigid.plug_inv` inverts a reduction out of a parked invocation in
an arbitrary `Runtime.EvalCtx`, and `Rigid.steps_factor` and
`Rigid.diverges_factor` are its finite and infinite run-level forms. The two
frame-irrelevance lemmas below, `steps_invoke_frame_irrelevant` and
`diverges_invoke_frame_irrelevant`, are proved from the same file's `Sealed`
invariant; `steps_invoke_compose` is the composition half. See
`Silmaril.Wasm.Equiv.Function`.
-/

@[expose] public section

namespace Silmaril.Wasm

universe u v w

/-! ## Module relations, generically -/

namespace Equiv

variable {S : Type u} {A : Type v} {V : Type w}
variable (E : EntryPoints S A V) (R R' : Behaviour V → Behaviour V → Prop)

/-- **Module refinement.** Every behaviour of every well-formed invocation in
`s` is `R`-related to one of the same invocation in `s'`. This is the
closed-program instance of the contextual-refinement contract. -/
def ModuleRefines (s s' : S) : Prop :=
  ∀ a vs, E.Ok s a vs → Behaviours.Refines R (E.beh s a vs) (E.beh s' a vs)

/-- **Module equivalence**, in the shape of `Behaviours.Equiv`. -/
def ModuleEquiv (s s' : S) : Prop :=
  ModuleRefines E R s s' ∧ ModuleRefines E (fun x y => R y x) s' s

/-- `s'` accepts every invocation `s` accepts: the side condition of module
transitivity, the store-level analogue of `OkMono`. -/
def StoreOkMono (s s' : S) : Prop := ∀ a vs, E.Ok s a vs → E.Ok s' a vs

variable {E R R'}

theorem StoreOkMono.refl (s : S) : StoreOkMono E s s := fun _ _ h => h

theorem StoreOkMono.trans {s s' s'' : S} (h : StoreOkMono E s s')
    (h' : StoreOkMono E s' s'') : StoreOkMono E s s'' := fun a vs hv => h' a vs (h a vs hv)

/-- Reflexivity, from reflexivity of `R`. -/
theorem ModuleRefines.refl (hR : ∀ b, R b b) (s : S) : ModuleRefines E R s s :=
  fun _ _ _ b hb => ⟨b, hb, hR b⟩

/-- Transitivity, from transitivity of `R` and the side condition. -/
theorem ModuleRefines.trans (hR : ∀ x y z, R x y → R y z → R x z) {s s' s'' : S}
    (hok : StoreOkMono E s s') (h : ModuleRefines E R s s') (h' : ModuleRefines E R s' s'') :
    ModuleRefines E R s s'' :=
  fun a vs hv => Behaviours.Refines.trans hR (h a vs hv) (h' a vs (hok a vs hv))

/-- **Monotonicity in the relation**: the behavior-refinement hierarchy lattice lifts to modules. -/
theorem ModuleRefines.mono (hRR' : ∀ x y, R x y → R' x y) {s s' : S}
    (h : ModuleRefines E R s s') : ModuleRefines E R' s s' :=
  fun a vs hv => Behaviours.Refines.mono hRR' (h a vs hv)

/-- `ModuleEquiv` projects to `ModuleRefines`. -/
theorem ModuleEquiv.refines {s s' : S} (h : ModuleEquiv E R s s') :
    ModuleRefines E R s s' := h.1

/-- Reflexivity of `ModuleEquiv`. -/
theorem ModuleEquiv.refl (hR : ∀ b, R b b) (s : S) : ModuleEquiv E R s s :=
  ⟨ModuleRefines.refl hR s, ModuleRefines.refl (R := fun x y => R y x) hR s⟩

/-- Symmetry of `ModuleEquiv`: swapping the halves swaps `R` for its opposite. -/
theorem ModuleEquiv.symm {s s' : S} (h : ModuleEquiv E R s s') :
    ModuleEquiv E (fun x y => R y x) s' s := ⟨h.2, h.1⟩

/-- Symmetry of `ModuleEquiv` for a symmetric `R`. -/
theorem ModuleEquiv.symm' (hR : ∀ x y, R x y → R y x) {s s' : S}
    (h : ModuleEquiv E R s s') : ModuleEquiv E R s' s :=
  ⟨h.2.mono (fun _ _ h' => hR _ _ h'), h.1.mono (fun _ _ h' => hR _ _ h')⟩

/-- Transitivity of `ModuleEquiv`. -/
theorem ModuleEquiv.trans (hR : ∀ x y z, R x y → R y z → R x z) {s s' s'' : S}
    (hok : StoreOkMono E s s') (hok' : StoreOkMono E s'' s') (h : ModuleEquiv E R s s')
    (h' : ModuleEquiv E R s' s'') : ModuleEquiv E R s s'' :=
  ⟨ModuleRefines.trans hR hok h.1 h'.1,
   ModuleRefines.trans (fun x y z hxy hyz => hR z y x hyz hxy) hok' h'.2 h.2⟩

/-- Monotonicity of `ModuleEquiv` in the relation. -/
theorem ModuleEquiv.mono (hRR' : ∀ x y, R x y → R' x y) {s s' : S}
    (h : ModuleEquiv E R s s') : ModuleEquiv E R' s s' :=
  ⟨h.1.mono hRR', h.2.mono (fun x y h' => hRR' y x h')⟩

/-- `ModuleEquiv Eq` is behaviour-set equality at every well-formed invocation,
provided the two stores accept the same invocations. -/
theorem moduleEquiv_eq_iff {s s' : S} (hok : ∀ a vs, E.Ok s a vs ↔ E.Ok s' a vs) :
    ModuleEquiv E (· = ·) s s' ↔ ∀ a vs, E.Ok s a vs → E.beh s a vs = E.beh s' a vs := by
  constructor
  · rintro ⟨h₁, h₂⟩ a vs hv
    exact Behaviours.equiv_eq_iff.mp ⟨h₁ a vs hv, h₂ a vs ((hok a vs).mp hv)⟩
  · intro h
    refine ⟨fun a vs hv => ?_, fun a vs hv => ?_⟩
    · exact (Behaviours.equiv_eq_iff.mpr (h a vs hv)).1
    · exact (Behaviours.equiv_eq_iff.mpr (h a vs ((hok a vs).mpr hv))).2

/-! ### The inclusion lattice at the module level -/

variable (E) in
/-- `Eq ⊆ TrapRefines`. -/
theorem moduleRefines_trapRefines_of_eq {s s' : S} (h : ModuleRefines E (· = ·) s s') :
    ModuleRefines E Behaviour.TrapRefines s s' :=
  h.mono fun _ _ => Behaviour.TrapRefines.of_eq

variable (E) in
/-- `Eq ⊆ TrapDiv`. -/
theorem moduleRefines_trapDiv_of_eq {s s' : S} (h : ModuleRefines E (· = ·) s s') :
    ModuleRefines E Behaviour.TrapDiv s s' :=
  h.mono fun _ _ => Behaviour.TrapDiv.of_eq

variable (E) in
/-- `TrapRefines ⊆ TrapRefinesDiv`. -/
theorem moduleRefines_trapRefinesDiv_of_trapRefines {s s' : S}
    (h : ModuleRefines E Behaviour.TrapRefines s s') :
    ModuleRefines E Behaviour.TrapRefinesDiv s s' :=
  h.mono fun _ _ => Behaviour.TrapRefines.trapRefinesDiv

variable (E) in
/-- `TrapDiv ⊆ TrapRefinesDiv`. -/
theorem moduleRefines_trapRefinesDiv_of_trapDiv {s s' : S}
    (h : ModuleRefines E Behaviour.TrapDiv s s') :
    ModuleRefines E Behaviour.TrapRefinesDiv s s' :=
  h.mono fun _ _ => Behaviour.TrapDiv.trapRefinesDiv

/-! ## Imports

the module-refinement contract asks that "an import can be *refined* by any binding
satisfying its spec". An import assumption is modelled as a predicate on
behaviour sets — concretely, as the set of behaviours the import is *allowed*
to have, one set per argument list — and satisfaction is `R`-refinement into it.
Everything here is at the invocation boundary, which is why it is tractable. -/

/-- An **import specification**: the behaviours the imported function may
exhibit, as a function of its arguments. -/
def ImportSpec (V : Type w) : Type w := List V → Set (Behaviour V)

variable (E R) in
/-- The binding at address `a` in `s` **meets** the specification `σ` up to `R`:
every behaviour it can exhibit is `R`-related to one the specification allows. -/
def Meets (s : S) (a : A) (σ : ImportSpec V) : Prop :=
  ∀ vs, E.Ok s a vs → Behaviours.Refines R (E.beh s a vs) (σ vs)

variable (E) in
/-- The specification a concrete binding induces: its own behaviours. -/
def specOf (s : S) (a : A) : ImportSpec V := fun vs => E.beh s a vs

/-- Every binding meets the specification it induces. -/
theorem meets_specOf (hR : ∀ b, R b b) (s : S) (a : A) : Meets E R s a (specOf E s a) :=
  fun _ _ b hb => ⟨b, hb, hR b⟩

/-- **Monotonicity in the specification**: weakening the assumption preserves
satisfaction. This is the half of import refinement that says a *more permissive*
import spec is satisfied by everything a stricter one is. -/
theorem Meets.mono_spec {s : S} {a : A} {σ σ' : ImportSpec V} (hσ : ∀ vs, σ vs ⊆ σ' vs)
    (h : Meets E R s a σ) : Meets E R s a σ' :=
  fun vs hv => Behaviours.Refines.mono_right (hσ vs) (h vs hv)

/-- **Monotonicity in the relation**: the behavior-refinement hierarchy lattice applies to import
assumptions too. -/
theorem Meets.mono_rel {s : S} {a : A} {σ : ImportSpec V} (hRR' : ∀ x y, R x y → R' x y)
    (h : Meets E R s a σ) : Meets E R' s a σ :=
  fun vs hv => Behaviours.Refines.mono hRR' (h vs hv)

/-- **Import refinement.** A binding that meets the specification `σ` refines any
function whose behaviours include everything `σ` allows. Instantiating `σ` with
`specOf E s b` says: any binding that meets `b`'s specification refines `b`. -/
theorem Meets.funRefines {s : S} {a b : A} {σ : ImportSpec V} (h : Meets E R s a σ)
    (hb : ∀ vs, σ vs ⊆ E.beh s b vs) : FunRefines E R s a b :=
  fun vs hv => Behaviours.Refines.mono_right (hb vs) (h vs hv)

/-- **Import refinement, transitive form.** A binding meeting `σ` refines any
function that `σ` itself refines. -/
theorem Meets.funRefines_of_refines (hR : ∀ x y z, R x y → R y z → R x z) {s : S} {a b : A}
    {σ : ImportSpec V} (h : Meets E R s a σ)
    (hb : ∀ vs, Behaviours.Refines R (σ vs) (E.beh s b vs)) : FunRefines E R s a b :=
  fun vs hv => Behaviours.Refines.trans hR (h vs hv) (hb vs)

/-- **Linking an import to a module function.** If `b`'s behaviours meet the
import assumption `σ`, then a client refinement proved against `σ` survives
replacing the assumption by `b`. -/
theorem Meets.trans_spec (hR : ∀ x y z, R x y → R y z → R x z) {s : S} {a b : A}
    {σ : ImportSpec V} (hab : FunRefines E R s a b) (hb : Meets E R s b σ)
    (hok : OkMono E s a b) : Meets E R s a σ :=
  fun vs hv => Behaviours.Refines.trans hR (hab vs hv) (hb vs (hok vs hv))

/-- The specification induced by a partial-correctness postcondition `Q`: any
behaviour that produces no result, and any return whose values satisfy `Q`. This
is the `{P} f {Q}` ⟹ `f ⊑ spec` direction of the Hoare-to-refinement goal noted in
the module-refinement contract. -/
def specOfPost (Q : List V → List V → Prop) : ImportSpec V :=
  fun vs => {b | b.NoResult} ∪ {b | ∃ ws, b = .returns ws ∧ Q vs ws}

/-- A Hoare-triple postcondition is exactly a specification met at equality. -/
theorem meets_specOfPost_iff {Q : List V → List V → Prop} {s : S} {a : A} :
    Meets E (· = ·) s a (specOfPost Q) ↔
      ∀ vs, E.Ok s a vs → ∀ b ∈ E.beh s a vs, b.NoResult ∨ ∃ ws, b = .returns ws ∧ Q vs ws := by
  simp only [Meets, Behaviours.refines_eq_iff, specOfPost, Set.subset_def, Set.mem_union,
    Set.mem_ofPred_eq]

/-- A postcondition that is implied by another gives a weaker specification. -/
theorem specOfPost_mono {Q Q' : List V → List V → Prop} (hQ : ∀ vs ws, Q vs ws → Q' vs ws)
    (vs : List V) : specOfPost Q vs ⊆ specOfPost Q' vs := by
  rintro b (hb | ⟨ws, rfl, hw⟩)
  · exact Or.inl hb
  · exact Or.inr ⟨ws, rfl, hQ _ _ hw⟩

end Equiv

/-! ## Replacement in a runtime store -/

namespace Execution.Runtime

variable {Code Host : Type*}

/-- `s[a := b]`: the store in which the function instance at address `a` is the
one at address `b`. The whole instance moves, including its `ModuleInst`,
because a Wasm body is only meaningful relative to the module instance it is
closed over. An out-of-range `b` leaves the store unchanged, which makes the
operation total. -/
def Store.replaceFunc (s : Store Code Host) (a b : FuncAddr) : Store Code Host :=
  match s.funcs[b.value]? with
  | some fb => { s with funcs := s.funcs.set a.value fb }
  | none => s

variable {s : Store Code Host} {a b : FuncAddr}

/-- Replacement touches only the function table. -/
@[simp] theorem Store.replaceFunc_tables : (s.replaceFunc a b).tables = s.tables := by
  unfold Store.replaceFunc; split <;> rfl

/-- Replacement touches only the function table. -/
@[simp] theorem Store.replaceFunc_memories : (s.replaceFunc a b).memories = s.memories := by
  unfold Store.replaceFunc; split <;> rfl

/-- Replacement touches only the function table. -/
@[simp] theorem Store.replaceFunc_globals : (s.replaceFunc a b).globals = s.globals := by
  unfold Store.replaceFunc; split <;> rfl

/-- Replacement does not change the number of functions, so it does not change
which addresses exist. -/
@[simp] theorem Store.replaceFunc_length :
    (s.replaceFunc a b).funcs.length = s.funcs.length := by
  unfold Store.replaceFunc; split <;> simp

/-- Away from `a`, the store is unchanged. -/
theorem Store.getElem?_replaceFunc_of_ne {i : Nat} (h : i ≠ a.value) :
    (s.replaceFunc a b).funcs[i]? = s.funcs[i]? := by
  unfold Store.replaceFunc
  split <;> simp [Ne.symm h]

/-- At `a`, the store holds `b`'s instance — provided `b` exists and `a` is in
range. -/
theorem Store.getElem?_replaceFunc_self {fb : FuncInst Code Host}
    (hb : s.funcs[b.value]? = some fb) (ha : a.value < s.funcs.length) :
    (s.replaceFunc a b).funcs[a.value]? = some fb := by
  unfold Store.replaceFunc
  rw [hb]
  simp [ha]

/-- An out-of-range `b` is a no-op. -/
theorem Store.replaceFunc_of_none (hb : s.funcs[b.value]? = none) : s.replaceFunc a b = s := by
  unfold Store.replaceFunc; rw [hb]

/-- Replacing a function by itself is a no-op. -/
@[simp] theorem Store.replaceFunc_self : s.replaceFunc a a = s := by
  unfold Store.replaceFunc
  split
  · rename_i fb hb
    obtain ⟨ha, hfb⟩ := List.getElem?_eq_some_iff.mp hb
    refine congrArg (fun l => { s with funcs := l }) (List.ext_getElem? fun i => ?_)
    rcases eq_or_ne i a.value with rfl | hne
    · simp [ha, hfb]
    · simp [Ne.symm hne]
  · rfl

end Execution.Runtime

/-! ## The WebAssembly 1.0 instance -/

namespace V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

variable {H : Type}

/-- **Module refinement in V1**, in the spelling of the module-refinement contract. -/
abbrev ModuleRefines (R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop)
    (host : HostSemantics H) (s s' : Store H) : Prop :=
  Equiv.ModuleRefines (entryPoints host) R s s'

/-- **Module equivalence in V1.** -/
abbrev ModuleEquiv (R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop)
    (host : HostSemantics H) (s s' : Store H) : Prop :=
  Equiv.ModuleEquiv (entryPoints host) R s s'

/-- Unfolding `ModuleRefines` to the statement of the issue. -/
theorem moduleRefines_iff {R : Behaviour Runtime.Value → Behaviour Runtime.Value → Prop}
    {host : HostSemantics H} {s s' : Store H} :
    ModuleRefines R host s s' ↔
      ∀ a vs, InvokeOk s a vs →
        Behaviours.Refines R (behaviours host s a vs) (behaviours host s' a vs) := Iff.rfl

/-! ### Replacement preserves the type table -/

/-- Under the type side condition, the replacement leaves every address with a
function instance of the same type. -/
theorem funcType_replaceFunc {s : Store H} {a b : FuncAddr} (h : SameFuncType s a b)
    (i : Nat) :
    ((s.replaceFunc a b).funcs[i]?.map FuncInst.type) = (s.funcs[i]?.map FuncInst.type) := by
  rcases eq_or_ne i a.value with rfl | hne
  · cases hb : s.funcs[b.value]? with
    | none =>
      rw [Store.replaceFunc_of_none hb]
    | some fb =>
      by_cases ha : a.value < s.funcs.length
      · rw [Store.getElem?_replaceFunc_self hb ha]
        rw [SameFuncType, hb] at h
        exact h.symm
      · exfalso
        rw [SameFuncType, hb, List.getElem?_eq_none (Nat.le_of_not_lt ha)] at h
        simp at h
  · rw [Store.getElem?_replaceFunc_of_ne hne]

/-- Under the type side condition, the replacement accepts exactly the same
invocations. -/
theorem invokeOk_replaceFunc {s : Store H} {a b : FuncAddr} (h : SameFuncType s a b)
    (c : FuncAddr) (vs : List Runtime.Value) :
    InvokeOk (s.replaceFunc a b) c vs ↔ InvokeOk s c vs := by
  have ht := funcType_replaceFunc h c.value
  constructor <;> rintro ⟨fn, hfn, hty⟩
  · rw [hfn] at ht
    obtain ⟨fn', hfn', hfn''⟩ := Option.map_eq_some_iff.mp ht.symm
    exact ⟨fn', hfn', hty.trans (congrArg FuncType.params hfn''.symm)⟩
  · rw [hfn] at ht
    obtain ⟨fn', hfn', hfn''⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨fn', hfn', hty.trans (congrArg FuncType.params hfn''.symm)⟩

/-- The replacement preserves `SameFuncType` from `a` to `b` as the identity on
types, so it is `StoreOkMono` in both directions. -/
theorem storeOkMono_replaceFunc {host : HostSemantics H} {s : Store H} {a b : FuncAddr}
    (h : SameFuncType s a b) :
    Equiv.StoreOkMono (entryPoints host) s (s.replaceFunc a b) :=
  fun c vs hv => (invokeOk_replaceFunc h c vs).mpr hv

/-! ### The replacement congruence

The statement the issue asks for is `NaiveReplacementCongruence`, and it is
false; see the module docstring. What is stated here is the corrected form,
whose hypothesis `CallSim` is an *effect-aware bisimulation at the call
boundary*, quantified over **all** stores. Counterexample (i) of the module
docstring is why the quantification over stores cannot be dropped, and
counterexample (ii) is why the store effect cannot be dropped.

Everything is at `R := Eq`, which is the strongest relation of the behavior-refinement hierarchy lattice;
the weaker relations follow by `Equiv.ModuleRefines.mono` with no extra work
(`moduleRefines_replace_trapRefines` and friends below). -/

/-- The statement the module-refinement contract literally asks for. It is **false** —
see the module docstring for the two counterexamples — so it is recorded as a
proposition, to keep the claim on the record in Lean, and not as a theorem. -/
def NaiveReplacementCongruence (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (a b : FuncAddr), SameFuncType s a b →
    FunEquiv (· = ·) host s a b → ModuleEquiv (· = ·) host s (s.replaceFunc a b)

/--
**The call-boundary bisimulation hypothesis.** At the store `s₁`, invoking `a`
is indistinguishable from invoking `a` after the replacement, *including the
effect on the store*: a terminating run reaching the result `r` with final store
`s₂` is matched by one reaching `r` with final store `s₂[a := b]`, every
terminating run after the replacement arises that way, and the two diverge
together.

Three things this is and `FunEquiv` is not, each forced by the analysis in the
module docstring:

* it is quantified over **every** store `s₁`, not just `s` — counterexample (i),
  recursion through the replaced address;
* it tracks the **final store**, not only the result — counterexample (ii),
  mutable state;
* its second clause is not the converse of the first read backwards: a
  terminating run *after* the replacement must land in a store that is itself a
  replacement, which is what rules out the replacement turning a stuck
  invocation into a returning one.
-/
def CallSim (host : HostSemantics H) (a b : FuncAddr) (s₁ : Store H) : Prop :=
  (∀ (vs : List Runtime.Value) (s₂ : Store H) (r : Runtime.Result),
      Steps host (invoke s₁ a vs) ⟨s₂, ⟨[], {}⟩, result r⟩ →
        Steps host (invoke (s₁.replaceFunc a b) a vs)
          ⟨s₂.replaceFunc a b, ⟨[], {}⟩, result r⟩) ∧
  (∀ (vs : List Runtime.Value) (s₂' : Store H) (r : Runtime.Result),
      Steps host (invoke (s₁.replaceFunc a b) a vs) ⟨s₂', ⟨[], {}⟩, result r⟩ →
        ∃ s₂ : Store H, s₂' = s₂.replaceFunc a b ∧
          Steps host (invoke s₁ a vs) ⟨s₂, ⟨[], {}⟩, result r⟩) ∧
  (∀ vs : List Runtime.Value,
      Diverges host (invoke s₁ a vs) ↔ Diverges host (invoke (s₁.replaceFunc a b) a vs))

/-- **Composition at a call boundary.** A terminating sub-run of an invocation
composes into a run of the surrounding evaluation context: this is the "frame"
half of the decomposition, and it is a direct consequence of `Steps.context`. -/
theorem steps_invoke_compose {host : HostSemantics H} {s s' : Store H} {f : Frame}
    {a : FuncAddr} {vs ws : List Runtime.Value}
    (sub : Steps host ⟨s, f, values vs ++ [.invoke a]⟩ ⟨s', f, values ws⟩)
    (pre : List Runtime.Value) (tail : List Admin) :
    Steps host ⟨s, f, values pre ++ (values vs ++ [.invoke a]) ++ tail⟩
      ⟨s', f, values pre ++ values ws ++ tail⟩ :=
  Steps.context sub pre tail

/--
**Frame irrelevance at a call boundary.** An invocation never reads or writes
the frame it is invoked from — every local operation inside it happens under the
`.frame` administrative instruction that `Step.invokeWasm` pushes — so a run of
`values vs ++ [.invoke a]` to a result does not depend on the enclosing frame.

Proved from `Sealed.steps` of `Silmaril/Wasm/V1/Execution/Inversion.lean`: the
code of an invocation in flight stays in the reduction-closed class `Sealed`,
whose every step is available at *every* frame and leaves the frame it is given
unchanged.
-/
theorem steps_invoke_frame_irrelevant {host : HostSemantics H} {s s' : Store H}
    {f g : Frame} {a : FuncAddr} {vs : List Runtime.Value} {r : Runtime.Result}
    (h : Steps host ⟨s, f, values vs ++ [.invoke a]⟩ ⟨s', f, result r⟩) :
    Steps host ⟨s, g, values vs ++ [.invoke a]⟩ ⟨s', g, result r⟩ :=
  steps_invoke_frame h

/-- **Frame irrelevance at a call boundary, for divergence.** Proved from
`Sealed.diverges`, by coinduction on the infinite trace. -/
theorem diverges_invoke_frame_irrelevant {host : HostSemantics H} {s : Store H}
    {f g : Frame} {a : FuncAddr} {vs : List Runtime.Value}
    (h : Diverges host ⟨s, f, values vs ++ [.invoke a]⟩) :
    Diverges host ⟨s, g, values vs ++ [.invoke a]⟩ :=
  diverges_invoke_frame h

/-! ### `CallSim` at *every* store is degenerate

`CallSim` is quantified over **every** store of the type, not over the stores
reachable in the module. That makes `∀ s₁, CallSim host a b s₁` refutable
whenever `a ≠ b`: a store that gives `a` a unary function and `b` a nullary one
makes the nullary invocation `invoke s₁ a []` stuck before the replacement and
terminating after it, which is exactly what the second clause of `CallSim`
forbids. The refutation is `eq_of_forall_callSim` below, and it needs no
assumption on the host.

The consequence is that the statements in *this* file apply only to the identity
replacement, so — while true and `sorryAx`-free — they are **vacuous**. They are
kept as the record of the flaw; the contentful form is
`V1.Execution.moduleEquiv_replaceOn` of
a separate congruence development (not included in this package). See the module docstring. -/

/-- A nullary WebAssembly instance with an empty body: invoking it on no
arguments returns immediately. -/
def nullaryInst : FuncInst Func H := .wasm ⟨[], []⟩ {} ⟨⟨0⟩, [], []⟩

/-- A unary WebAssembly instance: invoking it on *no* arguments is stuck,
because `Step.invokeWasm` requires as many arguments as parameters. -/
def unaryInst : FuncInst Func H := .wasm ⟨[ValType.i32], []⟩ {} ⟨⟨0⟩, [], []⟩

/-- The store that refutes `CallSim` at every store: `a` is unary, `b` is
nullary. -/
def refutingStore (a b : FuncAddr) : Store H :=
  { funcs := (List.replicate (max a.value b.value + 1) (nullaryInst : FuncInst Func H)).set
      a.value unaryInst }

/-- In the refuting store, `a` holds the unary instance. -/
theorem refutingStore_self (a b : FuncAddr) :
    (refutingStore (H := H) a b).funcs[a.value]? = some unaryInst := by
  simp [refutingStore, List.getElem?_set]
  omega

/-- In the refuting store, `b` holds the nullary instance. -/
theorem refutingStore_other (a b : FuncAddr) (hab : a.value ≠ b.value) :
    (refutingStore (H := H) a b).funcs[b.value]? = some nullaryInst := by
  simp [refutingStore, hab, List.getElem?_replicate]
  omega

/-- The refuting store has `a` in range. -/
theorem refutingStore_length (a b : FuncAddr) :
    a.value < (refutingStore (H := H) a b).funcs.length := by
  simp [refutingStore]
  omega

/-- Invoking a nullary empty-bodied function on no arguments returns, in three
steps: `Step.invokeWasm`, then the label and then the frame finish. -/
theorem nullaryInst_steps {host : HostSemantics H} (s : Store H) (a : FuncAddr)
    (hfound : s.funcs[a.value]? = some (nullaryInst : FuncInst Func H)) :
    Steps host (invoke s a []) ⟨s, ⟨[], {}⟩, result (.values [])⟩ := by
  have step1 : Step host (invoke s a [])
      ⟨s, ⟨[], {}⟩, [AdminInstr.frame 0 ⟨[], {}⟩ [.label 0 [] []]]⟩ := by
    have h := Step.invokeWasm (host := host) s ⟨[], {}⟩ a ⟨[], []⟩ {} ⟨⟨0⟩, [], []⟩ []
      hfound rfl (by simp)
    exact h
  have step2 : Step host ⟨s, ⟨[], {}⟩, [AdminInstr.frame 0 ⟨[], {}⟩ [.label 0 [] []]]⟩
      ⟨s, ⟨[], {}⟩, [AdminInstr.frame 0 ⟨[], {}⟩ []]⟩ :=
    Step.frame (Step.pure s ⟨[], {}⟩ (PureStep.labelDone 0 [] [])) 0 ⟨[], {}⟩
  have step3 : Step host ⟨s, ⟨[], {}⟩, [AdminInstr.frame 0 ⟨[], {}⟩ []]⟩
      ⟨s, ⟨[], {}⟩, result (.values [])⟩ :=
    Step.pure s ⟨[], {}⟩ (PureStep.frameDone 0 ⟨[], {}⟩ [] rfl)
  exact (step1.steps.tail step2).tail step3

/-- Invoking a unary function on no arguments takes no step at all. -/
theorem unaryInst_stuck {host : HostSemantics H} {s : Store H} {a : FuncAddr}
    (hfound : s.funcs[a.value]? = some (unaryInst : FuncInst Func H)) (c' : Config H) :
    ¬ Step host (invoke s a []) c' := by
  intro hstep
  obtain ⟨-, pre, args, X, hsplit, ⟨fi, hfound', hlen⟩, -, -, -⟩ :=
    hstep.invoke_inv (show (invoke s a [] : Config H).code = values [] ++ .invoke a :: [] from rfl)
  replace hfound' : s.funcs[a.value]? = some fi := hfound'
  rw [hfound] at hfound'
  cases hfound'
  have hargs : args = [] := (by simpa using hsplit.symm : pre = [] ∧ args = []).2
  subst hargs
  simp [unaryInst, FuncInst.type] at hlen

/--
**`CallSim` at every store forces `a = b`.** The second clause of `CallSim` —
"a terminating run *after* the replacement must land in a replaced store", the
clause that rules out the replacement turning a stuck invocation into a
returning one — is violated at `refutingStore a b` as soon as `a ≠ b`, with no
assumption on the host at all.

So the hypothesis `∀ s₁, CallSim host a b s₁` of `moduleRefines_replace` and
`moduleEquiv_replace` is only ever satisfied by the identity replacement. The
fix is not to weaken `CallSim` but to restrict its store quantifier to the
stores *reachable in the module*, which is what the module-refinement contract means by
"store states reachable in `M`".

This theorem is kept as the record of why the unrestricted form is wrong. The
restricted form is `V1.Execution.CallSimOn` of
a separate reachable-store refinement development (not included in this package), and the congruence it supports is
`V1.Execution.moduleEquiv_replaceOn` of a separate congruence development (not included in this package);
separate function-replacement examples (not included in this package) satisfies it with `a ≠ b`.
-/
theorem eq_of_forall_callSim {host : HostSemantics H} {a b : FuncAddr}
    (hsim : ∀ s₁ : Store H, CallSim host a b s₁) : a = b := by
  by_contra hne
  have hab : a.value ≠ b.value := by
    intro h
    exact hne (by cases a; cases b; simp_all)
  have hrepl : ((refutingStore (H := H) a b).replaceFunc a b).funcs[a.value]? =
      some nullaryInst :=
    Store.getElem?_replaceFunc_self (refutingStore_other a b hab) (refutingStore_length a b)
  obtain ⟨s₂, -, horig⟩ := (hsim (refutingStore a b)).2.1 []
    ((refutingStore (H := H) a b).replaceFunc a b) (.values [])
    (nullaryInst_steps (host := host) _ a hrepl)
  rcases Relation.ReflTransGen.cases_head horig with heq | ⟨c', hstep, -⟩
  · exact absurd (congrArg Config.code heq.symm) (by simp [invoke, result, Execution.values])
  · exact unaryInst_stuck (host := host) (refutingStore_self a b) c' hstep

/--
**The configuration-level replacement lemma.** Under the call-boundary
hypothesis at every store, the replacement is invisible from *every*
configuration, not just from an entry point.

**This proof is a degeneracy proof, not the milestone.** `eq_of_forall_callSim`
shows that the hypothesis `∀ s₁, CallSim host a b s₁` has no models with
`a ≠ b`, so the only replacement it licenses is `a := a`, which is the identity
on the store (`Store.replaceFunc_self`). The statement is therefore true and
`sorryAx`-free, and it carries no content: it does **not** establish that
replacing a function by a call-boundary-equivalent one preserves behaviour.

The three things a contentful version needs are all supplied elsewhere now:

1. a `CallSim` whose store quantifier ranges over the stores **reachable in the
   module** rather than over every store of the type — the module-refinement contract's
   "store states reachable in `M`". That is `V1.Execution.CallSimOn` of
   a separate reachable-store refinement development (not included in this package), against `V1.Execution.Reachable`;
2. **side conditions on the host.** `HostSemantics` is an unconstrained
   relation on the whole store, so a host function may both *read* the function
   table — and so observe the replacement at `a` from a configuration that
   never invokes `a` — and *write* it, destroying `SameFuncType` part-way
   through a run. Neither is excluded by `CallSim`, which constrains only runs
   that start at `invoke s₁ a vs`. That is
   `V1.Execution.HostRespectsReplace`, which holds vacuously for the closed
   host `H := Empty`;
3. the call-boundary decomposition: `V1.Execution.Rigid.plug_inv`,
   `Rigid.steps_factor` and `Rigid.diverges_factor` of
   `Silmaril/Wasm/V1/Execution/Inversion.lean`.

The resulting theorem is `V1.Execution.behavioursOf_replaceOn` of
a separate congruence development (not included in this package), which has this conclusion and a real
proof.
-/
theorem behavioursOf_replace {host : HostSemantics H} {a b : FuncAddr}
    (hsim : ∀ s₁ : Store H, CallSim host a b s₁) (c : Config H)
    (hty : SameFuncType c.store a b) :
    behavioursOf host c = behavioursOf host ⟨c.store.replaceFunc a b, c.frame, c.code⟩ := by
  obtain rfl := eq_of_forall_callSim hsim
  rw [Store.replaceFunc_self]

/-- The entry-point form of `behavioursOf_replace`. -/
theorem behaviours_replace {host : HostSemantics H} {a b : FuncAddr}
    (hsim : ∀ s₁ : Store H, CallSim host a b s₁) {s : Store H} (hty : SameFuncType s a b)
    (c : FuncAddr) (vs : List Runtime.Value) :
    behaviours host s c vs = behaviours host (s.replaceFunc a b) c vs :=
  behavioursOf_replace hsim (invoke s c vs) hty

/-- **Replacement refinement.** Derived in full from `behavioursOf_replace`. -/
theorem moduleRefines_replace {host : HostSemantics H} {a b : FuncAddr}
    (hsim : ∀ s₁ : Store H, CallSim host a b s₁) {s : Store H} (hty : SameFuncType s a b) :
    ModuleRefines (· = ·) host s (s.replaceFunc a b) := by
  intro c vs _ x hx
  refine ⟨x, ?_, rfl⟩
  show x ∈ behaviours host (s.replaceFunc a b) c vs
  rw [← behaviours_replace hsim hty c vs]
  exact hx

/--
**Replacement congruence.** Replacing a function by one that is
indistinguishable from it at the call boundary, at every store, gives an
equivalent module. Derived in full from `behavioursOf_replace`.

**Vacuous**, by `eq_of_forall_callSim`: the hypothesis has no models with
`a ≠ b`. Kept with this statement as the record of why the unrestricted store
quantifier is wrong. The contentful form, with the quantifier restricted to the
reachable stores, is `V1.Execution.moduleEquiv_replaceOn` of
a separate congruence development (not included in this package), and
separate function-replacement examples (not included in this package) instantiates it at `a ≠ b`.
-/
theorem moduleEquiv_replace {host : HostSemantics H} {a b : FuncAddr}
    (hsim : ∀ s₁ : Store H, CallSim host a b s₁) {s : Store H} (hty : SameFuncType s a b) :
    ModuleEquiv (· = ·) host s (s.replaceFunc a b) := by
  refine ⟨moduleRefines_replace hsim hty, ?_⟩
  intro c vs _ x hx
  refine ⟨x, ?_, rfl⟩
  show x ∈ behaviours host s c vs
  rw [behaviours_replace hsim hty c vs]
  exact hx

/-- The replacement congruence at trap-insertion refinement, by monotonicity. -/
theorem moduleRefines_replace_trapRefines {host : HostSemantics H} {a b : FuncAddr}
    (hsim : ∀ s₁ : Store H, CallSim host a b s₁) {s : Store H} (hty : SameFuncType s a b) :
    ModuleRefines Behaviour.TrapRefines host s (s.replaceFunc a b) :=
  Equiv.moduleRefines_trapRefines_of_eq _ (moduleRefines_replace hsim hty)

/-- The replacement congruence at trap ≈ divergence, by monotonicity. -/
theorem moduleRefines_replace_trapDiv {host : HostSemantics H} {a b : FuncAddr}
    (hsim : ∀ s₁ : Store H, CallSim host a b s₁) {s : Store H} (hty : SameFuncType s a b) :
    ModuleRefines Behaviour.TrapDiv host s (s.replaceFunc a b) :=
  Equiv.moduleRefines_trapDiv_of_eq _ (moduleRefines_replace hsim hty)

/-- The replacement congruence at trap insertion modulo divergence, by
monotonicity. -/
theorem moduleRefines_replace_trapRefinesDiv {host : HostSemantics H} {a b : FuncAddr}
    (hsim : ∀ s₁ : Store H, CallSim host a b s₁) {s : Store H} (hty : SameFuncType s a b) :
    ModuleRefines Behaviour.TrapRefinesDiv host s (s.replaceFunc a b) :=
  Equiv.moduleRefines_trapRefinesDiv_of_trapRefines _ (moduleRefines_replace_trapRefines hsim hty)

/-- A degenerate but complete instance: replacing a function by itself. -/
theorem moduleEquiv_replace_self {host : HostSemantics H} (s : Store H) (a : FuncAddr) :
    ModuleEquiv (· = ·) host s (s.replaceFunc a a) := by
  rw [Store.replaceFunc_self]
  exact Equiv.ModuleEquiv.refl (fun _ => rfl) s

end V1.Execution

/-! ## The Core 3.0 instance

Core 3.0's `FuncInst` is a **record** — `type`, `module`, `code` — rather than a
two-constructor inductive, so the replacement can be written the way the issue
phrases it, as a replacement of the *code* (together with the module instance
that closes it), keeping the declared `type` of the replaced address. Two
consequences, both recorded below:

* `funcType_replaceFunc` holds with **no side condition**: the function-type
  table is preserved by construction;
* `FuncCode.host` is a constructor of a record field, so a host code can be put
  at `a` just as in V1; under a closed host (`H := Empty`) the branch is again
  vacuous.

The `InvokeOk` transfer is *not* stated here. Core's `InvokeOk` quantifies
`Execution.Core.ValOk s`, which recurses through `RefOk s` and therefore reads
the store's function table; transferring it needs a `RefOk` congruence lemma
along the type-table equality, which is not proved in this module. -/

namespace Execution.Core

open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- `s[a := b]` for Core 3.0: the function instance at `a` keeps its declared
type and takes `b`'s module instance and code. Out-of-range addresses leave the
store unchanged. -/
def Store.replaceFunc (s : Store H) (a b : Nat) : Store H :=
  match s.funcs[a]?, s.funcs[b]? with
  | some fa, some fb =>
    { s with funcs := s.funcs.set a { fa with module := fb.module, code := fb.code } }
  | _, _ => s

variable {s : Store H} {a b : Nat}

/-- Replacement does not change the number of functions. -/
@[simp] theorem Store.replaceFunc_length :
    (s.replaceFunc a b).funcs.length = s.funcs.length := by
  unfold Store.replaceFunc; split <;> simp

/-- Away from `a`, the store is unchanged. -/
theorem Store.getElem?_replaceFunc_of_ne {i : Nat} (h : i ≠ a) :
    (s.replaceFunc a b).funcs[i]? = s.funcs[i]? := by
  unfold Store.replaceFunc
  split <;> simp [Ne.symm h]

/-- **The Core replacement preserves every function type, unconditionally.**
This is the payoff of `FuncInst` being a record: the declared type of `a` is
kept, so no `SameFuncType` side condition is needed. -/
theorem funcType_replaceFunc (i : Nat) :
    ((s.replaceFunc a b).funcs[i]?.map FuncInst.type) = (s.funcs[i]?.map FuncInst.type) := by
  rcases eq_or_ne i a with rfl | hne
  · unfold Store.replaceFunc
    split
    · rename_i fa fb ha _
      obtain ⟨hlt, hfa⟩ := List.getElem?_eq_some_iff.mp ha
      simp [hlt, hfa]
    · rfl
  · rw [Store.getElem?_replaceFunc_of_ne hne]

/-- Replacing a function by itself is a no-op. -/
@[simp] theorem Store.replaceFunc_self : s.replaceFunc a a = s := by
  unfold Store.replaceFunc
  split
  · rename_i fa fb ha hb
    rw [ha] at hb
    cases hb
    obtain ⟨hlt, hfa⟩ := List.getElem?_eq_some_iff.mp ha
    have hset : s.funcs.set a { fa with module := fa.module, code := fa.code } = s.funcs := by
      refine List.ext_getElem? fun i => ?_
      rcases eq_or_ne i a with rfl | hne
      · simp [hlt, hfa]
      · simp [Ne.symm hne]
    rw [hset]
  · rfl

/-- **Module refinement in Core 3.0.** -/
abbrev ModuleRefines (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (s s' : Store H) : Prop :=
  Equiv.ModuleRefines (entryPoints P host) R s s'

/-- **Module equivalence in Core 3.0.** -/
abbrev ModuleEquiv (R : Behaviour Val → Behaviour Val → Prop) (P : Profile)
    (host : HostSemantics H) (s s' : Store H) : Prop :=
  Equiv.ModuleEquiv (entryPoints P host) R s s'

/-- Unfolding `ModuleRefines` to the statement of the issue. -/
theorem moduleRefines_iff {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {host : HostSemantics H} {s s' : Store H} :
    ModuleRefines R P host s s' ↔
      ∀ a vs, InvokeOk s a vs →
        Behaviours.Refines R (behaviours P host s a vs) (behaviours P host s' a vs) := Iff.rfl

end Execution.Core

end Silmaril.Wasm
