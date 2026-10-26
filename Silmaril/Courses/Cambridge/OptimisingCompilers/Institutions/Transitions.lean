module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Institutions.Assertions

/-! # Programs as theories: the transition institution

The 3-address IR as an institution in which a *program is a theory* and the
models of the theory are the *steps of its executions*.

* Signatures are register files `RegSig` (injective renamings); the node labels
  `ι` are a fixed parameter.
* Models over `V` are transitions `Trans V ι`: a source configuration, an
  optional output and a target configuration (a discrete category).
* Sentences `TSen V ι`:
  - `instr n i`: a step from node `n` follows instruction `i` on the control
    flow, the memory, the output and the variables `i` defines (notes p. 4);
  - `frame n x`: a step from node `n` leaves `x` unchanged;
  - `src φ`: the source state satisfies the assertion `φ`;
  - `hoare n φ m ψ`: a Hoare-style assertion: a step from node `n` in a state
    satisfying `φ` that reaches node `m` reaches a state satisfying `ψ`.
* The satisfaction condition (`TSen.holds_rename`) holds along every renaming.

The theory of a flowgraph `G` is presented by `Flowgraph.axioms G`: one `instr`
sentence per node and one `frame` sentence for each variable a node does not
define. Its models are exactly the steps of `G` (`holds_axioms_iff`). Renaming
the theory along an injective renaming gives part of the theory of the renamed
program (`rename_axioms_subset`), so the satisfaction condition alone shows that
reducts of steps of `G.rename σ` are steps of `G` (`step_reduct_of_step_rename`).

A dataflow analysis computing an assertion `A n` at every node is *sound* when
its Hoare sentences `hoare n (A n) m (A m)` are consequences of the program's
theory (`IsInductive`); then every reachable state satisfies the assertion at
its node (`IsInductive.holds_of_steps`), which is the notes' notion of a safe
analysis for forward problems.

`assnToTrans` is the comorphism of institutions from state assertions to the
transition institution: an assertion becomes a statement about the source of a
step.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

open Silmaril.Logic.Institution

namespace Config

variable {V R ι : Type}

/-- The reduct of a configuration along a renaming. -/
def reduct (σ : V → R) (c : Config R ι) : Config V ι := ⟨c.pc, c.env ∘ σ, c.mem⟩

end Config

namespace Institutions

/-- A transition: a source configuration, an output and a target configuration.
The models of the transition institution. -/
structure Trans (V ι : Type) : Type where
  src : Config V ι
  out : Option ℤ
  dst : Config V ι

namespace Trans

variable {V R ι : Type}

/-- The reduct of a transition along a renaming. -/
def reduct (σ : V → R) (t : Trans R ι) : Trans V ι := ⟨t.src.reduct σ, t.out, t.dst.reduct σ⟩

end Trans

end Institutions

namespace Instr

open Institutions

variable {V ι : Type} [DecidableEq V]

/-- The transition `t` is a step of the instruction `i` on the control flow,
the memory, the output and the variables `i` defines (the frame is separate).
An `EXIT` has no steps. -/
def Realises (i : Instr V ι) (t : Trans V ι) : Prop :=
  match i.exec t.src.env t.src.mem with
  | none => False
  | some (m, env', mem', o) =>
    t.dst.pc = m ∧ t.dst.mem = mem' ∧ t.out = o ∧ ∀ d ∈ i.defs, t.dst.env d = env' d

omit [DecidableEq V] in
theorem rename_id' (i : Instr V ι) : i.rename id = i := by
  cases i <;> simp [Instr.rename, Operand.rename_id]

omit [DecidableEq V] in
theorem rename_comp' {R W : Type} (σ : V → R) (τ : R → W) (i : Instr V ι) :
    i.rename (τ ∘ σ) = (i.rename σ).rename τ := by
  cases i <;> simp [Instr.rename, Operand.rename_comp]

/-- `exec` changes only the variables an instruction defines. -/
theorem exec_env_of_not_mem_defs {i : Instr V ι} {env : Env V} {mem : Mem} {m : ι}
    {env' : Env V} {mem' : Mem} {o : Option ℤ} (h : i.exec env mem = some (m, env', mem', o))
    {x : V} (hx : x ∉ i.defs) : env' x = env x := by
  cases i <;> simp only [exec, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    simp only [defs, Finset.mem_singleton] at hx <;> obtain ⟨-, rfl, -, -⟩ := h <;>
    simp [hx]

variable {R : Type} [DecidableEq R]

/-- Realisation commutes with renaming (no injectivity needed). -/
theorem realises_rename (σ : V → R) (t : Trans R ι) (i : Instr V ι) :
    (i.rename σ).Realises t ↔ i.Realises (t.reduct σ) := by
  cases i <;>
    simp [Realises, Instr.rename, exec, defs, Trans.reduct, Config.reduct, Operand.eval_rename,
      Function.comp_def]
  exact fun _ _ => Iff.rfl

end Instr

namespace Institutions

/-- The sentences of the transition institution. -/
inductive TSen (V ι : Type) : Type where
  /-- A step from node `n` follows instruction `i`. -/
  | instr (n : ι) (i : Instr V ι)
  /-- A step from node `n` leaves `x` unchanged. -/
  | frame (n : ι) (x : V)
  /-- The source state satisfies `φ`. -/
  | src (φ : Assn V)
  /-- A step from `n` in a `φ`-state that reaches `m` reaches a `ψ`-state. -/
  | hoare (n : ι) (φ : Assn V) (m : ι) (ψ : Assn V)


namespace TSen

variable {V R W ι : Type}

/-- Rename the registers of a sentence. -/
def rename (σ : V → R) : TSen V ι → TSen R ι
  | .instr n i => .instr n (i.rename σ)
  | .frame n x => .frame n (σ x)
  | .src φ => .src (φ.rename σ)
  | .hoare n φ m ψ => .hoare n (φ.rename σ) m (ψ.rename σ)

variable [DecidableEq V] [DecidableEq R]

/-- Satisfaction of a sentence by a transition. -/
def Holds (t : Trans V ι) : TSen V ι → Prop
  | .instr n i => t.src.pc = n → i.Realises t
  | .frame n x => t.src.pc = n → t.dst.env x = t.src.env x
  | .src φ => φ.Holds t.src.env t.src.mem
  | .hoare n φ m ψ => t.src.pc = n → φ.Holds t.src.env t.src.mem → t.dst.pc = m →
      ψ.Holds t.dst.env t.dst.mem

set_option linter.unusedSectionVars false in
theorem rename_id (φ : TSen V ι) : φ.rename id = φ := by
  cases φ <;> simp [rename, Instr.rename_id', Assn.rename_id]

set_option linter.unusedSectionVars false in
theorem rename_comp (σ : V → R) (τ : R → W) (φ : TSen V ι) :
    φ.rename (τ ∘ σ) = (φ.rename σ).rename τ := by
  cases φ <;> simp [rename, Instr.rename_comp', Assn.rename_comp]

/-- The satisfaction condition of the transition institution. -/
theorem holds_rename (σ : V → R) (t : Trans R ι) (φ : TSen V ι) :
    (φ.rename σ).Holds t ↔ φ.Holds (t.reduct σ) := by
  cases φ with
  | instr n i => exact imp_congr Iff.rfl (Instr.realises_rename σ t i)
  | frame n x => exact Iff.rfl
  | src φ => exact Assn.holds_rename σ t.src.env t.src.mem φ
  | hoare n φ m ψ =>
    exact imp_congr Iff.rfl (imp_congr (Assn.holds_rename σ _ _ φ)
      (imp_congr Iff.rfl (Assn.holds_rename σ _ _ ψ)))

end TSen

/-- The transition institution over node labels `ι`. -/
def transLogic (ι : Type) : StateLogic.{0} where
  Sen A := TSen A.V ι
  map σ := TSen.rename (RegSig.ren σ)
  map_id _ := TSen.rename_id
  map_comp σ τ := TSen.rename_comp (RegSig.ren σ) (RegSig.ren τ)
  St A := Trans A.V ι
  reduct σ := Trans.reduct (RegSig.ren σ)
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Holds t φ := φ.Holds t
  holds_map σ t φ := TSen.holds_rename (RegSig.ren σ) t φ

/-- The comorphism from state assertions to transitions: an assertion holds of
a step when it holds of its source state. -/
def assnToTrans (ι : Type) : StateLogic.Comorphism assnLogic (transLogic ι) where
  sen φ := .src φ
  st t := (t.src.env, t.src.mem)
  sen_natural _ _ := rfl
  st_natural _ _ := rfl
  sat _ _ := Iff.rfl

/-- The room of the transition institution at a register file `V`. -/
abbrev transRoom (V ι : Type) [DecidableEq V] : Room.{0, 0, 0} :=
  (transLogic ι).room ⟨V⟩

end Institutions

namespace Flowgraph

open Institutions

variable {V ι : Type} [DecidableEq V] (G : Flowgraph V ι)

/-- The presentation of the theory of a flowgraph: each node's instruction, and
the frame of every variable it does not define. -/
def axioms : Set (TSen V ι) :=
  {φ | ∃ n, φ = .instr n (G.code n)} ∪ {φ | ∃ n x, x ∉ (G.code n).defs ∧ φ = .frame n x}

/-- The models of the theory of `G` are exactly the steps of `G`. -/
theorem holds_axioms_iff (t : Trans V ι) :
    (∀ φ ∈ G.axioms, φ.Holds t) ↔ G.step t.src = some (t.out, t.dst) := by
  obtain ⟨⟨pc, env, mem⟩, out, ⟨pc', env', mem'⟩⟩ := t
  constructor
  · intro h
    have hi : (G.code pc).Realises ⟨⟨pc, env, mem⟩, out, ⟨pc', env', mem'⟩⟩ :=
      h _ (Or.inl ⟨pc, rfl⟩) rfl
    have hf : ∀ x ∉ (G.code pc).defs, env' x = env x :=
      fun x hx => h _ (Or.inr ⟨pc, x, hx, rfl⟩) rfl
    cases he : (G.code pc).exec env mem with
    | none => simp [Instr.Realises, he] at hi
    | some r =>
      obtain ⟨m, e, mm, o⟩ := r
      simp only [Instr.Realises, he] at hi
      obtain ⟨h1, h2, h3, h4⟩ := hi
      simp only [step, he, Option.map_some, Option.some.injEq, Prod.mk.injEq, Config.mk.injEq]
      refine ⟨h3.symm, h1.symm, funext fun x => ?_, h2.symm⟩
      by_cases hx : x ∈ (G.code pc).defs
      · exact (h4 x hx).symm
      · rw [hf x hx, Instr.exec_env_of_not_mem_defs he hx]
  · intro h
    cases he : (G.code pc).exec env mem with
    | none => simp [step, he] at h
    | some r =>
      obtain ⟨m, e, mm, o⟩ := r
      simp only [step, he, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        Config.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rintro _ (⟨n, rfl⟩ | ⟨n, x, hx, rfl⟩) hn
      · simp only at hn
        subst hn
        simp [Instr.Realises, he]
      · simp only at hn
        subst hn
        exact Instr.exec_env_of_not_mem_defs he hx

set_option linter.unusedSectionVars false in
/-- Renaming the theory of `G` along an injective renaming yields sentences of
the theory of the renamed program. Injectivity is needed: along a
non-injective `σ`, `frame n x` with `x` not defined at `n` maps to
`frame n (σ x)`, which fails in the renamed program when `σ x = σ d` for the
variable `d` defined at `n`. -/
theorem rename_axioms_subset {R : Type} [DecidableEq R] {σ : V → R}
    (hσ : Function.Injective σ) : TSen.rename σ '' G.axioms ⊆ (G.rename σ).axioms := by
  rintro _ ⟨φ, ⟨n, rfl⟩ | ⟨n, x, hx, rfl⟩, rfl⟩
  · exact Or.inl ⟨n, rfl⟩
  · refine Or.inr ⟨n, σ x, ?_, rfl⟩
    show σ x ∉ ((G.code n).rename σ).defs
    cases hc : G.code n <;> rw [hc] at hx <;>
      simp_all [Instr.rename, Instr.defs, hσ.eq_iff]

/-- Reducts of steps of the renamed program are steps of the original: the
satisfaction condition applied to the theory of `G`. -/
theorem step_reduct_of_step_rename {R : Type} [DecidableEq R] {σ : V → R}
    (hσ : Function.Injective σ) (t : Trans R ι)
    (h : (G.rename σ).step t.src = some (t.out, t.dst)) :
    G.step (t.reduct σ).src = some ((t.reduct σ).out, (t.reduct σ).dst) := by
  have hall := ((G.rename σ).holds_axioms_iff t).2 h
  refine (G.holds_axioms_iff (t.reduct σ)).1 fun φ hφ => ?_
  exact (TSen.holds_rename σ t φ).1 (hall _ (G.rename_axioms_subset hσ ⟨φ, hφ, rfl⟩))

/-- An assignment of assertions to nodes is an inductive invariant of `G`: each
of its Hoare sentences is a consequence of the theory of `G`. -/
def IsInductive (A : ι → Assn V) : Prop :=
  ∀ n m, (transRoom V ι).Entails G.axioms (TSen.hoare n (A n) m (A m))

/-- Soundness of an inductive invariant: every state reachable from a state
satisfying the assertion at its node satisfies the assertion at its node. -/
theorem IsInductive.holds_of_steps {A : ι → Assn V} (hA : G.IsInductive A)
    {s s' : Config V ι} {w : List ℤ} (hs : (A s.pc).Holds s.env s.mem) (h : G.Steps s w s') :
    (A s'.pc).Holds s'.env s'.mem := by
  induction h with
  | refl => exact hs
  | @head s s₁ _ o _ hstep _ ih =>
    refine ih ?_
    have hax := (G.holds_axioms_iff ⟨s, o, s₁⟩).2 hstep
    exact hA s.pc s₁.pc (CategoryTheory.Discrete.mk ⟨s, o, s₁⟩) hax rfl hs rfl

end Flowgraph

end Silmaril.Courses.Cambridge.OptimisingCompilers
