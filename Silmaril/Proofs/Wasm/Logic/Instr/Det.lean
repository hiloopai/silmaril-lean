module

public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Instr.Defs

/-!
# Instruction rules: the generic family rules

Every non-control plain instruction (`famOf` other than `.control`: parametric,
numeric, vector, variable, table, memory, reference and aggregate instructions)
reduces by one rule of its silmaril-lean reduction family, applied to the values
right below it. This file derives two generic rules from the head rule
`Safe.head`:

* `Safe.fam`/`HWP.fam`/`TSafe.fam` (**every result**): if the instruction has
  some head step on the arguments `args`, and every head step on `args` leads to
  safe code, the instruction is safe. No other split of the operand stack can
  step (`Head.split_unique`: the arity of a family rule is fixed by the
  instruction and, for `struct.new`/`array.new_fixed`, the store and frame). This
  rule covers nondeterministic instructions (floats and NaNs, relaxed SIMD,
  `memory.grow`/`table.grow`) in every profile.
* `Safe.det`/`HWP.det`/`TSafe.det` (**one witness**): for an instruction whose
  head steps do not consult the profile (`ProfileFree`), one head step is the
  only one (`Head.unique`), so its result is the only continuation to prove.
  The proof moves both steps to a deterministic profile (`Head.toDet`) and uses
  silmaril-lean's `Det.Head.det_fam`.

A Silmaril addition, built on silmaril-lean's determinism toolkit
(`Silmaril.Wasm.SingleThreaded.Determinism.{Family,HeadDet,FamDet*}`).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det (Head famOf famOf_of_shape Fam FamRel)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

section Transport

variable {s : Store H} {f : Frame}

/-- The last instruction of a family left-hand side is profile free. -/
def LastFree (l : List Admin) : Prop := ∀ i, l.getLast? = some (.plain i) → ProfileFree i

theorem lastFree_of {args : List Val} {i : Instr} (h : ProfileFree i) :
    LastFree (vals args ++ [.plain i]) := by
  intro i' hi
  have hi' : i = i' := by simpa using hi
  exact hi' ▸ h

/-- Close a transport case: a profile-dependent rule contradicts `LastFree`, any
other rule is the same rule in the deterministic profile. -/
local macro "transport_case" hpf:ident : tactic => `(tactic| first
  | exact ($hpf _ rfl).elim
  | (constructor <;> assumption))

theorem numeric_toDet {l r : List Admin} (h : NumericStep P l r) (hpf : LastFree l) :
    NumericStep detP l r := by
  cases h <;> transport_case hpf

theorem vector_toDet {l r : List Admin} (h : VectorStep P l r) (hpf : LastFree l) :
    VectorStep detP l r := by
  cases h <;> transport_case hpf

theorem table_toDet {l : List Admin} {c : Config H} (h : TableStep P ⟨s, f, l⟩ c)
    (hpf : LastFree l) : TableStep detP ⟨s, f, l⟩ c := by
  cases h <;> transport_case hpf

theorem memory_toDet {l : List Admin} {c : Config H} (h : MemoryStep P ⟨s, f, l⟩ c)
    (hpf : LastFree l) : MemoryStep detP ⟨s, f, l⟩ c := by
  cases h <;> transport_case hpf

/-- A head step of a profile-free family instruction is a head step in the
deterministic profile. -/
theorem Head.toDet {args : List Val} {i : Instr} {c : Config H}
    (h : Head P s f args (.plain i) c) (hpf : ProfileFree i) :
    Head detP s f args (.plain i) c := by
  have hl : LastFree (vals args ++ [.plain i]) := lastFree_of hpf
  cases h with
  | parametric h => exact .parametric h
  | numeric h => exact .numeric (numeric_toDet h hl)
  | vector h => exact .vector (vector_toDet h hl)
  | «variable» h => exact .variable h
  | table h => exact .table (table_toDet h hl)
  | memory h => exact .memory (memory_toDet h hl)
  | reference h => exact .reference h
  | aggregate h => exact .aggregate h
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse hc => exact .ifFalse hc
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse hc => exact .brIfFalse hc
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | brOnNullNull => exact .brOnNullNull
  | brOnNullAddr hv => exact .brOnNullAddr hv
  | brOnNonNullNull => exact .brOnNonNullNull
  | brOnNonNullAddr hv => exact .brOnNonNullAddr hv
  | brOnCastSucceed h => exact .brOnCastSucceed h
  | brOnCastFail h => exact .brOnCastFail h
  | brOnCastFailSucceed h => exact .brOnCastFailSucceed h
  | brOnCastFailFail h => exact .brOnCastFailFail h
  | call hx hf => exact .call hx hf
  | callRefNull hc => exact .callRefNull hc
  | callRefFunc ha hc hf he hn hcode => exact .callRefFunc ha hc hf he hn hcode
  | returnCall hx hf => exact .returnCall hx hf
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect
  | throw ht he hn => exact .throw ht he hn
  | throwRefNull => exact .throwRefNull
  | tryTable hbt hm => exact .tryTable hbt hm

end Transport

/-! ## Splitting the operand stack -/

theorem split_of_length {us₁ us₂ args₁ args₂ : List Val} (hW : us₁ ++ args₁ = us₂ ++ args₂)
    (hn : args₁.length = args₂.length) : us₁ = us₂ ∧ args₁ = args₂ :=
  List.append_inj hW (by
    have h₁ : (us₁ ++ args₁).length = (us₂ ++ args₂).length := congrArg List.length hW
    simp only [List.length_append] at h₁
    omega)

/-- Two splits of an operand stack agree if neither argument list can be a
proper extension of the other. -/
theorem split_of_suffix {us₁ us₂ args₁ args₂ : List Val}
    (h₁ : ∀ p, args₁ = p ++ args₂ → p = []) (h₂ : ∀ p, args₂ = p ++ args₁ → p = [])
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ := by
  rcases List.append_eq_append_iff.mp hW with ⟨a', hu, ha⟩ | ⟨c', hu, ha⟩
  · have hp : a' = [] := h₁ a' ha
    subst hp
    exact ⟨by simpa using hu.symm, by simpa using ha⟩
  · have hp : c' = [] := h₂ c' ha
    subst hp
    exact ⟨by simpa using hu, by simpa using ha.symm⟩

/-! ## Arities -/

/-- The number of operands a numeric instruction takes. -/
def numArity : Instr → Nat
  | .intUnOp .. | .floatUnOp .. | .intTestOp .. | .convert _ => 1
  | _ => 2

/-- The number of operands a vector instruction takes. -/
def vecArity : Instr → Nat
  | .vecBinOp _ | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntRelOp .. | .vecFloatRelOp ..
  | .vecShiftOp .. | .vecSwizzle _ | .vecShuffle _ | .vecReplaceLane .. | .vecExtBinOp ..
  | .vecNarrow .. => 2
  | .vecTernOp _ | .vecIntTernOp .. | .vecFloatTernOp .. | .vecExtTernOp .. => 3
  | _ => 1

/-- The number of operands a table instruction takes. -/
def tableArity : Instr → Nat
  | .tableGet _ => 1
  | .tableSet _ | .tableGrow _ => 2
  | .tableSize _ | .elemDrop _ => 0
  | _ => 3

/-- The number of operands a memory instruction takes. -/
def memArity : Instr → Nat
  | .intLoad .. | .floatLoad .. | .vecLoad .. | .memoryGrow _ => 1
  | .intStore .. | .floatStore .. | .vecStore .. | .vecLoadLane .. | .vecStoreLane .. => 2
  | .memorySize _ | .dataDrop _ => 0
  | _ => 3

/-- Read off the arity of a family rule from its left-hand side. -/
local macro "arity_case" hl:ident : tactic => `(tactic| (
  have h₁ := congrArg List.length $hl
  have h₂ := congrArg List.getLast? $hl
  simp only [List.length_append, vals_length, List.length_cons, List.length_nil,
    List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
    Option.some_or, Option.some.injEq, Admin.plain.injEq] at h₁ h₂
  subst h₂
  simp only [numArity, vecArity, tableArity, memArity] at h₁ ⊢
  omega))

theorem NumericStep.arity {args : List Val} {i : Instr} {r : List Admin}
    (h : NumericStep P (vals args ++ [.plain i]) r) : args.length = numArity i := by
  generalize hl : vals args ++ [.plain i] = l at h
  cases h <;> arity_case hl

theorem VectorStep.arity {args : List Val} {i : Instr} {r : List Admin}
    (h : VectorStep P (vals args ++ [.plain i]) r) : args.length = vecArity i := by
  generalize hl : vals args ++ [.plain i] = l at h
  cases h <;> arity_case hl

theorem TableStep.arity {s : Store H} {f : Frame} {args : List Val} {i : Instr} {c : Config H}
    (h : TableStep P ⟨s, f, vals args ++ [.plain i]⟩ c) : args.length = tableArity i := by
  generalize hl : vals args ++ [.plain i] = l at h
  cases h <;> arity_case hl

theorem MemoryStep.arity {s : Store H} {f : Frame} {args : List Val} {i : Instr} {c : Config H}
    (h : MemoryStep P ⟨s, f, vals args ++ [.plain i]⟩ c) : args.length = memArity i := by
  generalize hl : vals args ++ [.plain i] = l at h
  cases h <;> arity_case hl

/-! ## Uniqueness of head steps -/

theorem lhs_eq {args₁ args₂ p : List Val} {e : Admin} (hp : args₁ = p ++ args₂) :
    vals args₁ ++ [e] = vals p ++ (vals args₂ ++ [e]) := by
  rw [hp]; simp

section Split

variable {s : Store H} {f : Frame} {us₁ us₂ args₁ args₂ : List Val} {i : Instr}
  {c₁ c₂ : Config H}

/-- Splits for two steps of a family whose rules are deterministic. -/
theorem split_of_det {R : List Admin → Prop} (hR₁ : R (vals args₁ ++ [.plain i]))
    (hR₂ : R (vals args₂ ++ [.plain i]))
    (hdet : ∀ {l₁ l₂ : List Admin} {p : List Val}, R l₁ → R l₂ → l₁ = vals p ++ l₂ → p = [])
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ :=
  split_of_suffix (fun _ hp => hdet hR₁ hR₂ (lhs_eq hp)) (fun _ hp => hdet hR₂ hR₁ (lhs_eq hp)) hW

theorem split_parametric
    (f₁ : FamRel P .parametric s f (vals args₁ ++ [.plain i]) c₁)
    (f₂ : FamRel P .parametric s f (vals args₂ ++ [.plain i]) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ :=
  split_of_det (R := fun l => ∃ r, ParametricStep l r) ⟨_, f₁.choose_spec.1⟩ ⟨_, f₂.choose_spec.1⟩
    (fun ⟨_, r₁⟩ ⟨_, r₂⟩ hl => (SingleThreaded.Det.ParametricStep.det r₁ r₂ hl).1) hW

theorem split_numeric
    (f₁ : FamRel P .numeric s f (vals args₁ ++ [.plain i]) c₁)
    (f₂ : FamRel P .numeric s f (vals args₂ ++ [.plain i]) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ :=
  split_of_length hW ((NumericStep.arity f₁.choose_spec.1).trans
    (NumericStep.arity f₂.choose_spec.1).symm)

theorem split_vector
    (f₁ : FamRel P .vector s f (vals args₁ ++ [.plain i]) c₁)
    (f₂ : FamRel P .vector s f (vals args₂ ++ [.plain i]) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ :=
  split_of_length hW ((VectorStep.arity f₁.choose_spec.1).trans
    (VectorStep.arity f₂.choose_spec.1).symm)

theorem split_variable
    (f₁ : FamRel P .variable s f (vals args₁ ++ [.plain i]) c₁)
    (f₂ : FamRel P .variable s f (vals args₂ ++ [.plain i]) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ :=
  split_of_det (R := fun l => ∃ c, VariableStep ⟨s, f, l⟩ c) ⟨_, f₁⟩ ⟨_, f₂⟩
    (fun ⟨_, r₁⟩ ⟨_, r₂⟩ hl => (SingleThreaded.Det.VariableStep.det r₁ r₂ hl).1) hW

theorem split_reference
    (f₁ : FamRel P .reference s f (vals args₁ ++ [.plain i]) c₁)
    (f₂ : FamRel P .reference s f (vals args₂ ++ [.plain i]) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ :=
  split_of_det (R := fun l => ∃ c, RefStep ⟨s, f, l⟩ c) ⟨_, f₁⟩ ⟨_, f₂⟩
    (fun ⟨_, r₁⟩ ⟨_, r₂⟩ hl => (SingleThreaded.Det.RefStep.det r₁ r₂ hl).1) hW

theorem split_aggregate
    (f₁ : FamRel P .aggregate s f (vals args₁ ++ [.plain i]) c₁)
    (f₂ : FamRel P .aggregate s f (vals args₂ ++ [.plain i]) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ :=
  split_of_det (R := fun l => ∃ c, AggregateStep ⟨s, f, l⟩ c) ⟨_, f₁⟩ ⟨_, f₂⟩
    (fun ⟨_, r₁⟩ ⟨_, r₂⟩ hl => (SingleThreaded.Det.AggregateStep.det r₁ r₂ hl).1) hW

/-- Splits for two steps of the same family. -/
theorem split_famRel {k : Fam} (hk : k ≠ .control)
    (f₁ : FamRel P k s f (vals args₁ ++ [.plain i]) c₁)
    (f₂ : FamRel P k s f (vals args₂ ++ [.plain i]) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ := by
  cases k with
  | parametric => exact split_parametric f₁ f₂ hW
  | numeric => exact split_numeric f₁ f₂ hW
  | vector => exact split_vector f₁ f₂ hW
  | «variable» => exact split_variable f₁ f₂ hW
  | table => exact split_of_length hW ((TableStep.arity f₁).trans (TableStep.arity f₂).symm)
  | memory => exact split_of_length hW ((MemoryStep.arity f₁).trans (MemoryStep.arity f₂).symm)
  | reference => exact split_reference f₁ f₂ hW
  | aggregate => exact split_aggregate f₁ f₂ hW
  | control => exact absurd rfl hk

/-- **The arity of a family instruction is fixed**: two head steps of the same
non-control instruction under the same operand stack use the same split. -/
theorem Head.split_unique (hfam : famOf (.plain i) ≠ .control)
    (h₁ : Head P s f args₁ (.plain i) c₁) (h₂ : Head P s f args₂ (.plain i) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ :=
  split_famRel hfam (h₁.fam_inv hfam) (h₂.fam_inv hfam) hW

end Split

/-- **Determinism of profile-free family instructions**, in every profile. -/
theorem Head.unique {s : Store H} {f : Frame} {us₁ us₂ args₁ args₂ : List Val} {i : Instr}
    {c₁ c₂ : Config H} (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i)
    (h₁ : Head P s f args₁ (.plain i) c₁) (h₂ : Head P s f args₂ (.plain i) c₂)
    (hW : us₁ ++ args₁ = us₂ ++ args₂) : us₁ = us₂ ∧ args₁ = args₂ ∧ c₁ = c₂ := by
  obtain ⟨rfl, rfl⟩ := Head.split_unique hfam h₁ h₂ hW
  exact ⟨rfl, rfl, (SingleThreaded.Det.Head.det_fam (p := []) hfam (Head.toDet h₁ hpf) (Head.toDet h₂ hpf)
    rfl).2⟩

/-- A family instruction is inert. -/
theorem inert_of_fam {i : Instr} (hfam : famOf (.plain i) ≠ .control) : Inert i := by
  cases i <;> simp [famOf, Inert, Admin.val?, Admin.isCallRef] at hfam ⊢

/-! ## The generic rules -/

/-- The head rule for total safety. -/
theorem TSafe.head {s : Store H} {f : Frame} {W : List Val} {i : Instr} {rest : List Admin}
    {Q : Post H} (hi : Inert i)
    (hp : ∃ vs args c₀, W = vs ++ args ∧ Head P s f args (.plain i) c₀)
    (hs : ∀ vs args c₀, W = vs ++ args → Head P s f args (.plain i) c₀ →
      TSafe P host Q ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩) :
    TSafe P host Q ⟨s, f, vals W ++ .plain i :: rest⟩ := by
  obtain ⟨vs, args, ⟨s₀, f₀, c₀⟩, rfl, hh⟩ := hp
  have h₁ : Step P host ⟨s, f, vals args ++ [.plain i]⟩ ⟨s₀, f₀, c₀⟩ :=
    Step.of_noHost host hh.toStep
  have h₂ : Step P host ⟨s, f, vals (vs ++ args) ++ .plain i :: rest⟩
      ⟨s₀, f₀, vals vs ++ c₀ ++ rest⟩ := by
    simpa using Sim.Step.append_right (Sim.Step.vals_left h₁ vs) rest
  refine TSafe.step ⟨_, h₂⟩ fun c' hst => ?_
  obtain ⟨vs', args', c₁, hW, hh', rfl⟩ := SingleThreaded.inert_head_inv hi.1 hi.2.1 hi.2.2 hst
  exact hs vs' args' c₁ hW hh'

section Generic

variable {s : Store H} {f : Frame} {us args : List Val} {i : Instr} {rest : List Admin}
  {Q : Post H}

/-- **The family rule** (every result): a family instruction on the arguments
`args` is safe for `n + 1` steps if it has a head step there and every head step
there leads to code safe for `n` steps. -/
theorem Safe.fam {n : Nat} (hfam : famOf (.plain i) ≠ .control)
    (hp : ∃ c₀, Head P s f args (.plain i) c₀)
    (h : ∀ c₀, Head P s f args (.plain i) c₀ →
      Safe P host Q n ⟨c₀.store, c₀.frame, vals us ++ c₀.code ++ rest⟩) :
    Safe P host Q (n + 1) ⟨s, f, vals (us ++ args) ++ .plain i :: rest⟩ := by
  obtain ⟨c₁, h₁⟩ := hp
  refine Safe.head (inert_of_fam hfam) ⟨us, args, c₁, rfl, h₁⟩ fun vs args' c₀ hW hh => ?_
  obtain ⟨rfl, rfl⟩ := Head.split_unique hfam h₁ hh hW
  exact h c₀ hh

/-- **The family rule** for every-run weakest preconditions. -/
theorem HWP.fam (hfam : famOf (.plain i) ≠ .control) (hp : ∃ c₀, Head P s f args (.plain i) c₀)
    (h : ∀ c₀, Head P s f args (.plain i) c₀ →
      HWP P host c₀.store c₀.frame (vals us ++ c₀.code ++ rest) Q) :
    HWP P host s f (vals (us ++ args) ++ .plain i :: rest) Q
  | 0 => trivial
  | n + 1 => Safe.fam hfam hp fun c₀ hh => h c₀ hh n

/-- **The family rule** for total correctness. -/
theorem TWP.fam (hfam : famOf (.plain i) ≠ .control) (hp : ∃ c₀, Head P s f args (.plain i) c₀)
    (h : ∀ c₀, Head P s f args (.plain i) c₀ →
      TWP P host c₀.store c₀.frame (vals us ++ c₀.code ++ rest) Q) :
    TWP P host s f (vals (us ++ args) ++ .plain i :: rest) Q := by
  obtain ⟨c₁, h₁⟩ := hp
  refine TSafe.head (inert_of_fam hfam) ⟨us, args, c₁, rfl, h₁⟩ fun vs args' c₀ hW hh => ?_
  obtain ⟨rfl, rfl⟩ := Head.split_unique hfam h₁ hh hW
  exact h c₀ hh

variable {c₁ : Config H}

/-- **The deterministic rule** (one witness): a profile-free family instruction
with a head step `h₁` is safe for `n + 1` steps if the result of `h₁` is safe for
`n` steps. -/
theorem Safe.det {n : Nat} (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i)
    (h₁ : Head P s f args (.plain i) c₁)
    (h : Safe P host Q n ⟨c₁.store, c₁.frame, vals us ++ c₁.code ++ rest⟩) :
    Safe P host Q (n + 1) ⟨s, f, vals (us ++ args) ++ .plain i :: rest⟩ :=
  Safe.fam hfam ⟨c₁, h₁⟩ fun c₀ hh => by
    obtain ⟨-, -, rfl⟩ := Head.unique (us₁ := []) hfam hpf h₁ hh rfl
    exact h

/-- **The deterministic rule** for every-run weakest preconditions. -/
theorem HWP.det (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i)
    (h₁ : Head P s f args (.plain i) c₁)
    (h : HWP P host c₁.store c₁.frame (vals us ++ c₁.code ++ rest) Q) :
    HWP P host s f (vals (us ++ args) ++ .plain i :: rest) Q
  | 0 => trivial
  | n + 1 => Safe.det hfam hpf h₁ (h n)

/-- **The deterministic rule** for total correctness. -/
theorem TWP.det (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i)
    (h₁ : Head P s f args (.plain i) c₁)
    (h : TWP P host c₁.store c₁.frame (vals us ++ c₁.code ++ rest) Q) :
    TWP P host s f (vals (us ++ args) ++ .plain i :: rest) Q :=
  TWP.fam hfam ⟨c₁, h₁⟩ fun c₀ hh => by
    obtain ⟨-, -, rfl⟩ := Head.unique (us₁ := []) hfam hpf h₁ hh rfl
    exact h

end Generic

/-! ## Both readings at once -/

section Wp

variable {m : Corr} {s : Store H} {f : Frame} {us args : List Val} {i : Instr}
  {rest : List Admin} {Q : Post H}

/-- **The family rule** in either reading. -/
theorem Wp.fam (hfam : famOf (.plain i) ≠ .control) (hp : ∃ c₀, Head P s f args (.plain i) c₀)
    (h : ∀ c₀, Head P s f args (.plain i) c₀ →
      Wp m P host c₀.store c₀.frame (vals us ++ c₀.code ++ rest) Q) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q := by
  cases m
  · exact HWP.fam hfam hp h
  · exact TWP.fam hfam hp h

/-- **The deterministic rule** in either reading. -/
theorem Wp.det {c₁ : Config H} (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i)
    (h₁ : Head P s f args (.plain i) c₁)
    (h : Wp m P host c₁.store c₁.frame (vals us ++ c₁.code ++ rest) Q) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q := by
  cases m
  · exact HWP.det hfam hpf h₁ h
  · exact TWP.det hfam hpf h₁ h

/-- The deterministic rule for an instruction that leaves values. -/
theorem Wp.detVals {s' : Store H} {f' : Frame} {res : List Val}
    (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i)
    (h₁ : Head P s f args (.plain i) ⟨s', f', vals res⟩)
    (h : Wp m P host s' f' (vals (us ++ res) ++ rest) Q) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q :=
  Wp.det hfam hpf h₁ (by simpa using h)

/-- An exit satisfying the postcondition. -/
theorem Wp.of_exits {code : List Admin} {o : Outcome} (he : Exits o code) (hq : Q s f o) :
    Wp m P host s f code Q := by
  cases m
  · exact HWP.of_exits he hq
  · exact TSafe.exit o he hq

/-- Final values satisfying the postcondition. -/
theorem Wp.of_vals {vs : List Val} (hq : Q s f (.normal vs)) : Wp m P host s f (vals vs) Q :=
  Wp.of_exits (o := .normal vs) rfl hq

/-- A trap, with values before it and dead code after it. -/
theorem Wp.trap (hq : Q s f .trap) : Wp m P host s f (vals us ++ .trap :: rest) Q :=
  Wp.of_exits (o := .trap) ⟨us, rest, rfl⟩ hq

/-- The deterministic rule for an instruction that traps. -/
theorem Wp.detTrap {s' : Store H} {f' : Frame} (hfam : famOf (.plain i) ≠ .control)
    (hpf : ProfileFree i) (h₁ : Head P s f args (.plain i) ⟨s', f', [.trap]⟩)
    (hq : Q s' f' .trap) : Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q :=
  Wp.det hfam hpf h₁ (by simpa using Wp.trap (us := us) (rest := rest) hq)

/-- Either reading gives partial correctness. -/
theorem Wp.hwp {code : List Admin} (h : Wp m P host s f code Q) : HWP P host s f code Q := by
  cases m
  · exact h
  · exact TWP.hwp h

end Wp

end Silmaril.Wasm.Logic.Hoare
