module

public import Silmaril.Wasm.Logic.V1.Judgement.Defs

/-!
# Soundness of one-instruction programs

Every rule of Figures 6, 7 and 8 — the basic, variable-management and
memory-management instructions — is a one-instruction program whose instruction
reduces by `Execution.Plain` or traps by `Execution.PlainTrap`. `valid_single`
discharges the common part once: the inversion of the execution, the matching of
the precondition's stack against the instruction's operands, and the framing
bookkeeping.

`valid_single_gen` is the same statement with the instruction's operand list
left general and constrained by an equation. That is the form to use: in
`Plain s f args i s' f' rets` the operand list is an *earlier* index than the
instruction, so `cases` on a derivation whose operand list is the concrete
`S.map (fun τ => τ ρ)` fails on an operand equation of some unrelated
constructor before it ever gets to discriminate on the instruction. With `args`
a variable the instruction discriminates first and every irrelevant case
disappears. With the concrete list, `generalize h : S.map (fun τ => τ ρ) = args
at step` first restores the same situation.

The specialisations save the callers the bookkeeping they never need:
`valid_single_heap` for an instruction that leaves the abstract variable store
alone, `valid_single_emp` for one that additionally leaves the heap alone, and
`valid_single_stack` for the `(S | emp)` precondition. `valid_single_pure` is
`valid_single_emp` with the postcondition in the `(S' | emp ∧ ψ)` shape too.

`Instr.IsSafe` and `not_plainTrap` discharge the trapping premises in one step
for the instructions that have no `Execution.PlainTrap` rule at all.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

/-- The instructions whose execution is an `Execution.Plain` or
`Execution.PlainTrap` rule: everything but structured control, branches, calls
and `return`. -/
def Instr.IsPlain : Silmaril.Wasm.V1.Instr → Prop
  | .block .. | .loop .. | .if_ .. | .br .. | .brIf .. | .brTable ..
  | .call .. | .callIndirect .. | .return_ => False
  | _ => True

/-- The instructions with no `Execution.PlainTrap` rule: the ones that cannot
trap, whatever their operands are. -/
def Instr.IsSafe : Silmaril.Wasm.V1.Instr → Prop
  | .unreachable | .intBinOp .. | .convert ..
  | .intLoad .. | .floatLoad .. | .intStore .. | .floatStore .. => False
  | _ => True

variable {H : Type*}

/-- An `Instr.IsSafe` instruction never traps. This discharges both the
`arityTrap` and the `noTrap` premises below at once. -/
theorem not_plainTrap {s : Store H} {f : Frame} {args : List Value} {i : Silmaril.Wasm.V1.Instr}
    (trap : PlainTrap s f args i) (safe : Instr.IsSafe i := by trivial) : False := by
  cases trap <;> exact safe.elim

/-- Inversion of the execution of a single non-control instruction: it either
takes an `Execution.Plain` step and stops, or it traps. -/
private theorem single_inv {host : HostSemantics H} {n : Nat} {s : Store H} {f : Frame}
    {vs : List Value} {i : Silmaril.Wasm.V1.Instr} {o : Outcome H} (isPlain : Instr.IsPlain i)
    (run : BigStepN host n s f vs [(.source i : Admin)] o) :
    (∃ (s' : Store H) (f' : Frame) (args rets vs₀ : List Value),
        vs = vs₀ ++ args ∧ Plain s f args i s' f' rets ∧
          o = ⟨s', f', .normal (vs₀ ++ rets)⟩) ∨
      (∃ args vs₀ : List Value,
        vs = vs₀ ++ args ∧ PlainTrap s f args i ∧ o = ⟨s, f, .trap⟩) := by
  cases run
  case plain =>
    rename_i s' f' args rets vs₀ step rest
    exact .inl ⟨s', f', args, rets, vs₀, rfl, step, rest.nil_inv⟩
  case plainTrap =>
    rename_i args vs₀ step
    exact .inr ⟨args, vs₀, rfl, step, rfl⟩
  all_goals exact isPlain.elim

/-- Soundness of a one-instruction program, with the instruction's operand list
left general: the workhorse behind every rule of Figures 6, 7 and 8. -/
theorem valid_single_gen {host : HostSemantics H} {n : Nat} {F : List FuncDef}
    {L : List Assert} {R : Option Assert} {i : Silmaril.Wasm.V1.Instr} {S : List (Term Value)}
    {Hp : HAssert} {Q : Assert}
    (isPlain : Instr.IsPlain i)
    (arity : ∀ (s s' : Store H) (f f' : Frame) (args rets : List Value),
      Plain s f args i s' f' rets → args.length = S.length)
    (arityTrap : ∀ (s : Store H) (f : Frame) (args : List Value),
      PlainTrap s f args i → args.length = S.length)
    (noTrap : ∀ (s : Store H) (f : Frame) (ρ : Sto) (h hf : AHeap) (args : List Value),
      args = S.map (fun τ => τ ρ) → Hp ρ h → AHeap.Disj h hf → Reifies F s f ρ (h ∪ hf) →
      ¬ PlainTrap s f args i)
    (effect : ∀ (s s' : Store H) (f f' : Frame) (ρ : Sto) (h hf : AHeap)
        (args rets : List Value),
      args = S.map (fun τ => τ ρ) → Hp ρ h → AHeap.Disj h hf → Reifies F s f ρ (h ∪ hf) →
      Plain s f args i s' f' rets →
      ∃ h' ρ', AHeap.Disj h' hf ∧ Reifies F s' f' ρ' (h' ∪ hf) ∧
        (∀ x, x ∉ Instr.modified i → ρ' x = ρ x) ∧ Q ρ' rets h') :
    Valid host n F L R (Assert.mk S Hp) [i] Q := by
  intro s f ρ vs vf h hf o pre disj reify run
  obtain ⟨rfl, hp⟩ := pre
  have run' : BigStepN host n s f (vf ++ S.map (fun τ => τ ρ)) [(.source i : Admin)] o := run
  rcases single_inv isPlain run' with
    ⟨s', f', args, rets, vs₀, heq, step, rfl⟩ | ⟨args, vs₀, heq, step, rfl⟩
  · have hlen : args.length = S.length := arity s s' f f' args rets step
    obtain ⟨rfl, hargs⟩ : vf = vs₀ ∧ S.map (fun τ => τ ρ) = args :=
      List.append_inj' heq (by simp [hlen])
    obtain ⟨h', ρ', disj', reify', agree, q⟩ :=
      effect s s' f f' ρ h hf args rets hargs.symm hp disj reify step
    exact ⟨h', ρ', disj', reify', by simpa using agree, rets, rfl, q⟩
  · have hlen : args.length = S.length := arityTrap s f args step
    obtain ⟨rfl, hargs⟩ : vf = vs₀ ∧ S.map (fun τ => τ ρ) = args :=
      List.append_inj' heq (by simp [hlen])
    exact absurd step (noTrap s f ρ h hf args hargs.symm hp disj reify)

/-- Soundness of a one-instruction program, given the instruction's effect on
the abstract state. -/
theorem valid_single {host : HostSemantics H} {n : Nat} {F : List FuncDef} {L : List Assert}
    {R : Option Assert} {i : Silmaril.Wasm.V1.Instr} {S : List (Term Value)} {Hp : HAssert} {Q : Assert}
    (isPlain : Instr.IsPlain i)
    (arity : ∀ (s s' : Store H) (f f' : Frame) (args rets : List Value),
      Plain s f args i s' f' rets → args.length = S.length)
    (arityTrap : ∀ (s : Store H) (f : Frame) (args : List Value),
      PlainTrap s f args i → args.length = S.length)
    (noTrap : ∀ (s : Store H) (f : Frame) (ρ : Sto) (h hf : AHeap),
      Hp ρ h → AHeap.Disj h hf → Reifies F s f ρ (h ∪ hf) →
      ¬ PlainTrap s f (S.map (fun τ => τ ρ)) i)
    (effect : ∀ (s s' : Store H) (f f' : Frame) (ρ : Sto) (h hf : AHeap) (rets : List Value),
      Hp ρ h → AHeap.Disj h hf → Reifies F s f ρ (h ∪ hf) →
      Plain s f (S.map (fun τ => τ ρ)) i s' f' rets →
      ∃ h' ρ', AHeap.Disj h' hf ∧ Reifies F s' f' ρ' (h' ∪ hf) ∧
        (∀ x, x ∉ Instr.modified i → ρ' x = ρ x) ∧ Q ρ' rets h') :
    Valid host n F L R (Assert.mk S Hp) [i] Q :=
  valid_single_gen isPlain arity arityTrap
    (fun s f ρ h hf _ hargs => hargs ▸ noTrap s f ρ h hf)
    (fun s s' f f' ρ h hf _ rets hargs hp disj reify step =>
      effect s s' f f' ρ h hf rets hp disj reify (hargs ▸ step))

/-- `valid_single_gen` for an instruction that leaves the abstract variable
store alone: the final store is `ρ` itself. -/
theorem valid_single_heap {host : HostSemantics H} {n : Nat} {F : List FuncDef}
    {L : List Assert} {R : Option Assert} {i : Silmaril.Wasm.V1.Instr} {S : List (Term Value)}
    {Hp : HAssert} {Q : Assert}
    (isPlain : Instr.IsPlain i)
    (arity : ∀ (s s' : Store H) (f f' : Frame) (args rets : List Value),
      Plain s f args i s' f' rets → args.length = S.length)
    (arityTrap : ∀ (s : Store H) (f : Frame) (args : List Value),
      PlainTrap s f args i → args.length = S.length)
    (noTrap : ∀ (s : Store H) (f : Frame) (ρ : Sto) (h hf : AHeap) (args : List Value),
      args = S.map (fun τ => τ ρ) → Hp ρ h → AHeap.Disj h hf → Reifies F s f ρ (h ∪ hf) →
      ¬ PlainTrap s f args i)
    (effect : ∀ (s s' : Store H) (f f' : Frame) (ρ : Sto) (h hf : AHeap)
        (args rets : List Value),
      args = S.map (fun τ => τ ρ) → Hp ρ h → AHeap.Disj h hf → Reifies F s f ρ (h ∪ hf) →
      Plain s f args i s' f' rets →
      ∃ h', AHeap.Disj h' hf ∧ Reifies F s' f' ρ (h' ∪ hf) ∧ Q ρ rets h') :
    Valid host n F L R (Assert.mk S Hp) [i] Q :=
  valid_single_gen isPlain arity arityTrap noTrap (by
    intro s s' f f' ρ h hf args rets hargs hp disj reify step
    obtain ⟨h', disj', reify', q⟩ :=
      effect s s' f f' ρ h hf args rets hargs hp disj reify step
    exact ⟨h', ρ, disj', reify', fun _ _ => rfl, q⟩)

/-- `valid_single_gen` for an instruction that touches neither the heap nor any
variable, with an arbitrary postcondition: the precondition's heap part is
`emp ∧ φ`, so the whole heap is the frame `hf`. -/
theorem valid_single_emp {host : HostSemantics H} {n : Nat} {F : List FuncDef}
    {L : List Assert} {R : Option Assert} {i : Silmaril.Wasm.V1.Instr} {S : List (Term Value)}
    {φ : Sto → Prop} {Q : Assert}
    (isPlain : Instr.IsPlain i)
    (arity : ∀ (s s' : Store H) (f f' : Frame) (args rets : List Value),
      Plain s f args i s' f' rets → args.length = S.length)
    (arityTrap : ∀ (s : Store H) (f : Frame) (args : List Value),
      PlainTrap s f args i → args.length = S.length)
    (noTrap : ∀ (s : Store H) (f : Frame) (ρ : Sto) (hf : AHeap) (args : List Value),
      args = S.map (fun τ => τ ρ) → φ ρ → Reifies F s f ρ hf → ¬ PlainTrap s f args i)
    (effect : ∀ (s s' : Store H) (f f' : Frame) (ρ : Sto) (hf : AHeap)
        (args rets : List Value),
      args = S.map (fun τ => τ ρ) → φ ρ → Reifies F s f ρ hf →
      Plain s f args i s' f' rets →
      Reifies F s' f' ρ hf ∧ Q ρ rets AHeap.emp) :
    Valid host n F L R (Assert.mk S (HAssert.empAnd φ)) [i] Q := by
  refine valid_single_heap isPlain arity arityTrap ?_ ?_
  · rintro s f ρ h hf args hargs ⟨rfl, hφ⟩ - reify
    exact noTrap s f ρ hf args hargs hφ (by simpa using reify)
  · rintro s s' f f' ρ h hf args rets hargs ⟨rfl, hφ⟩ disj reify step
    obtain ⟨reify', q⟩ :=
      effect s s' f f' ρ hf args rets hargs hφ (by simpa using reify) step
    exact ⟨AHeap.emp, disj, by simpa using reify', q⟩

/-- `valid_single_emp` with a precondition of the paper's `(S | emp)` shape. -/
theorem valid_single_stack {host : HostSemantics H} {n : Nat} {F : List FuncDef}
    {L : List Assert} {R : Option Assert} {i : Silmaril.Wasm.V1.Instr} {S : List (Term Value)} {Q : Assert}
    (isPlain : Instr.IsPlain i)
    (arity : ∀ (s s' : Store H) (f f' : Frame) (args rets : List Value),
      Plain s f args i s' f' rets → args.length = S.length)
    (arityTrap : ∀ (s : Store H) (f : Frame) (args : List Value),
      PlainTrap s f args i → args.length = S.length)
    (noTrap : ∀ (s : Store H) (f : Frame) (ρ : Sto) (hf : AHeap) (args : List Value),
      args = S.map (fun τ => τ ρ) → Reifies F s f ρ hf → ¬ PlainTrap s f args i)
    (effect : ∀ (s s' : Store H) (f f' : Frame) (ρ : Sto) (hf : AHeap)
        (args rets : List Value),
      args = S.map (fun τ => τ ρ) → Reifies F s f ρ hf → Plain s f args i s' f' rets →
      Reifies F s' f' ρ hf ∧ Q ρ rets AHeap.emp) :
    Valid host n F L R (Assert.stack S) [i] Q := by
  refine valid_single_heap (Hp := HAssert.emp) isPlain arity arityTrap ?_ ?_
  · rintro s f ρ h hf args hargs rfl - reify
    exact noTrap s f ρ hf args hargs (by simpa using reify)
  · rintro s s' f f' ρ h hf args rets hargs rfl disj reify step
    obtain ⟨reify', q⟩ := effect s s' f f' ρ hf args rets hargs (by simpa using reify) step
    exact ⟨AHeap.emp, disj, by simpa using reify', q⟩

/-- The common case: the instruction touches neither the heap nor any variable,
so the precondition's heap part is `emp ∧ φ`. -/
theorem valid_single_pure {host : HostSemantics H} {n : Nat} {F : List FuncDef}
    {L : List Assert} {R : Option Assert} {i : Silmaril.Wasm.V1.Instr} {S S' : List (Term Value)}
    {φ ψ : Sto → Prop}
    (isPlain : Instr.IsPlain i)
    (arity : ∀ (s s' : Store H) (f f' : Frame) (args rets : List Value),
      Plain s f args i s' f' rets → args.length = S.length)
    (arityTrap : ∀ (s : Store H) (f : Frame) (args : List Value),
      PlainTrap s f args i → args.length = S.length)
    (noTrap : ∀ (s : Store H) (f : Frame) (ρ : Sto), φ ρ →
      ¬ PlainTrap s f (S.map (fun τ => τ ρ)) i)
    (effect : ∀ (s s' : Store H) (f f' : Frame) (ρ : Sto) (rets : List Value), φ ρ →
      Plain s f (S.map (fun τ => τ ρ)) i s' f' rets →
      s' = s ∧ f' = f ∧ rets = S'.map (fun τ => τ ρ) ∧ ψ ρ) :
    Valid host n F L R (Assert.mk S (HAssert.empAnd φ)) [i]
      (Assert.mk S' (HAssert.empAnd ψ)) := by
  refine valid_single_emp isPlain arity arityTrap
    (fun s f ρ _ args hargs hφ _ => hargs ▸ noTrap s f ρ hφ) ?_
  rintro s s' f f' ρ hf args rets rfl hφ reify step
  obtain ⟨rfl, rfl, rfl, hψ⟩ := effect s s' f f' ρ rets hφ step
  exact ⟨reify, rfl, rfl, hψ⟩

end Silmaril.Wasm.Logic.V1
