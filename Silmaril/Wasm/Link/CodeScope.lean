module

public import Silmaril.Wasm.Link.ControlViews
public import Silmaril.Wasm.Execution.Core.Typing.Store

/-! # Source annotation scoping from instruction typing

Inline cast/block annotations and indexed tail-call annotations are read even
when an instruction has no successful type lookup premise in its reduction
rule. Typing bounds these annotations recursively through every source body.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.CodeScope

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

def Instruction (n : Nat) (i : Instr) : Prop :=
  match i with
  | .block bt body | .loop bt body | .tryTable bt _ body =>
      ControlViews.BlockScoped n bt ∧ ∀ nested : { i // i ∈ body }, Instruction n nested.val
  | .if_ bt yes no => ControlViews.BlockScoped n bt ∧
      (∀ nested : { i // i ∈ yes }, Instruction n nested.val) ∧
      (∀ nested : { i // i ∈ no }, Instruction n nested.val)
  | .refTest rt | .refCast rt => rt.Scoped n
  | .brOnCast _ rt₁ rt₂ | .brOnCastFail _ rt₁ rt₂ => rt₁.Scoped n ∧ rt₂.Scoped n
  | .returnCallRef x => x.toNat < n
  | _ => True
termination_by sizeOf i
decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem nested.property
  all_goals simp_wf
  all_goals omega

def Instructions (n : Nat) (xs : List Instr) : Prop := ∀ i ∈ xs, Instruction n i

theorem reference_scope {C : Context} {i : Instr} {it : InstrType}
    (valid : RefInstrOk C i it) : Instruction C.types.length i := by
  cases valid <;> simp only [Instruction] <;> try trivial
  case refTest valid _ _ => exact ControlViews.ref_scope_of_typing valid
  case refCast valid _ _ => exact ControlViews.ref_scope_of_typing valid

private theorem withLocals_types (C : Context) (xs : List Nat) (lts : List LocalType) :
    (C.withLocals xs lts).types = C.types := by
  induction xs generalizing C lts with
  | nil => rfl
  | cons x xs ih =>
    cases lts with
    | nil => rfl
    | cons lt lts => exact ih (C.setLocal x lt) lts

private theorem initLocals_types (C : Context) (xs : List Nat) :
    (C.initLocals xs).types = C.types := withLocals_types _ _ _

theorem instructions_scope {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) : Instructions C.types.length is := by
  refine InstrsOk.rec (motive_1 := fun C i _ _ => Instruction C.types.length i)
    (motive_2 := fun C is _ _ => Instructions C.types.length is) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  case refine_1 => intros C i it valid; cases valid <;> simp only [Instruction]
  case refine_2 => intros C i it valid; cases valid <;> simp only [Instruction]
  case refine_3 => intros C i it valid; cases valid <;> simp only [Instruction]
  case refine_4 => intros C i it valid; cases valid <;> simp only [Instruction]
  case refine_5 => intros C i it valid; cases valid <;> simp only [Instruction]
  case refine_6 => intros C i it valid; cases valid <;> simp only [Instruction]
  case refine_7 => intros C i it valid; exact reference_scope valid
  case refine_8 =>
    intros C bt body params results xs ht hb ih
    rw [Instruction]
    exact ⟨ControlViews.block_scope_of_typing ht, fun nested => ih _ nested.property⟩
  case refine_9 =>
    intros C bt body params results xs ht hb ih
    rw [Instruction]
    exact ⟨ControlViews.block_scope_of_typing ht, fun nested => ih _ nested.property⟩
  case refine_10 =>
    intros C bt yes no params results xs ys ht hy hn ihy ihn
    rw [Instruction]
    exact ⟨ControlViews.block_scope_of_typing ht, fun nested => ihy _ nested.property,
      fun nested => ihn _ nested.property⟩
  case refine_16 =>
    intros C l rt₁ rt₂ ts rt hl h₁ h₂ hs₁ hs₂
    rw [Instruction]
    exact ⟨ControlViews.ref_scope_of_typing h₁, ControlViews.ref_scope_of_typing h₂⟩
  case refine_17 =>
    intros C l rt₁ rt₂ ts rt hl h₁ h₂ hs₁ hs₂
    rw [Instruction]
    exact ⟨ControlViews.ref_scope_of_typing h₁, ControlViews.ref_scope_of_typing h₂⟩
  case refine_23 =>
    intros C x d ps rs rs' t₃ t₄ hd he hr hs hok
    rw [Instruction]
    exact (List.getElem?_eq_some_iff.mp hd).1
  case refine_27 =>
    intros C bt cs body params results xs ht hb hc ih
    rw [Instruction]
    exact ⟨ControlViews.block_scope_of_typing ht, fun nested => ih _ nested.property⟩
  case refine_28 => intros C i hi; simp only [List.not_mem_nil] at hi
  case refine_29 =>
    intros C i it valid ih j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact ih
  case refine_30 =>
    intros C left right params middle results xs ys hl hx hr ihl ihr i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ihl i hi
    · simpa only [initLocals_types] using ihr i hi
  case refine_31 =>
    intros C i is params middle results xs ys hi hx hs ihi ihs j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ihi
    · simpa only [initLocals_types] using ihs j hj
  case refine_32 => intros C is it it' valid hs hok ih; exact ih
  case refine_33 => intros C is ts t₁ t₂ xs valid hok ih; exact ih
  all_goals intros; simp only [Instruction]

theorem instruction_scope {C : Context} {i : Instr} {it : InstrType}
    (valid : InstrOk C i it) : Instruction C.types.length i :=
  instructions_scope (.instr valid) i (by simp only [List.mem_singleton])

theorem function_scope {C : Context} {f : Func} {d : DefType}
    (valid : FuncOk C f d) : Instructions C.types.length f.body := by
  cases valid with
  | mk _ _ _ body => simpa only [Context.funcBody] using instructions_scope body

theorem stored_function_scope {H : Type} {s : Store H} {fi : FuncInst H} {code : Func}
    (valid : FuncInstOk s fi) (wasm : fi.code = .wasm code) :
    Instructions fi.module.types.length code.body := by
  cases valid with
  | wasm _ module codeEq body _ =>
    cases codeEq.symm.trans wasm
    cases module
    exact function_scope body
  | host _ _ codeEq => cases codeEq.symm.trans wasm

theorem store_scope {H : Type} {s : Store H} (valid : StoreOk s) {address : Nat}
    {fi : FuncInst H} {code : Func} (lookup : s.funcs[address]? = some fi)
    (wasm : fi.code = .wasm code) : Instructions fi.module.types.length code.body :=
  stored_function_scope (valid.funcs fi (List.mem_of_getElem? lookup)) wasm

end Silmaril.Wasm.Link.GC.CodeScope
