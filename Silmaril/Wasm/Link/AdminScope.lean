module

public import Silmaril.Wasm.Link.CodeScope
public import Silmaril.Wasm.Execution.Core.Typing.Config

/-! # Annotation scoping for administrative code

Labels retain scoped source continuations and administrative bodies. Nested
frames scope their bodies against their own module's type arena. Execution
typing establishes this invariant without requiring source typing at every step.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.AdminScope

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

def Admin (n : Nat) (a : Execution.Core.Admin) : Prop :=
  match a with
  | .plain i => CodeScope.Instruction n i
  | .label _ cont body => CodeScope.Instructions n cont ∧
      ∀ nested : { a // a ∈ body }, Admin n nested.val
  | .handler _ _ body => ∀ nested : { a // a ∈ body }, Admin n nested.val
  | .frame _ fr body =>
      ∀ nested : { a // a ∈ body }, Admin fr.module.types.length nested.val
  | _ => True
termination_by sizeOf a
decreasing_by
  all_goals have h := List.sizeOf_lt_of_mem nested.property
  all_goals simp_wf
  all_goals omega

def Admins (n : Nat) (xs : List Execution.Core.Admin) : Prop := ∀ a ∈ xs, Admin n a

@[simp] theorem admins_nil (n : Nat) : Admins n [] := by simp [Admins]

@[simp] theorem admins_cons_iff {n : Nat} {a : Execution.Core.Admin}
    {xs : List Execution.Core.Admin} : Admins n (a :: xs) ↔ Admin n a ∧ Admins n xs := by
  simp [Admins]

@[simp] theorem admins_singleton_iff {n : Nat} {a : Execution.Core.Admin} :
    Admins n [a] ↔ Admin n a := by simp [Admins]

@[simp] theorem admins_append_iff {n : Nat} {xs ys : List Execution.Core.Admin} :
    Admins n (xs ++ ys) ↔ Admins n xs ∧ Admins n ys := by
  simp only [Admins,List.mem_append,or_imp,forall_and]

theorem append {n : Nat} {xs ys : List Execution.Core.Admin}
    (hx : Admins n xs) (hy : Admins n ys) : Admins n (xs ++ ys) :=
  admins_append_iff.mpr ⟨hx,hy⟩

theorem split {n : Nat} {xs ys : List Execution.Core.Admin}
    (h : Admins n (xs ++ ys)) : Admins n xs ∧ Admins n ys := admins_append_iff.mp h

theorem member {n : Nat} {xs : List Execution.Core.Admin} (h : Admins n xs)
    {a : Execution.Core.Admin} (ha : a ∈ xs) : Admin n a := h a ha

theorem subset {n : Nat} {xs ys : List Execution.Core.Admin} (h : Admins n ys)
    (hxy : ∀ a ∈ xs, a ∈ ys) : Admins n xs := fun a ha => h a (hxy a ha)

theorem expression_scope {n : Nat} {xs : List Instr} :
    Admins n (expression xs) ↔ CodeScope.Instructions n xs := by
  simp [Admins,expression,Admin,CodeScope.Instructions]

theorem vals_scope (n : Nat) (vs : List Val) : Admins n (vals vs) := by
  intro a ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
  cases v with
  | num v => rcases v with ⟨⟨t⟩ | ⟨t⟩,b⟩ <;> simp [Val.toAdmin,Admin,CodeScope.Instruction]
  | vec _ => simp [Val.toAdmin,Admin,CodeScope.Instruction]
  | ref _ => simp [Val.toAdmin,Admin]

@[simp] theorem plain_scope {n : Nat} {i : Instr} :
    Admin n (.plain i) ↔ CodeScope.Instruction n i := by rw [Admin]

@[simp] theorem label_scope {n k : Nat} {cont : List Instr} {body : List Execution.Core.Admin} :
    Admin n (.label k cont body) ↔ CodeScope.Instructions n cont ∧ Admins n body := by
  simp [Admin,Admins]

@[simp] theorem handler_scope {n k : Nat} {cs : List Catch} {body : List Execution.Core.Admin} :
    Admin n (.handler k cs body) ↔ Admins n body := by simp [Admin,Admins]

@[simp] theorem frame_scope {n k : Nat} {fr : Frame} {body : List Execution.Core.Admin} :
    Admin n (.frame k fr body) ↔ Admins fr.module.types.length body := by simp [Admin,Admins]

private theorem initLocals_types (C : Context) (xs : List Nat) :
    (C.initLocals xs).types = C.types :=
  congrArg TypeCtx.types (Context.initLocals_toTypeCtx C xs)

private theorem frame_types {H : Type} {s : Store H} {fr : Frame} {C : Context}
    (hf : FrameOk s fr C) : C.types = fr.module.types := by
  obtain ⟨C₀,lts,hm,_,rfl⟩ := hf
  cases hm
  rfl

theorem admins_scope {H : Type} {s : Store H} {C : Context}
    {xs : List Execution.Core.Admin} {it : InstrType} (valid : AdminsOk s C xs it) :
    Admins C.types.length xs := by
  refine AdminsOk.rec (motive_1 := fun C a _ _ => Admin C.types.length a)
    (motive_2 := fun C xs _ _ => Admins C.types.length xs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ valid
  case refine_1 => intros C i it h; exact plain_scope.mpr (CodeScope.instruction_scope h)
  case refine_2 => intros; simp only [Admin]
  case refine_3 => intros; simp only [Admin]
  case refine_4 => intros; simp only [Admin]
  case refine_5 =>
    intros C k cont body ts' ts xs' xs hn hc hb ihc ihb
    exact label_scope.mpr ⟨expression_scope.mp ihc,ihb⟩
  case refine_6 =>
    intros C C' k fr body ts hf hn hb hok ihb
    apply frame_scope.mpr
    simpa only [frame_types hf] using ihb
  case refine_7 =>
    intros C k cs body ts xs hc hb ihb
    exact handler_scope.mpr ihb
  case refine_8 => intros; simp only [Admin]
  case refine_9 => intros; simp only [Admin,CodeScope.Instruction]
  case refine_10 => intros; exact admins_nil _
  case refine_11 => intros C a it h ih; exact admins_singleton_iff.mpr ih
  case refine_12 =>
    intros C left right params middle results xs ys hl hx hr ihl ihr
    exact append ihl (by simpa only [initLocals_types] using ihr)
  case refine_13 =>
    intros C a rest params middle results xs ys ha hx hr iha ihr
    exact admins_cons_iff.mpr ⟨iha,by simpa only [initLocals_types] using ihr⟩
  case refine_14 => intros C xs it it' h hs hok ih; exact ih
  case refine_15 => intros C xs ts params results inits h hok ih; exact ih

theorem admin_scope {H : Type} {s : Store H} {C : Context}
    {a : Execution.Core.Admin} {it : InstrType} (valid : AdminOk s C a it) :
    Admin C.types.length a := admins_singleton_iff.mp (admins_scope (.single valid))

theorem config_scope {H : Type} {c : Config H} {ts : List CValType}
    (valid : ConfigOk c ts) : Admins c.frame.module.types.length c.code := by
  obtain ⟨C,⟨_,hf⟩,hc⟩ := valid
  simpa only [frame_types hf] using admins_scope hc

end Silmaril.Wasm.Link.GC.AdminScope
