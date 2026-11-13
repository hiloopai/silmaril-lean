module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTreeTyp

/-!
# Vector trees: straight-line vector code inside labels and frames, with traps

Round 8's `VecWhole.cover_vec` covers code with no label, frame or trap. A **vector tree**
(`VecCode`) also admits `TRAP`, and labels and frames whose bodies are vector trees. Such code
arises when vector code runs inside a block or a call: the label or frame is already there, and
the steps are the vector redexes under the contexts, the exits `label-vals` and `frame-vals`, and
the trap rules.

* `ExitBase`: the V2 exit and trap steps, `trap-vals` with its suffix plain (as `expression is`
  with every instruction of straight-line vector code), and `TreeBase P`: a covered vector redex
  (`VecWhole.VecBase P`) or an exit.
* **`cover_tree`**: every V2 step from a vector tree whose code is `Whole.Tail20` (round 6's
  plain-tail invariant) is a `Whole.Nest20 (TreeBase P)` step. `br`, `return` and every other
  instruction are excluded by the tree, and the suffix of `trap-vals` is plain by `Tail20`.
* `vecCode_nest`: nested covered steps keep the code a vector tree.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTree

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim20.VecWhole (vecOkI vecOkA VecBase VecSrc)
open Silmaril.Wasm.SpecTec.Sim20.Whole (Nest20 Tail20)

variable {H : Type}

/-! ## The code -/

/-- **An administrative instruction of a vector tree.** -/
inductive VecTreeA : Admin → Prop where
  | plain {i : V2.Instr} : vecOkI i = true → VecTreeA (.plain i)
  | funcAddr (a : FuncAddr) : VecTreeA (.refFuncAddr a)
  | hostAddr (a : HostAddr) : VecTreeA (.refHostAddr a)
  | trap : VecTreeA .trap
  | label (n : Nat) (cont : List V2.Instr) {body : List Admin} :
      (∀ a ∈ body, VecTreeA a) → VecTreeA (.label n cont body)
  | frame (n : Nat) (fr : Frame) {body : List Admin} :
      (∀ a ∈ body, VecTreeA a) → VecTreeA (.frame n fr body)

/-- **A vector tree**: every instruction is one. -/
def VecCode (l : List Admin) : Prop := ∀ a ∈ l, VecTreeA a

@[simp] theorem vecTreeA_plain_iff {i : V2.Instr} : VecTreeA (.plain i) ↔ vecOkI i = true :=
  ⟨fun h => by cases h; assumption, .plain⟩

@[simp] theorem vecTreeA_trap : VecTreeA .trap := .trap

@[simp] theorem not_vecTreeA_callAddr (a : FuncAddr) : ¬ VecTreeA (.callAddr a) := nofun

theorem vecTreeA_label_iff {n : Nat} {cont : List V2.Instr} {body : List Admin} :
    VecTreeA (.label n cont body) ↔ VecCode body :=
  ⟨fun h => by cases h; assumption, .label n cont⟩

theorem vecTreeA_frame_iff {n : Nat} {fr : Frame} {body : List Admin} :
    VecTreeA (.frame n fr body) ↔ VecCode body :=
  ⟨fun h => by cases h; assumption, .frame n fr⟩

@[simp] theorem vecCode_nil : VecCode [] := nofun

@[simp] theorem vecCode_cons {a : Admin} {l : List Admin} :
    VecCode (a :: l) ↔ VecTreeA a ∧ VecCode l := by
  simp [VecCode]

@[simp] theorem vecCode_append {l₁ l₂ : List Admin} :
    VecCode (l₁ ++ l₂) ↔ VecCode l₁ ∧ VecCode l₂ := by
  simp only [VecCode, List.mem_append]
  exact ⟨fun h => ⟨fun a ha => h a (.inl ha), fun a ha => h a (.inr ha)⟩,
    fun ⟨h₁, h₂⟩ a ha => ha.elim (h₁ a) (h₂ a)⟩

theorem vecTreeA_toAdmin (v : Val) : VecTreeA v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | (_ | _ | _) <;> first | exact .plain rfl | constructor

@[simp] theorem vecCode_vals (vs : List Val) : VecCode (vals vs) := by
  intro a ha
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
  exact vecTreeA_toAdmin v

@[simp] theorem vecCode_trap : VecCode [.trap] := by simp [VecTreeA.trap]

theorem vecCode_expression {is : List V2.Instr} :
    VecCode (expression is) ↔ is.all vecOkI = true := by
  simp [VecCode, expression, List.all_eq_true]

/-- Straight-line vector code is a vector tree. -/
theorem vecCode_of_vecOk {l : List Admin} (h : l.all vecOkA = true) : VecCode l := by
  intro a ha
  have := List.all_eq_true.1 h a ha
  cases a <;> simp_all [vecOkA] <;> constructor

/-! ## The exits -/

/-- **The V2 exit and trap steps**, with the suffix of `trap-vals` plain vector code. -/
inductive ExitBase : Config H → Config H → Prop where
  | labelVals {s : Store H} {f : Frame} {n : Nat} {cont : List V2.Instr} {vs : List Val} :
      ExitBase ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩
  | frameVals {s : Store H} {f fr : Frame} {vs : List Val} :
      ExitBase ⟨s, f, [.frame vs.length fr (vals vs)]⟩ ⟨s, f, vals vs⟩
  | trapVals {s : Store H} {f : Frame} {vs : List Val} {is : List V2.Instr}
      (hne : vs ≠ [] ∨ expression is ≠ []) (hok : is.all vecOkI = true) :
      ExitBase ⟨s, f, vals vs ++ [.trap] ++ expression is⟩ ⟨s, f, [.trap]⟩
  | trapLabel {s : Store H} {f : Frame} {n : Nat} {cont : List V2.Instr} :
      ExitBase ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩
  | trapFrame {s : Store H} {f fr : Frame} {n : Nat} :
      ExitBase ⟨s, f, [.frame n fr [.trap]]⟩ ⟨s, f, [.trap]⟩

/-- **The base steps of a vector tree**: a covered vector redex, or an exit. -/
inductive TreeBase (P : Profile) : Config H → Config H → Prop where
  | vec {c c' : Config H} : VecBase P c c' → TreeBase P c c'
  | exit {c c' : Config H} : ExitBase c c' → TreeBase P c c'

/-! ## Coverage -/

/-- The suffix of a trap, in `Tail20` code, is plain. -/
theorem trap_rest_plain {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    (ht : Tail20 s f (vals vs ++ [.trap] ++ rest)) : ∃ is, rest = expression is :=
  Whole.Tail20.plain_after (a := vs) (y := .trap) (by simpa using ht) rfl
    Whole.not_pendOp_trap

/-- `trap-vals` from a vector tree is an exit. -/
theorem exit_trapVals {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (hok : VecCode (vals vs ++ [.trap] ++ rest))
    (ht : Tail20 s f (vals vs ++ [.trap] ++ rest)) :
    ExitBase ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩ := by
  obtain ⟨is, rfl⟩ := trap_rest_plain ht
  refine .trapVals hne (vecCode_expression.1 ?_)
  simp only [vecCode_append] at hok
  exact hok.2

/-- **Every pure step from a vector tree is a covered base step.** -/
theorem treeBase_of_pure {P : Profile} {s : Store H} {f : Frame} {is is' : List Admin}
    (hp : PureStep P is is') (hok : VecCode is) (ht : Tail20 s f is) :
    TreeBase P ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  by_cases hall : is.all vecOkA = true
  · exact .vec (.mk (VecWhole.vecSrc_of_pureStep hp hall) hp)
  cases hp with
  | labelVals => exact .exit .labelVals
  | frameVals hn => subst hn; exact .exit .frameVals
  | trapVals hne => exact .exit (exit_trapVals hne hok ht)
  | trapLabel => exact .exit .trapLabel
  | trapFrame => exact .exit .trapFrame
  | _ =>
    exfalso
    simp_all [vecTreeA_label_iff, vecTreeA_frame_iff, vecOkI, vecOkA]

/-- No read step starts in a vector tree. -/
theorem not_readStep_tree {s : Store H} {f : Frame} {is is' : List Admin}
    (hr : ReadStep s f is is') (hok : VecCode is) : False := by
  cases hr <;> simp_all [vecOkI]

/-- **Every V2 step from a vector tree with plain tails is a nested covered base step.** -/
theorem cover_tree {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hok : VecCode c.code) (ht : Tail20 c.store c.frame c.code) :
    Nest20 (TreeBase P) c c' := by
  induction h with
  | pure hp => exact .base (treeBase_of_pure hp hok ht)
  | read hr => exact (not_readStep_tree hr hok).elim
  | ctxtInstrs hstep hne ih =>
    simp only [vecCode_append] at hok
    exact .ctx (ih hok.1.2 (Whole.tail20_ctx hstep.not_allVals ht)) hne
  | ctxtLabel _ ih =>
    simp only [vecCode_cons, vecTreeA_label_iff] at hok
    exact .label (ih hok.1 (Whole.tail20_label ht).tail)
  | ctxtFrame _ ih =>
    simp only [vecCode_cons, vecTreeA_frame_iff] at hok
    exact .frame (ih hok.1 (Whole.tail20_frame ht).tail)
  | _ => exfalso; simp_all [vecOkI, constI32]

/-! ## The code stays a vector tree -/

/-- A base step keeps the code a vector tree. -/
theorem vecCode_base {P : Profile} {c c' : Config H} (h : TreeBase P c c') (hok : VecCode c.code) :
    VecCode c'.code := by
  cases h with
  | vec h =>
    obtain ⟨hs, hp⟩ := h
    obtain ⟨v, rfl⟩ := VecWhole.val_of_vecSrc hs hp
    simpa using vecTreeA_toAdmin v
  | exit h =>
    cases h with
    | labelVals => simp
    | frameVals => simp
    | trapVals => simp
    | trapLabel => simp
    | trapFrame => simp

/-- **Nested covered steps keep the code a vector tree.** -/
theorem vecCode_nest {P : Profile} {c c' : Config H} (h : Nest20 (TreeBase P) c c')
    (hok : VecCode c.code) : VecCode c'.code := by
  induction h with
  | base h => exact vecCode_base h hok
  | ctx _ _ ih =>
    simp only [vecCode_append] at hok ⊢
    exact ⟨⟨hok.1.1, ih hok.1.2⟩, hok.2⟩
  | label _ ih =>
    simp only [vecCode_cons, vecTreeA_label_iff, vecCode_nil, and_true] at hok ⊢
    exact ih hok
  | frame _ ih =>
    simp only [vecCode_cons, vecTreeA_frame_iff, vecCode_nil, and_true] at hok ⊢
    exact ih hok

end Silmaril.Wasm.SpecTec.Sim20.VecTree
