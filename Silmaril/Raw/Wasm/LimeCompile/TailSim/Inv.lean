module

public import Silmaril.Wasm.Execution.Core.Sim.Closure.Basic

/-!
# The two-way simulation of the tail-call rewrite: inversion of control heads

`CtlHead s f us i is'` lists the rules of `Step` whose code is `val* i` for the six control
instructions that the tail rewrite touches or produces (`block`, `loop`, `if`, `call`,
`return_call`, `call_indirect`, `return_call_indirect`). `ctl_inv`: a step of `val* i ++ []`
for such an `i` is one of these rules on a suffix of the values, under `ctxt-instrs`, with store
and frame unchanged. `CtlHead.step`: each of them is a step.

New proofs (the case analysis follows silmaril's `Closure.struct_match_aux`).
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-- The control instructions handled by `ctl_inv`. -/
def IsCtl : Instr → Prop
  | .block _ _ | .loop _ _ | .if_ _ _ _ | .call _ | .returnCall _ | .callIndirect _ _
  | .returnCallIndirect _ _ => True
  | _ => False

theorem IsCtl.val?_eq {i : Instr} (hi : IsCtl i) : (Admin.plain i).val? = none := by
  cases i <;> first | rfl | exact (hi : False).elim

theorem IsCtl.not_isCallRef {i : Instr} (hi : IsCtl i) : ¬ (Admin.plain i).IsCallRef := by
  cases i <;> first | exact (hi : False).elim | exact id

theorem IsCtl.not_isReturnCallRef {i : Instr} (hi : IsCtl i) :
    ¬ (Admin.plain i).IsReturnCallRef := by
  cases i <;> first | exact (hi : False).elim | exact id

/-- The head rules of the control instructions. -/
inductive CtlHead (s : Store H) (f : Frame) : List Val → Instr → List Admin → Prop where
  | block {bt : BlockType} {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      CtlHead s f vs (.block bt body) [.label t₂.length [] (vals vs ++ expression body)]
  | loop {bt : BlockType} {body : List Instr} {vs : List Val} {t₁ t₂ : List CValType}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length) :
      CtlHead s f vs (.loop bt body) [.label t₁.length [.loop bt body] (vals vs ++ expression body)]
  | ifTrue {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr} (hc : c ≠ 0) :
      CtlHead s f [Val.i32 c] (.if_ bt b₁ b₂) [.plain (.block bt b₁)]
  | ifFalse {bt : BlockType} {b₁ b₂ : List Instr} :
      CtlHead s f [Val.i32 0] (.if_ bt b₁ b₂) [.plain (.block bt b₂)]
  | call {x : FuncIdx} {a : Nat} {fi : FuncInst H} (hx : f.module.funcs[x.toNat]? = some a)
      (hf : s.funcs[a]? = some fi) :
      CtlHead s f [] (.call x) [.ref (.func a), .callRefType fi.type]
  | returnCall {x : FuncIdx} {a : Nat} {fi : FuncInst H} (hx : f.module.funcs[x.toNat]? = some a)
      (hf : s.funcs[a]? = some fi) :
      CtlHead s f [] (.returnCall x) [.ref (.func a), .returnCallRefType fi.type]
  | callIndirect {x : TableIdx} {y : TypeIdx} :
      CtlHead s f [] (.callIndirect x y)
        [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.callRef y)]
  | returnCallIndirect {x : TableIdx} {y : TypeIdx} :
      CtlHead s f [] (.returnCallIndirect x y)
        [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.returnCallRef y)]

/-- Each control head rule is a step. -/
theorem CtlHead.step {s : Store H} {f : Frame} {us : List Val} {i : Instr} {is' : List Admin}
    (h : CtlHead s f us i is') : Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s, f, is'⟩ := by
  cases h with
  | block hbt hm => exact .block hbt hm
  | loop hbt hm => exact .loop hbt hm
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | call hx hf => exact .call hx hf
  | returnCall hx hf => exact .returnCall hx hf
  | callIndirect => exact .callIndirect
  | returnCallIndirect => exact .returnCallIndirect

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- **Inversion of a control head.** -/
theorem ctl_inv_aux {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (i : Instr), c.code = vals us ++ [.plain i] → IsCtl i →
      c'.store = c.store ∧ c'.frame = c.frame ∧ ∃ (ws us₁ : List Val) (is' : List Admin),
        us = ws ++ us₁ ∧ c'.code = vals ws ++ is' ∧ CtlHead c.store c.frame us₁ i is' := by
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us i hc hi
    dsimp only at hc ⊢
    obtain ⟨u₁, b, is₁, hb, rfl⟩ := exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ u₁) ++ b :: (is₁ ++ rest) = vals us ++ Admin.plain i :: [] := by
      rw [← hc]; simp
    obtain ⟨h1, rfl, h3⟩ := vals_append_cons_inj hb hi.val?_eq hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨hs', hf', ws, us₁, is'', rfl, hcode, hh⟩ := ih u₁ i rfl hi
    subst h1
    refine ⟨hs', hf', vs₀ ++ ws, us₁, is'', by simp, ?_, hh⟩
    dsimp only at hcode
    rw [hcode]; simp
  | @block s f bt body vs t₁ t₂ hbt hm =>
    intro us i hc hi
    dsimp only at hc ⊢
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc
    cases hi'
    exact ⟨rfl, rfl, [], vs, _, by simp, by simp [Sim.vals_nil'], .block hbt hm⟩
  | @loop s f bt body vs t₁ t₂ hbt hm =>
    intro us i hc hi
    dsimp only at hc ⊢
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc
    cases hi'
    exact ⟨rfl, rfl, [], vs, _, by simp, by simp [Sim.vals_nil'], .loop hbt hm⟩
  | @ifTrue s f c bt b₁ b₂ hc0 =>
    intro us i hc hi
    have hc' : vals [Val.i32 c] ++ Admin.plain (.if_ bt b₁ b₂) :: [] =
        vals us ++ Admin.plain i :: [] := hc
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc'
    cases hi'
    exact ⟨rfl, rfl, [], _, _, by simp, by simp [Sim.vals_nil'], .ifTrue hc0⟩
  | @ifFalse s f bt b₁ b₂ =>
    intro us i hc hi
    have hc' : vals [Val.i32 0] ++ Admin.plain (.if_ bt b₁ b₂) :: [] =
        vals us ++ Admin.plain i :: [] := hc
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc'
    cases hi'
    exact ⟨rfl, rfl, [], _, _, by simp, by simp [Sim.vals_nil'], .ifFalse⟩
  | @call s f x a fi hx hf =>
    intro us i hc hi
    have hc' : vals [] ++ Admin.plain (.call x) :: [] = vals us ++ Admin.plain i :: [] := hc
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc'
    cases hi'
    exact ⟨rfl, rfl, [], [], _, by simp, by simp [Sim.vals_nil'], .call hx hf⟩
  | @returnCall s f x a fi hx hf =>
    intro us i hc hi
    have hc' : vals [] ++ Admin.plain (.returnCall x) :: [] = vals us ++ Admin.plain i :: [] := hc
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc'
    cases hi'
    exact ⟨rfl, rfl, [], [], _, by simp, by simp [Sim.vals_nil'], .returnCall hx hf⟩
  | @callIndirect s f x y =>
    intro us i hc hi
    have hc' : vals [] ++ Admin.plain (.callIndirect x y) :: [] =
        vals us ++ Admin.plain i :: [] := hc
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc'
    cases hi'
    exact ⟨rfl, rfl, [], [], _, by simp, by simp [Sim.vals_nil'], .callIndirect⟩
  | @returnCallIndirect s f x y =>
    intro us i hc hi
    have hc' : vals [] ++ Admin.plain (.returnCallIndirect x y) :: [] =
        vals us ++ Admin.plain i :: [] := hc
    obtain ⟨rfl, hi', -⟩ := vals_append_cons_inj rfl hi.val?_eq hc'
    cases hi'
    exact ⟨rfl, rfl, [], [], _, by simp, by simp [Sim.vals_nil'], .returnCallIndirect⟩
  | @trapInstrs s f vs₀ rest hne =>
    intro us i hc hi
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.plain i :: [] := by
      rw [← hc]; simp
    exact absurd (vals_append_cons_inj val?_trap hi.val?_eq hc').2.1 (by simp)
  | @throwRefInstrs s f vs₀ a rest hne =>
    intro us i hc hi
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.plain i :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    have := (vals_append_cons_inj val?_throwRef hi.val?_eq hc').2.1
    cases this
    exact (hi : False).elim
  | _ =>
    intro us i hc hi
    have hnc := hi.not_isCallRef
    have hnr := hi.not_isReturnCallRef
    first
      | (((have := congrArg List.getLast? hc
           simp [constI32, Val.i32, Val.toAdmin] at this) <;> (try subst this) <;>
          first | exact (hi : False).elim | simp_all [IsCtl]) <;> done)
      | (rename_i hf; cases hf <;>
          (have := congrArg List.getLast? hc; simp [constI32, Val.i32, Val.toAdmin] at this) <;>
          (try subst this) <;>
          first | exact (hi : False).elim | simp_all [IsCtl] <;> done)

/-- **Inversion of a control head** (configuration form). -/
theorem ctl_inv {s s' : Store H} {f f' : Frame} {us : List Val} {i : Instr} {es' : List Admin}
    (hi : IsCtl i) (h : Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ ∃ (ws us₁ : List Val) (is' : List Admin),
      us = ws ++ us₁ ∧ es' = vals ws ++ is' ∧ CtlHead s f us₁ i is' :=
  ctl_inv_aux h us i rfl hi

end Silmaril.Raw.Wasm.LimeCompile.TailSim
