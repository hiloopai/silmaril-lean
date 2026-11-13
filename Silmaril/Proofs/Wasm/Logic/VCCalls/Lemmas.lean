module

public import Silmaril.Wasm.Logic.VC.Defs

/-!
# Call and loop lemmas for evaluating verification conditions with `simp`

Equations proved once, used as pre-rewrites (`↓`) by the tactic `wat_vc_calls`
(`Silmaril.Wasm.Logic.VCCalls.Thms`) so that `simp` does not explore the generic cases:

* `callVC_at`: a call whose callee address `a` and specification `(n, S)` are known is the
  precondition on the top `n` stack values and, for every outcome the postcondition allows,
  `callK`;
* `callVC_fn`: the same for a callee whose postcondition determines the store and the results
  (`s' = E s args ∧ o = .normal (R s args)`, the shape of `pureSpec`/`procSpec`/`fnSpec`-style
  specifications): the call continues with `K` on that store and stack;
* `labelQ_*`, `loopQ_*`: the block and loop postconditions at each outcome constructor, so
  that `simp` rewrites them only once the outcome is known (unfolding `labelQ` itself puts
  the continuation under a `match` on a symbolic outcome, once per nested block);
* `tableVC_*`: `br_table` at a known index selects one entry, without simplifying the
  continuations of the other entries (`simp` simplifies `c = j → K l` in full even when
  `c = j` is false);
* `forall_inv_eq`: an invariant that fixes the store, the stack and the frame of a loop
  (`s' = s ∧ a = l ∧ f' = F`) instantiates the loop body's condition at them.

Unfolding `callVC` instead makes `simp` simplify both branches of its `match` (with a symbolic
callee address and arity) and the whole continuation under them before the discriminant is
evaluated; the same happens for a loop body under its universally quantified state. Measured on
`Silmaril.Sim.X86.Max2`. A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.VC

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (FSpec)

variable {H : Type}

/-- A call of a callee with a known address and specification. -/
theorem callVC_at [Γ : VCSpecs H] {m : ModuleInst} {x : FuncIdx} {a n : Nat} {S : FSpec H}
    (hx : m.funcs[x.toNat]? = some a) (hΓ : Γ.specs a = some (n, S)) (s : Store H) (f : Frame)
    (hf : f.module = m) (vs : List Val) (K : Store H → List Val → Prop) (Q : Post H) :
    callVC s f vs x K Q = (n ≤ vs.length ∧ S.pre s (vs.drop (vs.length - n)) ∧
      ∀ s' o, S.post s (vs.drop (vs.length - n)) s' o →
        callK f (vs.take (vs.length - n)) K Q s' o) := by
  subst hf
  simp only [callVC, hx, hΓ]

/-- A call of a callee whose postcondition determines the store (`E`) and the results (`R`). -/
theorem callVC_fn [Γ : VCSpecs H] {m : ModuleInst} {x : FuncIdx} {a n : Nat} {S : FSpec H}
    {E : Store H → List Val → Store H} {R : Store H → List Val → List Val}
    (hx : m.funcs[x.toNat]? = some a) (hΓ : Γ.specs a = some (n, S))
    (hpost : ∀ s args s' o, S.post s args s' o ↔ (s' = E s args ∧ o = .normal (R s args)))
    (s : Store H) (f : Frame) (hf : f.module = m) (vs : List Val) (K : Store H → List Val → Prop)
    (Q : Post H) :
    callVC s f vs x K Q = (n ≤ vs.length ∧ S.pre s (vs.drop (vs.length - n)) ∧
      K (E s (vs.drop (vs.length - n))) (vs.take (vs.length - n) ++ R s (vs.drop (vs.length - n)))) := by
  rw [callVC_at hx hΓ s f hf]
  simp only [hpost]
  apply propext
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h => h _ _ ⟨rfl, rfl⟩, ?_⟩
  rintro h _ _ ⟨rfl, rfl⟩
  exact h

section Q
variable {n : Nat} {us vs : List Val} {K : Store H → Frame → List Val → Prop} {Q : Post H}
  {s : Store H} {f : Frame}

theorem labelQ_normal : labelQ n us K Q s f (.normal vs) = K s f (us ++ vs) := rfl
theorem labelQ_br_zero :
    labelQ n us K Q s f (.br 0 vs) = (n ≤ vs.length ∧ K s f (us ++ vs.drop (vs.length - n))) := rfl
theorem labelQ_br_succ {l : Nat} : labelQ n us K Q s f (.br (l + 1) vs) = Q s f (.br l (us ++ vs)) :=
  rfl
theorem labelQ_ret : labelQ n us K Q s f (.ret vs) = Q s f (.ret (us ++ vs)) := rfl
theorem labelQ_trap : labelQ n us K Q s f .trap = Q s f .trap := rfl
theorem labelQ_throw {a : Nat} : labelQ n us K Q s f (.throw a) = Q s f (.throw a) := rfl
theorem labelQ_tail {a : Nat} {c} :
    labelQ n us K Q s f (.tail vs a c) = Q s f (.tail (us ++ vs) a c) := rfl

variable {I : Store H → Frame → List Val → Prop}

theorem loopQ_normal : loopQ n us I K Q s f (.normal vs) = K s f (us ++ vs) := rfl
theorem loopQ_br_zero :
    loopQ n us I K Q s f (.br 0 vs) = (n ≤ vs.length ∧ I s f (vs.drop (vs.length - n))) := rfl
theorem loopQ_br_succ {l : Nat} : loopQ n us I K Q s f (.br (l + 1) vs) = Q s f (.br l (us ++ vs)) :=
  rfl
theorem loopQ_ret : loopQ n us I K Q s f (.ret vs) = Q s f (.ret (us ++ vs)) := rfl
theorem loopQ_trap : loopQ n us I K Q s f .trap = Q s f .trap := rfl
theorem loopQ_throw {a : Nat} : loopQ n us I K Q s f (.throw a) = Q s f (.throw a) := rfl
theorem loopQ_tail {a : Nat} {c} :
    loopQ n us I K Q s f (.tail vs a c) = Q s f (.tail (us ++ vs) a c) := rfl

end Q

section Table
variable {K : LabelIdx → Prop} {c j : Nat} {l d : LabelIdx} {ls : List LabelIdx}

/-- Past the index, the remaining table entries and the default ask nothing. -/
theorem tableVC_of_lt : ∀ {j : Nat} {ls : List LabelIdx}, c < j → (tableVC K c j ls d ↔ True)
  | _, [], h => by simp only [tableVC, iff_true]; omega
  | _, _ :: _, h => by
    simp only [tableVC, iff_true]
    exact ⟨fun e => absurd e (by omega), (tableVC_of_lt (by omega)).2 trivial⟩

theorem tableVC_cons_of_ne (h : c ≠ j) : tableVC K c j (l :: ls) d = tableVC K c (j + 1) ls d := by
  simp only [tableVC, h, false_implies, true_and]

theorem tableVC_cons_self : tableVC K j j (l :: ls) d = K l := by
  simp only [tableVC, forall_const, (tableVC_of_lt (Nat.lt_succ_self j)).trans Iff.rfl, and_true]

theorem tableVC_nil_of_le (h : j ≤ c) : tableVC K c j [] d = K d := by
  simp only [tableVC, h, forall_const]

end Table

/-- A loop invariant that fixes the store, the stack and the frame. -/
theorem forall_inv_eq {α β γ : Sort _} {x : α} {y : γ} {z : β} {P : α → β → γ → Prop} :
    (∀ a b c, (a = x ∧ c = y ∧ b = z) → P a b c) ↔ P x z y :=
  ⟨fun h => h _ _ _ ⟨rfl, rfl, rfl⟩, fun h _ _ _ ⟨h1, h2, h3⟩ => h1 ▸ h2 ▸ h3 ▸ h⟩

end Silmaril.Wasm.Logic.VC
