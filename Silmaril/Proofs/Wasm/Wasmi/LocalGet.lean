module

public import Silmaril.Wasm.Execution.Core.Sim.Context

@[expose] public section

/-!
# Inversion of a `local.get` redex

`Step.localGet_inv`: a step of `val* (local.get x)` reads the local: the store and frame are
unchanged and the code becomes `val* v` with `f.local? x = some (some v)`. Proved as
silmaril-lean's `Step.trap_redex_aux` (`Silmaril/Wasm/Execution/Core/Sim/Segments.lean`):
induction on the step, `ctxt-instrs` by the induction hypothesis on the first non-value, every
other rule by its last instruction. New proof.
-/

namespace Silmaril.Proofs.Wasm.Wasmi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The conclusion of the inversion, for a step `c ~> c'`. -/
def LocalGetIH (c c' : Config H) : Prop :=
  ∀ (us : List Val) (x : LocalIdx), c.code = vals us ++ [.plain (.localGet x)] →
    c'.store = c.store ∧ c'.frame = c.frame ∧
    ∃ v, c.frame.local? x = some (some v) ∧ c'.code = vals us ++ [v.toAdmin]

/-- `ctxt-instrs`: the first non-value of the inner code is the `local.get`. -/
theorem localGet_ctxt {s s' : Store H} {f f' : Frame} {vs₀ : List Val} {is is' rest : List Admin}
    (hs : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (ih : LocalGetIH ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    LocalGetIH ⟨s, f, vals vs₀ ++ is ++ rest⟩ ⟨s', f', vals vs₀ ++ is' ++ rest⟩ := by
  intro us x hc
  obtain ⟨u₁, b, is₁, hb, his⟩ : ∃ u₁ b is₁, b.val? = none ∧ is = vals u₁ ++ b :: is₁ :=
    exists_head_of_not_all hs.not_all_isVal
  have hc' : vals (vs₀ ++ u₁) ++ b :: (is₁ ++ rest) =
      vals us ++ Admin.plain (.localGet x) :: [] := by
    rw [← show vals vs₀ ++ is ++ rest = vals us ++ [.plain (.localGet x)] from hc, his]; simp
  obtain ⟨h1, h2, h3⟩ : vs₀ ++ u₁ = us ∧ b = .plain (.localGet x) ∧ is₁ ++ rest = [] :=
    vals_append_cons_inj hb rfl hc'
  have hnil : is₁ = [] ∧ rest = [] := List.append_eq_nil_iff.mp h3
  have hcode : is = vals u₁ ++ [.plain (.localGet x)] := by rw [his, h2, hnil.1]
  obtain ⟨hs', hf', v, hv, he⟩ := ih u₁ x hcode
  refine ⟨hs', hf', v, hv, ?_⟩
  show vals vs₀ ++ is' ++ rest = vals us ++ [v.toAdmin]
  rw [show is' = vals u₁ ++ [v.toAdmin] from he, hnil.2, ← h1]; simp

/-- `local.get` itself. -/
theorem localGet_variable {c c' : Config H} (hv : VariableStep c c') : LocalGetIH c c' := by
  intro us x hc
  cases hv with
  | @localGet s f y v hy =>
    show s = s ∧ f = f ∧ ∃ v', f.local? x = some (some v') ∧ [v.toAdmin] = vals us ++ [v'.toAdmin]
    rcases us with _ | ⟨u, us⟩
    · have hyx : y = x := by simpa [vals_nil'] using hc
      exact ⟨rfl, rfl, v, hyx ▸ hy, by simp [vals_nil']⟩
    · have hl : 1 = us.length + 2 := by simpa using congrArg List.length hc
      omega
  | _ =>
    have hl := congrArg List.getLast? hc
    simp [Val.toAdmin] at hl

/-- `trap-instrs`: its first non-value is `trap`. -/
theorem localGet_trap {s : Store H} {f : Frame} {vs₀ : List Val} {rest : List Admin} {c' : Config H} :
    LocalGetIH (H := H) ⟨s, f, vals vs₀ ++ [.trap] ++ rest⟩ c' := by
  intro us x hc
  have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.plain (.localGet x) :: [] := by
    rw [← hc]; simp
  exact absurd (vals_append_cons_inj val?_trap rfl hc').2.1 (by simp)

/-- `throw_ref-instrs`: its first non-value is `THROW_REF`. -/
theorem localGet_throw {s : Store H} {f : Frame} {vs₀ : List Val} {a : Nat} {rest : List Admin}
    {c' : Config H} : LocalGetIH (H := H) ⟨s, f, vals vs₀ ++ throwing a ++ rest⟩ c' := by
  intro us x hc
  have hc' : vals (vs₀ ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
      vals us ++ Admin.plain (.localGet x) :: [] := by
    rw [← hc]; simp [vals, throwing, Val.toAdmin]
  exact absurd (vals_append_cons_inj val?_throwRef rfl hc').2.1 (by simp)

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem Step.localGet_aux {c c' : Config H} (h : Step P host c c') : LocalGetIH c c' := by
  induction h with
  | ctxtInstrs hs _ ih => exact localGet_ctxt hs ih
  | «variable» hv => exact localGet_variable hv
  | trapInstrs => exact localGet_trap
  | throwRefInstrs => exact localGet_throw
  | _ =>
    intro us x hc
    first
      | (have := congrArg List.getLast? hc; simp at this; done)
      | (have := congrArg List.getLast? hc; simp at this; subst this;
          simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]; done)
      | (rename_i hf; cases hf <;>
          (have := congrArg List.getLast? hc; simp [constI32, Val.i32, Val.toAdmin] at this) <;>
          done)

/-- **`local.get` inversion.** -/
theorem Step.localGet_inv {s s' : Store H} {f f' : Frame} {us : List Val} {x : LocalIdx}
    {es' : List Admin} (h : Step P host ⟨s, f, vals us ++ [.plain (.localGet x)]⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ ∃ v, f.local? x = some (some v) ∧ es' = vals us ++ [v.toAdmin] :=
  Step.localGet_aux h us x rfl

end Silmaril.Proofs.Wasm.Wasmi
