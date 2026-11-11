module

public import Silmaril.Wasm.Auto.XExec.Defs
public import Silmaril.Wasm.Logic.Core.Thms

/-! # `execS` and `xexec`: runs of the small-step semantics

* `exec1S_sound`, `execS_sound`: a successful `execS` is a run (`Steps`), in every profile and
  for every host; `select` by silmaril's `selectTrue`/`selectFalse` head rules, every other
  instruction by `Silmaril.Wasm.Logic.Core.exec1_sound`;
* `execS_eq_exec`: without `select`, `execS` is `exec`;
* `xexec_ok_iff`: `xexec` ends normally exactly when `execS` succeeds, with the same result;
* `xexec_trap_steps`: when `xexec` traps, the code runs to a trap in the store and frame
  `xexec` reports (`binop-trap` for the trapping operator).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.XExec

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.XExec
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem exec1S_of_ne {s : Store H} {f : Frame} {rs : List Val} {i : Instr}
    (hi : ∀ ts, i ≠ .select ts) : exec1S s f rs i = exec1 s f rs i := by
  cases i <;> first | rfl | exact absurd rfl (hi _)

theorem selectV_eq {rs rs' : List Val} (h : selectV rs = some rs') :
    ∃ (c : BitVec 32) (v₂ v₁ : Val) (rs₀ : List Val),
      rs = Val.i32 c :: v₂ :: v₁ :: rs₀ ∧ rs' = (if c = 0 then v₂ else v₁) :: rs₀ := by
  unfold selectV at h
  split at h
  · rename_i c v₂ v₁ rs₀ hp
    cases h
    exact ⟨c, v₂, v₁, rs₀, popInt_eq hp, rfl⟩
  · cases h

/-- **`select` is a run**: it pops the condition and two values and pushes one. -/
theorem select_steps {s : Store H} {f : Frame} {c : BitVec 32} {v₂ v₁ : Val}
    {ts : Option (List ValType)} :
    Steps P host ⟨s, f, vals [v₁, v₂, Val.i32 c] ++ [.plain (.select ts)]⟩
      ⟨s, f, vals [if c = 0 then v₂ else v₁]⟩ := by
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl]
    exact .single (.parametric (.selectFalse v₁ v₂ ts))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    exact .single (.parametric (.selectTrue hc))

/-- **One instruction with `select` is a run.** -/
theorem exec1S_sound {s s' : Store H} {f f' : Frame} {rs rs' : List Val} {i : Instr}
    (rest : List Admin) (h : exec1S s f rs i = some (s', f', rs')) :
    Steps P host ⟨s, f, vals rs.reverse ++ .plain i :: rest⟩
      ⟨s', f', vals rs'.reverse ++ rest⟩ := by
  by_cases hi : ∃ ts, i = .select ts
  · obtain ⟨ts, rfl⟩ := hi
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    obtain ⟨c, v₂, v₁, rs₀, rfl, rfl⟩ := selectV_eq hr
    have hs : Steps P host ⟨s, f, vals [Val.i32 c, v₂, v₁].reverse ++ [.plain (.select ts)]⟩
        ⟨s, f, vals [if c = 0 then v₂ else v₁].reverse⟩ := select_steps
    exact steps_top (rs₀ := rs₀) rest hs
  · rw [exec1S_of_ne (fun ts he => hi ⟨ts, he⟩)] at h
    exact exec1_sound rest h

theorem execS_cons (s : Store H) (f : Frame) (rs : List Val) (i : Instr) (is : List Instr) :
    execS s f rs (i :: is) =
      (match exec1S s f rs i with
        | some (s₁, f₁, rs₁) => execS s₁ f₁ rs₁ is
        | none => none) := rfl

/-- **Soundness of `execS`.** -/
theorem execS_sound {s s' : Store H} {f f' : Frame} {rs rs' : List Val} {is : List Instr}
    (rest : List Admin) (h : execS s f rs is = some (s', f', rs')) :
    Steps P host ⟨s, f, vals rs.reverse ++ expression is ++ rest⟩
      ⟨s', f', vals rs'.reverse ++ rest⟩ := by
  induction is generalizing s f rs with
  | nil => cases h; exact Steps.of_eq (by simp)
  | cons i is ih =>
    rw [execS_cons] at h
    split at h
    · rename_i s₁ f₁ rs₁ h₁
      have h₁' := exec1S_sound (P := P) (host := host) (expression is ++ rest) h₁
      rw [expression_cons, List.append_assoc, List.cons_append]
      refine h₁'.trans ?_
      rw [← List.append_assoc]
      exact ih h
    · cases h

/-- Without `select`, `execS` is `exec`. -/
theorem execS_eq_exec (s : Store H) (f : Frame) (rs : List Val) :
    ∀ {is : List Instr}, noSelect is = true → execS s f rs is = exec s f rs is
  | [], _ => rfl
  | i :: is, h => by
    have hi : ∀ ts, i ≠ .select ts := by
      rintro ts rfl; simp [noSelect] at h
    have h' : noSelect is = true := by
      cases i <;> simp_all [noSelect]
    rw [execS_cons, exec_cons, exec1S_of_ne hi]
    cases exec1 s f rs i with
    | none => rfl
    | some r => exact execS_eq_exec _ _ _ h'

theorem xexec_cons (s : Store H) (f : Frame) (rs : List Val) (i : Instr) (is : List Instr) :
    xexec s f rs (i :: is) =
      (match exec1S s f rs i with
        | some (s₁, f₁, rs₁) => xexec s₁ f₁ rs₁ is
        | none => if traps1 rs i then .trap s f else .stuck) := rfl

/-- `xexec` ends normally exactly when `execS` succeeds. -/
theorem xexec_ok_iff {s s' : Store H} {f f' : Frame} {rs rs' : List Val} :
    ∀ {is : List Instr}, xexec s f rs is = .ok s' f' rs' ↔ execS s f rs is = some (s', f', rs')
  | [] => by
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl
  | i :: is => by
    rw [xexec_cons, execS_cons]
    split
    · exact xexec_ok_iff
    · constructor
      · intro h; split at h <;> cases h
      · intro h; cases h

/-- `execS` fails exactly when `xexec` traps or is stuck. -/
theorem execS_none_iff {s : Store H} {f : Frame} {rs : List Val} :
    ∀ {is : List Instr}, execS s f rs is = none ↔ ∀ s' f' rs', xexec s f rs is ≠ .ok s' f' rs'
  | [] => by simp [execS, xexec]
  | i :: is => by
    rw [xexec_cons, execS_cons]
    split
    · exact execS_none_iff
    · simp only [true_iff]
      intro s' f' rs' h
      split at h <;> cases h

theorem traps1_eq {rs : List Val} {i : Instr} (h : traps1 rs i = true) :
    ∃ (t : IntType) (op : IntBinOp) (x y : BitVec t.width) (e : IntTrap) (rs₀ : List Val),
      i = .intBinOp t op ∧ rs = .num ⟨.int t, y⟩ :: .num ⟨.int t, x⟩ :: rs₀ ∧
        intBinOp t op x y = .error e := by
  cases i <;> simp only [traps1, Bool.false_eq_true] at h
  rename_i t op
  split at h
  · rename_i y rs₁ hy
    split at h
    · rename_i x rs₀ hx
      split at h
      · rename_i e he
        refine ⟨t, op, x, y, e, rs₀, rfl, ?_, he⟩
        rw [popInt_eq hy, popInt_eq hx]
      · cases h
    · cases h
  · cases h

/-- The trapping instruction reduces to a trap. -/
theorem trap1_steps {s : Store H} {f : Frame} {rs : List Val} {i : Instr} (rest : List Admin)
    (h : traps1 rs i = true) : ∃ us : List Val,
      Steps P host ⟨s, f, vals rs.reverse ++ .plain i :: rest⟩ ⟨s, f, vals us ++ .trap :: rest⟩ := by
  obtain ⟨t, op, x, y, e, rs₀, rfl, rfl, he⟩ := traps1_eq h
  refine ⟨rs₀.reverse, ?_⟩
  have h₁ : Steps P host ⟨s, f, vals [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] ++ [.plain (.intBinOp t op)]⟩
      ⟨s, f, [.trap]⟩ :=
    .single (.numeric (.intBinOpTrap he))
  have k := Steps.ctx (P := P) (host := host) rs₀.reverse rest h₁
  simpa [vals, List.reverse_cons, List.append_assoc] using k

/-- **A trap of `xexec` is a run to a trap**, in the store and frame it reports. -/
theorem xexec_trap_steps {s s' : Store H} {f f' : Frame} {rs : List Val} (rest : List Admin) :
    ∀ {is : List Instr}, xexec s f rs is = .trap s' f' → ∃ (us : List Val) (rest' : List Admin),
      Steps P host ⟨s, f, vals rs.reverse ++ expression is ++ rest⟩
        ⟨s', f', vals us ++ .trap :: rest'⟩
  | [], h => by cases h
  | i :: is, h => by
    rw [xexec_cons] at h
    split at h
    · rename_i s₁ f₁ rs₁ h₁
      obtain ⟨us, rest', k⟩ := xexec_trap_steps rest h
      refine ⟨us, rest', ?_⟩
      have h₁' := exec1S_sound (P := P) (host := host) (expression is ++ rest) h₁
      rw [expression_cons, List.append_assoc, List.cons_append]
      refine h₁'.trans ?_
      rw [← List.append_assoc]
      exact k
    · split at h
      · rename_i ht
        cases h
        obtain ⟨us, k⟩ := trap1_steps (P := P) (host := host) (s := s) (f := f)
          (expression is ++ rest) ht
        exact ⟨us, expression is ++ rest, by simpa [List.append_assoc] using k⟩
      · cases h

end Silmaril.Proofs.Wasm.Auto.XExec