module

public import Silmaril.Proofs.Wasm.Auto.XExec.Sound
public import Silmaril.Wasm.Examples.Common.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Total.Thms

/-! # `select`, `execS` and traps in the every-run logic

* `Wp.selectTrue`, `Wp.selectFalse`: the `select` rules, in either reading (`HWP`/`TWP`), every
  profile and host (a profile-free head step, so the rule is deterministic);
* `Wp.intBinOp_trap`: an integer binary operator whose result is an error traps;
* `Wp.exec1S`, `Wp.execS`: an evaluated instruction or sequence (with `select`) is the only
  continuation;
* `wp_steps_inv`: the weakest precondition is kept along any run;
* `wp_xexec_ok_iff`, `wp_xexec_trap_iff`: code that `xexec` evaluates has the weakest
  precondition of its result; for a trap, that is the trap postcondition in the store and frame
  at the trap (forward by `Wp.detTrap`, backward along the run by `Safe.trap_post` and
  `TSafe.trap_post`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.XExec

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.XExec
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf)
open Silmaril.Wasm.Logic.Core (Post exec exec1 popInt popInt_eq expression_cons)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Examples.Common (HeadSpec)

variable {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s s' : Store H}
  {f f' : Frame} {rest : List Admin} {Q : Post H}

/-- **`select` with a non-zero condition** keeps the first value. -/
theorem Wp.selectTrue {us : List Val} {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List ValType)}
    (hc : c ≠ 0) (hk : Wp m P host s f (vals (us ++ [v₁]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v₁, v₂, Val.i32 c]) ++ .plain (.select ts) :: rest) Q :=
  Wp.detVals (args := [v₁, v₂, Val.i32 c]) (res := [v₁]) (by simp [famOf]) trivial
    (.parametric (show ParametricStep (vals [v₁, v₂, Val.i32 c] ++ [.plain (.select ts)])
      (vals [v₁]) from .selectTrue hc)) hk

/-- **`select` with a zero condition** keeps the second value. -/
theorem Wp.selectFalse {us : List Val} {v₁ v₂ : Val} {ts : Option (List ValType)}
    (hk : Wp m P host s f (vals (us ++ [v₂]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v₁, v₂, Val.i32 0]) ++ .plain (.select ts) :: rest) Q :=
  Wp.detVals (args := [v₁, v₂, Val.i32 0]) (res := [v₂]) (by simp [famOf]) trivial
    (.parametric (show ParametricStep (vals [v₁, v₂, Val.i32 0] ++ [.plain (.select ts)])
      (vals [v₂]) from .selectFalse v₁ v₂ ts)) hk

/-- **A trapping integer operator** (division or remainder by zero, `div_s` overflow). -/
theorem Wp.intBinOp_trap {us : List Val} {t : IntType} {op : IntBinOp} {x y : BitVec t.width}
    {e : IntTrap} (he : intBinOp t op x y = .error e) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
      .plain (.intBinOp t op) :: rest) Q :=
  Wp.detTrap (by simp [famOf]) trivial (.numeric (.intBinOpTrap he)) hq

/-- One evaluated instruction, with `select`. -/
theorem Wp.exec1S {rs rs' : List Val} {i : Instr} (h : exec1S s f rs i = some (s', f', rs'))
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals rs.reverse ++ .plain i :: rest) Q := by
  by_cases hi : ∃ ts, i = .select ts
  · obtain ⟨ts, rfl⟩ := hi
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    obtain ⟨c, v₂, v₁, rs₀, rfl, rfl⟩ := selectV_eq hr
    by_cases hc : c = 0
    · subst hc
      have k := Wp.selectFalse (us := rs₀.reverse) (v₁ := v₁) (ts := ts)
        (by simpa using hk)
      simpa using k
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hk
      have hk' : Wp m P host s f (vals (rs₀.reverse ++ [v₁]) ++ rest) Q := by
        simpa using hk
      have k := Wp.selectTrue (us := rs₀.reverse) (v₂ := v₂) (ts := ts) hc hk'
      simpa using k
  · rw [exec1S_of_ne (fun ts he => hi ⟨ts, he⟩)] at h
    exact Silmaril.Wasm.Examples.Common.Wp.exec1 h hk

/-- **Symbolic execution with `select`** in the every-run logic. -/
theorem Wp.execS {vs rs' : List Val} {is : List Instr}
    (he : execS s f vs.reverse is = some (s', f', rs'))
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q := by
  induction is generalizing s f vs with
  | nil =>
    cases he
    simpa using hk
  | cons i is ih =>
    rw [execS_cons] at he
    split at he
    · rename_i s₁ f₁ rs₁ h₁
      have k := ih (vs := rs₁.reverse) (by simpa using he)
      have h₁' := Wp.exec1S (rest := expression is ++ rest) h₁
        (by simpa only [List.append_assoc] using k)
      simpa only [List.reverse_reverse, expression_cons, List.append_assoc,
        List.cons_append] using h₁'
    · cases he

/-- The weakest precondition is kept along a run. -/
theorem wp_steps_inv {c c' : Config H} (hs : Steps P host c c')
    (h : Wp m P host c.store c.frame c.code Q) : Wp m P host c'.store c'.frame c'.code Q := by
  induction hs with
  | refl => exact h
  | tail _ hst ih =>
    cases m
    · exact HWP.step_inv ih hst
    · exact TSafe.step_inv ih hst

/-- The trap postcondition from a trap in a sequence. -/
theorem wp_trap_post {us : List Val} {rest' : List Admin}
    (h : Wp m P host s f (vals us ++ .trap :: rest') Q) : Q s f .trap := by
  cases m
  · exact Safe.trap_post (m := 0) (h 2)
  · exact TSafe.trap_post h

/-- **Code that `xexec` runs to the end** has the weakest precondition of its result. -/
theorem wp_xexec_ok_iff {vs rs' : List Val} {is : List Instr}
    (he : xexec s f vs.reverse is = .ok s' f' rs') :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q ↔
      Wp m P host s' f' (vals rs'.reverse ++ rest) Q := by
  have he' := xexec_ok_iff.mp he
  constructor
  · intro hw
    have hs := execS_sound (P := P) (host := host) rest he'
    rw [List.reverse_reverse] at hs
    exact wp_steps_inv hs hw
  · exact Wp.execS he'

/-- One evaluated instruction in front of the rest of a sequence. -/
theorem Wp.exec1S_cons {vs rs₁ : List Val} {i : Instr} {is : List Instr} {s₁ : Store H}
    {f₁ : Frame} (h₁ : XExec.exec1S s f vs.reverse i = some (s₁, f₁, rs₁))
    (k : Wp m P host s₁ f₁ (vals rs₁.reverse ++ expression is ++ rest) Q) :
    Wp m P host s f (vals vs ++ expression (i :: is) ++ rest) Q := by
  have h₁' : Wp m P host s f (vals vs.reverse.reverse ++ .plain i :: (expression is ++ rest)) Q :=
    Wp.exec1S (rest := expression is ++ rest) h₁ (by simpa only [List.append_assoc] using k)
  simpa only [List.reverse_reverse, expression_cons, List.append_assoc, List.cons_append] using h₁'

/-- A trapping instruction in front of the rest of a sequence. -/
theorem Wp.traps1_cons {vs : List Val} {i : Instr} {is : List Instr}
    (ht : traps1 vs.reverse i = true) (hq : Q s f .trap) :
    Wp m P host s f (vals vs ++ expression (i :: is) ++ rest) Q := by
  obtain ⟨t, op, x, y, e, rs₀, rfl, hrs, hz⟩ := traps1_eq ht
  have k : Wp m P host s f (vals (rs₀.reverse ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
      .plain (.intBinOp t op) :: (expression is ++ rest)) Q := Wp.intBinOp_trap hz hq
  have hvs : vs = rs₀.reverse ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩] := by
    rw [← List.reverse_reverse vs, hrs]; simp
  rw [hvs]
  simpa [List.append_assoc] using k

/-- The forward rule of a trap. -/
theorem Wp.xexec_trap {vs : List Val} {is : List Instr}
    (he : xexec s f vs.reverse is = .trap s' f') (hq : Q s' f' .trap) :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q := by
  induction is generalizing s f vs with
  | nil => cases he
  | cons i is ih =>
    rw [xexec_cons] at he
    split at he
    · rename_i s₁ f₁ rs₁ h₁
      exact Wp.exec1S_cons h₁ (ih (vs := rs₁.reverse) (by simpa using he))
    · split at he
      · rename_i ht
        cases he
        exact Wp.traps1_cons ht hq
      · cases he

/-- **Code that `xexec` runs to a trap** has the trap postcondition as its weakest
precondition, in the store and frame at the trap. -/
theorem wp_xexec_trap_iff {vs : List Val} {is : List Instr}
    (he : xexec s f vs.reverse is = .trap s' f') :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q ↔ Q s' f' .trap := by
  constructor
  · intro hw
    obtain ⟨us, rest', hs⟩ := xexec_trap_steps (P := P) (host := host) rest he
    rw [List.reverse_reverse] at hs
    exact wp_trap_post (wp_steps_inv hs hw)
  · exact Wp.xexec_trap he

end Silmaril.Proofs.Wasm.Auto.XExec