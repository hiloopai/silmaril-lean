module

public import Silmaril.Wasm.Auto.XExec.Defs
public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.Wasm.Examples.Common.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms
public import Silmaril.Wasm.Logic.Total.Thms
import Silmaril.Proofs.Wasm.Auto.XExec.Wp
import Silmaril.Raw.Wasm.Auto.XExec.Typed

/-! # Straight-line code with `select` and traps: soundness

Proofs in `Silmaril.Proofs.Wasm.Auto.XExec.{Sound,Wp}` and, for the instruction-by-instruction
progress lemma, `Silmaril.Raw.Wasm.Auto.XExec.Typed`.

Small-step soundness (every profile, every host):

* `execS_sound`: a successful `execS` (`exec` with `select`) is a run of `Steps`; `select` by
  silmaril's `selectTrue`/`selectFalse` head rules (`select_steps`);
* `execS_eq_exec`: without `select`, `execS` is `exec`;
* `xexec_ok_iff`, `execS_none_iff`: `xexec` ends normally exactly when `execS` succeeds;
* `xexec_trap_steps`: a trap of `xexec` is a run to `vals us ++ trap :: rest'` in the store and
  frame `xexec` reports.

The every-run logic (`Silmaril.Wasm.Logic.Hoare.Wp`, both readings):

* `Wp.selectTrue`, `Wp.selectFalse`, `Wp.intBinOp_trap`: the `select` rules and the rule of a
  trapping integer operator;
* `Wp.exec1S`, `Wp.execS`: symbolic execution with `select`;
* `wp_xexec_ok_iff`, `wp_xexec_trap_iff`: the weakest precondition of code that `xexec`
  evaluates is that of its end, or the trap postcondition at the trap (backward along the run
  by `Safe.trap_post`/`TSafe.trap_post`).

Typing (`tsteps`, `LocalsOk`, `StackOk`):

* `tstep1_progress`: a typed instruction succeeds (keeping the store, the module and both
  typings) or traps;
* `xexec_typed`: typed code ends normally or traps, in the same store and module;
* `xexec_typed_noTrap`: typed code without division or remainder ends normally.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.XExec

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.XExec` -/

section
-- from Silmaril/Proofs/Wasm/Auto/XExec/Sound.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.XExec
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

theorem exec1S_of_ne {H : Type} {s : Store H} {f : Frame} {rs : List Val} {i : Instr}
    (hi : ∀ ts, i ≠ .select ts) : exec1S s f rs i = exec1 s f rs i :=
  Silmaril.Proofs.Wasm.Auto.XExec.exec1S_of_ne (H := H) (s := s) (f := f) (rs := rs) (i := i)
    (hi := hi)

/-- **`select` is a run**: it pops the condition and two values and pushes one. -/
theorem select_steps {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {c : BitVec 32} {v₂ v₁ : Val}
    {ts : Option (List ValType)} :
    Steps P host ⟨s, f, vals [v₁, v₂, Val.i32 c] ++ [.plain (.select ts)]⟩
      ⟨s, f, vals [if c = 0 then v₂ else v₁]⟩ :=
  Silmaril.Proofs.Wasm.Auto.XExec.select_steps (H := H) (P := P) (host := host) (s := s) (f := f)
    (c := c) (v₂ := v₂) (v₁ := v₁) (ts := ts)

theorem execS_cons {H : Type} (s : Store H) (f : Frame) (rs : List Val) (i : Instr)
    (is : List Instr) :
    execS s f rs (i :: is) =
      (match exec1S s f rs i with
        | some (s₁, f₁, rs₁) => execS s₁ f₁ rs₁ is
        | none => none) :=
  Silmaril.Proofs.Wasm.Auto.XExec.execS_cons (H := H) (s := s) (f := f) (rs := rs) (i := i) (is := is)

/-- **Soundness of `execS`.** -/
theorem execS_sound {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {rs rs' : List Val} {is : List Instr}
    (rest : List Admin) (h : execS s f rs is = some (s', f', rs')) :
    Steps P host ⟨s, f, vals rs.reverse ++ expression is ++ rest⟩
      ⟨s', f', vals rs'.reverse ++ rest⟩ :=
  Silmaril.Proofs.Wasm.Auto.XExec.execS_sound (H := H) (P := P) (host := host) (s := s) (s' := s')
    (f := f) (f' := f') (rs := rs) (rs' := rs') (is := is) (rest := rest) (h := h)

/-- Without `select`, `execS` is `exec`. -/
theorem execS_eq_exec {H : Type} (s : Store H) (f : Frame) (rs : List Val) :
    ∀ {is : List Instr}, noSelect is = true → execS s f rs is = exec s f rs is :=
  Silmaril.Proofs.Wasm.Auto.XExec.execS_eq_exec (H := H) (s := s) (f := f) (rs := rs)

/-- `xexec` ends normally exactly when `execS` succeeds. -/
theorem xexec_ok_iff {H : Type} {s s' : Store H} {f f' : Frame} {rs rs' : List Val} :
    ∀ {is : List Instr}, xexec s f rs is = .ok s' f' rs' ↔ execS s f rs is = some (s', f', rs') :=
  Silmaril.Proofs.Wasm.Auto.XExec.xexec_ok_iff (H := H) (s := s) (s' := s') (f := f) (f' := f')
    (rs := rs) (rs' := rs')

/-- `execS` fails exactly when `xexec` traps or is stuck. -/
theorem execS_none_iff {H : Type} {s : Store H} {f : Frame} {rs : List Val} :
    ∀ {is : List Instr}, execS s f rs is = none ↔ ∀ s' f' rs', xexec s f rs is ≠ .ok s' f' rs' :=
  Silmaril.Proofs.Wasm.Auto.XExec.execS_none_iff (H := H) (s := s) (f := f) (rs := rs)

/-- **A trap of `xexec` is a run to a trap**, in the store and frame it reports. -/
theorem xexec_trap_steps {H : Type} {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {rs : List Val} (rest : List Admin) :
    ∀ {is : List Instr}, xexec s f rs is = .trap s' f' → ∃ (us : List Val) (rest' : List Admin),
      Steps P host ⟨s, f, vals rs.reverse ++ expression is ++ rest⟩
        ⟨s', f', vals us ++ .trap :: rest'⟩ :=
  Silmaril.Proofs.Wasm.Auto.XExec.xexec_trap_steps (H := H) (P := P) (host := host) (s := s) (s' := s')
    (f := f) (f' := f') (rs := rs) (rest := rest)

end

section
-- from Silmaril/Proofs/Wasm/Auto/XExec/Wp.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.XExec
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf)
open Silmaril.Wasm.Logic.Core (Post exec exec1 popInt popInt_eq expression_cons)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Examples.Common (HeadSpec)

/-- **`select` with a non-zero condition** keeps the first value. -/
theorem Wp.selectTrue {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {rest : List Admin} {Q : Post H} {us : List Val} {v₁ v₂ : Val} {c : BitVec 32}
    {ts : Option (List ValType)}
    (hc : c ≠ 0) (hk : Wp m P host s f (vals (us ++ [v₁]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v₁, v₂, Val.i32 c]) ++ .plain (.select ts) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.XExec.Wp.selectTrue (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (rest := rest) (Q := Q) (us := us) (v₁ := v₁) (v₂ := v₂) (c := c) (ts := ts) (hc := hc)
    (hk := hk)

/-- **`select` with a zero condition** keeps the second value. -/
theorem Wp.selectFalse {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {rest : List Admin} {Q : Post H} {us : List Val} {v₁ v₂ : Val}
    {ts : Option (List ValType)}
    (hk : Wp m P host s f (vals (us ++ [v₂]) ++ rest) Q) :
    Wp m P host s f (vals (us ++ [v₁, v₂, Val.i32 0]) ++ .plain (.select ts) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.XExec.Wp.selectFalse (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (rest := rest) (Q := Q) (us := us) (v₁ := v₁) (v₂ := v₂) (ts := ts) (hk := hk)

/-- **A trapping integer operator** (division or remainder by zero, `div_s` overflow). -/
theorem Wp.intBinOp_trap {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {rest : List Admin} {Q : Post H} {us : List Val} {t : IntType} {op : IntBinOp}
    {x y : BitVec t.width}
    {e : IntTrap} (he : intBinOp t op x y = .error e) (hq : Q s f .trap) :
    Wp m P host s f (vals (us ++ [.num ⟨.int t, x⟩, .num ⟨.int t, y⟩]) ++
      .plain (.intBinOp t op) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.XExec.Wp.intBinOp_trap (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (rest := rest) (Q := Q) (us := us) (t := t) (op := op) (x := x) (y := y) (e := e)
    (he := he) (hq := hq)

/-- One evaluated instruction, with `select`. -/
theorem Wp.exec1S {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {s' : Store H} {f : Frame} {f' : Frame} {rest : List Admin} {Q : Post H} {rs rs' : List Val}
    {i : Instr} (h : exec1S s f rs i = some (s', f', rs'))
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals rs.reverse ++ .plain i :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.XExec.Wp.exec1S (H := H) (P := P) (host := host) (m := m) (s := s)
    (s' := s') (f := f) (f' := f') (rest := rest) (Q := Q) (rs := rs) (rs' := rs') (i := i) (h := h)
    (hk := hk)

/-- **Symbolic execution with `select`** in the every-run logic. -/
theorem Wp.execS {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {s' : Store H} {f : Frame} {f' : Frame} {rest : List Admin} {Q : Post H} {vs rs' : List Val}
    {is : List Instr}
    (he : execS s f vs.reverse is = some (s', f', rs'))
    (hk : Wp m P host s' f' (vals rs'.reverse ++ rest) Q) :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q :=
  Silmaril.Proofs.Wasm.Auto.XExec.Wp.execS (H := H) (P := P) (host := host) (m := m) (s := s)
    (s' := s') (f := f) (f' := f') (rest := rest) (Q := Q) (vs := vs) (rs' := rs') (is := is)
    (he := he) (hk := hk)

/-- The weakest precondition is kept along a run. -/
theorem wp_steps_inv {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {Q : Post H}
    {c c' : Config H} (hs : Steps P host c c')
    (h : Wp m P host c.store c.frame c.code Q) : Wp m P host c'.store c'.frame c'.code Q :=
  Silmaril.Proofs.Wasm.Auto.XExec.wp_steps_inv (H := H) (P := P) (host := host) (m := m) (Q := Q)
    (c := c) (c' := c') (hs := hs) (h := h)

/-- **Code that `xexec` runs to the end** has the weakest precondition of its result. -/
theorem wp_xexec_ok_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {s' : Store H} {f : Frame} {f' : Frame} {rest : List Admin} {Q : Post H} {vs rs' : List Val}
    {is : List Instr}
    (he : xexec s f vs.reverse is = .ok s' f' rs') :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q ↔
      Wp m P host s' f' (vals rs'.reverse ++ rest) Q :=
  Silmaril.Proofs.Wasm.Auto.XExec.wp_xexec_ok_iff (H := H) (P := P) (host := host) (m := m) (s := s)
    (s' := s') (f := f) (f' := f') (rest := rest) (Q := Q) (vs := vs) (rs' := rs') (is := is)
    (he := he)

/-- **Code that `xexec` runs to a trap** has the trap postcondition as its weakest
precondition, in the store and frame at the trap. -/
theorem wp_xexec_trap_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {s' : Store H} {f : Frame} {f' : Frame} {rest : List Admin} {Q : Post H} {vs : List Val}
    {is : List Instr}
    (he : xexec s f vs.reverse is = .trap s' f') :
    Wp m P host s f (vals vs ++ expression is ++ rest) Q ↔ Q s' f' .trap :=
  Silmaril.Proofs.Wasm.Auto.XExec.wp_xexec_trap_iff (H := H) (P := P) (host := host) (m := m) (s := s)
    (s' := s') (f := f) (f' := f') (rest := rest) (Q := Q) (vs := vs) (is := is) (he := he)

end

section
-- from Silmaril/Raw/Wasm/Auto/XExec/Typed.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.XExec
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core

/-- **One typed instruction succeeds or traps**, keeping the store and the module. -/
theorem tstep1_progress {H : Type} {Γ st st' : List IntType} {f : Frame} {rs : List Val} {i : Instr}
    (ht : tstep1 Γ st i = some st') (hf : LocalsOk Γ f) (hs : StackOk st rs) (s : Store H) :
    (∃ f₁ rs₁, exec1S s f rs i = some (s, f₁, rs₁) ∧ f₁.module = f.module ∧ LocalsOk Γ f₁ ∧
        StackOk st' rs₁) ∨
      (exec1S s f rs i = none ∧ traps1 rs i = true) :=
  Silmaril.Proofs.Wasm.Auto.XExec.tstep1_progress (H := H) (Γ := Γ) (st := st) (st' := st') (f := f)
    (rs := rs) (i := i) (ht := ht) (hf := hf) (hs := hs) (s := s)

/-- **Typed code ends normally or traps**: `xexec` is never stuck. -/
theorem xexec_typed {H : Type} {Γ : List IntType} :
    ∀ {is : List Instr} {st st' : List IntType} {s : Store H} {f : Frame} {rs : List Val},
      tsteps Γ st is = some st' → LocalsOk Γ f → StackOk st rs →
        (∃ f' rs', xexec s f rs is = .ok s f' rs' ∧ f'.module = f.module) ∨
          (∃ f', xexec s f rs is = .trap s f' ∧ f'.module = f.module) :=
  Silmaril.Proofs.Wasm.Auto.XExec.xexec_typed (H := H) (Γ := Γ)

/-- Typed code without division ends normally. -/
theorem xexec_typed_noTrap {H : Type} {Γ : List IntType} :
    ∀ {is : List Instr} {st st' : List IntType} {s : Store H} {f : Frame} {rs : List Val},
      tsteps Γ st is = some st' → LocalsOk Γ f → StackOk st rs →
        (∀ t d, .intBinOp t (.div d) ∉ is) → (∀ t d, .intBinOp t (.rem d) ∉ is) →
        ∃ f' rs', xexec s f rs is = .ok s f' rs' ∧ f'.module = f.module :=
  Silmaril.Proofs.Wasm.Auto.XExec.xexec_typed_noTrap (H := H) (Γ := Γ)

end

end Silmaril.Wasm.Auto.XExec

