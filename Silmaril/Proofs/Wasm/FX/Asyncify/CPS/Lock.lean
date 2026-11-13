module

public import Silmaril.Wasm.FX.Asyncify.CPS.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.SM.Lock

/-!
# CPS runs in lock step with the state machine

`cstep (compK P) f₀ test (toC (compK P) f₀ x) = (pstep P f₀ test x).map (toC (compK P) f₀)`:
making the top record of a state-machine configuration into running CPS code commutes with one
step.

* `annK_drop`, `kCode_compK`, `enter_code`: the code a record re-enters at is the CPS
  compilation of its kernel code suffix;
* `call_toC`, `exec_toC`: one case per instruction;
* **`step_toC`**: the lock step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.CPS

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.CPS
open Silmaril.Wasm.FX.Asyncify.SM (PFrame PCfg psplit pstep pexec pcall smCode)
open Silmaril.Proofs.Wasm.FX.Asyncify.SM (drop_some drop_none)

variable {V : Type}

theorem annK_drop (fn : Nat) (l : List (Ins V)) (pc k : Nat) :
    (annK fn pc l).drop k = annK fn (pc + k) (l.drop k) := by
  induction l generalizing pc k with
  | nil => simp only [annK, List.drop_nil]
  | cons i l ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have h : (annK fn (pc + 1) l).drop k = annK fn (pc + 1 + k) (l.drop k) := ih (pc + 1) k
      simp only [annK, List.drop_succ_cons, h, Nat.add_assoc, Nat.add_comm 1 k]

variable (P : Prog (Ins V)) (f₀ : Nat)

theorem kCode_compK (fn : Nat) : kCode (compK P) f₀ fn = annK fn 0 (smCode P f₀ fn) := by
  cases fn with
  | zero => rfl
  | succ g =>
    cases hg : P g with
    | none => simp only [kCode, smCode, compK, hg, Option.map_none, Option.getD_none, annK]
    | some x => simp only [kCode, smCode, compK, hg, Option.map_some, Option.getD_some]

theorem enter_code (b : PFrame V) :
    (enter (compK P) f₀ b).code = annK b.fn b.pc ((smCode P f₀ b.fn).drop b.pc) := by
  simp only [enter, kCode_compK, annK_drop, Nat.zero_add]

theorem compK_some {g np : Nat} {body : List (Ins V)} (h : P g = some (np, body)) :
    compK P g = some (np, annK (g + 1) 0 body) := by
  simp only [compK, h, Option.map_some]

theorem enter_entry {g np : Nat} {body : List (Ins V)} (h : P g = some (np, body))
    (ops : List (SV V)) : enter (compK P) f₀ ⟨g + 1, 0, ops, none⟩ = ⟨annK (g + 1) 0 body, ops, none⟩ := by
  simp only [enter, kCode, compK_some P h, Option.map_some, Option.getD_some, List.drop_zero]

variable {P f₀}

/-- The CPS code after the case of `fr`. -/
abbrev nxtC (P : Prog (Ins V)) (f₀ : Nat) (fr : PFrame V) : List (CIns V) :=
  (enter (compK P) f₀ { fr with pc := fr.pc + 1 }).code

theorem call_toC (K : List (Option (List (PFrame V)))) (g : Nat) (fr : PFrame V)
    (ops : List (SV V)) (rest : List (PFrame V)) :
    ccall (compK P) K g fr.fn (fr.pc + 1) ops rest =
      (pcall P K g { fr with pc := fr.pc + 1 } ops rest).map (toC (compK P) f₀) := by
  cases hg : P g with
  | none => simp only [ccall, pcall, compK, hg, Option.map_none, Res.map]
  | some x =>
    obtain ⟨np, body⟩ := x
    cases hp : popN np ops with
    | none => simp only [ccall, pcall, compK_some P hg, hg, hp, Res.map]
    | some y => simp only [ccall, pcall, compK_some P hg, hg, hp, Res.map, toC, enter_entry P f₀ hg]

theorem resume_toC (K : List (Option (List (PFrame V)))) (n : Nat) (hs : List Clause)
    (fr : PFrame V) (rest : List (PFrame V)) (test : V → Bool) :
    cexec (compK P) f₀ test K (enter (compK P) f₀ fr) (.resume n hs fr.fn (fr.pc + 1)) (nxtC P f₀ fr)
        rest = (pexec P test K fr (.resume n hs) rest).map (toC (compK P) f₀) := by
  rcases fr with ⟨fn, pc, _ | ⟨_ | k, o⟩, w⟩
  · rfl
  · rfl
  · cases hp : popN n o with
    | none => simp only [cexec, pexec, enter, hp, Res.map]
    | some y =>
      obtain ⟨args, o'⟩ := y
      cases hk : K[k]? with
      | none => simp only [cexec, pexec, enter, hp, hk, Res.map]
      | some e =>
        rcases e with _ | _ | ⟨top, seg⟩
        · simp only [cexec, pexec, enter, hp, hk, Res.map]
        · simp only [cexec, pexec, enter, hp, hk, Res.map]
        · simp only [cexec, pexec, enter, hp, hk, Res.map, toC, List.cons_append]

theorem suspend_toC (K : List (Option (List (PFrame V)))) (t n : Nat) (fr : PFrame V)
    (rest : List (PFrame V)) (test : V → Bool) :
    cexec (compK P) f₀ test K (enter (compK P) f₀ fr) (.suspend t n fr.fn (fr.pc + 1))
        (nxtC P f₀ fr) rest = (pexec P test K fr (.suspend t n) rest).map (toC (compK P) f₀) := by
  cases hp : popN n fr.ops with
  | none => simp only [cexec, pexec, enter, hp, Res.map]
  | some y =>
    obtain ⟨p, o⟩ := y
    cases hq : psplit t rest with
    | none => simp only [cexec, pexec, enter, hp, hq, Res.map]
    | some z =>
      obtain ⟨m, h, r, rs⟩ := z
      cases hh : P h with
      | none => simp only [cexec, pexec, enter, hp, hq, hh, compK, Option.map_none, Res.map]
      | some b =>
        obtain ⟨np, body⟩ := b
        simp only [cexec, pexec, enter, hp, hq, hh, compK_some P hh, Res.map, toC, kCode,
          Option.map_some, Option.getD_some, List.drop_zero]

theorem exec_toC (K : List (Option (List (PFrame V)))) (i : Ins V) (fr : PFrame V)
    (rest : List (PFrame V)) (test : V → Bool) :
    cexec (compK P) f₀ test K (enter (compK P) f₀ fr) (annI fr.fn fr.pc i) (nxtC P f₀ fr) rest =
      (pexec P test K fr i rest).map (toC (compK P) f₀) := by
  cases i with
  | push v => rfl
  | prim n op =>
    cases hp : popN n fr.ops with
    | none => simp only [annI, cexec, pexec, enter, hp, Res.map]
    | some y =>
      cases ha : allVals y.1 with
      | none => simp only [annI, cexec, pexec, enter, hp, ha, Res.map]
      | some vs => simp only [annI, cexec, pexec, enter, hp, ha, Res.map]; rfl
  | drop => rcases fr with ⟨fn, pc, _ | ⟨_, o⟩, w⟩ <;> rfl
  | call g => exact call_toC K g fr fr.ops rest
  | cond f g =>
    rcases fr with ⟨fn, pc, _ | ⟨_ | v, o⟩, w⟩
    · rfl
    · exact call_toC K _ ⟨fn, pc, _, w⟩ o rest
    · rfl
  | contNew g =>
    cases hg : P g with
    | none => simp only [annI, cexec, pexec, compK, hg, Option.map_none, Res.map]
    | some b => simp only [annI, cexec, pexec, compK, hg, Option.map_some, Res.map, toC]; rfl
  | resume n hs => exact resume_toC K n hs fr rest test
  | suspend t n => exact suspend_toC K t n fr rest test

/-- **Lock step**: the CPS reading commutes with one step. -/
theorem step_toC (test : V → Bool) (x : PCfg V) :
    cstep (compK P) f₀ test (toC (compK P) f₀ x) = (pstep P f₀ test x).map (toC (compK P) f₀) := by
  rcases x with ⟨K, _ | ⟨fr, rest⟩⟩
  · rfl
  · cases hi : (smCode P f₀ fr.fn)[fr.pc]? with
    | none =>
      have hd : (enter (compK P) f₀ fr).code = [] := by
        rw [enter_code, drop_none hi]; rfl
      rcases rest with _ | ⟨b, rest⟩
      · simp only [cstep, pstep, toC, hd, hi, Res.map]; rfl
      · simp only [cstep, pstep, toC, hd, hi, Res.map]; rfl
    | some i =>
      have hd : (enter (compK P) f₀ fr).code = annI fr.fn fr.pc i :: nxtC P f₀ fr := by
        rw [enter_code, nxtC, enter_code, drop_some hi]; rfl
      have he := exec_toC (P := P) (f₀ := f₀) K i fr rest test
      simp only [cstep, pstep, toC, hd, hi]
      exact he

end Silmaril.Proofs.Wasm.FX.Asyncify.CPS
