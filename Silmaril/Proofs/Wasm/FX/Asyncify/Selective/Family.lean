module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Selective.Rel
public import Silmaril.Wasm.FX.Asyncify.Defs

/-!
# Selective instrumentation as a peephole, and the family's selective instance

The family of `Silmaril.Wasm.FX.Asyncify` compiles selectively at source level (`compO`, with
`Opt.selective S'`: keep the check after calls of functions in `S'`). The peephole `opt S`
removes checks from already compiled code (after calls of functions in `S`). They agree:

* **`opt_comp`**: `opt S false (comp d) = compO (.selective (!S ·)) d`, so `compSel S P` is
  `compPO (.selective (!S ·)) P` (`compSel_eq`);
* **`sound_of_safe`**: a certificate `SafeProg S (compP P)` gives a sound analysis
  `Sound (!S ·) P` for the family; so `analyze` gives one with no hypothesis (`analyze_sound`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Selective

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify Silmaril.Wasm.FX.Asyncify.Selective

variable {V : Type} {S : Nat → Bool}

/-- The family's selective optimization for the complement of `S`. -/
abbrev compl (S : Nat → Bool) : Opt := .selective fun f => !S f

theorem chkIf_not_true {b : Bool} (h : b = true) : chkIf (V := V) (!b) = [] := by
  simp only [chkIf, h, Bool.not_true, Bool.false_eq_true, ite_false]

theorem chkIf_not_false {b : Bool} (h : b = false) : chkIf (V := V) (!b) = [.chk] := by
  simp only [chkIf, h, Bool.not_false, ite_true]

/-- The code after a call whose check `opt` keeps or drops. -/
theorem opt_after_call (b : Bool) (c : List (TIns V)) :
    opt S b (.chk :: c) = chkIf (!b) ++ opt S false c := by
  cases b with
  | true => rw [opt_true_chk, chkIf_not_true rfl, List.nil_append]
  | false => rw [opt_false_cons, chkIf_not_false rfl, List.singleton_append]; rfl

/-- **The peephole on compiled code is the family's selective compilation.** -/
theorem opt_comp (S : Nat → Bool) : ∀ d : List (Ins V), opt S false (comp d) = compO (compl S) d
  | [] => rfl
  | .push v :: c => by rw [comp, opt_false_cons, compO]; exact congrArg (List.cons _) (opt_comp S c)
  | .prim n op :: c => by rw [comp, opt_false_cons, compO]; exact congrArg (List.cons _) (opt_comp S c)
  | .drop :: c => by rw [comp, opt_false_cons, compO]; exact congrArg (List.cons _) (opt_comp S c)
  | .call f :: c => by
    rw [comp, opt_false_cons, compO, opt_after_call, opt_comp S c]; rfl
  | .cond f g :: c => by
    have h : (!(S f && S g)) = ((compl S).instr f || (compl S).instr g) := Bool.not_and _ _
    rw [comp, opt_false_cons, compO, opt_after_call, opt_comp S c]
    exact congrArg (fun b => TIns.cond f g :: (chkIf b ++ compO (compl S) c)) h
  | .contNew f :: c => by rw [comp, opt_false_cons, compO]; exact congrArg (List.cons _) (opt_comp S c)
  | .resume n hs :: c => by
    rw [comp, opt_false_cons, compO]
    exact congrArg (fun x => TIns.startRewind n :: TIns.rchk hs :: x) (opt_comp S c)
  | .suspend t n :: c => by rw [comp, opt_false_cons, compO]; exact congrArg (List.cons _) (opt_comp S c)

theorem compSel_eq (S : Nat → Bool) (P : Prog (Ins V)) : compSel S P = compPO (compl S) P := by
  funext f
  simp only [compSel, optP, compP, compPO, Option.map_map, Function.comp_def, opt_comp]

/-! ## Certificates are sound analyses -/

theorem calm_cons {S' : Nat → Bool} {i : Ins V} {c : List (Ins V)} (hi : Calm S' [i])
    (hc : Calm S' c) : Calm S' (i :: c) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact hi j List.mem_cons_self
  · exact hc j hj'

theorem safeCode_append {a b : List (TIns V)} (h : SafeCode S (a ++ b)) :
    SafeCode S a ∧ SafeCode S b :=
  ⟨fun i hi => h i (List.mem_append_left b hi), fun i hi => h i (List.mem_append_right a hi)⟩

/-- The head instruction of safe compiled code is calm for the complement. -/
theorem calm_head {i : Ins V} {c : List (Ins V)} (h : SafeCode S (comp (i :: c))) :
    Calm (fun f => !S f) [i] ∧ SafeCode S (comp c) := by
  have hsing : ∀ {P : Ins V → Prop}, P i → ∀ j ∈ [i], P j := fun hp j hj => by
    rcases List.mem_singleton.mp hj with rfl; exact hp
  cases i with
  | call f =>
    have hf : S f = true := safeCode_head h
    exact ⟨hsing (by simp only [hf, Bool.not_true]), safeCode_tail (safeCode_tail h)⟩
  | cond f g =>
    have hfg : S f = true ∧ S g = true := Bool.and_eq_true_iff.mp (safeCode_head h)
    exact ⟨hsing (by simp only [hfg.1, hfg.2, Bool.not_true, and_self]),
      safeCode_tail (safeCode_tail h)⟩
  | resume n hs => exact absurd (safeCode_head h) (by simp only [safeI, Bool.false_eq_true, not_false_eq_true])
  | suspend t n => exact absurd (safeCode_head h) (by simp only [safeI, Bool.false_eq_true, not_false_eq_true])
  | push v => exact ⟨hsing trivial, safeCode_tail h⟩
  | prim n op => exact ⟨hsing trivial, safeCode_tail h⟩
  | drop => exact ⟨hsing trivial, safeCode_tail h⟩
  | contNew f => exact ⟨hsing trivial, safeCode_tail h⟩

/-- Safe compiled code is calm for the complement. -/
theorem calm_of_safe : ∀ {d : List (Ins V)}, SafeCode S (comp d) → Calm (fun f => !S f) d
  | [], _ => fun _ h => by cases h
  | _ :: _, h => calm_cons (calm_head h).1 (calm_of_safe (calm_head h).2)

/-- **A certificate is a sound analysis for the complement.** -/
theorem sound_of_safe {P : Prog (Ins V)} (h : SafeProg S (compP P)) :
    Sound (fun f => !S f) P := by
  intro f np body hp hf
  have hf' : S f = true := by simpa only [Bool.not_eq_false'] using hf
  obtain ⟨np', body', hq, hs⟩ := h f hf'
  have hq' : compP P f = some (np, comp body) := by simp only [compP, hp, Option.map_some]
  have he : some (np, comp body) = some (np', body') := hq'.symm.trans hq
  cases he
  exact calm_of_safe hs

/-- **The analysis gives a sound analysis**, with no hypothesis. -/
theorem analyze_sound (P : Prog (Ins V)) (n : Nat) :
    Sound (fun f => !analyze (compP P) n f) P :=
  sound_of_safe (analyze_safe (compP P) n)

end Silmaril.Proofs.Wasm.FX.Asyncify.Selective
