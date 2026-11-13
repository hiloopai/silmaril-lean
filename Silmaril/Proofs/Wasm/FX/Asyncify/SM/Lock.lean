module

public import Silmaril.Wasm.FX.Asyncify.SM.Defs

/-!
# The state machine runs in lock step with the handler kernel

`sstep P test (dec P f₀ x) = (pstep P f₀ test x).map (dec P f₀)` for every configuration `x`:
reading a state-machine configuration back as a kernel configuration commutes with one step.

* `drop_some`, `drop_none`: the code suffix at `pc` is the fetched case followed by the suffix at
  `pc + 1`, or empty;
* `split_dec`: the handler search on decoded records is the decoded handler search;
* `call_dec`, `exec_dec`: one case per instruction;
* **`step_dec`**: the lock step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.SM

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.SM

variable {V : Type} {α : Type}

theorem drop_some {l : List α} {pc : Nat} {i : α} (h : l[pc]? = some i) :
    l.drop pc = i :: l.drop (pc + 1) := by
  have hlt : pc < l.length := (List.getElem?_eq_some_iff.1 h).1
  have hi : l[pc] = i := (List.getElem?_eq_some_iff.1 h).2
  rw [List.drop_eq_getElem_cons hlt, hi]

theorem drop_none {l : List α} {pc : Nat} (h : l[pc]? = none) : l.drop pc = [] :=
  List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.1 h)

variable (P : Prog (Ins V)) (f₀ : Nat)

/-- Decoded continuation stores. -/
abbrev decK (K : List (Option (List (PFrame V)))) : List (Option (List (SFrame V))) :=
  K.map (Option.map (List.map (decF P f₀)))

theorem code_succ {g np : Nat} {body : List (Ins V)} (h : P g = some (np, body)) :
    smCode P f₀ (g + 1) = body := by
  simp only [smCode, h, Option.map_some, Option.getD_some]

theorem split_dec (t : Nat) (rest : List (PFrame V)) :
    split t (rest.map (decF P f₀)) = (psplit t rest).map
      (fun x => (x.1.map (decF P f₀), x.2.1, decF P f₀ x.2.2.1, x.2.2.2.map (decF P f₀))) := by
  induction rest with
  | nil => rfl
  | cons b rest ih =>
    cases hb : b.wait.bind (lookup t) with
    | some h =>
      have hb' : (decF P f₀ b).wait.bind (lookup t) = some h := hb
      simp only [List.map_cons, split, psplit, hb, hb', Option.map_some, List.map_nil]
    | none =>
      have hb' : (decF P f₀ b).wait.bind (lookup t) = none := hb
      simp only [List.map_cons, split, psplit, hb, hb', ih, Option.map_map]
      cases psplit t rest <;> rfl

variable {P f₀}

theorem call_dec (K : List (Option (List (PFrame V)))) (g : Nat)
    (fr : PFrame V) (ops : List (SV V)) (rest : List (PFrame V)) :
    scall P (decK P f₀ K) g (decF P f₀ fr) ops ((smCode P f₀ fr.fn).drop (fr.pc + 1))
        (rest.map (decF P f₀)) =
      (pcall P K g { fr with pc := fr.pc + 1 } ops rest).map (dec P f₀) := by
  cases hg : P g with
  | none => simp only [scall, pcall, hg, Res.map]
  | some x =>
    obtain ⟨np, body⟩ := x
    cases hp : popN np ops with
    | none => simp only [scall, pcall, hg, hp, Res.map]
    | some y =>
      simp only [scall, pcall, hg, hp, Res.map, dec, decF, List.map_cons, code_succ P f₀ hg,
        List.drop_zero]

/-- Abbreviation: the decoded code suffix after the case of `fr`. -/
abbrev nxt (P : Prog (Ins V)) (f₀ : Nat) (fr : PFrame V) : List (Ins V) := (smCode P f₀ fr.fn).drop (fr.pc + 1)

theorem exec_resume_dec (K : List (Option (List (PFrame V)))) (n : Nat) (hs : List Clause)
    (fr : PFrame V) (rest : List (PFrame V)) (test : V → Bool) :
    sexec P test (decK P f₀ K) (decF P f₀ fr) (.resume n hs) (nxt P f₀ fr) (rest.map (decF P f₀)) =
      (pexec P test K fr (.resume n hs) rest).map (dec P f₀) := by
  rcases fr with ⟨fn, pc, _ | ⟨_ | k, o⟩, w⟩
  · rfl
  · rfl
  · cases hp : popN n o with
    | none => simp only [sexec, pexec, decF, hp, Res.map]
    | some y =>
      obtain ⟨args, o'⟩ := y
      cases hk : K[k]? with
      | none => simp only [sexec, pexec, decF, hp, hk, decK, List.getElem?_map, Option.map_none, Res.map]
      | some e =>
        rcases e with _ | _ | ⟨top, seg⟩
        · simp only [sexec, pexec, decF, hp, hk, decK, List.getElem?_map, Option.map_some,
            Option.map_none, Res.map]
        · simp only [sexec, pexec, decF, hp, hk, decK, List.getElem?_map, Option.map_some,
            List.map_nil, Res.map]
        · simp only [sexec, pexec, decF, hp, hk, decK, List.getElem?_map, Option.map_some,
            List.map_cons, Res.map, dec, List.map_append, List.map_set, Option.map_none, nxt]

theorem exec_suspend_dec (K : List (Option (List (PFrame V)))) (t n : Nat)
    (fr : PFrame V) (rest : List (PFrame V)) (test : V → Bool) :
    sexec P test (decK P f₀ K) (decF P f₀ fr) (.suspend t n) (nxt P f₀ fr) (rest.map (decF P f₀)) =
      (pexec P test K fr (.suspend t n) rest).map (dec P f₀) := by
  cases hp : popN n fr.ops with
  | none => simp only [sexec, pexec, decF, hp, Res.map]
  | some y =>
    obtain ⟨p, o⟩ := y
    have hs := split_dec P f₀ t rest
    cases hq : psplit t rest with
    | none => simp only [sexec, pexec, decF, hp, hq, hs, Option.map_none, Res.map]
    | some z =>
      obtain ⟨m, h, r, rs⟩ := z
      cases hh : P h with
      | none => simp only [sexec, pexec, decF, hp, hq, hs, hh, Option.map_some, Res.map]
      | some b =>
        simp only [sexec, pexec, decF, hp, hq, hs, hh, Option.map_some, Res.map, dec, decK,
          List.map_append, List.map_cons, List.map_nil, List.length_map, code_succ P f₀ hh,
          List.drop_zero, nxt]

theorem exec_dec (K : List (Option (List (PFrame V)))) (i : Ins V) (fr : PFrame V)
    (rest : List (PFrame V)) (test : V → Bool) :
    sexec P test (decK P f₀ K) (decF P f₀ fr) i (nxt P f₀ fr) (rest.map (decF P f₀)) =
      (pexec P test K fr i rest).map (dec P f₀) := by
  cases i with
  | push v => rfl
  | prim n op =>
    cases hp : popN n fr.ops with
    | none => simp only [sexec, pexec, decF, hp, Res.map]
    | some y =>
      cases ha : allVals y.1 with
      | none => simp only [sexec, pexec, decF, hp, ha, Res.map]
      | some vs => simp only [sexec, pexec, decF, hp, ha, Res.map]; rfl
  | drop => rcases fr with ⟨fn, pc, _ | ⟨_, o⟩, w⟩ <;> rfl
  | call g => exact call_dec K g fr fr.ops rest
  | cond f g =>
    rcases fr with ⟨fn, pc, _ | ⟨_ | v, o⟩, w⟩
    · rfl
    · exact call_dec K _ ⟨fn, pc, _, w⟩ o rest
    · rfl
  | contNew g =>
    cases hg : P g with
    | none => simp only [sexec, pexec, hg, Res.map]
    | some b =>
      simp only [sexec, pexec, hg, Res.map, dec, decK, decF, List.map_append, List.map_cons,
        List.map_nil, List.length_map, Option.map_some, code_succ P f₀ hg, List.drop_zero]
  | resume n hs => exact exec_resume_dec K n hs fr rest test
  | suspend t n => exact exec_suspend_dec K t n fr rest test

/-- **Lock step**: decoding commutes with one step. -/
theorem step_dec (test : V → Bool) (x : PCfg V) :
    sstep P test (dec P f₀ x) = (pstep P f₀ test x).map (dec P f₀) := by
  rcases x with ⟨K, _ | ⟨fr, rest⟩⟩
  · rfl
  · cases hi : (smCode P f₀ fr.fn)[fr.pc]? with
    | none =>
      have hd : (decF P f₀ fr).code = [] := drop_none hi
      rcases rest with _ | ⟨b, rest⟩
      · simp only [sstep, pstep, dec, List.map_cons, List.map_nil, hd, hi, Res.map]; rfl
      · simp only [sstep, pstep, dec, List.map_cons, hd, hi, Res.map]; rfl
    | some i =>
      have hd : (decF P f₀ fr).code = i :: nxt P f₀ fr := drop_some hi
      have he := exec_dec (P := P) (f₀ := f₀) K i fr rest test
      simp only [sstep, pstep, dec, List.map_cons, hd, hi]
      exact he

end Silmaril.Proofs.Wasm.FX.Asyncify.SM
