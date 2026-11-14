module

public import Silmaril.Wasi.Versions.WitImport.Resolve.Thms
public import Silmaril.Wasi.Versions.WitImport.Typing.Defs

/-!
# Resolution changes nothing on types without named types

`refFree n t`: the WIT type `t` has no named type (`Binary.Ty.ref`) and at most `n` nested
constructors. `sigFree s`: every parameter and the result of `s` are `refFree fuel`.

* **`tyOkR_free`**: on a `refFree n` type the resolved typing with fuel `n` *is* `tyOk`, in
  every environment and interface.
* **`witROk_free`**, `witRTrapOk_free`: for a package whose signatures are all `sigFree`
  (`PkgFree`), the resolved typing of answers is the unresolved typing of `strip`.

This is how a package without named types (`wasi:random`) is moved onto the resolved typing
without redoing its comparisons (`Silmaril.Wasi.Versions.WitImport.RP3`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)

/-- `t` has no named type and at most `n` nested constructors. -/
def refFree : Nat → Binary.Ty → Bool
  | 0, _ => false
  | _ + 1, .prim _ => true
  | _ + 1, .ref _ => false
  | n + 1, .list t => refFree n t
  | n + 1, .fixedList t _ => refFree n t
  | n + 1, .map k w => refFree n k && refFree n w
  | n + 1, .option t => refFree n t
  | n + 1, .result a b => a.all (refFree n) && b.all (refFree n)
  | n + 1, .tuple ts => ts.all (refFree n)
  | _ + 1, .own _ | _ + 1, .borrow _ | _ + 1, .future _ | _ + 1, .stream _ => true

/-- Every parameter and the result of `s` have no named type (with the fuel of `tyOkR`). -/
def sigFree (s : Binary.Sig) : Bool :=
  s.params.all (fun p => refFree fuel p.2) && s.result.all (refFree fuel)

/-- Every signature of the package has no named type. -/
def PkgFree (P : RPkg) : Bool := P.1.all fun x => sigFree x.2.2

theorem all_eq_tyAll {g : Val → Bool} {t : Binary.Ty} (hg : ∀ v, g v = tyOk t v) :
    ∀ vs : List Val, vs.all g = tyAll t vs
  | [] => rfl
  | v :: vs => by simp [tyAll, hg v, all_eq_tyAll hg vs]

theorem all_pairOk_eq {f : Binary.Ty → Val → Bool} {k w : Binary.Ty}
    (hk : ∀ v, f k v = tyOk k v) (hw : ∀ v, f w v = tyOk w v) :
    ∀ vs : List Val, vs.all (pairOk f k w) = pairsOk k w vs
  | [] => rfl
  | v :: vs => by
    have ih := all_pairOk_eq hk hw vs
    cases v with
    | record xs =>
      rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩
      all_goals simp [pairOk, pairsOk, hk, hw, ih, Bool.and_assoc]
    | _ => simp [pairOk, pairsOk]

theorem zipOk_eq_tysOk {f : Binary.Ty → Val → Bool} :
    ∀ (ts : List Binary.Ty), (∀ t ∈ ts, ∀ v, f t v = tyOk t v) →
      ∀ vs : List Val, zipOk f ts vs = tysOk ts vs
  | [], _, [] => rfl
  | [], _, _ :: _ => rfl
  | _ :: _, _, [] => rfl
  | t :: ts, h, v :: vs => by
    have ih := zipOk_eq_tysOk ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) vs
    simp [zipOk, tysOk, h t List.mem_cons_self v, ih]

theorem optOk_eq_tyOpt {f : Binary.Ty → Val → Bool} :
    ∀ (a : Option Binary.Ty), (∀ t ∈ a, ∀ v, f t v = tyOk t v) →
      ∀ p : Option Val, optOk f a p = tyOpt a p
  | none, _, none => rfl
  | none, _, some _ => rfl
  | some _, _, none => rfl
  | some t, h, some v => by simpa [optOk, tyOpt] using h t rfl v

/-- **On a type without named types the resolved typing is `tyOk`.** -/
theorem tyOkR_free (E : TyEnv) :
    ∀ (n : Nat) (c : Binary.IfaceName) (t : Binary.Ty) (v : Val),
      refFree n t = true → tyOkR E n c t v = tyOk t v
  | 0, _, _, _, h => by simp [refFree] at h
  | n + 1, c, t, v, h => by
    have ih : ∀ t v, refFree n t = true → tyOkR E n c t v = tyOk t v :=
      fun t v ht => tyOkR_free E n c t v ht
    cases t with
    | prim p => simp [tyOkR_prim, tyOk]
    | ref r => simp [refFree] at h
    | list t =>
      simp only [refFree] at h
      rw [tyOkR_list]
      cases v <;> simp [recV, tyOk, all_eq_tyAll (fun v => ih t v h)]
    | fixedList t k =>
      simp only [refFree] at h
      cases v <;> simp [tyOkR, tyOk, all_eq_tyAll (fun v => ih t v h)]
    | map k w =>
      simp only [refFree, Bool.and_eq_true] at h
      cases v <;> simp [tyOkR, recV, tyOk, all_pairOk_eq (fun v => ih k v h.1) (fun v => ih w v h.2)]
    | option t =>
      simp only [refFree] at h
      rw [tyOkR_option]
      cases v with
      | variant i p => rcases i with _ | _ | i <;> rcases p with _ | p <;> simp [optV, tyOk, ih t _ h]
      | _ => simp [optV, tyOk]
    | result a b =>
      simp only [refFree, Bool.and_eq_true, Option.all_eq_true] at h
      rw [tyOkR_result]
      have ha := optOk_eq_tyOpt (f := tyOkR E n c) a (fun t ht v => ih t v (h.1 t ht))
      have hb := optOk_eq_tyOpt (f := tyOkR E n c) b (fun t ht v => ih t v (h.2 t ht))
      cases v with
      | variant i p => rcases i with _ | _ | i <;> simp [resV, tyOk, ha, hb]
      | _ => simp [resV, tyOk]
    | tuple ts =>
      simp only [refFree, List.all_eq_true] at h
      have hz := zipOk_eq_tysOk (f := tyOkR E n c) ts (fun t ht v => ih t v (h t ht))
      cases v <;> simp [tyOkR, tyOk, hz]
    | own r => cases v <;> rfl
    | borrow r => cases v <;> rfl
    | future r => cases v <;> rfl
    | stream r => cases v <;> rfl

theorem argsOkR_free {E : TyEnv} {i : Binary.IfaceName} {s : Binary.Sig} (h : sigFree s = true)
    (a : List Val) : argsOkR E i s a = argsOk s a := by
  simp only [sigFree, Bool.and_eq_true, List.all_eq_true] at h
  refine zipOk_eq_tysOk _ (fun t ht v => tyOkR_free E fuel i t v ?_) a
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ht
  exact h.1 p hp

theorem resOkR_free {E : TyEnv} {i : Binary.IfaceName} {s : Binary.Sig} (h : sigFree s = true)
    (r : Option (List Val)) : resOkR E i s r = resOk s r := by
  simp only [sigFree, Bool.and_eq_true, Option.all_eq_true] at h
  rcases r with _ | vs
  · rfl
  · simp only [resOkR, resOk]
    cases hs : s.result with
    | none => rfl
    | some t =>
      rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
      · rfl
      · exact tyOkR_free E fuel i t v (h.2 t hs)
      · rfl

theorem rlookup_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {L : List (α × β)} {a : α} {b : β}, L.lookup a = some b → (a, b) ∈ L
  | [], _, _, h => by simp [List.lookup] at h
  | (x, y) :: L, a, b, h => by
    by_cases hx : a = x
    · subst hx
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · simp only [List.lookup, beq_false_of_ne hx] at h
      exact List.mem_cons_of_mem _ (rlookup_mem h)

theorem sigFree_of_lookup {P : RPkg} (hP : PkgFree P = true) {f : FnName}
    {i : Binary.IfaceName} {s : Binary.Sig} (h : P.1.lookup f = some (i, s)) : sigFree s = true := by
  simp only [PkgFree, List.all_eq_true] at hP
  exact hP _ (rlookup_mem h)

/-- **For a package without named types, the resolved typing is the unresolved one.** -/
theorem witROk_free {P : RPkg} (hP : PkgFree P = true) (e : WEv) :
    witROk P e = witOk (strip P.1) e := by
  cases e with
  | imp f a r =>
    simp only [witROk, witOk, lookup_strip]
    cases hl : P.1.lookup f with
    | none => rfl
    | some x =>
      obtain ⟨i, s⟩ := x
      have hs := sigFree_of_lookup hP hl
      simp [argsOkR_free hs, resOkR_free hs]
  | _ => rfl

/-- **The same with traps admitted.** -/
theorem witRTrapOk_free {P : RPkg} (hP : PkgFree P = true) (e : WEv) :
    witRTrapOk P e = witTrapOk (strip P.1) e := by
  cases e with
  | imp f a r =>
    simp only [witRTrapOk, witTrapOk, lookup_strip]
    cases hl : P.1.lookup f with
    | none => rfl
    | some x =>
      obtain ⟨i, s⟩ := x
      have hs := sigFree_of_lookup hP hl
      simp [argsOkR_free hs, resOkR_free hs]
  | _ => rfl

end Silmaril.Wasi.Versions.WitImport
