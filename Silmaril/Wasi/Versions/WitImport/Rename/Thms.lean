module

public import Silmaril.Wasi.Versions.WitImport.Rename.Defs

@[expose] public section

/-!
# Renaming interfaces does not change the resolved typing

* `findTy_rn`: for an injective `ρ`, looking up a renamed reference from a renamed interface
  in the renamed environment finds the renamed definition.
* **`tyOkR_rn`**: `tyOkR (rnEnv ρ E) n (ρ cur) (rnTy ρ t) = tyOkR E n cur t`.
* **`witROk_rn`**: `witROk (rnPkg ρ P) = witROk P`, and likewise `witRTrapOk_rn`.
* `swapVer_injective`: exchanging two versions is injective.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)

/-! ## Lookups -/

/-- Looking up a renamed key in a list with renamed keys and mapped values. -/
theorem lookup_map_inj {α β γ : Type} [BEq α] [LawfulBEq α] {f : α → α}
    (hf : Function.Injective f) (g : β → γ) :
    ∀ (L : List (α × β)) (a : α), (L.map fun x => (f x.1, g x.2)).lookup (f a) = (L.lookup a).map g
  | [], _ => rfl
  | (x, y) :: L, a => by
    by_cases hx : a = x
    · subst hx
      simp [List.lookup]
    · have hfx : f a ≠ f x := fun e => hx (hf e)
      have ih := lookup_map_inj hf g L a
      simpa [List.lookup, beq_false_of_ne hx, beq_false_of_ne hfx] using ih

/-- The owner of a renamed reference. -/
theorem ownerOf_rn (ρ : Binary.IfaceName → Binary.IfaceName) (cur : Binary.IfaceName)
    (o : Binary.Owner) : ownerOf (ρ cur) (rnOwner ρ o) = ρ (ownerOf cur o) := by
  cases o <;> rfl

/-- **A renamed reference resolves to the renamed definition.** -/
theorem findTy_rn {ρ : Binary.IfaceName → Binary.IfaceName} (hρ : Function.Injective ρ)
    (E : TyEnv) (cur : Binary.IfaceName) (r : Binary.TyRef) :
    findTy (rnEnv ρ E) (ρ cur) (rnRef ρ r) =
      (findTy E cur r).map fun p => (ρ p.1, rnKind ρ p.2) := by
  have hE : (rnEnv ρ E).lookup (ρ (ownerOf cur r.owner)) =
      (E.lookup (ownerOf cur r.owner)).map fun ts => ts.map fun d => (d.1, rnKind ρ d.2) :=
    lookup_map_inj hρ _ E _
  have hT : ∀ ts : List (String × Binary.TyDefKind),
      (ts.map fun d => (d.1, rnKind ρ d.2)).lookup r.name = (ts.lookup r.name).map (rnKind ρ) :=
    fun ts => lookup_map_inj (f := id) (fun _ _ h => h) (rnKind ρ) ts r.name
  simp only [findTy, rnRef, ownerOf_rn, hE]
  cases E.lookup (ownerOf cur r.owner) with
  | none => rfl
  | some ts =>
    simp [hT]
    cases ts.lookup r.name <;> rfl

/-! ## Value checks over renamed types -/

theorem rnTyList_eq (ρ : Binary.IfaceName → Binary.IfaceName) :
    ∀ ts : List Binary.Ty, rnTyList ρ ts = ts.map (rnTy ρ)
  | [] => by simp [rnTyList]
  | t :: ts => by simp [rnTyList, rnTyList_eq ρ ts]

variable {ρ : Binary.IfaceName → Binary.IfaceName}

theorem zipOk_rn {ok' ok : Binary.Ty → Val → Bool} (h : ∀ t, ok' (rnTy ρ t) = ok t) :
    ∀ (ts : List Binary.Ty) (vs : List Val), zipOk ok' (ts.map (rnTy ρ)) vs = zipOk ok ts vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, v :: vs => by simp [zipOk, h t, zipOk_rn h ts vs]

theorem optOk_rn {ok' ok : Binary.Ty → Val → Bool} (h : ∀ t, ok' (rnTy ρ t) = ok t)
    (a : Option Binary.Ty) (p : Option Val) : optOk ok' (rnTyOpt ρ a) p = optOk ok a p := by
  cases a <;> cases p <;> simp [optOk, rnTyOpt, h]

theorem pairOk_rn {ok' ok : Binary.Ty → Val → Bool} (h : ∀ t, ok' (rnTy ρ t) = ok t)
    (k w : Binary.Ty) : pairOk ok' (rnTy ρ k) (rnTy ρ w) = pairOk ok k w := by
  funext v
  unfold pairOk
  split <;> simp [h]

theorem resV_rn {ok' ok : Binary.Ty → Val → Bool} (h : ∀ t, ok' (rnTy ρ t) = ok t)
    (a b : Option Binary.Ty) : resV ok' (rnTyOpt ρ a) (rnTyOpt ρ b) = resV ok a b := by
  funext v
  unfold resV
  split <;> simp [optOk_rn h]

/-- **A renamed kind checks the same values**, for value checks that agree on renamed types. -/
theorem kindOk_rn {ok' ok : Binary.IfaceName → Binary.Ty → Val → Bool}
    (h : ∀ c t, ok' (ρ c) (rnTy ρ t) = ok c t) (j : Binary.IfaceName) (k : Binary.TyDefKind)
    (v : Val) : kindOk ok' (ρ j) (rnKind ρ k) v = kindOk ok j k v := by
  have hj : ∀ t, ok' (ρ j) (rnTy ρ t) = ok j t := h j
  cases k with
  | record fs =>
    have hm : (fs.map fun f => ({ f with ty := rnTy ρ f.ty } : Binary.Labeled Binary.Ty)).map
        (·.ty) = (fs.map (·.ty)).map (rnTy ρ) := by simp
    cases v <;> simp only [kindOk, rnKind, hm, zipOk_rn hj]
  | variant cs =>
    cases v with
    | variant i p =>
      simp only [kindOk, rnKind, List.getElem?_map]
      cases cs[i]? with
      | none => rfl
      | some c => exact optOk_rn hj c.ty p
    | _ => rfl
  | type t => exact congrFun (hj t) v
  | enum _ =>
    cases v with
    | variant i p => cases p <;> rfl
    | _ => rfl
  | flags _ | resource => cases v <;> rfl

/-! ## The resolved typing -/

/-- **Renaming does not change the resolved typing.** -/
theorem tyOkR_rn (hρ : Function.Injective ρ) (E : TyEnv) :
    ∀ (n : Nat) (cur : Binary.IfaceName) (t : Binary.Ty),
      tyOkR (rnEnv ρ E) n (ρ cur) (rnTy ρ t) = tyOkR E n cur t
  | 0, _, _ => by funext v; simp [tyOkR]
  | n + 1, cur, t => by
    have ih : ∀ c t, tyOkR (rnEnv ρ E) n (ρ c) (rnTy ρ t) = tyOkR E n c t :=
      fun c t => tyOkR_rn hρ E n c t
    funext v
    cases t with
    | ref r =>
      show (match findTy (rnEnv ρ E) (ρ cur) (rnRef ρ r) with
          | some (j, k) => kindOk (tyOkR (rnEnv ρ E) n) j k v | none => false) =
        (match findTy E cur r with | some (j, k) => kindOk (tyOkR E n) j k v | none => false)
      rw [findTy_rn hρ]
      cases findTy E cur r with
      | none => rfl
      | some p => exact kindOk_rn (fun c t => ih c t) p.1 p.2 v
    | tuple ts => cases v <;> simp [tyOkR, rnTy, rnTyList_eq, zipOk_rn (ih cur)]
    | map k w => simp [tyOkR, rnTy, pairOk_rn (ih cur)]
    | result a b => simp [tyOkR, rnTy, resV_rn (ih cur)]
    | _ => simp [tyOkR, rnTy, ih]

theorem argsOkR_rn (hρ : Function.Injective ρ) (E : TyEnv) (i : Binary.IfaceName)
    (s : Binary.Sig) (a : List Val) : argsOkR (rnEnv ρ E) (ρ i) (rnSig ρ s) a = argsOkR E i s a := by
  have hm : (rnSig ρ s).params.map Prod.snd = (s.params.map Prod.snd).map (rnTy ρ) := by
    simp [rnSig]
  simp only [argsOkR, hm, zipOk_rn (fun t => tyOkR_rn hρ E fuel i t)]

theorem resOkR_rn (hρ : Function.Injective ρ) (E : TyEnv) (i : Binary.IfaceName)
    (s : Binary.Sig) (r : Option (List Val)) : resOkR (rnEnv ρ E) (ρ i) (rnSig ρ s) r = resOkR E i s r := by
  rcases r with _ | vs
  · rfl
  · cases hs : s.result with
    | none => simp [resOkR, rnSig, rnTyOpt, hs]
    | some t =>
      rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩ <;> simp [resOkR, rnSig, rnTyOpt, hs, tyOkR_rn hρ]

/-- The renamed table finds the renamed entry. -/
theorem rnPkg_lookup (P : RPkg) (f : FnName) :
    (rnPkg ρ P).1.lookup f = (P.1.lookup f).map fun x => (ρ x.1, rnSig ρ x.2) := by
  have h := lookup_map_inj (f := (id : FnName → FnName)) (fun _ _ h => h)
    (fun x : Binary.IfaceName × Binary.Sig => (ρ x.1, rnSig ρ x.2)) P.1 f
  simpa [rnPkg] using h

/-- **Renaming a package does not change its resolved typing.** -/
theorem witROk_rn (hρ : Function.Injective ρ) (P : RPkg) (e : WEv) :
    witROk (rnPkg ρ P) e = witROk P e := by
  cases e with
  | imp f a r =>
    simp only [witROk, rnPkg_lookup]
    cases P.1.lookup f with
    | none => rfl
    | some x => simp [rnPkg, argsOkR_rn hρ, resOkR_rn hρ]
  | _ => rfl

/-- The same with traps admitted. -/
theorem witRTrapOk_rn (hρ : Function.Injective ρ) (P : RPkg) (e : WEv) :
    witRTrapOk (rnPkg ρ P) e = witRTrapOk P e := by
  cases e with
  | imp f a r =>
    simp only [witRTrapOk, rnPkg_lookup]
    cases P.1.lookup f with
    | none => rfl
    | some x => simp [rnPkg, argsOkR_rn hρ, resOkR_rn hρ]
  | _ => rfl

/-- Exchanging two versions twice is the identity. -/
theorem swapVer_swapVer (a b : String) (j : Binary.IfaceName) :
    swapVer a b (swapVer a b j) = j := by
  obtain ⟨⟨ns, nm, v⟩, i⟩ := j
  by_cases ha : v = some a <;> by_cases hb : v = some b <;> simp_all [swapVer]

theorem swapVer_injective (a b : String) : Function.Injective (swapVer a b) :=
  fun x y h => by rw [← swapVer_swapVer a b x, h, swapVer_swapVer]

end Silmaril.Wasi.Versions.WitImport
