module

public import Silmaril.Wasi.Versions.WitImport.RNet.Thms

/-!
# Kernel checks on the output of the resolving importer glue

The resolving importer adds three pieces of unverified glue (`rtable`, `envOf`, `plainKind`,
`Silmaril.Wasi.Versions.WitImport.RImport`). Their outputs are quoted constants, so properties of
the outputs can be checked by the kernel even though the glue itself runs in the evaluator.
This module checks, for every resolved package:

* **closed and fuel-adequate** (`RClosed`): every named type reachable from a signature
  resolves in the environment (`envOf` lost no definition a signature needs, and `rtable`
  attached an interface in which the `.local` names resolve), every handle names a known
  type, and the nesting fits in the fuel. **`tyOkR_fuel_mono`** / **`tyOkR_fuel_add`**: on a
  well-formed type more fuel changes nothing. So for these packages the resolved typing
  with `fuel = 32` is the typing with any fuel `≥ 32` (`closed_fuel`): the fuel is not a
  source of spurious rejections. Before, this was only an informal claim.
* **one entry per interface** (`KeysNodup`): `List.lookup` on the environment sees every
  interface's own types;
* **doc-free** (`DocFree`): the environment is a fixed point of `plainKind`, which is what
  `plainKind` is for;
* every function's interface is a key of the environment (`IfacesKnown`).

All are decided by the kernel (`rpkgs_checked`). What remains trusted is that the kinds in
the environment are the ones the WIT files define (the evaluator runs the verified front end;
kernel evaluation of the parser on whole files did not finish, Follow-up 3).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.WitImport

open Silmaril.Wasi
open Silmaril.Wasm.Wit
open Silmaril.Wasm.Component (Val)

/-- The types of a kind are well formed, for a check `ok`. -/
def wfKind (ok : Binary.IfaceName → Binary.Ty → Bool) (j : Binary.IfaceName) :
    Binary.TyDefKind → Bool
  | .record fs => fs.all fun f => ok j f.ty
  | .variant cs => cs.all fun c => c.ty.all (ok j)
  | .type t => ok j t
  | _ => true

/-- `t`, seen from `cur`, is well formed with fuel `n`: every named type and handle resolves,
within `n` nested constructors or named types (the fuel accounting of `tyOkR`). -/
def wfTy (E : TyEnv) : Nat → Binary.IfaceName → Binary.Ty → Bool
  | 0, _, _ => false
  | n + 1, cur, t =>
    match t with
    | .prim _ => true
    | .ref r =>
      match findTy E cur r with
      | some (j, k) => wfKind (wfTy E n) j k
      | none => false
    | .list t => wfTy E n cur t
    | .fixedList t _ => wfTy E n cur t
    | .map k w => wfTy E n cur k && wfTy E n cur w
    | .option t => wfTy E n cur t
    | .result a b => a.all (wfTy E n cur) && b.all (wfTy E n cur)
    | .tuple ts => ts.all (wfTy E n cur)
    | .own r | .borrow r => (findTy E cur r).isSome
    | .future _ | .stream _ => true

/-- Every signature of the package is well formed with the fuel of `tyOkR`. -/
def RClosed (P : RPkg) : Bool :=
  P.1.all fun x => x.2.2.params.all (fun p => wfTy P.2 fuel x.2.1 p.2) &&
    x.2.2.result.all (wfTy P.2 fuel x.2.1)

/-- The environment has one entry per interface. -/
def KeysNodup (P : RPkg) : Bool := decide (P.2.map Prod.fst).Nodup

/-- The environment is a fixed point of `plainKind` (no doc comments). -/
def DocFree (P : RPkg) : Bool := P.2.all fun x => x.2.all fun d => decide (plainKind d.2 = d.2)

/-- Every function's interface is a key of the environment. -/
def IfacesKnown (P : RPkg) : Bool := P.1.all fun x => (P.2.lookup x.2.1).isSome

/-- All four checks. -/
def RChecked (P : RPkg) : Bool := RClosed P && KeysNodup P && DocFree P && IfacesKnown P

/-- **Every resolved package passes the checks.** -/
theorem rpkgs_checked :
    [io2P, clocks2P, cli2P, fs2P, sock2P, sock3P, http2P, rand2P, rand3P, clocks3P, cli3P,
      fs3P, http3P].all RChecked = true := by
  decide +kernel

/-! ## More fuel changes nothing on well-formed types -/

theorem zipOk_congr {f g : Binary.Ty → Val → Bool} :
    ∀ (ts : List Binary.Ty), (∀ t ∈ ts, ∀ v, f t v = g t v) →
      ∀ vs : List Val, zipOk f ts vs = zipOk g ts vs
  | [], _, [] => rfl
  | [], _, _ :: _ => rfl
  | _ :: _, _, [] => rfl
  | t :: ts, h, v :: vs => by
    simp [zipOk, h t List.mem_cons_self v,
      zipOk_congr ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) vs]

theorem optOk_congr {f g : Binary.Ty → Val → Bool} :
    ∀ (a : Option Binary.Ty), (∀ t ∈ a, ∀ v, f t v = g t v) →
      ∀ p : Option Val, optOk f a p = optOk g a p
  | none, _, p => by cases p <;> rfl
  | some t, h, none => rfl
  | some t, h, some v => by simpa [optOk] using h t rfl v

theorem kindOk_congr_record {f g : Binary.IfaceName → Binary.Ty → Val → Bool}
    {wf : Binary.Ty → Bool} (j : Binary.IfaceName) (fs : List (Binary.Labeled Binary.Ty))
    (hk : ∀ x ∈ fs, wf x.ty = true) (h : ∀ t, wf t = true → ∀ v, f j t v = g j t v) (v : Val) :
    kindOk f j (.record fs) v = kindOk g j (.record fs) v := by
  cases v <;> try rfl
  simp only [kindOk]
  refine zipOk_congr _ (fun t ht v => h t ?_ v) _
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
  exact hk x hx

theorem kindOk_congr_variant {f g : Binary.IfaceName → Binary.Ty → Val → Bool}
    {wf : Binary.Ty → Bool} (j : Binary.IfaceName) (cs : List (Binary.Labeled (Option Binary.Ty)))
    (hk : ∀ c ∈ cs, ∀ t ∈ c.ty, wf t = true) (h : ∀ t, wf t = true → ∀ v, f j t v = g j t v)
    (v : Val) : kindOk f j (.variant cs) v = kindOk g j (.variant cs) v := by
  cases v <;> try rfl
  rename_i i p
  simp only [kindOk]
  cases hc : cs[i]? with
  | none => rfl
  | some c => exact optOk_congr _ (fun t ht v => h t (hk c (List.mem_of_getElem? hc) t ht) v) p

theorem kindOk_congr_enum {f g : Binary.IfaceName → Binary.Ty → Val → Bool} (j : Binary.IfaceName)
    (cs : List (Binary.Labeled Unit)) (v : Val) :
    kindOk f j (.enum cs) v = kindOk g j (.enum cs) v := by
  cases v <;> try rfl
  rename_i i p
  rcases p with _ | p <;> rfl

theorem kindOk_congr {f g : Binary.IfaceName → Binary.Ty → Val → Bool} {wf : Binary.Ty → Bool}
    (j : Binary.IfaceName) (k : Binary.TyDefKind) (hk : wfKind (fun _ => wf) j k = true)
    (h : ∀ t, wf t = true → ∀ v, f j t v = g j t v) (v : Val) :
    kindOk f j k v = kindOk g j k v := by
  cases k with
  | record fs => exact kindOk_congr_record j fs (by simpa [wfKind] using hk) h v
  | variant cs => exact kindOk_congr_variant j cs (by simpa [wfKind, Option.all_eq_true] using hk) h v
  | enum cs => exact kindOk_congr_enum j cs v
  | flags fs => cases v <;> rfl
  | resource => cases v <;> rfl
  | type t => simpa [kindOk_type] using h t hk v

theorem wfKind_mono {p q : Binary.IfaceName → Binary.Ty → Bool} (j : Binary.IfaceName)
    (h : ∀ t, p j t = true → q j t = true) :
    ∀ k : Binary.TyDefKind, wfKind p j k = true → wfKind q j k = true
  | .record fs, hk => by
    simp only [wfKind, List.all_eq_true] at hk ⊢
    exact fun x hx => h _ (hk x hx)
  | .variant cs, hk => by
    simp only [wfKind, List.all_eq_true, Option.all_eq_true] at hk ⊢
    exact fun c hc t ht => h _ (hk c hc t ht)
  | .enum _, _ => rfl
  | .flags _, _ => rfl
  | .resource, _ => rfl
  | .type t, hk => h t hk

/-- **Well-formedness is monotone in the fuel.** -/
theorem wfTy_mono (E : TyEnv) :
    ∀ (n : Nat) (c : Binary.IfaceName) (t : Binary.Ty), wfTy E n c t = true →
      wfTy E (n + 1) c t = true
  | 0, _, _, h => by simp [wfTy] at h
  | n + 1, c, t, h => by
    have ih : ∀ c t, wfTy E n c t = true → wfTy E (n + 1) c t = true := wfTy_mono E n
    cases t with
    | prim p => rfl
    | ref r =>
      simp only [wfTy] at h ⊢
      cases hf : findTy E c r with
      | none => simp [hf] at h
      | some x =>
        obtain ⟨j, k⟩ := x
        simp only [hf] at h ⊢
        exact wfKind_mono j (fun t ht => ih j t ht) k h
    | list t => exact ih c t h
    | fixedList t _ => exact ih c t h
    | map k w =>
      simp only [wfTy, Bool.and_eq_true] at h ⊢
      exact ⟨ih c k h.1, ih c w h.2⟩
    | option t => exact ih c t h
    | result a b =>
      simp only [wfTy, Bool.and_eq_true, Option.all_eq_true] at h ⊢
      exact ⟨fun t ht => ih c t (h.1 t ht), fun t ht => ih c t (h.2 t ht)⟩
    | tuple ts =>
      simp only [wfTy, List.all_eq_true] at h ⊢
      exact fun t ht => ih c t (h t ht)
    | own r => exact h
    | borrow r => exact h
    | future r => rfl
    | stream r => rfl

theorem pairOk_congr {f g : Binary.Ty → Val → Bool} {k w : Binary.Ty}
    (hk : ∀ v, f k v = g k v) (hw : ∀ v, f w v = g w v) (v : Val) :
    pairOk f k w v = pairOk g k w v := by
  cases v <;> try rfl
  rename_i vs
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, vs⟩⟩⟩ <;> try rfl
  simp [pairOk, hk, hw]

section Eqns

variable {E : TyEnv} {n : Nat} {c : Binary.IfaceName} {v : Val}

theorem tyOkR_map (k w : Binary.Ty) :
    tyOkR E (n + 1) c (.map k w) v = recV (pairOk (tyOkR E n c) k w) v := rfl
theorem tyOkR_fixedList (t : Binary.Ty) (k : Nat) :
    tyOkR E (n + 1) c (.fixedList t k) v =
      match v with
      | .record vs => vs.length == k && vs.all (tyOkR E n c t)
      | _ => false := rfl

end Eqns

theorem wfTy_add (E : TyEnv) (n : Nat) (c : Binary.IfaceName) (t : Binary.Ty)
    (h : wfTy E n c t = true) : ∀ m, wfTy E (n + m) c t = true
  | 0 => h
  | m + 1 => wfTy_mono E _ c t (wfTy_add E n c t h m)

/-- **One more unit of fuel changes nothing on a well-formed type.** -/
theorem tyOkR_fuel_mono (E : TyEnv) :
    ∀ (n : Nat) (c : Binary.IfaceName) (t : Binary.Ty), wfTy E n c t = true →
      ∀ v : Val, tyOkR E (n + 1) c t v = tyOkR E n c t v
  | 0, _, _, h, _ => by simp [wfTy] at h
  | n + 1, c, t, h, v => by
    have ih : ∀ c t, wfTy E n c t = true → ∀ v, tyOkR E (n + 1) c t v = tyOkR E n c t v :=
      tyOkR_fuel_mono E n
    have hf : ∀ c t, wfTy E n c t = true → tyOkR E (n + 1) c t = tyOkR E n c t :=
      fun c t ht => funext (ih c t ht)
    cases t with
    | prim p => rfl
    | ref r =>
      simp only [wfTy] at h
      cases hfd : findTy E c r with
      | none => simp [hfd] at h
      | some x =>
        obtain ⟨j, k⟩ := x
        simp only [hfd] at h
        rw [tyOkR_ref hfd, tyOkR_ref hfd]
        exact kindOk_congr (wf := wfTy E n j) j k h (fun t ht v => ih j t ht v) v
    | list t => simp only [tyOkR_list, hf c t h]
    | fixedList t k =>
      simp only [wfTy] at h
      rw [tyOkR_fixedList, tyOkR_fixedList, hf c t h]
    | map k w =>
      simp only [wfTy, Bool.and_eq_true] at h
      rw [tyOkR_map, tyOkR_map]
      have hp : pairOk (tyOkR E (n + 1) c) k w = pairOk (tyOkR E n c) k w :=
        funext (pairOk_congr (ih c k h.1) (ih c w h.2))
      rw [hp]
    | option t => simp only [tyOkR_option, hf c t h]
    | result a b =>
      simp only [wfTy, Bool.and_eq_true, Option.all_eq_true] at h
      rw [tyOkR_result, tyOkR_result]
      cases v <;> try rfl
      rename_i i p
      rcases i with _ | _ | i
      · exact optOk_congr a (fun t ht v => ih c t (h.1 t ht) v) p
      · exact optOk_congr b (fun t ht v => ih c t (h.2 t ht) v) p
      · rfl
    | tuple ts =>
      simp only [wfTy, List.all_eq_true] at h
      cases v <;> try rfl
      exact zipOk_congr ts (fun t ht v => ih c t (h t ht) v) _
    | own r => rfl
    | borrow r => rfl
    | future r => rfl
    | stream r => rfl

/-- **Any amount of extra fuel changes nothing on a well-formed type.** -/
theorem tyOkR_fuel_add (E : TyEnv) (n : Nat) (c : Binary.IfaceName) (t : Binary.Ty)
    (h : wfTy E n c t = true) (v : Val) : ∀ m, tyOkR E (n + m) c t v = tyOkR E n c t v
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc, tyOkR_fuel_mono E _ c t (wfTy_add E n c t h m),
      tyOkR_fuel_add E n c t h v m]

/-- **For a closed package, `fuel` is enough**: every parameter and result type of an entry
has the same resolved typing with any larger fuel. -/
theorem closed_fuel {P : RPkg} (hP : RClosed P = true) {f : FnName} {i : Binary.IfaceName}
    {s : Binary.Sig} (hl : P.1.lookup f = some (i, s)) (m : Nat) (v : Val) :
    (∀ p ∈ s.params, tyOkR P.2 (fuel + m) i p.2 v = tyOkR P.2 fuel i p.2 v) ∧
    (∀ t ∈ s.result, tyOkR P.2 (fuel + m) i t v = tyOkR P.2 fuel i t v) := by
  simp only [RClosed, List.all_eq_true, Bool.and_eq_true, Option.all_eq_true] at hP
  have h := hP _ (rlookup_mem hl)
  exact ⟨fun p hp => tyOkR_fuel_add _ _ _ _ (h.1 p hp) v m,
    fun t ht => tyOkR_fuel_add _ _ _ _ (h.2 t ht) v m⟩

end Silmaril.Wasi.Versions.WitImport
