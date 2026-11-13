module

public import Silmaril.Wasm.FX.Asyncify.Live.Defs
public import Silmaril.Wasm.FX.Asyncify.RelSim.Thms

/-!
# Save functions that keep the live locals do not change behaviours

Two runs of the kernel with locals, with save functions `sv` and `sv'` that both keep the live
locals (`KeepsLive`), run in lock step for the relation `CR`: equal code, operands and waits,
and locals that **agree on the live locals** of each frame's code (`FrR`).

* `live_sub`: an instruction other than `set` keeps every local live after it live before it;
* `save_agree`: two saves of agreeing locals agree on the live locals;
* `split_rel`: the handler search on related stacks;
* `call_rel`, `resume_rel`, `suspend_rel`, `exec_rel`: one case per instruction;
* **`lock`**: the lock step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Live

open Silmaril.Wasm.Models.FXAsync Silmaril.Wasm.FX.Asyncify.Live
open Silmaril.Wasm.FX.Asyncify.RelSim

variable {V : Type}

/-- Locals agreeing on the live locals of `c`. -/
def Agree (c : List (LIns V)) (la lb : Locals V) : Prop := ∀ y, live c y = true → la y = lb y

/-- Related frames. -/
def FrR (a b : LFrame V) : Prop :=
  a.code = b.code ∧ a.ops = b.ops ∧ a.wait = b.wait ∧ Agree a.code a.locals b.locals

/-- Related configurations. -/
def CR (x y : LCfg V) : Prop :=
  List.Forall₂ (Option.Rel (List.Forall₂ FrR)) x.conts y.conts ∧ List.Forall₂ FrR x.stack y.stack

theorem frR_mk {c : List (LIns V)} {o : List (SV V)} {w : Option (List Clause)} {la lb : Locals V}
    (h : Agree c la lb) : FrR ⟨c, o, la, w⟩ ⟨c, o, lb, w⟩ := ⟨rfl, rfl, rfl, h⟩

theorem frR_refl (a : LFrame V) : FrR a a := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem frR_ops {a b : LFrame V} (h : FrR a b) (o : List (SV V)) :
    FrR { a with ops := o } { b with ops := o } := ⟨h.1, rfl, h.2.2.1, h.2.2.2⟩

theorem frR_pre {a b : LFrame V} (h : FrR a b) (p : List (SV V)) :
    FrR { a with ops := p ++ a.ops } { b with ops := p ++ b.ops } := by
  have ho : a.ops = b.ops := h.2.1
  rw [ho]
  exact frR_ops h _

theorem frR_wait {a b : LFrame V} (h : FrR a b) (w : Option (List Clause)) :
    FrR { a with wait := w } { b with wait := w } := ⟨h.1, h.2.1, rfl, h.2.2.2⟩

theorem live_sub {i : LIns V} (hi : ∀ x, i ≠ .set x) (c : List (LIns V)) :
    ∀ y, live c y = true → live (i :: c) y = true := by
  intro y hy
  cases i with
  | get x =>
    show (x == y || live c y) = true
    rw [hy, Bool.or_true]
  | set x => exact absurd rfl (hi x)
  | _ => exact hy

theorem agree_tail {i : LIns V} (hi : ∀ x, i ≠ .set x) {c : List (LIns V)} {la lb : Locals V}
    (h : Agree (i :: c) la lb) : Agree c la lb :=
  fun y hy => h y (live_sub hi c y hy)

theorem save_agree {sv sv' : Save V} (hs : KeepsLive sv) (hs' : KeepsLive sv')
    {c : List (LIns V)} {la lb : Locals V} (h : Agree c la lb) : Agree c (sv c la) (sv' c lb) :=
  fun y hy => by rw [hs c la y hy, hs' c lb y hy]; exact h y hy

theorem fresh_agree (c : List (LIns V)) : Agree c fresh fresh := fun _ _ => rfl

theorem rel_map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {f : α → γ} {g : β → δ}
    {a : Option α} {b : Option β} (h : Option.Rel R a b) (hfg : ∀ x y, R x y → S (f x) (g y)) :
    Option.Rel S (a.map f) (b.map g) := by
  cases h with
  | none => exact .none
  | some hxy => exact .some (hfg _ _ hxy)

/-- The handler search on related stacks. -/
theorem split_rel (t : Nat) {rest rest' : List (LFrame V)} (h : List.Forall₂ FrR rest rest') :
    Option.Rel (fun x x' => List.Forall₂ FrR x.1 x'.1 ∧ x.2.1 = x'.2.1 ∧ FrR x.2.2.1 x'.2.2.1 ∧
      List.Forall₂ FrR x.2.2.2 x'.2.2.2) (lsplit t rest) (lsplit t rest') := by
  induction h with
  | nil => exact .none
  | @cons b b' r r' hb hr ih =>
    have hw : b.wait = b'.wait := hb.2.2.1
    cases hl : b.wait.bind (lookup t) with
    | some hf =>
      have hl' : b'.wait.bind (lookup t) = some hf := by rw [← hw]; exact hl
      simp only [lsplit, hl, hl']
      exact .some ⟨.nil, rfl, hb, hr⟩
    | none =>
      have hl' : b'.wait.bind (lookup t) = none := by rw [← hw]; exact hl
      simp only [lsplit, hl, hl']
      exact rel_map ih fun _ _ hx => ⟨.cons hb hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩

variable {P : Prog (LIns V)} {sv sv' : Save V} {test : V → Bool}
  {K K' : List (Option (List (LFrame V)))} {rest rest' : List (LFrame V)}

theorem call_rel (hs : KeepsLive sv) (hs' : KeepsLive sv')
    (hK : List.Forall₂ (Option.Rel (List.Forall₂ FrR)) K K') (hr : List.Forall₂ FrR rest rest')
    (f : Nat) (c' c : List (LIns V)) (ops ops0 : List (SV V)) {la lb : Locals V}
    (w : Option (List Clause))
    (h : Agree c la lb) :
    RRes CR (lcall P sv K f ⟨c', ops0, la, w⟩ ops c rest) (lcall P sv' K' f ⟨c', ops0, lb, w⟩ ops c rest') := by
  cases hf : P f with
  | none => simp only [lcall, hf]; exact .stop _
  | some x =>
    obtain ⟨np, body⟩ := x
    cases hp : popN np ops with
    | none => simp only [lcall, hf, hp]; exact .stop _
    | some y =>
      simp only [lcall, hf, hp]
      exact .next ⟨hK, .cons (frR_refl _) (.cons (frR_mk (save_agree hs hs' h)) hr)⟩

theorem resume_match {a b : Option (Option (List (LFrame V)))}
    (hab : Option.Rel (Option.Rel (List.Forall₂ FrR)) a b) {Kn Kn' : List (Option (List (LFrame V)))}
    (hKn : List.Forall₂ (Option.Rel (List.Forall₂ FrR)) Kn Kn') (hr : List.Forall₂ FrR rest rest')
    (args : List (SV V)) {sa sb : LFrame V} (hsv : FrR sa sb) :
    RRes CR (match (generalizing := false) a with
        | some (some (top :: seg)) =>
          .next ⟨Kn, { top with ops := args ++ top.ops } :: seg ++ sa :: rest⟩
        | _ => (.stop .trap : Res (LCfg V) V))
      (match (generalizing := false) b with
        | some (some (top :: seg)) =>
          .next ⟨Kn', { top with ops := args ++ top.ops } :: seg ++ sb :: rest'⟩
        | _ => (.stop .trap : Res (LCfg V) V)) := by
  cases hab with
  | none => exact .stop _
  | some hab =>
    cases hab with
    | none => exact .stop _
    | some hl =>
      cases hl with
      | nil => exact .stop _
      | cons htop hseg => exact .next ⟨hKn, .cons (frR_pre htop _) (List.rel_append hseg (.cons hsv hr))⟩

theorem resume_rel (hs : KeepsLive sv) (hs' : KeepsLive sv')
    (hK : List.Forall₂ (Option.Rel (List.Forall₂ FrR)) K K') (hr : List.Forall₂ FrR rest rest')
    (n : Nat) (hcl : List Clause) (c' c : List (LIns V)) (ops : List (SV V)) {la lb : Locals V}
    (w : Option (List Clause)) (h : Agree c la lb) :
    RRes CR (lexec P sv test K ⟨c', ops, la, w⟩ (.resume n hcl) c rest)
      (lexec P sv' test K' ⟨c', ops, lb, w⟩ (.resume n hcl) c rest') := by
  rcases ops with _ | ⟨_ | k, o⟩
  · exact .stop _
  · exact .stop _
  · cases hp : popN n o with
    | none => simp only [lexec, hp]; exact .stop _
    | some y =>
      have hsave : FrR ⟨c, y.2, sv c la, some hcl⟩ ⟨c, y.2, sv' c lb, some hcl⟩ :=
        frR_mk (save_agree hs hs' h)
      simp only [lexec, hp]
      exact resume_match (forall₂_getElem? hK k) (forall₂_set hK .none k) hr y.1 hsave

theorem handler_rel (hK : List.Forall₂ (Option.Rel (List.Forall₂ FrR)) K K')
    {cap cap' : LFrame V} (hcap : FrR cap cap') {m m' rs rs' : List (LFrame V)} {r r' : LFrame V}
    (hm : List.Forall₂ FrR m m') (hrr : FrR r r') (hrs : List.Forall₂ FrR rs rs') (hf : Nat)
    (p : List (SV V)) :
    RRes CR (match P hf with
        | none => (.stop .trap : Res (LCfg V) V)
        | some (_, body) =>
          .next ⟨K ++ [some (cap :: m)], ⟨body, .cont K.length :: p, fresh, none⟩ ::
            { r with wait := none } :: rs⟩)
      (match P hf with
        | none => (.stop .trap : Res (LCfg V) V)
        | some (_, body) =>
          .next ⟨K' ++ [some (cap' :: m')], ⟨body, .cont K'.length :: p, fresh, none⟩ ::
            { r' with wait := none } :: rs'⟩) := by
  have hlen : K'.length = K.length := hK.length_eq.symm
  cases P hf with
  | none => exact .stop _
  | some x =>
    rw [hlen]
    exact .next ⟨forall₂_append_one hK (.some (.cons hcap hm)),
      .cons (frR_refl _) (.cons (frR_wait hrr none) hrs)⟩

theorem suspend_rel (hs : KeepsLive sv) (hs' : KeepsLive sv')
    (hK : List.Forall₂ (Option.Rel (List.Forall₂ FrR)) K K') (hr : List.Forall₂ FrR rest rest')
    (t n : Nat) (c' c : List (LIns V)) (ops : List (SV V)) {la lb : Locals V}
    (w : Option (List Clause)) (h : Agree c la lb) :
    RRes CR (lexec P sv test K ⟨c', ops, la, w⟩ (.suspend t n) c rest)
      (lexec P sv' test K' ⟨c', ops, lb, w⟩ (.suspend t n) c rest') := by
  cases hp : popN n ops with
  | none => simp only [lexec, hp]; exact .stop _
  | some y =>
    have hsp := split_rel t hr
    have hcap : FrR ⟨c, y.2, sv c la, w⟩ ⟨c, y.2, sv' c lb, w⟩ := frR_mk (save_agree hs hs' h)
    simp only [lexec, hp]
    generalize lsplit t rest = a at hsp ⊢
    generalize lsplit t rest' = b at hsp ⊢
    cases hsp with
    | none => exact .stop _
    | @some x x' hx =>
      obtain ⟨m, hf, r, rs⟩ := x
      obtain ⟨m', hf', r', rs'⟩ := x'
      obtain ⟨hm, hh, hrr, hrs⟩ := hx
      have hh' : hf' = hf := hh.symm
      rw [hh']
      exact handler_rel hK hcap hm hrr hrs hf y.1

theorem agree_set {x : Nat} {c : List (LIns V)} {la lb : Locals V} (h : Agree (.set x :: c) la lb)
    (v : SV V) : Agree c (upd la x v) (upd lb x v) := by
  intro y hy
  by_cases hyx : y = x
  · simp only [upd, hyx, ite_true]
  · have hl : live (.set x :: c) y = true := by
      simp only [live, bne_iff_ne, ne_eq, Bool.and_eq_true]
      exact ⟨fun e => hyx e.symm, hy⟩
    simp only [upd, hyx, ite_false]
    exact h y hl

theorem get_eq {x : Nat} {c : List (LIns V)} {la lb : Locals V} (h : Agree (.get x :: c) la lb) :
    la x = lb x :=
  h x (by simp only [live, beq_self_eq_true, Bool.true_or])

theorem exec_rel (hs : KeepsLive sv) (hs' : KeepsLive sv')
    (hK : List.Forall₂ (Option.Rel (List.Forall₂ FrR)) K K') (hr : List.Forall₂ FrR rest rest')
    (i : LIns V) (c : List (LIns V)) (ops : List (SV V)) {la lb : Locals V}
    (w : Option (List Clause)) (h : Agree (i :: c) la lb) :
    RRes CR (lexec P sv test K ⟨i :: c, ops, la, w⟩ i c rest)
      (lexec P sv' test K' ⟨i :: c, ops, lb, w⟩ i c rest') := by
  have ht : ∀ {j : LIns V}, (∀ x, j ≠ .set x) → Agree (j :: c) la lb → Agree c la lb :=
    fun hj hh => agree_tail hj hh
  cases i with
  | push v => exact .next ⟨hK, .cons (frR_mk (ht (fun _ e => by cases e) h)) hr⟩
  | prim n op =>
    have hc : Agree c la lb := ht (fun _ e => by cases e) h
    cases hp : popN n ops with
    | none => simp only [lexec, hp]; exact .stop _
    | some y =>
      cases ha : allVals y.1 with
      | none => simp only [lexec, hp, ha]; exact .stop _
      | some vs => simp only [lexec, hp, ha]; exact .next ⟨hK, .cons (frR_mk hc) hr⟩
  | drop =>
    rcases ops with _ | ⟨_, o⟩
    · exact .stop _
    · exact .next ⟨hK, .cons (frR_mk (ht (fun _ e => by cases e) h)) hr⟩
  | get x =>
    have hc : Agree c la lb := ht (fun _ e => by cases e) h
    show RRes CR (.next ⟨K, ⟨c, la x :: ops, la, w⟩ :: rest⟩) (.next ⟨K', ⟨c, lb x :: ops, lb, w⟩ :: rest'⟩)
    rw [get_eq h]
    exact .next ⟨hK, .cons (frR_mk hc) hr⟩
  | set x =>
    rcases ops with _ | ⟨v, o⟩
    · exact .stop _
    · exact .next ⟨hK, .cons (frR_mk (agree_set h v)) hr⟩
  | call f => exact call_rel hs hs' hK hr f _ c ops ops w (ht (fun _ e => by cases e) h)
  | cond f g =>
    rcases ops with _ | ⟨_ | v, o⟩
    · exact .stop _
    · exact call_rel hs hs' hK hr _ _ c o _ w (ht (fun _ e => by cases e) h)
    · exact .stop _
  | contNew f =>
    have hc : Agree c la lb := ht (fun _ e => by cases e) h
    have hlen : K'.length = K.length := hK.length_eq.symm
    cases hf : P f with
    | none => simp only [lexec, hf]; exact .stop _
    | some y =>
      simp only [lexec, hf, hlen]
      exact .next ⟨forall₂_append_one hK (.some (.cons (frR_refl _) .nil)), .cons (frR_mk hc) hr⟩
  | resume n hcl => exact resume_rel hs hs' hK hr n hcl _ c ops w (ht (fun _ e => by cases e) h)
  | suspend t n => exact suspend_rel hs hs' hK hr t n _ c ops w (ht (fun _ e => by cases e) h)

theorem lock_top (hs : KeepsLive sv) (hs' : KeepsLive sv')
    (hK : List.Forall₂ (Option.Rel (List.Forall₂ FrR)) K K') (hr : List.Forall₂ FrR rest rest')
    (cc : List (LIns V)) (o : List (SV V)) {la lb : Locals V} (w : Option (List Clause))
    (h : Agree cc la lb) :
    RRes CR (lstep P sv test ⟨K, ⟨cc, o, la, w⟩ :: rest⟩)
      (lstep P sv' test ⟨K', ⟨cc, o, lb, w⟩ :: rest'⟩) := by
  cases cc with
  | nil =>
    cases hr with
    | nil => exact .stop _
    | cons hb hr' => exact .next ⟨hK, .cons (frR_pre hb o) hr'⟩
  | cons i c => exact exec_rel hs hs' hK hr i c o w h

/-- **Lock step.** -/
theorem lock (hs : KeepsLive sv) (hs' : KeepsLive sv') :
    LockStep CR (lstep P sv test) (lstep P sv' test) := by
  rintro ⟨K, st⟩ ⟨K', st'⟩ ⟨hK, hst⟩
  cases hst with
  | nil => exact .stop _
  | @cons a b rest rest' hab hr =>
    obtain ⟨cc, o, la, w⟩ := a
    obtain ⟨cc', o', lb, w'⟩ := b
    obtain ⟨hc, ho, hw, hag⟩ := hab
    have hc' : cc' = cc := hc.symm
    have ho' : o' = o := ho.symm
    have hw' : w' = w := hw.symm
    rw [hc', ho', hw']
    exact lock_top hs hs' hK hr cc o w hag

end Silmaril.Proofs.Wasm.FX.Asyncify.Live
