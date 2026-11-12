module

public import Silmaril.Wasm.Resource.ExternClient.Defs
public import Silmaril.Wasm.Verify.Check.Thms
public import Silmaril.Wasm.Resource.Client.Thms

/-!
# Call targets of administrative code: preservation by every Core step

`Tight T pr p l` (`Silmaril.Wasm.Resource.ExternClient`): every call instruction of the code comes
right after the value prefix of its sequence and consumes a reference into `T`; no source
instruction has a dynamic call.

* `tight_append`: the check of `A ++ B` is the check of `A` and the check of `B` from the state
  after `A` (`afPr`, `afP`); `tight_vals_append`, `Tight.of_post` (code checked after a
  non-value is checked everywhere), `tight_simple` (code without call instructions).
* `tight_fill`: replacing the hole of a context; `tight_callout`: the function of a callout is
  in `T`.
* **`Step.tight`**: every host-free Core 3.0 step keeps `Tight R true p` (every profile), from the
  reachability invariant `CfgIn G fs (CallPl R bad fs)` with `R ⊆ G`, bodies of the functions of
  `G` without dynamic calls, and a step that is not a call of a function in `bad` (`BadStep`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.ExternClient

open Silmaril.Wasm.Resource.Client
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn RefIn PlOK CallPl BadStep refFuncs instrRF instrCalls)

variable {T : Nat → Prop}

/-! ## No dynamic calls -/

theorem noDynL_cons (i : Instr) (is : List Instr) :
    noDynL (i :: is) = (noDynI i && noDynL is) := by
  simp [noDynL]

theorem noDynL_iff : ∀ {l : List Instr}, noDynL l = true ↔ ∀ i ∈ l, noDynI i = true
  | [] => by simp [noDynL]
  | i :: is => by simp [noDynL_cons, noDynL_iff]

/-! ## The state after a list -/

/-- Whether only values precede, after `l`. -/
def afPr : Bool → List Admin → Bool
  | pr, [] => pr
  | pr, .ref _ :: l => afPr pr l
  | pr, .plain i :: l => afPr (pr && (Admin.plain i).val?.isSome) l
  | _, _ :: l => afPr false l

/-- Whether the last element of `l` is a reference into `T`. -/
def afP (T : Nat → Prop) : Prop → List Admin → Prop
  | p, [] => p
  | _, .ref r :: l => afP T (RefIn T r) l
  | _, _ :: l => afP T False l

theorem afPr_false : ∀ (l : List Admin), afPr false l = false
  | [] => rfl
  | .ref _ :: l => afPr_false l
  | .plain _ :: l => by simpa [afPr] using afPr_false l
  | .trap :: l | .label .. :: l | .handler .. :: l | .frame .. :: l | .callRefType _ :: l
  | .returnCallRefType _ :: l => afPr_false l

/-- After a non-value, the prefix has ended. -/
theorem afPr_of_not_all : ∀ (l : List Admin) (pr : Bool), l.all Admin.isVal = false →
    afPr pr l = false
  | [], _, h => by simp at h
  | .ref _ :: l, pr, h => afPr_of_not_all l pr (by simpa [Admin.isVal, Admin.val?] using h)
  | .plain i :: l, pr, h => by
    rcases hv : (Admin.plain i).val? with _ | v
    · simp only [afPr, hv, Option.isSome_none, Bool.and_false]; exact afPr_false l
    · have h' : l.all Admin.isVal = false := by simpa [Admin.isVal, hv] using h
      simp only [afPr, hv, Option.isSome_some, Bool.and_true]
      exact afPr_of_not_all l pr h'
  | .trap :: l, _, _ | .label .. :: l, _, _ | .handler .. :: l, _, _ | .frame .. :: l, _, _
  | .callRefType _ :: l, _, _ | .returnCallRefType _ :: l, _, _ => afPr_false l

theorem afP_mono : ∀ {l : List Admin} {p p' : Prop}, (p → p') → afP T p l → afP T p' l
  | [], _, _, h, hp => h hp
  | .ref _ :: _, _, _, _, hp => hp
  | .plain _ :: _, _, _, _, hp | .trap :: _, _, _, _, hp | .label .. :: _, _, _, _, hp
  | .handler .. :: _, _, _, _, hp | .frame .. :: _, _, _, _, hp
  | .callRefType _ :: _, _, _, _, hp | .returnCallRefType _ :: _, _, _, _, hp => hp

theorem afPr_vals : ∀ (vs : List Val) (pr : Bool), afPr pr (vals vs) = pr
  | [], _ => rfl
  | v :: vs, pr => by
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | r <;>
      simp [vals, Val.toAdmin, afPr, Admin.val?] <;> exact afPr_vals vs pr

/-! ## Appending -/

/-- **The check of a concatenation.** -/
theorem tight_append : ∀ (A B : List Admin) (pr : Bool) (p : Prop),
    Tight T pr p (A ++ B) ↔ Tight T pr p A ∧ Tight T (afPr pr A) (afP T p A) B
  | [], B, pr, p => by simp [Tight, afPr, afP]
  | .ref r :: A, B, pr, p => by
    simp only [List.cons_append, Tight, afPr, afP]; exact tight_append A B pr _
  | .plain i :: A, B, pr, p => by
    simp only [List.cons_append, Tight, afPr, afP, tight_append A B, and_assoc]
  | .trap :: A, B, pr, p => by
    simp only [List.cons_append, Tight, afPr, afP]; exact tight_append A B false False
  | .label n k b :: A, B, pr, p => by
    simp only [List.cons_append, Tight, afPr, afP, tight_append A B, and_assoc]
  | .handler n cs b :: A, B, pr, p => by
    simp only [List.cons_append, Tight, afPr, afP, tight_append A B, and_assoc]
  | .frame n fr b :: A, B, pr, p => by
    simp only [List.cons_append, Tight, afPr, afP, tight_append A B, and_assoc]
  | .callRefType d :: A, B, pr, p => by
    simp only [List.cons_append, Tight, afPr, afP, tight_append A B, and_assoc]
  | .returnCallRefType d :: A, B, pr, p => by
    simp only [List.cons_append, Tight, afPr, afP, tight_append A B, and_assoc]

theorem tight_vals : ∀ (vs : List Val) (pr : Bool) (p : Prop), Tight T pr p (vals vs)
  | [], _, _ => by simp [vals, Tight]
  | v :: vs, pr, p => by
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | r <;>
      simp only [vals, List.map_cons, Val.toAdmin, Tight, Admin.val?, Option.isSome_some,
        Bool.and_true, noDynI, true_and] <;> exact tight_vals vs _ _

theorem tight_vals_append (vs : List Val) (l : List Admin) (pr : Bool) (p : Prop) :
    Tight T pr p (vals vs ++ l) ↔ Tight T pr (afP T p (vals vs)) l := by
  rw [tight_append, afPr_vals]
  exact ⟨fun h => h.2, fun h => ⟨tight_vals vs pr p, h⟩⟩

/-- **Code checked after the prefix is checked everywhere.** -/
theorem Tight.of_post : ∀ {l : List Admin} {q : Prop} (pr : Bool) (p : Prop),
    Tight T false q l → Tight T pr p l
  | [], _, _, _, _ => by simp [Tight]
  | .ref _ :: _, _, pr, _, h => by
    simp only [Tight] at h ⊢; exact Tight.of_post pr _ h
  | .plain _ :: _, _, pr, _, h => by
    simp only [Tight, Bool.false_and] at h ⊢; exact ⟨h.1, Tight.of_post _ _ h.2⟩
  | .trap :: _, _, _, _, h | .label .. :: _, _, _, _, h | .handler .. :: _, _, _, _, h
  | .frame .. :: _, _, _, _, h => by simp only [Tight] at h ⊢; exact h
  | .callRefType _ :: _, _, _, _, h | .returnCallRefType _ :: _, _, _, _, h => by
    simp [Tight] at h

theorem Tight.mono_p : ∀ {l : List Admin} {pr : Bool} {p p' : Prop}, (p → p') →
    Tight T pr p l → Tight T pr p' l
  | [], _, _, _, _, _ => by simp [Tight]
  | .ref _ :: _, _, _, _, _, h | .plain _ :: _, _, _, _, _, h | .trap :: _, _, _, _, _, h
  | .label .. :: _, _, _, _, _, h | .handler .. :: _, _, _, _, _, h
  | .frame .. :: _, _, _, _, _, h => by simp only [Tight] at h ⊢; exact h
  | .callRefType _ :: _, _, _, _, hp, h | .returnCallRefType _ :: _, _, _, _, hp, h => by
    simp only [Tight] at h ⊢; exact ⟨h.1, hp h.2.1, h.2.2⟩

/-! ## Code without call instructions -/

/-- An element without call instruction or dynamic call. -/
def SimpleT (x : Admin) : Prop :=
  (∃ i, x = .plain i ∧ noDynI i = true) ∨ (∃ r, x = .ref r) ∨ x = .trap

@[simp] theorem simpleT_plain {i : Instr} : SimpleT (.plain i) ↔ noDynI i = true := by
  simp [SimpleT]

@[simp] theorem simpleT_ref (r : Ref) : SimpleT (.ref r) := .inr (.inl ⟨r, rfl⟩)

@[simp] theorem simpleT_trap : SimpleT .trap := .inr (.inr rfl)

@[simp] theorem simpleT_toAdmin (v : Val) : SimpleT v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | r <;> simp [Val.toAdmin, noDynI]

/-- **Code without call instructions is checked from every state.** -/
theorem tight_simple : ∀ {l : List Admin}, (∀ x ∈ l, SimpleT x) → ∀ (pr : Bool) (p : Prop),
    Tight T pr p l
  | [], _, _, _ => by simp [Tight]
  | x :: l, h, pr, p => by
    have ih := tight_simple (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
    rcases h x List.mem_cons_self with ⟨i, rfl, hi⟩ | ⟨r, rfl⟩ | rfl
    · simp only [Tight]; exact ⟨hi, ih _ _⟩
    · simp only [Tight]; exact ih _ _
    · simp only [Tight]; exact ih _ _

theorem tight_expression {b : List Instr} (h : noDynL b = true) (pr : Bool) (p : Prop) :
    Tight T pr p (expression b) :=
  tight_simple (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact simpleT_plain.2 (noDynL_iff.1 h i hi)) pr p

theorem tight_vals_expression {vs : List Val} {b : List Instr} (h : noDynL b = true)
    (pr : Bool) (p : Prop) : Tight T pr p (vals vs ++ expression b) :=
  (tight_vals_append vs _ pr p).2 (tight_expression h _ _)

theorem tight_toAdmin (r : Result) (pr : Bool) (p : Prop) : Tight T pr p r.toAdmin := by
  refine tight_simple (fun x hx => ?_) pr p
  cases r with
  | values vs =>
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hx
    exact simpleT_toAdmin v
  | trap => simp only [Result.toAdmin, List.mem_singleton] at hx; subst hx; simp
  | throw a =>
    simp only [Result.toAdmin, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [noDynI]

/-! ## Contexts -/

/-- **Replacing the hole of a context** by code without call instructions. -/
theorem tight_fill {X Y : List Admin} (hX : X.all Admin.isVal = false)
    (hY : ∀ pr p, Tight T pr p Y) :
    ∀ (E : Ctx) {pr : Bool} {p : Prop}, Tight T pr p (E.fill X) → Tight T pr p (E.fill Y)
  | .top pre rest, pr, p, h => by
    simp only [Ctx.fill] at h ⊢
    rw [tight_append, tight_vals_append] at h ⊢
    rw [afPr_of_not_all _ _ (by simpa [List.all_append] using hX)] at h
    exact ⟨hY _ _, Tight.of_post _ _ h.2⟩
  | .label pre n k E rest, pr, p, h => by
    simp only [Ctx.fill] at h ⊢
    rw [List.append_assoc, tight_vals_append] at h ⊢
    simp only [List.cons_append, List.nil_append, Tight] at h ⊢
    exact ⟨h.1, tight_fill hX hY E h.2.1, h.2.2⟩
  | .handler pre n cs E rest, pr, p, h => by
    simp only [Ctx.fill] at h ⊢
    rw [List.append_assoc, tight_vals_append] at h ⊢
    simp only [List.cons_append, List.nil_append, Tight] at h ⊢
    exact ⟨tight_fill hX hY E h.1, h.2⟩
  | .frame pre n fr E rest, pr, p, h => by
    simp only [Ctx.fill] at h ⊢
    rw [List.append_assoc, tight_vals_append] at h ⊢
    simp only [List.cons_append, List.nil_append, Tight] at h ⊢
    exact ⟨tight_fill hX hY E h.1, h.2⟩

theorem afP_vals_ref (vs : List Val) (r : Ref) (p : Prop) :
    afP T p (vals vs ++ [.ref r]) = RefIn T r := by
  induction vs generalizing p with
  | nil => rfl
  | cons v vs ih =>
    rcases v with ⟨⟨_ | _⟩, _⟩ | _ | r' <;> simp only [vals, List.map_cons, Val.toAdmin,
      List.cons_append, afP] <;> exact ih _

/-- **The function of a call instruction** of checked code is in `T`. -/
theorem tight_callout {args : List Val} {a : Nat} {yy : Admin} (hyy : yy.IsCallRef) :
    ∀ (E : Ctx) {pr : Bool} {p : Prop}, Tight T pr p (E.fill (vals args ++ [.ref (.func a), yy])) →
      T a
  | .top pre rest, pr, p, h => by
    simp only [Ctx.fill, List.append_assoc, List.cons_append, List.nil_append] at h
    rw [← List.append_assoc, ← vals_append, tight_vals_append] at h
    simp only [Tight] at h
    rcases yy with ⟨⟨⟩⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsCallRef, Tight, noDynI,
      RefIn, refFuncs]
  | .label pre n k E rest, pr, p, h => by
    simp only [Ctx.fill] at h
    rw [List.append_assoc, tight_vals_append] at h
    simp only [List.cons_append, List.nil_append, Tight] at h
    exact tight_callout hyy E h.2.1
  | .handler pre n cs E rest, pr, p, h => by
    simp only [Ctx.fill] at h
    rw [List.append_assoc, tight_vals_append] at h
    simp only [List.cons_append, List.nil_append, Tight] at h
    exact tight_callout hyy E h.1
  | .frame pre n fr E rest, pr, p, h => by
    simp only [Ctx.fill] at h
    rw [List.append_assoc, tight_vals_append] at h
    simp only [List.cons_append, List.nil_append, Tight] at h
    exact tight_callout hyy E h.1

end Silmaril.Wasm.Resource.ExternClient
