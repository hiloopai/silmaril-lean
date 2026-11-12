module

public import Silmaril.Elf.Link.Dyn.Loader.Defs

/-! # The loader relation: cached resolution

PROVED (standard axioms):

* `resolveK_sound`: resolution from correct lookup tables (`Known.Ok`) is the loader's
  `resolve` wherever the tables answer. This is how per-library facts, checked once per
  library version (`Dyn.Glibc`), are reused by every executable: an executable's binding
  certificate is computed from the tables, never by re-reading the libraries;
* `slotTableWith_mono`: a slot table computed with a resolver that agrees with the loader's
  wherever it answers is the loader's slot table;
* `PageBase.mod16`: the executable's base (the head of page-aligned bases) is 16-byte aligned.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn

open Silmaril.X86 (Word)
open Silmaril.X86.Link (Blob)

@[simp] theorem obind_some {α β : Type} (a : α) (f : α → Option β) : (some a).bind f = f a := rfl

theorem resolveKFrom_sound {ks : List Known} (hk : ∀ k ∈ ks, k.Ok) {n : Nat} {r : Elf.Ref}
    {p : Bool} {x : Option (Nat × Elf.Def)} (h : resolveKFrom n (ks.map (·.facts)) r p = some x) :
    resolveFrom n (ks.map (·.file)) r p = some x := by
  induction ks generalizing n with
  | nil => simpa [resolveKFrom, resolveFrom] using h
  | cons k ks ih =>
    obtain ⟨hinfo, hfacts⟩ := hk k (List.mem_cons_self ..)
    have ih' := @ih (fun k' hm => hk k' (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, resolveKFrom] at h
    split at h
    · rename_i a b d he
      have hm := List.mem_of_find?_eq_some he
      have hp := List.find?_some he
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have hl := hfacts _ hm
      simp only at hl
      cases h
      simp only [List.map_cons, resolveFrom, hinfo, Option.bind_eq_bind, obind_some, hl]
      rfl
    · rename_i a b he
      have hm := List.mem_of_find?_eq_some he
      have hp := List.find?_some he
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have hl := hfacts _ hm
      simp only at hl
      simp only [List.map_cons, resolveFrom, hinfo, Option.bind_eq_bind, obind_some, hl]
      exact ih' h
    · cases h

theorem resolveK_sound {ks : List Known} (hk : ∀ k ∈ ks, k.Ok) {r : Elf.Ref} {p : Bool}
    {x : Option (Nat × Elf.Def)} (h : resolveK (ks.map (·.facts)) r p = some x) :
    resolve (ks.map (·.file)) r p = some x :=
  resolveKFrom_sound hk h

theorem mapM_mono {α β : Type} {f g : α → Option β} (h : ∀ a b, g a = some b → f a = some b) :
    ∀ (l : List α) (bs : List β), l.mapM g = some bs → l.mapM f = some bs := by
  intro l
  induction l with
  | nil => intro bs hb; simpa using hb
  | cons a l ih =>
    intro bs hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hb ⊢
    cases e : g a with
    | none => simp [e] at hb
    | some b =>
      rw [e] at hb
      simp only [obind_some] at hb
      cases e2 : l.mapM g with
      | none => simp [e2] at hb
      | some bs' =>
        rw [e2] at hb
        simp only [obind_some] at hb
        rw [h a b e, obind_some, ih bs' e2, obind_some]
        exact hb

theorem bindVal_mono {R R' : Resolver} (h : ∀ r p x, R' r p = some x → R r p = some x)
    {r : Elf.Ref} {p : Bool} {w : Val} (hw : bindVal R' r p = some w) : bindVal R r p = some w := by
  unfold bindVal at hw ⊢
  cases e : R' r p with
  | none => simp [e] at hw
  | some x => rw [e] at hw; rw [h r p x e]; exact hw

theorem relocVal_mono {R R' : Resolver} (h : ∀ r p x, R' r p = some x → R r p = some x)
    {f : Blob} {i : Elf.DynInfo} {r : Elf.Rela} {w : Val}
    (hw : relocVal R' f i r = some w) : relocVal R f i r = some w := by
  unfold relocVal at hw ⊢
  split_ifs at hw ⊢
  · exact hw
  · exact hw
  · cases e : frun f (Elf.refOf i r.sym) with
    | none => simp [e] at hw
    | some ref =>
      simp only [e, Option.bind_eq_bind, obind_some] at hw ⊢
      exact bindVal_mono h hw
  · exact hw

theorem bind_mono {α β : Type} {x : Option α} {f f' : α → Option β}
    (hf : ∀ a b, f' a = some b → f a = some b) {b : β} (h : x.bind f' = some b) :
    x.bind f = some b := by
  cases x with
  | none => cases h
  | some a => exact hf a b h

theorem bind_mono' {α β : Type} {x x' : Option α} {f f' : α → Option β}
    (hx : ∀ a, x' = some a → x = some a) (hf : ∀ a b, f' a = some b → f a = some b) {b : β}
    (h : x'.bind f' = some b) : x.bind f = some b := by
  cases e : x' with
  | none => rw [e] at h; cases h
  | some a => rw [e] at h; rw [hx a e]; exact hf a b h

theorem slotsWith_mono {R R' : Resolver} (h : ∀ r p x, R' r p = some x → R r p = some x)
    {lazy : Bool} {f : Blob} {i : Elf.DynInfo} {D : List (Nat × Val)}
    (hD : slotsWith R' lazy f i = some D) : slotsWith R lazy f i = some D := by
  unfold slotsWith at hD ⊢
  refine bind_mono (fun aj D hD => ?_) hD
  obtain ⟨a, j⟩ := aj
  refine bind_mono' (mapM_mono (fun r x hx => ?_) a) (fun ra D hD => ?_) hD
  · cases e' : relocVal R' f i r with
    | none => simp [e'] at hx
    | some w => rw [e'] at hx; rw [relocVal_mono h e']; exact hx
  · refine bind_mono' (mapM_mono (fun r x hx => ?_) j) (fun _ _ h => h) hD
    split at hx
    · rename_i hl; simp only [hl, ite_true]; exact hx
    · rename_i hl
      simp only [hl]
      cases e' : relocVal R' f i r with
      | none => simp [e'] at hx
      | some w => rw [e'] at hx; rw [relocVal_mono h e']; exact hx

/-- **Cached binding certificate**: a slot table computed from correct lookup tables is the
loader's. -/
theorem slots_of_known {ks : List Known} (hk : ∀ k ∈ ks, k.Ok) {lazy : Bool} {f : Blob}
    {i : Elf.DynInfo} {D : List (Nat × Val)} (hD : slotsWith (resolveK (ks.map (·.facts))) lazy f i = some D) :
    slots (ks.map (·.file)) lazy f i = some D :=
  slotsWith_mono (fun _ _ _ hx => resolveK_sound hk hx) hD

/-- The head base of page-aligned bases is 16-byte aligned. -/
theorem PageBase.mod16 {b : Word} {bs : List Word} (h : PageBase (b :: bs)) : b.toNat % 16 = 0 := by
  have := h b (List.mem_cons_self ..)
  omega

end Silmaril.Elf.Link.Dyn
