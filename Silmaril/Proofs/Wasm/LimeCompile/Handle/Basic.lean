module

public import Silmaril.Wasm.LimeCompile.Handle.Defs

/-!
# Handle translation of export APIs: proofs

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.Handle

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.LimeCompile.Preserve (ApiTy limeVal ApiLime)
open Silmaril.Wasm.LimeCompile.Handle

theorem handleVal_lime {t t' : ValType} (h : handleVal t = some t') : limeVal t' = true := by
  unfold handleVal at h
  split at h
  · cases h
    assumption
  · split at h
    · cases h
      rfl
    · cases h

theorem handleVal_of_lime {t : ValType} (h : limeVal t = true) : handleVal t = some t := by
  simp [handleVal, h]

theorem mapM_lime : ∀ {l l' : List ValType}, l.mapM handleVal = some l' → l'.all limeVal = true
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | t :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨l'', hl, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨handleVal_lime ht, mapM_lime hl⟩

theorem mapM_of_lime : ∀ {l : List ValType}, l.all limeVal = true → l.mapM handleVal = some l
  | [], _ => rfl
  | t :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.mapM_cons, handleVal_of_lime h.1, mapM_of_lime h.2, Option.bind_eq_bind,
      Option.pure_def, Option.bind_some]

theorem handleTy_lime {t t' : ApiTy} (h : handleTy t = some t') : t'.lime = true := by
  unfold handleTy at h
  split at h
  · split at h
    · rename_i ps rs hps hrs
      cases h
      simp only [ApiTy.lime, Bool.and_eq_true]
      exact ⟨mapM_lime hps, mapM_lime hrs⟩
    · cases h
  · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
    exact handleVal_lime hv
  · split at h
    · cases h
      assumption
    · cases h

theorem handleTy_of_lime {t : ApiTy} (h : t.lime = true) : handleTy t = some t := by
  unfold handleTy
  split
  · rename_i ft
    simp only [ApiTy.lime, Bool.and_eq_true] at h
    rw [mapM_of_lime h.1, mapM_of_lime h.2]
  · rename_i g
    rw [handleVal_of_lime h]
    rfl
  · simp [h]

theorem mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ b ∈ l', ∃ a ∈ l, f a = some b
  | [], l', h, b, hb => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    cases hb
  | a :: l, l', h, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨b', hb', h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨l'', hl, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hb'⟩
    · obtain ⟨a', ha', hfa⟩ := mem_of_mapM hl b hb
      exact ⟨a', List.mem_cons_of_mem a ha', hfa⟩

theorem length_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨b', -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨l'', hl, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    simp only [List.length_cons, length_of_mapM hl]

theorem handleEntry_lime {q p : String × Option ApiTy} (h : handleEntry q = some p) :
    ∀ t, p.2 = some t → t.lime = true := by
  intro t ht
  obtain ⟨n, o⟩ := q
  cases o with
  | none =>
    cases h
    cases ht
  | some u =>
    obtain ⟨u', hu, rfl⟩ := Option.map_eq_some_iff.mp h
    cases ht
    exact handleTy_lime hu

theorem handleApi_lime {A A' : List (String × Option ApiTy)} (h : handleApi A = some A') :
    ApiLime A' := by
  intro p hp t ht
  obtain ⟨q, -, hq⟩ := mem_of_mapM h p hp
  exact handleEntry_lime hq t ht

theorem handleEntry_of_lime {p : String × Option ApiTy} (h : ∀ t, p.2 = some t → t.lime = true) :
    handleEntry p = some p := by
  obtain ⟨n, o⟩ := p
  cases o with
  | none => rfl
  | some u =>
    show (handleTy u).map (fun t' => (n, some t')) = some (n, some u)
    rw [handleTy_of_lime (h u rfl)]
    rfl

theorem handleApi_of_apiLime : ∀ {A : List (String × Option ApiTy)}, ApiLime A →
    handleApi A = some A
  | [], _ => rfl
  | p :: A, h => by
    have hp := handleEntry_of_lime (h p List.mem_cons_self)
    have hA : handleApi A = some A :=
      handleApi_of_apiLime fun q hq => h q (List.mem_cons_of_mem p hq)
    unfold handleApi at hA ⊢
    simp only [List.mapM_cons, hp, hA, Option.bind_eq_bind, Option.pure_def, Option.bind_some]

end Silmaril.Proofs.Wasm.LimeCompile.Handle
