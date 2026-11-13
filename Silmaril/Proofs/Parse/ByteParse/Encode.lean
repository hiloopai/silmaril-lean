module

public import Silmaril.Proofs.Parse.ByteParse.AtEnd
public import Silmaril.Wasm.Binaryen.Exe.EncodeBaseSound

/-!
# Encoder laws

Each encoder of `Silmaril.Parse.ByteParse.Enc` produces bytes its grammar accepts.
With completeness this is the round trip `parse (enc a ++ rest) = ok a`.
LEB128 laws reuse silmaril's `encU_sound`/`encS_sound`.
-/

@[expose] public section

namespace Silmaril.Parse.ByteParse

open Silmaril.Wasm.Binary (Seq Vec UN SN U32)

variable {α : Type}

namespace Enc

theorem u32_G {n : Nat} {l : Bytes} (h : u32 n = some l) : UN 32 l n := by
  unfold u32 at h
  split at h
  · cases h; exact Silmaril.Wasm.Binaryen.Exe.encU_sound ‹_›
  · cases h

theorem u32_lt {n : Nat} {l : Bytes} (h : u32 n = some l) : n < 2 ^ 32 := by
  unfold u32 at h
  split at h
  · assumption
  · cases h

theorem sN_G {N : Nat} {i : Int} {l : Bytes} (h : sN N i = some l) : SN N l i := by
  unfold sN at h
  split at h
  · next hc => cases h; exact Silmaril.Wasm.Binaryen.Exe.encS_sound hc.2.1 hc.2.2 hc.1
  · cases h

theorem u32_ne_nil {n : Nat} {l : Bytes} (h : u32 n = some l) : l ≠ [] := by
  have := u32_G h
  intro e; subst e; exact UN.ne_nil this

theorem name_G {s : String} {l : Bytes} (h : name s = some l) : Grammar.name.G l s := by
  simp only [name, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨nb, hn, rfl⟩ := h
  exact Grammar.name_G s (u32_G hn)

theorem list_G {G : Bytes → α → Prop} {f : α → Option Bytes}
    (hf : ∀ x l, f x = some l → G l x) : ∀ {xs : List α} {l : Bytes}, list f xs = some l → Seq G l xs
  | [], l, h => by cases h; exact Seq.nil
  | x :: xs, l, h => by
    simp only [Enc.list, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact Seq.cons (hf x b hb) (list_G hf hbs)

theorem list_G_mem {G : Bytes → α → Prop} {f : α → Option Bytes} :
    ∀ {xs : List α} {l : Bytes}, (∀ x ∈ xs, ∀ l, f x = some l → G l x) → list f xs = some l → Seq G l xs
  | [], l, _, h => by cases h; exact Seq.nil
  | x :: xs, l, hf, h => by
    simp only [Enc.list, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact Seq.cons (hf x (by simp) b hb)
      (list_G_mem (fun y hy => hf y (List.mem_cons_of_mem _ hy)) hbs)

/-- Each element's encoding is no longer than the whole list's. -/
theorem list_length_le {f : α → Option Bytes} :
    ∀ {xs : List α} {l : Bytes}, list f xs = some l →
      ∀ x ∈ xs, ∃ b, f x = some b ∧ b.length ≤ l.length
  | [], _, _, x, hx => by simp at hx
  | y :: xs, l, h, x, hx => by
    simp only [Enc.list, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, hb, by simp⟩
    · obtain ⟨c, hc, hl⟩ := list_length_le hbs x hx
      exact ⟨c, hc, by simp; omega⟩

theorem vec_parts {f : α → Option Bytes} {xs : List α} {l : Bytes} (h : vec f xs = some l) :
    ∃ nb b, l = nb ++ b ∧ U32 nb xs.length ∧ list f xs = some b ∧ nb ≠ [] := by
  simp only [vec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨nb, hn, b, hb, rfl⟩ := h
  exact ⟨nb, b, rfl, u32_G hn, hb, u32_ne_nil hn⟩

theorem vec_G {g : Grammar α} {hne : NonEmpty g.G} {f : α → Option Bytes}
    {xs : List α} {l : Bytes} (hf : ∀ x ∈ xs, ∀ l, f x = some l → g.G l x)
    (h : vec f xs = some l) : (Grammar.vec g hne).G l xs := by
  obtain ⟨nb, b, rfl, hn, hb, -⟩ := vec_parts h
  exact Vec.mk hn (list_G_mem hf hb)

theorem sized_parts {b l : Bytes} (h : sized b = some l) :
    ∃ nb, l = nb ++ b ∧ U32 nb b.length := by
  simp only [sized, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨nb, hn, rfl⟩ := h
  exact ⟨nb, rfl, u32_G hn⟩

theorem opt_G {G : Bytes → α → Prop} {f : α → Option Bytes} (hf : ∀ x l, f x = some l → G l x) :
    ∀ {o : Option α} {l : Bytes}, opt f o = some l → Spec.opt G l o
  | none, l, h => by cases h; rfl
  | some a, l, h => by
    simp only [opt, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨b, rfl, hf a b hb⟩

theorem le_G (n v : Nat) (hv : v < 2 ^ (8 * n)) : Spec.le n (le n v) v := by
  induction n generalizing v with
  | zero => simp at hv; subst hv; exact ⟨rfl, rfl⟩
  | succ n ih =>
    have h1 : v / 256 < 2 ^ (8 * n) := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      calc v < 2 ^ (8 * (n + 1)) := hv
        _ = 2 ^ (8 * n) * 256 := by rw [Nat.mul_succ, pow_add]; norm_num
    obtain ⟨hl, hv'⟩ := ih (v / 256) h1
    refine ⟨by simp [le, hl], ?_⟩
    simp only [le, Silmaril.Wasm.Binary.littleEndian, ← hv']
    rw [UInt8.toNat_ofNat_of_lt' (show v % 256 < 256 by omega)]
    omega

end Enc

end Silmaril.Parse.ByteParse
