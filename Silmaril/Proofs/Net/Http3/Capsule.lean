module

public import Silmaril.Net.Http3.Capsule.Defs
import Silmaril.Net.Quic.VarInt.Thms

/-!
# The HTTP Capsule Protocol: proofs

For `Silmaril.Net.Http3.Capsule.Thms` (RFC 9297 §3.2, §3.3).
-/

@[expose] public section

namespace Silmaril.Proofs.Net.Http3.Capsule

open Silmaril.Net.Quic Silmaril.Net.Http3

theorem read_encode {m : Nat} {c : Capsule} (hc : c.Valid) (hm : c.value.length ≤ m)
    (rest : List UInt8) : Capsule.read m (c.encode ++ rest) = .ok (c, rest) := by
  obtain ⟨ht, hl⟩ := hc
  have e : c.encode ++ rest =
      VarInt.encode c.type ++ (VarInt.encode c.value.length ++ (c.value ++ rest)) := by
    simp [Capsule.encode, List.append_assoc]
  rw [e]
  simp only [Capsule.read, VarInt.decode_encode ht, VarInt.decode_encode hl,
    show ¬ m < c.value.length by omega, List.length_append,
    show ¬ c.value.length + rest.length < c.value.length by omega, ↓reduceIte,
    List.take_left' rfl, List.drop_left' rfl]

/-- What a successful read consumed: a type, a length and that many bytes. -/
theorem read_ok {m : Nat} {xs : List UInt8} {c : Capsule} {rest : List UInt8}
    (h : Capsule.read m xs = .ok (c, rest)) :
    c.value.length ≤ m ∧ rest.length < xs.length ∧ c.Valid := by
  unfold Capsule.read at h
  split at h
  · cases h
  · rename_i ty r1 h1
    split at h
    · cases h
    · rename_i len r2 h2
      split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have l1 := VarInt.decode_length h1
          have l2 := VarInt.decode_length h2
          refine ⟨by simp; omega, by simp; omega, VarInt.decode_valid h1, ?_⟩
          have := VarInt.decode_valid h2
          unfold VarInt.Valid at this ⊢
          simp only [List.length_take]; omega

theorem read_local {m : Nat} {xs : List UInt8} {c : Capsule} {rest : List UInt8}
    (tail : List UInt8) (h : Capsule.read m xs = .ok (c, rest)) :
    Capsule.read m (xs ++ tail) = .ok (c, rest ++ tail) := by
  unfold Capsule.read at h ⊢
  split at h
  · cases h
  · rename_i ty r1 h1
    rw [VarInt.decode_local tail h1]
    split at h
    · cases h
    · rename_i len r2 h2
      simp only [VarInt.decode_local tail h2]
      split at h
      · cases h
      · rename_i hm
        split at h
        · cases h
        · rename_i hl
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [hm, ↓reduceIte, List.length_append,
            show ¬ r2.length + tail.length < len by omega, Except.ok.injEq, Prod.mk.injEq,
            List.drop_append_of_le_length (show len ≤ r2.length by omega), and_true]
          simp [List.take_append_of_le_length (show len ≤ r2.length by omega)]

theorem readAllFuel_encodeAll {m : Nat} (cs : List Capsule) (hv : ∀ c ∈ cs, c.Valid)
    (hm : ∀ c ∈ cs, c.value.length ≤ m) :
    ∀ fuel, (Capsule.encodeAll cs).length ≤ fuel →
      Capsule.readAllFuel m fuel (Capsule.encodeAll cs) = .ok cs := by
  induction cs with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons c cs ih =>
    intro fuel hf
    have hd := read_encode (hv c (by simp)) (hm c (by simp)) (Capsule.encodeAll cs)
    have hne : c.encode ≠ [] := by simp [Capsule.encode, VarInt.encode_ne_nil]
    obtain ⟨b, tl, hbt⟩ := List.exists_cons_of_ne_nil hne
    have he : Capsule.encodeAll (c :: cs) = b :: (tl ++ Capsule.encodeAll cs) := by
      simp [Capsule.encodeAll, hbt]
    rw [hbt, List.cons_append] at hd
    rw [he] at hf ⊢
    simp only [List.length_cons, List.length_append] at hf
    match fuel with
    | 0 => omega
    | fuel + 1 =>
      rw [Capsule.readAllFuel, hd]
      simp only [ih (fun w hw => hv w (by simp [hw])) (fun w hw => hm w (by simp [hw])) fuel
        (by omega)]

theorem readAll_encodeAll {m : Nat} (cs : List Capsule) (hv : ∀ c ∈ cs, c.Valid)
    (hm : ∀ c ∈ cs, c.value.length ≤ m) :
    Capsule.readAll m (Capsule.encodeAll cs) = .ok cs :=
  readAllFuel_encodeAll cs hv hm _ (Nat.le_refl _)

theorem known_insert_unknown (isKnown : Nat → Bool) (xs ys : List Capsule) (c : Capsule)
    (hc : isKnown c.type = false) :
    Capsule.known isKnown (xs ++ c :: ys) = Capsule.known isKnown (xs ++ ys) := by
  simp [Capsule.known, List.filter_append, hc]

theorem datagrams_append (xs ys : List Capsule) :
    Capsule.datagrams (xs ++ ys) = Capsule.datagrams xs ++ Capsule.datagrams ys := by
  simp [Capsule.datagrams, List.filterMap_append]

theorem datagrams_map_datagram (ps : List (List UInt8)) :
    Capsule.datagrams (ps.map Capsule.datagram) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, Capsule.datagrams, List.filterMap_cons, Capsule.datagram,
      ↓reduceIte] at ih ⊢
    rw [ih]

end Silmaril.Proofs.Net.Http3.Capsule
