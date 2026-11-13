module

public import Silmaril.Wasm.Component.Wat.Defs

/-!
# Component WAT: atoms read back

Numbers, names and byte strings read back from their printing, `mapO` reads
back a mapped list, and the printed atoms are well formed.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Wat

open Sexp

/-! ## Numbers -/

theorem digitVal_digitChar' : ∀ d : Fin 10, digitVal? (digitChar d) = some d := by decide

theorem digitVal_digitChar {d : Nat} (h : d < 10) : digitVal? (digitChar d) = some d :=
  digitVal_digitChar' ⟨d, h⟩

theorem idChar_digitChar' : ∀ d : Fin 10, isIdChar (digitChar d) = true := by decide

theorem natChars_ne_nil (n : Nat) : natChars n ≠ [] := by
  rw [natChars]; split <;> simp

theorem foldl_natChars (n : Nat) : (natChars n).foldl digitStep (some 0) = some n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natChars]
    split
    · simp [digitStep, digitVal_digitChar ‹n < 10›]
    · rename_i h
      rw [List.foldl_append, ih (n / 10) (by omega)]
      simp only [List.foldl_cons, List.foldl_nil, digitStep, Option.bind_some,
        digitVal_digitChar (Nat.mod_lt n (by omega : 10 > 0)), Option.map_some]
      congr 1; omega

theorem parseNat_natChars (n : Nat) : parseNat (natChars n) = some n := by
  have h := natChars_ne_nil n
  cases hc : natChars n with
  | nil => exact absurd hc h
  | cons c cs => rw [parseNat, ← hc, foldl_natChars]

@[simp] theorem num?_num (n : Nat) : num? (num n) = some n := by
  simp [num?, num, String.toList_ofList, parseNat_natChars]

/-! ## Names and bytes -/

theorem fromUTF8_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  rw [String.toUTF8_eq_toByteArray, dite_eq_left_of_eq_true (eq_true s.isValidUTF8)]
  rfl

@[simp] theorem nm?_nm (s : String) : nm? (nm s) = some s := by
  simp only [nm?, nm]
  simpa using fromUTF8_toUTF8 s

@[simp] theorem bytes?_bytesS (b : ByteArray) : bytes? (bytesS b) = some b := by
  simp [bytes?, bytesS]

/-! ## Lists -/

theorem mapO_map {α β : Type} (f : Sexp → Option α) (g : β → Sexp) (h : β → α) :
    ∀ xs : List β, (∀ x ∈ xs, f (g x) = some (h x)) → mapO f (xs.map g) = some (xs.map h)
  | [], _ => rfl
  | x :: xs, hx => by
    simp only [List.map_cons, mapO, hx x (by simp), Option.bind_eq_bind, Option.bind_some,
      mapO_map f g h xs (fun y hy => hx y (by simp [hy])), Option.pure_def]

theorem mapO_map_id {α : Type} (f : Sexp → Option α) (g : α → Sexp)
    (xs : List α) (hx : ∀ x ∈ xs, f (g x) = some x) : mapO f (xs.map g) = some xs := by
  have := mapO_map f g id xs hx
  simpa using this

/-! ## Well-formed atoms -/

theorem atomOk_natChars (n : Nat) : AtomOk (String.ofList (natChars n)) := by
  refine ⟨by simpa [String.toList_ofList] using natChars_ne_nil n, ?_⟩
  rw [String.toList_ofList]
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natChars]
    have hd : ∀ d, d < 10 → isIdChar (digitChar d) = true := fun d h =>
      idChar_digitChar' ⟨d, h⟩
    split
    · simpa using hd n ‹_›
    · intro c hc
      rcases List.mem_append.1 hc with h | h
      · exact ih (n / 10) (by omega) c h
      · simp at h; subst h; exact hd _ (Nat.mod_lt _ (by omega))

@[simp] theorem wf_atom (a : String) : WF (.atom a) ↔ AtomOk a := by simp [WF]
@[simp] theorem wf_str (b : List UInt8) : WF (.str b) := by simp [WF]
@[simp] theorem wf_list (xs : List Sexp) : WF (.list xs) ↔ WFL xs := by simp [WF]
@[simp] theorem wfl_nil : WFL [] := by simp [WFL]
@[simp] theorem wfl_cons (x : Sexp) (xs : List Sexp) : WFL (x :: xs) ↔ WF x ∧ WFL xs := by
  simp [WFL]

@[simp] theorem wfl_append : ∀ (xs ys : List Sexp), WFL (xs ++ ys) ↔ WFL xs ∧ WFL ys
  | [], ys => by simp
  | x :: xs, ys => by simp [wfl_append xs ys, and_assoc]

@[simp] theorem wfl_map {α : Type} (f : α → Sexp) : ∀ xs : List α,
    WFL (xs.map f) ↔ ∀ x ∈ xs, WF (f x)
  | [] => by simp
  | x :: xs => by simp [wfl_map f xs]

@[simp] theorem wf_num (n : Nat) : WF (num n) := by
  simpa [num] using atomOk_natChars n

@[simp] theorem wf_nm (s : String) : WF (nm s) := by simp [nm]

@[simp] theorem wf_bytesS (b : ByteArray) : WF (bytesS b) := by simp [bytesS]

end Silmaril.Wasm.Component.Wat
