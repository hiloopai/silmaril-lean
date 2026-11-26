module

public import Silmaril.Semantics.SQLite.Isolation.Cancel.Defs

public section

namespace Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel

open Silmaril.Semantics.SQLite.Isolation.Cancel

theorem decode_encode {i : Instr} (h : i.Supported) : decode (encode i) = i := by
  cases i with
  | halt => rfl
  | work => rfl
  | jump t =>
    have h1 : (8 * t + 2) % 8 = 2 := by omega
    have h2 : (8 * t + 2) / 8 = t := by omega
    simp [encode, decode, h1, h2]
  | branch t =>
    have h1 : (8 * t + 3) % 8 = 3 := by omega
    have h2 : (8 * t + 3) / 8 = t := by omega
    simp [encode, decode, h1, h2]
  | helper n =>
    have h1 : (8 * n + 4) % 8 = 4 := by omega
    have h2 : (8 * n + 4) / 8 = n := by omega
    simp [encode, decode, h1, h2]
  | call => rfl
  | poll => rfl
  | unsupported _ => exact h.elim
  | malformed _ => exact h.elim

theorem compileAt_supported : ∀ (w : Work) (base : Nat), ∀ i ∈ compileAt w base, i.Supported
  | .tick, _, i, h | .call, _, i, h | .helper _, _, i, h | .halt, _, i, h => by
    simp [compileAt] at h; subst h; trivial
  | .seq a b, base, i, h => by
    simp only [compileAt, List.mem_append] at h
    rcases h with h | h
    · exact compileAt_supported a _ i h
    · exact compileAt_supported b _ i h
  | .forever body, base, i, h => by
    simp only [compileAt, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact compileAt_supported body _ i h
    · trivial

theorem map_decode_encode :
    ∀ l : List Instr, (∀ i ∈ l, i.Supported) → (l.map encode).map decode = l
  | [], _ => rfl
  | i :: l, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨decode_encode (h i (by simp)),
      map_decode_encode l (fun j hj => h j (by simp [hj]))⟩

theorem compile_decode (w : Work) : (compile w).map decode = compileAt w 0 ++ [.halt] := by
  apply map_decode_encode
  intro i hi
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · exact compileAt_supported w 0 i hi
  · trivial

end Silmaril.Proofs.Semantics.SQLite.Isolation.Cancel
