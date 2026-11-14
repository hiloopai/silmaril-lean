module

public import Silmaril.Net.Http1.Fields.Defs
public import Silmaril.Net.Http1.Message.Thms

/-! Proofs for `Silmaril.Net.Http1.Fields.Thms`. -/

@[expose] public section

namespace Silmaril.Net.Http1.Proofs.Fields

open Silmaril.Net.Http1
open Silmaril.Parse.ByteParse (Bytes)

theorem tchar_not_ws : ∀ b : UInt8, isTchar b = true → isWS b = false := by decide
theorem tchar_not_comma : ∀ b : UInt8, isTchar b = true → b ≠ COMMA := by decide

theorem splitOn_of_not_mem {sep : UInt8} : ∀ {l : Bytes}, (∀ b ∈ l, b ≠ sep) → splitOn sep l = [l]
  | [], _ => rfl
  | c :: cs, h => by
    have hc : c ≠ sep := h c (by simp)
    have ih := splitOn_of_not_mem (l := cs) (fun b hb => h b (by simp [hb]))
    simp [splitOn, hc, ih]

theorem listElements_token {l : Bytes} (h : IsToken l) : listElements l = [l] := by
  have e₁ : l.dropWhile isWS = l :=
    dropWhile_of_head fun b hb => tchar_not_ws b (h.2 b (List.mem_of_mem_head? hb))
  have e₂ : l.reverse.dropWhile isWS = l.reverse := by
    apply dropWhile_of_head
    rw [List.head?_reverse]
    exact fun b hb => tchar_not_ws b (h.2 b (List.mem_of_mem_getLast? hb))
  unfold listElements
  rw [splitOn_of_not_mem (fun b hb => tchar_not_comma b (h.2 b hb))]
  simp [trimOWS, e₁, e₂, h.1]

end Silmaril.Net.Http1.Proofs.Fields
