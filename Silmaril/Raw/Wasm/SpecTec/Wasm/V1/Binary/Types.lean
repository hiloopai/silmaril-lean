module

public import Silmaril.Wasm.Binary.Basic
public import Silmaril.Wasm.V1.Types

/-! # WebAssembly 1.0 binary format: types

Transcribed from the W3C Recommendation of 5 December 2019, section 5.3
(cited `REC 5.3.n`). Value types are exactly the four numeric types; block types
are `0x40` or a single value type; the only element type is the byte `0x70`
(`funcref`); limits are `u32`.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Binary

open Silmaril.Wasm.Binary

/-- `valtype` (REC 5.3.1). -/
inductive ValType : Bytes → V1.ValType → Prop where
  | i32 : ValType [0x7F] (.int .i32)
  | i64 : ValType [0x7E] (.int .i64)
  | f32 : ValType [0x7D] (.float .f32)
  | f64 : ValType [0x7C] (.float .f64)

/-- `blocktype ::= 0x40 ⇒ [] | t:valtype ⇒ [t]` (REC 5.3.2). -/
inductive BlockType : Bytes → V1.BlockType → Prop where
  | empty : BlockType [0x40] none
  | value {b : Bytes} {t : V1.ValType} (h : ValType b t) : BlockType b (some t)

/-- `functype ::= 0x60 t₁*:vec(valtype) t₂*:vec(valtype)` (REC 5.3.3). -/
inductive FuncType : Bytes → V1.FuncType → Prop where
  | mk {b₁ b₂ : Bytes} {ps rs : List V1.ValType} (h₁ : Vec ValType b₁ ps) (h₂ : Vec ValType b₂ rs) :
      FuncType ([0x60] ++ b₁ ++ b₂) ⟨ps, rs⟩

/-- `limits ::= 0x00 n:u32 | 0x01 n:u32 m:u32` (REC 5.3.4). -/
inductive Limits : Bytes → V1.Limits → Prop where
  | min {b : Bytes} {n : Fin (2 ^ 32)} (h : U32 b n.val) : Limits ([0x00] ++ b) ⟨n, none⟩
  | minMax {b b' : Bytes} {n m : Fin (2 ^ 32)} (h : U32 b n.val) (h' : U32 b' m.val) :
      Limits ([0x01] ++ b ++ b') ⟨n, some m⟩

/-- `memtype ::= lim:limits` (REC 5.3.5). -/
inductive MemType : Bytes → V1.MemoryType → Prop where
  | mk {b : Bytes} {l : V1.Limits} (h : Limits b l) : MemType b ⟨l⟩

/-- `tabletype ::= et:elemtype lim:limits`, `elemtype ::= 0x70 ⇒ funcref` (REC 5.3.6). -/
inductive TableType : Bytes → V1.TableType → Prop where
  | mk {b : Bytes} {l : V1.Limits} (h : Limits b l) : TableType ([0x70] ++ b) ⟨l⟩

/-- `mut ::= 0x00 ⇒ const | 0x01 ⇒ var` (REC 5.3.7). -/
inductive Mut : Bytes → Mutability → Prop where
  | const : Mut [0x00] .const
  | var : Mut [0x01] .var

/-- `globaltype ::= t:valtype m:mut` (REC 5.3.7). -/
inductive GlobalType : Bytes → V1.GlobalType → Prop where
  | mk {b b' : Bytes} {t : V1.ValType} {m : Mutability} (ht : ValType b t) (hm : Mut b' m) :
      GlobalType (b ++ b') ⟨m, t⟩

/-- Sequencing of two prefix-free productions is prefix-free. -/
theorem PrefixFree.append {α β : Type} {G₁ : Bytes → α → Prop} {G₂ : Bytes → β → Prop}
    (h₁ : PrefixFree G₁) (h₂ : PrefixFree G₂) {b₁ b₂ b₁' b₂' r r' : Bytes} {a₁ a₁' : α}
    {a₂ a₂' : β} (g₁ : G₁ b₁ a₁) (g₂ : G₂ b₂ a₂) (g₁' : G₁ b₁' a₁') (g₂' : G₂ b₂' a₂')
    (h : b₁ ++ (b₂ ++ r) = b₁' ++ (b₂' ++ r')) : b₁ = b₁' ∧ a₁ = a₁' ∧ b₂ = b₂' ∧ a₂ = a₂' := by
  obtain ⟨rfl, rfl⟩ := h₁ g₁ g₁' h
  obtain ⟨rfl, rfl⟩ := h₂ g₂ g₂' (List.append_cancel_left h)
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ValType.prefixFree : PrefixFree ValType := by
  intro _ _ r r' _ _ h h' e
  cases h <;> cases h' <;> simp_all

theorem BlockType.prefixFree : PrefixFree BlockType := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | empty => cases h' with
    | empty => exact ⟨rfl, rfl⟩
    | value hv => cases hv <;> simp at e
  | value hv => cases h' with
    | empty => cases hv <;> simp at e
    | value hv' =>
      obtain ⟨rfl, rfl⟩ := ValType.prefixFree hv hv' e
      exact ⟨rfl, rfl⟩

theorem FuncType.prefixFree : PrefixFree FuncType := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | mk h₁ h₂ => cases h' with
    | mk h₁' h₂' =>
      simp only [List.append_assoc, List.cons_append, List.cons.injEq, true_and] at e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := PrefixFree.append (Vec.prefixFree ValType.prefixFree)
        (Vec.prefixFree ValType.prefixFree) h₁ h₂ h₁' h₂' e
      exact ⟨rfl, rfl⟩

theorem Limits.prefixFree : PrefixFree Limits := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | min h => cases h' with
    | min h' =>
      simp only [List.append_assoc, List.cons_append, List.cons.injEq, true_and] at e
      obtain ⟨rfl, hv⟩ := UN.prefixFree 32 h h' e
      exact ⟨rfl, by rw [Fin.ext hv]⟩
    | minMax _ _ => simp at e
  | minMax h₁ h₂ => cases h' with
    | min _ => simp at e
    | minMax h₁' h₂' =>
      simp only [List.append_assoc, List.cons_append, List.cons.injEq, true_and] at e
      obtain ⟨rfl, hv, rfl, hv'⟩ := PrefixFree.append (UN.prefixFree 32) (UN.prefixFree 32)
        h₁ h₂ h₁' h₂' e
      exact ⟨rfl, by rw [Fin.ext hv, Fin.ext hv']⟩

theorem TableType.prefixFree : PrefixFree TableType := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | mk h => cases h' with
    | mk h' =>
      simp only [List.append_assoc, List.cons_append, List.cons.injEq, true_and] at e
      obtain ⟨rfl, rfl⟩ := Limits.prefixFree h h' e
      exact ⟨rfl, rfl⟩

theorem Mut.prefixFree : PrefixFree Mut := by
  intro _ _ r r' _ _ h h' e
  cases h <;> cases h' <;> simp_all

theorem GlobalType.prefixFree : PrefixFree GlobalType := by
  intro _ _ r r' _ _ h h' e
  cases h with
  | mk ht hm => cases h' with
    | mk ht' hm' =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        PrefixFree.append ValType.prefixFree Mut.prefixFree ht hm ht' hm'
        (by simpa only [List.append_assoc] using e)
      exact ⟨rfl, rfl⟩

end Silmaril.Wasm.V1.Binary
