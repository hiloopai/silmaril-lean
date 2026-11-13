module

public import Silmaril.Wasm.Jco.Styles.EncWrap.Thms
public import Silmaril.Wasm.Jco.Styles.Imports.Thms

/-!
# String encodings: when the canonical store is an exact copy

The canonical algorithms for `utf16` and `latin1+utf16` first allocate a worst-case block and
then shrink or grow it, which calls `realloc` with a nonzero old pointer. Through the emulated
`realloc` of a C allocator this is a second `alloc` and a copy, and the first block leaks.

* **`lowerStr_exact`**: for a string with `NoShrink enc s`, the canonical store through the
  emulated `realloc` **is** the exact-copy store `Meta.exactStr`. This holds for UTF-16 when the
  UTF-16 byte length is twice the UTF-8 length, and for Latin-1/UTF-16 when the string is ASCII.
* **`specCallE_exact`**: on such arguments the C convention with encoding `enc` is the exact-copy
  convention.

Nothing here says the two conventions differ elsewhere. They do whenever `alloc` is observable
(for example a bump allocator: the final allocator states differ), but that is not stated.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst) (md : Meta)

theorem shrinkTo_self (R : List Flat → RM M.St (List Flat)) (p : BitVec 32) (w : Nat) :
    shrinkTo M R p w w = pure p := by
  simp [shrinkTo]

theorem reallocCall_emu0 (al n : Nat) :
    reallocCall M (reallocEmuF M md.alloc) 0 0 al n =
      (M.call md.alloc [i32n n, i32n al] >>= fun r => RM.ofOption (single32? r)) := by
  simp [reallocCall, reallocEmuF, reallocEmu]

theorem latin1Bytes_length (s : String) : (latin1Bytes s s.length).length = s.length := by
  simp [latin1Bytes, ← String.length_toList]

theorem storeUtf16_exact {s : String} (h : (utf16Bytes s).length = 2 * (utf8 s).length) :
    storeUtf16 M (reallocEmuF M md.alloc) s =
      md.exactBytes M 2 (utf16Bytes s) ((utf16Bytes s).length / 2) := by
  unfold storeUtf16 Meta.exactBytes
  simp only [reallocCall_emu0, ← h, shrinkTo_self, RM.bind_assoc, RM.pure_bind]

theorem storeLatin1Utf16_exact {s : String} (h1 : latin1Prefix s = s.length)
    (h2 : s.length = (utf8 s).length) :
    storeLatin1Utf16 M (reallocEmuF M md.alloc) s =
      md.exactBytes M 2 (latin1Bytes s s.length) s.length := by
  unfold storeLatin1Utf16 Meta.exactBytes
  simp only [reallocCall_emu0, h1, ← h2, latin1Bytes_length, shrinkTo_self, RM.bind_assoc,
    RM.pure_bind, ↓reduceIte]

/-- **The canonical store is the exact copy** on strings that need no second allocation. -/
theorem lowerStr_exact (enc : StrEnc) {s : String} (h : NoShrink enc s = true) :
    lowerStr M (reallocEmuF M md.alloc) enc s = md.exactStr M enc s := by
  cases enc
  · exact lowerBytes_agree M md (reallocEmuF_zero M md) _ _
  · exact storeUtf16_exact M md (by simpa [NoShrink] using h)
  · have h' : latin1Prefix s = s.length ∧ s.length = (utf8 s).length := by
      simpa [NoShrink] using h
    show storeLatin1Utf16 M _ s = (if latin1Prefix s = s.length then _ else _)
    rw [ite_eq_left_iff.mpr (fun hn => absurd h'.1 hn)]
    exact storeLatin1Utf16_exact M md h'.1 h'.2

theorem lowerParamE_exact (enc : StrEnc) (t : PTy) (v : PVal)
    (h : ∀ s, v = .string s → NoShrink enc s = true) :
    lowerParamE M enc (reallocEmuF M md.alloc) t v = md.exactParam M enc t v := by
  cases t <;> cases v
  case string.string s => exact lowerStr_exact M md enc (h s rfl)
  all_goals
    unfold lowerParamE Meta.exactParam
    exact lowerParam_agree M md (reallocEmuF_zero M md) _ _

theorem lowerParamsE_exact (enc : StrEnc) : ∀ (ps : List PTy) (vs : List PVal),
    NoShrinkArgs enc vs →
      lowerParamsE M enc (reallocEmuF M md.alloc) ps vs = md.exactParams M enc ps vs
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | t :: ts, v :: vs, h => by
    have hv : ∀ s, v = .string s → NoShrink enc s = true := fun s hs =>
      h s (by rw [← hs]; exact List.mem_cons_self)
    have hvs : NoShrinkArgs enc vs := fun s hs => h s (List.mem_cons_of_mem _ hs)
    simp only [lowerParamsE, Meta.exactParams, lowerParamE_exact M md enc t v hv,
      lowerParamsE_exact enc ts vs hvs]

/-- **On arguments that need no second allocation, the C convention with encoding `enc` is the
exact-copy convention.** -/
theorem specCallE_exact (enc : StrEnc) (s : Sig) {vs : List PVal} (h : NoShrinkArgs enc vs) :
    md.specCallE M enc s vs = md.specCallExact M enc s vs := by
  unfold Meta.specCallE Meta.specCallExact
  rw [lowerParamsE_exact M md enc _ _ h]

end Silmaril.Wasm.Jco
