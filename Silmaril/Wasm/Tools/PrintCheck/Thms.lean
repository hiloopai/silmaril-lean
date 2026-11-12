module

public import Silmaril.Wasm.Tools.PrintCheck.Defs
public import Silmaril.Wasm.Tools.Text.Thms

/-!
# The fast paths are equal to the specification functions

* `parMapM_eq`: the chunked parallel map is `List.mapM`;
* `mapCertified_val`: silmaril-lean's `mapCertified` without certificates is `List.mapM`;
* `moduleFast?_eq`: `moduleFast? k x = (Wat.Source.module? x).map Subtype.val`;
* `checkFast_eq`, `printModuleFast_eq`, `binaryToWatWithFast_eq`: `print`'s check, printer and
  core are the specification ones;
* `parseSupportedFast?_eq`, `textToBinaryFast_eq`, `watToBinaryFast_eq`, `watToWatFast_eq`:
  likewise for `parse`;
* `binaryToWatWithFast_sound`, `watToBinaryFast_sound`: the specification theorems of
  `Silmaril.Wasm.Tools.Text.Thms`, transported.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.PrintCheck

open Silmaril Silmaril.Wasm Silmaril.Wasm.Text Silmaril.Wasm.Text.Core
open Silmaril.Wasm.Binaryen.Toolkit.Wat.Source
open Silmaril.Wasm.Tools.Annot (stripTrivia)

theorem flatten_chunksF {α : Type} (k : Nat) : ∀ (f : Nat) (xs : List α),
    (chunksF k f xs).flatten = xs
  | 0, xs => by simp [chunksF]
  | _ + 1, [] => by simp [chunksF]
  | f + 1, x :: xs => by
    simp only [chunksF, List.flatten_cons, flatten_chunksF k f]
    exact List.take_append_drop k (x :: xs)

theorem mapM_flatten {α β : Type} (f : α → Option β) : ∀ cs : List (List α),
    (cs.mapM (fun c : List α => c.mapM f)).map List.flatten = cs.flatten.mapM f
  | [] => by simp
  | c :: cs => by
    rw [List.flatten_cons, List.mapM_append, ← mapM_flatten f cs, List.mapM_cons]
    cases c.mapM f <;> cases cs.mapM (fun c : List α => c.mapM f) <;> simp

theorem parMapM_eq {α β : Type} (k : Nat) (f : α → Option β) (xs : List α) :
    parMapM k f xs = xs.mapM f := by
  have hget : (Task.get ∘ fun c : List α => Task.spawn fun _ => c.mapM f) =
      (fun c : List α => c.mapM f) := rfl
  simp only [parMapM]
  rw [List.mapM_map, hget, mapM_flatten, flatten_chunksF]

theorem mapCertified_val {α β : Type} {R : α → β → Prop}
    (f : (a : α) → Option {b : β // R a b}) : ∀ as : List α,
    (mapCertified f as).map Subtype.val = as.mapM (fun a => (f a).map Subtype.val)
  | [] => rfl
  | a :: as => by
    rw [List.mapM_cons, ← mapCertified_val f as]
    simp only [mapCertified]
    cases f a <;> cases mapCertified f as <;> rfl

theorem moduleFast?_eq (k : Nat) (x : SExp) :
    moduleFast? k x = (module? x).map Subtype.val := by
  simp only [moduleFast?, module?, parMapM_eq, ← mapCertified_val, Option.bind_eq_bind, Option.map_bind,
    Option.bind_map, Function.comp_def, apply_dite (Option.map Subtype.val), Option.map_some,
    Option.map_none, dite_eq_ite]

theorem readBackFast_eq (k : Nat) (s : String) : readBackFast k s = Print.readBack s := by
  unfold readBackFast Print.readBack
  cases Formats.SExpEncoding.Wat.sexpWatFullExec? .core3 s with
  | none => rfl
  | some x =>
    simp only [moduleFast?_eq]
    cases module? x <;> rfl

theorem checkFast_eq (k : Nat) (m : Wasm.Module) (t : String) :
    checkFast k m t = Print.check m t := by
  simp only [checkFast, Print.check, readBackFast_eq]
  rfl

theorem printModuleFast_eq (k : Nat) (cfg : Print.Config) (b : ByteArray) :
    printModuleFast k cfg b = Print.printModule cfg b := by
  simp only [printModuleFast, Print.printModule, checkFast_eq]

theorem binaryToWatWithFast_eq (k : Nat) (cfg : Print.Config) (b : ByteArray) :
    binaryToWatWithFast k cfg b = Text.binaryToWatWith cfg b := by
  simp only [binaryToWatWithFast, Text.binaryToWatWith, printModuleFast_eq, checkFast_eq]
  rfl

theorem parseSupportedFast?_eq (k : Nat) (x : SExp) :
    parseSupportedFast? k x = Binaryen.Toolkit.Wat.parseSupported? x := by
  simp only [parseSupportedFast?, Binaryen.Toolkit.Wat.parseSupported?, moduleFast?_eq]
  rfl

theorem textTreeFast?_eq (k : Nat) (s : String) : textTreeFast? k s = Text.textTree? s := by
  simp only [textTreeFast?, Text.textTree?, parseSupportedFast?_eq]
  rfl

theorem textToBinaryFast_eq (k : Nat) (s : String) :
    textToBinaryFast k s = Text.textToBinary s := by
  simp only [textToBinaryFast, Text.textToBinary, textTreeFast?_eq]
  rfl

theorem watToBinaryFast_eq (k : Nat) (i : ByteArray) :
    watToBinaryFast k i = Text.watToBinary i := by
  simp only [watToBinaryFast, Text.watToBinary, textToBinaryFast_eq]
  rfl

theorem watToWatFast_eq (k : Nat) (i : ByteArray) : watToWatFast k i = Text.watToWat i := by
  simp only [watToWatFast, Text.watToWat, Text.binaryToWat, watToBinaryFast_eq,
    binaryToWatWithFast_eq]

/-- `print`'s fast core meets `print`'s specification (`Text.binaryToWatWith_sound`). -/
theorem binaryToWatWithFast_sound {k : Nat} {cfg : Print.Config} {i : ByteArray} {t : String}
    (h : binaryToWatWithFast k cfg i = .ok t) :
    ∃ m, Binary.Core.Encodes i.data.toList m ∧ Text.Core.Encodes (stripTrivia t) m :=
  Text.binaryToWatWith_sound (by rwa [binaryToWatWithFast_eq] at h)

/-- `parse`'s fast core meets `parse`'s specification (`Text.watToBinary_sound`). -/
theorem watToBinaryFast_sound {k : Nat} {i b : ByteArray} (h : watToBinaryFast k i = .ok b) :
    ∃ m, Binary.Core.Encodes b.data.toList m ∧
      ((Text.isBinary i = true ∧ b = i) ∨
        (Text.isBinary i = false ∧ ∃ s, String.fromUTF8? i = some s ∧
          Text.Core.Encodes (stripTrivia s) m)) :=
  Text.watToBinary_sound (by rwa [watToBinaryFast_eq] at h)

/-- The coloured output with its escapes removed is the certified text, or it is the
certified text itself. -/
theorem colorText_spec (cfg : Print.Config) (b : ByteArray) (plain : String) :
    stripAnsi (colorText cfg b plain) = plain ∨ colorText cfg b plain = plain := by
  unfold colorText
  split
  · split
    · rename_i h; exact .inl (by simpa using h)
    · exact .inr rfl
  · exact .inr rfl

end Silmaril.Wasm.Tools.PrintCheck
