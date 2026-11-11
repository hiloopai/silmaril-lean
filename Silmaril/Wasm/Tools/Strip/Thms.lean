module

public import Silmaril.Wasm.Tools.Strip.Defs
public import Silmaril.Wasm.Tools.Framing.Thms

/-!
# `wasm-tools strip`: theorems

For a core module (`frame none b = .ok (.module, ss)`):

* **`strip_module`**: the output is the module preamble followed by the kept sections, in their
  input order, each with its contents unchanged and its size written minimally;
* **`strip_module_frames`**: the output splits back into exactly those sections;
* `strip_module_noncustom`: every non-custom section of the input is in the output, in order
  (only custom sections are removed);
* `Mode.removes_all`, `Mode.removes_dflt_name`: `--all` removes every custom section, the default
  keeps `name`.

New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Strip

open Silmaril.Wasm.Binary (Bytes)
open Silmaril.Wasm.Tools.Framing

/-- On a module's sections, `stripF` filters and canonicalises. -/
theorem stripF_module (rm : String → Bool) (fuel : Nat) :
    ∀ ss : List RawSec, stripF rm fuel .module ss = .ok ((ss.filter (keepSec rm)).map RawSec.canon)
  | [] => by rw [stripF]; rfl
  | s :: ss => by
    rw [stripF]
    have ih := stripF_module rm fuel ss
    by_cases hk : keepSec rm s = true
    · simp [ih, hk, nestedEnc]
    · simp [ih, hk]

/-- **Strip on a module**: the preamble, then the kept sections with minimal sizes. -/
theorem strip_module {rm : String → Bool} {b : Bytes} {ss : List RawSec}
    (h : frame none b = .ok (.module, ss)) :
    strip rm b = .ok (Enc.module.header ++ join ((ss.filter (keepSec rm)).map RawSec.canon)) := by
  unfold strip
  rw [h]
  simp only [bind, Except.bind, stripF_module, pure, Except.pure]

/-- Contents of framed sections are shorter than 4 GiB. -/
theorem frame_lengths {e : Option Enc} {b : Bytes} {e' : Enc} {ss : List RawSec}
    (h : frame e b = .ok (e', ss)) : ∀ s ∈ ss, s.content.length < 2 ^ 32 := by
  unfold frame at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · rename_i ss' hs
      obtain ⟨_, hok⟩ := splitSecs_sound hs
      split at h
      · cases h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact fun s hs => Silmaril.Wasm.Binary.UN.lt_two_pow (hok s hs)
    · cases h

/-- **The output frames back** to the kept sections (sizes minimal). -/
theorem strip_module_frames {rm : String → Bool} {b : Bytes} {ss : List RawSec}
    (h : frame none b = .ok (.module, ss)) {out : Bytes} (ho : strip rm b = .ok out) :
    out.take 8 = Enc.module.header ∧
      splitSecs (out.drop 8) = some ((ss.filter (keepSec rm)).map RawSec.canon) := by
  rw [strip_module h] at ho
  cases ho
  have hl : (Enc.module.header).length = 8 := rfl
  refine ⟨by simp [List.take_left' hl], ?_⟩
  rw [List.drop_left' hl]
  apply splitSecs_join
  apply canon_sizesOk
  intro s hs
  exact frame_lengths h s (List.mem_filter.mp hs).1

/-- **Only custom sections are removed**: the non-custom sections of the output are those of
the input, in order, with minimal sizes. -/
theorem strip_module_noncustom (rm : String → Bool) (ss : List RawSec) :
    ((ss.filter (keepSec rm)).map RawSec.canon).filter (·.id != 0) =
      (ss.filter (·.id != 0)).map RawSec.canon := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    by_cases h0 : s.id = 0
    · by_cases hk : keepSec rm s = true
      · simp_all [RawSec.canon]
      · simp_all
    · have hk : keepSec rm s = true := by simp [keepSec, h0]
      simp_all [RawSec.canon]

theorem Mode.removes_all (isMatch : String → String → Bool) (n : String) :
    Mode.all.removes isMatch n = true := rfl

theorem Mode.removes_dflt_name (isMatch : String → String → Bool) :
    Mode.dflt.removes isMatch "name" = false := by simp [Mode.removes]

end Silmaril.Wasm.Tools.Strip
