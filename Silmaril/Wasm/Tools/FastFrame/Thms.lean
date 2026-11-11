module

public import Silmaril.Wasm.Tools.FastFrame.Defs
public import Silmaril.Wasm.Tools.Framing.Thms
import Silmaril.Proofs.Wasm.Tools.FastFrame

/-!
# Framing on `ByteArray` windows equals framing on lists

Each fast function of `FastFrame.Defs` computes its specification function of
`Silmaril.Wasm.Tools.Framing` on the window `win b i e` (a list), for windows inside the array:

* `readUN_win`: `readUN N (win b i e)` is `readUNAt b e N i` with the consumed bytes and the
  rest as windows;
* `splitSecsF_win`: `splitSecsF` of a window is `splitAt` mapped through `View.raw`;
* `customName_win`, `secCount_win`, `checkSecs_win`, `readHeader_win`;
* **`frame_win`**: `frame expect (win b i e)` is `frameAt b expect i e` mapped through
  `View.raw`; with `i = 0` and `e = b.size` the window is the whole input (`win_all`).

The proofs are in `Silmaril.Proofs.Wasm.Tools.FastFrame`; this header restates them, with the
window lemmas (`win_*`, `readUNAt_bounds`, `splitAt_ok`) the other fast paths use.

New theorems.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.FastFrame

open Silmaril.Wasm.Binary (Bytes)
open Silmaril.Wasm.Tools.Framing

theorem length_data_toList (b : ByteArray) : b.data.toList.length = b.size :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.length_data_toList b

theorem win_all (b : ByteArray) : win b 0 b.size = b.data.toList :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.win_all b

theorem win_cons {b : ByteArray} {i e : Nat} (hi : i < e) (he : e ≤ b.size) :
    win b i e = b[i]'(by omega) :: win b (i + 1) e :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.win_cons hi he

theorem win_nil {b : ByteArray} {i e : Nat} (h : e ≤ i) : win b i e = [] :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.win_nil h

theorem win_length {b : ByteArray} {i e : Nat} (he : e ≤ b.size) : (win b i e).length = e - i :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.win_length he

theorem win_take (b : ByteArray) (i e k : Nat) : (win b i e).take k = win b i (min (i + k) e) :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.win_take b i e k

theorem win_drop (b : ByteArray) (i e k : Nat) : (win b i e).drop k = win b (i + k) e :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.win_drop b i e k

theorem winC_eq (b : ByteArray) (i e : Nat) : winC b i e = win b i e :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.winC_eq b i e

theorem readUNAt_bounds {b : ByteArray} {e : Nat} (N i : Nat) {v j : Nat}
    (h : readUNAt b e N i = some (v, j)) : i < j ∧ j ≤ e :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.readUNAt_bounds N i h

theorem readUN_win {b : ByteArray} {e : Nat} (he : e ≤ b.size) (N i : Nat) :
    readUN N (win b i e) =
      (readUNAt b e N i).map (fun p => (p.1, win b i p.2, win b p.2 e)) :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.readUN_win he N i

theorem splitAt_ok {b : ByteArray} {e : Nat} :
    ∀ (fuel i : Nat) {vs : List View}, splitAt b e fuel i = some vs → ∀ v ∈ vs, View.ok e v :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.splitAt_ok

theorem splitSecsF_win {b : ByteArray} {e : Nat} (he : e ≤ b.size) :
    ∀ (fuel i : Nat), splitSecsF fuel (win b i e) = (splitAt b e fuel i).map (List.map (View.raw b)) :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.splitSecsF_win he

theorem customName_win {b : ByteArray} {i e : Nat} (he : e ≤ b.size) :
    customName (win b i e) = customNameAt b i e :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.customName_win he

theorem secCount_win {b : ByteArray} {i e : Nat} (he : e ≤ b.size) :
    secCount (win b i e) = secCountAt b i e :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.secCount_win he

theorem Inside.tail {b : ByteArray} {v : View} {vs : List View} (h : Inside b (v :: vs)) :
    Inside b vs :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.Inside.tail h

theorem checkSecs_win {b : ByteArray} {vs : List View} (h : Inside b vs) (e : Enc) :
    checkSecs e (vs.map (View.raw b)) = checkSecsAt b e vs :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.checkSecs_win h e

theorem readHeader_win (b : ByteArray) (e : Nat) (expect : Option Enc) (i : Nat) :
    readHeader expect (win b i e) =
      (readHeaderAt b expect i e).map (fun p => (p.1, win b p.2 e)) :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.readHeader_win b e expect i

/-- **`frame` on a window is `frameAt`** (with the views read back as sections). -/
theorem frame_win {b : ByteArray} {e : Nat} (he : e ≤ b.size) (expect : Option Enc) (i : Nat) :
    frame expect (win b i e) =
      (frameAt b expect i e).map (fun p => (p.1, p.2.map (View.raw b))) :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.frame_win he expect i

/-- **`frame` of a whole binary is `frameAt` on the array.** -/
theorem frame_eq_frameAt (b : ByteArray) (expect : Option Enc) :
    frame expect b.data.toList =
      (frameAt b expect 0 b.size).map (fun p => (p.1, p.2.map (View.raw b))) :=
  Silmaril.Proofs.Wasm.Tools.FastFrame.frame_eq_frameAt b expect

end Silmaril.Wasm.Tools.FastFrame

end
