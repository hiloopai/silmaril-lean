module

public import Silmaril.Wasm.Perf.WatPrint.Defs
public import Silmaril.Wasm.Wit.Tool.Defs

/-!
# The string-builder printer prints what `Sexp.printAll` prints: proofs

The statements are restated in `Silmaril.Wasm.Perf.WatPrint.Thms`.

`ppS_eq`/`ppLS_eq` (mutual): `ppS flat ind s acc = acc ++ String.ofList (pp flat ind s)`;
`printAllF_eq : printAllF = Sexp.printAll`; `printF_eq : printF = Wat.print` (also registered
with `@[csimp]`); `printWatF_eq : printWatF = Wit.Tool.printWat`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Perf.WatPrint

open Silmaril.Wasm.Component.Wat (Sexp)
open Silmaril.Wasm.Component.Wat.Sexp (escByte quote hexDigit width breakSep pp ppL)
open Silmaril.Wasm.Perf.WatPrint

private theorem push_ofList (s : String) (c : Char) : s.push c = s ++ String.ofList [c] := by
  rw [String.push_eq_append, String.ofList_cons, String.ofList_nil, String.append_empty]

theorem escPush_eq (b : UInt8) (acc : String) : escPush b acc = acc ++ String.ofList (escByte b) := by
  unfold escPush escByte
  split
  · exact push_ofList acc _
  · simp only [push_ofList, String.append_assoc, ← String.ofList_append, List.cons_append,
      List.nil_append]

theorem escAll_eq : ∀ (bs : List UInt8) (acc : String),
    escAll bs acc = acc ++ String.ofList (bs.flatMap escByte)
  | [], acc => by simp only [escAll, List.flatMap_nil, String.ofList_nil, String.append_empty]
  | b :: bs, acc => by
    simp only [escAll, escAll_eq bs, escPush_eq, List.flatMap_cons, String.ofList_append,
      String.append_assoc]

theorem escW_eq (b : UInt8) : escW b = (escByte b).length := by
  unfold escW escByte
  split <;> rfl

theorem escLen_eq : ∀ (bs : List UInt8) (n : Nat), escLen bs n = n + (bs.flatMap escByte).length
  | [], n => by simp only [escLen, List.flatMap_nil, List.length_nil, Nat.add_zero]
  | b :: bs, n => by
    simp only [escLen, escLen_eq bs, escW_eq, List.flatMap_cons, List.length_append,
      Nat.add_assoc]

theorem quoteS_eq (bs : List UInt8) (acc : String) : quoteS bs acc = acc ++ String.ofList (quote bs) := by
  simp only [quoteS, quote, escAll_eq, push_ofList, String.append_assoc, ← String.ofList_append,
    List.cons_append, List.nil_append]

theorem pp_true (ind : Nat) : ∀ s : Sexp, pp true ind s = pp true 0 s
  | .atom _ => by simp only [pp]
  | .str _ => by simp only [pp]
  | .list _ => by simp only [pp, Bool.true_or, ite_true]

mutual
theorem flatLen_eq : ∀ s : Sexp, flatLen s = (pp true 0 s).length
  | .atom a => by simp only [flatLen, pp, String.length_toList]
  | .str b => by
    simp only [flatLen, pp, quote, escLen_eq, List.length_cons, List.length_append,
      List.length_nil]
    omega
  | .list xs => by
    simp only [flatLen, pp, Bool.true_or, ite_true, List.length_cons, List.length_append,
      List.length_nil, flatLenL_eq xs]

theorem flatLenL_eq : ∀ xs : List Sexp, flatLenL xs = (ppL true (fun _ _ => [' ']) 0 xs).length
  | [] => by simp only [flatLenL, ppL, List.length_nil]
  | [x] => by simp only [flatLenL, ppL, flatLen_eq x]
  | x :: y :: xs => by
    simp only [flatLenL, ppL, List.length_append, List.length_singleton, flatLen_eq x,
      flatLenL_eq (y :: xs)]
end

mutual
theorem ppS_eq (flat : Bool) (ind : Nat) :
    ∀ (s : Sexp) (acc : String), ppS flat ind s acc = acc ++ String.ofList (pp flat ind s)
  | .atom a, acc => by simp only [ppS, pp, String.ofList_toList]
  | .str b, acc => by simp only [ppS, pp, quoteS_eq]
  | .list xs, acc => by
    have hl : flatLenL xs + 2 =
        ('(' :: (ppL true (fun _ _ => [' ']) 0 xs ++ [')'])).length := by
      simp only [flatLenL_eq xs, List.length_cons, List.length_append, List.length_nil]
    have h1 := ppLS_eq true (fun _ _ => [' ']) 0 xs (acc.push '(')
    have h2 := ppLS_eq false (breakSep (ind + 2)) (ind + 2) xs (acc.push '(')
    simp only [ppS, pp, hl]
    split
    · rw [h1]
      simp only [push_ofList, String.append_assoc, ← String.ofList_append, List.cons_append,
        List.nil_append]
    · rw [h2]
      simp only [push_ofList, String.append_assoc, ← String.ofList_append, List.cons_append,
        List.nil_append]

theorem ppLS_eq (flat : Bool) (sep : Sexp → Sexp → List Char) (ind : Nat) :
    ∀ (xs : List Sexp) (acc : String),
      ppLS flat sep ind xs acc = acc ++ String.ofList (ppL flat sep ind xs)
  | [], acc => by simp only [ppLS, ppL, String.ofList_nil, String.append_empty]
  | [x], acc => by simp only [ppLS, ppL, ppS_eq flat ind x]
  | x :: y :: xs, acc => by
    simp only [ppLS, ppL, ppS_eq flat ind x, ppLS_eq flat sep ind (y :: xs),
      String.ofList_append, String.append_assoc]
end

theorem printAllF_eq : printAllF = Sexp.printAll := by
  funext ss
  have step : ∀ (ss : List Sexp) (acc : String),
      ss.foldl (fun acc s => (ppS false 0 s acc).push '\n') acc =
        acc ++ String.ofList (ss.flatMap fun s => pp false 0 s ++ ['\n']) := by
    intro ss
    induction ss with
    | nil => intro acc; simp only [List.foldl_nil, List.flatMap_nil, String.ofList_nil,
        String.append_empty]
    | cons s ss ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp only [ppS_eq, push_ofList, List.flatMap_cons, String.ofList_append,
        String.append_assoc]
  simp only [printAllF, Sexp.printAll, step, String.empty_append]

theorem printF_eq : printF = Silmaril.Wasm.Component.Wat.print := by
  funext c
  simp only [printF, Silmaril.Wasm.Component.Wat.print, printAllF_eq]

theorem printWatF_eq : printWatF = Silmaril.Wasm.Wit.Tool.printWat := by
  funext b
  simp only [printWatF, Silmaril.Wasm.Wit.Tool.printWat, printF_eq]
  rfl

end Silmaril.Proofs.Wasm.Perf.WatPrint
