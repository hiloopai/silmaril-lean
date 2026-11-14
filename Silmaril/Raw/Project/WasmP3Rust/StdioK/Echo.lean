module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Main
public import Silmaril.Wasi.Theory.Thms

/-!
# `echo`: from the plan's guarantee to `echoG1 args`

Under the arguments theory `argsTh args`, the last `get-arguments` answer of every prefix is
`args` (as UTF-8 bytes) or absent, so the target of `echoPlan` is the line of `args`, which is
`utf8 (" ".intercalate (args.drop 1) ++ "\n")` (`lineOf_utf8`).
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Project.Shapes.Component (WasiSat)

/-! ## UTF-8 -/

theorem toList_loop (bs : ByteArray) :
    ∀ (n i : Nat) (r : List UInt8), bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i
  | 0, i, r, hn => by
    have hsz : bs.size = bs.data.toList.length := by rw [Array.length_toList]; rfl
    rw [ByteArray.toList.loop]
    have hi : ¬ i < bs.size := by omega
    simp only [hi, ite_false]
    rw [List.drop_eq_nil_of_le (by rw [← hsz]; omega), List.append_nil]
  | n + 1, i, r, hn => by
    have hsz : bs.size = bs.data.toList.length := by rw [Array.length_toList]; rfl
    rw [ByteArray.toList.loop]
    have hi : i < bs.size := by omega
    simp only [hi, ite_true]
    rw [toList_loop bs n (i + 1) _ (by omega), List.reverse_cons, List.append_assoc]
    congr 1
    have hi' : i < bs.data.toList.length := hsz ▸ hi
    rw [List.drop_eq_getElem_cons hi']
    have hget : bs.get! i = bs.data.toList[i]'hi' := by
      rcases bs with ⟨d⟩
      have hd : i < d.size := by simpa using hi'
      show d[i]! = d.toList[i]'hi'
      rw [Array.getElem_toList]
      exact getElem!_pos d i hd
    rw [hget]
    rfl

theorem byteArray_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  unfold ByteArray.toList
  rw [toList_loop bs bs.size 0 [] (by omega)]
  simp

theorem utf8_eq (s : String) : utf8 s = s.toByteArray.data.toList.map fun b => BitVec.ofNat 8 b.toNat := by
  simp only [utf8, String.toUTF8_eq_toByteArray, byteArray_toList]

theorem utf8_append (s t : String) : utf8 (s ++ t) = utf8 s ++ utf8 t := by
  simp only [utf8_eq, String.toByteArray_append, ByteArray.data_append, Array.toList_append,
    List.map_append]

theorem utf8_intercalate (sep : String) :
    ∀ l : List String, utf8 (sep.intercalate l) = List.intercalate (utf8 sep) (l.map utf8)
  | [] => by simp [utf8_eq]
  | [t] => by simp
  | t :: u :: l => by
    rw [String.intercalate_cons_cons, utf8_append, utf8_append, utf8_intercalate sep (u :: l)]
    simp only [List.map_cons, List.intercalate_cons_cons]

theorem utf8_space : utf8 " " = [32] := by decide +kernel

theorem utf8_newline : utf8 "\n" = [10] := by decide +kernel

/-- **The line of the arguments is the UTF-8 of `echo`'s string.** -/
theorem lineOf_utf8 (args : List String) :
    lineOf (args.map utf8) = utf8 (" ".intercalate (args.drop 1) ++ "\n") := by
  rw [utf8_append, utf8_intercalate, utf8_space, utf8_newline, lineOf, ← List.map_drop]

/-! ## The arguments theory -/

theorem argsSeen_of {args : List String} :
    ∀ (x : Option (List (List (BitVec 8)))) (t : List WEv),
      (x = none ∨ x = some (args.map utf8)) → (∀ e ∈ t, argsOk args e = true) →
      t.foldl argsStep x = none ∨ t.foldl argsStep x = some (args.map utf8)
  | x, [], hx, _ => hx
  | x, e :: t, hx, h => by
    simp only [List.foldl_cons]
    refine argsSeen_of _ t ?_ (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have he := h e List.mem_cons_self
    cases e with
    | imp f a r =>
      simp only [argsStep]
      split
      · rename_i hf
        simp only [argsOk, hf, decide_true, Bool.not_true, Bool.false_or,
          decide_eq_true_eq] at he
        exact .inr he
      · exact hx
    | _ => exact hx

theorem argsOk_of_hostView {args : List String} {t : List WEv}
    (h : (argsTh args).Accepts (hostView t)) : ∀ e ∈ t, argsOk args e = true := by
  rw [argsTh, pointwise_accepts_iff] at h
  intro e he
  cases hi : e.isImp
  · cases e <;> simp_all [WEv.isImp, argsOk]
  · exact h e (List.mem_filter.2 ⟨he, hi⟩)

/-! ## Guarantees, prefix by prefix -/

theorem ofTraces_mono {Q Q' : List WEv → Bool} :
    ∀ (q t : List WEv), (∀ p, p <+: t → p ≠ [] → Q (q ++ p) = true → Q' (q ++ p) = true) →
      ((ofTraces Q).run q t).isSome → ((ofTraces Q').run q t).isSome
  | q, [], _, _ => rfl
  | q, e :: t, h, ha => by
    have hs : ∀ R : List WEv → Bool, (ofTraces R).step q e =
        if R (q ++ [e]) then some (q ++ [e]) else none := fun _ => rfl
    rw [Protocol.run_cons, hs] at ha ⊢
    split at ha
    · rename_i hq
      have hq' : Q' (q ++ [e]) = true := h [e] (List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩)
        (List.cons_ne_nil _ _) hq
      simp only [hq', ite_true, Option.bind_some] at ha ⊢
      refine ofTraces_mono (q ++ [e]) t (fun p hp hne hQ => ?_) ha
      have := h (e :: p) (List.cons_prefix_cons.2 ⟨rfl, hp⟩) (List.cons_ne_nil _ _)
      simp only [List.append_assoc, List.singleton_append] at hQ ⊢ this
      exact this hQ
    · simp at ha

/-- `echoPlan`'s guarantee gives `echoG1 args` on traces whose `get-arguments` answers are
`args`. -/
theorem echoG1_of {args : List String} {t : List WEv} (hg : (GP echoPlan).Accepts t)
    (ha : ∀ e ∈ t, argsOk args e = true) : (echoG1 args).Accepts t := by
  refine ofTraces_mono (Q := fun t => !decide (runCalls t ≤ 1) || goodB echoPlan (obsOf t))
    (Q' := fun t => !decide (runCalls t ≤ 1) ||
      printsP (utf8 (" ".intercalate (args.drop 1) ++ "\n")) t) [] t (fun p hp _ hQ => ?_) hg
  simp only [List.nil_append] at hQ ⊢
  simp only [Bool.or_eq_true] at hQ ⊢
  rcases hQ with hQ | hQ
  · exact .inl hQ
  · right
    have hs := argsSeen_of (args := args) none p (.inl rfl)
      (fun e he => ha e (hp.subset he))
    simp only [goodB, tgt, echoPlan] at hQ
    simp only [printsP]
    change (stdoutBytes p).isPrefixOf _ && (!runOk p || stdoutBytes p == _) = true
    have hargs : (obsOf p).args = argsSeen p := rfl
    rcases hs with hs | hs
    · have hn : argsSeen p = none := hs
      rw [hargs, hn] at hQ
      simp only [Option.map_none, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at hQ
      obtain ⟨h1, h2⟩ := hQ
      have h1' : stdoutBytes p = [] := h1
      have h2' : runOk p = false := h2
      simp [h1', h2']
    · have hn : argsSeen p = some (args.map utf8) := hs
      rw [hargs, hn, Option.map_some, lineOf_utf8] at hQ
      exact hQ

/-- **`echo`'s model meets `echoG1 args` over every host of `echoTh args`.** -/
theorem echo_sat {args : List String} {σ : p3xWorld.Model}
    (h : WasiSat σ waitTh3x (GP echoPlan)) : WasiSat σ (echoTh args) (echoG1 args) := by
  intro s hs hT
  have hT' := (Protocol.accepts_prod_iff _ _ _).1 hT
  have hw := ((Protocol.accepts_prod_iff _ _ _).1 hT'.1).2
  exact echoG1_of (h s hs hw) (argsOk_of_hostView hT'.2)

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
