module

public import Silmaril.Proofs.Wasm.Logic.Words.Rules
public import Silmaril.Proofs.Wasm.Logic.Words.Sorted

/-!
# `i32` words, arrays and an `i32` view of frames: results

Proofs in `Silmaril/Proofs/Wasm/Logic/Words`, for every profile and host relation:

* words and arrays (`Mem`): `load_wd`, `store_wr`, `size_wr`, `wd_wr_same`, `wd_wr_ne`;
  `length_words`, `getElem_words`, `getD_words`, **`words_wr`** (a write inside an array segment
  is `List.set`), `words_wr_out`; the frame of writes: `sameOutside_wr`, `SameOutside.refl`,
  `.trans`, `.mono`, `.wd_eq`, `.words_eq`;
* rules over the view `fr mi L` / `MemAt` (`Rules`), with the operand stack top-first:
  `w_const`, `w_lget`, `w_lset`, `w_ltee`, `w_drop`, `w_bin`, `w_rel`, `w_test`, `w_load`,
  `w_store`, `w_end` in both readings (`Wp m`); for total correctness `t_br`, `t_brIf`, `t_if`
  (with `armPostT`, `t_armEnd`) and **`t_while`** (`block (loop body)` with an invariant and a
  natural-number variant; `whilePostT_exit`, `whilePostT_cont`); `bodyPostT_normal` (a returning
  body meets its call postcondition);
* tactics `wbegin`, `wstep`, `wnorm`, `wrun` (symbolic execution of straight-line code over the
  view).

A Silmaril addition.
-/
