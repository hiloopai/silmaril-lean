module

public import Silmaril.Proofs.Wasm.Logic.HoareExamples.List

/-!
# Worked examples for the every-run logic

Checked in every profile and for every host relation
(proofs in `Silmaril/Proofs/Wasm/Logic/HoareExamples`):

* `catchProg_hwp` (exceptions): `block (try_table (catch x 0) (i32.const 7;
  throw x))` ends normally with `7` in every run, the store extended by the
  thrown exception;
* `loopSpec_valid` (tail calls and recursion): a function counting its argument
  down by `return_call` to itself meets "returns `42`, store unchanged" for
  every run of every call (partial correctness), by Löb induction;
* `listProg_hwp` (GC): building the linked list `2 → 1 → null` with `struct.new`
  and reading `1` through the first node with `struct.get` succeeds in every run.

Each is stated for any module instance and store in which the program's indices
resolve as assumed (the theorem hypotheses).
-/
