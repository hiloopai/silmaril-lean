module

public import Silmaril.Wasm.Component.Conformance.Run.Defs
import Silmaril.Wasm.Component.Reference.Defs

/-!
# Every oracle choice: scripted oracles and their enumeration

The reference machine resolves REF's non-determinism through an `Oracle` (`Machine/Oracle`:
C1 early return of a satisfied wait, C2/C3 which ready thread to resume, C4 the shuffle of a
waitable set, C5 cancel-now, C6a keep an error-context message, E1 host choices, and the
value choices C6b, C7). The conformance runner's default `Oracle.first` takes the first
alternative everywhere (REF's deterministic profile), `eagerOracle` one other schedule. This
module enumerates *all* of them for one call:

* `arity k`: the number of alternatives of choice `k`. Every alternative of the scheduling and
  branching choices: `earlyReturn` 2, `tickPick`/`syncLoopPick`/`host` `last + 1`, `shuffle n`
  `n!`, `cancelNow` 2, `errCtxKeep` 2. The value choices `errCtxMessage` (C6b, any consistent
  string) and `nan` (C7, any NaN bits) have infinitely many admissible answers, which a test
  can only observe as values; they keep the first-alternative answer (arity 1);
* `scriptAnswer k i`: alternative `i` (`0` is `Oracle.first .nondet`'s answer; `earlyReturn`
  alternative `1` returns early); `shuffle n` alternative `i` is `indexPerm n i`, the
  permutation whose insertion positions are the digits of `i` in the factorial base;
* `scriptOracle script` (`nondet` profile): answers the `j`-th choice of a run with
  alternative `script[j]` (`0` past the end), recording the arity of every choice it is asked
  (`ScriptSt.arities`);
* `nextScript script arities`: the lexicographic successor among the scripts of the run tree,
  `none` when the run just made was the last. Starting from `[]` and following `nextScript`
  visits every leaf of the tree of choice sequences once (depth-first, left to right), as long
  as the machine is a function of the configuration and the answers (it is: `step?`).

**Proved**: `scriptAnswer_allowed`, every answer is admissible in the `nondet` profile
(`Allowed .nondet`), so the machine never stops on an answer of `scriptOracle`; `indexPerm_perm`.
Not proved: that `nextScript` enumerates every leaf (it is the standard successor of a
mixed-radix counter; checked by the runner's counts), nor that the factorial-base digits give
pairwise distinct permutations.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Conformance.Explore

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon

/-- The permutation of `range n` whose insertion positions are the factorial-base digits of
`i`: `n - 1` is inserted `i % n` places before the end of the permutation of `range (n - 1)`
for `i / n` (so `indexPerm n 0 = range n`). -/
def indexPerm : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, i => (indexPerm n (i / (n + 1))).insertIdx (n - i % (n + 1)) n

theorem length_indexPerm : ∀ n i, (indexPerm n i).length = n
  | 0, _ => rfl
  | n + 1, i => by
    simp only [indexPerm]
    rw [List.length_insertIdx_of_le_length (by rw [length_indexPerm n]; exact Nat.sub_le _ _),
      length_indexPerm n]

theorem indexPerm_perm : ∀ n i, (indexPerm n i).Perm (List.range n)
  | 0, _ => List.Perm.refl _
  | n + 1, i => by
    simp only [indexPerm]
    refine (List.perm_insertIdx n _ ?_).trans ?_
    · rw [length_indexPerm]; exact Nat.sub_le _ _
    · rw [List.range_succ]
      exact ((indexPerm_perm n _).cons n).trans (List.perm_append_singleton n _).symm

example : indexPerm 3 0 = [0, 1, 2] ∧ ((List.range 6).map (indexPerm 3)).Nodup ∧
    ((List.range 24).map (indexPerm 4)).Nodup := by decide

/-- The number of alternatives `scriptOracle` enumerates at choice `k`. -/
def arity : ChoiceKind → Nat
  | .earlyReturn _ => 2
  | .tickPick last | .syncLoopPick last | .host last => last + 1
  | .shuffle n => n.factorial
  | .cancelNow | .errCtxKeep => 2
  | .errCtxMessage _ | .nan _ _ => 1

/-- Alternative `i` of choice `k`. -/
def scriptAnswer : (k : ChoiceKind) → Nat → k.Resp
  | .earlyReturn _, i => i % 2 == 1
  | .tickPick last, i => ⟨i % (last + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  | .syncLoopPick last, i => ⟨i % (last + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  | .host last, i => ⟨i % (last + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  | .shuffle n, i => indexPerm n i
  | .cancelNow, i => i % 2 == 0
  | .errCtxKeep, i => i % 2 == 1
  | .errCtxMessage s, _ => keepMessage s
  | .nan t x, _ => firstNan .nondet t x

/-- **Every answer of a script is admissible** in the `nondet` profile. -/
theorem scriptAnswer_allowed (k : ChoiceKind) (i : Nat) : Allowed .nondet k (scriptAnswer k i) := by
  cases k with
  | earlyReturn _ => exact fun h => nomatch h
  | tickPick _ => trivial
  | syncLoopPick _ => trivial
  | shuffle n => exact indexPerm_perm n i
  | cancelNow => exact fun h => nomatch h
  | errCtxKeep => exact fun h => nomatch h
  | errCtxMessage m => exact keepMessage_allowed _ m
  | nan t x => exact firstNan_allowed .nondet t x
  | host _ => trivial

/-- Alternative `0` is `Oracle.first .nondet`'s answer. -/
example (k : ChoiceKind) : scriptAnswer k 0 = firstAnswer .nondet k := by
  cases k with
  | shuffle n =>
    show indexPerm n 0 = List.range n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [indexPerm, Nat.zero_div, Nat.zero_mod, Nat.sub_zero, ih, List.range_succ]
      have h := List.insertIdx_length_self (l := List.range n) (x := n)
      rwa [List.length_range] at h
  | _ => rfl

/-- The state of a scripted oracle: the script, the position, and the arities seen. -/
structure ScriptSt where
  script : List Nat
  pos : Nat := 0
  arities : Array Nat := #[]

/-- The oracle following `script` (`nondet` profile). -/
def scriptOracle {E : CoreEngine} (script : List Nat) : Oracle E where
  prof := .nondet
  State := ScriptSt
  state := { script }
  answer := fun st _ k =>
    (scriptAnswer k (st.script.getD st.pos 0),
      { st with pos := st.pos + 1, arities := st.arities.push (arity k) })

/-- The next script after a run that followed `script` and met choices of `arities`:
increment the last position that has an untried alternative, drop everything after it. -/
def nextScript (script : List Nat) (arities : Array Nat) : Option (List Nat) :=
  let cs := (List.range arities.size).map fun j => script.getD j 0
  let rec go : List (Nat × Nat) → Option (List Nat)
    | [] => none
    | (c, a) :: rest =>
      match go rest with
      | some r => some (c :: r)
      | none => if c + 1 < a then some [c + 1] else none
  go (cs.zip arities.toList)

example : nextScript [] #[2, 3] = some [0, 1] := by decide
example : nextScript [0, 2] #[2, 3] = some [1] := by decide
example : nextScript [1, 2] #[2, 3] = none := by decide

/-- The result of one schedule of a call. -/
structure Run where
  script : List Nat
  result : CallResult
  cfg : Cfg
  choices : Nat

/-- Run call `k` of `f` on `args` from `m` under every script, at most `budget` of them, in
the order of `nextScript`; `true` when the enumeration finished. -/
def exploreCall (fuel : Nat) (m : Cfg) (k : Nat) (f : FuncId) (args : List Value.Val)
    (budget : Nat) : List Run × Bool :=
  let rec loop : Nat → List Nat → List Run → List Run × Bool
    | 0, _, acc => (acc.reverse, false)
    | n + 1, script, acc =>
      let o : Oracle Eng := scriptOracle script
      match callUntil emb.hr emb.dispatch emb.X o hasPending resolvePending fuel ⟨k⟩ f args m with
      | none => ((⟨script, .stuck "invoke event not enabled", m, 0⟩ :: acc).reverse, true)
      | some r =>
        let st : ScriptSt := r.state
        let run : Run := ⟨script, classify k r, r.config, st.arities.size⟩
        match nextScript script st.arities with
        | none => ((run :: acc).reverse, true)
        | some s => loop n s (run :: acc)
  loop budget [] []

end Silmaril.Wasm.Component.Conformance.Explore
