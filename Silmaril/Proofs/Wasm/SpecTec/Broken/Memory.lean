module

public import Silmaril.Proofs.Wasm.SpecTec.Broken.Rules

/-!
# The load boundary gap, at the rules of the generated scripts

`Step_read/load-num-oob` (rule 38) traps when the accessed bytes run *past* the end of memory;
`Step_read/load-num-val` (rule 39) reads them through `Value.slice?`.  The interpreter
(`il/eval.ml:284`, and `:595` for slice update) bounds slices with a strict `i + n < |es|`, so a
load whose last byte is the memory's last byte satisfied neither rule.  This is a defect of the
evaluator, not of the specification text, and the errata leave both rules unchanged.

The port in `Sem/Value.lean` now uses the corrected bound `≤` (upstream item U2 of
`docs/projects/spectec/README.md`).  This file keeps the **original** behaviour as a documented defect,
`sliceEvalMl?` (the strict transcription) and `sliceEvalMl?_boundary`, and proves the corrected
behaviour at the boundary: `load_boundary_slice` (the `-val` side condition holds with the last
`k` bytes, `-oob`'s does not) and `loadNum_boundary_not_oob`.

The rule-level statements are conditional on two functionality facts the runtime bridge would
supply: `$mem(z, x).BYTES` and `$size(nt)/8` each have one value.
-/

public section

namespace Silmaril.Wasm.SpecTec.Broken

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.SpecTec.Equiv.Validation
open Silmaril.SpecTec.Equiv.ExecReadMemory
open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 8000000
set_option maxHeartbeats 8000000

/-- `Value.slice?` as `il/eval.ml:284` writes it, with the **strict** bound `i + n < |es|`.
This was the ported definition before upstream item U2; it is kept here only to document the
interpreter's defect. -/
def sliceEvalMl? (v : Value) (i n : Nat) : Option Value :=
  match v with
  | .list vs => if i + n < vs.length then some (.list ((vs.drop i).take n)) else none
  | _ => none

/-- **The defect.**  At the boundary `a + k = |es|` the interpreter's slice is undefined, while
the `-oob` guard `|es| < a + k` fails too: an access ending at the last element had no step.  The
corrected `Value.slice?` is defined there. -/
theorem sliceEvalMl?_boundary {a k : Nat} {bs : List Value} (h : a + k = bs.length) :
    ¬ bs.length < a + k ∧ sliceEvalMl? (.list bs) a k = none ∧
      Value.slice? (.list bs) a k = some (.list (bs.drop a)) := by
  refine ⟨by omega, ?_, (boundary_slice h).2⟩
  simp only [sliceEvalMl?, ite_eq_right_iff]
  omega

/-- Off the boundary the correction changes nothing. -/
theorem sliceEvalMl?_eq_slice? {a k : Nat} {v : Value}
    (h : ∀ bs, v = .list bs → a + k ≠ bs.length) :
    sliceEvalMl? v a k = Value.slice? v a k := by
  cases v with
  | list bs =>
      have := h bs rfl
      simp only [sliceEvalMl?, Value.slice?]
      by_cases hlt : a + k < bs.length
      · simp [hlt, Nat.le_of_lt hlt]
      · have hle : ¬ a + k ≤ bs.length := by omega
        simp [hlt, hle]
  | _ => rfl

/-- At the boundary `a + k = |bytes|`, the `-oob` side condition fails and the `-val` slice
condition holds, with the last `k` bytes. -/
theorem load_boundary_slice {env : Env} {z x i ao : Value} {k a : Nat} {bs : List Value}
    (hbs : ∀ bs', CallBytes env "mem" z x bs' → bs' = bs) (hc : CallBytes env "mem" z x bs)
    (ha : EffAddr i ao a) (hk : a + k = bs.length) :
    ¬ LoadOob env z x i ao k ∧ LoadSlice env z x i ao k (.list (bs.drop a)) := by
  constructor
  · rintro ⟨a', bs', ha', hc', hlt⟩
    obtain rfl := effAddr_unique ha ha'
    obtain rfl := hbs bs' hc'
    omega
  · exact ⟨a, bs, ha, hc, (boundary_slice hk).2⟩

/-- The two load rules, in the generated original. -/
theorem hasLoadRules_original :
    HasRuleAt Wasm30.envOriginal "Step_read" "%~>%" 38 ExecRead.loadNumOobRule ∧
      HasRuleAt Wasm30.envOriginal "Step_read" "%~>%" 39 ExecRead.loadNumValRule :=
  ⟨hasRuleAt_original ExecRead.hasReadRules_wasm30.loadNumOob,
    hasRuleAt_original ExecRead.hasReadRules_wasm30.loadNumVal⟩

/-- …and unchanged in the generated fixed script. -/
theorem hasLoadRules_fixed :
    HasRuleAt Wasm30.envFixed "Step_read" "%~>%" 38 ExecRead.loadNumOobRule ∧
      HasRuleAt Wasm30.envFixed "Step_read" "%~>%" 39 ExecRead.loadNumValRule :=
  ⟨⟨_, _, _, by rfl, rfl, by rfl⟩, ⟨_, _, _, by rfl, rfl, by rfl⟩⟩

/-- **The boundary at the rules.**  For a `load` of a type whose byte width `k` is determined,
at an address `a` with `a + k` equal to the memory's length, `load-num-oob` does not fire, whatever
the result.  (`load-num-val`'s slice side condition holds there: `load_boundary_slice`.) -/
theorem loadNum_boundary_not_oob {env : Env} {z atv i nt x ao : Value} {k a : Nat}
    {bs r : List Value} (hbs : ∀ bs', CallBytes env "mem" z x bs' → bs' = bs)
    (hsz : ∀ m k', ExecNumeric.Applies env "size" [.val nt] (.num m) → BitsToBytes m k' → k' = k)
    (ha : EffAddr i ao a) (hk : a + k = bs.length) :
    ¬ RuleFires env "%~>%" [] [] (readV z [Execution.constV atv i, loadV nt (.opt none) x ao] r)
        ExecRead.loadNumOobRule := by
  intro hf
  obtain ⟨z', atv', i', nt', x', ao', m, k', hv, hs, hb, hoob⟩ := ruleFires_loadNumOob_iff.1 hf
  simp only [readV, Execution.constV, loadV, Value.tuple.injEq, Value.case.injEq,
    List.cons.injEq, ExecStep.configV, Value.list.injEq, and_true, true_and] at hv
  obtain ⟨⟨rfl, ⟨-, rfl⟩, rfl, rfl, rfl⟩, -⟩ := hv
  obtain rfl := hsz m k' hs hb
  obtain ⟨a', bs', ha', hc', hlt⟩ := hoob
  obtain rfl := effAddr_unique ha ha'
  obtain rfl := hbs bs' hc'
  omega

end Silmaril.Wasm.SpecTec.Broken
