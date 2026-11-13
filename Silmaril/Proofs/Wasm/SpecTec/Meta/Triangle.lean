module

public import Silmaril.Proofs.Wasm.SpecTec.Meta.Original
public import Silmaril.Raw.Wasm.SpecTec.Scripts.Wasm30.Original
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.Execution
public import Silmaril.Wasm.SpecTec.Broken.Thms

/-!
# Their semantics as a third reading of wasm-3.0: two rule instances

Two expressions of the wasm-3.0 script are evaluated three ways: by our IL semantics, by Core 3.0
through the existing simulation lemmas, and by their `Reduce_exp` (read by `DDerives`) after
instantiating the rule's variables and encoding the result as IL-as-data.

* **`i32.add`** reduces by `Step_pure/binop-val` to `$iadd_(32, i₁, i₂)`, whose only clause has the
  body `iaddBody` (`iadd_clause`, checked by `rfl` against the generated script). Under the
  clause's bindings `iaddBody` evaluates to the encoding of `(i₁ + i₂) mod 2^32`
  (`evalExp_iaddBody`), which is what `$iadd_` denotes (`Equiv.callDef_iadd_intBinOp`: Silmaril's
  `Numerics.intBinOp .i32 .add`, the operation Core's `i32.add` uses). The arithmetic inside the
  `%` wrapper, with the projections of the arguments evaluated, is `modPow a b 32`. In the fixed
  meta-theory script it reduces to the same number (`triangle_iadd`); in the original it reduces
  to no value at all (`original_modPow_stuck`).
* **`br_if`**: `Step_pure/br_if-true` (rule 11) has the premise `brIfPremise`, `c =/= 0` on the
  payload of `c` (`brIfTrue_premise`). Instantiated, it is `brIfCore k`; our evaluator and the
  fixed meta-theory agree that it is `k ≠ 0` (`triangle_brIf`), and Core's `Step.brIfTrue` fires
  under exactly that side condition (`Equiv.Execution.derives_brIfTrue`). In the original
  meta-theory it never reduces to `true` (`original_ne_stuck`), so `br_if` with a non-zero
  condition is unfireable there.

The instantiation (substituting the payloads for `proj (uncase (var x) "%") 0`) is done at the IL
level, by evaluation; encoding whole wasm-3.0 rules as IL-as-data, and running their `CALL-apply`
on `$iadd_` itself, is the scaling step left (`docs/projects/wasm-extras.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Meta

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000

/-- The rules of a relation definition. -/
def relRules : IL.Def → List Rule
  | .relD _ _ _ _ rs => rs
  | _ => []

/-- The clauses of a function definition. -/
def defClauses : IL.Def → List Clause
  | .decD _ _ _ cs => cs
  | _ => []

/-! ## `i32.add` -/

/-- The body of the only clause of wasm-3.0's `$iadd_`. -/
def iaddBody : Exp :=
  .caseE "%" (.tupE [.binE .modOp (.numT .natT)
    (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i_1") "%") 0)
      (.projE (.uncaseE (.varE "i_2") "%") 0))
    (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.varE "N"))])

theorem iadd_clause : ∃ qs pats,
    defClauses Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d431 = [.defD qs pats iaddBody []] :=
  ⟨_, _, rfl⟩

/-- The bindings of `$iadd_(32, i₁, i₂)`'s clause. -/
abbrev iaddScope (a b : Nat) : VarEnv :=
  ((VarEnv.empty.bindVal "N" (.num (.natN 32))).bindVal "i_1" (con "%" [.num (.natN a)])).bindVal
    "i_2" (con "%" [.num (.natN b)])

theorem evalExp_iaddBody {env : Env} (a b : Nat) :
    EvalExp env (iaddScope a b) iaddBody (con "%" [.num (.natN ((a + b) % 2 ^ 32))]) :=
  ⟨10, by with_unfolding_all rfl⟩

theorem strict_modPow (a b : Nat) :
    (modPow a b 32).strict = some (.num (.natN ((a + b) % 2 ^ 32))) := by
  simp [modPow, FExp.strict, binValues, Num.bin, Res.ofOption, FExp.resVal]

theorem noIntPow_modPow (a b N : Nat) : (modPow a b N).NoIntPow := by
  simp [modPow, FExp.NoIntPow, FExp.strict]

/-- **`i32.add`, three ways.** Our `$iadd_` of wasm-3.0 is Silmaril's `intBinOp .i32 .add`
(Core's `i32.add`) and its clause body is `(a + b) mod 2^32`; their fixed `Reduce_exp` reduces
the same arithmetic to the same number; their original one to nothing. -/
theorem triangle_iadd (x y : Silmaril.Wasm.Numerics.IntValue .i32) :
    CallDef (envOfScript Specs.wasm30) VarEnv.empty "iadd_"
        (Equiv.litArgs [Equiv.natV 32, Equiv.bvV x, Equiv.bvV y])
        (Equiv.bvV ((Silmaril.Wasm.Numerics.intBinOp .i32 .add x y).toOption.getD 0)) ∧
      EvalExp (envOfScript Specs.wasm30) (iaddScope x.toNat y.toNat) iaddBody
        (con "%" [.num (.natN ((x.toNat + y.toNat) % 2 ^ 32))]) ∧
      MReduce envF emptyS (modPow x.toNat y.toNat 32).enc
        (encVal (.num (.natN ((x.toNat + y.toNat) % 2 ^ 32)))) ∧
      ∀ v, ¬ MReduce envO emptyS (modPow x.toNat y.toNat 32).enc (encVal v) :=
  ⟨Equiv.callDef_iadd_intBinOp .i32 x y, evalExp_iaddBody _ _,
    reduceF_complete typedV_emptyS (noIntPow_modPow _ _ _) (strict_modPow _ _),
    original_modPow_stuck _ _ _⟩

/-! ## `br_if` -/

/-- The premise of `Step_pure/br_if-true` in wasm-3.0: `c =/= 0`. -/
def brIfPremise : Exp :=
  .cmpE .neOp .boolT (.projE (.uncaseE (.varE "c") "%") 0) (.numE (.natN 0))

theorem brIfTrue_premise : ∃ qs concl,
    (relRules Silmaril.Wasm.SpecTec.Scripts.Wasm30.Original.d637)[11]? =
      some (.ruleD "br_if-true" qs "%~>%" concl [.ifPr brIfPremise]) :=
  ⟨_, _, rfl⟩

/-- `br_if-true`'s premise with `c` the `i32` constant of payload `k`. -/
def brIfCore (k : Nat) : FExp := .cmp .neOp .boolT (.nat k) (.nat 0)

theorem beq_natN_zero (k : Nat) :
    (Value.num (.natN k) == Value.num (.natN 0)) = decide (k = 0) := by
  by_cases h : k = 0 <;> simp [h]

theorem evalExp_brIfPremise {env : Env} (k : Nat) :
    EvalExp env (VarEnv.empty.bindVal "c" (con "%" [.num (.natN k)])) brIfPremise
      (.bool (decide (k ≠ 0))) := by
  have hp : EvalExp env (VarEnv.empty.bindVal "c" (con "%" [.num (.natN k)]))
      (.projE (.uncaseE (.varE "c") "%") 0) (.num (.natN k)) := ⟨5, by with_unfolding_all rfl⟩
  have e := evalExp_ne (t := .boolT) hp (evalExp_numE_iff.2 rfl : EvalExp env _ (.numE (.natN 0)) _)
  simpa [beq_natN_zero, brIfPremise] using e

theorem strict_brIfCore (k : Nat) : (brIfCore k).strict = some (.bool (decide (k ≠ 0))) := by
  simp [brIfCore, FExp.strict, cmpValues, FExp.resVal, beq_natN_zero]

/-- **`br_if`, three ways.** Our evaluation of `br_if-true`'s premise and their fixed
`Reduce_exp` both give `k ≠ 0` (Core's side condition for `Step.brIfTrue`,
`Equiv.Execution.derives_brIfTrue`); their original one never reduces it to `true` when
`k ≠ 0`. -/
theorem triangle_brIf (k : Nat) :
    EvalExp (envOfScript Specs.wasm30) (VarEnv.empty.bindVal "c" (con "%" [.num (.natN k)]))
        brIfPremise (.bool (decide (k ≠ 0))) ∧
      MReduce envF emptyS (brIfCore k).enc (encVal (.bool (decide (k ≠ 0)))) ∧
      (k ≠ 0 → ¬ MReduce envO emptyS (brIfCore k).enc (encVal (.bool true))) :=
  ⟨evalExp_brIfPremise k,
    reduceF_complete typedV_emptyS (e := brIfCore k) ⟨trivial, trivial⟩ (strict_brIfCore k),
    fun hk => original_ne_stuck hk⟩

/-! ## A load at the end of memory: `ACC-SLICE` -/

/-- The side condition of `Step_exp/ACC-SLICE` (and, the same text, of `UPD-SLICE`):
`n <= $(n + m) < |e'*|`. -/
def accSliceGuard : Exp :=
  .binE .andOp .boolT
    (.cmpE .leOp (.numT .natT) (.varE "n") (.binE .addOp (.numT .natT) (.varE "n") (.varE "m")))
    (.cmpE .ltOp (.numT .natT) (.binE .addOp (.numT .natT) (.varE "n") (.varE "m"))
      (.lenE (.iterE (.varE "e'") (.mk .list [.mk "e'" (.varE "e'*")]))))

/-- `ACC-SLICE` is rule 43 of the fixed `Step_exp`, and its second premise is `accSliceGuard`
(M1 does not touch it; in the original it is rule 41). -/
theorem accSlice_guard : ∃ qs concl p₁ p₃,
    (rulesOf envF "Step_exp")[43]? =
      some (.ruleD "ACC-SLICE" qs "%|-%~>%" concl [p₁, .ifPr accSliceGuard, p₃]) :=
  ⟨_, _, _, _, rfl⟩

theorem accSlice_guard_original : ∃ qs concl p₁ p₃,
    (rulesOf envO "Step_exp")[41]? =
      some (.ruleD "ACC-SLICE" qs "%|-%~>%" concl [p₁, .ifPr accSliceGuard, p₃]) :=
  ⟨_, _, _, _, rfl⟩

/-- Four encoded bytes, the list a 4-byte load slices. -/
def fourBytes : List Value := [encNum (.natN 0), encNum (.natN 1), encNum (.natN 2), encNum (.natN 3)]

/-- The guard's scope for `fourBytes[n : m]`. -/
abbrev sliceScope (n m : Nat) : VarEnv :=
  ((VarEnv.empty.bindVal "n" (.num (.natN n))).bindVal "m" (.num (.natN m))).bindVal "e'*"
    (.list fourBytes)

/-- **The slice bound, three ways.** Taking the last 4 of 4 bytes (`n = 0`, `m = 4`): their
guard (in both scripts) is `false`, so `ACC-SLICE` cannot fire, exactly as eval.ml's strict bound
(`Broken.sliceEvalMl?`) has no slice; our `Value.slice?` (upstream item U2) returns the bytes, as
Core's load does at the boundary (`Silmaril.Wasm.SpecTec.boundary_slice`). One byte shorter, all
agree. -/
theorem triangle_slice {env : Env} :
    EvalExp env (sliceScope 0 4) accSliceGuard (.bool false) ∧
      Silmaril.Wasm.SpecTec.Broken.sliceEvalMl? (.list fourBytes) 0 4 = none ∧
      Value.slice? (.list fourBytes) 0 4 = some (.list fourBytes) ∧
      EvalExp env (sliceScope 0 3) accSliceGuard (.bool true) ∧
      Value.slice? (.list fourBytes) 0 3 = some (.list (fourBytes.take 3)) :=
  ⟨⟨10, by with_unfolding_all rfl⟩, (Silmaril.Wasm.SpecTec.Broken.sliceEvalMl?_boundary rfl).2.1, rfl,
    ⟨10, by with_unfolding_all rfl⟩, rfl⟩

end Silmaril.Wasm.SpecTec.Meta
