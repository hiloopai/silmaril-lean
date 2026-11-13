module

public import Silmaril.Wasm.Det.GrowTrap.Litmus.Defs
public import Silmaril.Wasm.Det.GrowTrap.Thms
public import Silmaril.Wasm.Det.Core.Litmus.Thms

/-!
# Litmus module of subset 2: explicit Core runs of the unguarded grow (proofs)

`unguarded_runs`: at a profile whose grow policy is the specification's (`P.grow = .nondet`),
the invocation of function `2` of `growStore` (`i32.const 1; memory.grow 0`) returns `0` (the
old size, the grow succeeding) and also `-1` (the grow failing), by explicit Core runs built rule
by rule (`MemoryStep.growSucceed`, `MemoryStep.growFail`, then the invocation through
`Silmaril.Proofs.Wasm.Det.Core.Litmus.steps_invoke_nil`). The shape of the allocated function and
of its memory is computed by kernel evaluation (`ung_shape`); that the grow can succeed is
proved from the memory limits (`grow?_isSome`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.GrowTrap.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.GrowTrap.Litmus
open Silmaril.Proofs.Wasm.Det.Core.Litmus (steps_invoke_nil expand_of_funcType?)
open Silmaril.Wasm.Numerics (Profile)

/-- The body of function `2`. -/
def unguardedB : List Instr → Bool
  | [.intConst .i32 x, .memoryGrow m] => decide (x = 1 ∧ m = ⟨0⟩)
  | _ => false

/-- The shape of function `2`: its code, its type, and its memory (address `0`, no page, at
most one page, 32-bit). -/
def ungShape (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .wasm fn => fn.locals.isEmpty && unguardedB fn.body
    | .host _ => false) &&
  decide (fi.type.funcType? = some ([], [.num (.int .i32)])) &&
  (match growStore.mem? (Frame.forCall fi.module [] []) ⟨0⟩ with
    | some (ma, mi) => ma == 0 && mi.pages == 0 && decide (mi.type.limits.max = some 1) &&
        decide (mi.type.address = .i32)
    | none => false)

theorem ung_shape : growStore.funcs[2]?.map ungShape = some true := by decide +kernel

theorem unguardedB_eq {b : List Instr} (h : unguardedB b = true) :
    b = [.intConst .i32 1, .memoryGrow ⟨0⟩] := by
  unfold unguardedB at h
  split at h
  · rename_i x m
    have h' : x = 1 ∧ m = ⟨0⟩ := of_decide_eq_true h
    rw [h'.1, h'.2]
  · cases h

/-- A memory without pages, of at most one page, can grow by one page. -/
theorem grow?_isSome {mi : MemInst} (h₁ : mi.pages = 0) (h₂ : mi.type.limits.max = some 1)
    (h₃ : mi.type.address = .i32) : ∃ mi', mi.grow? 1 = some mi' := by
  unfold MemInst.grow?
  simp only [MemInst.pages] at h₁
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · rename_i hn
    exfalso
    refine hn ⟨?_, ?_⟩
    · rw [h₁, h₃]
      decide
    · intro j hj
      rw [h₂] at hj
      cases hj
      rw [h₁]
      decide

/-- What the shape check gives. -/
theorem ung_spec : ∃ fi fn ma mi, growStore.funcs[2]? = some fi ∧ fi.code = .wasm fn ∧
    fn.locals = [] ∧ fn.body = [.intConst .i32 1, .memoryGrow ⟨0⟩] ∧
    fi.type.funcType? = some ([], [.num (.int .i32)]) ∧
    growStore.mem? (Frame.forCall fi.module [] []) ⟨0⟩ = some (ma, mi) ∧ mi.pages = 0 ∧
    (∃ mi', mi.grow? 1 = some mi') := by
  rcases hfi : growStore.funcs[2]? with _ | fi
  · have h := ung_shape
    rw [hfi] at h
    cases h
  · have h := ung_shape
    rw [hfi] at h
    have hs : ungShape fi = true := Option.some.inj h
    rcases hc : fi.code with fn | hh
    · rcases hm : growStore.mem? (Frame.forCall fi.module [] []) ⟨0⟩ with _ | ⟨ma, mi⟩
      · simp [ungShape, hm] at hs
      · have hs' : (fn.locals = [] ∧ unguardedB fn.body = true) ∧
            fi.type.funcType? = some ([], [.num (.int .i32)]) ∧
            (ma = 0 ∧ mi.pages = 0 ∧ mi.type.limits.max = some 1) ∧ mi.type.address = .i32 := by
          simpa [ungShape, hc, hm, and_assoc] using hs
        exact ⟨fi, fn, ma, mi, rfl, hc, hs'.1.1, unguardedB_eq hs'.1.2, hs'.2.1, hm,
          hs'.2.2.1.2.1, grow?_isSome hs'.2.2.1.2.1 hs'.2.2.1.2.2 hs'.2.2.2⟩
    · simp [ungShape, hc] at hs

/-- **Function `2` returns `0` and also `-1`** at a profile with the specification's grow
policy: the unguarded `memory.grow` may succeed (the old size, `0`) or fail (`-1`). -/
theorem unguarded_runs {P : Profile} (hP : P.grow = .nondet) :
    (∃ s', Steps P Det.noHost (invoke growStore 2 []) ⟨s', {}, vals [Val.i32 0]⟩) ∧
      Steps P Det.noHost (invoke growStore 2 []) ⟨growStore, {}, vals [Val.i32 (BitVec.allOnes 32)]⟩ := by
  obtain ⟨fi, fn, ma, mi, hfi, hcode, hloc, hbody, hty, hm, hpg, mi', hg⟩ := ung_spec
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hty
  have hps0 : ps.length = 0 := by
    show ps.toList.length = 0
    rw [hps]
    rfl
  have hout : ∀ v : Val, [v].length = rs.length := by
    intro v
    show 1 = rs.toList.length
    rw [hrs]
    rfl
  have hm' : growStore.mem? (Frame.forCall fi.module [] fn.locals) ⟨0⟩ = some (ma, mi) := by
    rw [hloc]
    exact hm
  have hsucc : P.growMaySucceed .memory ma mi.pages 1 := by
    simp [Numerics.Profile.growMaySucceed, hP]
  have hfail : P.growMayFail .memory ma mi.pages 1 := by
    simp [Numerics.Profile.growMayFail, hP]
  have hcode₁ : expression fn.body = [aconst .i32 1, .plain (.memoryGrow ⟨0⟩)] := by
    rw [hbody]
    rfl
  constructor
  · show ∃ s', Steps P Det.noHost (invoke growStore 2 []) ⟨s', {}, vals [Val.i32 0]⟩
    have h₁ : Step P Det.noHost ⟨growStore, Frame.forCall fi.module [] fn.locals,
        [aconst .i32 1, .plain (.memoryGrow ⟨0⟩)]⟩
        ⟨growStore.setMem ma mi', Frame.forCall fi.module [] fn.locals,
          [aconst .i32 (BitVec.ofNat _ mi.pages)]⟩ :=
      .memory (.growSucceed (a := .i32) (n := (1 : BitVec 32)) hm' hg hsucc)
    have h₂ : Steps P Det.noHost
        ⟨growStore, Frame.forCall fi.module [] fn.locals, expression fn.body⟩
        ⟨growStore.setMem ma mi', Frame.forCall fi.module [] fn.locals, vals [Val.i32 0]⟩ := by
      rw [hcode₁]
      have h₃ := Relation.ReflTransGen.single h₁
      rw [hpg] at h₃
      exact h₃
    exact ⟨_, steps_invoke_nil hfi he hps0 hcode h₂ (hout _)⟩
  · show Steps P Det.noHost (invoke growStore 2 [])
      ⟨growStore, {}, vals [Val.i32 (BitVec.allOnes 32)]⟩
    have h₂ : Steps P Det.noHost
        ⟨growStore, Frame.forCall fi.module [] fn.locals, expression fn.body⟩
        ⟨growStore, Frame.forCall fi.module [] fn.locals, vals [Val.i32 (BitVec.allOnes 32)]⟩ := by
      rw [hcode₁]
      exact Relation.ReflTransGen.single
        (.memory (.growFail (a := .i32) (n := (1 : BitVec 32)) hm' (.inl hfail)))
    exact steps_invoke_nil hfi he hps0 hcode h₂ (hout _)

/-- Function `2` is invoked on no arguments. -/
theorem invokeOk_unguarded : InvokeOk growStore 2 [] := by
  obtain ⟨fi, -, -, -, hfi, -, -, -, hty, -, -, -⟩ := ung_spec
  obtain ⟨ps, rs, he, hps, -⟩ := expand_of_funcType? hty
  refine ⟨fi, ps, rs, hfi, he, ?_⟩
  rw [hps]
  exact .nil

end Silmaril.Proofs.Wasm.Det.GrowTrap.Litmus
