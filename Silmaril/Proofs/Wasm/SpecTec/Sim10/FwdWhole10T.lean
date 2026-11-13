module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLoadVal10T

/-!
# The forward 1.0 whole step in `simEnv10T`, under one invariant

Every forward leaf of rounds 2–4 now holds at `FwdAt10T` (`FwdLeaf10T` … `FwdLoadVal10T`), and the
store leaves are an earlier (`StoreAgree.fwdAt10T_storeLeaf`). This module puts them together:

* the plain-suffix wrappers (`fwdAt10T_labelBranchP`, …) and `fwdAt10T_pureR`: every pure step from
  `Plain10` code, the numeric ones from `NumAgree10`;
* `fwdAt10T_memoryGrow`, `fwdAt10T_store`: `memory.grow` and the four store constructors at
  `bytesB10`;
* **`fwd10T_step`**: every V1 step from a configuration with `Plain10` code, `GSetOk` and aligned
  memories satisfies `FwdAt10T` at `fwdB10 nd r`;
* **`wholeStepFwd10T_inv`**: so every such step between configurations whose images are typed
  in `simEnv10T` is a step of `simEnv10T (fwdB10 nd r)` between the images. The store may hold
  functions that store, and the code may store anywhere. This is round 4's `wholeStepFwd10`
  with `simEnv10` replaced by `simEnv10T`, without the union 's
  `wholeStepFwd10T_stores` (`wholeStepFwd10T_stores_of_inv`: its first branch is an instance,
  and so is its second wherever the invariant holds).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  result frameMemory frameTable setGlobal setMemory loadInt loadFloat storeInt storeFloat
  effectiveAddress expression asValue?)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst GlobalAddr FuncAddr MemAddr MemInst
  TableInst FuncInst ModuleInst Result)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)

variable {B : Builtins} {H : Type} {hn : H → String}

open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (frameMemory setMemory storeInt storeFloat effectiveAddress)
open Silmaril.Wasm.Execution.Runtime (MemAddr MemInst)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)
open Silmaril.Wasm.SpecTec.Sim10.StoreAgree (StoreLeaf10 fwdAt10T_storeLeaf)

/-- `br-zero` forward at `Plain10` code. -/
theorem fwdAt10T_labelBranchP (s : Store H) (f : Frame) {n : Nat} {cont : V1.Expr}
    {extra vs : List Execution.Runtime.Value} {tail : List Admin}
    (hpl : Plain10 [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail)])
    (hlen : vs.length = n) :
    FwdAt10T B hn ⟨s, f, [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail)]⟩
      ⟨s, f, values vs ++ expression cont⟩ := by
  have e : values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail =
      values (extra ++ vs) ++ .source (.br ⟨0⟩) :: tail := by simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.suffix (e ▸ hpl.label_body) rfl
  rw [his]
  exact fwdAt10T_labelBranch s f n cont extra vs is hlen

/-- `br-succ` forward at `Plain10` code. -/
theorem fwdAt10T_labelBranchOuterP (s : Store H) (f : Frame) {n : Nat} {cont : V1.Expr}
    {vs : List Execution.Runtime.Value} {tail : List Admin} {l : LabelIdx}
    (hpl : Plain10 [.label n cont (values vs ++ [.source (.br l)] ++ tail)]) (hl : l.toNat ≠ 0) :
    FwdAt10T B hn ⟨s, f, [.label n cont (values vs ++ [.source (.br l)] ++ tail)]⟩
      ⟨s, f, values vs ++ [.source (.br (V1.Execution.lowerLabel l))]⟩ := by
  have e : values vs ++ [.source (.br l)] ++ tail = values vs ++ .source (.br l) :: tail := by
    simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.suffix (e ▸ hpl.label_body) rfl
  rw [his]
  exact fwdAt10T_labelBranchOuter s f n cont vs is l hl

/-- `return-label` forward at `Plain10` code. -/
theorem fwdAt10T_labelReturnP (s : Store H) (f : Frame) {n : Nat} {cont : V1.Expr}
    {vs : List Execution.Runtime.Value} {tail : List Admin}
    (hpl : Plain10 [.label n cont (values vs ++ [.source .return_] ++ tail)]) :
    FwdAt10T B hn ⟨s, f, [.label n cont (values vs ++ [.source .return_] ++ tail)]⟩
      ⟨s, f, values vs ++ [.source .return_]⟩ := by
  have e : values vs ++ [.source .return_] ++ tail = values vs ++ .source .return_ :: tail := by
    simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.suffix (e ▸ hpl.label_body) rfl
  rw [his]
  exact fwdAt10T_labelReturn s f n cont vs is

/-- `return-frame` forward at `Plain10` code. -/
theorem fwdAt10T_frameReturnP (s : Store H) (f : Frame) {n : Nat} {fr : Frame}
    {extra vs : List Execution.Runtime.Value} {tail : List Admin}
    (hpl : Plain10 [.frame n fr (values extra ++ values vs ++ [.source .return_] ++ tail)])
    (hlen : vs.length = n) :
    FwdAt10T B hn ⟨s, f, [.frame n fr (values extra ++ values vs ++ [.source .return_] ++ tail)]⟩
      ⟨s, f, values vs⟩ := by
  have e : values extra ++ values vs ++ [.source .return_] ++ tail =
      values (extra ++ vs) ++ .source .return_ :: tail := by simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.suffix (e ▸ hpl.frame_body) rfl
  rw [his]
  exact fwdAt10T_frameReturn s f n fr extra vs is hlen

/-- `trap-vals` (V1's `trapValues`) forward at `Plain10` code. -/
theorem fwdAt10T_trapValuesP (s : Store H) (f : Frame) {v : Execution.Runtime.Value}
    {vs : List Execution.Runtime.Value} {tail : List Admin}
    (hpl : Plain10 (values (v :: vs) ++ [.trap] ++ tail)) :
    FwdAt10T B hn ⟨s, f, values (v :: vs) ++ [.trap] ++ tail⟩ ⟨s, f, [.trap]⟩ := by
  have e : values (v :: vs) ++ [.trap] ++ tail = values (v :: vs) ++ .trap :: tail := by simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source := Plain10.suffix (e ▸ hpl) rfl
  rw [his]
  exact fwdAt10T_trapValues s f v vs is

/-- `trap-vals` (V1's `trapTail`) forward at `Plain10` code. -/
theorem fwdAt10T_trapTailP (s : Store H) (f : Frame) {i : Admin} {tail : List Admin}
    (hpl : Plain10 (.trap :: i :: tail)) :
    FwdAt10T B hn ⟨s, f, .trap :: i :: tail⟩ ⟨s, f, [.trap]⟩ := by
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, i :: tail = is.map .source :=
    Plain10.suffix (ws := []) hpl rfl
  obtain ⟨j, js, -, hj, hjs⟩ := List.map_eq_cons_iff.1 his.symm
  rw [← hj, ← hjs]
  exact fwdAt10T_trapTail s f j js


/-! ## Every pure step -/

/-- **Every pure step from `Plain10` code satisfies `FwdAt10T`**, the numeric steps from
`NumAgree10` at the spec profile. -/
theorem fwdAt10T_pureR {nd : Bool} {r : RelaxedChoice}
    (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (s : Store H)
    (f : Frame) {before after : List Admin} (hp : PureStep before after) (hpl : Plain10 before) :
    FwdAt10T B hn ⟨s, f, before⟩ ⟨s, f, after⟩ := by
  cases hp with
  | nop => exact fwdAt10T_nop s f
  | unreachable => exact fwdAt10T_unreachable s f
  | drop v => exact fwdAt10T_drop s f v
  | selectZero a b _ => exact fwdAt10T_selectZero s f a b
  | selectNonzero a b _ c hc => exact fwdAt10T_selectNonzero s f a b c hc
  | block bt body => exact fwdAt10T_block s f bt body
  | loop bt body => exact fwdAt10T_loop s f bt body
  | ifZero bt l r => exact fwdAt10T_ifZero s f bt l r
  | ifNonzero bt l r c hc => exact fwdAt10T_ifNonzero s f bt l r c hc
  | brIfZero l => exact fwdAt10T_brIfZero s f l
  | brIfNonzero l c hc => exact fwdAt10T_brIfNonzero s f l c hc
  | brTable ls d c => exact fwdAt10T_brTable s f ls d c
  | labelDone n cont vs => exact fwdAt10T_labelDone s f n cont vs
  | labelBranch n cont extra vs tail hlen => exact fwdAt10T_labelBranchP s f hpl hlen
  | labelBranchOuter n cont vs tail l hl => exact fwdAt10T_labelBranchOuterP s f hpl hl
  | labelReturn n cont vs tail => exact fwdAt10T_labelReturnP s f hpl
  | frameDone n fr vs hlen => exact hlen ▸ fwdAt10T_frameDone s f fr vs
  | frameReturn n fr extra vs tail hlen => exact fwdAt10T_frameReturnP s f hpl hlen
  | trapValues v vs tail => exact fwdAt10T_trapValuesP s f hpl
  | trapTail i tail => exact fwdAt10T_trapTailP s f hpl
  | labelTrap n cont => exact fwdAt10T_labelTrap s f n cont
  | frameTrap n fr => exact fwdAt10T_frameTrap s f fr n
  | localTee i v => exact fwdAt10T_localTee s f i v
  | intUnary t op x => exact fwdAt10T_num A s f (.intUnary t op x)
  | intBinary t op x y z h => exact fwdAt10T_num A s f (.intBinary t op x y z h)
  | intBinaryTrap t op x y e h => exact fwdAt10T_num A s f (.intBinaryTrap t op x y e h)
  | intTest t op x => exact fwdAt10T_num A s f (.intTest t op x)
  | intRel t op x y => exact fwdAt10T_num A s f (.intRel t op x y)
  | floatUnary t op x y h => exact fwdAt10T_num A s f (.floatUnary t op x y h)
  | floatBinary t op x y z h => exact fwdAt10T_num A s f (.floatBinary t op x y z h)
  | floatRel t op x y => exact fwdAt10T_num A s f (.floatRel t op x y)
  | convert op x y h => exact fwdAt10T_num A s f (.convert op x y h)
  | convertTrap op x e h => exact fwdAt10T_num A s f (.convertTrap op x e h)

/-! ## `memory.grow` and the stores at `bytesB10` -/

/-- **`memory.grow` forward at `bytesB10`**, succeeding or failing. -/
theorem fwdAt10T_memoryGrow {P : Profile} (s : Store H) (f : Frame) (a : MemAddr)
    (m : MemInst) (c r : BitVec 32) (bytes : Execution.Memory.Bytes)
    (hm : frameMemory s f = some (a, m)) (hg : Execution.Memory.Grow m.data m.max c.toNat bytes r) :
    FwdAt10T (bytesB10 P) hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
      ⟨setMemory s a {m with data := bytes}, f, [value (.int .i32 r)]⟩ := by
  cases hg with
  | success _ h => exact fwdAt10T_memGrowSucceed_bytesB10 s f a m c _ hm h
  | failure => exact fwdAt10T_memGrowFail s f a m c hm

/-- An integer store forward at `bytesB10`, packed or not (an earlier store leaves). -/
theorem fwdAt10T_intStore {P : Profile} (s : Store H) (f : Frame) (t : IntType)
    (p : Option V1.PackSize) (arg : V1.MemArg) (c : BitVec 32) (x : BitVec t.width) (a : MemAddr)
    (m : MemInst) (b : Execution.Memory.Bytes) (hm : frameMemory s f = some (a, m))
    (hs : storeInt t p m.data (effectiveAddress c arg) x = some b) :
    FwdAt10T (bytesB10 P) hn ⟨s, f, [value (.int .i32 c), value (.int t x),
      .source (.intStore t p arg)]⟩ ⟨setMemory s a {m with data := b}, f, []⟩ := by
  cases p with
  | none => exact fwdAt10T_storeLeaf (.intStore s f t arg c x a m b hm hs)
  | some sz => exact fwdAt10T_storeLeaf (.intStorePack s f t sz arg c x a m b hm hs)

/-! ## Every step -/

/-- **The forward 1.0 half in `simEnv10T`, leaf by leaf**: every V1 step from a configuration
with `Plain10` code, `GSetOk` and aligned memories satisfies `FwdAt10T` at `fwdB10 nd r`. -/
theorem fwd10T_step {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice} {c c' : Config H}
    (h : Step host c c') (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code)
    (hal : MemsAligned10 c.store) : FwdAt10T (fwdB10 nd r) hn c c' := by
  induction h with
  | pure s f hp => exact fwdAt10T_pureR (numAgree10_bytesB10 _) s f hp hpl
  | context hs vs tail ih =>
    exact fwdAt10_contextT (ih (Plain10.mid hpl hs.firstRedex_ne_none).1 (gsetOk_mid hg) hal)
      vs tail
  | label _ n cont ih => exact fwdAt10_labelT (ih hpl.label_body (gsetOk_label hg) hal) n cont
  | frame _ n outer ih => exact fwdAt10_frameT (ih hpl.frame_body (gsetOk_frame hg) hal) n outer
  | localGet s f i v hv => exact fwdAt10T_localGet s f i v hv
  | localSet s f i v old hv => exact fwdAt10T_localSet s f i v old hv
  | globalGet s f i a g h₁ h₂ => exact fwdAt10T_globalGet s f i a g h₁ h₂
  | globalSet s f i a g v h₁ h₂ _ =>
    exact fwdAt10T_globalSet s f i a g v h₁ h₂ (gsetOk_redex hg h₁ h₂)
  | call s f i a h₁ => exact fwdAt10T_call s f i a h₁
  | callIndirect s f i c t a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact fwdAt10T_callIndirect s f i c t a fn ft h₁ h₂ h₃ h₄ h₅
  | callIndirectBounds s f i c t h₁ h₂ => exact fwdAt10T_callIndirectBounds s f i c t h₁ h₂
  | callIndirectNull s f i c t h₁ h₂ => exact fwdAt10T_callIndirectNull s f i c t h₁ h₂
  | callIndirectType s f i c t a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact fwdAt10T_callIndirectType s f i c t a fn ft h₁ h₂ h₃ h₄ h₅
  | invokeWasm s f a ft m fn args h₁ h₂ _ => exact fwdAt10T_invokeWasm s f a ft m fn args h₁ h₂
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact fwdAt10T_invokeHost s s' f a ft fn args r h₁
  | invokeHostDiverges s f a ft fn args h₁ _ _ =>
    exact fwdAt10T_invokeHostDiverges s f a ft fn args h₁
  | intLoad s f t p arg c a m v h₁ h₂ => exact fwdAt10T_intLoad_bytesB10 s f t p arg c a m v h₁ h₂
  | intLoadTrap s f t p arg c a m h₁ h₂ => exact fwdAt10T_intLoadTrap s f t p arg c a m h₁ h₂
  | floatLoad s f t arg c a m v h₁ h₂ => exact fwdAt10T_floatLoad_bytesB10 s f t arg c a m v h₁ h₂
  | floatLoadTrap s f t arg c a m h₁ h₂ => exact fwdAt10T_floatLoadTrap s f t arg c a m h₁ h₂
  | intStore s f t p arg c x a m b h₁ h₂ => exact fwdAt10T_intStore s f t p arg c x a m b h₁ h₂
  | intStoreTrap s f t p arg c x a m h₁ h₂ =>
    exact fwdAt10T_storeLeaf (.intStoreTrap s f t p arg c x a m h₁ h₂)
  | floatStore s f t arg c x a m b h₁ h₂ =>
    exact fwdAt10T_storeLeaf (.floatStore s f t arg c x a m b h₁ h₂)
  | floatStoreTrap s f t arg c x a m h₁ h₂ =>
    exact fwdAt10T_storeLeaf (.floatStoreTrap s f t arg c x a m h₁ h₂)
  | memorySize s f a m h₁ => exact fwdAt10T_memorySize s f a m h₁ (hal.frame h₁)
  | memoryGrow s f a m c r b h₁ h₂ => exact fwdAt10T_memoryGrow s f a m c r b h₁ h₂

/-- **The forward 1.0 whole step in `simEnv10T`, under one invariant**: every V1 step from a
configuration with `Plain10` code, `GSetOk` and aligned memories, between configurations whose
images are typed in `simEnv10T`, is a step of `simEnv10T (fwdB10 nd r)` between the images. -/
theorem wholeStepFwd10T_inv {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (hc : Typed10 (simEnv10T (fwdB10 nd r)) hn c)
    (hc' : Typed10 (simEnv10T (fwdB10 nd r)) hn c') (hpl : Plain10 c.code)
    (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store) (h : Step host c c') :
    SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) (configV hn c') :=
  fwd10T_step h hpl hg hal (typedV_state_of_typed10T hc) (typedV_state_of_typed10T hc')
    (typedV_code_of_typed10T hc) (typedV_code_of_typed10T hc')

/-- **an earlier union, from the one invariant**: the first branch of `wholeStepFwd10T_stores`
(typed in `simEnv10`) is an instance of `wholeStepFwd10T_inv`, by subject reduction in `simEnv10`
and growth to `simEnv10T`; so is the second (a nested store, typed in `simEnv10T`) wherever the
invariant holds. -/
theorem wholeStepFwd10T_stores_of_inv {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    {c c' : Config H} (h : Step host c c')
    (hg : (Typed10 (simEnv10 (fwdB10 nd r)) hn c ∧ Plain10 c.code ∧
        GSetOk c.store c.frame c.code ∧ MemsAligned10 c.store) ∨
      (Typed10 (simEnv10T (fwdB10 nd r)) hn c ∧ Typed10 (simEnv10T (fwdB10 nd r)) hn c' ∧
        Plain10 c.code ∧ GSetOk c.store c.frame c.code ∧ MemsAligned10 c.store)) :
    SStepB (simEnv10T (fwdB10 nd r)) (configV hn c) (configV hn c') := by
  rcases hg with ⟨hc, hpl, hgs, hal⟩ | ⟨hc, hc', hpl, hgs, hal⟩
  · exact wholeStepFwd10T_inv (StoreAgree.typed10T_of_typed10 hc)
      (StoreAgree.typed10T_of_typed10 (typed10_step' h hc hgs)) hpl hgs hal h
  · exact wholeStepFwd10T_inv hc hc' hpl hgs hal h

end Silmaril.Wasm.SpecTec.Sim10.Whole
