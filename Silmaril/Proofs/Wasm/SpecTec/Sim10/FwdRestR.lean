module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdCallAddr

/-!
# The forward 1.0 half: what is left after round 3, pass 3

Pass 2 left twelve obligations (`FwdRestQ10`). This pass proves, at every builtins:

* `br_table` (`FwdTable.fwdAt10_brTable`) and the four `call_indirect` cases
  (`fwdAt10_callIndirect`, `…Bounds`, `…Null`, `…Type`);
* `call_addr` of a Wasm function (`FwdCallAddr.fwdAt10_invokeWasm`);
* both load traps (`FwdMem.fwdAt10_intLoadTrap`, `fwdAt10_floatLoadTrap`);
* `memory.grow` when it fails (`fwdAt10_memGrowFail`);
* `memory.size` **at a page-aligned memory of fewer than `2^32` pages** (`fwdAt10_memorySize`).
  The unrestricted field is expected to be false (V1 rounds the page count down, the script's
  premise `n * 64 * $Ki = |bytes|` needs a whole number of pages); this pass does not prove that
  refutation. It restates the field under the store invariant `MemsAligned10`.

**`FwdRestR10 B hn`** collects the three obligations still open: successful integer and float
loads and `memory.grow` when it succeeds. None of them can hold at the spec's builtins `floatIntB`:
1.0's `$bytes_`, `$ibytes_` and `$growmemory` are answered by the builtins, and `floatIntB` answers
none of them (round 2). `FwdBytes` defines builtins that answer them.

**`wholeStepFwd10_of_restR`**: given `NumAgree10` at the spec profile and `FwdRestR10`, every V1
step between configurations whose images are typed, from one satisfying `Plain10`, `GSetOk` and
`MemsAligned10`, is a step of the 1.0 script between the images.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  result frameMemory frameTable setGlobal setMemory loadInt loadFloat storeInt storeFloat
  effectiveAddress expression)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst GlobalAddr FuncAddr MemAddr MemInst
  TableInst FuncInst ModuleInst Result)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim10 (GSetOk)

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## The store invariant -/

/-- Every memory of the store is page-aligned and has fewer than `2^32` pages. -/
def MemsAligned10 (s : Store H) : Prop := ∀ m ∈ s.memories, MemAligned10 m

/-- The frame's memory of an aligned store is aligned. -/
theorem MemsAligned10.frame {s : Store H} (hal : MemsAligned10 s) {f : Frame} {a : MemAddr}
    {m : MemInst} (hm : frameMemory s f = some (a, m)) : MemAligned10 m :=
  hal m (List.mem_of_getElem? (frameMemory_some hm).2)

/-! ## What is left -/

/-- **The forward obligations still open after pass 3** (3 of them). -/
structure FwdRestR10 (B : Builtins) (hn : H → String) : Prop where
  intLoad : ∀ (s : Store H) (f : Frame) (t : IntType) (packed : Option (V1.PackSize × Signedness))
    (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value),
      frameMemory s f = some (a, m) → loadInt t packed m.data (effectiveAddress c arg) = some v →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ ⟨s, f, [value v]⟩
  floatLoad : ∀ (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
    (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value), frameMemory s f = some (a, m) →
      loadFloat t m.data (effectiveAddress c arg) = some v →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [value v]⟩
  memoryGrowSucceed : ∀ (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst) (c : BitVec 32)
    (bytes : Execution.Memory.Bytes), frameMemory s f = some (a, m) →
      Execution.Memory.grow? m.data m.max c.toNat = some bytes →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
        ⟨setMemory s a {m with data := bytes},
          f, [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩

/-- `memory.grow` forward, by `grow-succeed` (open) or `grow-fail` (proved). -/
theorem fwdAt10_memoryGrow (R : FwdRestR10 B hn) (s : Store H) (f : Frame) (a : MemAddr)
    (m : MemInst) (c r : BitVec 32) (bytes : Execution.Memory.Bytes)
    (hm : frameMemory s f = some (a, m)) (hg : Execution.Memory.Grow m.data m.max c.toNat bytes r) :
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
      ⟨setMemory s a {m with data := bytes}, f, [value (.int .i32 r)]⟩ := by
  cases hg with
  | success _ h => exact R.memoryGrowSucceed s f a m c _ hm h
  | failure => exact fwdAt10_memGrowFail s f a m c hm

/-! ## Every pure step -/

/-- **Every pure step from `Plain10` code satisfies `FwdAt10`**, the numeric steps from
`NumAgree10` at the spec profile. -/
theorem fwdAt10_pureR {nd : Bool} {r : RelaxedChoice}
    (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (s : Store H)
    (f : Frame) {before after : List Admin} (hp : PureStep before after) (hpl : Plain10 before) :
    FwdAt10 B hn ⟨s, f, before⟩ ⟨s, f, after⟩ := by
  cases hp with
  | nop => exact fwdAt10_nop s f
  | unreachable => exact fwdAt10_unreachable s f
  | drop v => exact fwdAt10_drop s f v
  | selectZero a b _ => exact fwdAt10_selectZero s f a b
  | selectNonzero a b _ c hc => exact fwdAt10_selectNonzero s f a b c hc
  | block bt body => exact fwdAt10_block s f bt body
  | loop bt body => exact fwdAt10_loop s f bt body
  | ifZero bt l r => exact fwdAt10_ifZero s f bt l r
  | ifNonzero bt l r c hc => exact fwdAt10_ifNonzero s f bt l r c hc
  | brIfZero l => exact fwdAt10_brIfZero s f l
  | brIfNonzero l c hc => exact fwdAt10_brIfNonzero s f l c hc
  | brTable ls d c => exact fwdAt10_brTable s f ls d c
  | labelDone n cont vs => exact fwdAt10_labelDone s f n cont vs
  | labelBranch n cont extra vs tail hlen => exact fwdAt10_labelBranchP s f hpl hlen
  | labelBranchOuter n cont vs tail l hl => exact fwdAt10_labelBranchOuterP s f hpl hl
  | labelReturn n cont vs tail => exact fwdAt10_labelReturnP s f hpl
  | frameDone n fr vs hlen => exact hlen ▸ fwdAt10_frameDone s f fr vs
  | frameReturn n fr extra vs tail hlen => exact fwdAt10_frameReturnP s f hpl hlen
  | trapValues v vs tail => exact fwdAt10_trapValuesP s f hpl
  | trapTail i tail => exact fwdAt10_trapTailP s f hpl
  | labelTrap n cont => exact fwdAt10_labelTrap s f n cont
  | frameTrap n fr => exact fwdAt10_frameTrap s f fr n
  | localTee i v => exact fwdAt10_localTee s f i v
  | intUnary t op x => exact fwdAt10_num A s f (.intUnary t op x)
  | intBinary t op x y z h => exact fwdAt10_num A s f (.intBinary t op x y z h)
  | intBinaryTrap t op x y e h => exact fwdAt10_num A s f (.intBinaryTrap t op x y e h)
  | intTest t op x => exact fwdAt10_num A s f (.intTest t op x)
  | intRel t op x y => exact fwdAt10_num A s f (.intRel t op x y)
  | floatUnary t op x y h => exact fwdAt10_num A s f (.floatUnary t op x y h)
  | floatBinary t op x y z h => exact fwdAt10_num A s f (.floatBinary t op x y z h)
  | floatRel t op x y => exact fwdAt10_num A s f (.floatRel t op x y)
  | convert op x y h => exact fwdAt10_num A s f (.convert op x y h)
  | convertTrap op x e h => exact fwdAt10_num A s f (.convertTrap op x e h)

/-! ## Every step -/

/-- **The forward 1.0 half under the invariants**: under `NumAgree10` at the spec profile and
`FwdRestR10`, every V1 step from a configuration whose code is `Plain10`, which satisfies `GSetOk`,
and whose memories are aligned, satisfies `FwdAt10`. -/
theorem fwd10_of_restR {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (R : FwdRestR10 B hn) {c c' : Config H}
    (h : Step host c c') (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code)
    (hal : MemsAligned10 c.store) : FwdAt10 B hn c c' := by
  induction h with
  | pure s f hp => exact fwdAt10_pureR A s f hp hpl
  | context hs vs tail ih =>
    exact fwdAt10_context (ih (Plain10.mid hpl hs.firstRedex_ne_none).1 (gsetOk_mid hg) hal)
      vs tail
  | label _ n cont ih => exact fwdAt10_label (ih hpl.label_body (gsetOk_label hg) hal) n cont
  | frame _ n outer ih => exact fwdAt10_frame (ih hpl.frame_body (gsetOk_frame hg) hal) n outer
  | localGet s f i v hv => exact fwdAt10_localGet s f i v hv
  | localSet s f i v old hv => exact fwdAt10_localSet s f i v old hv
  | globalGet s f i a g h₁ h₂ => exact fwdAt10_globalGet s f i a g h₁ h₂
  | globalSet s f i a g v h₁ h₂ _ =>
    exact fwdAt10_globalSet s f i a g v h₁ h₂ (gsetOk_redex hg h₁ h₂)
  | call s f i a h₁ => exact fwdAt10_call s f i a h₁
  | callIndirect s f i c t a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact fwdAt10_callIndirect s f i c t a fn ft h₁ h₂ h₃ h₄ h₅
  | callIndirectBounds s f i c t h₁ h₂ => exact fwdAt10_callIndirectBounds s f i c t h₁ h₂
  | callIndirectNull s f i c t h₁ h₂ => exact fwdAt10_callIndirectNull s f i c t h₁ h₂
  | callIndirectType s f i c t a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact fwdAt10_callIndirectType s f i c t a fn ft h₁ h₂ h₃ h₄ h₅
  | invokeWasm s f a ft m fn args h₁ h₂ _ => exact fwdAt10_invokeWasm s f a ft m fn args h₁ h₂
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact fwdAt10_invokeHost s s' f a ft fn args r h₁
  | invokeHostDiverges s f a ft fn args h₁ _ _ =>
    exact fwdAt10_invokeHostDiverges s f a ft fn args h₁
  | intLoad s f t p arg c a m v h₁ h₂ => exact R.intLoad s f t p arg c a m v h₁ h₂
  | intLoadTrap s f t p arg c a m h₁ h₂ => exact fwdAt10_intLoadTrap s f t p arg c a m h₁ h₂
  | floatLoad s f t arg c a m v h₁ h₂ => exact R.floatLoad s f t arg c a m v h₁ h₂
  | floatLoadTrap s f t arg c a m h₁ h₂ => exact fwdAt10_floatLoadTrap s f t arg c a m h₁ h₂
  | intStore s f t p arg c x a m b h₁ h₂ => exact fwdAt10_intStore s f t p arg c x _ _
  | intStoreTrap s f t p arg c x a m h₁ h₂ => exact fwdAt10_intStore s f t p arg c x _ _
  | floatStore s f t arg c x a m b h₁ h₂ => exact fwdAt10_floatStore s f t arg c x _ _
  | floatStoreTrap s f t arg c x a m h₁ h₂ => exact fwdAt10_floatStore s f t arg c x _ _
  | memorySize s f a m h₁ => exact fwdAt10_memorySize s f a m h₁ (hal.frame h₁)
  | memoryGrow s f a m c r b h₁ h₂ => exact fwdAt10_memoryGrow R s f a m c r b h₁ h₂

/-- **The forward 1.0 half on typed images, under the invariants**, at builtins that agree with
the spec's numerics. -/
theorem wholeStepFwd10_of_restR {host : HostSemantics H} {nd : Bool} {r : RelaxedChoice}
    (A : NumAgree10 (simEnv10 B) (Profile.spec nd r)) (R : FwdRestR10 B hn) {c c' : Config H}
    (hc : Typed10 (simEnv10 B) hn c) (hc' : Typed10 (simEnv10 B) hn c')
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store)
    (h : Step host c c') : SStepB (simEnv10 B) (configV hn c) (configV hn c') :=
  fwd10_of_restR A R h hpl hg hal (typedV_state_of_typed10 hc) (typedV_state_of_typed10 hc')
    (typedV_code_of_typed10 hc) (typedV_code_of_typed10 hc')

/-- **At the spec's builtins**: `wholeStepFwd10_of_restR` at `floatIntB (Profile.spec nd r)`. -/
theorem wholeStepFwd10_of_restR_floatIntB {host : HostSemantics H} {nd : Bool}
    {r : RelaxedChoice} (R : FwdRestR10 (Sim.Floats.floatIntB (Profile.spec nd r)) hn)
    {c c' : Config H} (hc : Typed10 (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c)
    (hc' : Typed10 (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) hn c')
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (hal : MemsAligned10 c.store)
    (h : Step host c c') :
    SStepB (simEnv10 (Sim.Floats.floatIntB (Profile.spec nd r))) (configV hn c) (configV hn c') :=
  wholeStepFwd10_of_restR numAgree10_floatIntB R hc hc' hpl hg hal h

end Silmaril.Wasm.SpecTec.Sim10.Whole
