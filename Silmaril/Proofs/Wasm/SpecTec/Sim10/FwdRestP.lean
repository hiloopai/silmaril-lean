module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdBlock

/-!
# The forward 1.0 half under the reachability invariant: what is left

`FwdRest10` (pass 1) asked for 18 non-structural constructors of V1's `Step` and for `pure` off
the sixteen-leaf fragment. Under the invariant `Plain10 c.code ∧ GSetOk c.store c.frame c.code`
(code after a redex is plain, and `global.set` writes a value of its global's type), this module
discharges, at every builtins:

* `global.set` (`fwdAt10_globalSet`, with `GSetOk`);
* the two host-call leaves (`fwdAt10_invokeHost`, `fwdAt10_invokeHostDiverges`, vacuous: a typed
  state has no host function);
* the pure rules `block`, `loop`, `if-*`, `br-zero`, `br-succ`, `return-label`,
  `return-frame`, `trap-vals` (both V1 forms), on top of pass 1's sixteen leaves
  (`fwdAt10_pureP`).

**`FwdRestP10 B hn host`** collects what is still open: `br_table`, the ten numeric `PureStep`
constructors, the four `call_indirect` cases, `call_addr` of a wasm function (`invokeWasm`),
the eight load/store cases, `memory.size` and `memory.grow`. **`fwd10_of_restP`**: under
`FwdRestP10`, every V1 step from a configuration satisfying the invariant satisfies `FwdAt10`.
`plain10_step` (in `PlainInv`) shows the first half of the invariant holds along every run from
an invocation; `GSetOk` is part of round 2's `GoodV1`, which validation guarantees.
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

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## The open obligations -/

/-- `before → after` is one of V1's ten numeric `PureStep`s, with V1's premises. -/
inductive NumStep10 : List Admin → List Admin → Prop where
  | intUnary (t : IntType) (op : V1.IntUnOp) (x : BitVec t.width) :
      NumStep10 [value (.int t x), .source (.intUnOp t op)]
        [value (.int t (Numerics.intUnOp t op.toCore x))]
  | intBinary (t : IntType) (op : IntBinOp) (x y z : BitVec t.width)
      (h : Numerics.intBinOp t op x y = .ok z) :
      NumStep10 [value (.int t x), value (.int t y), .source (.intBinOp t op)] [value (.int t z)]
  | intBinaryTrap (t : IntType) (op : IntBinOp) (x y : BitVec t.width) (err : Numerics.IntTrap)
      (h : Numerics.intBinOp t op x y = .error err) :
      NumStep10 [value (.int t x), value (.int t y), .source (.intBinOp t op)] [.trap]
  | intTest (t : IntType) (op : IntTestOp) (x : BitVec t.width) :
      NumStep10 [value (.int t x), .source (.intTestOp t op)]
        [value (.int .i32 (Numerics.intTestOp t op x))]
  | intRel (t : IntType) (op : IntRelOp) (x y : BitVec t.width) :
      NumStep10 [value (.int t x), value (.int t y), .source (.intRelOp t op)]
        [value (.int .i32 (Numerics.intRelOp t op x y))]
  | floatUnary (t : FloatType) (op : FloatUnOp) (x y : BitVec t.width)
      (h : Numerics.floatUnOpRel t op x y) :
      NumStep10 [value (.float t x), .source (.floatUnOp t op)] [value (.float t y)]
  | floatBinary (t : FloatType) (op : FloatBinOp) (x y z : BitVec t.width)
      (h : Numerics.floatBinOpRel t op x y z) :
      NumStep10 [value (.float t x), value (.float t y), .source (.floatBinOp t op)]
        [value (.float t z)]
  | floatRel (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width) :
      NumStep10 [value (.float t x), value (.float t y), .source (.floatRelOp t op)]
        [value (.int .i32 (Numerics.floatRelOp t op x y))]
  | convert (op : V1.ConvertOp) (x : Numerics.NumValue op.toCore.source)
      (y : Numerics.NumValue op.toCore.target) (h : Numerics.convertRel op.toCore x (.ok y)) :
      NumStep10 [value ⟨op.toCore.source, x⟩, .source (.convert op)] [value ⟨op.toCore.target, y⟩]
  | convertTrap (op : V1.ConvertOp) (x : Numerics.NumValue op.toCore.source)
      (err : Numerics.FloatTrap) (h : Numerics.convertRel op.toCore x (.error err)) :
      NumStep10 [value ⟨op.toCore.source, x⟩, .source (.convert op)] [.trap]

/-- **The forward obligations still open under the invariant** (26 of them). -/
structure FwdRestP10 (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  brTable : ∀ (s : Store H) (f : Frame) (ls : List LabelIdx) (d : LabelIdx) (c : BitVec 32),
    FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.brTable ls d)]⟩
      ⟨s, f, [.source (.br (ls[c.toNat]?.getD d))]⟩
  numeric : ∀ (s : Store H) (f : Frame) (before after : List Admin), NumStep10 before after →
    FwdAt10 B hn ⟨s, f, before⟩ ⟨s, f, after⟩
  callIndirect : ∀ (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32) (table : TableInst)
    (a : FuncAddr) (fn : FuncInst V1.Func H) (ft : V1.FuncType), frameTable s f = some table →
      f.module.types[i.toNat]? = some ft → table.refs[c.toNat]? = some (some a) →
      s.funcs[a.value]? = some fn → fn.type = ft →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.invoke a]⟩
  callIndirectBounds : ∀ (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32)
    (table : TableInst), frameTable s f = some table → table.refs[c.toNat]? = none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  callIndirectNull : ∀ (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32)
    (table : TableInst), frameTable s f = some table → table.refs[c.toNat]? = some none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  callIndirectType : ∀ (s : Store H) (f : Frame) (i : TypeIdx) (c : BitVec 32) (table : TableInst)
    (a : FuncAddr) (fn : FuncInst V1.Func H) (ft : V1.FuncType), frameTable s f = some table →
      f.module.types[i.toNat]? = some ft → table.refs[c.toNat]? = some (some a) →
      s.funcs[a.value]? = some fn → fn.type ≠ ft →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ ⟨s, f, [.trap]⟩
  invokeWasm : ∀ (s : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType) (module : ModuleInst)
    (fn : V1.Func) (args : List Execution.Runtime.Value),
      s.funcs[a.value]? = some (.wasm ft module fn) → args.length = ft.params.length →
      ft.results.length ≤ 1 →
      FwdAt10 B hn ⟨s, f, values args ++ [.invoke a]⟩
        ⟨s, f, [.frame ft.results.length ⟨args ++ fn.locals.map Execution.Runtime.Value.zero,
          module⟩ [.label ft.results.length [] (expression fn.body)]]⟩
  intLoad : ∀ (s : Store H) (f : Frame) (t : IntType) (packed : Option (V1.PackSize × Signedness))
    (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value),
      frameMemory s f = some (a, m) → loadInt t packed m.data (effectiveAddress c arg) = some v →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ ⟨s, f, [value v]⟩
  intLoadTrap : ∀ (s : Store H) (f : Frame) (t : IntType)
    (packed : Option (V1.PackSize × Signedness)) (arg : V1.MemArg) (c : BitVec 32) (a : MemAddr)
    (m : MemInst), frameMemory s f = some (a, m) →
      loadInt t packed m.data (effectiveAddress c arg) = none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.intLoad t packed arg)]⟩ ⟨s, f, [.trap]⟩
  floatLoad : ∀ (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
    (a : MemAddr) (m : MemInst) (v : Execution.Runtime.Value), frameMemory s f = some (a, m) →
      loadFloat t m.data (effectiveAddress c arg) = some v →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [value v]⟩
  floatLoadTrap : ∀ (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
    (a : MemAddr) (m : MemInst), frameMemory s f = some (a, m) →
      loadFloat t m.data (effectiveAddress c arg) = none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source (.floatLoad t arg)]⟩ ⟨s, f, [.trap]⟩
  intStore : ∀ (s : Store H) (f : Frame) (t : IntType) (packed : Option V1.PackSize) (arg : V1.MemArg)
    (c : BitVec 32) (x : BitVec t.width) (a : MemAddr) (m : MemInst) (bytes : Execution.Memory.Bytes),
      frameMemory s f = some (a, m) →
      storeInt t packed m.data (effectiveAddress c arg) x = some bytes →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t packed arg)]⟩
        ⟨setMemory s a {m with data := bytes}, f, []⟩
  intStoreTrap : ∀ (s : Store H) (f : Frame) (t : IntType) (packed : Option V1.PackSize)
    (arg : V1.MemArg) (c : BitVec 32) (x : BitVec t.width) (a : MemAddr) (m : MemInst),
      frameMemory s f = some (a, m) → storeInt t packed m.data (effectiveAddress c arg) x = none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), value (.int t x), .source (.intStore t packed arg)]⟩
        ⟨s, f, [.trap]⟩
  floatStore : ∀ (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
    (x : BitVec t.width) (a : MemAddr) (m : MemInst) (bytes : Execution.Memory.Bytes),
      frameMemory s f = some (a, m) →
      storeFloat t m.data (effectiveAddress c arg) x = some bytes →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩
        ⟨setMemory s a {m with data := bytes}, f, []⟩
  floatStoreTrap : ∀ (s : Store H) (f : Frame) (t : FloatType) (arg : V1.MemArg) (c : BitVec 32)
    (x : BitVec t.width) (a : MemAddr) (m : MemInst), frameMemory s f = some (a, m) →
      storeFloat t m.data (effectiveAddress c arg) x = none →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), value (.float t x), .source (.floatStore t arg)]⟩
        ⟨s, f, [.trap]⟩
  memorySize : ∀ (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst),
    frameMemory s f = some (a, m) → FwdAt10 B hn ⟨s, f, [.source .memorySize]⟩
      ⟨s, f, [value (.int .i32 (BitVec.ofNat 32 (Execution.Memory.size m.data)))]⟩
  memoryGrow : ∀ (s : Store H) (f : Frame) (a : MemAddr) (m : MemInst) (c r : BitVec 32)
    (bytes : Execution.Memory.Bytes), frameMemory s f = some (a, m) →
      Execution.Memory.Grow m.data m.max c.toNat bytes r →
      FwdAt10 B hn ⟨s, f, [value (.int .i32 c), .source .memoryGrow]⟩
        ⟨setMemory s a {m with data := bytes}, f, [value (.int .i32 r)]⟩

/-! ## The pure rules -/

/-- The suffix after a non-value redex of `Plain10` code is plain. -/
theorem Plain10.suffix {ws : List Execution.Runtime.Value} {x : Admin} {rest : List Admin}
    (h : Plain10 (values ws ++ x :: rest)) (hx : asValue? x = none) :
    ∃ is : List V1.Instr, rest = is.map .source :=
  (h.split hx).1

/-- `br-zero` forward at `Plain10` code. -/
theorem fwdAt10_labelBranchP (s : Store H) (f : Frame) {n : Nat} {cont : V1.Expr}
    {extra vs : List Execution.Runtime.Value} {tail : List Admin}
    (hpl : Plain10 [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail)])
    (hlen : vs.length = n) :
    FwdAt10 B hn ⟨s, f, [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail)]⟩
      ⟨s, f, values vs ++ expression cont⟩ := by
  have e : values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail =
      values (extra ++ vs) ++ .source (.br ⟨0⟩) :: tail := by simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.suffix (e ▸ hpl.label_body) rfl
  rw [his]
  exact fwdAt10_labelBranch s f n cont extra vs is hlen

/-- `br-succ` forward at `Plain10` code. -/
theorem fwdAt10_labelBranchOuterP (s : Store H) (f : Frame) {n : Nat} {cont : V1.Expr}
    {vs : List Execution.Runtime.Value} {tail : List Admin} {l : LabelIdx}
    (hpl : Plain10 [.label n cont (values vs ++ [.source (.br l)] ++ tail)]) (hl : l.toNat ≠ 0) :
    FwdAt10 B hn ⟨s, f, [.label n cont (values vs ++ [.source (.br l)] ++ tail)]⟩
      ⟨s, f, values vs ++ [.source (.br (V1.Execution.lowerLabel l))]⟩ := by
  have e : values vs ++ [.source (.br l)] ++ tail = values vs ++ .source (.br l) :: tail := by
    simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.suffix (e ▸ hpl.label_body) rfl
  rw [his]
  exact fwdAt10_labelBranchOuter s f n cont vs is l hl

/-- `return-label` forward at `Plain10` code. -/
theorem fwdAt10_labelReturnP (s : Store H) (f : Frame) {n : Nat} {cont : V1.Expr}
    {vs : List Execution.Runtime.Value} {tail : List Admin}
    (hpl : Plain10 [.label n cont (values vs ++ [.source .return_] ++ tail)]) :
    FwdAt10 B hn ⟨s, f, [.label n cont (values vs ++ [.source .return_] ++ tail)]⟩
      ⟨s, f, values vs ++ [.source .return_]⟩ := by
  have e : values vs ++ [.source .return_] ++ tail = values vs ++ .source .return_ :: tail := by
    simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.suffix (e ▸ hpl.label_body) rfl
  rw [his]
  exact fwdAt10_labelReturn s f n cont vs is

/-- `return-frame` forward at `Plain10` code. -/
theorem fwdAt10_frameReturnP (s : Store H) (f : Frame) {n : Nat} {fr : Frame}
    {extra vs : List Execution.Runtime.Value} {tail : List Admin}
    (hpl : Plain10 [.frame n fr (values extra ++ values vs ++ [.source .return_] ++ tail)])
    (hlen : vs.length = n) :
    FwdAt10 B hn ⟨s, f, [.frame n fr (values extra ++ values vs ++ [.source .return_] ++ tail)]⟩
      ⟨s, f, values vs⟩ := by
  have e : values extra ++ values vs ++ [.source .return_] ++ tail =
      values (extra ++ vs) ++ .source .return_ :: tail := by simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source :=
    Plain10.suffix (e ▸ hpl.frame_body) rfl
  rw [his]
  exact fwdAt10_frameReturn s f n fr extra vs is hlen

/-- `trap-vals` (V1's `trapValues`) forward at `Plain10` code. -/
theorem fwdAt10_trapValuesP (s : Store H) (f : Frame) {v : Execution.Runtime.Value}
    {vs : List Execution.Runtime.Value} {tail : List Admin}
    (hpl : Plain10 (values (v :: vs) ++ [.trap] ++ tail)) :
    FwdAt10 B hn ⟨s, f, values (v :: vs) ++ [.trap] ++ tail⟩ ⟨s, f, [.trap]⟩ := by
  have e : values (v :: vs) ++ [.trap] ++ tail = values (v :: vs) ++ .trap :: tail := by simp
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, tail = is.map .source := Plain10.suffix (e ▸ hpl) rfl
  rw [his]
  exact fwdAt10_trapValues s f v vs is

/-- `trap-vals` (V1's `trapTail`) forward at `Plain10` code. -/
theorem fwdAt10_trapTailP (s : Store H) (f : Frame) {i : Admin} {tail : List Admin}
    (hpl : Plain10 (.trap :: i :: tail)) :
    FwdAt10 B hn ⟨s, f, .trap :: i :: tail⟩ ⟨s, f, [.trap]⟩ := by
  obtain ⟨is, his⟩ : ∃ is : List V1.Instr, i :: tail = is.map .source :=
    Plain10.suffix (ws := []) hpl rfl
  obtain ⟨j, js, -, hj, hjs⟩ := List.map_eq_cons_iff.1 his.symm
  rw [← hj, ← hjs]
  exact fwdAt10_trapTail s f j js

/-- **Every pure step from `Plain10` code satisfies `FwdAt10`**, given the open numeric and
`br_table` obligations. -/
theorem fwdAt10_pureP {host : HostSemantics H} (R : FwdRestP10 B hn host) (s : Store H)
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
  | brTable ls d c => exact R.brTable s f ls d c
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
  | intUnary t op x => exact R.numeric s f _ _ (.intUnary t op x)
  | intBinary t op x y z h => exact R.numeric s f _ _ (.intBinary t op x y z h)
  | intBinaryTrap t op x y e h =>
    exact R.numeric s f _ _ (.intBinaryTrap t op x y e h)
  | intTest t op x => exact R.numeric s f _ _ (.intTest t op x)
  | intRel t op x y => exact R.numeric s f _ _ (.intRel t op x y)
  | floatUnary t op x y h => exact R.numeric s f _ _ (.floatUnary t op x y h)
  | floatBinary t op x y z h =>
    exact R.numeric s f _ _ (.floatBinary t op x y z h)
  | floatRel t op x y => exact R.numeric s f _ _ (.floatRel t op x y)
  | convert op x y h => exact R.numeric s f _ _ (.convert op x y h)
  | convertTrap op x e h => exact R.numeric s f _ _ (.convertTrap op x e h)

/-! ## Every step -/

/-- **The forward 1.0 half under the invariant**: under `FwdRestP10`, every V1 step from a
configuration whose code is `Plain10` and which satisfies `GSetOk` satisfies `FwdAt10`. -/
theorem fwd10_of_restP {host : HostSemantics H} (R : FwdRestP10 B hn host) {c c' : Config H}
    (h : Step host c c') (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) :
    FwdAt10 B hn c c' := by
  induction h with
  | pure s f hp => exact fwdAt10_pureP R s f hp hpl
  | context hs vs tail ih =>
    exact fwdAt10_context (ih (Plain10.mid hpl hs.firstRedex_ne_none).1 (gsetOk_mid hg)) vs tail
  | label _ n cont ih => exact fwdAt10_label (ih hpl.label_body (gsetOk_label hg)) n cont
  | frame _ n outer ih => exact fwdAt10_frame (ih hpl.frame_body (gsetOk_frame hg)) n outer
  | localGet s f i v hv => exact fwdAt10_localGet s f i v hv
  | localSet s f i v old hv => exact fwdAt10_localSet s f i v old hv
  | globalGet s f i a g h₁ h₂ => exact fwdAt10_globalGet s f i a g h₁ h₂
  | globalSet s f i a g v h₁ h₂ _ => exact fwdAt10_globalSet s f i a g v h₁ h₂ (gsetOk_redex hg h₁ h₂)
  | call s f i a h₁ => exact fwdAt10_call s f i a h₁
  | callIndirect s f i c t a fn ft h₁ h₂ h₃ h₄ h₅ => exact R.callIndirect s f i c t a fn ft h₁ h₂ h₃ h₄ h₅
  | callIndirectBounds s f i c t h₁ h₂ => exact R.callIndirectBounds s f i c t h₁ h₂
  | callIndirectNull s f i c t h₁ h₂ => exact R.callIndirectNull s f i c t h₁ h₂
  | callIndirectType s f i c t a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact R.callIndirectType s f i c t a fn ft h₁ h₂ h₃ h₄ h₅
  | invokeWasm s f a ft m fn args h₁ h₂ h₃ => exact R.invokeWasm s f a ft m fn args h₁ h₂ h₃
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact fwdAt10_invokeHost s s' f a ft fn args r h₁
  | invokeHostDiverges s f a ft fn args h₁ _ _ => exact fwdAt10_invokeHostDiverges s f a ft fn args h₁
  | intLoad s f t p arg c a m v h₁ h₂ => exact R.intLoad s f t p arg c a m v h₁ h₂
  | intLoadTrap s f t p arg c a m h₁ h₂ => exact R.intLoadTrap s f t p arg c a m h₁ h₂
  | floatLoad s f t arg c a m v h₁ h₂ => exact R.floatLoad s f t arg c a m v h₁ h₂
  | floatLoadTrap s f t arg c a m h₁ h₂ => exact R.floatLoadTrap s f t arg c a m h₁ h₂
  | intStore s f t p arg c x a m b h₁ h₂ => exact R.intStore s f t p arg c x a m b h₁ h₂
  | intStoreTrap s f t p arg c x a m h₁ h₂ => exact R.intStoreTrap s f t p arg c x a m h₁ h₂
  | floatStore s f t arg c x a m b h₁ h₂ => exact R.floatStore s f t arg c x a m b h₁ h₂
  | floatStoreTrap s f t arg c x a m h₁ h₂ => exact R.floatStoreTrap s f t arg c x a m h₁ h₂
  | memorySize s f a m h₁ => exact R.memorySize s f a m h₁
  | memoryGrow s f a m c r b h₁ h₂ => exact R.memoryGrow s f a m c r b h₁ h₂

/-- **The forward 1.0 half on typed images, under the invariant**: under `FwdRestP10`, a V1 step
between configurations whose images are typed, from one satisfying `Plain10` and `GSetOk`, is a
step of the wasm-1.0 script between the images. -/
theorem wholeStepFwd10_of_restP {host : HostSemantics H} (R : FwdRestP10 B hn host)
    {c c' : Config H} (hc : Typed10 (simEnv10 B) hn c) (hc' : Typed10 (simEnv10 B) hn c')
    (hpl : Plain10 c.code) (hg : GSetOk c.store c.frame c.code) (h : Step host c c') :
    SStepB (simEnv10 B) (configV hn c) (configV hn c') :=
  fwd10_of_restP R h hpl hg (typedV_state_of_typed10 hc) (typedV_state_of_typed10 hc')
    (typedV_code_of_typed10 hc) (typedV_code_of_typed10 hc')

end Silmaril.Wasm.SpecTec.Sim10.Whole
