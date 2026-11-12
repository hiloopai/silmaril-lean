module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdLeafI32

/-!
# The forward 1.0 half: the target on the fragment, and the reduction of the whole

* **`Task.wholeStepNest10`** (frozen, proved by `wholeStepNest10`): at every builtins, every V1 step
  built from the sixteen leaves of `Leaf10F` (`unreachable`, `nop`, `drop`, `label-vals`,
  `frame-vals`, `trap-label`, `trap-frame`, `local.tee`, `br_if-*`, `select-*`, `local.get`,
  `global.get`, `call`, `local.set`) under **any** nesting of V1's `context`, `label` and `frame`,
  between configurations whose images are typed, is a step of the wasm-1.0 script between the
  images. This is the 1.0 counterpart of `Sim20.Whole.Task.wholeStepCtxS20`, without the
  restriction to one context and without an erratum.
* `FwdLeaves10 B hn host`: one obligation per non-structural constructor of V1's `Step` (23 of
  them), each `FwdAt10` at that constructor's step. `fwd10_of_leaves`: they give `FwdAt10` at every
  V1 step.
* `FwdRest10 B hn host`: the obligations not yet discharged; `fwd10_of_rest`: they give `FwdAt10`
  at every V1 step. `local.get`, `local.set`, `global.get` and `call` are gone, and the `pure`
  obligation is asked only off the fragment (`¬ Leaf10F`).

As for 2.0, the successor's typing is a hypothesis (`FwdAt10` asks for it): subject reduction for
the image is not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  result frameMemory frameTable setGlobal setMemory loadInt loadFloat storeInt storeFloat
  effectiveAddress expression)
open Silmaril.Wasm.Execution.Runtime (Frame GlobalInst GlobalAddr FuncAddr MemAddr MemInst
  TableInst FuncInst ModuleInst Result)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

variable {B : Builtins} {H : Type} {hn : H → String}

/-! ## The fragment -/

/-- **The V1 leaf steps the forward half covers**, with V1's premises. -/
inductive Leaf10F : Config H → Config H → Prop where
  | unreachable (s : Store H) (f : Frame) : Leaf10F ⟨s, f, [.source .unreachable]⟩ ⟨s, f, [.trap]⟩
  | nop (s : Store H) (f : Frame) : Leaf10F ⟨s, f, [.source .nop]⟩ ⟨s, f, []⟩
  | drop (s : Store H) (f : Frame) (v : Execution.Runtime.Value) :
      Leaf10F ⟨s, f, [value v, .source .drop]⟩ ⟨s, f, []⟩
  | localGet (s : Store H) (f : Frame) (x : LocalIdx) (v : Execution.Runtime.Value)
      (hv : f.locals[x.toNat]? = some v) :
      Leaf10F ⟨s, f, [.source (.localGet x)]⟩ ⟨s, f, [value v]⟩
  | globalGet (s : Store H) (f : Frame) (x : GlobalIdx) (a : Execution.Runtime.GlobalAddr)
      (g : GlobalInst) (ha : f.module.globals[x.toNat]? = some a)
      (hg : s.globals[a.value]? = some g) :
      Leaf10F ⟨s, f, [.source (.globalGet x)]⟩ ⟨s, f, [value g.value]⟩
  | call (s : Store H) (f : Frame) (x : FuncIdx) (a : Execution.Runtime.FuncAddr)
      (ha : f.module.funcs[x.toNat]? = some a) :
      Leaf10F ⟨s, f, [.source (.call x)]⟩ ⟨s, f, [.invoke a]⟩
  | localSet (s : Store H) (f : Frame) (x : LocalIdx) (v old : Execution.Runtime.Value)
      (hold : f.locals[x.toNat]? = some old) :
      Leaf10F ⟨s, f, [value v, .source (.localSet x)]⟩
        ⟨s, { f with locals := f.locals.set x.toNat v }, []⟩
  | labelDone (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr)
      (vs : List Execution.Runtime.Value) :
      Leaf10F ⟨s, f, [.label n cont (values vs)]⟩ ⟨s, f, values vs⟩
  | frameDone (s : Store H) (f fr : Frame) (vs : List Execution.Runtime.Value) :
      Leaf10F ⟨s, f, [.frame vs.length fr (values vs)]⟩ ⟨s, f, values vs⟩
  | labelTrap (s : Store H) (f : Frame) (n : Nat) (cont : V1.Expr) :
      Leaf10F ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩
  | frameTrap (s : Store H) (f fr : Frame) (n : Nat) :
      Leaf10F ⟨s, f, [.frame n fr [.trap]]⟩ ⟨s, f, [.trap]⟩
  | localTee (s : Store H) (f : Frame) (x : LocalIdx) (v : Execution.Runtime.Value) :
      Leaf10F ⟨s, f, [value v, .source (.localTee x)]⟩
        ⟨s, f, [value v, value v, .source (.localSet x)]⟩
  | brIfZero (s : Store H) (f : Frame) (l : LabelIdx) :
      Leaf10F ⟨s, f, [value (.int .i32 0), .source (.brIf l)]⟩ ⟨s, f, []⟩
  | brIfNonzero (s : Store H) (f : Frame) (l : LabelIdx) (c : BitVec 32) (hc : c ≠ 0) :
      Leaf10F ⟨s, f, [value (.int .i32 c), .source (.brIf l)]⟩ ⟨s, f, [.source (.br l)]⟩
  | selectZero (s : Store H) (f : Frame) (a b : Execution.Runtime.Value) (hab : a.type = b.type) :
      Leaf10F ⟨s, f, [value a, value b, value (.int .i32 0), .source .select]⟩ ⟨s, f, [value b]⟩
  | selectNonzero (s : Store H) (f : Frame) (a b : Execution.Runtime.Value) (hab : a.type = b.type)
      (c : BitVec 32) (hc : c ≠ 0) :
      Leaf10F ⟨s, f, [value a, value b, value (.int .i32 c), .source .select]⟩ ⟨s, f, [value a]⟩

/-- Every leaf of the fragment is a V1 step. -/
theorem Leaf10F.step {host : HostSemantics H} {c c' : Config H} (h : Leaf10F c c') :
    Step host c c' := by
  cases h with
  | unreachable s f => exact .pure s f .unreachable
  | nop s f => exact .pure s f .nop
  | drop s f v => exact .pure s f (.drop v)
  | localGet s f x v hv => exact .localGet s f x v hv
  | globalGet s f x a g ha hg => exact .globalGet s f x a g ha hg
  | call s f x a ha => exact .call s f x a ha
  | localSet s f x v old hold => exact .localSet s f x v old hold
  | labelDone s f n cont vs => exact .pure s f (.labelDone n cont vs)
  | frameDone s f fr vs => exact .pure s f (.frameDone vs.length fr vs rfl)
  | labelTrap s f n cont => exact .pure s f (.labelTrap n cont)
  | frameTrap s f fr n => exact .pure s f (.frameTrap n fr)
  | localTee s f x v => exact .pure s f (.localTee x v)
  | brIfZero s f l => exact .pure s f (.brIfZero l)
  | brIfNonzero s f l c hc => exact .pure s f (.brIfNonzero l c hc)
  | selectZero s f a b hab => exact .pure s f (.selectZero a b hab)
  | selectNonzero s f a b hab c hc => exact .pure s f (.selectNonzero a b hab c hc)

/-- **`FwdAt10` holds at every leaf of the fragment**, at every builtins. -/
theorem fwdAt10_leafF {c c' : Config H} (h : Leaf10F c c') : FwdAt10 B hn c c' := by
  cases h with
  | unreachable s f => exact fwdAt10_unreachable s f
  | nop s f => exact fwdAt10_nop s f
  | drop s f v => exact fwdAt10_drop s f v
  | localGet s f x v hv => exact fwdAt10_localGet s f x v hv
  | globalGet s f x a g ha hg => exact fwdAt10_globalGet s f x a g ha hg
  | call s f x a ha => exact fwdAt10_call s f x a ha
  | localSet s f x v old hold => exact fwdAt10_localSet s f x v old hold
  | labelDone s f n cont vs => exact fwdAt10_labelDone s f n cont vs
  | frameDone s f fr vs => exact fwdAt10_frameDone s f fr vs
  | labelTrap s f n cont => exact fwdAt10_labelTrap s f n cont
  | frameTrap s f fr n => exact fwdAt10_frameTrap s f fr n
  | localTee s f x v => exact fwdAt10_localTee s f x v
  | brIfZero s f l => exact fwdAt10_brIfZero s f l
  | brIfNonzero s f l c hc => exact fwdAt10_brIfNonzero s f l c hc
  | selectZero s f a b _ => exact fwdAt10_selectZero s f a b
  | selectNonzero s f a b _ c hc => exact fwdAt10_selectNonzero s f a b c hc

/-! ## The fragment target -/

/-- **The forward 1.0 half on the fragment, under any nesting** (frozen; proved below): at every
builtins, every `Nest10 Leaf10F` step between configurations whose images are typed is a step of
the wasm-1.0 script between the images. -/
def Task.wholeStepNest10 : Prop :=
  ∀ (H : Type) (hn : H → String) (B : Builtins) (c c' : Config H),
    Typed10 (simEnv10 B) hn c → Typed10 (simEnv10 B) hn c' → Nest10 Leaf10F c c' →
      SStepB (simEnv10 B) (configV hn c) (configV hn c')

/-- **`Task.wholeStepNest10` holds.** -/
theorem wholeStepNest10 : Task.wholeStepNest10 :=
  fun _ _ _ _ _ hc hc' h => fwd10_nest_typed (fun _ _ hl => fwdAt10_leafF hl) hc hc' h

/-- Every step of the fragment target is a V1 step. -/
theorem nest10_leafF_step {host : HostSemantics H} {c c' : Config H} (h : Nest10 Leaf10F c c') :
    Step host c c' :=
  Nest10.step (fun _ _ hl => hl.step) h

/-! ## The whole forward half, by leaves -/

/-- **The forward obligations at the V1 constructors other than `pure`, `local.get`,
`local.set`, `global.get` and `call`** (18 of them). -/
structure FwdOther10 (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop where
  globalSet : ∀ (s : Store H) (f : Frame) (i : GlobalIdx) (a : GlobalAddr) (g : GlobalInst)
    (v : Execution.Runtime.Value), f.module.globals[i.toNat]? = some a →
      s.globals[a.value]? = some g → g.mutability = .var →
      FwdAt10 B hn ⟨s, f, [value v, .source (.globalSet i)]⟩
        ⟨setGlobal s a {g with value := v}, f, []⟩
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
  invokeHost : ∀ (s s' : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType) (fn : H)
    (args : List Execution.Runtime.Value) (r : Result),
      s.funcs[a.value]? = some (.host ft fn) → args.length = ft.params.length →
      host fn s args (.returned s' r) →
      FwdAt10 B hn ⟨s, f, values args ++ [.invoke a]⟩ ⟨s', f, result r⟩
  invokeHostDiverges : ∀ (s : Store H) (f : Frame) (a : FuncAddr) (ft : V1.FuncType) (fn : H)
    (args : List Execution.Runtime.Value),
      s.funcs[a.value]? = some (.host ft fn) → args.length = ft.params.length →
      host fn s args .diverged →
      FwdAt10 B hn ⟨s, f, values args ++ [.invoke a]⟩ ⟨s, f, values args ++ [.invoke a]⟩
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

/-- **One forward obligation per non-structural constructor of V1's `Step`** (23 of them). -/
structure FwdLeaves10 (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop
    extends FwdOther10 B hn host where
  pure : ∀ (s : Store H) (f : Frame) (before after : List Admin), PureStep before after →
    FwdAt10 B hn ⟨s, f, before⟩ ⟨s, f, after⟩
  localGet : ∀ (s : Store H) (f : Frame) (i : LocalIdx) (v : Execution.Runtime.Value),
    f.locals[i.toNat]? = some v → FwdAt10 B hn ⟨s, f, [.source (.localGet i)]⟩ ⟨s, f, [value v]⟩
  localSet : ∀ (s : Store H) (f : Frame) (i : LocalIdx) (v old : Execution.Runtime.Value),
    f.locals[i.toNat]? = some old → FwdAt10 B hn ⟨s, f, [value v, .source (.localSet i)]⟩
      ⟨s, {f with locals := f.locals.set i.toNat v}, []⟩
  globalGet : ∀ (s : Store H) (f : Frame) (i : GlobalIdx) (a : GlobalAddr) (g : GlobalInst),
    f.module.globals[i.toNat]? = some a → s.globals[a.value]? = some g →
      FwdAt10 B hn ⟨s, f, [.source (.globalGet i)]⟩ ⟨s, f, [value g.value]⟩
  call : ∀ (s : Store H) (f : Frame) (i : FuncIdx) (a : FuncAddr),
    f.module.funcs[i.toNat]? = some a → FwdAt10 B hn ⟨s, f, [.source (.call i)]⟩ ⟨s, f, [.invoke a]⟩

/-- **The leaves give the whole forward half**: under `FwdLeaves10`, every V1 step satisfies
`FwdAt10`, through any nesting of V1's `context`, `label` and `frame`. -/
theorem fwd10_of_leaves {host : HostSemantics H} (L : FwdLeaves10 B hn host) {c c' : Config H}
    (h : Step host c c') : FwdAt10 B hn c c' := by
  induction h with
  | pure s f hp => exact L.pure s f _ _ hp
  | context _ vs tail ih => exact fwdAt10_context ih vs tail
  | label _ n cont ih => exact fwdAt10_label ih n cont
  | frame _ n outer ih => exact fwdAt10_frame ih n outer
  | localGet s f i v hv => exact L.localGet s f i v hv
  | localSet s f i v old hv => exact L.localSet s f i v old hv
  | globalGet s f i a g h₁ h₂ => exact L.globalGet s f i a g h₁ h₂
  | globalSet s f i a g v h₁ h₂ h₃ => exact L.globalSet s f i a g v h₁ h₂ h₃
  | call s f i a h₁ => exact L.call s f i a h₁
  | callIndirect s f i c t a fn ft h₁ h₂ h₃ h₄ h₅ => exact L.callIndirect s f i c t a fn ft h₁ h₂ h₃ h₄ h₅
  | callIndirectBounds s f i c t h₁ h₂ => exact L.callIndirectBounds s f i c t h₁ h₂
  | callIndirectNull s f i c t h₁ h₂ => exact L.callIndirectNull s f i c t h₁ h₂
  | callIndirectType s f i c t a fn ft h₁ h₂ h₃ h₄ h₅ =>
    exact L.callIndirectType s f i c t a fn ft h₁ h₂ h₃ h₄ h₅
  | invokeWasm s f a ft m fn args h₁ h₂ h₃ => exact L.invokeWasm s f a ft m fn args h₁ h₂ h₃
  | invokeHost s s' f a ft fn args r h₁ h₂ h₃ => exact L.invokeHost s s' f a ft fn args r h₁ h₂ h₃
  | invokeHostDiverges s f a ft fn args h₁ h₂ h₃ => exact L.invokeHostDiverges s f a ft fn args h₁ h₂ h₃
  | intLoad s f t p arg c a m v h₁ h₂ => exact L.intLoad s f t p arg c a m v h₁ h₂
  | intLoadTrap s f t p arg c a m h₁ h₂ => exact L.intLoadTrap s f t p arg c a m h₁ h₂
  | floatLoad s f t arg c a m v h₁ h₂ => exact L.floatLoad s f t arg c a m v h₁ h₂
  | floatLoadTrap s f t arg c a m h₁ h₂ => exact L.floatLoadTrap s f t arg c a m h₁ h₂
  | intStore s f t p arg c x a m b h₁ h₂ => exact L.intStore s f t p arg c x a m b h₁ h₂
  | intStoreTrap s f t p arg c x a m h₁ h₂ => exact L.intStoreTrap s f t p arg c x a m h₁ h₂
  | floatStore s f t arg c x a m b h₁ h₂ => exact L.floatStore s f t arg c x a m b h₁ h₂
  | floatStoreTrap s f t arg c x a m h₁ h₂ => exact L.floatStoreTrap s f t arg c x a m h₁ h₂
  | memorySize s f a m h₁ => exact L.memorySize s f a m h₁
  | memoryGrow s f a m c r b h₁ h₂ => exact L.memoryGrow s f a m c r b h₁ h₂

/-- **The forward obligations still open**: `FwdLeaves10` without `local.get`, `local.set`,
`global.get` and `call`, and with `pure` asked only at pure steps outside the fragment. -/
structure FwdRest10 (B : Builtins) (hn : H → String) (host : HostSemantics H) : Prop
    extends FwdOther10 B hn host where
  pure : ∀ (s : Store H) (f : Frame) (before after : List Admin), PureStep before after →
    ¬ Leaf10F (⟨s, f, before⟩ : Config H) ⟨s, f, after⟩ → FwdAt10 B hn ⟨s, f, before⟩ ⟨s, f, after⟩

/-- The discharged leaves complete `FwdRest10` to `FwdLeaves10`. -/
theorem fwdLeaves10_of_rest {host : HostSemantics H} (R : FwdRest10 B hn host) :
    FwdLeaves10 B hn host where
  toFwdOther10 := R.toFwdOther10
  pure s f before after hp := by
    by_cases hl : Leaf10F (⟨s, f, before⟩ : Config H) ⟨s, f, after⟩
    · exact fwdAt10_leafF hl
    · exact R.pure s f before after hp hl
  localGet := fwdAt10_localGet
  localSet := fwdAt10_localSet
  globalGet := fwdAt10_globalGet
  call := fwdAt10_call

/-- **The forward 1.0 half from the open obligations**: under `FwdRest10`, every V1 step satisfies
`FwdAt10`. -/
theorem fwd10_of_rest {host : HostSemantics H} (R : FwdRest10 B hn host) {c c' : Config H}
    (h : Step host c c') : FwdAt10 B hn c c' :=
  fwd10_of_leaves (fwdLeaves10_of_rest R) h

end Silmaril.Wasm.SpecTec.Sim10.Whole
