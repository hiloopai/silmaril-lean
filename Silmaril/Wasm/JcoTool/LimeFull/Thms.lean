module

public import Silmaril.Wasm.JcoTool.ToolI.Thms
public import Silmaril.Wasm.JcoTool.Lime.Thms

/-!
# `wasm-jco new --lime` for every world

`ToolI.newLimeFull` is `--lime` on top of `ToolI.newFull`: the input module goes through the
verified 3.0 → Lime compiler, the component is built from the re-encoded module (an earlier
emitter or `NewI`, whatever the world), and every core module of the output must be in Lime1.

**`newLimeFull_correct`**: if `newLimeFull core wf = .ok o`, then

1. the input decodes (silmaril's `decode?`, sound for the Core grammar) to a module `m` that the
   direct 3.0 → Lime compiler maps to a Lime1 module `l`; the module put into the component is
   the verified encoding of `l.toCore`; for valid `m`, `m` and `l.toCore` are exactly
   export-equivalent at every profile and host parametric in the code
   (`LimeCompile.Direct.compile_correct`);
2. the output is that of `newFull` on those bytes (same bytes, AST, IR verdict and core
   modules), so `ToolI.newFull_correct` applies to it: the pass-1 theorem
   `Tool.newWith_correct_full`, or `NewIOk` (canonical-ABI side conditions, `xparse` read-back);
3. every core module of the output (the module, the `shim` and `fixup` helpers) decodes and
   compiles to Lime1.

`newLimeFull_full` restates 2 through `newFull_correct`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.ToolI

open Silmaril.Wasm.Wit.Binary (WorldFull)
open Silmaril.Wasm (Module)
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.LimeCompile.Direct (compile)
open New (bind_ok require_ok)

/-- **The correctness theorem of `wasm-jco new --lime`, for every world.** -/
theorem newLimeFull_correct {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newLimeFull core wf = .ok o) :
    ∃ (core' : ByteArray) (m : Module) (l : Silmaril.Wasm.Lime1.Module),
      Silmaril.Wasm.Binary.Core.decode? core = some m ∧ compile m = some l ∧
      Silmaril.Wasm.Binary.Core.Encodes core'.data.toList l.toCore ∧
      (∀ {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H),
        Silmaril.Wasm.Execution.Core.Sim.HostParametric host →
        (∃ mt, Silmaril.Wasm.Validation.ModuleOk m mt) →
        Silmaril.Wasm.Binaryen.ExportEquiv (· = ·) P host m l.toCore) ∧
      (∃ o', newFull core' wf = .ok o' ∧ o.bytes = o'.bytes ∧ o.ast = o'.ast ∧ o.ir = o'.ir ∧
        o.cores = o'.cores) ∧
      (∀ b ∈ o.cores, ∃ m' l', Silmaril.Wasm.Binary.Core.decode? b = some m' ∧ compile m' = some l') := by
  obtain ⟨core', hl, h₁⟩ := bind_ok h
  obtain ⟨m, l, hm, hc, he⟩ := Lime.toLime_ok hl
  obtain ⟨o', ho', h₂⟩ := bind_ok h₁
  obtain ⟨_, hq, h₃⟩ := bind_ok h₂
  cases h₃
  have hall : ∀ b ∈ o'.cores, Lime.isLime b = true := List.all_eq_true.mp (require_ok hq)
  exact ⟨core', m, l, hm, hc, he,
    fun P host hh hv => Silmaril.Wasm.LimeCompile.Direct.compile_correct (P := P) hh hc hv,
    ⟨o', ho', rfl, rfl, rfl, rfl⟩, fun b hb => Lime.isLime_ok (hall b hb)⟩

/-- `newLimeFull_correct` with the output of `newFull` unfolded by `newFull_correct`: the
component built from the Lime module satisfies the pass-1 theorem or `NewIOk`, and its bytes
are read back by `xparse`. -/
theorem newLimeFull_full {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newLimeFull core wf = .ok o) :
    ∃ (core' : ByteArray) (o' : Tool.Out), o.bytes = o'.bytes ∧
      ((inOld wf.world = true ∧ Tool.newWith core' wf.world = .ok o') ∨
        (inOld wf.world = false ∧ NewIOk core' wf o')) ∧
      (∃ c : XAst, c.encode = some o.bytes ∧ xparse o.bytes = .ok c.norm) := by
  obtain ⟨core', -, -, -, -, -, -, ⟨o', ho', hb, -⟩, -⟩ := newLimeFull_correct h
  obtain ⟨c, hc, hx⟩ := newFull_xparse ho'
  exact ⟨core', o', hb, newFull_correct ho', c, hb ▸ hc, hb ▸ hx⟩

end Silmaril.Wasm.JcoTool.ToolI
