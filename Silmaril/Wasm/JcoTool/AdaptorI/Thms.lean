module

public import Silmaril.Wasm.JcoTool.AdaptorI.Defs
public import Silmaril.Wasm.JcoTool.Adaptor.Thms
public import Silmaril.Wasm.JcoTool.XParse.Thms

/-!
# The correctness theorem of `wasm-jco new --adaptor` with interfaces

**`newAdaptorI_correct`**: if `newAdaptorI core wf alloc = .ok o`, then

1. the metadata is `mdOf wf alloc`: the world's exported functions, then those of its exported
   interfaces (named `key#f`), each `Sig.ofWit` of the world's function;
2. the module imports nothing, exports the allocator at `(i32, i32) -> i32` and each
   function at its C-convention core type (`Adaptor.calleeCore`);
3. the adaptor bytes encode `(adaptorLime md).toCore` in the Core binary grammar
   (`encodeModule?_sound`), and the output's bytes are the encoding of the emitted component,
   read back by `xparse`;
4. the adaptor validates under the conditions of `Jco.Real.adaptorLime_valid_of_lt`;
5. `wrap md` behaves, at every function of the world and of its exported interfaces, as the
   module under the C convention (`Jco.wrap_correct`).

As for adaptor mode, item 5 is about the memory model's `wrap md`; the instance exports of the
interfaces are read by wasmtime, which the tests run.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.AdaptorI

open Silmaril.Wasm.Wit.Binary (WorldFull)
open Silmaril.Wasm.Jco (Meta Sig CoreInst PVal)
open New (bind_ok require_ok expectExport_ok)

theorem planI_ok {core : ByteArray} {wf : WorldFull} {alloc : String} {p : Plan}
    (h : planI core wf alloc = .ok p) :
    mdOf wf alloc = .ok p.md ∧ Silmaril.Wasm.Component.Binary.Lower.coreMod core = .ok p.mod ∧ p.mod.imports = [] ∧
      New.coreExport? p.mod alloc = some ⟨[ti32, ti32], [ti32]⟩ ∧
      ∀ s ∈ p.md.world, New.coreExport? p.mod s.name = some (Adaptor.calleeCore s) := by
  obtain ⟨fns, hf, h₁⟩ := bind_ok h
  obtain ⟨m, hm, h₂⟩ := bind_ok h₁
  obtain ⟨_, hi, h₃⟩ := bind_ok h₂
  obtain ⟨_, _, h₄⟩ := bind_ok h₃
  obtain ⟨_, ha, h₅⟩ := bind_ok h₄
  obtain ⟨_, hw, h₆⟩ := bind_ok h₅
  cases h₆
  have hmd : mdOf wf alloc = .ok ⟨fns.map (·.s), alloc⟩ := by simp [mdOf, hf]
  exact ⟨hmd, (congrFun Silmaril.Wasm.Perf.CoreMod.coreModF_eq core).symm.trans hm,
    List.isEmpty_iff.mp (require_ok hi), expectExport_ok ha,
    fun s hs => expectExport_ok (Adaptor.forM_ok hw s hs)⟩

theorem newAdaptorI_steps {core : ByteArray} {wf : WorldFull} {alloc : String} {o : Out}
    (h : newAdaptorI core wf alloc = .ok o) :
    planI core wf alloc = .ok o.plan ∧ Adaptor.adaptorBytes o.plan.md = .ok o.adaptor ∧
      ∃ c, emitI core o.adaptor o.plan = .ok c ∧ c.encode = some o.bytes ∧ o.ast = c.toAst := by
  obtain ⟨p, hp, h₁⟩ := bind_ok h
  obtain ⟨a, ha, h₂⟩ := bind_ok h₁
  obtain ⟨c, hc, h₃⟩ := bind_ok h₂
  obtain ⟨b, hb, h₄⟩ := bind_ok h₃
  cases h₄
  have hb' : c.encode = some b := by
    unfold New.mustEncode at hb
    split at hb
    · cases hb
      assumption
    · cases hb
  exact ⟨hp, ha, c, hc, hb', rfl⟩

/-- **The correctness theorem of adaptor mode with interfaces.** -/
theorem newAdaptorI_correct {core : ByteArray} {wf : WorldFull} {alloc : String} {o : Out}
    (h : newAdaptorI core wf alloc = .ok o) :
    mdOf wf alloc = .ok o.plan.md ∧
    (o.plan.mod.imports = [] ∧ New.coreExport? o.plan.mod alloc = some ⟨[ti32, ti32], [ti32]⟩ ∧
      ∀ s ∈ o.plan.md.world, New.coreExport? o.plan.mod s.name = some (Adaptor.calleeCore s)) ∧
    Silmaril.Wasm.Binary.Core.Encodes o.adaptor.data.toList
      (Silmaril.Wasm.Jco.adaptorLime o.plan.md).toCore ∧
    (∃ c : XAst, c.encode = some o.bytes ∧ xparse o.bytes = .ok c.norm) ∧
    ((Silmaril.Wasm.Jco.importNames o.plan.md).Nodup →
      "cabi_realloc" ∉ o.plan.md.world.map (·.name) →
      (∀ s ∈ o.plan.md.world, (Silmaril.Wasm.Jco.flatParams s.params).length + 2 < 2 ^ 32) →
      o.plan.md.world.length < 2 ^ 31 →
      Silmaril.Wasm.Validation.ModuleValid (Silmaril.Wasm.Jco.adaptorLime o.plan.md).toCore) ∧
    (∀ M : CoreInst, o.plan.md.Conforms M → ∀ (name : String) (vs : List PVal),
      (Silmaril.Wasm.Jco.wrap o.plan.md).callExport M name vs = o.plan.md.spec M name vs) := by
  obtain ⟨hp, ha, c, _, he, _⟩ := newAdaptorI_steps h
  obtain ⟨hmd, _, hi, hal, hs⟩ := planI_ok hp
  exact ⟨hmd, ⟨hi, hal, hs⟩, Adaptor.adaptorBytes_encodes ha, ⟨c, he, xparse_encode he⟩,
    fun hn hr hpar hw => Silmaril.Wasm.Jco.Real.adaptorLime_valid_of_lt _ hn hr hpar hw,
    fun M hC name vs => Silmaril.Wasm.Jco.wrap_correct M _ hC name vs⟩

end Silmaril.Wasm.JcoTool.AdaptorI
