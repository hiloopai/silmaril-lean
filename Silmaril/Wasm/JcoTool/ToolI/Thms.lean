module

public import Silmaril.Wasm.JcoTool.ToolI.Defs
public import Silmaril.Wasm.JcoTool.NewI.Thms
public import Silmaril.Wasm.JcoTool.Tool.Thms

/-!
# The correctness theorem of `wasm-jco new` for every world

`newFull core wf = .ok o` is what `wasm-jco new` computes (thin-wrapper mode) before it
writes `o.bytes`. **`newFull_correct`**: either

* the world is 's fragment (`inOld`) and `o` is `Tool.newWith core wf.world`'s
  output, so `Tool.newWith_correct_full` applies (canonical-ABI side conditions, the read-back
  by `xparse`, by the verified parser without async built-ins, and the IR read-back as a thin
  wrapper for memory-free synchronous worlds); or
* the world has interfaces, named types or resources, and the `NewI` plan exists with the
  guarantees of `NewI.plan_ok` (every export at its canonical core type, every core import
  classified at its canonical type, named types flattened by `AbiR`), and the bytes are the
  encoding of the emitted component, which `xparse` reads back as its normal form (and the
  verified parser as the component itself when there are no async built-ins).

Not proved: that the emitted component's types, aliases and instances are the ones the world
describes (no component-level reading of resources or interfaces exists yet); this is what
`wasm-tools validate`, the comparison of worlds with wit-component's and the executions of
`tools/wasm-jco/tests/run.sh` test.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.ToolI

open Silmaril.Wasm.Wit.Binary (WorldFull)
open Silmaril.Wasm.Component.Binary (Ast parse)

theorem newI_steps {core : ByteArray} {wf : WorldFull} {o : Tool.Out} (h : newI core wf = .ok o) :
    ∃ p c, NewI.plan core wf = .ok p ∧ NewI.emit p = .ok c ∧ c.encode = some o.bytes ∧
      o.ast = c.toAst := by
  obtain ⟨p, hp, h₁⟩ := New.bind_ok h
  obtain ⟨c, hc, h₂⟩ := New.bind_ok h₁
  obtain ⟨b, hb, h₃⟩ := New.bind_ok h₂
  cases h₃
  have hb' : c.encode = some b := by
    unfold New.mustEncode at hb
    split at hb
    · cases hb
      assumption
    · cases hb
  exact ⟨p, c, hp, hc, hb', rfl⟩

/-- What is known of a `NewI` output. -/
def NewIOk (core : ByteArray) (wf : WorldFull) (o : Tool.Out) : Prop :=
  ∃ p c, NewI.plan core wf = .ok p ∧ NewI.emit p = .ok c ∧
    Silmaril.Wasm.Component.Binary.Lower.coreMod core = .ok p.mod ∧ p.fns = NewI.exportFns wf ∧
    List.Forall₂ (NewI.LiftOk wf p.mod) p.fns p.lifts ∧
    List.Forall₂ (NewI.ReqOk wf p.tables) (p.mod.importNames.zip p.mod.imports) p.reqs ∧
    c.encode = some o.bytes ∧ xparse o.bytes = .ok c.norm ∧
    (∀ a, o.ast = some a → parse o.bytes = .ok a)

theorem newI_correct {core : ByteArray} {wf : WorldFull} {o : Tool.Out} (h : newI core wf = .ok o) :
    NewIOk core wf o := by
  obtain ⟨p, c, hp, hc, he, hast⟩ := newI_steps h
  obtain ⟨hm, -, -, hf, hl, hr⟩ := NewI.plan_ok hp
  refine ⟨p, c, hp, hc, hm, hf, hl, hr, he, xparse_encode he, fun a ha => ?_⟩
  have hca : c.toAst = some a := hast ▸ ha
  have hb : Silmaril.Wasm.Component.Binary.encode a = some o.bytes := by
    rw [← XAst.encode_toAst hca, he]
  exact Silmaril.Wasm.Component.Binary.parse_encode hb

/-- **The correctness theorem of `wasm-jco new`**, for every world. -/
theorem newFull_correct {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newFull core wf = .ok o) :
    (inOld wf.world = true ∧ Tool.newWith core wf.world = .ok o) ∨
      (inOld wf.world = false ∧ NewIOk core wf o) := by
  unfold newFull at h
  cases hw : inOld wf.world
  · rw [hw] at h
    exact .inr ⟨rfl, newI_correct h⟩
  · rw [hw] at h
    exact .inl ⟨rfl, h⟩

/-- `newFull_correct` with the first case unfolded through `Tool.newWith_correct_full`: the
read-back by `xparse` holds for every output of `wasm-jco new`. -/
theorem newFull_xparse {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newFull core wf = .ok o) : ∃ c : XAst, c.encode = some o.bytes ∧ xparse o.bytes = .ok c.norm := by
  rcases newFull_correct h with ⟨_, ho⟩ | ⟨_, p, c, _, _, _, _, _, _, he, hx, _⟩
  · obtain ⟨p, c, _, _, he, _, _⟩ := Tool.newWith_steps ho
    exact ⟨c, he, xparse_encode he⟩
  · exact ⟨c, he, hx⟩

end Silmaril.Wasm.JcoTool.ToolI
