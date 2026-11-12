module

public import Silmaril.Wasm.JcoTool.Tool.Defs
public import Silmaril.Wasm.JcoTool.New.Thms
public import Silmaril.Wasm.JcoTool.Emit.Thms
public import Silmaril.Wasm.JcoTool.Check.Thms
public import Silmaril.Wasm.Component.Binary.Thms
public import Silmaril.Wasm.JcoTool.XParse.Thms

/-!
# The correctness theorem of `wasm-jco new`, at the tool's entry point

`newWith core w = .ok o` is what `wasm-jco new` computes before it writes `o.bytes`
(`newEmbedded` and `newWit` only choose the world `w`). **`newWith_correct`** states what is
then known about the output, in three layers:

1. **Canonical ABI side conditions** (always): the plan of `core` against `w` exists; its
   module is `core`'s decoded interface; every world export is a core export at the canonical
   core type (`LiftOk`: sync, stackful or callback); every core import is classified and has
   the canonical type of what it asks for (`ReqOk`).
2. **Syntax** (when `o.ast = some a`, i.e. no async built-ins): the verified parser reads the
   bytes back as `a`.
3. **Behaviour** (when `o.ir = true`, memory-free synchronous worlds): the component IR reads
   the bytes as the thin wrapper `thin w' m p` of a module `m` with the bytes `core`, along a
   recognized plan that fits, and under every core semantics this is the strategy of `m`
   wrapped with the identity adaptor (`Thin.wrapGlue`, the monadic jco construction).

What is not covered, stated honestly: for async exports and memory-using worlds the
behaviour is not read back (the component IR has neither memory nor async built-ins), so for
them layers 1 and (without built-ins) 2 hold and execution is tested
(`tools/wasm-jco/tests/run.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Tool

open Silmaril.Wasm.Wit.Binary (World)
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Binary (Ast parse parseComponent CoreMod)
open Silmaril.Wasm.Jco.Thin (thin wrapGlue importWiring recognize)

theorem newWith_steps {core : ByteArray} {w : World} {o : Out} (h : newWith core w = .ok o) :
    ∃ p c, New.plan core w = .ok p ∧ New.emit p = .ok c ∧ c.encode = some o.bytes ∧
      o.ast = c.toAst ∧ o.ir = Check.irCheck core o.bytes := by
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
  exact ⟨p, c, hp, hc, hb', rfl, rfl⟩

/-- Layer 2: without built-ins, the bytes parse back to the emitted syntax. -/
theorem newWith_parse {core : ByteArray} {w : World} {o : Out} {a : Ast}
    (h : newWith core w = .ok o) (ha : o.ast = some a) : parse o.bytes = .ok a := by
  obtain ⟨_, c, _, _, he, hast, _⟩ := newWith_steps h
  have hc : c.toAst = some a := hast ▸ ha
  have hb : Silmaril.Wasm.Component.Binary.encode a = some o.bytes := by
    rw [← XAst.encode_toAst hc, he]
  exact Silmaril.Wasm.Component.Binary.parse_encode hb

/-- **The correctness theorem of `wasm-jco new`.** -/
theorem newWith_correct {core : ByteArray} {w : World} {o : Out} (h : newWith core w = .ok o) :
    (∃ p, New.plan core w = .ok p ∧ Binary.Lower.coreMod core = .ok p.mod ∧
      List.Forall₂ (New.LiftOk p.mod) p.exports p.lifts ∧
      List.Forall₂ (New.ReqOk p.imports p.exports) (p.mod.importNames.zip p.mod.imports) p.reqs) ∧
    (∀ a, o.ast = some a → parse o.bytes = .ok a) ∧
    (o.ir = true → ∃ (w' : Silmaril.Wasm.Jco.Thin.World) (m : CoreMod) (p : Silmaril.Wasm.Jco.Thin.Plan),
      parseComponent o.bytes = .ok (thin w' m p) ∧ m.bytes = core ∧
      recognize .plain w' (CoreModule.imports m) (CoreModule.exports m) = some p ∧
      ∀ C : CoreSem CoreMod, (thin w' m p).denU C = (wrapGlue .plain w' m (importWiring w' p) p.glue).denU C) := by
  obtain ⟨p, _, hp, _, _, _, hir⟩ := newWith_steps h
  have hok := New.plan_ok hp
  refine ⟨⟨p, hp, hok.1, hok.2.2.1, hok.2.2.2⟩, fun a ha => newWith_parse h ha, fun hi => ?_⟩
  obtain ⟨w', m, q, h₁, h₂, h₃, _, h₅⟩ := Check.irCheck_sound (hir ▸ hi)
  exact ⟨w', m, q, h₁, h₂, h₃, h₅⟩

/-- **Layer 2 for every world**, async built-ins included: the parser `xparse` of
`Silmaril.Wasm.JcoTool.XParse` reads the output bytes back as the emitted component `c` (its normal
form), `canon` sections as their definitions and built-ins in order. -/
theorem newWith_xparse {core : ByteArray} {w : World} {o : Out} (h : newWith core w = .ok o) :
    ∃ p c, New.plan core w = .ok p ∧ New.emit p = .ok c ∧ xparse o.bytes = .ok c.norm := by
  obtain ⟨p, c, hp, hc, he, _, _⟩ := newWith_steps h
  exact ⟨p, c, hp, hc, xparse_encode he⟩

/-- **The correctness theorem of `wasm-jco new`, with the read-back of async worlds**:
`newWith_correct`, and the bytes parse back (`xparse`) as the emitted component of the plan. -/
theorem newWith_correct_full {core : ByteArray} {w : World} {o : Out} (h : newWith core w = .ok o) :
    (∃ p, New.plan core w = .ok p ∧ Binary.Lower.coreMod core = .ok p.mod ∧
      List.Forall₂ (New.LiftOk p.mod) p.exports p.lifts ∧
      List.Forall₂ (New.ReqOk p.imports p.exports) (p.mod.importNames.zip p.mod.imports) p.reqs ∧
      ∃ c, New.emit p = .ok c ∧ xparse o.bytes = .ok c.norm) ∧
    (∀ a, o.ast = some a → parse o.bytes = .ok a) ∧
    (o.ir = true → ∃ (w' : Silmaril.Wasm.Jco.Thin.World) (m : CoreMod) (p : Silmaril.Wasm.Jco.Thin.Plan),
      parseComponent o.bytes = .ok (thin w' m p) ∧ m.bytes = core ∧
      recognize .plain w' (CoreModule.imports m) (CoreModule.exports m) = some p ∧
      ∀ C : CoreSem CoreMod, (thin w' m p).denU C = (wrapGlue .plain w' m (importWiring w' p) p.glue).denU C) := by
  obtain ⟨⟨p, hp, h1, h2, h3⟩, h4, h5⟩ := newWith_correct h
  obtain ⟨p', c, hp', hc, hx⟩ := newWith_xparse h
  have e : p' = p := by rw [hp] at hp'; cases hp'; rfl
  subst e
  exact ⟨⟨p', hp, h1, h2, h3, c, hc, hx⟩, h4, h5⟩

end Silmaril.Wasm.JcoTool.Tool
