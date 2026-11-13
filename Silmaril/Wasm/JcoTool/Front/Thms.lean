module

public import Silmaril.Wasm.JcoTool.Front.Defs
public import Silmaril.Wasm.JcoTool.LayoutRef.Thms
public import Silmaril.Wasm.JcoTool.LayoutRefX.Thms
public import Silmaril.Wasm.Perf.JcoNew.Thms

/-!
# The world `wasm-jco new` works on: what is guaranteed

* `worldFullOf_utf8`: the world `wasm-jco new` passes on has the UTF-8 string encoding, the
  only one the canonical ABI code of `NewI` implements.
* `worldFullOf_eq`: it is `WorldMerge.liveWorld` of the decoded worlds (the sections of the
  module, or the `--wit` world) and the module's import names, as decoded by silmaril's
  verified core decoder.

* `newValid_correct`, `newValid_valid`: what `wasm-jco new` writes is `ToolV.newFullR` of
  the prepared module (so `newFullR_correct` applies), and its bytes read back as a reference
  component that is `Reference.Valid` at `Features.all`, with the layout reading.

The entry-point theorems (`ToolI.newFull_correct`, `ToolV.newFullR_correct`, …) hold for every
world, so for this one. That `liveWorld` is the world wit-component builds is tested
(`tools/wasm-jco/tests/corpus.sh`, `wit-component.sh`), not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Front

open Silmaril.Wasm.Wit.Binary

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem checkUtf8_ok {wf wf' : WorldFull} (h : checkUtf8 wf = .ok wf') :
    wf' = wf ∧ wf'.encoding = .utf8 := by
  unfold checkUtf8 at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem worldFullOf_eq {core : ByteArray}
    {wit : Option ((String × String) × List (String × String) × String)} {wf : WorldFull}
    (h : worldFullOf core wit = .ok wf) :
    ∃ names wfs, WorldMerge.coreImportNames core = .ok names ∧ worldsOf core wit = .ok wfs ∧
      WorldMerge.liveWorld wfs names = .ok wf ∧ wf.encoding = .utf8 := by
  unfold worldFullOf at h
  obtain ⟨names, hn, h⟩ := except_bind_ok h
  obtain ⟨wfs, hs, h⟩ := except_bind_ok h
  obtain ⟨w, hw, h⟩ := except_bind_ok h
  obtain ⟨rfl, he⟩ := checkUtf8_ok h
  exact ⟨names, wfs, hn, hs, hw, he⟩

theorem worldFullOf_utf8 {core : ByteArray}
    {wit : Option ((String × String) × List (String × String) × String)} {wf : WorldFull}
    (h : worldFullOf core wit = .ok wf) : wf.encoding = .utf8 := by
  obtain ⟨_, _, _, _, _, he⟩ := worldFullOf_eq h
  exact he

theorem newValid_correct {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newValid core wf = .ok o) :
    ∃ core' ct, prepareCore core = .ok core' ∧ ToolV.newFullR core' wf = .ok o ∧
      ToolV.refCheckX o.bytes = .ok ct := by
  unfold newValid at h
  rw [Silmaril.Wasm.Perf.JcoNew.newFullRF_eq] at h
  obtain ⟨core', hc, h⟩ := except_bind_ok h
  obtain ⟨o', ho, h⟩ := except_bind_ok h
  revert h
  cases hr : ToolV.refCheckX o'.bytes with
  | ok ct => intro h; cases h; exact ⟨core', ct, hc, ho, hr⟩
  | error e => intro h; cases h

theorem newValid_valid {core : ByteArray} {wf : WorldFull} {o : Tool.Out}
    (h : newValid core wf = .ok o) :
    ∃ core' x c ct, prepareCore core = .ok core' ∧ ToolV.newFullR core' wf = .ok o ∧
      xparse o.bytes = .ok x ∧ LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x = some c ∧
      Silmaril.Wasm.Component.Reference.Valid Silmaril.Wasm.Component.Features.all c ct := by
  obtain ⟨core', ct, hc, ho, hr⟩ := newValid_correct h
  obtain ⟨x, c, hx, ht, hv, _⟩ := ToolV.refCheckX_valid hr
  exact ⟨core', x, c, ct, hc, ho, hx, ht, hv⟩

end Silmaril.Wasm.JcoTool.Front
