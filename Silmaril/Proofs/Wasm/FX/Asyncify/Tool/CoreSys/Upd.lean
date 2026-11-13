module

public import Silmaril.Wasm.FX.Asyncify.Tool.CoreSys.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim.Seg

/-!
# The host's update of a Core store exists

`hostUpd_exists`: from a store holding the program, the globals and the memory, setting
`state := 2` and writing the answers as aligned words in bounds gives a store with `HostUpd`.
So the `round` case of `CoreObs`, which asks for every such store, is not vacuous.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSys

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Memory
open Silmaril.Wasm.FX.Asyncify.Tool
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core
open Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

variable {H : Type} {cap : Nat} {E : Env} {mi : ModuleInst}

theorem store_some (bytes : ByteArray) {a : Nat} (v : W) (h : a + 4 ≤ bytes.size) :
    ∃ b, store bytes a (count := 4) v = some b := by
  have hbound : a + (encodeLE 4 v.toNat).size ≤ bytes.size := by rw [encodeLE_size]; exact h
  refine ⟨(encodeLE 4 v.toNat).copySlice 0 bytes a (encodeLE 4 v.toNat).size, ?_⟩
  show writeBytes bytes a (encodeLE 4 (v.setWidth 32).toNat) = _
  rw [BitVec.setWidth_eq]
  simp only [writeBytes, hbound, ↓reduceIte]

/-- One aligned word written into the bytes. -/
theorem memAre_write1 {s : Store H} {mem : Nat → W} {a : Nat} (ha : a % 4 = 0)
    (hcap : a + 4 ≤ cap) (v : W) (hM : MemAre s ⟨[], mi⟩ mem cap) :
    ∃ s' : Store H, MemAre s' ⟨[], mi⟩ (upd mem a v) cap ∧ s'.funcs = s.funcs ∧
      ∀ g, s'.global? ⟨[], mi⟩ g = s.global? ⟨[], mi⟩ g := by
  obtain ⟨ma, mi', hm, hsz, hw⟩ := hM
  obtain ⟨b, hb⟩ := store_some mi'.bytes v (by rw [hsz]; exact hcap)
  exact ⟨s.setMem ma { mi' with bytes := b }, memAre_store ⟨ma, mi', hm, hsz, hw⟩ hm ha v hb,
    rfl, fun _ => rfl⟩

/-- Aligned words written from an aligned address, in bounds. -/
theorem memAre_writeWords {s : Store H} :
    ∀ (ws : List W) {mem : Nat → W} {a : Nat}, a % 4 = 0 → a + 4 * ws.length ≤ cap →
      MemAre s ⟨[], mi⟩ mem cap →
      ∃ s' : Store H, MemAre s' ⟨[], mi⟩ (writeWords mem a ws) cap ∧ s'.funcs = s.funcs ∧
        ∀ g, s'.global? ⟨[], mi⟩ g = s.global? ⟨[], mi⟩ g
  | [], _, _, _, _, hM => ⟨s, hM, rfl, fun _ => rfl⟩
  | w :: ws, mem, a, ha, hcap, hM => by
    have hl : (w :: ws).length = ws.length + 1 := rfl
    obtain ⟨s₁, hM₁, hf₁, hg₁⟩ := memAre_write1 ha (by omega) w hM
    obtain ⟨s₂, hM₂, hf₂, hg₂⟩ := memAre_writeWords (s := s₁) ws (mem := upd mem a w)
      (a := a + 4) (by omega) (by omega) hM₁
    exact ⟨s₂, hM₂, hf₂.trans hf₁, fun g => (hg₂ g).trans (hg₁ g)⟩

/-- **The host's update exists.** -/
theorem hostUpd_exists {s : Store H} {gs : List W} {mem : Nat → W} {ws : List W}
    (hH : HoldsProg s mi E) (hg : GlobalsAre s ⟨[], mi⟩ gs) (hM : MemAre s ⟨[], mi⟩ mem cap)
    (h0 : 0 < gs.length) (hws : 4 * ws.length ≤ cap) :
    ∃ s'' : Store H, HostUpd cap E mi s'' gs mem ws := by
  obtain ⟨a, gi, hgl, -, -⟩ := hg.2.1 0 h0
  have hG₁ : GlobalsAre (s.setGlobal a (Val.i32 2)) ⟨[], mi⟩ (gs.set 0 2) :=
    globalsAre_set hg hgl h0 2
  obtain ⟨s'', hM'', hf, hgg⟩ := memAre_writeWords (s := s.setGlobal a (Val.i32 2)) ws
    (mem := mem) (a := 0) rfl (by omega) hM
  exact ⟨s'', holdsProg_of_funcs hf hH, globalsAre_of_eq hgg hG₁, hM''⟩

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSys
