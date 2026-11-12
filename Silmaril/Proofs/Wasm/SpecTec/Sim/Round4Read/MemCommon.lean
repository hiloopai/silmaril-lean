module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round4Read.TableInit

/-!
# Shared readers for the memory rules

The `memory.*` counterparts of the table readers: the opcode decoders, `|$mem(z, x).BYTES|` and
`|$data(z, y).BYTES|` for resolved indices, and the store bounds on memories and data segments.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Read

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open State (idxV aconstV)

variable {H : Type} {hn : H → String}

theorem head_memoryCopy {a : Admin} (h : Typing.adminHead a = "MEMORY.COPY") :
    ∃ x y, a = .plain (.memoryCopy x y) := by
  revert h
  admin_head_inv

theorem head_memoryInit {a : Admin} (h : Typing.adminHead a = "MEMORY.INIT") :
    ∃ x y, a = .plain (.memoryInit x y) := by
  revert h
  admin_head_inv

theorem head_memorySize {a : Admin} (h : Typing.adminHead a = "MEMORY.SIZE") :
    ∃ x, a = .plain (.memorySize x) := by
  revert h
  admin_head_inv

theorem decode_memoryCopy {a : Admin} {X : Value} (h : adminToV a = .case "MEMORY.COPY" X) :
    ∃ (x y : MemIdx), a = .plain (.memoryCopy x y) ∧ X = .tuple [idxV x.toNat, idxV y.toNat] := by
  obtain ⟨x, y, rfl⟩ := head_memoryCopy (Typing.adminToV_case h).symm
  refine ⟨x, y, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

theorem decode_memoryInit {a : Admin} {X : Value} (h : adminToV a = .case "MEMORY.INIT" X) :
    ∃ (x : MemIdx) (y : DataIdx), a = .plain (.memoryInit x y) ∧
      X = .tuple [idxV x.toNat, idxV y.toNat] := by
  obtain ⟨x, y, rfl⟩ := head_memoryInit (Typing.adminToV_case h).symm
  refine ⟨x, y, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

theorem decode_memorySize {a : Admin} {X : Value} (h : adminToV a = .case "MEMORY.SIZE" X) :
    ∃ x : MemIdx, a = .plain (.memorySize x) ∧ X = idxV x.toNat := by
  obtain ⟨x, rfl⟩ := head_memorySize (Typing.adminToV_case h).symm
  refine ⟨x, rfl, ?_⟩
  injection h with _ h₂
  exact h₂.symm

/-- Under the store bounds, a resolved memory has fewer than `2 ^ 32` bytes. -/
theorem mem_lt32 {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (hs : Integrate.StoreOk s) (hm : s.mem? f x = some (ma, mi)) : mi.bytes.size < 2 ^ 32 :=
  (hs.mems mi (List.mem_of_getElem? (Memory.Store.mem?_eq_some hm).2)).2

/-- Under the store bounds, a resolved memory is a whole number of pages. -/
theorem mem_pages {s : Store H} {f : Frame} {x : MemIdx} {ma : Nat} {mi : MemInst}
    (hs : Integrate.StoreOk s) (hm : s.mem? f x = some (ma, mi)) :
    mi.bytes.size % Silmaril.Wasm.Execution.Memory.pageSize = 0 :=
  (hs.mems mi (List.mem_of_getElem? (Memory.Store.mem?_eq_some hm).2)).1

/-- Under the store bounds, a resolved data segment has fewer than `2 ^ 32` bytes. -/
theorem data_lt32 {s : Store H} {f : Frame} {y : DataIdx} {da : Nat} {di : DataInst}
    (hs : Integrate.StoreOk s) (hd : s.data? f y = some (da, di)) : di.bytes.size < 2 ^ 32 :=
  hs.aggs.datas di (List.mem_of_getElem? (State.Store.data?_eq_some hd).2)

variable (B : Builtins)

/-- `|$mem(z, x).BYTES|` for a resolved memory, in a rule scope. -/
theorem evalExp_memLen' {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {x : MemIdx}
    {ma : Nat} {mi : MemInst} {zx : IL.Id}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fx : (VarEnv.empty.bindVals σ).findVal? zx = some (idxV x.toNat))
    (hm : s.mem? f x = some (ma, mi)) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE zx)]) "BYTES"))
      (.num (.natN mi.bytes.size)) := by
  have h := Memory.evalExp_memBytesLen (State.stateDefs_simEnv B) (evalExp_var fz)
    (evalExp_var fx) (Memory.memAt_of_mem? hn hm) (Memory.memInstV_BYTES mi)
  rwa [Memory.bytesL_length] at h

/-- `|$data(z, y).BYTES|` for a resolved data segment, in a rule scope. -/
theorem evalExp_dataLen' {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {y : DataIdx}
    {da : Nat} {di : DataInst} {zy : IL.Id}
    (fz : (VarEnv.empty.bindVals σ).findVal? "z" = some (stV (storeV hn s) (frameV f)))
    (fy : (VarEnv.empty.bindVals σ).findVal? zy = some (idxV y.toNat))
    (hd : s.data? f y = some (da, di)) :
    EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.lenE (.dotE (.callE "data" [.expA (.varE "z"), .expA (.varE zy)]) "BYTES"))
      (.num (.natN di.bytes.size)) := by
  have h := RefsGC.evalExp_len (RefsGC.evalExp_dot (Memory.evalExp_data_of
    (State.stateDefs_simEnv B) (evalExp_var fz) (evalExp_var fy) (Memory.dataAt_of_data? hn hd))
    (Memory.dataInstV_BYTES di))
  rwa [Memory.bytesL_length] at h

end Silmaril.Wasm.SpecTec.Sim.Round4Read
