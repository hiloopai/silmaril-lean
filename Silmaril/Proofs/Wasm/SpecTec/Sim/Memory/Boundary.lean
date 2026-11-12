module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Memory.MemoryFwd
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Equiv.ExecReadMemory

/-!
# The load/store boundary, with the corrected slice bound

`Step_read/load-num-oob` (38) traps when `i + ao.OFFSET + |nt|/8 > |bytes|`;
`Step_read/load-num-val` (39) reads the bytes through `Value.slice?`. The interpreter's strict
slice bound (`il/eval.ml:284`) left a load whose last byte is the memory's last byte with
neither rule (obstruction 2; the original behaviour is `Broken.sliceEvalMl?_boundary`). The port
now uses `≤` (upstream item U2), and the bounds layer matches Core exactly, boundary included:

* `slice?_bytesL`: `bytes[a : k]` on the encoded memory is the image of Core's `readBytes`, at
  every address (both directions: one is defined iff the other is);
* `setSlice_bytesL`: `bytes[a : |w|] = w` on the encoded memory is the image of Core's
  `writeBytes`, at every address;
* `not_loadNumOob_boundary` / `evalExp_loadNumValSlice`: at the boundary no instance of
  `load-num-oob` has the image as its left-hand side, and `load-num-val`'s slice evaluates, to the
  image of the bytes Core reads (`loadBoundary`).

Firing `load-num-val` itself still needs the `$nbytes_` bridge (the encoded constant's bytes),
which is not done here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Memory

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.SpecTec.Equiv.ExecRead
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (aconstV idxV StateDefs GrowDefs)

variable {env : Env}

/-- `CONST at i (LOAD I32 x ao)`, the image of `i32.load`'s redex. -/
abbrev loadCode (A : Value) (i n : Nat) (arg : MemArg) : List Value :=
  [aconstV A i, .case "LOAD" (.tuple [i32V, .opt none, idxV n, memargV arg])]

/-- The bindings a `load` left-hand side forces. -/
theorem binds_load {ρ : VarEnv} {z A : Value} {i n : Nat} {arg : MemArg}
    (he : EvalExp env ρ (.caseE "%;%" (.tupE [.varE "z", .listE [
      .caseE "CONST" (.tupE [.subE (.varE "at") (.varT "addrtype" []) (.varT "numtype" []),
        .varE "i"]),
      .caseE "LOAD" (.tupE [.varE "nt", .optE none, .varE "x", .varE "ao"])]]))
      (cfgV z (loadCode A i n arg))) :
    EvalExp env ρ (.varE "z") z ∧ EvalExp env ρ (.varE "i") (idxV i) ∧
      EvalExp env ρ (.varE "nt") i32V ∧ EvalExp env ρ (.varE "x") (idxV n) ∧
      EvalExp env ρ (.varE "ao") (memargV arg) := by
  obtain ⟨hz, hl⟩ := RefsGC.cfgz_inv he
  have hs := RefsGC.elems_of_list hl
  have ht := RefsGC.elems_of_tup (RefsGC.case_inv (RefsGC.evalExps_get hs 1 rfl rfl))
  exact ⟨hz, const_inv (RefsGC.evalExps_get hs 0 rfl rfl), RefsGC.evalExps_get ht 0 rfl rfl,
    RefsGC.evalExps_get ht 2 rfl rfl, RefsGC.evalExps_get ht 3 rfl rfl⟩

/-- `$size(I32) / 8` written as the load rules write it, in ℚ and back: `4`. -/
theorem evalExp_width32 (G : GrowDefs env) {σ : List (IL.Id × Value)}
    (hnt : EvalExp env (VarEnv.empty.bindVals σ) (.varE "nt") i32V) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.cvtE (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT) (.num (.natN 4)) := by
  have hs := State.evalExp_size G (findDef_bindVals_empty σ _) .i32 hnt
  have e₁ : EvalExp env (VarEnv.empty.bindVals σ)
      (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT) (.num (.ratN 32)) :=
    evalExp_cvtE_iff.2 ⟨_, _, hs, rfl, rfl⟩
  have e₂ : EvalExp env (VarEnv.empty.bindVals σ) (.cvtE (.numE (.natN 8)) .natT .ratT)
      (.num (.ratN 8)) := evalExp_cvtE_iff.2 ⟨_, _, RefsGC.evalExp_num', rfl, rfl⟩
  have e₃ : EvalExp env (VarEnv.empty.bindVals σ)
      (.binE .divOp (.numT .ratT) (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
        (.cvtE (.numE (.natN 8)) .natT .ratT)) (.num (.ratN 4)) :=
    evalExp_binE_iff.2 ⟨_, e₁, .inr ⟨rfl, _, e₂, by
      simp only [binValues, Num.bin, show (8 : ℚ) ≠ 0 by decide, show (32 : ℚ) / 8 = 4 by decide +kernel,
        ↓reduceIte]
      rfl⟩⟩
  exact evalExp_cvtE_iff.2 ⟨_, _, e₃, by simp [Num.cvt], rfl⟩

/-- The effective address `i + ao.OFFSET`. -/
theorem evalExp_effAddr {ρ : VarEnv} {i : Nat} {arg : MemArg}
    (hi : EvalExp env ρ (.varE "i") (idxV i)) (hao : EvalExp env ρ (.varE "ao") (memargV arg)) :
    EvalExp env ρ (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
      (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
      (.num (.natN (i + arg.offset.val))) :=
  RefsGC.evalExp_addNat (RefsGC.evalExp_unpct hi) (RefsGC.evalExp_unpct (RefsGC.evalExp_dot hao rfl))

/-- **`load-num-oob` does not fire at the boundary**: an `i32.load` whose four bytes end exactly at
the end of memory is in bounds. -/
theorem not_loadNumOob_boundary (D : StateDefs env) (G : GrowDefs env) {Dr : Interp} {els : Prop}
    {S F m A c : Value} {bs : List Value} {i n : Nat} {arg : MemArg} (hm : MemAt S F n m)
    (hB : m.field? "BYTES" = some (.list bs)) (hk : i + arg.offset.val + 4 = bs.length) :
    ¬ RuleBody env Dr els [] [] "%~>%" loadNumOobRule
      (.tuple [cfgV (stV S F) (loadCode A i n arg), c]) := by
  rintro ⟨-, ρ₀, σ, hb, -, he, hp⟩
  obtain rfl := bindParams_nil hb
  obtain ⟨hz, hi, hnt, hx, hao⟩ := binds_load (RefsGC.lhs_of_concl he)
  have hc := cmp_true (RefsGC.premW_if (hp _ (List.mem_singleton_self _)))
    (RefsGC.evalExp_addNat (evalExp_effAddr hi hao) (evalExp_width32 G hnt))
    (evalExp_memBytesLen D hz hx hm hB) rfl
  simp only [decide_eq_true_eq] at hc
  omega

/-! ## The bounds layer: slices of the encoded memory are Core's reads and writes -/

/-- The encoded bytes of a sub-array are the slice of the encoded bytes. -/
theorem bytesL_extract (b : ByteArray) (a e : Nat) :
    bytesL (b.extract a e) = ((bytesL b).drop a).take (e - a) := by
  simp only [bytesL, ByteArray.data_extract, Array.toList_extract, List.map_take, List.map_drop]

/-- **Loads.** On the encoded memory, `bytes[a : k]` is defined exactly when Core's `readBytes`
is, and is then the image of the bytes Core reads. -/
theorem slice?_bytesL (b : ByteArray) (a k : Nat) :
    (Value.list (bytesL b)).slice? a k =
      (Silmaril.Wasm.Execution.Memory.readBytes b a k).map (fun r => .list (bytesL r)) := by
  unfold Silmaril.Wasm.Execution.Memory.readBytes
  simp only [Value.slice?, bytesL_length]
  split
  · simp only [Option.map_some, bytesL_extract, Nat.add_sub_cancel_left]
  · rfl

/-- Core's `writeBytes` buffer, as a list: the prefix, the new bytes, the suffix. -/
theorem copySlice_toList (m w : ByteArray) (a : Nat) :
    (ByteArray.copySlice w 0 m a w.size).data.toList =
      m.data.toList.take a ++ w.data.toList ++ m.data.toList.drop (a + w.size) := by
  have hw : w.data.toList.length = w.size := Array.length_toList
  have hmin : min w.size w.data.size = w.size := Nat.min_self _
  have hms : m.data.size = m.size := rfl
  simp only [ByteArray.copySlice, Array.toList_append, Array.toList_extract,
    List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, hmin, hms]
  rw [List.take_of_length_le (l := w.data.toList) (by omega),
    List.take_of_length_le (l := m.data.toList.drop (a + w.size)) (by simp)]

/-- **Stores.** On the encoded memory, `bytes[a : |w|] = w` is defined exactly when Core's
`writeBytes` is, and is then the image of the memory Core writes. -/
theorem setSlice_bytesL (m w : ByteArray) (a : Nat) :
    (Value.list (bytesL m)).setSlice a w.size (.list (bytesL w)) =
      (Silmaril.Wasm.Execution.Memory.writeBytes m a w).map (fun r => .list (bytesL r)) := by
  unfold Silmaril.Wasm.Execution.Memory.writeBytes
  simp only [Value.setSlice, bytesL_length]
  split
  · simp only [Option.map_some, bytesL, copySlice_toList, List.map_append, List.map_take,
      List.map_drop]
  · rfl

/-- **`load-num-val`'s slice evaluates** whenever the four bytes end at or before the end of
memory, the boundary included: under the bindings the left-hand side forces,
`$mem(z, x).BYTES[i + ao.OFFSET : $size(nt)/8]` is the four bytes at the effective address. -/
theorem evalExp_loadNumValSlice (D : StateDefs env) (G : GrowDefs env)
    {σ : List (IL.Id × Value)} {S F m : Value} {bs : List Value} {i n : Nat} {arg : MemArg}
    (hm : MemAt S F n m) (hB : m.field? "BYTES" = some (.list bs))
    (hz : EvalExp env (VarEnv.empty.bindVals σ) (.varE "z") (stV S F))
    (hi : EvalExp env (VarEnv.empty.bindVals σ) (.varE "i") (idxV i))
    (hnt : EvalExp env (VarEnv.empty.bindVals σ) (.varE "nt") i32V)
    (hx : EvalExp env (VarEnv.empty.bindVals σ) (.varE "x") (idxV n))
    (hao : EvalExp env (VarEnv.empty.bindVals σ) (.varE "ao") (memargV arg))
    (hk : i + arg.offset.val + 4 ≤ bs.length) :
    EvalExp env (VarEnv.empty.bindVals σ)
      (.sliceE (.dotE (.callE "mem" [.expA (.varE "z"), .expA (.varE "x")]) "BYTES")
        (.binE .addOp (.numT .natT) (.projE (.uncaseE (.varE "i") "%") 0)
          (.projE (.uncaseE (.dotE (.varE "ao") "OFFSET") "%") 0))
        (.cvtE (.binE .divOp (.numT .ratT)
          (.cvtE (.callE "size" [.expA (.varE "nt")]) .natT .ratT)
          (.cvtE (.numE (.natN 8)) .natT .ratT)) .ratT .natT))
      (.list ((bs.drop (i + arg.offset.val)).take 4)) :=
  evalExp_sliceE_iff.2 ⟨_, _, _, RefsGC.evalExp_dot (evalExp_mem_of D hz hx hm) hB,
    evalExp_effAddr hi hao, evalExp_width32 G hnt,
    Equiv.ExecReadMemory.slice?_eq_some_iff.2 ⟨bs, rfl, hk, rfl⟩⟩

/-- **Core steps at the boundary**: `i32.load` reads its four bytes whenever they end at or
before the end of memory, so `MemoryStep.loadIntVal` applies at `a + 4 = |bytes|`. -/
theorem loadBoundary_core {mi : MemInst} {a : Nat} (hk : a + 4 = mi.bytes.size) :
    ∃ c, Silmaril.Wasm.Execution.Memory.load mi.bytes a (IntType.i32.width / 8) = some c := by
  have hle : a + IntType.i32.width / 8 ≤ mi.bytes.size := by
    simp only [IntType.width]
    omega
  unfold Silmaril.Wasm.Execution.Memory.load Silmaril.Wasm.Execution.Memory.readBytes
  simp only [hle, ↓reduceIte]
  exact ⟨_, rfl⟩

/-- **The boundary at the Core encoding** (obstruction 2, resolved by U2). For a configuration
`i32.load x arg` at address `i` whose four bytes end at the end of memory `x`: Core reads four
bytes `r`, no instance of `load-num-oob` in `simEnv B` has the image as its left-hand side, and the
slice `load-num-val` compares against is the image of `r`. -/
theorem loadBoundary {H : Type} (B : Builtins) (hn : H → String) {s : Store H} {f : Frame}
    {x : MemIdx} {arg : MemArg} {a : AddrType} {i : BitVec a.intType.width} {ma : Nat}
    {mi : MemInst} (hm : s.mem? f x = some (ma, mi))
    (hk : effAddr i.toNat arg + 4 = mi.bytes.size) :
    (∃ c, Silmaril.Wasm.Execution.Memory.load mi.bytes (effAddr i.toNat arg)
      (IntType.i32.width / 8) = some c) ∧
    (∀ (Dr : Interp) (els : Prop) (c : Value),
      ¬ RuleBody (simEnv B) Dr els [] [] "%~>%" loadNumOobRule
        (.tuple [configV hn ⟨s, f, [aconst a i, .plain (.intLoad .i32 none x arg)]⟩, c])) ∧
    ∃ r, Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat arg) 4 = some r ∧
      (Value.list (bytesL mi.bytes)).slice? (effAddr i.toNat arg) 4 = some (.list (bytesL r)) := by
  refine ⟨loadBoundary_core hk, fun Dr els c => ?_, ?_⟩
  · have hk' : i.toNat + arg.offset.val + 4 = (bytesL mi.bytes).length := by
      rw [bytesL_length]; exact hk
    rw [State.configV_eq]
    simp only [State.adminsToV_cons, State.adminsToV_nil, State.adminToV_aconst]
    exact not_loadNumOob_boundary (State.stateDefs_simEnv B) (State.growDefs_simEnv B)
      (memAt_of_mem? hn hm) (memInstV_BYTES mi) hk'
  · have hr : Silmaril.Wasm.Execution.Memory.readBytes mi.bytes (effAddr i.toNat arg) 4 =
        some (mi.bytes.extract (effAddr i.toNat arg) (effAddr i.toNat arg + 4)) := by
      unfold Silmaril.Wasm.Execution.Memory.readBytes
      simp only [show effAddr i.toNat arg + 4 ≤ mi.bytes.size by omega, ↓reduceIte]
    exact ⟨_, hr, by rw [slice?_bytesL, hr]; rfl⟩

end Silmaril.Wasm.SpecTec.Sim.Memory
