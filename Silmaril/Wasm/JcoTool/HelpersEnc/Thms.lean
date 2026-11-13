module

public import Silmaril.Wasm.JcoTool.HelpersEnc.Defs
public import Silmaril.Proofs.Wasm.JcoTool.HelpersEnc.Checks
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Perf.CoreDecode.Thms

/-!
# The helper encoder of `wasm-jco new` is correct for every input it is used on

`wasm-jco new` writes the `shim` and `fixup` modules of wit-component's indirect-call pattern
as `CMod.encode (New.shimMod tys)` and `CMod.encode (New.fixupMod tys)` (`New.emit`,
`NewI.emit`). For every list `tys` of slot types (fewer than `2 ^ 31` for the shim, whose
trampolines push the slot number as an `i32.const`; fewer than `2 ^ 32` for the fixup):

* **`shim_correct`**: when the encoder succeeds, its bytes are exactly silmaril's canonical
  encoding of `shimAst tys` (`encodeModule?`), so they encode `shimAst tys` in the Core 3.0
  binary grammar (functional: nothing else), and `shimAst tys` passes `Helpers.isShim`;
* **`fixup_correct`**: the same for `fixupAst tys` and `Helpers.isFixup`;
* `shim_decode`, `fixup_decode`: whatever silmaril's decoder returns for those bytes is that
  module, so the check `Helpers.helperOk` of `ToolV.newFullV` passes on them whenever the
  decoder accepts them (`shim_helperOk`, `fixup_helperOk`).

This replaces translation validation of the helper encoder (`Helpers.newFullV_correct`) by a
proof for all inputs; the per-output check stays in the tool.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.HelpersEnc

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen.Exe
open Silmaril.Wasm.Component (CoreFuncTy)

theorem encU32_ok_lt {n : Nat} {b : List UInt8} (h : encU32 n = .ok b) : n < 2 ^ 32 := by
  unfold encU32 at h
  by_cases hn : n < 2 ^ 32
  · exact hn
  · have hn' : ¬ n < 4294967296 := hn
    simp [hn'] at h

theorem encList_ok_mem {α : Type} {g : α → Except String (List UInt8)} {xs : List α}
    {v : List UInt8} (h : encList g xs = .ok v) : ∀ x ∈ xs, ∃ c, g x = .ok c := by
  induction xs generalizing v with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
    intro x hx
    cases hy : g y with
    | error e => simp [encList, hy, bind, Except.bind] at h
    | ok c =>
      cases hys : encList g ys with
      | error e => simp [encList, hy, hys, bind, Except.bind] at h
      | ok cs =>
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨c, hy⟩
        · exact ih hys x hx

theorem encVec_ok {α : Type} {g : α → Except String (List UInt8)} {xs : List α}
    {v : List UInt8} (h : encVec g xs = .ok v) :
    xs.length < 2 ^ 32 ∧ ∀ x ∈ xs, ∃ c, g x = .ok c := by
  unfold encVec at h
  cases hl : encU32 xs.length with
  | error e => simp [hl, bind, Except.bind] at h
  | ok n =>
    cases hs : encList g xs with
    | error e => simp [hl, hs, bind, Except.bind] at h
    | ok bs => exact ⟨encU32_ok_lt hl, encList_ok_mem hs⟩

/-- A slot type the type section encodes has fewer than `2 ^ 32` parameters. -/
theorem params_lt {t : CoreFuncTy} {c : List UInt8} (h : encRecType (ftAst t) = .ok c) :
    t.params.length < 2 ^ 32 := by
  have h' : encFuncType ⟨t.params.map .num, t.results.map .num⟩ = .ok c := h
  unfold encFuncType at h'
  cases hp : encVec encValType (t.params.map ValType.num) with
  | error e => simp [hp, bind, Except.bind] at h'
  | ok v => simpa using (encVec_ok hp).1

/-- The bound on parameters follows from a successful encoding of the types. -/
theorem params_of_types {tys : List CoreFuncTy} {ty : Silmaril.Parse.ByteParse.Bytes}
    (h : CMod.vecSec 1 CMod.funcType tys = some ty) : ∀ t ∈ tys, t.params.length ≤ 2 ^ 32 := by
  obtain ⟨v, hv, _⟩ := vecSec_ok (types_rel tys) h
  intro t ht
  obtain ⟨c, hc⟩ := (encVec_ok hv).2 (ftAst t) (List.mem_map_of_mem ht)
  exact Nat.le_of_lt (params_lt hc)

/-- **The shim encoder is correct.** -/
theorem shim_correct {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 31) {b : ByteArray}
    (h : CMod.encode (New.shimMod tys) = some b) :
    encodeModule? (shimAst tys) = .ok b.data.toList ∧
      Binary.Core.Encodes b.data.toList (shimAst tys) ∧ Helpers.isShim (shimAst tys) = true := by
  obtain ⟨ty, hty, _⟩ := Option.bind_eq_some_iff.mp h
  have hp : ∀ t ∈ tys, t.params.length ≤ 2 ^ 32 := params_of_types hty
  have he : encodeModule? (shimAst tys) = .ok b.data.toList := shim_encode hn hp h
  exact ⟨he, encodeModule?_sound he, shimAst_isShim (Nat.lt_trans hn (by decide)) hp⟩

/-- **The fixup encoder is correct.** -/
theorem fixup_correct {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 32) {b : ByteArray}
    (h : CMod.encode (New.fixupMod tys) = some b) :
    encodeModule? (fixupAst tys) = .ok b.data.toList ∧
      Binary.Core.Encodes b.data.toList (fixupAst tys) ∧ Helpers.isFixup (fixupAst tys) = true := by
  have he : encodeModule? (fixupAst tys) = .ok b.data.toList := fixup_encode hn h
  exact ⟨he, encodeModule?_sound he, fixupAst_isFixup hn⟩

/-- Silmaril's decoder can only return `shimAst tys` for the shim's bytes. -/
theorem shim_decode {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 31) {b : ByteArray}
    (h : CMod.encode (New.shimMod tys) = some b) {m : Module} (hd : Binary.Core.decode? b = some m) :
    m = shimAst tys :=
  Binary.Core.functional (Binary.Core.decode?_sound hd) (shim_correct hn h).2.1

/-- Silmaril's decoder can only return `fixupAst tys` for the fixup's bytes. -/
theorem fixup_decode {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 32) {b : ByteArray}
    (h : CMod.encode (New.fixupMod tys) = some b) {m : Module}
    (hd : Binary.Core.decode? b = some m) : m = fixupAst tys :=
  Binary.Core.functional (Binary.Core.decode?_sound hd) (fixup_correct hn h).2.1

/-- The tool's check passes on a shim the decoder accepts. -/
theorem shim_helperOk {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 31) {b : ByteArray}
    (h : CMod.encode (New.shimMod tys) = some b) {m : Module}
    (hd : Binary.Core.decode? b = some m) : Helpers.helperOk b = true := by
  have hm : m = shimAst tys := shim_decode hn h hd
  simp [Helpers.helperOk, Silmaril.Wasm.Perf.CoreDecode.decodeF_eq, hd, hm, (shim_correct hn h).2.2]

/-- The tool's check passes on a fixup the decoder accepts. -/
theorem fixup_helperOk {tys : List CoreFuncTy} (hn : tys.length < 2 ^ 32) {b : ByteArray}
    (h : CMod.encode (New.fixupMod tys) = some b) {m : Module}
    (hd : Binary.Core.decode? b = some m) : Helpers.helperOk b = true := by
  have hm : m = fixupAst tys := fixup_decode hn h hd
  simp [Helpers.helperOk, Silmaril.Wasm.Perf.CoreDecode.decodeF_eq, hd, hm, (fixup_correct hn h).2.2]

end Silmaril.Wasm.JcoTool.HelpersEnc
