module

public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Defs

/-!
# Round 4 integration: `ConfigOk` gives `ReadValid`

Track r4-read stated its validity facts as `Round4Read.ReadValid` (store bounds and index
resolution at every depth of the active code) and left open that Core validity implies them.
Here: `readValid_of_configOk`. The proof recurses on Core's `AdminsOk`/`AdminOk` derivation,
carrying `CtxRes` (the context's indices resolve); a frame's body is checked against the frame's
own `FrameOk`, which with the store's `StoreOk` is a `StateOk`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4Int

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round4Read (ReadValid codeIdx adminIdx)

variable {H : Type} {s : Store H} {f : Frame}

/-- Core's `StateOk` resolves every index of its context. -/
theorem ctxRes_of_stateOk {C : Context} (h : StateOk s f C) : CtxRes s f C where
  table hx := by obtain ⟨_, _, e, -⟩ := h.table hx; simp [e]
  mem hx := by obtain ⟨_, _, e, -⟩ := h.mem hx; simp [e]
  elem hy := by obtain ⟨_, _, e, -⟩ := h.elem hy; simp [e]
  data hy := by obtain ⟨_, _, e⟩ := h.data hy; simp [e]

/-- `CtxRes` depends only on the context's frame view. -/
theorem CtxRes.of_frameView {C C' : Context} (h : CtxRes s f C)
    (e : C'.frameView = C.frameView) : CtxRes s f C' where
  table hx := h.table (by simpa [Context.frameView] using (congrArg Context.tables e) ▸ hx)
  mem hx := h.mem (by simpa [Context.frameView] using (congrArg Context.mems e) ▸ hx)
  elem hy := h.elem (by simpa [Context.frameView] using (congrArg Context.elems e) ▸ hy)
  data hy := h.data (by simpa [Context.frameView] using (congrArg Context.datas e) ▸ hy)

/-- A valid table instruction names only resolving indices. -/
theorem idxOk_of_tableInstrOk {C : Context} {i : Instr} {it : InstrType} (R : CtxRes s f C)
    (h : TableInstrOk C i it) : Round4Read.Instr.IdxOk s f i := by
  cases h with
  | tableGet hx => exact R.table hx
  | tableSet hx => exact R.table hx
  | tableSize hx => exact R.table hx
  | tableGrow hx => exact R.table hx
  | tableFill hx => exact R.table hx
  | tableCopy h₁ h₂ _ => exact ⟨R.table h₁, R.table h₂⟩
  | tableInit hx he _ => exact ⟨R.table hx, R.elem he⟩
  | elemDrop he => exact R.elem he

/-- A valid memory instruction names only resolving indices. -/
theorem idxOk_of_memoryInstrOk {C : Context} {i : Instr} {it : InstrType} (R : CtxRes s f C)
    (h : MemoryInstrOk C i it) : Round4Read.Instr.IdxOk s f i := by
  cases h with
  | memorySize hx => exact R.mem hx
  | memoryGrow hx => exact R.mem hx
  | memoryFill hx => exact R.mem hx
  | memoryCopy h₁ h₂ => exact ⟨R.mem h₁, R.mem h₂⟩
  | memoryInit hx hd => exact ⟨R.mem hx, R.data hd⟩
  | dataDrop hd => exact R.data hd
  | intLoad hx _ => exact R.mem hx
  | intLoadPack hx _ _ => exact R.mem hx
  | floatLoad hx _ => exact R.mem hx
  | intStore hx _ => exact R.mem hx
  | intStorePack hx _ _ => exact R.mem hx
  | floatStore hx _ => exact R.mem hx
  | vecLoad hx _ => exact R.mem hx
  | vecLoadLane hx _ _ => exact R.mem hx
  | vecStore hx _ => exact R.mem hx
  | vecStoreLane hx _ _ => exact R.mem hx

/-- **A valid instruction names only resolving indices.** -/
theorem idxOk_of_instrOk {C : Context} {i : Instr} {it : InstrType} (R : CtxRes s f C)
    (h : InstrOk C i it) : Round4Read.Instr.IdxOk s f i := by
  by_cases ht : i.IsTableI
  · exact idxOk_of_tableInstrOk R (h.table_inv ht)
  by_cases hm : i.IsMemI
  · exact idxOk_of_memoryInstrOk R (h.memory_inv hm)
  cases i <;> first | exact trivial | exact absurd trivial ht | exact absurd trivial hm

/-- `codeIdx` along an append. -/
theorem codeIdx_append {f : Frame} :
    ∀ {l₁ l₂ : List Admin}, codeIdx s f l₁ → codeIdx s f l₂ → codeIdx s f (l₁ ++ l₂)
  | [], _, _, h₂ => h₂
  | _ :: _, _, h₁, h₂ => ⟨h₁.1, codeIdx_append h₁.2 h₂⟩

mutual
/-- **Every index of a valid administrative instruction resolves**, at every depth. -/
theorem adminIdx_of_ok (hS : StoreOk s) :
    ∀ {f : Frame} {C : Context} {a : Admin} {it : InstrType}, CtxRes s f C →
      AdminOk s C a it → adminIdx s f a
  | _, _, _, _, R, .plain h => idxOk_of_instrOk R h
  | _, _, _, _, _, .callRefType _ _ => trivial
  | _, _, _, _, _, .returnCallRefType _ _ _ _ _ => trivial
  | _, _, _, _, _, .ref _ => trivial
  | _, C, _, _, R, .label (t' := t') _ _ hb =>
    adminsIdx_of_ok hS (R.of_frameView (C' := C.withLabel t') rfl) hb
  | _, _, _, _, _, .frame (C' := C') (ts := ts) hf _ hb _ =>
    adminsIdx_of_ok hS ((ctxRes_of_stateOk ⟨hS, hf⟩).of_frameView
      (C' := { C' with return_ := some ts }) rfl) hb
  | _, _, _, _, R, .handler _ hb => adminsIdx_of_ok hS R hb
  | _, _, _, _, _, .trap _ => trivial
  | _, _, _, _, _, .throwRefInits _ => trivial

/-- **Every index of valid code resolves**, at every depth. -/
theorem adminsIdx_of_ok (hS : StoreOk s) :
    ∀ {f : Frame} {C : Context} {l : List Admin} {it : InstrType}, CtxRes s f C →
      AdminsOk s C l it → codeIdx s f l
  | _, _, _, _, _, .nil => trivial
  | _, _, _, _, R, .single h => ⟨adminIdx_of_ok hS R h, trivial⟩
  | _, _, _, _, R, .seq h₁ _ h₂ =>
    codeIdx_append (adminsIdx_of_ok hS R h₁)
      (adminsIdx_of_ok hS (R.of_frameView (Context.initLocals_frameView _ _)) h₂)
  | _, _, _, _, R, .cons ha _ hs =>
    ⟨adminIdx_of_ok hS R ha,
      adminsIdx_of_ok hS (R.of_frameView (Context.initLocals_frameView _ _)) hs⟩
  | _, _, _, _, R, .sub h _ _ => adminsIdx_of_ok hS R h
  | _, _, _, _, R, .frame h _ => adminsIdx_of_ok hS R h
end

/-- **Core validity and the store bounds give `ReadValid`.** -/
theorem readValid_of_configOk {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hs : Integrate.StoreOk c.store) : ReadValid c := by
  obtain ⟨C, hst, hcode⟩ := hc
  exact ⟨hs, adminsIdx_of_ok hst.1 (ctxRes_of_stateOk hst) hcode⟩

/-- **A valid, bounded configuration satisfies `ReadValid`.** -/
theorem readValid_of_bounded {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (hb : Round4.Bounded c) : ReadValid c :=
  readValid_of_configOk hc hb.store

end Silmaril.Wasm.SpecTec.Sim.Round4Int
