module

public import Silmaril.Wasm.SpecTec.Sim.Round4.Defs
public import Silmaril.Wasm.SpecTec.Sim.BwdPureStep.Thms
public import Silmaril.Wasm.SpecTec.Sim.BwdRead.Thms
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms

/-!
# Round 4: what Core validity says about the active code

`ConfigOk c ts` types the active code in a context `C` with `StateOk c.store c.frame C`. Every
administrative instruction of the code (at top level) is typed by `AdminOk` in a context that
differs from `C` only in its locals (`adminsOk_mem`: the sequencing rules only initialise
locals). So every index a top-level instruction mentions resolves in the frame's module and the
store (`mem?_of_configOk`, `table?_of_configOk`): what SpecTec's `table.grow-fail` and
`memory.grow-fail` (`Step` 16, 27) do not check, and Core's `growFail` does.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round4

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **Every top-level instruction of typed code is typed**, in a context with the same
non-local fields. -/
theorem adminsOk_mem {s : Store H} :
    ∀ {C : Context} {l : List Admin} {it : InstrType}, AdminsOk s C l it → ∀ a ∈ l,
      ∃ C' it', AdminOk s C' a it' ∧ C'.frameView = C.frameView
  | _, _, _, .nil, _, h => absurd h List.not_mem_nil
  | C, _, it, .single h, a, ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact ⟨C, it, h, rfl⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, a, ha => by
    rcases List.mem_append.1 ha with h | h
    · exact adminsOk_mem h₁ a h
    · obtain ⟨C', it', h', e⟩ := adminsOk_mem h₂ a h
      exact ⟨C', it', h', e.trans (Context.initLocals_frameView C xs₁)⟩
  | C, _, _, .cons (a := b) (xs₁ := xs₁) hb _ hs, a, ha => by
    rcases List.mem_cons.1 ha with rfl | h
    · exact ⟨C, _, hb, rfl⟩
    · obtain ⟨C', it', h', e⟩ := adminsOk_mem hs a h
      exact ⟨C', it', h', e.trans (Context.initLocals_frameView C xs₁)⟩
  | _, _, _, .sub h _ _, a, ha => adminsOk_mem h a ha
  | _, _, _, .frame h _, a, ha => adminsOk_mem h a ha

/-- **A top-level source instruction of a valid configuration is valid** (other than the
administrative `throw_ref`, which `AdminOk` also types directly), in a context with the frame's
non-local fields. -/
theorem instrOk_of_configOk {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) {i : Instr}
    (hi : Admin.plain i ∈ c.code) (hne : i ≠ .throwRef) :
    ∃ C C' it, StateOk c.store c.frame C ∧ InstrOk C' i it ∧ C'.frameView = C.frameView := by
  obtain ⟨C, hst, hcode⟩ := hc
  obtain ⟨C', it, ha, e⟩ := adminsOk_mem hcode _ hi
  cases ha with
  | plain h => exact ⟨C, C', it, hst, h, e⟩
  | throwRefInits _ => exact absurd rfl hne

/-- The memories of two contexts with the same frame view agree. -/
theorem mems_of_frameView {C C' : Context} (e : C'.frameView = C.frameView) :
    C'.mems = C.mems := by
  have h := congrArg Context.mems e
  simpa [Context.frameView] using h

/-- The tables of two contexts with the same frame view agree. -/
theorem tables_of_frameView {C C' : Context} (e : C'.frameView = C.frameView) :
    C'.tables = C.tables := by
  have h := congrArg Context.tables e
  simpa [Context.frameView] using h

/-- **`memory.grow x` in valid code names a memory of the store.** -/
theorem mem?_of_configOk {c : Config H} {ts : List CValType} (hc : ConfigOk c ts) {x : MemIdx}
    (hi : Admin.plain (.memoryGrow x) ∈ c.code) :
    ∃ ma mi, c.store.mem? c.frame x = some (ma, mi) := by
  obtain ⟨C, C', it, hst, h, e⟩ := instrOk_of_configOk hc hi (by simp)
  cases h.memory_inv trivial with
  | memoryGrow hx =>
    rw [mems_of_frameView e] at hx
    obtain ⟨ma, mi, hm, -⟩ := hst.mem hx
    exact ⟨ma, mi, hm⟩

/-- **`table.grow x` in valid code names a table of the store.** -/
theorem table?_of_configOk {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    {x : TableIdx} (hi : Admin.plain (.tableGrow x) ∈ c.code) :
    ∃ ta ti, c.store.table? c.frame x = some (ta, ti) := by
  obtain ⟨C, C', it, hst, h, e⟩ := instrOk_of_configOk hc hi (by simp)
  cases h.table_inv trivial with
  | tableGrow hx =>
    rw [tables_of_frameView e] at hx
    exact hst.table? hx

end Silmaril.Wasm.SpecTec.Sim.Round4
