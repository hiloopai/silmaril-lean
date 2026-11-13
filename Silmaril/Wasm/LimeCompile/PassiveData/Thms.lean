module

public import Silmaril.Proofs.Wasm.LimeCompile.PassiveData.Emu
public import Silmaril.Proofs.Wasm.LimeCompile.PassiveData.Module
public import Silmaril.Wasm.Models.Lime1Core.Thms
public import Silmaril.Wasm.Binaryen.Equiv

/-!
# The passive-data container: what is proved

An earlier step of the container track (docs/projects/wasm-wasi.md, "3.0 to Lime compiler"). The fragment
is Lime1 plus passive data segments and `memory.init` on memory 0. `compile` emits a Lime1
module with one helper function per data segment (`Defs`).

Proved:

* **`memoryInit_emulation`**, the emulation theorem. It is a non-lockstep simulation of one
  `memory.init 0 y` by a call to its helper. Take a source store `s` and a target store `t` with
  the same memories, where `t` holds the helper of `y` (`HelperAt`), and memory 0 is a valid
  32-bit memory (`MemOk`). Then:
  - if the bounds hold, the source's `memory.init` returns with store `s'`
    (`memoryInitLoop`, in `1 + 2n` Core steps), and the call returns with the memories of `s'`
    and every other part of `t` unchanged;
  - if the bounds fail, the source traps in one step on an unchanged store, and so does the
    call.
  In both cases the memories written are equal. The call is many Core steps for each source
  step: a frame, labels, the bounds check, a `select` chain per byte and a recursive call.
* static facts about the output: `compile_toCore` (the output's Core image is `emuModule m`),
  the kept sections (`emuModule_exports` and the others), the helper of segment `y` sits at
  index `helperBase m + y` (`helpers_getElem?`), `memory.init 0 y` becomes a call to it
  (`rwI_memoryInit`), and sizes (`rwL_length`, `helperBody_length`, `stepCode_length`);
* `compileP_preserving`: the Lime-preserving variant returns every Lime1 module unchanged.

Open (frozen as `Task.exportEquiv`, results that use it are conditional): **module-level
export equivalence** of `m` and the Core image of `compile m` under `lime1Emb`, at the closed
host. The emulation theorem is its local step. What is missing is lifting it to whole
configurations. silmaril-lean's code simulation (`Sim.BaseSim`,
`exportRefines_of_bodiesRel`) relates stores that differ only in function code, while this
container also changes the data instances (passive bytes against empty placeholders) and the
number of functions (the helpers). A store relation for that, and the closure of the simulation
under it, are not done.

New statements over the proofs in `Silmaril.Proofs.Wasm.LimeCompile.PassiveData`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.PassiveData

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (ExportEquiv)
open Silmaril.Proofs.Wasm.LimeCompile.PassiveData (I32 MemOk HelperAt)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## The emulation of `memory.init` -/

/-- **The emulation theorem.** One source `memory.init 0 y` on `i`, `j`, `n` and one call of the
helper of `y` on the same arguments end in the same way and write the same memory. -/
theorem memoryInit_emulation {y : DataIdx} {da ma a h : Nat} {di : DataInst} {mi : MemInst}
    {bs : List UInt8} {s t : Store H} {f g : Frame} {i j n : BitVec 32}
    (hm : s.mem? f (idx 0) = some (ma, mi)) (hmi : MemOk mi) (hd : s.data? f y = some (da, di))
    (hdi : di.bytes.data.toList = bs) (hbs : bs.length ≤ 2 ^ 32) (htm : t.mems = s.mems)
    (hH : HelperAt t a h ma bs) (hg : g.module.funcs[(idx h : FuncIdx).toNat]? = some a) :
    (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size →
      ∃ s', Steps P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s', f, []⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n, .plain (.call (idx h))]⟩
          ⟨{ t with mems := s'.mems }, g, []⟩) ∧
    (¬ (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size) →
      Step P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s, f, [.trap]⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n, .plain (.call (idx h))]⟩
          ⟨t, g, [.trap]⟩) := by
  have hsm : s.mems[ma]? = some mi ∧ f.module.mems[(idx 0 : MemIdx).toNat]? = some ma :=
    ⟨(Silmaril.Proofs.Wasm.LimeCompile.PassiveData.mem?_inv hm).2,
      (Silmaril.Proofs.Wasm.LimeCompile.PassiveData.mem?_inv hm).1⟩
  refine ⟨fun hb => ?_, fun hb => ⟨Step.memory (.initOob (a := .i32) hm hd ?_), ?_⟩⟩
  · obtain ⟨s', hs'⟩ := Silmaril.Proofs.Wasm.LimeCompile.PassiveData.memoryInitLoop_some
      (H := H) n hm hd hb.1 hb.2
    refine ⟨s', memoryInitLoop_steps n hs', ?_⟩
    have := Silmaril.Proofs.Wasm.LimeCompile.PassiveData.emu_ok (P := P) (host := host) hbs hdi n
      hs' hd hsm.2 (fun mi' h' => by rw [hsm.1] at h'; cases h'; exact hmi) htm hH hg
    simpa [vals, constI32, Val.i32] using this
  · show mi.bytes.size < i.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat
    omega
  · have := Silmaril.Proofs.Wasm.LimeCompile.PassiveData.emu_trap (P := P) (host := host)
      (i := i) (j := j) (n := n) hbs hdi hm hmi hb htm hH hg
    simpa [vals, constI32, Val.i32] using this

/-! ## The compiled module -/

/-- The output's Core image is the emulated module. -/
theorem compile_toCore {m : Module} {L : Lime1.Module} (h : compile m = some L) :
    L.toCore = emuModule m :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveData.compile_toCore h

/-- The export API is kept: exports, imports, tags, globals, memories, tables, element segments
and the start function are those of the source. -/
theorem emuModule_api (m : Module) :
    (emuModule m).exports = m.exports ∧ (emuModule m).imports = m.imports ∧
      (emuModule m).tags = m.tags ∧ (emuModule m).globals = m.globals ∧
      (emuModule m).memories = m.memories ∧ (emuModule m).tables = m.tables ∧
      (emuModule m).elems = m.elems ∧ (emuModule m).start = m.start :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The types are extended by the helper type at the end; existing type indices are kept. -/
theorem emuModule_types (m : Module) :
    (emuModule m).types = m.types ++ [helperType.toCoreRec] := rfl

/-- The functions are the rewritten source functions (same types and locals), then the helpers. -/
theorem emuModule_funcs (m : Module) :
    (emuModule m).funcs = m.funcs.map (rwFunc (helperBase m)) ++ helpers m := rfl

/-- A data segment is kept if active and becomes an empty active segment if passive, so the
data index space has the same length. -/
theorem emuModule_data (m : Module) : (emuModule m).data = m.data.map emuData := rfl

/-- The helper of data segment `y` (at function index `helperBase m + y`). -/
theorem helpers_getElem? (m : Module) (y : Nat) :
    (helpers m)[y]? = (m.data[y]?).map (helperFunc m y) :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveData.helpers_getElem? m y

/-- `memory.init 0 y` becomes a call to the helper of `y`. -/
theorem rwI_memoryInit (base : Nat) (y : DataIdx) :
    rwI base (.memoryInit (idx 0) y) = .call (idx (base + y.toNat)) :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveData.rwI_memoryInit base y

/-! ## Size data -/

/-- Call sites: the rewrite keeps the number of instructions of every sequence. -/
theorem rwL_length (base : Nat) (l : List Instr) : (rwL base l).length = l.length :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveData.rwL_length base l

/-- A helper body has 21 top-level instructions (the bounds check and the copy `if`). -/
theorem helperBody_length (bs : List UInt8) (h : Nat) : (helperBody bs h).length = 21 := rfl

/-- The per-byte block has `5 · |b| + 13` instructions: the `select` chain is linear in the
segment. -/
theorem stepCode_length (bs : List UInt8) (h : Nat) :
    (stepCode bs h).length = 5 * bs.length + 13 :=
  Silmaril.Proofs.Wasm.LimeCompile.PassiveData.stepCode_length bs h

/-- One helper per data segment. -/
theorem emuModule_funcs_length (m : Module) :
    (emuModule m).funcs.length = m.funcs.length + m.data.length := by
  simp [emuModule_funcs, Silmaril.Proofs.Wasm.LimeCompile.PassiveData.helpers_length]

/-! ## Examples -/

/-- `exM` (a passive segment and `memory.init`) compiles to a Lime1 module. -/
theorem compile_exM : (compile exM).isSome = true := by decide +kernel

/-- `exDrop` (with `data.drop`) is rejected: the dropped flag is not emulated. -/
theorem compile_exDrop : compile exDrop = none := by decide +kernel

/-- The source `exM` is not Lime-only, so `compileP` runs the container on it. -/
theorem compileP_exM : compileP exM = compile exM :=
  Preserve.limePres_of_nonLime compile (Preserve.limeView_eq_none_iff.mp (by decide +kernel))

/-! ## Lime-preserving variant -/

/-- **`compileP` is the identity on Lime-only code.** -/
theorem compileP_preserving : Preserve.LimePreserving compileP :=
  Preserve.limePres_preserving compile

/-! ## The open module-level target -/

/-- **Open (frozen):** module-level correctness. A valid source and a valid output of `compile`
are exactly export-equivalent under `lime1Emb`, at every profile, for the closed host. -/
def Task.exportEquiv : Prop :=
  ∀ (H : Type) (P : Profile) (m : Module) (L : Lime1.Module),
    (∃ mt, ModuleOk m mt) → (∃ mt, ModuleOk L.toCore mt) → compile m = some L →
    ExportEquiv (· = ·) P (fun _ _ _ _ => False : HostSemantics H)
      ((Silmaril.Wasm.Models.Lime1Core.lime1Emb H).mod L) m

/-- Correctness, conditional on `Task.exportEquiv`. -/
theorem compile_correct_of_task (hT : Task.exportEquiv) {m : Module} {L : Lime1.Module}
    (hm : ∃ mt, ModuleOk m mt) (hL : ∃ mt, ModuleOk L.toCore mt) (h : compile m = some L) :
    ExportEquiv (· = ·) P (fun _ _ _ _ => False : HostSemantics H)
      ((Silmaril.Wasm.Models.Lime1Core.lime1Emb H).mod L) m :=
  hT H P m L hm hL h

/-! ## Axiom audit -/

/-- info: 'Silmaril.Wasm.LimeCompile.PassiveData.memoryInit_emulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms memoryInit_emulation

end Silmaril.Wasm.LimeCompile.PassiveData
