module

public import Silmaril.Proofs.Wasm.LimeCompile.DataDrop.Emu
public import Silmaril.Proofs.Wasm.LimeCompile.DataDrop.Module
public import Silmaril.Wasm.Models.Lime1Core.Thms

/-!
# The container with `data.drop`: what is proved

An earlier step of the container track (docs/projects/wasm-wasi.md, "3.0 to Lime compiler"). The fragment
is Lime1 plus passive data, `memory.init` on memory 0 and `data.drop`. Each segment has a dropped
flag (a mutable `i32` global) and four functions: an earlier helper on the segment's bytes, an earlier
helper on no bytes, a dispatcher on the flag, and `$drop_y` (`Defs`).

Proved, with no `Task`, `sorry`, new axiom or native evaluation:

* **`wrap_emulation`**: one `memory.init 0 y` against a call of the dispatcher of `y`. If the
  source's data instance holds the full bytes exactly when the flag is clear, then in bounds both
  return and write the same memory, and out of bounds both trap on unchanged stores. The
  dispatcher reads the flag and calls one of the two helpers, whose run is an earlier
  `memoryInit_emulation` at the dispatcher's frame.
* **`drop_emulation`**: one `data.drop y` (the source's data instance becomes empty) against a
  call of `$drop_y` (the target's flag becomes `1`). Together with `wrap_emulation` this keeps the
  invariant "the source holds the full bytes iff the flag is clear".
* Static facts: `rwI_memoryInit`, `rwI_dataDrop`, `rwL_length` (call sites keep their length),
  `emuModule_funcs_length` (four functions per segment), and the export API is unchanged
  (`emuModule_api`; the flag globals are appended after all globals).
* Examples, by `decide +kernel`: `compile_exDrop` (an earlier `exDrop`, rejected there, now
  compiles) and `compile_exM`.
* `compileP_preserving`: the Lime-preserving variant is the identity on Lime1.

Open (frozen as `Task.exportEquiv`, as ): module-level export equivalence. Its store
relation is an earlier `PassiveEquiv.SRel` with one more component: the flag global of segment `y`
is `1` exactly when the source's data instance of `y` has been dropped.

New statements over the proofs in `Silmaril.Proofs.Wasm.LimeCompile.DataDrop`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.DataDrop

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (ExportEquiv)
open Silmaril.Wasm.LimeCompile.PassiveData (idx)
open Silmaril.Proofs.Wasm.LimeCompile.PassiveData (I32 MemOk HelperAt)
open Silmaril.Proofs.Wasm.LimeCompile.DataDrop (WrapAt DropAt)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## The emulation -/

/-- **`memory.init 0 y` against a call of the dispatcher of `y`.** -/
theorem wrap_emulation {y : DataIdx} {da ma aw a1 a0 ga hw full empty flag : Nat} {di : DataInst}
    {mi : MemInst} {bs : List UInt8} {s t : Store H} {f g : Frame} {i j n : BitVec 32}
    {gi : GlobalInst} {v : BitVec 32}
    (hm : s.mem? f (idx 0) = some (ma, mi)) (hmi : MemOk mi) (hd : s.data? f y = some (da, di))
    (hbs : bs.length ≤ 2 ^ 32) (hdi : di.bytes.data.toList = if v = 0 then bs else [])
    (htm : t.mems = s.mems) (hW : WrapAt t aw full empty flag a1 a0 ga)
    (hF : HelperAt t a1 full ma bs) (hE : HelperAt t a0 empty ma [])
    (hgi : t.globals[ga]? = some gi) (hv : gi.value = I32 v)
    (hg : g.module.funcs[(idx hw : FuncIdx).toNat]? = some aw) :
    (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size →
      ∃ s', Steps P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s', f, []⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n, .plain (.call (idx hw))]⟩
          ⟨{ t with mems := s'.mems }, g, []⟩) ∧
    (¬ (i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size) →
      Step P host ⟨s, f, [constI32 i, constI32 j, constI32 n, .plain (.memoryInit (idx 0) y)]⟩
          ⟨s, f, [.trap]⟩ ∧
        Steps P host ⟨t, g, [constI32 i, constI32 j, constI32 n, .plain (.call (idx hw))]⟩
          ⟨t, g, [.trap]⟩) :=
  Silmaril.Proofs.Wasm.LimeCompile.DataDrop.wrap_emulation hm hmi hd hbs hdi htm hW hF hE hgi hv hg

/-- **`data.drop y` against a call of `$drop_y`.** -/
theorem drop_emulation {y : DataIdx} {da ad ga hdrop flag : Nat} {di : DataInst} {s t : Store H}
    {f g : Frame} {gi : GlobalInst} (hd : s.data? f y = some (da, di))
    (hD : DropAt t ad flag ga) (hgi : t.globals[ga]? = some gi)
    (hg : g.module.funcs[(idx hdrop : FuncIdx).toNat]? = some ad) :
    Step P host ⟨s, f, [.plain (.dataDrop y)]⟩ ⟨s.setData da ByteArray.empty, f, []⟩ ∧
      Steps P host ⟨t, g, [.plain (.call (idx hdrop))]⟩ ⟨t.setGlobal ga (I32 1), g, []⟩ :=
  Silmaril.Proofs.Wasm.LimeCompile.DataDrop.drop_emulation hd hD hgi hg

/-! ## The compiled module -/

/-- `memory.init 0 y` calls the dispatcher of `y`. -/
theorem rwI_memoryInit (m : Module) (y : DataIdx) :
    rwI m (.memoryInit (idx 0) y) = .call (idx (wrapIdx m y.toNat)) :=
  Silmaril.Proofs.Wasm.LimeCompile.DataDrop.rwI_memoryInit m y

/-- `data.drop y` calls `$drop_y`. -/
theorem rwI_dataDrop (m : Module) (y : DataIdx) :
    rwI m (.dataDrop y) = .call (idx (dropIdx m y.toNat)) :=
  Silmaril.Proofs.Wasm.LimeCompile.DataDrop.rwI_dataDrop m y

/-- Call sites: the rewrite keeps the number of instructions of every sequence. -/
theorem rwL_length (m : Module) (l : List Instr) : (rwL m l).length = l.length :=
  Silmaril.Proofs.Wasm.LimeCompile.DataDrop.rwL_length m l

/-- Four functions per segment. -/
theorem emuModule_funcs_length (m : Module) :
    (emuModule m).funcs.length = m.funcs.length + 4 * m.data.length :=
  Silmaril.Proofs.Wasm.LimeCompile.DataDrop.emuModule_funcs_length m

/-- The export API is kept: exports, imports, tags, memories, tables, element segments and the
start function are those of the source, and the flags come after the source's globals. -/
theorem emuModule_api (m : Module) :
    (emuModule m).exports = m.exports ∧ (emuModule m).imports = m.imports ∧
      (emuModule m).tags = m.tags ∧ (emuModule m).memories = m.memories ∧
      (emuModule m).tables = m.tables ∧ (emuModule m).elems = m.elems ∧
      (emuModule m).start = m.start ∧
      (emuModule m).globals = m.globals ++ List.replicate m.data.length flagGlobal :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The dispatcher has 2 top-level instructions and 10 in all; `$drop_y` has 2. -/
theorem wrapBody_length (full empty flag : Nat) : (wrapBody full empty flag).length = 2 := rfl

theorem dropBody_length (flag : Nat) : (dropBody flag).length = 2 := rfl

/-! ## Examples -/

/-- an earlier `exDrop` (`memory.init` then `data.drop`) compiles. -/
theorem compile_exDrop : (compile PassiveData.exDrop).isSome = true := by decide +kernel

/-- an earlier `exM` compiles. -/
theorem compile_exM : (compile PassiveData.exM).isSome = true := by decide +kernel

/-! ## Lime-preserving variant -/

/-- **`compileP` is the identity on Lime-only code.** -/
theorem compileP_preserving : Preserve.LimePreserving compileP :=
  Preserve.limePres_preserving compile

/-! ## The open module-level target -/

/-- **Open (frozen):** module-level correctness of the container with `data.drop`, at the
closed host. -/
def Task.exportEquiv : Prop :=
  ∀ (H : Type) (P : Profile) (m : Module) (L : Lime1.Module),
    (∃ mt, ModuleOk m mt) → (∃ mt, ModuleOk L.toCore mt) → compile m = some L →
    ExportEquiv (· = ·) P (fun _ _ _ _ => False : HostSemantics H)
      ((Silmaril.Wasm.Models.Lime1Core.lime1Emb H).mod L) m

/-! ## Axiom audit -/

/-- info: 'Silmaril.Wasm.LimeCompile.DataDrop.wrap_emulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrap_emulation

/-- info: 'Silmaril.Wasm.LimeCompile.DataDrop.drop_emulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms drop_emulation

end Silmaril.Wasm.LimeCompile.DataDrop
