module

public import Silmaril.Elf.Region.CFG.Function.Defs
public import Silmaril.Machine.Region.X86.CFG.Semantic.Thms

@[expose] public section
namespace Silmaril.Elf.Region.CFG
open Silmaril.X86.Decompile

/-- No skipped bytes or decoder-only truncation within the declared extent. -/
theorem FunctionRow.Valid.encoded_bytes {file : Silmaril.X86.Link.Blob} {f : FunctionRow}
    (h : f.Valid file) : (f.cfg.listing.map (fun d => Silmaril.X86.Ext.encode d.instr)).flatten =
      f.cfg.code.bytes := Region.decode?_covers h.cfg.2.1

theorem FunctionRow.Valid.encoded_size {file : Silmaril.X86.Link.Blob} {f : FunctionRow}
    (h : f.Valid file) :
    ((f.cfg.listing.map (fun d => Silmaril.X86.Ext.encode d.instr)).flatten).length = f.symbol.raw.size := by
  rw [h.encoded_bytes, h.size]

/-- Loading and interference are premises separate from symbol/byte evidence.
RET is not a hidden normal edge: this relation rejects RET-containing rows. -/
theorem FunctionRow.Valid.first_exit {file : Silmaril.X86.Link.Blob} {f : FunctionRow}
    (h : f.Valid file) {Ambient : Type*}
    (c : Silmaril.Machine.Region.X86.CFG.ExecutionContract f.cfg Ambient) {A : Ambient → Prop}
    (admit : ∀ s, A s → c.invariant s) :
    Silmaril.Semantics.Region.Sound c.interleaving A f.cfg.Support (fun l => l ∈ f.cfg.exits) :=
  Silmaril.Machine.Region.X86.CFG.interleaving_sound h.cfg.2 c admit

end Silmaril.Elf.Region.CFG
