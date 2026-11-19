module

public import Silmaril.Elf.Region.CFG.Defs
public import Silmaril.Elf.Staged.Decomp.Defs

/-! # Complete symbol-extent CFG certificates

This optional interpretation ties a region row to an entire nonzero-size ELF
function symbol. It does not change region validity or perform function
extraction. External direct transfers are outward edges; the target function
is outside this certificate. Calls and RET remain excluded by `Row.Valid`.
-/

@[expose] public section
namespace Silmaril.Elf.Region.CFG

structure FunctionRow where
  layout : Staged.Layout
  tableSection : Nat
  symbolIndex : Nat
  symbol : Silmaril.Formats.ELF.ObjectSymbol
  cfg : Silmaril.Machine.Region.X86.CFG.Row

/-- Completeness means every byte of this symbol's declared extent is decoded.
It is not a theorem that symbol metadata captures every execution belonging to
a source-level function, or that an outward tail transfer eventually returns. -/
structure FunctionRow.Valid (file : Silmaril.X86.Link.Blob) (f : FunctionRow) : Prop where
  layout : Staged.LayoutIs file f.layout
  symbol : Staged.Decomp.SymbolIs file f.layout f.tableSection f.symbolIndex f.symbol
  kind : f.symbol.kind = Staged.Decomp.STT_FUNC
  nonempty : 0 < f.symbol.raw.size
  base : f.cfg.code.base = f.symbol.raw.value
  size : f.cfg.code.bytes.length = f.symbol.raw.size
  entry : f.cfg.entry = f.symbol.raw.value
  extentSection : ∃ sh, f.layout.shs[f.symbol.raw.sectionIndex]? = some sh ∧
    Staged.Decomp.IsExec sh ∧ sh.address ≤ f.cfg.code.base ∧
    f.cfg.code.base + f.cfg.code.bytes.length ≤ sh.address + sh.size
  cfg : CFG.Valid file f.cfg

structure CertifiedFunction (file : Silmaril.X86.Link.Blob) where
  row : FunctionRow
  valid : row.Valid file

end Silmaril.Elf.Region.CFG
