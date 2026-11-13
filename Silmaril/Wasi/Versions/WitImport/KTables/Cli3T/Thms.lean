module

public import Silmaril.Wasi.Versions.WitImport.KImport.Defs
public import Silmaril.Wasi.Versions.WitImport.Tables.Defs
public import Silmaril.Wasi.Versions.WitImport.NetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.Http3Table.Defs

@[expose] public section

/-!
# Kernel-checked WIT signature table `cli3T`

Each theorem evaluates the importer (`kTable`/`kDrops`: the verified parser through the fuelled
lexer, `mergeDocs`, `Elab.elaborate`, `table`/`drops`) in the kernel on the glued texts of the
same files as the table's `wit_table%`/`wit_drops%`/`wit_iface_table%`, and compares the result
with the table. The glue that makes the texts (`withHeader`, `demoteParamDocs`, inside
`wit_src%`) still runs in Lean's evaluator.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- **`cli3T` is kernel-checked**: the importer, evaluated in the kernel, gives it. -/
theorem cli3T_kernel :
    kTable true false
      [wit_src% "../../../../../../specs/wasi/0.3.2/cli/environment.wit",
      wit_src% "../../../../../../specs/wasi/0.3.2/cli/exit.wit",
      wit_src% "../../../../../../specs/wasi/0.3.2/cli/run.wit",
      wit_src% "../../../../../../specs/wasi/0.3.2/cli/stdio.wit",
      wit_src% "../../../../../../specs/wasi/0.3.2/cli/terminal.wit"] = some cli3T := by
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
