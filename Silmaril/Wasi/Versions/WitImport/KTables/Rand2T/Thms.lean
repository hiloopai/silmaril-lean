module

public import Silmaril.Wasi.Versions.WitImport.KImport.Defs
public import Silmaril.Wasi.Versions.WitImport.Tables.Defs
public import Silmaril.Wasi.Versions.WitImport.NetTables.Defs
public import Silmaril.Wasi.Versions.WitImport.Http3Table.Defs

@[expose] public section

/-!
# Kernel-checked WIT signature table `rand2T`

Each theorem evaluates the importer (`kTable`/`kDrops`: the verified parser through the fuelled
lexer, `mergeDocs`, `Elab.elaborate`, `table`/`drops`) in the kernel on the glued texts of the
same files as the table's `wit_table%`/`wit_drops%`/`wit_iface_table%`, and compares the result
with the table. The glue that makes the texts (`withHeader`, `demoteParamDocs`, inside
`wit_src%`) still runs in Lean's evaluator.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.WitImport

set_option maxRecDepth 1000000

/-- **`rand2T` is kernel-checked**: the importer, evaluated in the kernel, gives it. -/
theorem rand2T_kernel :
    kTable false false
      [wit_src% "../../../../../../specs/wasi/0.2.12/random/insecure-seed.wit",
      wit_src% "../../../../../../specs/wasi/0.2.12/random/insecure.wit",
      wit_src% "../../../../../../specs/wasi/0.2.12/random/random.wit"] = some rand2T := by
  decide +kernel

end Silmaril.Wasi.Versions.WitImport
