module

public import Silmaril.Proofs.Data.Cells.Store
public import Silmaril.Proofs.Data.Cells.Check
public import Silmaril.Proofs.Data.Cells.Perm

/-!
# Cells: theorems

The store rule (`Silmaril.Data.Cell.holds_storeAll`), the update rule (`Silmaril.Data.Frag.holds_update`, up to permutation `Frag.holds_update_perm`),
separation (`Frag.sep_cons`, `Frag.sep_append`, `Frag.Sep.apart`), and the soundness of the executable
separation check (`Frag.sep_of_sepB`).
-/
