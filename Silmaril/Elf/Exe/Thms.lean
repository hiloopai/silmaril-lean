module

public import Silmaril.Elf.Exe.Defs
public import Silmaril.Proofs.Elf.Exe.RoLoaded
public import Silmaril.Proofs.Elf.Exe.Task

/-! # Executables: theorems

(proofs in `Silmaril.Proofs.Elf.Exe.{RoLoaded,Task}`; standard axioms only)

* `roLoaded_of_exeLoaded`: **`ExeLoaded ⊑ RoLoaded`**. In memory where the loader relation holds
  for the executable `F` at base `b` (the head of the scope), the read-only segments of `F` are
  loaded at `b` (`ElfBind.RoLoaded`), when no loader write touches them (`NoTextRelD F lazy`)
  and `F` is placed at `b` (`ElfBind.Placement`). No `Task`.
* `noTextRelD_of_check`: the closed Boolean `noTextRel F lazy` decides it (one `decide +kernel`:
  1.1 s on a gcc `hello`, 2.8 s on GNU `sha256sum`).
* `roLoaded_task`: **`Task.roLoaded_of_exeLoaded`** (the API-level statement, under `NoTextRel A`
  and `NoLazyGotRo A`), from `Task.dynInfo_rd` and `Task.relas_rd`.
* `exists_of_parse`: a property of the parse, checked by one kernel run of the parse
  specification, as an existential over the parse (the form every API fact has).
* `slotsWith_pos`, `phdrsOf_of_finfo`, `roLoaded_of_imageOk`: the steps.
-/

@[expose] public section

namespace Silmaril.Elf.Exe

open Silmaril.X86.Link (Blob)

/-- **A property of the parse, by computation**: if the parse of `F` exists and satisfies the
decidable `p` (one `decide +kernel` on `(parse F).map (decide ∘ p) = some true`), some parse of `F`
satisfies `p`. -/
theorem exists_of_parse {F : Blob} {p : File → Prop} [DecidablePred p]
    (h : (parse F).map (fun A => decide (p A)) = some true) : ∃ A, Parses F A ∧ p A := by
  cases hA : parse F with
  | none => rw [hA] at h; cases h
  | some A =>
    rw [hA] at h
    exact ⟨A, hA, of_decide_eq_true (Option.some.inj h)⟩

end Silmaril.Elf.Exe
