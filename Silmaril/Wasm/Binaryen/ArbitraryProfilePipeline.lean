module

public import Silmaril.Wasm.Binaryen.ArbitraryProfileExtended
public import Silmaril.Wasm.Binaryen.AddChainAny
public import Silmaril.Wasm.Binaryen.ConstBranchAny
public import Silmaril.Wasm.Binaryen.IfSwapAny

@[expose] public section

/-! # Eight-pass cleanup at every numerical profile

`extendedCleanup` runs the separate five-pass cleanup followed by checked
addition-chain folding, constant-branch folding, and conditional arm swapping.
The shared pass monoid retains validity and exact equivalence for the same
arbitrary profile under the closed host. All checked guards remain active.

This is a separately named module-level pipeline. The existing four/five-pass
functions and the default executable/byte-level theorem remain unchanged.
-/

namespace Silmaril.Wasm.Binaryen.ArbitraryProfile

open Execution.Core Numerics

variable {H : Type}

/-- The actual checked addition-chain executable, retaining all its guards. -/
def addChainCheckedP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := AddChain.addChainChecked
  inv_run hm := (AddChain.addChainChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (AddChain.addChainChecked_sound_any hm).2

/-- The actual checked constant-condition executable, retaining its export/validator guards. -/
def constBranchCheckedP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := ConstBranch.constBranchChecked
  inv_run hm := (ConstBranch.constBranchChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (ConstBranch.constBranchChecked_sound_any hm).2

/-- The actual checked conditional arm swap, retaining its validator fallback. -/
def ifSwapCheckedP (P : Profile) : EquivPass P (closedHost (H := H)) where
  run := IfSwap.ifSwapChecked
  inv_run hm := (IfSwap.ifSwapChecked_sound_any (P := P) (H := H) hm).1
  sound hm := (IfSwap.ifSwapChecked_sound_any hm).2

/-- Eight passes: checked DCE, anchored vacuum, anchored integer precompute,
tee/drop, RUME, checked AddChain, checked ConstBranch, checked IfSwap. -/
def extendedCleanupP (P : Profile) : EquivPass P (closedHost (H := H)) :=
  cleanupWithTeeP P * addChainCheckedP P * constBranchCheckedP P * ifSwapCheckedP P

/-- The separate eight-pass executable function, with every checked guard retained. -/
def extendedCleanup (m : BModule) : BModule :=
  IfSwap.ifSwapChecked (ConstBranch.constBranchChecked
    (AddChain.addChainChecked (cleanupWithTee m)))

@[simp] theorem extendedCleanupP_run (P : Profile) :
    (extendedCleanupP (H := H) P).run = extendedCleanup := rfl

/-- Valid inputs yield valid outputs and exact export equivalence at the same
arbitrary numerical profile under the closed host. -/
theorem extendedCleanup_sound (P : Profile) {m : BModule} (hm : m.Ok) :
    (extendedCleanup m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (extendedCleanup m).lower m.lower :=
  ⟨(extendedCleanupP (H := H) P).inv_run hm, (extendedCleanupP (H := H) P).sound hm⟩

/-- Any finite number of eight-pass rounds retains the exact same profile and host. -/
theorem extendedCleanup_iterate_sound (P : Profile) (rounds : Nat) {m : BModule} (hm : m.Ok) :
    (extendedCleanup^[rounds] m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H)) (extendedCleanup^[rounds] m).lower m.lower := by
  have hrun := Silmaril.Compile.PassAPI.Pass.pow_run (extendedCleanupP (H := H) P) rounds
  rw [extendedCleanupP_run] at hrun
  have result : ((extendedCleanupP (H := H) P ^ rounds).run m).Ok ∧
      ExportEquiv (· = ·) P (closedHost (H := H))
        ((extendedCleanupP (H := H) P ^ rounds).run m).lower m.lower :=
    ⟨(extendedCleanupP (H := H) P ^ rounds).inv_run hm,
      (extendedCleanupP (H := H) P ^ rounds).sound hm⟩
  rw [hrun] at result
  exact result

end Silmaril.Wasm.Binaryen.ArbitraryProfile
