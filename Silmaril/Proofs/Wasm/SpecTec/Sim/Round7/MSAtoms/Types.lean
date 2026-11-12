module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSAtoms.Basic

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge: types and runtime values

Every encoder of a type, an index, a runtime value or a runtime instance record that `configV`
uses produces a value without a `case` of an atom of `HStep.hAtoms` (`VLOAD`, `VLOAD_LANE`,
`VSTORE`, `VSTORE_LANE`, `CALL_REF`). The `Encode` instances built by `Encode.ofCase` unfold to
a `case` of their view; `tyV` is one structural induction over the `Ty` family.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.Execution.Core
open VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)
open HStep (hAtoms)

/-! ## Leaves -/

theorem nh_nat (n : Nat) : NH (Encode.toValue n) := trivial

theorem nh_percent {v : Value} (h : NH v) : NH (percentV v) := by
  simp only [percentV, caseV]; nh_close

theorem nh_pctNat (n : Nat) : NH (percentV (.num (.natN n))) := nh_percent trivial

theorem nh_idx {k : Silmaril.Wasm.IndexKind} (x : Silmaril.Wasm.Idx k) :
    NH (Encode.toValue x) := by
  show NH (percentV (.num (.natN x.toNat)))
  exact nh_pctNat _

theorem nh_fin64 (x : Fin (2 ^ 64)) : NH (Encode.toValue x) := by
  show NH (percentV (.num (.natN x.val)))
  exact nh_pctNat _

theorem nh_optFin64 (x : Option (Fin (2 ^ 64))) : NH (Encode.toValue x) := by
  cases x with
  | none => trivial
  | some y => exact nh_fin64 y

theorem nh_numType (t : Silmaril.Wasm.NumType) : NH (Encode.toValue t) := by
  rcases t with t | t <;> cases t <;> simp [NoAtoms, NoAtomsL, Encode.toValue, mem_hAtoms]

theorem nh_vecType (t : Silmaril.Wasm.VecType) : NH (Encode.toValue t) := by
  cases t; simp [NoAtoms, NoAtomsL, Encode.toValue, mem_hAtoms]

theorem nh_absHeapType (t : Silmaril.Wasm.AbsHeapType) : NH (Encode.toValue t) := by
  cases t <;> simp [NoAtoms, NoAtomsL, Encode.toValue, mem_hAtoms]

theorem nh_packType (t : Silmaril.Wasm.PackType) : NH (Encode.toValue t) := by
  cases t <;> simp [NoAtoms, NoAtomsL, Encode.toValue, mem_hAtoms]

theorem nh_addrType (t : Silmaril.Wasm.AddrType) : NH (Encode.toValue t) := by
  cases t <;> simp [NoAtoms, NoAtomsL, Encode.toValue, mem_hAtoms]

theorem nh_mut (t : Silmaril.Wasm.Mutability) : NH (Encode.toValue t) := by
  cases t <;> simp [NoAtoms, NoAtomsL, Encode.toValue, mutToValue, mem_hAtoms]

theorem nh_limits (l : Silmaril.Wasm.Limits) : NH (Encode.toValue l) := by
  have h₁ := nh_fin64 l.min
  have h₂ := nh_optFin64 l.max
  show NH (.case "[%..%]" (.tuple [Encode.toValue l.min, Encode.toValue l.max]))
  nh_close

theorem nh_memType (m : Silmaril.Wasm.MemoryType) : NH (Encode.toValue m) := by
  have h₁ := nh_addrType m.address
  have h₂ := nh_limits m.limits
  show NH (.case "%%PAGE" (.tuple [Encode.toValue m.address, Encode.toValue m.limits]))
  nh_close

theorem nh_heapType (t : Silmaril.Wasm.HeapType) : NH (Encode.toValue t) := by
  rcases t with a | x
  · cases a <;> simp [NoAtoms, NoAtomsL, Encode.toValue, heapTypeView, mem_hAtoms]
  · have hx := nh_idx x
    show NH (.case "_IDX" (Encode.toValue x))
    nh_close

theorem nh_refType (r : Silmaril.Wasm.RefType) : NH (Encode.toValue r) := by
  have hh := nh_heapType r.heap
  show NH (.case "REF" (.tuple [nullToValue r.nullable, Encode.toValue r.heap]))
  cases r.nullable <;> simp only [nullToValue] <;> nh_close

theorem nh_valType (t : Silmaril.Wasm.ValType) : NH (Encode.toValue t) := by
  rcases t with t | t | t
  · exact nh_numType t
  · exact nh_vecType t
  · exact nh_refType t

theorem nh_blockType (b : Silmaril.Wasm.BlockType) : NH (Encode.toValue b) := by
  rcases b with _ | t | x
  · show NH (.case "_RESULT" (.opt none))
    nh_close
  · have ht := nh_valType t
    show NH (.case "_RESULT" (.opt (some (Encode.toValue t))))
    nh_close
  · have hx := nh_idx x
    show NH (.case "_IDX" (Encode.toValue x))
    nh_close

theorem nh_catch (c : Silmaril.Wasm.Catch) : NH (Encode.toValue c) := by
  rcases c with ⟨x, l⟩ | ⟨x, l⟩ | l | l
  · have hx := nh_idx x
    have hl := nh_idx l
    show NH (.case "CATCH" (.tuple [Encode.toValue x, Encode.toValue l]))
    nh_close
  · have hx := nh_idx x
    have hl := nh_idx l
    show NH (.case "CATCH_REF" (.tuple [Encode.toValue x, Encode.toValue l]))
    nh_close
  · have hl := nh_idx l
    show NH (.case "CATCH_ALL" (Encode.toValue l))
    nh_close
  · have hl := nh_idx l
    show NH (.case "CATCH_ALL_REF" (Encode.toValue l))
    nh_close

/-! ## The semantic types (`tyV`) -/

open Silmaril.Wasm.Validation (TKind Ty) in
/-- **`tyV` has no atom of `hAtoms`**, at every sort. -/
theorem nh_tyV : ∀ {k : TKind} (t : Ty k), NH (Validation.tyV t)
  | _, .nil => by simp [NH, Validation.tyV, NoAtoms, NoAtomsL]
  | _, .cons a l => by
      have ha := nh_tyV a
      have hl := nh_tyV l
      simp only [Validation.tyV, Validation.consV]
      split
      · rename_i vs hvs
        rw [hvs] at hl
        exact ⟨ha, hl⟩
      · exact ⟨ha, trivial⟩
  | _, .idx x => by simp [NH, Validation.tyV, Validation.idxV, Validation.natV, percentV, caseV,
      NoAtoms, NoAtomsL, hAtoms]
  | _, .recv i => by simp [NH, Validation.tyV, Validation.natV, NoAtoms, hAtoms]
  | _, .dt d => nh_tyV d
  | _, .defn g i => by
      have hg := nh_tyV g
      simp only [NH] at hg
      simp [NH, Validation.tyV, Validation.natV, NoAtoms, NoAtomsL, hAtoms]
      exact hg
  | _, .abs a => by cases a <;> simp [NH, Validation.tyV, Validation.absV, NoAtoms, hAtoms, NoAtomsL]
  | _, .bot => by simp [NH, Validation.tyV, NoAtoms, hAtoms, NoAtomsL]
  | _, .use u => nh_tyV u
  | _, .ref n h => by
      have hh := nh_tyV h
      simp only [NH] at hh
      cases n <;> simp [NH, Validation.tyV, Validation.nullV, NoAtoms, NoAtomsL, hAtoms] <;>
        exact hh
  | _, .num t => by
      rcases t with t | t <;> cases t <;>
        simp [NH, Validation.tyV, Validation.numtypeV, NoAtoms, hAtoms, NoAtomsL]
  | _, .vec t => by cases t; simp [NH, Validation.tyV, Validation.vectypeV, NoAtoms, hAtoms, NoAtomsL]
  | _, .refv r => nh_tyV r
  | _, .botv => by simp [NH, Validation.tyV, NoAtoms, hAtoms, NoAtomsL]
  | _, .val t => nh_tyV t
  | _, .pack p => by cases p <;> simp [NH, Validation.tyV, Validation.packtypeV, NoAtoms, hAtoms,
      NoAtomsL]
  | _, .field m s => by
      have hs := nh_tyV s
      simp only [NH] at hs
      cases m <;> simp [NH, Validation.tyV, Validation.mutV, NoAtoms, NoAtomsL, hAtoms] <;>
        exact hs
  | _, .struct fs => by
      have hs := nh_tyV fs
      simp only [NH] at hs
      simp [NH, Validation.tyV, percentV, caseV, NoAtoms, NoAtomsL, hAtoms]
      exact hs
  | _, .array f => by
      have hs := nh_tyV f
      simp only [NH] at hs
      simp [NH, Validation.tyV, NoAtoms, hAtoms]
      exact hs
  | _, .func ps rs => by
      have h₁ := nh_tyV ps
      have h₂ := nh_tyV rs
      simp only [NH] at h₁ h₂
      simp [NH, Validation.tyV, percentV, caseV, NoAtoms, NoAtomsL, hAtoms]
      exact ⟨h₁, h₂⟩
  | _, .sub fin sups ct => by
      have h₁ := nh_tyV sups
      have h₂ := nh_tyV ct
      simp only [NH] at h₁ h₂
      cases fin <;> simp [NH, Validation.tyV, Validation.finalV, NoAtoms, NoAtomsL, hAtoms] <;>
        exact ⟨h₁, h₂⟩
  | _, .group subs => by
      have hs := nh_tyV subs
      simp only [NH] at hs
      simp [NH, Validation.tyV, percentV, caseV, NoAtoms, NoAtomsL, hAtoms]
      exact hs

theorem nh_defType (d : Silmaril.Wasm.Validation.DefType) : NH (closedTypes.defType d) :=
  nh_tyV d

theorem nh_elemType (r : Silmaril.Wasm.Validation.CRefType) : NH (closedTypes.elemType r) :=
  nh_tyV r

theorem nh_globalType (g : Silmaril.Wasm.Validation.CGlobalType) :
    NH (closedTypes.globalType g) := by
  have h₁ := nh_mut g.mutability
  have h₂ := nh_tyV g.type
  show NH (.case "%%" (.tuple [Encode.toValue g.mutability, Validation.tyV g.type]))
  nh_close

theorem nh_tableType (t : Silmaril.Wasm.Validation.CTableType) :
    NH (closedTypes.tableType t) := by
  have h₁ := nh_addrType t.address
  have h₂ := nh_limits t.limits
  have h₃ := nh_tyV t.element
  show NH (.case "%%%" (.tuple [Encode.toValue t.address, Encode.toValue t.limits,
    Validation.tyV t.element]))
  nh_close

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
