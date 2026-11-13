module

public import Silmaril.Wasm.Unified.Versions.Binary.Defs
public import Silmaril.Wasm.Unified.Versions.Thms
public import Silmaril.Wasm.Unified.Versions.Sig.Defs

/-!
# Binary opcodes renamed to the named 3.0 opcodes: naturality and the reduct equation

* `plain_decodes`, `fb_decodes`, `fc_decodes`, `fd_decodes`: every immediate-free instruction of
  silmaril's binary opcode tables decodes to itself (`binInstr?` agrees with the tables);
* `bsigB_sub`: inclusions of feature sets are inclusions of binary signatures;
* **`renB_natural`**: the renaming is natural in the feature set: renaming after the binary
  inclusion is the named inclusion after renaming. So the binary and the named presentations of
  the version lattice are related by one renaming per version, compatibly with every inclusion;
* **`binAt_reduct`**: the reduct equation: the binary model at the image point of `coreEmb`,
  reducted to the smaller binary signature, is the binary model at the point; `binAt_v30`:
  the binary 3.0 model is the reduct of the Core 3.0 model `at30` along `ren30`;
  `bin_sat_iff`: a sentence over binary opcodes holds in the binary model iff its renaming holds
  in Core 3.0 (the satisfaction condition along `ren30`);
* `ren_tableGrow`, `tableGrow_bsep`: `table.grow` (`0xFC 0x0F`) renames to the named
  `table.grow` and separates the binary 2.0 signature from 1.0;
* `ren_select`: the renaming is not injective (`0x1B` and `0x1C` are both `select`);
* `vsig_no_decode`: **no morphism from the capability-level `vsig v30` to `sig30` sends
  `v128.load` (`0xFD 0x00`) to a `vecLoad` opcode** (typing is not preserved), while `ren30`
  does (`ren30_v128load`). This is why the renaming starts at `bsigB`, not at `vsig`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models
open Silmaril.Wasm.Unified.Core30 Silmaril.Wasm.Atlas
open Silmaril.Wasm.Numerics (Profile)

/-! ## The decoding agrees with silmaril's opcode tables -/

theorem plain_decodes {b : UInt8} {i : Instr} (h : Binary.Core.PlainOp b i) :
    binInstr? (.bin none b.toNat) = some i := by
  simp [binInstr?, plainB?, b.toNat_lt, h.lookup]

theorem fb_decodes {n : Nat} {i : Instr} (h : Binary.Core.PrefixFBOp n i) :
    binInstr? (.bin (some 0xFB) n) = some i := by
  simp [binInstr?, h.lookup]

theorem fc_decodes {n : Nat} {i : Instr} (h : Binary.Core.PrefixFCOp n i) :
    binInstr? (.bin (some 0xFC) n) = some i := by
  simp [binInstr?, h.lookup]

theorem fd_decodes {n : Nat} {i : Instr} (h : Binary.Core.PrefixFDOp n i) :
    binInstr? (.bin (some 0xFD) n) = some i := by
  simp [binInstr?, vecB?, h.lookup]

/-! ## Naturality and the reduct equation -/

/-- Inclusions of feature sets are inclusions of binary signatures. -/
theorem bsigB_sub {S T : FeatureSet} (h : S ≤ T) : FSig.Sub (bsigB S) (bsigB T) :=
  ⟨fun _ ⟨i, hi, hs⟩ => ⟨i, hi, headB_mono h i hs⟩, fun _ _ => rfl⟩

/-- **The renaming is natural** in the feature set. -/
theorem renB_natural {S T : FeatureSet} (h : S ≤ T) :
    FSig.incl (bsigB_sub h) ≫ renB T = renB S ≫ FSig.incl (nsig_sub h) :=
  FSig.hom_ext (funext fun _ => rfl)

variable {H : Type} (f : Frame) (okc : List Instr → Prop)

/-- **The reduct equation** along `coreEmb`, on binary opcodes. -/
theorem binAt_reduct (P : Profile) {S T : FeatureSet} (h : S ≤ T) (x : Core.Pt H) :
    (binAt T P f okc ((coreEmb P H h).pt x)).reduct (FSig.incl (bsigB_sub h)) =
      binAt S P f okc x := by
  unfold binAt
  rw [← Model.reduct_comp, renB_natural h, Model.reduct_comp, coreEmb_reduct]

/-- The binary 3.0 model is the reduct of Core 3.0 along `ren30`. -/
theorem binAt_v30 (P : Profile) (x : Core.Pt H) :
    binAt v30 P f okc x = (at30 P f okc x).reduct ren30 := rfl

/-- **Transfer along the renaming**: the satisfaction condition along `ren30`. -/
theorem bin_sat_iff (P : Profile) (x : Core.Pt H) (φ : Sen UIn UObs (bsigB v30)) :
    Sat (at30 P f okc x) (φ.map ren30) ↔ Sat (binAt v30 P f okc x) φ := by
  rw [sat_map_iff, binAt_v30]

/-! ## Examples -/

theorem opTableGrow_mem : opTableGrow ∈ (bsigB v20).ops := ⟨.tableGrow i0, rfl, by decide⟩

/-- `table.grow` renames to the named `table.grow`. -/
theorem ren_tableGrow : ((renB v20).f ⟨opTableGrow, opTableGrow_mem⟩).1 = nTableGrow := rfl

/-- **`table.grow` separates the binary 2.0 signature from 1.0.** -/
theorem tableGrow_bsep : opTableGrow ∈ (bsigB v20).ops ∧ opTableGrow ∉ (bsigB v10).ops := by
  refine ⟨opTableGrow_mem, ?_⟩
  rintro ⟨i, hi, hs⟩
  have hi' : i = .tableGrow i0 := (Option.some.inj hi).symm
  subst hi'
  exact absurd hs (by decide)

theorem select_mem : Opcode.bin none 0x1B ∈ (bsigB v30).ops := ⟨.select none, rfl, by decide⟩

theorem selectT_mem : Opcode.bin none 0x1C ∈ (bsigB v30).ops := ⟨.select (some []), rfl, by decide⟩

/-- **The renaming is not injective**: `select` and `select t` are one named opcode. -/
theorem ren_select : ren30.f ⟨_, select_mem⟩ = ren30.f ⟨_, selectT_mem⟩ ∧
    (⟨_, select_mem⟩ : (bsigB v30).Op) ≠ ⟨_, selectT_mem⟩ := by
  refine ⟨rfl, fun h => ?_⟩
  have := congrArg Subtype.val h
  simp at this

/-- `v128.load`. -/
def opV128Load : Opcode := .bin (some 0xFD) 0

theorem v128load_mem : opV128Load ∈ (bsigB v30).ops :=
  ⟨.vecLoad .full i0 ma0, rfl, by decide⟩

theorem v128load_vsig : opV128Load ∈ (vsig v30).ops := by
  show inB v30 opV128Load = true
  decide

/-- `ren30` sends `v128.load` to the named `vecLoad` opcode. -/
theorem ren30_v128load :
    (ren30.f ⟨opV128Load, v128load_mem⟩).1 = head (.vecLoad .full i0 ma0) := rfl

/-- **No renaming from the capability-level `vsig v30` decodes `v128.load`**: a morphism into
`sig30` preserves typing, and `vsig` gives `v128.load` no immediates while every `vecLoad`
opcode has two. -/
theorem vsig_no_decode (σ : vsig v30 ⟶ sig30) (op : VecLoadOp) (m : MemIdx) (a : MemArg) :
    (σ.f ⟨opV128Load, v128load_vsig⟩).1 ≠ head (.vecLoad op m a) := by
  intro heq
  have hty : arity30 (σ.f ⟨opV128Load, v128load_vsig⟩).1 = tyU opV128Load :=
    σ.ty ⟨opV128Load, v128load_vsig⟩
  rw [heq] at hty
  have h₁ : arity30 (head (.vecLoad op m a)) = ⟨2, 0, false⟩ := rfl
  have h₂ : tyU opV128Load = ⟨0, 0, false⟩ := rfl
  rw [h₁, h₂] at hty
  exact absurd (congrArg OpTy.imms hty) (by decide)
