module

public import Silmaril.X86.Features.Ext.SseMerged.Codec
public import Silmaril.X86.Features.Ext.Sse2.Extension
public import Silmaril.X86.Features.Ext.SsePacked.Extension
public import Silmaril.X86.Features.Restrict

/-!
# The reconciled SSE/SSE2 profile

`Sse2` is canonical where the two lanes overlap (`Codec.lean`); `SsePacked`
contributes the rest. `ssePackedRest` is `SsePacked.ext` restricted to the
instructions `Sse2` does not decode (`shadowed`), and

`sseExts = [floatExt, sse2Ext, ssePackedRest]`

is the profile of the legacy-encoded scalar and packed SSE/SSE2 instructions.

## Restriction of an extension

`Extension.restrict` (from `Restrict.lean`) keeps the instructions satisfying
a Boolean predicate. A restriction embeds into the original (`Extension.restrict_embeds`), and
disjointness passes to restrictions (`Extension.Disjoint.restrict_left`,
`restrict_right`).

## Lattice facts

* `sse2Ext_disjoint_ssePackedRest`: by codec agreement (`decode_agree`) and
  `shadowed_iff`, `Sse2` and the restricted `SsePacked` never decode the same
  bytes, so `sseExts` is pairwise disjoint (`sseExts_pairwiseDisjoint`).
* `included_sse2`, `included_float`, `included_ssePackedRest`: each of the
  lanes' own profiles is `Included` in `sseExts`, and
  `ssePackedRest_embeds`: the residual lane embeds into `SsePacked.ext`.
* `run_sse2_conservative` (and the other `run_*_conservative`): a run proved
  with `[floatExt, sse2Ext]` (the canonical lane's profile) whose states all
  decode is the same run with `sseExts`. With `FeatureFree.same_behaviour`,
  everything proved with the weaker decoder or feature set holds with the
  stronger one.
* `requires_toPacked`: both lanes require the same CPUID features on the
  overlap. `exec_toPacked_*`: on the register forms of the bitwise
  operations and of the moves, the two semantics are definitionally equal.
  The other overlapping forms are compared on the native differential
  vectors (`Vectors.lean`).

A run proved with `[floatExt, SsePacked.ext]` transfers to `sseExts` when it
avoids the overlap (it then decodes under `[floatExt, ssePackedRest]`); on the
overlap it agrees as far as the semantics agree, which is proved for the
forms above and tested for the others.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory)

/-! ## Restriction of an extension

`Extension.restrict` and `Extension.Disjoint.restrict_left` are those of
`Silmaril.X86.Features.Restrict`. -/

theorem Extension.restrict_embeds (e : Extension) (p : e.Syntax → Bool) :
    (e.restrict p).Embeds e :=
  Extension.Embeds.restrict e p

theorem Extension.Disjoint.restrict_right {e e' : Extension} (h : e.Disjoint e')
    (p : e'.Syntax → Bool) : e.Disjoint (e'.restrict p) :=
  (h.symm.restrict_left p).symm

/-! ## The residual SsePacked lane and the profile -/

/-- `SsePacked` without the instructions that `Sse2` decodes. -/
def ssePackedRest : Extension := SsePacked.ext.restrict fun j => !SseMerged.shadowed j

theorem ssePackedRest_embeds : ssePackedRest.Embeds SsePacked.ext :=
  Extension.restrict_embeds _ _

theorem ssePackedRest_decode_eq_some {bytes : List Byte} {j : ssePackedRest.Syntax} {n : Nat} :
    ssePackedRest.decoder.decode bytes = some (j, n) ↔ SsePacked.decode bytes = some (j.1, n) :=
  Machine.restrictDecode_eq_some

/-- The canonical `Sse2` lane and the residual `SsePacked` lane never decode the
same bytes. -/
theorem sse2Ext_disjoint_ssePackedRest : Extension.Disjoint sse2Ext ssePackedRest := by
  intro bytes
  cases h : Sse2.decode bytes with
  | none => exact .inl h
  | some r =>
    right
    obtain ⟨i, n⟩ := r
    cases h2 : ssePackedRest.decoder.decode bytes with
    | none => rfl
    | some r' =>
      exfalso
      obtain ⟨⟨j, hj⟩, m⟩ := r'
      have hp := ssePackedRest_decode_eq_some.mp h2
      rw [SseMerged.decode_agree h] at hp
      obtain ⟨j', hj', heq⟩ := Option.map_eq_some_iff.mp hp
      simp only at heq
      obtain ⟨rfl, -⟩ := heq
      have hs : SseMerged.shadowed j = true := (SseMerged.shadowed_iff j).mpr ⟨i, hj'⟩
      simp [hs] at hj

theorem floatExt_disjoint_ssePackedRest : Extension.Disjoint floatExt ssePackedRest :=
  SsePacked.disjoint_floatExt'.restrict_right _

/-- The reconciled legacy SSE/SSE2 profile. -/
def sseExts : List Extension := [floatExt, sse2Ext, ssePackedRest]

theorem sseExts_pairwiseDisjoint : Extension.PairwiseDisjoint sseExts := by
  simp only [sseExts, Extension.PairwiseDisjoint, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
    IsEmpty.forall_iff, implies_true]
  exact ⟨⟨floatExt_disjoint_sse2Ext, floatExt_disjoint_ssePackedRest⟩,
    sse2Ext_disjoint_ssePackedRest⟩

theorem included_sse2 : Included [floatExt, sse2Ext] sseExts :=
  Included.of_subset (by simp [sseExts])

theorem included_float : Included [floatExt] sseExts :=
  Included.of_subset (by simp [sseExts])

theorem included_ssePackedRest : Included [floatExt, ssePackedRest] sseExts :=
  Included.of_subset (by simp [sseExts])

theorem sseExts_included_nil : Included [] sseExts := fun _ h => absurd h List.not_mem_nil

/-- The residual profile is included in the recovered lane's own profile. -/
theorem included_ssePackedRest_ssePacked :
    Included [floatExt, ssePackedRest] [floatExt, SsePacked.ext] := by
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact ⟨floatExt, by simp, Extension.Embeds.refl _⟩
  · exact ⟨SsePacked.ext, by simp, ssePackedRest_embeds⟩

/-! ## Transfer from the lanes' own profiles -/

variable {F : FeatureSet} {exit : Word}

/-- A run of the canonical lane's profile whose states all decode is the same
run with the reconciled profile. -/
theorem run_sse2_conservative {initial : MState}
    (hdec : ∀ n m, run F [floatExt, sse2Ext] exit n initial = some m →
      Decodes [floatExt, sse2Ext] m) (n : Nat) :
    run F sseExts exit n initial = run F [floatExt, sse2Ext] exit n initial :=
  run_conservative sseExts_pairwiseDisjoint included_sse2 hdec n

theorem run_float_conservative {initial : MState}
    (hdec : ∀ n m, run F [floatExt] exit n initial = some m → Decodes [floatExt] m) (n : Nat) :
    run F sseExts exit n initial = run F [floatExt] exit n initial :=
  run_conservative sseExts_pairwiseDisjoint included_float hdec n

theorem run_ssePackedRest_conservative {initial : MState}
    (hdec : ∀ n m, run F [floatExt, ssePackedRest] exit n initial = some m →
      Decodes [floatExt, ssePackedRest] m) (n : Nat) :
    run F sseExts exit n initial = run F [floatExt, ssePackedRest] exit n initial :=
  run_conservative sseExts_pairwiseDisjoint included_ssePackedRest hdec n

theorem run_nil_sseExts_conservative {initial : MState}
    (hdec : ∀ n m, run F [] exit n initial = some m → Decodes [] m) (n : Nat) :
    run F sseExts exit n initial = run F [] exit n initial :=
  run_conservative sseExts_pairwiseDisjoint sseExts_included_nil hdec n

/-- One step that the canonical lane's profile decodes is unchanged. -/
theorem step_sse2_conservative {m : MState} (hdec : Decodes [floatExt, sse2Ext] m) :
    step F sseExts exit m = step F [floatExt, sse2Ext] exit m :=
  step_conservative sseExts_pairwiseDisjoint included_sse2 hdec

/-! ## Agreement on the overlap -/

namespace SseMerged

/-- Both lanes require the same CPUID features on the overlap. -/
theorem requires_toPacked {i : Sse2.Instr} {j : SsePacked.Instr} (h : toPacked i = some j) :
    j.requires = i.requires := by
  cases i
  case movRRStore => cases h
  case movqStore dst _ =>
    cases dst with
    | reg => cases h
    | mem => simp only [toPacked, Option.some.injEq] at h; subst h; rfl
  case shiftBytes left _ _ =>
    cases left <;> (simp only [toPacked, Option.some.injEq] at h; subst h; rfl)
  case movLoad k _ _ | movStore k _ _ =>
    simp only [toPacked, Option.some.injEq] at h; subst h; cases k <;> rfl
  case movRR k _ _ =>
    simp only [toPacked, Option.some.injEq] at h; subst h; cases k <;> rfl
  all_goals (simp only [toPacked, Option.some.injEq] at h; subst h; rfl)

theorem exec_toPacked_logic (op : Sse2.Logic) (dst src : XReg) (n : Nat) (s : State)
    (memory : Memory) :
    (SsePacked.Instr.pint (binOp (.logic op)) dst (.reg src)).exec n s memory =
      Sse2.exec (.binop (.logic op) dst (.reg src)) n s memory := by
  cases op <;> rfl

theorem exec_toPacked_movRR (k : Sse2.RRKind) (dst src : XReg) (n : Nat) (s : State)
    (memory : Memory) :
    (SsePacked.Instr.movReg (regMov k) dst src).exec n s memory =
      Sse2.exec (.movRR k dst src) n s memory := rfl

theorem exec_toPacked_movqLoad (dst src : XReg) (n : Nat) (s : State) (memory : Memory) :
    (SsePacked.Instr.movqLoad dst (.reg src)).exec n s memory =
      Sse2.exec (.movqLoad dst (.reg src)) n s memory := rfl

end SseMerged

end Silmaril.X86.Features
