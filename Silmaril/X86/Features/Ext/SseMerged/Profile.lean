module

public import Silmaril.X86.Features.Ext.SseMerged.Extension
public import Silmaril.X86.Features.Ext.Sse4.Extension

/-!
# The legacy-SSE profile up to SSE4.2

`sse42Exts = [floatExt, sse2Ext, ssePackedRest, sse4Ext]` adds the SSE3–SSE4.2
lane to the reconciled SSE/SSE2 profile `sseExts`. It is pairwise disjoint
(`sse42Exts_pairwiseDisjoint`), and `sseExts` and the canonical SSE2 lane's
profile are `Included` in it, so their decoded runs transfer by
`run_conservative` (`run_sseExts_conservative`, `run_sse2_sse42_conservative`).
Combined with `FeatureFree.same_behaviour`, a run proved on an SSE2-only
machine with `sseExts` is the same run on any machine with more features and
the SSE4 decoder.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word)

theorem ssePackedRest_disjoint_sse4Ext : Extension.Disjoint ssePackedRest sse4Ext :=
  ssePacked_disjoint_sse4Ext.restrict_left _

/-- The legacy-encoded scalar and packed SSE profile up to SSE4.2. -/
def sse42Exts : List Extension := [floatExt, sse2Ext, ssePackedRest, sse4Ext]

theorem sse42Exts_pairwiseDisjoint : Extension.PairwiseDisjoint sse42Exts := by
  simp only [sse42Exts, Extension.PairwiseDisjoint, List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true,
    IsEmpty.forall_iff, implies_true]
  exact ⟨⟨floatExt_disjoint_sse2Ext, floatExt_disjoint_ssePackedRest, floatExt_disjoint_sse4Ext⟩,
    ⟨sse2Ext_disjoint_ssePackedRest, sse2Ext_disjoint_sse4Ext⟩, ssePackedRest_disjoint_sse4Ext⟩

theorem included_sseExts : Included sseExts sse42Exts :=
  Included.of_subset (by simp [sseExts, sse42Exts])

theorem included_sse2_sse42 : Included [floatExt, sse2Ext] sse42Exts :=
  Included.of_subset (by simp [sse42Exts])

theorem included_sse4 : Included [sse4Ext] sse42Exts :=
  Included.of_subset (by simp [sse42Exts])

variable {F : FeatureSet} {exit : Word}

theorem run_sseExts_conservative {initial : MState}
    (hdec : ∀ n m, run F sseExts exit n initial = some m → Decodes sseExts m) (n : Nat) :
    run F sse42Exts exit n initial = run F sseExts exit n initial :=
  run_conservative sse42Exts_pairwiseDisjoint included_sseExts hdec n

theorem run_sse2_sse42_conservative {initial : MState}
    (hdec : ∀ n m, run F [floatExt, sse2Ext] exit n initial = some m →
      Decodes [floatExt, sse2Ext] m) (n : Nat) :
    run F sse42Exts exit n initial = run F [floatExt, sse2Ext] exit n initial :=
  run_conservative sse42Exts_pairwiseDisjoint included_sse2_sse42 hdec n

end Silmaril.X86.Features
