module

public import Silmaril.X86.Features.Ext.Sse2.Encoding
public import Silmaril.X86.Features.Ext.Sse2.Semantics
public import Silmaril.X86.Features.Embed

/-!
# The SSE/SSE2 integer and move lane as an extension

`sse2Ext` packages the lane for the feature-parametric machine: the codec of
`Encoding.lean`, `Instr.requires` (SSE for MOVAPS/MOVUPS, SSE2 otherwise) and
`exec`.

## Lattice facts

* `sse2Ext_disjoint_floatExt`, `floatExt_disjoint_sse2Ext`: the lane and
  `X86.Float`'s scalar SSE extension never decode the same bytes, so
  `[floatExt, sse2Ext]` is pairwise disjoint (`pairwiseDisjoint`), in either
  order.
* `included_floatExt`, `included_sse2Ext`: each of `[floatExt]`, `[sse2Ext]`,
  `[]` is `Included` in `[floatExt, sse2Ext]`.
* `run_floatExt_conservative`, `run_sse2Ext_conservative`: by
  `run_conservative`, any run proved with the weaker decoder (`[floatExt]` or
  `[sse2Ext]`) whose states all decode under it is the same run with both;
  `step_floatExt_conservative` is the one-step form. Together with
  `FeatureFree.same_behaviour` (more features), everything proved for a
  weaker decoder or feature set holds for the stronger one.
* `ext_decode_encode`: the integer decoder rejects the lane's encodings, so
  `step_sse2Ext` (from `step_of_ext`) applies whenever the lane decodes the
  bytes at RIP.
-/

@[expose] public section

namespace Silmaril.X86.Features

open Silmaril.X86 (Word Byte fetchWindow maxInstrLength)
open Silmaril.Process (Memory)

/-- The SSE/SSE2 integer and move instructions as an extension. -/
def sse2Ext : Extension where
  name := "SSE/SSE2 integer and moves"
  Syntax := Sse2.Instr
  decoder := Sse2.byteDecoder
  requires := Sse2.Instr.requires
  exec := Sse2.exec

@[simp] theorem sse2Ext_decode : sse2Ext.decoder.decode = Sse2.decode := rfl

theorem sse2Ext_requires (i : Sse2.Instr) : sse2Ext.requires i = i.requires := rfl

theorem sse2Ext_exec (i : Sse2.Instr) (n : Nat) (s : State) (memory : Memory) :
    sse2Ext.exec i n s memory = Sse2.exec i n s memory := rfl

/-- The lane requires only SSE or SSE2, both in the x86-64 baseline. -/
theorem sse2Ext_requires_baseline (i : Sse2.Instr) :
    FeatureSet.baseline64.missing (sse2Ext.requires i) = none := by
  cases i <;> simp only [sse2Ext_requires, Sse2.Instr.requires] <;> (try split) <;> decide

/-! ## Disjointness and inclusion -/

theorem sse2Ext_disjoint_floatExt : Extension.Disjoint sse2Ext floatExt :=
  Sse2.decode_disjoint_float

theorem floatExt_disjoint_sse2Ext : Extension.Disjoint floatExt sse2Ext := fun bytes =>
  (Sse2.decode_disjoint_float bytes).symm

theorem pairwiseDisjoint : Extension.PairwiseDisjoint [floatExt, sse2Ext] := by
  simp only [Extension.PairwiseDisjoint, List.pairwise_cons, List.mem_cons,
    or_false, forall_eq, List.not_mem_nil, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  exact floatExt_disjoint_sse2Ext

theorem pairwiseDisjoint' : Extension.PairwiseDisjoint [sse2Ext, floatExt] := by
  simp only [Extension.PairwiseDisjoint, List.pairwise_cons, List.mem_cons,
    or_false, forall_eq, List.not_mem_nil, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  exact sse2Ext_disjoint_floatExt

theorem included_floatExt : Included [floatExt] [floatExt, sse2Ext] :=
  Included.of_subset (by simp)

theorem included_sse2Ext : Included [sse2Ext] [floatExt, sse2Ext] :=
  Included.of_subset (by simp)

theorem included_nil : Included [] [floatExt, sse2Ext] := fun _ h => absurd h List.not_mem_nil

/-! ## Transfer from the weaker decoders -/

variable {F : FeatureSet} {exit : Word}

/-- One step that `[floatExt]` decodes is the same with the lane added. -/
theorem step_floatExt_conservative {m : MState} (hdec : Decodes [floatExt] m) :
    step F [floatExt, sse2Ext] exit m = step F [floatExt] exit m :=
  step_conservative pairwiseDisjoint included_floatExt hdec

/-- A run of `[floatExt]` that only visits decoded states is the same run with
the lane added. -/
theorem run_floatExt_conservative {initial : MState}
    (hdec : ∀ n m, run F [floatExt] exit n initial = some m → Decodes [floatExt] m) (n : Nat) :
    run F [floatExt, sse2Ext] exit n initial = run F [floatExt] exit n initial :=
  run_conservative pairwiseDisjoint included_floatExt hdec n

/-- The same for runs proved with the lane alone. -/
theorem run_sse2Ext_conservative {initial : MState}
    (hdec : ∀ n m, run F [sse2Ext] exit n initial = some m → Decodes [sse2Ext] m) (n : Nat) :
    run F [floatExt, sse2Ext] exit n initial = run F [sse2Ext] exit n initial :=
  run_conservative pairwiseDisjoint included_sse2Ext hdec n

/-- And for runs of the integer machine alone. -/
theorem run_nil_conservative {initial : MState}
    (hdec : ∀ n m, run F [] exit n initial = some m → Decodes [] m) (n : Nat) :
    run F [floatExt, sse2Ext] exit n initial = run F [] exit n initial :=
  run_conservative pairwiseDisjoint included_nil hdec n

/-! ## Stepping a lane instruction -/

/-- An instruction of the lane at RIP: the integer decoder rejects it, so the
machine takes the lane's step. -/
theorem step_sse2Ext {exts : List Extension} {m : MState} {i : Sse2.Instr} {more : List Byte}
    (hwin : fetchWindow m.memory maxInstrLength m.state.core.rip.toNat = Sse2.encode i ++ more)
    (hext : extDecode exts (Sse2.encode i ++ more) = some ⟨sse2Ext, i, (Sse2.encode i).length⟩)
    (hperm : m.memory.Permitted .execute m.state.core.rip.toNat (Sse2.encode i).length) :
    step F exts exit m = extStep F sse2Ext i (Sse2.encode i).length m :=
  step_of_ext (by rw [hwin]; exact Sse2.ext_decode_encode i more) (by rw [hwin]; exact hext) hperm

/-- In `[floatExt, sse2Ext]` the lane's encodings are found by `extDecode`. -/
theorem extDecode_sse2 (i : Sse2.Instr) (more : List Byte) :
    extDecode [floatExt, sse2Ext] (Sse2.encode i ++ more) =
      some ⟨sse2Ext, i, (Sse2.encode i).length⟩ :=
  extDecode_of_mem pairwiseDisjoint (by simp) (Sse2.decode_encode_append i more)

/-- The register-only instructions are pure. -/
theorem sse2Ext_pure_binop_reg (op : Sse2.BinOp) (dst src : X86.XReg) :
    sse2Ext.Pure (.binop op dst (.reg src)) :=
  Extension.Pure.of_eq _ (fun s => s.writeXmmLegacy dst.toV (op.eval (s.xmm dst.toV) (s.xmm src.toV)))
    (fun _ => rfl) (fun _ _ _ => rfl)

theorem sse2Ext_pure_movRR (k : Sse2.RRKind) (dst src : X86.XReg) :
    sse2Ext.Pure (.movRR k dst src) :=
  Extension.Pure.of_eq _ (fun s => s.writeXmmLegacy dst.toV (s.xmm src.toV))
    (fun _ => rfl) (fun _ _ _ => rfl)

end Silmaril.X86.Features
