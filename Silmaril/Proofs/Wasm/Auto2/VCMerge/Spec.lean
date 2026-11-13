module

public import Silmaril.Proofs.Wasm.Auto2.VCMerge.Conds
public import Silmaril.Wasm.Auto2.VCSort.Thms

/-!
# `merge` through the VC generator: the specification

`merge_tspec`: every function instance running `merge` meets `fspec mergeFns mergeSpecV` for total
correctness (`genFunc_tsound` on `merge_vcs`). `mergeSpec_vcgen`: the same, restated as the
specification library's `Silmaril.WasmSpec.MergeSort.MergeSpec` (a second solution of it, through
the generator: `TFSpecAt.conseq` from `fspec` to `mergeSpec`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCMerge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Hoare (FSpec TFSpecAt)
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.MergeSort (mergeSpec Sorts)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- **`merge` meets its annotated specification**, for total correctness, at every profile and for
every host relation. -/
theorem merge_tspec {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm Silmaril.WasmSpec.MergeSort.mergeFunc)
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 4) (hrs : rs.length = 0) :
    TFSpecAt P host a (fspec mergeFns mergeSpecV a fi) :=
  genFunc_tsound rfl hcode he hps.symm hrs.symm merge_vcs (by intro c hc; cases hc)

/-- The environment of the arguments `p, m, n, t` and the memory `B`. -/
def envOf (p m n t : BitVec 32) (B : ByteArray) : Env where
  e32 i := [p, m, n, t].getD i 0
  e64 _ := 0
  mem _ := B

theorem argsOf_envOf (p m n t : BitVec 32) (B : ByteArray) :
    argsOf mergeSpecV (envOf p m n t B) = [.i32 p, .i32 m, .i32 n, .i32 t] := rfl

theorem globOk_merge {s : Store H} {mi : ModuleInst} {ρ : Env} : GlobOk mergeSpecV s mi ρ :=
  ⟨fun g _ _ hg => by simp [mergeSpecV] at hg, fun g t ht => by simp [mergeSpecV] at ht⟩

theorem pre_conseq {a : Nat} {fi : FuncInst H} {s : Store H} {args : List Val}
    (hp : (mergeSpec a fi).pre s args) : (fspec mergeFns mergeSpecV a fi).pre s args := by
  obtain ⟨hfi, p, m, n, t, ma, mt, B, rfl, ⟨⟨hm, hs⟩, hl⟩, hmn, hL, hR⟩ := hp
  have hc : Callees mergeSpecV fi s := by
    intro c hc
    simp [mergeSpecV] at hc
  have hmo : MemOk mergeSpecV s fi.module ((envOf p m n t B).mem 0) := ⟨ma, ⟨mt, B⟩, hm, hs, rfl⟩
  exact ⟨hfi, hc, envOf p m n t B, (argsOf_envOf p m n t B).symm, hmo, globOk_merge,
    ⟨hl, hmn, hL, hR⟩⟩

theorem post_args {fi : FuncInst H} {s s' : Store H} {p m n t : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B B' : ByteArray} (hmB : MemAt s fi.module ma mt B)
    (hs' : s' = setGs (upd mergeSpecV s fi.module B') fi.module [])
    (hpost : ∀ ρ, [.i32 p, .i32 m, .i32 n, .i32 t] = argsOf mergeSpecV ρ →
      MemOk mergeSpecV s fi.module (ρ.mem 0) → GlobOk mergeSpecV s fi.module ρ →
      mergeSpecV.post.den mergeFns ρ (valEnv ([] ++ []) B')) :
    s' = s.setMem ma ⟨mt, B'⟩ ∧ Sorts B B' p.toNat n.toNat t.toNat := by
  obtain ⟨hm, hs⟩ := hmB
  have hρ := hpost (envOf p m n t B) (argsOf_envOf p m n t B).symm ⟨ma, ⟨mt, B⟩, hm, hs, rfl⟩
    globOk_merge
  refine ⟨?_, ?_⟩
  · rw [hs', setGs_nil]
    simp [upd, mergeSpecV, setM, hm, hs]
  · simpa [mergeSpecV, Fm.den, MR.den, valEnv, envOf, Tm.dens32, Tm.den, Env.get,
      mergeFns] using hρ

theorem post_conseq {a : Nat} {fi : FuncInst H} {s s' : Store H} {args : List Val}
    {o : Silmaril.Wasm.Logic.Core.Outcome} (hpre : (mergeSpec a fi).pre s args)
    (hq : (fspec mergeFns mergeSpecV a fi).post s args s' o) :
    (mergeSpec a fi).post s args s' o := by
  obtain ⟨B', G, hs', hG, res, rfl, hlen, -, hpost⟩ := hq
  obtain rfl : G = [] := by simpa [mergeSpecV] using hG
  obtain rfl : res = [] := List.eq_nil_of_length_eq_zero hlen
  obtain ⟨-, p, m, n, t, ma, mt, B, rfl, ⟨hmB, -⟩, -⟩ := hpre
  intro p' m' n' t' ma' mt' B'' hargs hm'
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hmB
  rcases hargs with h | ⟨h, -⟩
  · simp only [List.cons.injEq, and_true, Val.i32, Val.num.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ : p = p' ∧ m = m' ∧ n = n' ∧ t = t' :=
      ⟨Silmaril.Wasm.Auto.VCGen.numVal_inj h.1, Silmaril.Wasm.Auto.VCGen.numVal_inj h.2.1,
        Silmaril.Wasm.Auto.VCGen.numVal_inj h.2.2.1, Silmaril.Wasm.Auto.VCGen.numVal_inj h.2.2.2⟩
    exact ⟨rfl, B', post_args hmB hs' hpost⟩
  · simp at h

/-- **`merge`, through the VC generator**: a second solution of the specification library's
`Silmaril.WasmSpec.MergeSort.MergeSpec` (total correctness, every profile, every host relation), from
the 33 conditions of `merge_vcs`. -/
theorem mergeSpec_vcgen : Silmaril.WasmSpec.MergeSort.MergeSpec := by
  intro H P host a fi ps rs hcode he hps hrs
  exact VCSort.TFSpecAt.conseq (merge_tspec hcode he hps hrs) (fun _ _ hp => pre_conseq hp)
    (fun _ _ _ _ hp hq => post_conseq hp hq)

end Silmaril.Wasm.Auto2.VCMerge
