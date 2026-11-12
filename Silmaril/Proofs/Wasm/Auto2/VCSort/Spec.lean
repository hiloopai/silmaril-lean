module

public import Silmaril.Proofs.Wasm.Auto2.VCSort.Conds

/-!
# Insertion sort through the VC generator: the specification

`sort_tspec`: every function instance running `insertion_sort` meets `fspec sortFns sortSpecV`
for total correctness (`genFunc_tsound` on `sort_vcs`). `spec_vcgen`: the same, restated as the
specification library's `Silmaril.WasmSpec.InsertionSort.Spec` (a second solution of it, through the
generator: `TFSpecAt.conseq` from `fspec` to `sortSpec`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCSort

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Hoare (FSpec TFSpecAt TSafe callPost)
open Silmaril.Wasm.Logic.Words

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The consequence rule for total function specifications. -/
theorem TFSpecAt.conseq {a : Nat} {S S' : FSpec H} (h : TFSpecAt P host a S)
    (hpre : ∀ s args, S'.pre s args → S.pre s args)
    (hpost : ∀ s args s' o, S'.pre s args → S.post s args s' o → S'.post s args s' o) :
    TFSpecAt P host a S' := by
  intro s args hp f vs₀ c hc
  refine Silmaril.Wasm.Logic.Hoare.TSafe.post_mono (h s args (hpre s args hp) f vs₀ c hc) ?_
  rintro s' f' o ⟨rfl, ⟨res, rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨a', rfl, hq⟩⟩
  · exact ⟨rfl, .inl ⟨res, rfl, hpost _ _ _ _ hp hq⟩⟩
  · exact ⟨rfl, .inr (.inl ⟨rfl, hpost _ _ _ _ hp hq⟩)⟩
  · exact ⟨rfl, .inr (.inr ⟨a', rfl, hpost _ _ _ _ hp hq⟩)⟩

/-- **Insertion sort meets its annotated specification**, for total correctness, at every profile
and for every host relation. -/
theorem sort_tspec {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm Silmaril.WasmSpec.InsertionSort.sortFunc)
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 0) :
    TFSpecAt P host a (fspec sortFns sortSpecV a fi) :=
  genFunc_tsound rfl hcode he hps.symm hrs.symm sort_vcs (by intro c hc; cases hc)

/-- The environment of the arguments `p, n` and the memory `B`. -/
def envOf (p n : BitVec 32) (B : ByteArray) : Env where
  e32 i := if i = 0 then p else n
  e64 _ := 0
  mem _ := B

theorem argsOf_envOf (p n : BitVec 32) (B : ByteArray) :
    argsOf sortSpecV (envOf p n B) = [.i32 p, .i32 n] := rfl

theorem envOf_of_args {ρ : Env} {p n : BitVec 32} (h : argsOf sortSpecV ρ = [.i32 p, .i32 n]) :
    ρ.e32 0 = p ∧ ρ.e32 1 = n := by
  simp only [argsOf, sortSpecV, List.mapIdx_cons, List.mapIdx_nil, List.cons.injEq, Val.i32,
    Val.num.injEq] at h
  exact ⟨Silmaril.Wasm.Auto.VCGen.numVal_inj h.1, Silmaril.Wasm.Auto.VCGen.numVal_inj h.2.1⟩

theorem globOk_sort {s : Store H} {mi : ModuleInst} {ρ : Env} : GlobOk sortSpecV s mi ρ :=
  ⟨fun g _ _ hg => by simp [sortSpecV] at hg, fun g t ht => by simp [sortSpecV] at ht⟩

theorem pre_conseq {a : Nat} {fi : FuncInst H} {s : Store H} {args : List Val}
    (hp : (Silmaril.WasmSpec.InsertionSort.sortSpec a fi).pre s args) :
    (fspec sortFns sortSpecV a fi).pre s args := by
  obtain ⟨hfi, p, n, ma, mt, B, rfl, ⟨hm, hs⟩, hb, hw⟩ := hp
  have hc : Callees sortSpecV fi s := by
    intro c hc
    simp [sortSpecV] at hc
  have hmo : MemOk sortSpecV s fi.module ((envOf p n B).mem 0) := ⟨ma, ⟨mt, B⟩, hm, hs, rfl⟩
  exact ⟨hfi, hc, envOf p n B, (argsOf_envOf p n B).symm, hmo, globOk_sort, ⟨hb, hw⟩⟩

theorem post_conseq {a : Nat} {fi : FuncInst H} {s s' : Store H} {args : List Val}
    {o : Silmaril.Wasm.Logic.Core.Outcome}
    (hq : (fspec sortFns sortSpecV a fi).post s args s' o) :
    (Silmaril.WasmSpec.InsertionSort.sortSpec a fi).post s args s' o := by
  obtain ⟨B', G, hs', hG, res, rfl, hlen, -, hpost⟩ := hq
  obtain rfl : G = [] := by simpa [sortSpecV] using hG
  obtain rfl : res = [] := List.eq_nil_of_length_eq_zero hlen
  intro p n ma mt B hargs ⟨hm, hs⟩
  subst hargs
  refine ⟨rfl, B', ?_, ?_⟩
  · rw [hs', setGs_nil]
    simp [upd, sortSpecV, setM, hm, hs]
  · have hρ := hpost (envOf p n B) (argsOf_envOf p n B).symm ⟨ma, ⟨mt, B⟩, hm, hs, rfl⟩ globOk_sort
    simpa [sortSpecV, Fm.den, MR.den, valEnv, envOf, Tm.dens32, Tm.den, Env.get,
      sortFns_post] using hρ

/-- **Insertion sort, through the VC generator**: a second solution of the specification
library's `Silmaril.WasmSpec.InsertionSort.Spec` (total correctness, every profile, every host
relation), from the 15 conditions of `sort_vcs`. -/
theorem spec_vcgen : Silmaril.WasmSpec.InsertionSort.Spec := by
  intro H P host a fi ps rs hcode he hps hrs
  exact TFSpecAt.conseq (sort_tspec hcode he hps hrs) (fun _ _ hp => pre_conseq hp)
    (fun _ _ _ _ _ hq => post_conseq hq)

end Silmaril.Wasm.Auto2.VCSort
