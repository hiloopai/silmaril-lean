module

public import Silmaril.Proofs.Wasm.Auto2.VCMSort.Conds

/-!
# Merge sort through the VC generator: the specification

* `merge_tspecN`: `merge` meets `fspec (msFns N) mergeSpecV` (from `VCMerge.merge_tspec`: the
  formulas of `mergeSpecV` only use the predicates `msFns N` shares with `mergeFns`);
* `msort_tspec`: every instance of `merge_sort` whose function `1` is itself meets
  `fspec (msFns N) msortSpec` for every `N` (`genFunc_tsound_rec`);
* `spec_vcgen`: the specification library's `Silmaril.WasmSpec.MergeSort.Spec`, a second solution
  through the generator (`N = 2 ^ 32`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCMSort

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Hoare (FSpec TFSpecAt)
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.MergeSort (Bounds Sorts sortSpec Linked mergeFunc sortFunc)
open Silmaril.Wasm.Auto2.VCMerge (mergeFns mergeSpecV merge_tspec)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- `merge` under `msFns N`. -/
theorem merge_tspecN (N : Nat) {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm mergeFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 4)
    (hrs : rs.length = 0) : TFSpecAt P host a (fspec (msFns N) mergeSpecV a fi) :=
  VCSort.TFSpecAt.conseq (merge_tspec hcode he hps hrs) (fun _ _ hp => hp)
    (fun _ _ _ _ _ hq => hq)

/-- **Merge sort meets its annotated specification** for every bound `N`, if function `1` of its
module is itself. -/
theorem msort_tspec {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm sortFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 3)
    (hrs : rs.length = 0) (hx : fi.module.funcs[1]? = some a) :
    ∀ N, TFSpecAt P host a (fspec (msFns N) msortSpec a fi) := by
  refine genFunc_tsound_rec (S' := msortSpec') rfl hcode he hps.symm hrs.symm hx msort_vcs
    (fun e he hx' => ?_) ⟨rfl, rfl, rfl, rfl⟩ (fun N ρ h => h) (fun ρ h => ?_)
    (fun N ρ ξ h => h) (fun N e he hex a' fi' ps' rs' hc hE hp hr => ?_)
  · simp only [msortSpec, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp at hx'
    · rfl
  · exact Nat.not_lt_zero _ h.2
  · simp only [msortSpec, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact merge_tspecN N hc hE hp.symm hr.symm
    · exact absurd rfl hex

/-- The environment of the arguments `p, n, t` and the memory `B`. -/
def envOf (p n t : BitVec 32) (B : ByteArray) : Env where
  e32 i := [p, n, t].getD i 0
  e64 _ := 0
  mem _ := B

theorem argsOf_envOf (p n t : BitVec 32) (B : ByteArray) :
    argsOf msortSpec (envOf p n t B) = [.i32 p, .i32 n, .i32 t] := rfl

theorem globOk_msort {s : Store H} {mi : ModuleInst} {ρ : Env} : GlobOk msortSpec s mi ρ :=
  ⟨fun g _ _ hg => by simp [msortSpec, msortSpec'] at hg,
    fun g t ht => by simp [msortSpec, msortSpec'] at ht⟩

theorem pre_conseq {a aM : Nat} {fi fiM : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm sortFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 3)
    (hrs : rs.length = 0) (hlink : Linked a fi aM fiM) {s : Store H} {args : List Val}
    (hp : (sortSpec a fi aM fiM).pre s args) :
    (fspec (msFns (2 ^ 32)) msortSpec a fi).pre s args := by
  obtain ⟨hfi, hfiM, p, n, t, ma, mt, B, rfl, ⟨hm, hs⟩, hl⟩ := hp
  obtain ⟨hx0, hx1, hcM, hmM, psM, rsM, hEM, hpM, hrM⟩ := hlink
  have hc : Callees msortSpec fi s := by
    intro c hc
    simp only [msortSpec, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨aM, fiM, psM, rsM, hx0, hfiM, hcM, hmM, hEM, by simp [mergeSpecV, hpM],
        by simp [mergeSpecV, hrM]⟩
    · exact ⟨a, fi, ps, rs, hx1, hfi, hcode, rfl, he, by simp [msortSpec', hps],
        by simp [msortSpec', hrs]⟩
  have hmo : MemOk msortSpec s fi.module ((envOf p n t B).mem 0) := ⟨ma, ⟨mt, B⟩, hm, hs, rfl⟩
  exact ⟨hfi, hc, envOf p n t B, (argsOf_envOf p n t B).symm, hmo, globOk_msort,
    ⟨hl, by have := n.isLt; simp [envOf]; omega⟩⟩

theorem post_args {fi : FuncInst H} {s s' : Store H} {p n t : BitVec 32} {ma : Nat}
    {mt : MemoryType} {B B' : ByteArray} (hmB : MemAt s fi.module ma mt B)
    (hs' : s' = setGs (upd msortSpec s fi.module B') fi.module [])
    (hpost : ∀ ρ, [.i32 p, .i32 n, .i32 t] = argsOf msortSpec ρ →
      MemOk msortSpec s fi.module (ρ.mem 0) → GlobOk msortSpec s fi.module ρ →
      msortSpec.post.den (msFns (2 ^ 32)) ρ (valEnv ([] ++ []) B')) :
    s' = s.setMem ma ⟨mt, B'⟩ ∧ Sorts B B' p.toNat n.toNat t.toNat := by
  obtain ⟨hm, hs⟩ := hmB
  have hρ := hpost (envOf p n t B) (argsOf_envOf p n t B).symm ⟨ma, ⟨mt, B⟩, hm, hs, rfl⟩
    globOk_msort
  refine ⟨?_, ?_⟩
  · rw [hs', setGs_nil]
    simp [upd, msortSpec, msortSpec', setM, hm, hs]
  · simpa [msortSpec, msortSpec', Fm.den, MR.den, valEnv, envOf, Tm.dens32, Tm.den, Env.get,
      msFns, mergeFns] using hρ

theorem post_conseq {a aM : Nat} {fi fiM : FuncInst H} {s s' : Store H} {args : List Val}
    {o : Silmaril.Wasm.Logic.Core.Outcome} (hpre : (sortSpec a fi aM fiM).pre s args)
    (hq : (fspec (msFns (2 ^ 32)) msortSpec a fi).post s args s' o) :
    (sortSpec a fi aM fiM).post s args s' o := by
  obtain ⟨B', G, hs', hG, res, rfl, hlen, -, hpost⟩ := hq
  obtain rfl : G = [] := by simpa [msortSpec, msortSpec'] using hG
  obtain rfl : res = [] := List.eq_nil_of_length_eq_zero hlen
  obtain ⟨-, -, p, n, t, ma, mt, B, rfl, ⟨hmB, -⟩⟩ := hpre
  intro p' m' n' t' ma' mt' B'' hargs hm'
  obtain ⟨rfl, rfl, rfl⟩ := hm'.unique hmB
  rcases hargs with h | ⟨h, -⟩
  · simp at h
  · simp only [List.cons.injEq, and_true, Val.i32, Val.num.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ : p = p' ∧ n = n' ∧ t = t' :=
      ⟨Silmaril.Wasm.Auto.VCGen.numVal_inj h.1, Silmaril.Wasm.Auto.VCGen.numVal_inj h.2.1,
        Silmaril.Wasm.Auto.VCGen.numVal_inj h.2.2⟩
    exact ⟨rfl, B', post_args hmB hs' hpost⟩

/-- **Merge sort, through the VC generator**: a second solution of the specification library's
`Silmaril.WasmSpec.MergeSort.Spec` (total correctness, every profile, every host relation), from the
5 conditions of `msort_vcs` (for every bound), the 33 of `merge`, and the recursion theorem
`genFunc_tsound_rec`. -/
theorem spec_vcgen : Silmaril.WasmSpec.MergeSort.Spec := by
  intro H P host a fi aM fiM ps rs hcode he hps hrs hlink
  exact VCSort.TFSpecAt.conseq (msort_tspec hcode he hps hrs hlink.2.1 (2 ^ 32))
    (fun _ _ hp => pre_conseq hcode he hps hrs hlink hp) (fun _ _ _ _ hp hq => post_conseq hp hq)

end Silmaril.Wasm.Auto2.VCMSort
