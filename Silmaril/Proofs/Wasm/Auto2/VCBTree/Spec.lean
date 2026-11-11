module

public import Silmaril.Proofs.Wasm.Auto2.VCBTree.Conds
public import Silmaril.Wasm.Auto2.VCSort.Thms

/-!
# The B-tree library's array functions through VC generator 4: the specification

`get_tspec`, `find_tspec`: total correctness of `oba_get` and `oba_find` against the annotated
specifications (`genFunc_tsound`); `obaSpec_vcgen`: the specification library's
`Silmaril.WasmSpec.BTree.OBASpec`, a second solution through the generator
(`Silmaril.Wasm.Auto2.VCSort.TFSpecAt.conseq`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBTree

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Hoare (FSpec TFSpecAt)
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.BTree (OBA FindsAt getSpec findSpec getFunc findFunc)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The environment of two `i32` arguments and the memory `B`. -/
def envOf (x y : BitVec 32) (B : ByteArray) : Env where
  e32 i := if i = 0 then x else y
  e64 _ := 0
  mem _ := B

theorem argsOf_envOf {S : FnSpec} (hS : S.params = [.i32, .i32]) (x y : BitVec 32)
    (B : ByteArray) : argsOf S (envOf x y B) = [.i32 x, .i32 y] := by
  simp [argsOf, hS, envOf, Env.get, Val.i32]

theorem env_of_args {S : FnSpec} (hS : S.params = [.i32, .i32]) {ρ : Env} {x y : BitVec 32}
    (h : argsOf S ρ = [.i32 x, .i32 y]) : ρ.e32 0 = x ∧ ρ.e32 1 = y := by
  simp only [argsOf, hS, List.mapIdx_cons, List.mapIdx_nil, List.cons.injEq, Val.i32,
    Val.num.injEq] at h
  exact ⟨Silmaril.Wasm.Auto.VCGen.numVal_inj h.1, Silmaril.Wasm.Auto.VCGen.numVal_inj h.2.1⟩

theorem globOk_none {S : FnSpec} (hS : S.globals = []) {s : Store H} {mi : ModuleInst} {ρ : Env} :
    GlobOk S s mi ρ :=
  ⟨fun g _ _ hg => by simp [hS] at hg, fun g t ht => by simp [hS] at ht⟩

/-- The memory `0` of `fi`'s module, as `MemOk` of a specification using memory. -/
theorem memOk_of {S : FnSpec} (hS : S.mem = true) {s : Store H} {mi : ModuleInst} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (h : MemAt s mi ma mt B) : MemOk S s mi B := by
  simp only [MemOk, hS, ↓reduceIte]
  exact ⟨ma, ⟨mt, B⟩, h.1, h.2, rfl⟩

/-- The final store of a call that leaves memory unchanged. -/
theorem store_same {S : FnSpec} (hS : S.mem = true) {s : Store H} {mi : ModuleInst} {ma : Nat}
    {mt : MemoryType} {B : ByteArray} (h : MemAt s mi ma mt B) : upd S s mi B = s := by
  simp only [upd, hS, ↓reduceIte, setM, h.1, h.2]
  exact setMem_self h.2

theorem res_one {res : List Val} (h : res.map valTy = [some IntType.i32]) :
    ∃ r : BitVec 32, res = [.i32 r] := by
  rcases res with _ | ⟨v, _ | ⟨w, r⟩⟩ <;> simp at h
  obtain ⟨r, rfl⟩ := valTy_eq_some h
  exact ⟨r, rfl⟩

/-! ## `oba_get` -/

theorem get_tspec {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm getFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 2)
    (hrs : rs.length = 1) : TFSpecAt P host a (fspec btFns getSpecV a fi) :=
  genFunc_tsound rfl hcode he hps.symm hrs.symm get_vcs (by intro c hc; cases hc)

theorem get_pre {a : Nat} {fi : FuncInst H} {s : Store H} {args : List Val}
    (hp : (getSpec a fi).pre s args) : (fspec btFns getSpecV a fi).pre s args := by
  obtain ⟨hfi, x, k, ma, mt, B, n, α, rfl, hm, hoba, hk⟩ := hp
  have hc : Callees getSpecV fi s := by intro c hc; simp [getSpecV] at hc
  exact ⟨hfi, hc, envOf x k B, (argsOf_envOf rfl x k B).symm, memOk_of rfl hm, globOk_none rfl,
    ⟨n, α, hoba, hk⟩⟩

theorem memAt_bytes {s : Store H} {mi : ModuleInst} {ma ma' : Nat} {mt mt' : MemoryType}
    {B B' : ByteArray} (h : MemAt s mi ma mt B) (h' : MemAt s mi ma' mt' B') : B = B' := by
  have hma : ma = ma' := Option.some.inj (h.1.symm.trans h'.1)
  subst hma
  exact congrArg MemInst.bytes (Option.some.inj (h.2.symm.trans h'.2))

theorem args2_inj {x y x' y' : BitVec 32} (h : [Val.i32 x, Val.i32 y] = [Val.i32 x', Val.i32 y']) :
    x = x' ∧ y = y' := by
  simp only [List.cons.injEq, Val.i32, Val.num.injEq, and_true] at h
  exact ⟨Silmaril.Wasm.Auto.VCGen.numVal_inj h.1, Silmaril.Wasm.Auto.VCGen.numVal_inj h.2⟩

theorem get_post_den {x k r : BitVec 32} {B B' : ByteArray}
    (h : getSpecV.post.den btFns (envOf x k B) (valEnv ([.i32 r] ++ []) B')) :
    btFns.pr 1 B [x, k, r] ∧ B' = B := by
  simpa [getSpecV, Fm.den, MR.den, valEnv, envOf, Tm.dens32, Tm.den, Env.get, Val.i32] using h

theorem find_post_den {x e r : BitVec 32} {B B' : ByteArray}
    (h : findSpecV.post.den btFns (envOf x e B) (valEnv ([.i32 r] ++ []) B')) :
    btFns.pr 3 B [x, e, r] ∧ B' = B := by
  simpa [findSpecV, Fm.den, MR.den, valEnv, envOf, Tm.dens32, Tm.den, Env.get, Val.i32] using h

theorem get_post {a : Nat} {fi : FuncInst H} {s s' : Store H} {args : List Val}
    {o : Silmaril.Wasm.Logic.Core.Outcome} (hp : (getSpec a fi).pre s args)
    (hq : (fspec btFns getSpecV a fi).post s args s' o) : (getSpec a fi).post s args s' o := by
  obtain ⟨-, x₀, k₀, ma₀, mt₀, B₀, -, -, rfl, hm₀, -, -⟩ := hp
  obtain ⟨B', G, hs', hG, res, rfl, -, hty, hpost⟩ := hq
  obtain rfl : G = [] := by simpa [getSpecV] using hG
  obtain ⟨r, rfl⟩ := res_one (by simpa [getSpecV] using hty)
  obtain ⟨hρ1, rfl⟩ := get_post_den (hpost (envOf x₀ k₀ B₀) (argsOf_envOf rfl x₀ k₀ B₀).symm
    (memOk_of rfl hm₀) (globOk_none rfl))
  refine ⟨by rw [hs', setGs_nil, store_same rfl hm₀], ?_⟩
  intro x k ma mt B n α hargs hm hoba hk
  obtain ⟨rfl, rfl⟩ := args2_inj hargs
  obtain rfl := memAt_bytes hm hm₀
  exact congrArg (fun r => Silmaril.Wasm.Logic.Core.Outcome.normal [Val.i32 r]) (hρ1 n α hoba hk)

/-! ## `oba_find` -/

theorem find_tspec {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm findFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 2)
    (hrs : rs.length = 1) : TFSpecAt P host a (fspec btFns findSpecV a fi) :=
  genFunc_tsound rfl hcode he hps.symm hrs.symm find_vcs (by intro c hc; cases hc)

theorem find_pre {a : Nat} {fi : FuncInst H} {s : Store H} {args : List Val}
    (hp : (findSpec a fi).pre s args) : (fspec btFns findSpecV a fi).pre s args := by
  obtain ⟨hfi, x, e, ma, mt, B, n, α, rfl, hm, hoba⟩ := hp
  have hc : Callees findSpecV fi s := by intro c hc; simp [findSpecV] at hc
  exact ⟨hfi, hc, envOf x e B, (argsOf_envOf rfl x e B).symm, memOk_of rfl hm, globOk_none rfl,
    ⟨n, α, hoba⟩⟩

theorem find_post {a : Nat} {fi : FuncInst H} {s s' : Store H} {args : List Val}
    {o : Silmaril.Wasm.Logic.Core.Outcome} (hp : (findSpec a fi).pre s args)
    (hq : (fspec btFns findSpecV a fi).post s args s' o) : (findSpec a fi).post s args s' o := by
  obtain ⟨-, x₀, e₀, ma₀, mt₀, B₀, -, -, rfl, hm₀, -⟩ := hp
  obtain ⟨B', G, hs', hG, res, rfl, -, hty, hpost⟩ := hq
  obtain rfl : G = [] := by simpa [findSpecV] using hG
  obtain ⟨r, rfl⟩ := res_one (by simpa [findSpecV] using hty)
  obtain ⟨hρ1, rfl⟩ := find_post_den (hpost (envOf x₀ e₀ B₀) (argsOf_envOf rfl x₀ e₀ B₀).symm
    (memOk_of rfl hm₀) (globOk_none rfl))
  refine ⟨by rw [hs', setGs_nil, store_same rfl hm₀], ?_⟩
  intro x e ma mt B n α hargs hm hoba
  obtain ⟨rfl, rfl⟩ := args2_inj hargs
  obtain rfl := memAt_bytes hm hm₀
  exact ⟨r.toNat, hρ1 n α hoba, by simp [Val.i32]⟩

/-- **`oba_get` and `oba_find`, through the VC generator**: a second solution of the
specification library's `Silmaril.WasmSpec.BTree.OBASpec` (total correctness, every profile, every
host relation), from the 2 + 7 conditions of `get_vcs` and `find_vcs`. -/
theorem obaSpec_vcgen : Silmaril.WasmSpec.BTree.OBASpec := by
  intro H P host a fi ps rs he hps hrs
  refine ⟨fun hcode => ?_, fun hcode => ?_⟩
  · exact Silmaril.Wasm.Auto2.VCSort.TFSpecAt.conseq (get_tspec hcode he hps hrs)
      (fun _ _ hp => get_pre hp) (fun _ _ _ _ hp hq => get_post hp hq)
  · exact Silmaril.Wasm.Auto2.VCSort.TFSpecAt.conseq (find_tspec hcode he hps hrs)
      (fun _ _ hp => find_pre hp) (fun _ _ _ _ hp hq => find_post hp hq)

end Silmaril.Wasm.Auto2.VCBTree
