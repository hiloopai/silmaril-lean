module

public import Silmaril.Proofs.Wasm.Auto2.VCBSearch.Conds
public import Silmaril.Wasm.Auto2.VCBTree.Thms
public import Silmaril.Wasm.Auto2.VCSort.Thms

/-!
# `btree_search` through the VC generator: the specifications

* `search_spec`: every function instance running `btree_search` meets
  `fspec searchFns searchSpecV` (partial correctness, every profile, every host relation), given
  its callees in the store (`fspec`'s `Callees`: functions `0` and `1` of its module are instances
  of `oba_get` and `oba_find`); the callees' contracts are proved here (`getBA_vcs`, `find_vcs'`);
* `search_tspec`: the same for total correctness against `searchSpecT` (ghost height);
* `searchL_valid`, `searchLT_valid`: restated as the library's `searchSpec` with the callees in
  the store added to the precondition (`searchSpecL`), and for total correctness also the height
  bound (`searchSpecLT`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCBSearch

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation (Expand Ty)
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Logic.Hoare (FSpec TFSpecAt FSpecValid)
open Silmaril.Wasm.Logic.Words
open Silmaril.WasmSpec.BTree (searchSpec searchFunc getFunc findFunc IsBTree)
open Silmaril.Wasm.Auto2.VCBTree (findSpecV f_entry f_len_bound f_exit_len f_elem_bound f_exit_found
  f_step f_var memOk_of store_same res_one memAt_bytes globOk_none)

variable {H : Type} {P : Profile} {host : HostSemantics H}

set_option maxRecDepth 100000 in
/-- The conditions of `oba_find` (`find_vcs` of `Silmaril.Wasm.Auto2.VCBTree`) under `searchFns`. -/
theorem find_vcs' : AllValid searchFns (genFunc findSpecV findFunc searchFuel) := by
  vcgen4
  · exact fun h => f_entry h
  · exact fun h => f_len_bound h
  · exact fun h => f_exit_len h
  · exact fun h => f_elem_bound h
  · exact fun h => f_exit_found h
  · exact fun h => f_step h
  · exact fun h => f_var h

/-- The callees, partial correctness. -/
theorem callees_part : CalleesValid .part P host searchFns searchSpecV := by
  intro e he a' fi' ps' rs' hcode hE hp hr
  simp only [searchSpecV, searchCalls, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact genFunc_sound hcode hE hp hr getBA_vcs (by intro c hc; cases hc)
  · exact genFunc_sound hcode hE hp hr find_vcs' (by intro c hc; cases hc)

/-- The callees, total correctness. -/
theorem callees_total : CalleesValid .total P host searchFns searchSpecT := by
  intro e he a' fi' ps' rs' hcode hE hp hr
  simp only [searchSpecT, searchSpecV, searchCalls, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · exact genFunc_tsound rfl hcode hE hp hr getBA_vcs (by intro c hc; cases hc)
  · exact genFunc_tsound rfl hcode hE hp hr find_vcs' (by intro c hc; cases hc)

/-- **`btree_search`, partial correctness** (every profile, every host relation). -/
theorem search_spec {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm searchFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) : FSpecValid P host a (fspec searchFns searchSpecV a fi) :=
  genFunc_sound hcode he hps.symm hrs.symm search_vcs callees_part

/-- **`btree_search`, total correctness** (the ghost height as variant). -/
theorem search_tspec {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm searchFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) : TFSpecAt P host a (fspec searchFns searchSpecT a fi) :=
  genFunc_tsound rfl hcode he hps.symm hrs.symm search_tvcs callees_total

/-! ## The library's specification -/

/-- The library's `searchSpec` with the callees in the store. -/
def searchSpecL (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := (searchSpec a fi).pre s args ∧ Callees searchSpecV fi s
  post := (searchSpec a fi).post

/-- The library's `searchSpec` with the callees in the store and the height bound. -/
noncomputable def searchSpecLT (a : Nat) (fi : FuncInst H) : FSpec H where
  pre s args := (searchSpec a fi).pre s args ∧ Callees searchSpecV fi s ∧
    ∀ ma mt B, MemAt s fi.module ma mt B → hgt B (wd B 4).toNat < 2 ^ 32
  post := (searchSpec a fi).post

/-- The environment of one `i32` argument and the memory `B`. -/
def envOf1 (k : BitVec 32) (B : ByteArray) : Env where
  e32 _ := k
  e64 _ := 0
  mem _ := B

theorem argsOf_envOf1 {S : FnSpec} (hS : S.params = [.i32]) (k : BitVec 32) (B : ByteArray) :
    argsOf S (envOf1 k B) = [.i32 k] := by
  simp [argsOf, hS, envOf1, Env.get, Val.i32]

theorem arg1_inj {k k' : BitVec 32} (h : [Val.i32 k] = [Val.i32 k']) : k = k' := by
  simp only [List.cons.injEq, Val.i32, Val.num.injEq, and_true] at h
  exact Silmaril.Wasm.Auto.VCGen.numVal_inj h

theorem search_post_den {S : FnSpec} (hS : S.post = searchSpecV.post) {k b : BitVec 32}
    {B B' : ByteArray} (h : S.post.den searchFns (envOf1 k B) (valEnv ([.i32 b] ++ []) B')) :
    searchFns.pr 9 B [k, b] ∧ B' = B := by
  rw [hS] at h
  simpa [searchSpecV, Fm.den, MR.den, valEnv, envOf1, Tm.dens32, Tm.den, Env.get, Val.i32] using h

/-- The library's postcondition from `fspec`'s, for both specifications. -/
theorem post_conseq {S : FnSpec} (hS : S.post = searchSpecV.post) (hm : S.mem = true)
    (hg : S.globals = []) (hr : S.results = [.i32]) (hpa : S.params = [.i32]) {a : Nat}
    {fi : FuncInst H} {s s' : Store H} {args : List Val} {o : Silmaril.Wasm.Logic.Core.Outcome}
    (hp : (searchSpec a fi).pre s args) (hq : (fspec searchFns S a fi).post s args s' o) :
    (searchSpec a fi).post s args s' o := by
  obtain ⟨-, k₀, ma₀, mt₀, B₀, -, -, rfl, hm₀, -⟩ := hp
  obtain ⟨B', G, hs', hG, res, rfl, -, hty, hpost⟩ := hq
  obtain rfl : G = [] := by simpa [hg] using hG
  obtain ⟨b, rfl⟩ := res_one (by simpa [hr] using hty)
  obtain ⟨h9, rfl⟩ := search_post_den hS (hpost (envOf1 k₀ B₀) (argsOf_envOf1 hpa k₀ B₀).symm
    (memOk_of hm hm₀) (globOk_none hg))
  refine ⟨by rw [hs', setGs_nil, store_same hm hm₀], ?_⟩
  intro k ma mt B t κ hargs hmB hb
  obtain rfl := arg1_inj hargs
  obtain rfl := memAt_bytes hmB hm₀
  exact ⟨b, rfl, h9 t κ hb⟩

/-- The consequence rule for partial-correctness function specifications. -/
theorem FSpecValid.conseq {a : Nat} {S S' : FSpec H} (h : FSpecValid P host a S)
    (hpre : ∀ s args, S'.pre s args → S.pre s args)
    (hpost : ∀ s args s' o, S'.pre s args → S.post s args s' o → S'.post s args s' o) :
    FSpecValid P host a S' := by
  intro n s args hp f vs₀ c hc
  refine Silmaril.Wasm.Logic.Hoare.Safe.post_mono ?_ (h n s args (hpre s args hp) f vs₀ c hc)
  rintro s' f' o ⟨rfl, ⟨res, rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨a', rfl, hq⟩⟩
  · exact ⟨rfl, .inl ⟨res, rfl, hpost _ _ _ _ hp hq⟩⟩
  · exact ⟨rfl, .inr (.inl ⟨rfl, hpost _ _ _ _ hp hq⟩)⟩
  · exact ⟨rfl, .inr (.inr ⟨a', rfl, hpost _ _ _ _ hp hq⟩)⟩

/-- **The library's `searchSpec`, partial correctness**, with the callees in the store. -/
theorem searchL_valid {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm searchFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) : FSpecValid P host a (searchSpecL a fi) := by
  refine FSpecValid.conseq (search_spec hcode he hps hrs) (fun s args hp => ?_)
    (fun _ _ _ _ hp hq => post_conseq rfl rfl rfl rfl rfl hp.1 hq)
  obtain ⟨⟨hfi, k, ma, mt, B, t, κ, rfl, hm, hb⟩, hc⟩ := hp
  exact ⟨hfi, hc, envOf1 k B, (argsOf_envOf1 rfl k B).symm, memOk_of rfl hm, globOk_none rfl,
    ⟨t, κ, hb⟩⟩

/-- **The library's `searchSpec`, total correctness**, with the callees in the store and the
height bound. -/
theorem searchLT_valid {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)}
    (hcode : fi.code = .wasm searchFunc) (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1)
    (hrs : rs.length = 1) : TFSpecAt P host a (searchSpecLT a fi) := by
  refine VCSort.TFSpecAt.conseq (search_tspec hcode he hps hrs) (fun s args hp => ?_)
    (fun _ _ _ _ hp hq => post_conseq rfl rfl rfl rfl rfl hp.1 hq)
  obtain ⟨⟨hfi, k, ma, mt, B, t, κ, rfl, hm, hb⟩, hc, hh⟩ := hp
  exact ⟨hfi, hc, envOf1 k B, (argsOf_envOf1 rfl k B).symm, memOk_of rfl hm, globOk_none rfl,
    ⟨⟨t, κ, hb⟩, hh ma mt B hm⟩⟩

end Silmaril.Wasm.Auto2.VCBSearch
