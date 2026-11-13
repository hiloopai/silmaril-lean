module

public import Silmaril.Wasm.Models.V2CoreInstHostFn.Defs

/-!
# Instantiation into stores with host functions, and into stores of any host type

* `instantiate_imports_any`: the earlier `V2CoreInstImp.instantiate_imports` without its
  `HostFree` hypothesis, which was used only to conclude that the new store is host-free. The
  proof is the same.
* **`instantiate_behaviours`**: at **every** host type `H` (not only `Store Nat`), every typed
  2.0 store, every host satisfying 2.0's `HostOk` and every profile, a valid module whose imports
  are typed instantiates, and its instantiation has a behaviour under that host (2.0 type
  soundness, `V2Sound.behavioursOf_nonempty`, from `Instantiate.ok`). No `HostFree`.
* **`domInstHost_of_storeOk`**: every point of `v20instHT P`'s domain with a typed store and a
  host satisfying `HostOk` is in `domInstHost P` (behaviours at the point's own host); host
  functions allowed.
* `hostDivPt`: a store with one host function, under `divV`. It is in the domain
  (`hostDivPt_dom`), typed (`storeOk_hostFnStore`), **not** host-free (`not_hostFree_hostFnStore`,
  so the earlier `domInstP_of_storeOk_any` does not apply), and in `domInstHost P`
  (`domInstHost_hostDivPt`).

New proofs; the first follows `V2CoreInstImp/Progress`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Models.V2CoreInstFn (nopType nopModInst)
open Silmaril.Wasm.Models.V2CoreInstHostFn (domInstHost hostFunc hostFnStore hostDivPt)
open Silmaril.Proofs.Wasm.Models.V2Sound (HostFree divV hostOk_divV)
open Silmaril.Proofs.Wasm.Models.V2CoreInstDom (SegBounded forall₂_of_exists)
open Silmaril.Proofs.Wasm.Models.V2CoreInstImp (ctx_of_moduleOk_imp const_denotes_imp
  const_ref_denotes_imp allocModule_some_imp fi)

variable {H : Type}

/-- **2.0 instantiation progress with imports, without `HostFree`.** -/
theorem instantiate_imports_any (P : Profile) {s : Store H} (hs : StoreOk s)
    {m : Module} {ixt xt : List ExternType} {xas : List ExternAddr} (hm : ModuleOk m ixt xt)
    (hx : List.Forall₂ (ExternAddrOk s) xas ixt) (hb : SegBounded m) :
    ∃ c : Config H, ∀ host : HostSemantics H, Instantiate P host s m xas c := by
  obtain ⟨C', hglobals, helems, hf, hg⟩ := ctx_of_moduleOk_imp hm
  obtain ⟨vs, hvs⟩ : ∃ vs, List.Forall₂ (fun (g : Global) (v : Val) =>
      constExpr? s (fi s m xas).module g.init = some v) m.globals vs :=
    forall₂_of_exists fun g hg' => const_denotes_imp hx (hglobals g hg') hf hg
  obtain ⟨rss, hrss⟩ : ∃ rss, List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
      List.Forall₂ (fun (ex : Expr) (r : Ref) =>
        constExpr? s (fi s m xas).module ex = some (Val.ref r)) e.init rs)
      m.elems rss :=
    forall₂_of_exists fun e he =>
      forall₂_of_exists fun ex hex => const_ref_denotes_imp hs hx (helems e he ex hex) hf hg
  obtain ⟨⟨s', mi⟩, hal⟩ := allocModule_some_imp hm hx hvs.length_eq hrss.length_eq
  refine ⟨⟨s', { module := mi }, expression (runElems m ++ runDatas m ++
    (match m.start with | some x => [Instr.call x] | none => []))⟩, fun host => ?_⟩
  refine ⟨⟨ixt, xt, hm, hx⟩, hb, vs, rss, s', mi, ?_, ?_, hal, rfl⟩
  · exact hvs.imp fun _ _ h => evalExpr_of_constExpr? h
  · exact hrss.imp fun _ _ h => h.imp fun _ _ h => evalExpr_of_constExpr? h

/-- **Instantiation with a behaviour, at every host type and every well-behaved host**: no
host-free hypothesis, and stores of any type `Store H`. -/
theorem instantiate_behaviours (P : Profile) {s : Store H} (hs : StoreOk s)
    {host : HostSemantics H} (hh : HostOk host)
    {m : Module} {ixt xt : List ExternType} {xas : List ExternAddr} (hm : ModuleOk m ixt xt)
    (hx : List.Forall₂ (ExternAddrOk s) xas ixt) (hb : SegBounded m) :
    ∃ c : Config H, Instantiate P host s m xas c ∧ (behavioursOf P host c).Nonempty := by
  obtain ⟨c, hinst⟩ := instantiate_imports_any P hs hm hx hb
  obtain ⟨hok, -⟩ := Instantiate.ok hh hs (hinst host)
  exact ⟨c, hinst host, Silmaril.Proofs.Wasm.Models.V2Sound.behavioursOf_nonempty hh hok⟩

/-- **Every typed point of the domain with a well-behaved host is in `domInstHost P`**, host
functions allowed. -/
theorem domInstHost_of_storeOk {P : Profile} {p : Pt Nat} (hd : (v20instHT P).dom p)
    (hs : StoreOk p.1) (hh : HostOk p.2) : domInstHost P p := by
  refine ⟨hd, fun m cm xas hval hcm ⟨C, hC⟩ => ?_⟩
  obtain ⟨xtE, xtI, hok, hxas⟩ := hC.valid
  obtain ⟨ixt, xt, hm⟩ := hval
  have hx : List.Forall₂ (ExternAddrOk p.1) xas ixt :=
    Silmaril.Wasm.Models.V2CoreInstFn.importsTransport_all hd.1.2.1 m cm xas ixt xt xtI xtE hm hcm
      hok hxas
  exact instantiate_behaviours P hs hh hm hx
    (Silmaril.Proofs.Wasm.Models.V2CoreInstDom.segBounded_of_core hcm hC.bounded)

/-! ## A point with a host function -/

theorem hostFnStore_toCore_isSome : (Store.toCore hostFnStore).isSome := rfl

/-- `hostDivPt` is in `v20instHT`'s domain at every profile. -/
theorem hostDivPt_dom (P : Profile) : (v20instHT P).dom hostDivPt := by
  refine ⟨⟨⟨fun i fi h => ?_, fun _ _ h => by simp [hostDivPt, hostFnStore] at h,
    fun _ _ h => by simp [hostDivPt, hostFnStore] at h,
    fun _ _ h => by simp [hostDivPt, hostFnStore] at h⟩,
    hostFnStore_toCore_isSome, Silmaril.Proofs.Wasm.Models.V2CoreInstFn.divV_preserves,
    Silmaril.Proofs.Wasm.Models.V2CoreInstFn.divV_keeps⟩,
    hostEmbV_blind Silmaril.Proofs.Wasm.Models.V2CoreInstFn.divV_blind, ?_⟩
  · have hfi : fi = hostFunc := by
      have hm : fi ∈ hostFnStore.funcs := List.mem_of_getElem? h
      simpa [hostFnStore] using hm
    subst hfi
    intro a ha
    simp [hostFunc, nopModInst] at ha
    simp [ha, hostDivPt, hostFnStore]
  · intro fi hfi
    simp [ptCore, hostDivPt, hostFnStore, Store.toCore, hostFunc, FuncInst.toCore] at hfi
    subst hfi
    simp [ModuleInst.toCore, nopModInst]

/-- The store with a host function is typed. -/
theorem storeOk_hostFnStore : StoreOk hostFnStore := by
  constructor <;> simp [hostFnStore]
  exact .host trivial rfl

/-- **It is not host-free**, so the earlier `domInstP_of_storeOk_any` does not apply to it. -/
theorem not_hostFree_hostFnStore : ¬ HostFree hostFnStore :=
  fun h => h hostFunc (by simp [hostFnStore]) 0 rfl

/-- **`hostDivPt`, a store with a host function, is in `domInstHost P`** at every profile. -/
theorem domInstHost_hostDivPt (P : Profile) : domInstHost P hostDivPt :=
  domInstHost_of_storeOk (hostDivPt_dom P) storeOk_hostFnStore hostOk_divV

end Silmaril.Proofs.Wasm.Models.V2CoreInstHostFn
