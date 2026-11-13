module

public import Silmaril.Wasm.Models.V2CoreInstImp.Thms

/-!
# Core import typing back to 2.0, at every store

An earlier step transported Core's typing of image addresses back to 2.0 for memories, globals
and tables (`V2CoreInstImp`), and so for every store without functions. This file adds
functions and drops the restriction:

* `func_of_coreAddrOk`: Core's chain of `Externtype_sub` steps over a function address collapses
  (`ExternSub.trans`) to one `Sub` between defined types, from the type of a function instance of
  the image store;
* `funcInst_toCore`: a function instance of the image store is the image of one of `s`, so its
  defined type is the image of a 2.0 function type (`FuncType.toDefType`);
* `funcImport_transport`: between images of 2.0 function types, Core's defined-type subtyping is
  2.0's equality (silmaril-lean's `FuncType.toDefType_sub_iff`), so Core's typing of an image
  function address at an image type is 2.0's;
* `addr_transport`: the same for every kind of address, at the image of every 2.0 external type;
* `importsTransport_all`: `V2CoreInstImp.ImportsTransport p` holds at **every** point whose store
  has a Core image. Core's import types of a module image are the images of the module's 2.0
  import types (`V2Core.Reflect.types_refl`, `imports_refl`), and 2.0 import typing is a function
  of the module.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreInstFn

open Silmaril.Wasm.V2 Silmaril.Wasm.V2.Execution Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Models Silmaril.Wasm.Models.V2Core Silmaril.Wasm.Models.V2CoreSpec
open Silmaril.Wasm.Models.V2CoreInstImp (ImportsTransport memImport_transport globalImport_transport
  tableImport_transport)

variable {H : Type}

/-! ## Function instances of the image store -/

theorem funcs_of_toCore {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (h : Store.toCore s = some cs) : s.funcs.mapM FuncInst.toCore = some cs.funcs := by
  simp only [Store.toCore, Option.map_eq_some_iff] at h
  obtain ⟨fs, hfs, rfl⟩ := h
  exact hfs

theorem funcInst_toCore_type {fi : FuncInst H} {cfi : Silmaril.Wasm.Execution.Core.FuncInst H}
    (h : fi.toCore = some cfi) : cfi.type = fi.type.toDefType := by
  unfold FuncInst.toCore at h
  split at h
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h
    rfl

theorem getElem?_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ {i : Nat} {b : β}, l'[i]? = some b →
      ∃ a, l[i]? = some a ∧ f a = some b
  | [], l', h, i, b, hb => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp at hb
  | a :: l, l', h, i, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b₀, hb₀, l₀, hl₀, rfl⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      exact ⟨a, rfl, hb ▸ hb₀⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hb ⊢
      exact getElem?_mapM hl₀ hb

/-- **A function instance of the image store is the image of one of `s`.** -/
theorem funcInst_toCore {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {a : Nat} {cfi : Silmaril.Wasm.Execution.Core.FuncInst H}
    (h : cs.funcs[a]? = some cfi) : ∃ fi, s.funcs[a]? = some fi ∧ cfi.type = fi.type.toDefType := by
  obtain ⟨fi, hfi, hc⟩ := getElem?_mapM (funcs_of_toCore hcs) h
  exact ⟨fi, hfi, funcInst_toCore_type hc⟩

/-! ## Function addresses -/

/-- **A Core typing of `FUNC a` is a subtype of the instance's type** (the chain collapses). -/
theorem func_of_coreAddrOk {cs : Silmaril.Wasm.Execution.Core.Store H}
    {xa : Silmaril.Wasm.Execution.Core.ExternAddr} {xt : Silmaril.Wasm.Validation.CExternType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa xt) :
    ∀ a, xa = .func a → ∃ cfi, cs.funcs[a]? = some cfi ∧
      (xt = .func cfi.type ∨ Silmaril.Wasm.Validation.ExternTypeOk {} xt) ∧
      Silmaril.Wasm.Validation.ExternSub {} (.func cfi.type) xt := by
  induction h with
  | tag _ => intro a h; cases h
  | global _ => intro a h; cases h
  | mem _ => intro a h; cases h
  | table _ => intro a h; cases h
  | @func a' cfi hcfi =>
    intro a ha
    cases ha
    exact ⟨cfi, hcfi, .inl rfl, Silmaril.Wasm.Validation.ExternSub.refl _ _⟩
  | sub _ hok hs ih =>
    intro a ha
    obtain ⟨cfi, hcfi, hmid, hsub⟩ := ih a ha
    refine ⟨cfi, hcfi, .inr hok, ?_⟩
    rcases hmid with rfl | hmok
    · exact hs
    · exact Silmaril.Wasm.Validation.ExternSub.trans
        Silmaril.Wasm.Validation.TypeCtx.ok_empty hmok hsub hs

/-- Core's `Externtype_sub` between the images of two 2.0 function types is equality. -/
theorem funcSub_toC {f₀ f : FuncType}
    (h : Silmaril.Wasm.Validation.ExternSub {} (.func f₀.toDefType) (.func f.toDefType)) :
    f₀ = f := by
  cases h with
  | func hs => exact (FuncType.toDefType_sub_iff {} f₀ f).1 hs

/-- **A function import Core types at an image address is typed by 2.0 there.** -/
theorem funcImport_transport {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {a : Nat} {ft : FuncType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs (.func a) (.func ft.toDefType)) :
    ExternAddrOk s (.func a) (.func ft) := by
  obtain ⟨cfi, hcfi, -, hsub⟩ := func_of_coreAddrOk h a rfl
  obtain ⟨fi, hfi, hty⟩ := funcInst_toCore hcs hcfi
  rw [hty] at hsub
  have e : fi.type = ft := funcSub_toC hsub
  exact e ▸ .func hfi

/-! ## Every kind of address -/

/-- The kind of a Core external address: `0` function, `1` global, `2` table, `3` memory,
`4` tag. -/
def addrKind : Silmaril.Wasm.Execution.Core.ExternAddr → Nat
  | .func _ => 0
  | .global _ => 1
  | .table _ => 2
  | .mem _ => 3
  | .tag _ => 4

/-- The kind of a Core external type, numbered as `addrKind`. -/
def typeKind : Silmaril.Wasm.Validation.CExternType → Nat
  | .func _ => 0
  | .global _ => 1
  | .table _ => 2
  | .mem _ => 3
  | .tag _ => 4

/-- Core's external address typing relates an address and a type of one kind. -/
theorem kind_of_coreAddrOk {cs : Silmaril.Wasm.Execution.Core.Store H}
    {xa : Silmaril.Wasm.Execution.Core.ExternAddr} {xt : Silmaril.Wasm.Validation.CExternType}
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa xt) : addrKind xa = typeKind xt := by
  induction h with
  | tag _ => rfl
  | global _ => rfl
  | mem _ => rfl
  | table _ => rfl
  | func _ => rfl
  | sub _ _ hs ih => rw [ih]; cases hs <;> rfl

/-- **Core's typing of an image address at the image of a 2.0 external type is 2.0's typing.** -/
theorem addr_transport {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {xa : ExternAddr} {it : ExternType} (hok : ExternType.Ok it)
    (h : Silmaril.Wasm.Execution.Core.ExternAddrOk cs xa.toCore it.toCore) :
    ExternAddrOk s xa it := by
  have hk := kind_of_coreAddrOk h
  cases xa with
  | func a =>
    cases it with
    | func ft => exact funcImport_transport hcs h
    | _ => simp [ExternAddr.toCore, ExternType.toCore, addrKind, typeKind] at hk
  | global a =>
    cases it with
    | global g => exact globalImport_transport hcs h
    | _ => simp [ExternAddr.toCore, ExternType.toCore, addrKind, typeKind] at hk
  | table a =>
    cases it with
    | table t => exact tableImport_transport hcs hok h
    | _ => simp [ExternAddr.toCore, ExternType.toCore, addrKind, typeKind] at hk
  | mem a =>
    cases it with
    | memory mt => exact memImport_transport hcs hok h
    | _ => simp [ExternAddr.toCore, ExternType.toCore, addrKind, typeKind] at hk

/-! ## Whole import lists -/

theorem types_of_toCore {m : Module} {cm : Silmaril.Wasm.Module}
    (hcm : Module.toCore m = some cm) : cm.types = m.types.map FuncType.toCoreRec := by
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcm
  obtain ⟨_, _, _, _, _, _, _, _, hcm⟩ := hcm
  subst hcm
  rfl

/-- 2.0's `Type_ok` is the identity on the types it accepts. -/
theorem types_eq_of_typeOk : ∀ {ts ft' : List FuncType}, List.Forall₂ TypeOk ts ft' → ft' = ts
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hs => by rw [h.1, types_eq_of_typeOk hs]

/-- 2.0 import typing is a function of the import. -/
theorem importOk_det {C : Context} :
    ∀ {is : List Import} {xs ys : List ExternType}, List.Forall₂ (ImportOk C) is xs →
      List.Forall₂ (ImportOk C) is ys → xs = ys
  | [], [], [], .nil, .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h hs, .cons h' hs' => by
    have e := h.1.symm.trans h'.1
    rw [Option.some.inj e, importOk_det hs hs']

/-- The address step of `importsTransport_all`, along the import list. -/
theorem addrs_transport {s : Store H} {cs : Silmaril.Wasm.Execution.Core.Store H}
    (hcs : Store.toCore s = some cs) {C : Context} :
    ∀ {is : List Import} {ixt : List ExternType} {xas : List ExternAddr},
      List.Forall₂ (ImportOk C) is ixt →
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk cs) (xas.map ExternAddr.toCore)
        (ixt.map ExternType.toCore) →
      List.Forall₂ (ExternAddrOk s) xas ixt
  | [], [], [], .nil, _ => .nil
  | [], [], _ :: _, .nil, ha => by cases ha
  | _ :: _, _ :: _, [], .cons _ _, ha => by cases ha
  | _ :: _, _ :: _, _ :: _, .cons hi his, .cons ha has =>
    .cons (addr_transport hcs hi.2 ha) (addrs_transport hcs his has)

/-- **Import typing transports at every point whose store has a Core image**, functions
included. -/
theorem importsTransport_all {p : Pt Nat} (hd : (Store.toCore p.1).isSome) :
    ImportsTransport p := by
  intro m cm xas ixt xt xtI xtE hm hcm hcok hxas
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 hd
  have hp : (ptCore p).1 = cs := by simp [ptCore, hcs]
  rw [hp] at hxas
  cases hm with
  | mk htypes himports =>
    cases hcok with
    | mk htypesC himportsC =>
      rw [types_of_toCore hcm] at htypesC
      rw [Silmaril.Proofs.Wasm.Models.V2Core.Reflect.types_refl htypesC,
        Silmaril.Proofs.Wasm.Models.V2CoreInstDom.imports_of_toCore hcm] at himportsC
      obtain ⟨ixt', hi', rfl⟩ := Silmaril.Proofs.Wasm.Models.V2Core.Reflect.imports_refl himportsC
      rw [types_eq_of_typeOk htypes] at himports
      rw [importOk_det himports hi']
      exact addrs_transport hcs hi' hxas

end Silmaril.Proofs.Wasm.Models.V2CoreInstFn
