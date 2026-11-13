module

public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping
public import Silmaril.Proofs.Wasm.Game.Strategy.Basic

/-!
# Static linking: Retype

Original module documentation:

# Store typing only reads function types (M3, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3. Store typing
(`StoreOk`) reads stored functions only through their types and module instances, except for
the function instances themselves. Replacing the code of some functions by host code, keeping
their types (which expand to function types) and their module instances, keeps the store
typed (`storeOk_recode`). This types the consumer's store with host stubs
(`Linking.Setup.consumerI`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Linking

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- `t` is `s` with the code of some functions replaced by host code; types and module
instances are kept. -/
structure Recoded (s t : Store H) : Prop where
  tags : t.tags = s.tags
  globals : t.globals = s.globals
  mems : t.mems = s.mems
  tables : t.tables = s.tables
  datas : t.datas = s.datas
  elems : t.elems = s.elems
  structs : t.structs = s.structs
  arrays : t.arrays = s.arrays
  exns : t.exns = s.exns
  funcs : List.Forall₂ (fun fi fi' : FuncInst H => fi'.type = fi.type ∧ fi'.module = fi.module ∧
    (fi'.code = fi.code ∨ ∃ h, fi'.code = .host h ∧ ∃ ps rs, Expand fi.type (.func ps rs)))
    s.funcs t.funcs

private theorem forall₂_lookup {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

namespace Recoded

variable {s t : Store H}

theorem func_lookup (h : Recoded s t) {a : Nat} {fi : FuncInst H} (hf : s.funcs[a]? = some fi) :
    ∃ fi', t.funcs[a]? = some fi' ∧ fi'.type = fi.type :=
  let ⟨fi', h₁, h₂⟩ := forall₂_lookup h.funcs hf
  ⟨fi', h₁, h₂.1⟩

theorem refOk (h : Recoded s t) {r : Ref} {rt : CRefType} (hr : RefOk s r rt) : RefOk t r rt := by
  induction hr with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct hs => exact .struct (h.structs ▸ hs)
  | array hs => exact .array (h.arrays ▸ hs)
  | func hf =>
    obtain ⟨fi', ht, he⟩ := h.func_lookup hf
    rw [← he]
    exact .func ht
  | exn hs => exact .exn (h.exns ▸ hs)
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem valOk (h : Recoded s t) {v : Val} {vt : CValType} (hv : ValOk s v vt) : ValOk t v vt := by
  cases hv with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref hr => exact .ref (h.refOk hr)

theorem fieldValOk (h : Recoded s t) {v : FieldVal} {st : CStorageType}
    (hv : FieldValOk s v st) : FieldValOk t v st := by
  cases hv with
  | val hv => exact .val (h.valOk hv)
  | pack p b => exact .pack p b

theorem externAddrOk (h : Recoded s t) {xa : ExternAddr} {xt : CExternType}
    (hx : ExternAddrOk s xa xt) : ExternAddrOk t xa xt := by
  induction hx with
  | tag hh => exact .tag (h.tags ▸ hh)
  | global hh => exact .global (h.globals ▸ hh)
  | mem hh => exact .mem (h.mems ▸ hh)
  | table hh => exact .table (h.tables ▸ hh)
  | func hf =>
    obtain ⟨fi', ht, he⟩ := h.func_lookup hf
    rw [← he]
    exact .func ht
  | sub _ hok hs ih => exact .sub ih hok hs

theorem elemInstOk (h : Recoded s t) {ei : ElemInst} (he : ElemInstOk s ei) :
    ElemInstOk t ei :=
  ⟨he.1, fun r hr => h.refOk (he.2 r hr)⟩

theorem tableInstOk (h : Recoded s t) {ti : TableInst} (he : TableInstOk s ti) :
    TableInstOk t ti :=
  ⟨he.1, he.2.1, fun r hr => h.refOk (he.2.2 r hr)⟩

theorem moduleInstOk (h : Recoded s t) {mi : ModuleInst} {C : Context}
    (hm : ModuleInstOk s mi C) : ModuleInstOk t mi C := by
  cases hm with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems hexports hdisjoint
      hexportAddrs hk =>
    refine .mk htypes (htags.imp fun _ _ hh => h.externAddrOk hh)
      (hglobals.imp fun _ _ hh => h.externAddrOk hh)
      (hfuncs.imp fun _ _ hh => h.externAddrOk hh)
      (hmems.imp fun _ _ hh => h.externAddrOk hh)
      (htables.imp fun _ _ hh => h.externAddrOk hh)
      (fun a ha => h.datas ▸ hdatas a ha) (helems.imp fun _ _ hh => ?_) (fun xi hxi => ?_)
      hdisjoint hexportAddrs hk
    · obtain ⟨ei, hei, hok, rfl⟩ := hh
      exact ⟨ei, h.elems ▸ hei, h.elemInstOk hok, rfl⟩
    · obtain ⟨xt, hxt⟩ := hexports xi hxi
      exact ⟨xt, h.externAddrOk hxt⟩

end Recoded

/-- **Store typing survives recoding** functions as host functions of the same type. -/
theorem storeOk_recode {s t : Store H} (hs : StoreOk s) (h : Recoded s t) : StoreOk t where
  tags ti hti := hs.tags ti (h.tags ▸ hti)
  globals gi hgi := by
    obtain ⟨h₁, h₂⟩ := hs.globals gi (h.globals ▸ hgi)
    exact ⟨h₁, h.valOk h₂⟩
  mems mi hmi := hs.mems mi (h.mems ▸ hmi)
  tables ti hti := h.tableInstOk (hs.tables ti (h.tables ▸ hti))
  funcs fi' hfi' := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hfi'
    obtain ⟨fi, hfi, hrel⟩ := forall₂_lookup h.funcs.flip hi
    obtain ⟨hty, hmod, hcode⟩ := hrel
    have hok := hs.funcs fi (List.mem_of_getElem? hfi)
    rcases hcode with hcode | ⟨hh, hcode, ps, rs, hexp⟩
    · cases hok with
      | wasm hdt hm hc hf hsub =>
        exact .wasm (hty ▸ hdt) (hmod ▸ h.moduleInstOk hm) (hcode.trans hc) hf (hty ▸ hsub)
      | host hdt he' hc => exact .host (hty ▸ hdt) (hty ▸ he') (hcode.trans hc)
    · have hdt : TyOk {} fi.type := by
        cases hok with
        | wasm hdt => exact hdt
        | host hdt => exact hdt
      exact .host (hty ▸ hdt) (hty ▸ hexp) hcode
  elems ei hei := h.elemInstOk (hs.elems ei (h.elems ▸ hei))
  structs si hsi := by
    obtain ⟨fs, hx, hf⟩ := hs.structs si (h.structs ▸ hsi)
    exact ⟨fs, hx, hf.imp fun _ _ hh => h.fieldValOk hh⟩
  arrays ai hai := by
    obtain ⟨ft, hx, hf⟩ := hs.arrays ai (h.arrays ▸ hai)
    exact ⟨ft, hx, fun fv hfv => h.fieldValOk (hf fv hfv)⟩
  exns e he := by
    obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e (h.exns ▸ he)
    exact ⟨ti, ts, h.tags ▸ ht, hx, hf.imp fun _ _ hh => h.valOk hh⟩
  acyclicStructs a ha hr := hs.acyclicStructs a (h.structs ▸ ha)
    (TM.immutReachable_transfer h.structs h.arrays h.exns hr)
  acyclicArrays a ha hr := hs.acyclicArrays a (h.arrays ▸ ha)
    (TM.immutReachable_transfer h.structs h.arrays h.exns hr)
  acyclicExns a ha hr := hs.acyclicExns a (h.exns ▸ ha)
    (TM.immutReachable_transfer h.structs h.arrays h.exns hr)
  structsClosed si hsi := hs.structsClosed si (h.structs ▸ hsi)
  arraysClosed ai hai := hs.arraysClosed ai (h.arrays ▸ hai)

end Silmaril.Proofs.Wasm.Game.Linking
