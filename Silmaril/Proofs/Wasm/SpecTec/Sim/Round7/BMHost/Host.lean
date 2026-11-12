module

public import Silmaril.Wasm.SpecTec.Sim.Round7.BMHost.Defs
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Round 7, memory SIMD: `msAddHost` is finite and `HostOk`

* `extend_addMS`: `s ⪯ addMS s` (a memory and a function appended).
* `funcInstOk_msFn`: the appended function is valid in `addMS s`: its module instance types the
  appended memory, and its body `unreachable; v128.store` checks (silmaril's `funcCheck`, by
  `decide`).
* `storeOk_addMS`: `addMS` keeps `StoreOk`.
* `msAddHost_finite`, `msAddHost_ok`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.BMHost

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Round5.Pos (dt0 tyOk_dt0)

/-! ## Extension -/

theorem extendMem_refl (a : MemInst) : ExtendMem a a := ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem extend_addMS {s : Store Unit} (hs : StoreOk s) : Extend s (addMS s) :=
  let he := Extend.refl hs
  { tags := he.tags, globals := he.globals
    mems := ExtendsList.of_prefix (List.prefix_append _ _) fun _ _ => extendMem_refl _
    tables := he.tables
    funcs := ExtendsList.of_prefix (List.prefix_append _ _)
      fun _ _ => ⟨rfl, rfl, fun _ h => h, fun _ h => h⟩
    datas := he.datas, elems := he.elems, structs := he.structs, arrays := he.arrays
    exns := he.exns }

theorem immut_addMS {s : Store Unit} {a b : FieldVal}
    (h : ImmutReachable (addMS s) a b) : ImmutReachable s a b := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct hs he hi hfv
  | refArray hs he hfv => exact .refArray hs he hfv
  | refExn hs hv => exact .refExn hs hv
  | refExtern r => exact .refExtern r

/-! ## The appended function -/

/-- The context of `msModule k` in a store whose memory `k` is `mem0`. -/
def msCtx : Context :=
  { types := [dt0], recs := [], tags := [], globals := [], mems := [mem0.type], tables := [],
    funcs := [], datas := [], elems := [], refs := List.range 0 }

theorem mem_addMS (s : Store Unit) : (addMS s).mems[s.mems.length]? = some mem0 := by
  simp [addMS]

theorem moduleInstOk_ms (s : Store Unit) :
    ModuleInstOk (addMS s) (msModule s.mems.length) msCtx :=
  .mk (tags := []) (globals := []) (mems := [mem0.type]) (tables := []) (funcs := [])
    (elems := []) (k := 0)
    (by simp only [msModule, List.mem_singleton]; rintro _ rfl; exact tyOk_dt0)
    .nil .nil .nil (.cons (.mem (mem_addMS s)) .nil) .nil (by simp [msModule]) .nil
    (by simp [msModule]) (by simp [msModule]) (by simp [msModule]) (Nat.zero_le _)

theorem funcOk_ms : FuncOk msCtx ⟨⟨0⟩, [], msBody⟩ dt0 :=
  funcCheck_sound tyOkC_sound' exprC_sound (by decide)

theorem funcInstOk_msFn (s : Store Unit) : FuncInstOk (addMS s) (msFnAt s.mems.length) :=
  .wasm tyOk_dt0 (moduleInstOk_ms s) rfl funcOk_ms (Sub.refl _ (k := .def) trivial _)

/-! ## `StoreOk` and the host contract -/

theorem storeOk_addMS {s : Store Unit} (hs : StoreOk s) : StoreOk (addMS s) :=
  have he := extend_addMS hs
  { tags := hs.tags
    globals := fun gi h => ⟨(hs.globals gi h).1, (hs.globals gi h).2.extend he⟩
    mems := fun mi h => by
      simp only [addMS, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact hs.mems mi h
      · exact ⟨show mem0.type.Valid by decide, rfl⟩
    tables := fun ti h => ⟨(hs.tables ti h).1, (hs.tables ti h).2.1,
      fun r hr => ((hs.tables ti h).2.2 r hr).extend he⟩
    funcs := fun g h => by
      simp only [addMS, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · cases hs.funcs g h with
        | wasm hdt hm hcode hf hsub => exact .wasm hdt (hm.extend hs he) hcode hf hsub
        | host hdt he' hcode => exact .host hdt he' hcode
      · exact funcInstOk_msFn s
    elems := fun ei h => (hs.elems ei h).extend he ⟨rfl, .inl rfl⟩
    structs := fun si h => by
      obtain ⟨fs, hx, hf⟩ := hs.structs si h
      exact ⟨fs, hx, hf.imp fun _ _ h => h.extend he⟩
    arrays := fun ai h => by
      obtain ⟨ft, hx, hf⟩ := hs.arrays ai h
      exact ⟨ft, hx, fun fv hfv => (hf fv hfv).extend he⟩
    exns := fun e h => by
      obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e h
      exact ⟨ti, ts, ht, hx, hf.imp fun _ _ h => h.extend he⟩
    acyclicStructs := fun a ha hr => hs.acyclicStructs a ha (immut_addMS hr)
    acyclicArrays := fun a ha hr => hs.acyclicArrays a ha (immut_addMS hr)
    acyclicExns := fun a ha hr => hs.acyclicExns a ha (immut_addMS hr)
    structsClosed := hs.structsClosed
    arraysClosed := hs.arraysClosed }

/-- **`msAddHost` is finite**: one outcome per call. -/
theorem msAddHost_finite : HostFinite msAddHost :=
  fun _ s _ => ⟨[.returned (addMS s) .trap], fun _ => by simp [msAddHost]⟩

/-- **`msAddHost` meets the host contract.** -/
theorem msAddHost_ok : HostOk msAddHost := by
  intro s _ _ _ _ _ hs _ _ _ _
  refine ⟨⟨_, rfl⟩, fun out ho => ?_⟩
  subst ho
  exact ⟨storeOk_addMS hs, extend_addMS hs, trivial⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.BMHost
