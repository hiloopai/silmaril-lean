module

public import Silmaril.Wasm.JcoTool.KCoreHost.Defs
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff

/-!
# Instantiation of the emitted modules exists on the host store

`instantiate?_some`: silmaril's computable instantiation `instantiate? evalConst?` of
`{ KCoreEmit.toModule P name with imports := is }` (any program `P`, any import list) succeeds on
every store with eight imported functions: the nine constant globals evaluate in place
(`evalGlobals_c32`), there are no tables, segments or start function, and the allocation finds
every type and export index (`alloc_some`, by computation).

`imports_xt`, `addrs_ok`: when the module is valid (`ModuleOk`), the extern types of its imports are
the closed types of `KCoreEmit.types` that `KCoreHost.hostDT` gives the host store's functions, so
the host store's addresses match them (`ExternAddrOk`). With silmaril's `instantiate?_iff`:
`inst_exists`, **a valid emitted module has a Core 3.0 instantiation on the host store**.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreHost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCore (BI Prog)
open Silmaril.Wasm.JcoTool.KCoreHost
open Silmaril.Wasm.JcoTool.KCoreEmit (c32 toModule)

variable {H : Type}

theorem evalConst_c32 (s : Store H) (f : Frame) (n : Nat) :
    evalConst? s f [c32 n] = some (s, Val.i32 (BitVec.ofNat 32 n)) := rfl

/-- Constant `i32` initializers evaluate in place. -/
theorem evalGlobals_c32 : ∀ (s : Store H) (f : Frame) (gs : List CGlobalType) (ns : List Nat),
    gs.length = ns.length → ∃ r, evalGlobals? evalConst? s f gs (ns.map fun n => [c32 n]) = some r
  | _, _, [], [], _ => ⟨_, rfl⟩
  | s, f, g :: gs, n :: ns, h => by
    obtain ⟨r, hr⟩ := evalGlobals_c32 (allocGlobal s g (Val.i32 (BitVec.ofNat 32 n))).1
      { f with module := { f.module with
        globals := f.module.globals ++ [(allocGlobal s g (Val.i32 (BitVec.ofNat 32 n))).2] } }
      gs ns (by simpa using h)
    exact ⟨(r.1, r.2.1, Val.i32 (BitVec.ofNat 32 n) :: r.2.2),
      by simp only [List.map_cons, evalGlobals?, evalConst_c32, hr]⟩
  | _, _, [], _ :: _, h => by simp at h
  | _, _, _ :: _, [], h => by simp at h

/-- The allocation of the emitted module succeeds (by computation; the code is not inspected). -/
theorem alloc_some (P : Prog) (name : String) (is : List Import) (s₃ : Store H) (vs : List Val) :
    (allocModule? s₃ { toModule P name with imports := is } (hostAddrs.map .func) vs [] []).isSome := rfl

/-- `instantiate?` succeeds on a module with constant `i32` globals, no tables or segments, whose
allocation succeeds. -/
theorem instantiate?_some_of (m : Module) (s : Store H) (xas : List ExternAddr) (ns : List Nat)
    (hgl : m.globals.map Global.init = ns.map fun n => [c32 n]) (hlen : m.globals.length = ns.length)
    (ht : m.tables = []) (he : m.elems = []) (hd : m.data = [])
    (ha : ∀ (s₃ : Store H) (vs : List Val), (allocModule? s₃ m xas vs [] []).isSome) :
    (instantiate? evalConst? s m xas).isSome := by
  obtain ⟨⟨s₁, f₁, vs⟩, hg⟩ := evalGlobals_c32 s ⟨[], ModuleInst.initial s m xas⟩
    (m.globals.map fun g => ⟨g.type.mutability, (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
    ns (by simpa using hlen)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (ha s₁ vs)
  unfold instantiate?
  rw [hgl, hg]
  simp [ht, he, hd, evalExprs?, evalExprss?, hr]

/-- **Silmaril's computable instantiation of the emitted module succeeds** on every store, with
the eight imported functions at `hostAddrs`. -/
theorem instantiate?_some (P : Prog) (name : String) (is : List Import) (s : Store H) :
    (instantiate? evalConst? s { toModule P name with imports := is } (hostAddrs.map .func)).isSome :=
  instantiate?_some_of _ s _ ((List.range 9).map P.g0) (by simp only [toModule, List.map_map]; rfl)
    (by simp [toModule]) rfl rfl rfl fun s₃ vs => alloc_some P name is s₃ vs

/-- The closed types `$alloctypes` gives `KCoreEmit.types` (by computation). -/
theorem allocTypes_types : allocTypes Silmaril.Wasm.JcoTool.KCoreEmit.types =
    Silmaril.Wasm.JcoTool.KCoreEmit.types.map fun rt => .defn (liftRec rt) 0 := rfl

/-- **The extern types of the stream modules' imports** are those of the host store's functions. -/
theorem imports_xt {name : String} {xtI : List CExternType}
    (h : List.Forall₂ (ImportOk { types := allocTypes Silmaril.Wasm.JcoTool.KCoreEmit.types })
      (Silmaril.Wasm.JcoTool.KCoreEmit.imports name) xtI) :
    xtI = bis.map fun b => .func (hostDT b) := by
  rcases h with _ | ⟨h0, h⟩; rcases h with _ | ⟨h1, h⟩; rcases h with _ | ⟨h2, h⟩
  rcases h with _ | ⟨h3, h⟩; rcases h with _ | ⟨h4, h⟩; rcases h with _ | ⟨h5, h⟩
  rcases h with _ | ⟨h6, h⟩; rcases h with _ | ⟨h7, h⟩; rcases h with _ | ⟨_, _⟩
  have e : ∀ {x y : Option CExternType} {z : CExternType}, x = some z → x = y → y = some z :=
    fun h1 h2 => h2 ▸ h1
  simp only [bis, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact ⟨(Option.some.inj (e h0.1 rfl)).symm, (Option.some.inj (e h1.1 rfl)).symm,
    (Option.some.inj (e h2.1 rfl)).symm, (Option.some.inj (e h3.1 rfl)).symm,
    (Option.some.inj (e h4.1 rfl)).symm, (Option.some.inj (e h5.1 rfl)).symm,
    (Option.some.inj (e h6.1 rfl)).symm, (Option.some.inj (e h7.1 rfl)).symm⟩

theorem addr_ok (hb : BI → H) (i : Nat) (b : BI)
    (h : (hostStore hb).funcs[i]? = some ⟨hostDT b, {}, .host (hb b)⟩) :
    ExternAddrOk (hostStore hb) (.func i) (.func (hostDT b)) := .func h

/-- The host store's addresses have the host functions' types. -/
theorem addrs_ok (hb : BI → H) :
    List.Forall₂ (ExternAddrOk (hostStore hb)) (hostAddrs.map .func) (bis.map fun b => .func (hostDT b)) :=
  .cons (addr_ok hb 0 .taskReturn rfl) <| .cons (addr_ok hb 1 .streamNew rfl) <|
    .cons (addr_ok hb 2 .streamRead rfl) <| .cons (addr_ok hb 3 .streamWrite rfl) <|
    .cons (addr_ok hb 4 .dropR rfl) <| .cons (addr_ok hb 5 .dropW rfl) <|
    .cons (addr_ok hb 6 .wsNew rfl) <| .cons (addr_ok hb 7 .join rfl) .nil

/-- **A valid emitted module has a Core 3.0 instantiation on the host store.** -/
theorem inst_exists {Pf : Profile} {host : HostSemantics H} (hb : BI → H) (P : Prog) (name : String)
    (hv : ModuleValid (toModule P name)) :
    ∃ c, Instantiate Pf host (hostStore hb) (toModule P name) (hostAddrs.map .func) c := by
  obtain ⟨⟨xtI, xtE⟩, hok⟩ := hv
  have hvalid : ∃ xtE xtI, ModuleOk (toModule P name) ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk (hostStore hb)) (hostAddrs.map .func) xtI := by
    refine ⟨xtE, xtI, hok, ?_⟩
    obtain ⟨htypes, himports, -⟩ := hok
    rw [← allocTypes_eq htypes] at himports
    rw [imports_xt himports]
    exact addrs_ok hb
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (instantiate?_some P name (toModule P name).imports (hostStore hb))
  exact ⟨c, (instantiate?_iff hvalid).1 hc⟩

end Silmaril.Proofs.Wasm.JcoTool.KCoreHost
