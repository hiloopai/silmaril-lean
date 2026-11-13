module

public import Silmaril.Proofs.Wasm.Component.FXRefV.Map
public import Silmaril.Proofs.Wasm.Component.FXRefE.Facts
public import Silmaril.Wasm.Component.FXRefV.Defs
public import Silmaril.Wasm.Component.EngineRef.Defs

/-!
# Instantiating a module with FX functions in the WasmFX engine with suspension

For a component `c : SimpleFX` whose Core part is instantiated as the IR assumes, `fxEV P`
instantiates `c.ofCore c.core.mod` (the Core module with the FX functions `c.fxs`) in the empty
store at every host type `H`:

* the Core part as Core 3.0 does (`instantiateOnce?`, store `cs₁`, frame `f'`), then the FX
  functions at addresses `|cs₁.funcs| + j` (`allocFX_getElem?`), with FX code only
  (`allocFX_SM`);
* export `k` of the IR module is found by name (`lookup_k`): a Core export at
  `I.addrs.getD k 0` (Core export names are not FX names), an FX export `j` at
  `|cs₁.funcs| + j` (FX names are distinct);
* `instFacts_fxV`: **the instantiation facts** (`EngineRef.InstFacts`) of `fxEV P`;
* `instOf_fxV`: the engine instance used by the specification (host type `Nat`) has the store
  `SM g cs` (the machine's store renamed) and the same export addresses;
* `hostFree_cs`: the instantiated store has no component host functions.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXRefV

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.EngineRef
open Silmaril.Wasm.Component.FXRefV
open Silmaril.Proofs.Wasm.Component.Reference (inst_once lookup_funcExport instantiateOnce?_mapH
  empty_mapH Store.mapH FuncInst.mapH FuncCode.mapH instantiateOnce?_exports allocExports_names
  mapS)
open Silmaril.Proofs.Wasm.Component.FXRefE (prepare_core3 importTypes_fx mapM_some mapM_getElem?)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component.Runtime (CanonHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H H' : Type} {P : Profile}

/-! ## Lists -/

theorem lookup_append_some {α : Type} {a : String} {v : α} :
    ∀ {l₁ : List (String × α)} (l₂ : List (String × α)), l₁.lookup a = some v →
      (l₁ ++ l₂).lookup a = some v
  | [], _, h => by simp at h
  | (b, w) :: l₁, l₂, h => by
    rw [List.cons_append, List.lookup_cons]
    rw [List.lookup_cons] at h
    split at h
    · exact h
    · exact lookup_append_some l₂ h

theorem lookup_append_none {α : Type} {a : String} :
    ∀ {l₁ : List (String × α)} (l₂ : List (String × α)), a ∉ l₁.map (·.1) →
      (l₁ ++ l₂).lookup a = l₂.lookup a
  | [], _, _ => rfl
  | (b, w) :: l₁, l₂, h => by
    have hne : a ≠ b := fun e => h (e ▸ List.mem_cons_self)
    have hbeq : (a == b) = false := by simpa only [beq_eq_false_iff_ne] using hne
    rw [List.cons_append, List.lookup_cons, hbeq]
    exact lookup_append_none l₂ fun hm => h (List.mem_cons_of_mem _ hm)

theorem lookup_of_nodup {α : Type} :
    ∀ {L : List (String × α)} {j : Nat} {a : String} {v : α}, (L.map (·.1)).Nodup →
      L[j]? = some (a, v) → L.lookup a = some v
  | [], _, _, _, _, h => by simp at h
  | (b, w) :: L, j, a, v, hnd, h => by
    have hnd' := List.nodup_cons.1 hnd
    cases j with
    | zero =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp
    | succ j =>
      have hm : a ∈ L.map (·.1) := List.mem_map.2 ⟨(a, v), List.mem_of_getElem? h, rfl⟩
      have hne : a ≠ b := fun e => hnd'.1 (e ▸ hm)
      have hbeq : (a == b) = false := by simpa only [beq_eq_false_iff_ne] using hne
      rw [List.lookup_cons, hbeq]
      exact lookup_of_nodup hnd'.2 h

/-! ## FX function allocation -/

theorem allocHost_SM (g : H → H') (s : Store (FXCode H)) (ft : V1.FuncType)
    (F : Silmaril.Wasm.Models.FX.FuncFX) :
    SingleThreaded.allocHost (SM g s) ft (FXCode.fx F) =
      (SM g (SingleThreaded.allocHost s ft (FXCode.fx F)).1,
        (SingleThreaded.allocHost s ft (FXCode.fx F)).2) := by
  simp [SingleThreaded.allocHost, allocFunc, Store.mapH, FuncInst.mapH, FuncCode.mapH, mapC]

/-- **Allocating FX functions commutes with renaming.** -/
theorem allocFX_SM (g : H → H') (inst : ModuleInst) :
    ∀ (s : Store (FXCode H)) (ds : List FXDecl),
      allocFX inst (SM g s) ds = (SM g (allocFX inst s ds).1, (allocFX inst s ds).2)
  | _, [] => rfl
  | s, d :: ds => by
    simp only [allocFX]
    rw [allocHost_SM, allocFX_SM g inst _ ds]

theorem allocHost_length (s : Store (FXCode H)) (ft : V1.FuncType) (c : FXCode H) :
    (SingleThreaded.allocHost s ft c).2 = s.funcs.length ∧
      (SingleThreaded.allocHost s ft c).1.funcs.length = s.funcs.length + 1 := by
  simp [SingleThreaded.allocHost, allocFunc]

/-- The FX exports of `allocFX`: FX function `j` at address `|s.funcs| + j`. -/
theorem allocFX_getElem? (inst : ModuleInst) :
    ∀ (s : Store (FXCode H)) (ds : List FXDecl) {j : Nat} {d : FXDecl}, ds[j]? = some d →
      (allocFX inst s ds).2[j]? = some (d.name, .func (s.funcs.length + j))
  | _, [], _, _, h => by simp at h
  | s, d₀ :: ds, j, d, h => by
    obtain ⟨ha, hl⟩ := allocHost_length s d₀.type (.fx (d₀.func inst))
    cases j with
    | zero =>
      cases Option.some.inj h
      simp only [allocFX, List.getElem?_cons_zero, ha, Nat.add_zero]
    | succ j =>
      simp only [allocFX, List.getElem?_cons_succ]
      rw [allocFX_getElem? inst _ ds h, hl]
      congr 3
      omega

theorem allocFX_names (inst : ModuleInst) :
    ∀ (s : Store (FXCode H)) (ds : List FXDecl), (allocFX inst s ds).2.map (·.1) = ds.map (·.name)
  | _, [] => rfl
  | s, d :: ds => by
    simp only [allocFX, List.map_cons]
    rw [allocFX_names inst _ ds]

/-! ## Export lookup -/

/-- The FX instance of `c` given the Core frame `f'` and the Core store `cs₁`. -/
def ciOf (c : SimpleFX) (f' : Frame) (cs₁ : Store (FXCode H)) : InstFX :=
  ⟨f'.module, (allocFX (fxInst f'.module cs₁.funcs.length c.fxs.length) cs₁ c.fxs).2⟩

/-- The store of `c`'s instance given the Core frame `f'` and the Core store `cs₁`. -/
def csOf (c : SimpleFX) (f' : Frame) (cs₁ : Store (FXCode H)) : Store (FXCode H) :=
  (allocFX (fxInst f'.module cs₁.funcs.length c.fxs.length) cs₁ c.fxs).1

/-- The address of export `k` of `c`'s IR module. -/
def addrOf (c : SimpleFX) (Ia : List Nat) (n : Nat) (k : Nat) : Nat :=
  if k < c.core.exports.length then Ia.getD k 0 else n + (k - c.core.exports.length)

theorem ciOf_SM (g : H → H') (c : SimpleFX) (f' : Frame) (cs₁ : Store (FXCode H)) :
    ciOf c f' (SM g cs₁) = ciOf c f' cs₁ := by
  unfold ciOf
  rw [show (SM g cs₁).funcs.length = cs₁.funcs.length from List.length_map _, allocFX_SM]

theorem csOf_SM (g : H → H') (c : SimpleFX) (f' : Frame) (cs₁ : Store (FXCode H)) :
    csOf c f' (SM g cs₁) = SM g (csOf c f' cs₁) := by
  unfold csOf
  rw [show (SM g cs₁).funcs.length = cs₁.funcs.length from List.length_map _, allocFX_SM]

/-- A Core export of the IR module is found by name in the Core part of the FX instance. -/
theorem lookup_core {c : SimpleFX} (hi : c.Inst) {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} {cs₁ : Store (FXCode H)}
    (hv : Validation.validate? c.core.mod = some mt)
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.core.mod [] = some (cs₁, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) {k : Nat}
    {p : String × CoreFuncTy} (hk : c.mod.exports[k]? = some p)
    (hlt : k < c.core.exports.length) :
    (Silmaril.Wasm.Component.Engine.Core3.instExports f'.module ++ (ciOf c f' cs₁).fx).lookup p.1 =
      (some (.func (I.addrs.getD k 0)) : Option ExternAddr) := by
  have hk' : c.core.exports[k]? = some p :=
    (List.getElem?_append_left hlt).symm.trans hk
  have hl : (Silmaril.Wasm.Component.Engine.Core3.instExports f'.module).lookup p.1 =
      some (.func (I.addrs.getD k 0)) :=
    lookup_funcExport (c := c.coreSimple) hi.core hv ho ha (n := p.1) (ft := p.2) hk'
  exact lookup_append_some _ hl

/-- An FX name is not an export name of the Core instance. -/
theorem fx_not_core {c : SimpleFX} (hi : c.Inst) {f' : Frame} {cs₁ : Store (FXCode H)}
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.core.mod [] = some (cs₁, f', none))
    {d : FXDecl} (hd : d ∈ c.fxs) :
    d.name ∉ (Silmaril.Wasm.Component.Engine.Core3.instExports f'.module).map (·.1) := by
  obtain ⟨ei, hX⟩ := instantiateOnce?_exports ho
  have hnames : f'.module.exports.map (·.name) = c.core.mod.exports.map (·.name) :=
    (allocExports_names hX).1
  have heq : (Silmaril.Wasm.Component.Engine.Core3.instExports f'.module).map (·.1) =
      f'.module.exports.map (·.name) := by
    simp [Silmaril.Wasm.Component.Engine.Core3.instExports, List.map_map, Function.comp_def]
  rw [heq, hnames]
  exact hi.fresh d hd

/-- An FX export of the IR module is found by name in the FX part of the FX instance. -/
theorem lookup_fxpart {c : SimpleFX} (hi : c.Inst) {f' : Frame} {cs₁ : Store (FXCode H)}
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.core.mod [] = some (cs₁, f', none))
    {j : Nat} {d : FXDecl} (hd : c.fxs[j]? = some d) :
    (Silmaril.Wasm.Component.Engine.Core3.instExports f'.module ++ (ciOf c f' cs₁).fx).lookup
        d.name = (some (.func (cs₁.funcs.length + j)) : Option ExternAddr) := by
  have hnd : ((allocFX (fxInst f'.module cs₁.funcs.length c.fxs.length) cs₁ c.fxs).2.map
      (·.1)).Nodup := by
    rw [allocFX_names]
    exact hi.nodup
  rw [lookup_append_none _ (fx_not_core hi ho (List.mem_of_getElem? hd))]
  exact lookup_of_nodup hnd (allocFX_getElem? _ cs₁ c.fxs hd)

/-- **Export `k` of the IR module is found by name in the FX instance.** -/
theorem lookup_k {c : SimpleFX} (hi : c.Inst) {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} {cs₁ : Store (FXCode H)}
    (hv : Validation.validate? c.core.mod = some mt)
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.core.mod [] = some (cs₁, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) {k : Nat}
    {p : String × CoreFuncTy} (hk : c.mod.exports[k]? = some p) :
    (Silmaril.Wasm.Component.Engine.Core3.instExports f'.module ++ (ciOf c f' cs₁).fx).lookup p.1 =
      (some (.func (addrOf c I.addrs cs₁.funcs.length k)) : Option ExternAddr) := by
  by_cases hlt : k < c.core.exports.length
  · have ha' : addrOf c I.addrs cs₁.funcs.length k = I.addrs.getD k 0 := by
      simp only [addrOf, hlt, ↓reduceIte]
    rw [ha']
    exact lookup_core hi hv ho ha hk hlt
  · have ha' : addrOf c I.addrs cs₁.funcs.length k =
        cs₁.funcs.length + (k - c.core.exports.length) := by
      simp only [addrOf, hlt, ↓reduceIte]
    have hk' : (c.fxs[k - c.core.exports.length]?).map
        (fun d => (d.name, (⟨d.type.params, d.type.results⟩ : CoreFuncTy))) = some p := by
      rw [← List.getElem?_map, ← hk]
      exact (List.getElem?_append_right (Nat.le_of_not_lt hlt)).symm
    obtain ⟨d, hd, hdp⟩ := Option.map_eq_some_iff.1 hk'
    rw [ha', ← hdp]
    exact lookup_fxpart hi ho hd

/-! ## Instantiation -/

/-- `prepare?` of `fxEV P` on the module of `c`. -/
theorem prepare_fxV {c : SimpleFX} {mt : Validation.CModuleType} {f' : Frame}
    {cs₁ : Store (FXCode H)} (hv : Validation.validate? c.core.mod = some mt)
    (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.core.mod [] = some (cs₁, f', none)) :
    (fxEV P).prepare? ((fxEV P).empty H) (c.ofCore c.core.mod) [] =
      some (csOf c f' cs₁, ciOf c f' cs₁, none) := by
  show prepareFXV? ({} : Store (FXCode H)) ⟨c.core.mod, c.fxs⟩ [] = _
  unfold prepareFXV?
  rw [show (⟨c.core.mod, c.fxs⟩ : ModuleFX).core = c.core.mod from rfl, prepare_core3 hv hmt ho]
  rfl

/-- The instantiation of the Core part in a renamed empty store. -/
theorem instantiate_SM (g : H → H') {m : Module} {cs₁ : Store (FXCode H)} {f' : Frame}
    (ho : instantiateOnce? ({} : Store (FXCode H)) m [] = some (cs₁, f', none)) :
    instantiateOnce? ({} : Store (FXCode H')) m [] = some (SM g cs₁, f', none) := by
  have e := instantiateOnce?_mapH (mapC g) ({} : Store (FXCode H)) m []
  rw [empty_mapH, ho] at e
  exact e

/-- **The instantiated store has no component host functions.** -/
theorem hostFree_cs {c : SimpleFX} {m : Module} {cs₁ : Store (FXCode H)} {f' : Frame}
    (ho : instantiateOnce? ({} : Store (FXCode H)) m [] = some (cs₁, f', none)) :
    HostFree (csOf c f' cs₁) := by
  apply hostFree_of_SM_eq
  rw [← csOf_SM, ← csOf_SM]
  have e₁ := instantiate_SM (fun _ : H => true) ho
  have e₂ := instantiate_SM (fun _ : H => false) ho
  rw [e₁] at e₂
  obtain ⟨h, -⟩ := Prod.mk.inj (Option.some.inj e₂)
  rw [h]

/-- **The instantiation facts of `fxEV P`** for a `SimpleFX.Inst` component. -/
theorem instFacts_fxV {c : SimpleFX} (hc : c.toSimple.Good) (hi : c.Inst)
    {I : Silmaril.Wasm.Game.ScalarInstance} {mt : Validation.CModuleType} {f' : Frame}
    {cs₁ : Store (FXCode (CanonHost (fxEV P)))}
    (hv : Validation.validate? c.core.mod = some mt) (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store (FXCode (CanonHost (fxEV P)))) c.core.mod [] =
      some (cs₁, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) :
    InstFacts (fxEV P) c.ofCore c.toSimple (csOf c f' cs₁) (ciOf c f' cs₁)
      (addrOf c I.addrs cs₁.funcs.length) where
  imports := importTypes_fx (P := P) hv hmt
  prepare := prepare_fxV hv hmt ho
  lookup x hx := by
    obtain ⟨nm, hn⟩ := hc.core x hx
    refine ⟨.func (addrOf c I.addrs cs₁.funcs.length x.core), ?_, rfl⟩
    have e : coreNameE c.toSimple.mod x = nm := by
      rw [coreNameE, hn]
      rfl
    rw [e]
    exact lookup_k hi hv ho ha hn

/-- The address of export `k` in the FX instance. -/
theorem asFunc_lookup_k {c : SimpleFX} (hi : c.Inst) {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} {cs₁ : Store (FXCode H)}
    (hv : Validation.validate? c.core.mod = some mt)
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.core.mod [] = some (cs₁, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) {k : Nat}
    {p : String × CoreFuncTy} (hk : c.mod.exports[k]? = some p) :
    (((fxEV P).exports (ciOf c f' cs₁)).lookup p.1).bind (fxEV P).asFunc? =
      some (addrOf c I.addrs cs₁.funcs.length k) := by
  show (List.lookup p.1 (Silmaril.Wasm.Component.Engine.Core3.instExports f'.module ++
    (ciOf c f' cs₁).fx)).bind (fxEV P).asFunc? = _
  rw [lookup_k hi hv ho ha hk]
  rfl

/-- `prepare?` of `fxEV P` at host type `Nat` gives the renamed store. -/
theorem prepare_fxV_nat {c : SimpleFX} {mt : Validation.CModuleType} {f' : Frame}
    {cs₁ : Store (FXCode H)} (g : H → Nat) (hv : Validation.validate? c.core.mod = some mt)
    (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.core.mod [] = some (cs₁, f', none)) :
    (fxEV P).prepare? ((fxEV P).empty Nat) (c.emb c.mod) [] =
      some (SM g (csOf c f' cs₁), ciOf c f' cs₁, none) := by
  have hp : (fxEV P).prepare? ((fxEV P).empty Nat) (c.ofCore c.core.mod) [] =
      some (csOf c f' (SM g cs₁), ciOf c f' (SM g cs₁), none) :=
    prepare_fxV hv hmt (instantiate_SM g ho)
  rw [csOf_SM, ciOf_SM] at hp
  exact hp

/-- **The engine instance of the specification** (host type `Nat`): the store is the machine's
store renamed, and export `k` is at `addrOf … k`. -/
theorem instOf_fxV {c : SimpleFX} (hi : c.Inst) {I : Silmaril.Wasm.Game.ScalarInstance}
    {mt : Validation.CModuleType} {f' : Frame} {cs₁ : Store (FXCode H)} (g : H → Nat)
    (hv : Validation.validate? c.core.mod = some mt) (hmt : mt.imports = [])
    (ho : instantiateOnce? ({} : Store (FXCode H)) c.core.mod [] = some (cs₁, f', none))
    (ha : Silmaril.Wasm.Game.exportFuncAddrs f'.module = I.addrs) :
    ∃ J : EInstance (fxEV P), instOf (fxEV P) (c.emb c.mod) [] c.mod.exports = some J ∧
      J.store = SM g (csOf c f' cs₁) ∧
      ∀ (k : Nat) (p : String × CoreFuncTy), c.mod.exports[k]? = some p →
        J.addrs[k]? = some (addrOf c I.addrs cs₁.funcs.length k) := by
  obtain ⟨L, hL⟩ : ∃ L, exportAddrs (fxEV P) (ciOf c f' cs₁) c.mod.exports = some L :=
    mapM_some fun p hp => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
      exact ⟨_, asFunc_lookup_k hi hv ho ha hk⟩
  have hJ : instOf (fxEV P) (c.emb c.mod) [] c.mod.exports = some ⟨SM g (csOf c f' cs₁), L⟩ := by
    unfold instOf
    simp only [allocHosts, List.map_nil, prepare_fxV_nat g hv hmt ho, hL]
    rfl
  refine ⟨⟨SM g (csOf c f' cs₁), L⟩, hJ, rfl, fun k p hk => ?_⟩
  obtain ⟨y, hy, hLk⟩ := mapM_getElem? hL hk
  have hy' : some (addrOf c I.addrs cs₁.funcs.length k) = some y :=
    (asFunc_lookup_k hi hv ho ha hk).symm.trans hy
  show L[k]? = _
  rw [hLk, hy']

end Silmaril.Proofs.Wasm.Component.FXRefV
