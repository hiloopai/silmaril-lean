module

public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Inst
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpCore
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpDefs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstImpRun
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.InstNest
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Call
public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Link.Base
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# `Silmaril.Proofs.Wasm.Component.Reference.InstLinkDefs` over `core3R P V IR`

Provenance: a copy of the declarations of `Silmaril.Proofs.Wasm.Component.Reference.InstLinkDefs` that the
soundness of linked components (`linked2_sound`, `linked2_sound_seq`) uses and whose statements
mention the engine `core3R P V IR`, with `core3R P V IR` replaced by `core3R P V IR` (Core 3.0 with
validity `V` and an internal step `IR` contained in `InternalP P`, `Core3R.Sub`). The other
declarations of that module are engine-generic and reused from it. Proofs are unchanged except
where a core step of the machine is read as an `InternalP P` step (through `Sub P IR`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Proofs.Wasm.Component.Reference

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)
open Silmaril.Wasm.Numerics (Profile)

variable {Pf : Profile} {σ : Type} {R : Recurse (core3R Pf V IR) σ}
  {inst : InstId} {outer : List (Frame (core3R Pf V IR))} {args : Exports (core3R Pf V IR)}

/-! ## Imports bound to arbitrary component functions -/

/-- **The definitions of the imports `ps` run silently**, pushing component functions
`fid k, fid (k + 1), …` when import `j` of `ps` is bound to `fid (k + j)`, a function of its
resolved type. -/
theorem importsDefs_runG (fid : Nat → FuncId) : ∀ (ps : Iface) (k : Nat) (sc : Scope (core3R Pf V IR))
    (cfg : Machine.Config (core3R Pf V IR) σ),
    (∀ j (hj : j < ps.length), args.lookup ps[j].1 = some (.func (fid (k + j))) ∧
      ∃ fi, ArenaField.funcs.get? cfg.store (fid (k + j)) = some fi ∧ fi.ft = witFt ps[j].2) →
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (SimpleI.importsDefs ps sc.frame.types.length).1) cfg sc' cfg ∧
      (∃ new, sc'.frame = { sc.frame with types := sc.frame.types ++ new,
                                          funcs := sc.frame.funcs ++ (List.range' k ps.length).map fid }) ∧
      sc'.frame.types.length = (SimpleI.importsDefs ps sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports
  | [], _, sc, cfg, _ => ⟨sc, TRuns.foldlM_nil sc cfg, ⟨[], by cases sc.frame; simp⟩, rfl, rfl⟩
  | p :: ps, k, sc, cfg, h => by
    obtain ⟨hl, fi, hs, ht⟩ := h 0 (Nat.zero_lt_succ _)
    obtain ⟨sc₁, hr₁, ⟨new₁, hf₁⟩, hn₁, hx₁⟩ := importDef_run (R := R) (inst := inst)
      (outer := outer) p (fid (k + 0)) sc cfg hl hs ht
    obtain ⟨sc₂, hr₂, ⟨new₂, hf₂⟩, hn₂, hx₂⟩ := importsDefs_runG fid ps (k + 1) sc₁ cfg
      (fun j hj => by
        obtain ⟨a, b⟩ := h (j + 1) (Nat.succ_lt_succ hj)
        rw [← Nat.add_assoc, Nat.add_right_comm] at a b
        exact ⟨a, b⟩)
    rw [importsDefs_cons]
    refine ⟨sc₂, TRuns.foldlM_append hr₁ (hn₁ ▸ hr₂), ⟨new₁ ++ new₂, ?_⟩, hn₁ ▸ hn₂,
      hx₂.trans hx₁⟩
    rw [hf₂, hf₁]
    simp only [List.length_cons, List.range'_succ, List.map_cons, List.append_assoc,
      List.singleton_append, Nat.add_zero]

/-! ## Trampolines after an existing core store -/

/-- The trampoline of an import of type `ft` lowering component function `callee` in instance
`inst`. -/
noncomputable def trampFIL (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (inst : InstId) (callee : FuncId) (ft : FuncTy) :
    Silmaril.Wasm.Execution.Core.FuncInst (CanonHost (core3R P V IR)) :=
  ⟨Silmaril.Wasm.SingleThreaded.ofFlatType (flatV1 ft), {},
    .host (.lowered callee (witFt ft) {} inst)⟩

/-- The trampolines of the imports `ims`, import `k` lowering `fid k`. -/
noncomputable def trampsL (P : Profile) (V : Silmaril.Wasm.Module → Prop)
    (IR : {H : Type} → Cfg3 H → Cfg3 H → Prop) (inst : InstId) (fid : Nat → FuncId) (ims : Iface) :
    List (Silmaril.Wasm.Execution.Core.FuncInst (CanonHost (core3R P V IR))) :=
  ims.mapIdx fun k p => trampFIL P V IR inst (fid k) p.2

/-- The core store `cs₀` followed by the trampolines of the imports `ims`. -/
noncomputable def trampStoreL (P : Profile) (cs₀ : (core3R P V IR).Store (CanonHost (core3R P V IR)))
    (inst : InstId) (fid : Nat → FuncId) (ims : Iface) : (core3R P V IR).Store (CanonHost (core3R P V IR)) :=
  { (cs₀ : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3R P V IR))) with
    funcs := (cs₀ : Silmaril.Wasm.Execution.Core.Store (CanonHost (core3R P V IR))).funcs ++
      trampsL P V IR inst fid ims }

theorem trampsL_take_succ (inst : InstId) (fid : Nat → FuncId) (ims : Iface) (k : Nat)
    (hk : k < ims.length) :
    trampsL Pf V IR inst fid (ims.take (k + 1)) =
      trampsL Pf V IR inst fid (ims.take k) ++ [trampFIL Pf V IR inst (fid k) ims[k].2] := by
  have hl : (ims.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  simp only [trampsL, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.mapIdx_append, hl, List.mapIdx_singleton, Nat.zero_add]

theorem trampStoreL_funcs_length (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (inst : InstId)
    (fid : Nat → FuncId) (ims : Iface) :
    (trampStoreL Pf cs₀ inst fid ims : Silmaril.Wasm.Execution.Core.Store _).funcs.length =
      (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + ims.length := by
  simp [trampStoreL, trampsL]

/-- **The `canon lower` of import `k`** appends its trampoline at core address `b + k`, where
`b` is the number of core functions of `cs₀`. -/
theorem lowerL_step {c : SimpleI} (har : ∀ p ∈ c.imports, (ValTy.flatList p.2.params).length ≤ 16 ∧
      (ValTy.flatList p.2.results).length ≤ 1 ∧ p.2.results.length ≤ 1)
    (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (fid : Nat → FuncId)
    (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ) (k : Nat)
    (hk : k < c.imports.length) (hf : sc.frame.funcs[k]? = some (fid k))
    (hcore : cfg.store.core = trampStoreL Pf cs₀ inst fid (c.imports.take k))
    {fi : CFuncInst (core3R Pf V IR)} (hs : ArenaField.funcs.get? cfg.store (fid k) = some fi)
    (ht : fi.ft = witFt c.imports[k].2) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lower k []))) cfg
      { sc with frame := { sc.frame with coreFuncs := sc.frame.coreFuncs ++
          ([(cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + k] :
            List (core3R Pf V IR).FuncAddr) } }
      { cfg with store := { cfg.store with
          core := trampStoreL Pf cs₀ inst fid (c.imports.take (k + 1)) } } := by
  obtain ⟨h₁, h₂, h₃⟩ := har _ (List.getElem_mem hk)
  have hty : (CanonHost.lowered (E := core3R Pf V IR) (fid k) fi.ft {} inst).coreType
      (addrTypesOf cfg.store) = flatV1 c.imports[k].2 := by
    rw [ht]
    exact coreType_lowered _ _ _ _ h₁ h₂ h₃
  have hl : (c.imports.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  have r := lower_run (R := R) (inst := inst) (outer := outer) (args := args) sc cfg hf hs hty
  have ha : ((core3R Pf V IR).allocHost cfg.store.core (flatV1 c.imports[k].2)
      (.lowered (fid k) fi.ft {} inst)).2 =
        (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + k := by
    show (cfg.store.core : Silmaril.Wasm.Execution.Core.Store _).funcs.length = _
    rw [hcore, trampStoreL_funcs_length, hl]
  have hst : allocHostSt (flatV1 c.imports[k].2) (.lowered (fid k) fi.ft {} inst)
      cfg.store = { cfg.store with
        core := trampStoreL Pf cs₀ inst fid (c.imports.take (k + 1)) } := by
    have e : trampStoreL Pf cs₀ inst fid (c.imports.take (k + 1)) =
        { (trampStoreL Pf cs₀ inst fid (c.imports.take k) :
            Silmaril.Wasm.Execution.Core.Store (CanonHost (core3R Pf V IR))) with
          funcs := (trampStoreL Pf cs₀ inst fid (c.imports.take k) :
            Silmaril.Wasm.Execution.Core.Store (CanonHost (core3R Pf V IR))).funcs ++
            [trampFIL Pf V IR inst (fid k) c.imports[k].2] } := by
      simp only [trampStoreL, trampsL_take_succ _ _ _ _ hk, List.append_assoc]
      rfl
    rw [e, ← hcore, ht]
    rfl
  rw [ha, hst] at r
  exact r

/-- **The `canon lower` definitions run silently**, allocating the trampolines `k, …, n - 1`
at core addresses `b + k, …, b + n - 1`. -/
theorem lowersL_run {c : SimpleI} (har : ∀ p ∈ c.imports, (ValTy.flatList p.2.params).length ≤ 16 ∧
      (ValTy.flatList p.2.results).length ≤ 1 ∧ p.2.results.length ≤ 1)
    (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (fid : Nat → FuncId) :
    ∀ (m k : Nat) (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ),
      k + m = c.imports.length → (∀ j < c.imports.length, sc.frame.funcs[j]? = some (fid j)) →
      cfg.store.core = trampStoreL Pf cs₀ inst fid (c.imports.take k) →
      (∀ j (hj : j < c.imports.length), ∃ fi,
        ArenaField.funcs.get? cfg.store (fid j) = some fi ∧ fi.ft = witFt c.imports[j].2) →
      TRuns (List.foldlM (instantiateDef R inst outer args) sc
          ((List.range' k m).map fun j => .canon (.lower j [])))
        cfg { sc with frame := { sc.frame with
          coreFuncs := sc.frame.coreFuncs ++
            addrList Pf (List.range' ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + k) m) } }
        { cfg with store := { cfg.store with core := trampStoreL Pf cs₀ inst fid c.imports } }
  | 0, k, sc, cfg, hkm, _, hcore, _ => by
    have hk : k = c.imports.length := hkm
    have hst : { cfg.store with core := trampStoreL Pf cs₀ inst fid c.imports } = cfg.store := by
      rw [← List.take_length (l := c.imports), ← hk, ← hcore]
    have hfr : { sc with frame := { sc.frame with
        coreFuncs := sc.frame.coreFuncs ++ addrList Pf (List.range'
          ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + k) 0) } } = sc := by
      have e : sc.frame.coreFuncs ++ addrList Pf (List.range'
          ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + k) 0) =
          sc.frame.coreFuncs := List.append_nil _
      rw [e]
      obtain ⟨⟨⟩, _⟩ := sc
      rfl
    rw [hst, hfr]
    exact TRuns.foldlM_nil sc cfg
  | m + 1, k, sc, cfg, hkm, hf, hcore, hs => by
    have hk : k < c.imports.length := by omega
    obtain ⟨fi, hfi, hft⟩ := hs k hk
    have r₁ := lowerL_step (R := R) (outer := outer) (args := args) har cs₀ fid sc cfg k hk
      (hf k hk) hcore hfi hft
    have r₂ := lowersL_run har cs₀ fid m (k + 1)
      { sc with frame := { sc.frame with coreFuncs := sc.frame.coreFuncs ++
          ([(cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + k] :
            List (core3R Pf V IR).FuncAddr) } }
      { cfg with store := { cfg.store with
          core := trampStoreL Pf cs₀ inst fid (c.imports.take (k + 1)) } }
      (by omega) hf rfl hs
    have hfr : sc.frame.coreFuncs ++
        ([(cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + k] :
          List (core3R Pf V IR).FuncAddr) ++
        addrList Pf (List.range' ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length +
          (k + 1)) m) =
        sc.frame.coreFuncs ++ addrList Pf (List.range'
          ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + k) (m + 1)) := by
      rw [List.append_assoc, List.range'_succ, Nat.add_assoc]
      rfl
    rw [← hfr]
    exact TRuns.foldlM_cons r₁ r₂

/-- The inline core instance exporting core functions `b, …, b + n - 1` under the names `ps`. -/
theorem coreExportsAt_run (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ)
    (b : Nat) (ps : CoreIface) (hcf : sc.frame.coreFuncs = addrList Pf (List.range' b ps.length)) :
    TRuns (instantiateDef R inst outer args sc
        (.coreInstance (.exports (ps.mapIdx fun k p => (p.1, ⟨.func, k⟩))))) cfg
      { sc with frame := { sc.frame with
        coreInstances := sc.frame.coreInstances ++
                           ([envExportsAt b ps] : List (List (String × (core3R Pf V IR).ExternVal))) } }
      cfg := by
  have hm : (ps.mapIdx fun k p => (p.1, (⟨.func, k⟩ : Syntax.SortIdx Syntax.CoreSort))).mapM
      (fun (x : String × Syntax.SortIdx Syntax.CoreSort) =>
        (x.1, ·) <$> externAt? sc.frame x.2) = some (envExportsAt b ps) := by
    refine mapM_eq_some_of_getElem (List.length_mapIdx.trans List.length_mapIdx.symm)
      fun i hi => ?_
    have hi' : i < ps.length := by simpa using hi
    simp only [List.getElem_mapIdx, envExportsAt, externAt?, Frame.get?, Frame.coreFunc?, hcf,
      addrList]
    erw [List.getElem?_range' hi', List.getElem_mapIdx]
    rw [Nat.one_mul]
    rfl
  simp only [instantiateDef, hm, need, orTrap, pure_bind, pushEntry, Frame.push]
  exact TRuns.pure _ _

/-! ## The exports after existing component functions -/

/-- `canon lift` allocates the next component function, whatever the core function index. -/
theorem liftG_run (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ) {cf ft : Nat}
    {a : (core3R Pf V IR).FuncAddr} {t : Types.FuncType RtId}
    (ha : sc.frame.coreFuncs[cf]? = some a) (ht : sc.frame.types[ft]? = some (.func t)) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lift cf [] ft))) cfg
      { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨cfg.store.funcs.length⟩] } }
      { cfg with store := ArenaOps.allocSt ArenaField.funcs (.lifted a t {} inst) cfg.store } := by
  rw [instDef_lift sc ha ht]
  exact (TRuns.allocObj _ (fun _ _ => rfl) _ cfg).bind (TRuns.pure _ _)

/-- The frame after the function type, the alias and the lift of an export allocating
component function `fid`. -/
def liftFrameL (f : Frame (core3R Pf V IR)) (t : Types.FuncType RtId) (a : (core3R Pf V IR).FuncAddr)
    (fid : FuncId) : Frame (core3R Pf V IR) :=
  { f with types := f.types ++ [.func t], coreFuncs := f.coreFuncs ++ [a],
           funcs := f.funcs ++ [fid] }

/-- **The definitions of one shifted export run silently** in a store holding `fb + i`
component functions: they allocate the lifted function `fb + i` and record its export. -/
theorem exportDefsAtL_run (names : CoreIface) (ix base fb i : Nat) (x : SimpleExport)
    (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ)
    {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} {a : (core3R Pf V IR).FuncAddr}
    (hinv : ExpInvAt es₀ ix base i sc.frame) (hs : cfg.store.funcs.length = fb + i)
    (hlk : lookupExport? es₀ (((names[x.core]?).map (·.1)).getD "") = some (.func a)) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (SimpleI.exportDefsAt names ix base i x sc.frame.types.length).1) cfg sc'
        { cfg with store :=
            ArenaOps.allocSt ArenaField.funcs (.lifted a (liftedFt x) {} inst) cfg.store } ∧
      ExpInvAt es₀ ix base (i + 1) sc'.frame ∧
      sc'.frame.types.length = (SimpleI.exportDefsAt names ix base i x sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports ++ [(x.name, ⟨fb + i⟩)] := by
  obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.params sc
  obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.results sc₁
  have hl₁ : sc₁.frame.types.length =
      (emitTys (M := (core3R Pf V IR).Module) x.ty.params sc.frame.types.length).2.2 := hP₁.2.2.1
  have hl₂ : sc₂.frame.types.length =
      (emitTys (M := (core3R Pf V IR).Module) x.ty.results sc₁.frame.types.length).2.2 := hP₂.2.2.1
  rw [exportDefsAt_eq, ← hl₁, ← hl₂]
  have hinv₂ : ExpInvAt es₀ ix base i sc₂.frame := hP₂.expInvAtR (hP₁.expInvAtR hinv)
  have hft : resolveFuncType? sc₂.frame
      { params := labels "a" (emitTys (M := (core3R Pf V IR).Module) x.ty.params
          sc.frame.types.length).1,
        result := (emitTys (M := (core3R Pf V IR).Module) x.ty.results
          sc₁.frame.types.length).1.head? } = some (liftedFt x) :=
    resolveFuncType_lifted (hR₁.imp fun _ _ h => h.mono hP₂.prefix) hR₂
  have h₃ := instDef_func (R := R) (inst := inst) (outer := outer) (args := args) sc₂ hft
  have hci : (Frame.coreInstance? { sc₂.frame with types := sc₂.frame.types ++
      [.func (liftedFt x)] } ix) = some es₀ := hinv₂.ci
  have h₄ := instDef_alias (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    { sc₂ with frame := { sc₂.frame with types := sc₂.frame.types ++ [.func (liftedFt x)] } }
    hci hlk rfl
  have hcf : (sc₂.frame.coreFuncs ++ [a])[base + i]? = some a := by
    rw [List.getElem?_append_right (by rw [hinv₂.cf]), hinv₂.cf, Nat.sub_self]
    rfl
  have hty : (sc₂.frame.types ++ [.func (liftedFt x)])[sc₂.frame.types.length]? =
      some (.func (liftedFt x)) := by simp
  have h₅ := liftG_run (R := R) (inst := inst) (outer := outer) (args := args)
    { sc₂ with frame := { sc₂.frame with
        types := sc₂.frame.types ++ [Types.TypeDef.func (liftedFt x)],
        coreFuncs := sc₂.frame.coreFuncs ++ [a] } } cfg hcf hty
  rw [hs] at h₅
  have hfn : (sc₂.frame.funcs ++ [(⟨fb + i⟩ : FuncId)])[base + 2 * i]? = some ⟨fb + i⟩ := by
    rw [List.getElem?_append_right (by rw [hinv₂.fn]), hinv₂.fn, Nat.sub_self]
    rfl
  have h₆ := instDef_funcExport (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    (nm := { name := x.name })
    { sc₂ with frame := liftFrameL sc₂.frame (liftedFt x) a ⟨fb + i⟩ } hfn
  refine ⟨_, TRuns.foldlM_append (TRuns.foldlM_append (TRuns.ofPure hP₁ cfg)
    (TRuns.ofPure hP₂ cfg)) (TRuns.foldlM_cons (TRuns.of_eq cfg h₃)
    (TRuns.foldlM_cons (TRuns.of_eq cfg h₄) (TRuns.foldlM_cons h₅
    (TRuns.foldlM_cons (TRuns.of_eq _ h₆) (TRuns.foldlM_nil _ _))))), ?_, ?_, ?_⟩
  · exact ⟨hinv₂.ci, by simp [liftFrameL, hinv₂.cf]; omega, by simp [liftFrameL, hinv₂.fn]; omega⟩
  · simp [liftFrameL]
  · have hx : funcExports sc₂.exports = funcExports sc.exports := hP₂.2.2.2.1.trans hP₁.2.2.2.1
    rw [funcExports_append_func, hx]

/-- **The definitions of all shifted exports run silently** in a store holding `fb + i`
component functions, appending the lifted functions and recording their exports at
`fb + i + k`. -/
theorem exportsDefsAtL_run (names : CoreIface) (ix base fb : Nat)
    (addr : Nat → (core3R Pf V IR).FuncAddr)
    {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} :
    ∀ (xs : List SimpleExport) (i : Nat) (sc : Scope (core3R Pf V IR))
      (cfg : Machine.Config (core3R Pf V IR) σ), ExpInvAt es₀ ix base i sc.frame →
      cfg.store.funcs.length = fb + i →
      (∀ x ∈ xs, lookupExport? es₀ (((names[x.core]?).map (·.1)).getD "") =
        some (.func (addr x.core))) →
      ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
          (SimpleI.exportsDefsAt names ix base i xs sc.frame.types.length)) cfg sc'
          { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst xs } } ∧
        funcExports sc'.exports =
          funcExports sc.exports ++ xs.mapIdx (fun k x => (x.name, ⟨fb + i + k⟩))
  | [], i, sc, cfg, _, _, _ => by
    refine ⟨sc, ?_, by rw [List.mapIdx_nil, List.append_nil]⟩
    simp only [liftedList, List.map_nil, List.append_nil]
    exact TRuns.foldlM_nil sc cfg
  | x :: xs, i, sc, cfg, hinv, hs, hlk => by
    obtain ⟨sc₁, hr₁, hinv₁, hl₁, hx₁⟩ := exportDefsAtL_run (R := R) (inst := inst)
      (outer := outer) (args := args) names ix base fb i x sc cfg hinv hs
      (hlk x List.mem_cons_self)
    have hs₁ : (cfg.store.funcs ++ liftedList addr inst [x]).length = fb + (i + 1) := by
      rw [List.length_append, hs]
      rfl
    obtain ⟨sc₂, hr₂, hx₂⟩ := exportsDefsAtL_run names ix base fb addr xs (i + 1) sc₁
      { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst [x] } }
      hinv₁ hs₁
      (fun y hy => hlk y (List.mem_cons_of_mem _ hy))
    rw [exportsDefsAt_cons]
    refine ⟨sc₂, ?_, ?_⟩
    · rw [liftedList_cons, ← List.append_assoc]
      exact TRuns.foldlM_append hr₁ (hl₁ ▸ hr₂)
    · rw [hx₂, hx₁, List.mapIdx_cons, List.append_assoc, Nat.add_zero, ← Nat.add_assoc,
        mapIdx_shift_at]
      rfl

/-! ## The core instantiation in the shared store -/

/-- **The core facts of the importer in a shared store**, over `core3R Pf V IR`: the importer module
instantiates in the core store `cs₀` followed by its trampolines (`trampStoreL`; trampoline `k`
lowers `fid k` in instance `inst`) with the import vector of the trampolines, without a start
function, to `cs` and `ci`; the inline core instance gives that import vector; and the core
exports lifted by `c` are found by name at `addr x.core`. -/
structure CoreFactsL (c : SimpleI) (cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR)))
    (inst : InstId) (fid : Nat → FuncId) (addr : Nat → Nat)
    (cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (ci : (core3R Pf V IR).Inst) : Prop where
  prepare : (core3R Pf V IR).prepare? (trampStoreL Pf cs₀ inst fid c.imports) c.mod.mod
    ((List.range' (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length c.imports.length).map
      Silmaril.Wasm.Execution.Core.ExternAddr.func) = some (cs, ci, none)
  imports : ∀ f : Frame (core3R Pf V IR),
    f.coreInstance? 0 = some (envExportsAt (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length
      c.mod.imports) →
    coreImportsFor? (trampStoreL Pf cs₀ inst fid c.imports) c.mod.mod [("env", 0)] f =
      some ((List.range' (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length
        c.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
  lookup : ∀ x ∈ c.exports, lookupExport? ((core3R Pf V IR).exports ci) (coreNameI c x) =
    some (.func (addr x.core))

/-- The import bindings of a nested instantiation: import `j` of `c` is bound in `args` to the
component function `fid j` of the store `s`, whose type is the resolved type of the import. -/
def ImportsBound (c : SimpleI) (args : Exports (core3R Pf V IR)) (fid : Nat → FuncId)
    (s : CStore (core3R Pf V IR)) : Prop :=
  ∀ j (hj : j < c.imports.length), args.lookup c.imports[j].1 = some (.func (fid j)) ∧
    ∃ fi, ArenaField.funcs.get? s (fid j) = some fi ∧ fi.ft = witFt c.imports[j].2

/-- **The definitions of `c.toRef` run silently in a nested instance over a shared store**:
from a store whose core store is `cs₀` and which holds `fb` component functions, with import `j`
bound to `fid j`, the imports, the core module, the trampolines (after `cs₀`), the two core
instances and the lifted functions of the exports (after the `fb` functions), exported at
`fb + i`. -/
theorem toRefDefsL_run {c : SimpleI} (hc : c.Good) (har : c.Arity)
    {cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {fid : Nat → FuncId} {addr : Nat → Nat}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hF : CoreFactsL c cs₀ inst fid addr cs ci) (cfg : Machine.Config (core3R Pf V IR) σ) {fb : Nat}
    (hcore : cfg.store.core = cs₀) (hfb : cfg.store.funcs.length = fb)
    (hb : ImportsBound c args fid cfg.store) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) {} c.toRef) cfg sc'
        { cfg with store := liftStore cs cfg.store (liftedList addr inst c.exports) } ∧
      funcExports sc'.exports = c.exports.mapIdx fun i x => (x.name, ⟨fb + i⟩) := by
  have hb' : ∀ j (hj : j < c.imports.length), ∃ fi,
      ArenaField.funcs.get? cfg.store (fid j) = some fi ∧ fi.ft = witFt c.imports[j].2 :=
    fun j hj => (hb j hj).2
  -- the imports
  obtain ⟨scA, rA, ⟨newA, hfA⟩, hlA, hxA⟩ := importsDefs_runG (R := R) (inst := inst)
    (outer := outer) (args := args) fid c.imports 0 {} cfg fun j hj => by
      rw [Nat.zero_add]
      exact hb j hj
  have hlenm : c.mod.imports.length = c.imports.length := by rw [hc.imports, List.length_map]
  -- the core module
  have rB := instDef_coreModule (R := R) (inst := inst) (outer := outer) (args := args) scA
    c.mod.mod
  -- the trampolines
  have hfB : ∀ j < c.imports.length,
      ({ scA.frame with coreModules := scA.frame.coreModules ++
          ([c.mod.mod] : List (core3R Pf V IR).Module) } : Frame (core3R Pf V IR)).funcs[j]? =
        some (fid j) := by
    intro j hj
    show scA.frame.funcs[j]? = _
    rw [hfA]
    simp [hj, Frame.empty]
  have hcore₀ : cfg.store.core = trampStoreL Pf cs₀ inst fid (c.imports.take 0) := by
    rw [hcore]
    simp [trampStoreL, trampsL]
    rfl
  have rC := lowersL_run (R := R) (inst := inst) (outer := outer) (args := args)
    (arity_imports har) cs₀ fid c.imports.length 0
    { scA with frame := { scA.frame with coreModules := scA.frame.coreModules ++
        ([c.mod.mod] : List (core3R Pf V IR).Module) } }
    cfg (Nat.zero_add _) hfB hcore₀ hb'
  -- the inline core instance
  have hcfC : (scA.frame.coreFuncs ++ addrList Pf (List.range'
      ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + 0) c.imports.length)) =
      addrList Pf (List.range' (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length
        c.mod.imports.length) := by
    rw [hfA, hlenm, Nat.add_zero]
    rfl
  have rD := coreExportsAt_run (R := R) (inst := inst) (outer := outer) (args := args)
    { scA with frame := { scA.frame with
        coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3R Pf V IR).Module),
        coreFuncs := scA.frame.coreFuncs ++ addrList Pf (List.range'
          ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + 0) c.imports.length) } }
    { cfg with store := { cfg.store with core := trampStoreL Pf cs₀ inst fid c.imports } }
    _ c.mod.imports hcfC
  -- the core instantiation
  have hmE : (scA.frame.coreModules ++ ([c.mod.mod] : List (core3R Pf V IR).Module)) =
      ([c.mod.mod] : List (core3R Pf V IR).Module) := by rw [hfA]; rfl
  have hciE : (scA.frame.coreInstances ++
      ([envExportsAt (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length c.mod.imports] :
        List (List (String × (core3R Pf V IR).ExternVal))))[0]? =
      some (envExportsAt (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length
        c.mod.imports) := by rw [hfA]; rfl
  have rE := instantiateEnv_run (R := R) (inst := inst) (outer := outer) (args := args)
    { scA with frame := { scA.frame with
        coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3R Pf V IR).Module),
        coreFuncs := scA.frame.coreFuncs ++ addrList Pf (List.range'
          ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + 0) c.imports.length),
        coreInstances := scA.frame.coreInstances ++
          ([envExportsAt (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length
            c.mod.imports] : List (List (String × (core3R Pf V IR).ExternVal))) } }
    { cfg with store := { cfg.store with core := trampStoreL Pf cs₀ inst fid c.imports } } hmE
    (hF.imports _ hciE) hF.prepare
  -- the exports
  have hinv : ExpInvAt ((core3R Pf V IR).exports ci) 1 c.imports.length 0
      ({ scA.frame with
          coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3R Pf V IR).Module),
          coreFuncs := scA.frame.coreFuncs ++ addrList Pf (List.range'
            ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + 0) c.imports.length),
          coreInstances := scA.frame.coreInstances ++
            ([envExportsAt (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length
              c.mod.imports] : List (List (String × (core3R Pf V IR).ExternVal))) ++
            [(core3R Pf V IR).exports ci] } : Frame (core3R Pf V IR)) := by
    refine ⟨?_, ?_, ?_⟩
    · show (scA.frame.coreInstances ++ _ ++ _)[1]? = _
      rw [hfA]
      rfl
    · show (scA.frame.coreFuncs ++ addrList Pf _).length = _
      rw [hfA]
      show (addrList Pf (List.range' _ c.imports.length)).length = c.imports.length + 0
      exact List.length_range'
    · show scA.frame.funcs.length = _
      rw [hfA]
      simp [Frame.empty]
  have hs : (setCoreSt cs { cfg.store with
      core := trampStoreL Pf cs₀ inst fid c.imports }).funcs.length = fb + 0 := hfb
  obtain ⟨scF, rF, hxF⟩ := exportsDefsAtL_run (R := R) (inst := inst) (outer := outer)
    (args := args) c.mod.exports 1 c.imports.length fb addr c.exports 0
    { scA with frame := { scA.frame with
        coreModules := scA.frame.coreModules ++ ([c.mod.mod] : List (core3R Pf V IR).Module),
        coreFuncs := scA.frame.coreFuncs ++ addrList Pf (List.range'
          ((cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length + 0) c.imports.length),
        coreInstances := scA.frame.coreInstances ++
          ([envExportsAt (cs₀ : Silmaril.Wasm.Execution.Core.Store _).funcs.length
            c.mod.imports] : List (List (String × (core3R Pf V IR).ExternVal))) ++
          [(core3R Pf V IR).exports ci] } }
    { cfg with store := setCoreSt cs { cfg.store with
        core := trampStoreL Pf cs₀ inst fid c.imports } }
    hinv hs (fun x hx => hF.lookup x hx)
  have hlA' : scA.frame.types.length = (SimpleI.importsDefs c.imports 0).2 := hlA
  rw [hlA'] at rF
  refine ⟨scF, ?_, ?_⟩
  · rw [← lowers_eq] at rC
    rw [toRef_eq]
    exact TRuns.foldlM_append rA (TRuns.foldlM_append (TRuns.foldlM_append (TRuns.foldlM_append
      (TRuns.foldlM_cons (TRuns.of_eq cfg rB) (TRuns.foldlM_nil _ _)) rC)
      (TRuns.foldlM_cons rD (TRuns.foldlM_cons rE (TRuns.foldlM_nil _ _)))) rF)
  · have hx₀ : funcExports scA.exports = [] := hxA
    rw [hxF]
    show funcExports scA.exports ++ _ = _
    rw [hx₀, List.nil_append]
    simp only [Nat.add_zero]

/-! ## The nested instantiation of the importer -/

/-- The store after the nested instantiation of a simple component with imports in the
instance allocated next: the core store `cs`, the lifted functions after those of `s`. -/
noncomputable def nestStoreI (cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR)))
    (s : CStore (core3R Pf V IR)) (addr : Nat → Nat) (inst : InstId) (c : SimpleI) :
    CStore (core3R Pf V IR) :=
  liftStore cs (ArenaOps.allocSt ArenaField.insts {} s) (liftedList addr inst c.exports)

/-- **The nested instantiation of a simple component with imports runs silently**: in a store
whose core store is `cs₀` and which holds `fb` component functions, with import `j` bound to
`fid j`, the dispatcher's program for `Call.instantiate ⟨c.toRef, outer⟩ vs` allocates the next
instance, runs the definitions of `c.toRef` in it (`toRefDefsL_run`) and answers its exports,
export `i` at function `fb + i`. -/
theorem instantiateCall_simpleI {c : SimpleI} (hc : c.Good) (har : c.Arity)
    {cs₀ : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {fid : Nat → FuncId} {addr : Nat → Nat}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (outer : List (Frame (core3R Pf V IR))) (vs : Exports (core3R Pf V IR))
    (cfg : Machine.Config (core3R Pf V IR) σ) {fb : Nat}
    (hF : CoreFactsL c cs₀ (nextInst cfg.store) fid addr cs ci)
    (hcore : cfg.store.core = cs₀) (hfb : cfg.store.funcs.length = fb)
    (hb : ImportsBound c vs fid cfg.store) :
    ∃ es, funcExports es = c.exports.mapIdx (fun i x => (x.name, ⟨fb + i⟩)) ∧
      TRuns (instantiateCallProg ⟨c.toRef, outer⟩ vs : P (core3R Pf V IR) σ (Ret (core3R Pf V IR))) cfg
        (.items es)
        { cfg with store := nestStoreI cs cfg.store addr (nextInst cfg.store) c } := by
  obtain ⟨sc', hr, hx⟩ := toRefDefsL_run (R := callRecurse) (inst := nextInst cfg.store)
    (outer := outer) (args := vs) hc har hF
    { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store } hcore hfb hb
  refine ⟨sc'.exports, hx, ?_⟩
  unfold instantiateCallProg instantiateClosure instantiateComponent
  refine TRuns.bind (f := fun es => Pure.pure (Ret.items es)) ?_ (TRuns.pure _ _)
  exact (TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind
    (TRuns.bind (a := sc') (b := sc'.exports) hr (TRuns.pure _ _))

end Silmaril.Proofs.Wasm.Component.Param.Core3R
