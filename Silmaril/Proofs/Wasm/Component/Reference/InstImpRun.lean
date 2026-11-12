module

public import Silmaril.Proofs.Wasm.Component.Reference.InstImpDefs
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The definitions of `SimpleI.toRef` after its imports

After the import definitions (`InstImpDefs`), `SimpleI.toRef` defines the core module, the
`canon lower` of each import (`lowers_run`: trampoline `k` is allocated at core address `k`, the
core store becomes `trampStore`), the inline core instance exporting the trampolines under the
module's import names (`coreExports_run`), the instantiation of the module with it as `"env"`
(`instantiateEnv_run`), and the exports aliased from core instance `1` (`exportsDefsAt_run`,
the export definitions of `Simple.toRef` shifted by the `n` imports: lift `n + i`, export
function `n + 2i`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition)

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type} {R : Recurse (core3P Pf) σ}
  {inst : InstId} {outer : List (Frame (core3P Pf))} {args : Exports (core3P Pf)}

/-! ## The export definitions, shifted -/

/-- What the frame holds before export `i`: the core instance `es₀` at index `ix`, `base + i`
core functions and `base + 2i` component functions. -/
structure ExpInvAt (es₀ : List (String × (core3P Pf).ExternVal)) (ix base i : Nat)
    (f : Frame (core3P Pf)) : Prop where
  ci : f.coreInstance? ix = some es₀
  cf : f.coreFuncs.length = base + i
  fn : f.funcs.length = base + 2 * i

theorem PureTys.expInvAt {sc sc' : Scope (core3P Pf)}
    {ds : List (Syntax.Definition (core3P Pf).Module)} {n ix base i : Nat}
    {es₀ : List (String × (core3P Pf).ExternVal)} (h : PureTys R inst outer args sc ds sc' n)
    (hi : ExpInvAt es₀ ix base i sc.frame) : ExpInvAt es₀ ix base i sc'.frame := by
  obtain ⟨-, ⟨new, hf⟩, -⟩ := h
  rw [hf]
  exact ⟨hi.ci, hi.cf, hi.fn⟩

theorem exportDefsAt_eq (names : CoreIface) (ix base i : Nat) (x : SimpleExport) (n : Nat) :
    (SimpleI.exportDefsAt names ix base i x n :
      List (Syntax.Definition (core3P Pf).Module) × Nat) =
      ((emitTys (M := (core3P Pf).Module) x.ty.params n).2.1 ++
        (emitTys (M := (core3P Pf).Module) x.ty.results
          (emitTys (M := (core3P Pf).Module) x.ty.params n).2.2).2.1 ++
        [.type (.func { params := labels "a" (emitTys (M := (core3P Pf).Module) x.ty.params n).1,
                        result := (emitTys (M := (core3P Pf).Module) x.ty.results
                          (emitTys (M := (core3P Pf).Module) x.ty.params n).2.2).1.head? }),
         .alias (.coreExport ix (((names[x.core]?).map (·.1)).getD "") .func),
         .canon (.lift (base + i) [] (emitTys (M := (core3P Pf).Module) x.ty.results
           (emitTys (M := (core3P Pf).Module) x.ty.params n).2.2).2.2),
         .export_ { name := x.name } ⟨.func, base + 2 * i⟩ none],
        (emitTys (M := (core3P Pf).Module) x.ty.results
          (emitTys (M := (core3P Pf).Module) x.ty.params n).2.2).2.2 + 1) := by
  simp only [SimpleI.exportDefsAt]
  rfl

/-- **The definitions of one shifted export run silently**: from the frame invariant of export
`i`, they allocate the lifted function `base + i` and record its export. -/
theorem exportDefsAt_run (names : CoreIface) (ix base i : Nat) (x : SimpleExport)
    (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ)
    {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} {a : (core3P Pf).FuncAddr}
    (hinv : ExpInvAt es₀ ix base i sc.frame) (hs : cfg.store.funcs.length = base + i)
    (hlk : lookupExport? es₀ (((names[x.core]?).map (·.1)).getD "") = some (.func a)) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (SimpleI.exportDefsAt names ix base i x sc.frame.types.length).1) cfg sc'
        { cfg with store :=
            ArenaOps.allocSt ArenaField.funcs (.lifted a (liftedFt x) {} inst) cfg.store } ∧
      ExpInvAt es₀ ix base (i + 1) sc'.frame ∧
      sc'.frame.types.length = (SimpleI.exportDefsAt names ix base i x sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports ++ [(x.name, ⟨base + i⟩)] ∧
      NoImport (SimpleI.exportDefsAt names ix base i x sc.frame.types.length).1 := by
  obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.params sc
  obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.results sc₁
  have hl₁ : sc₁.frame.types.length =
      (emitTys (M := (core3P Pf).Module) x.ty.params sc.frame.types.length).2.2 := hP₁.2.2.1
  have hl₂ : sc₂.frame.types.length =
      (emitTys (M := (core3P Pf).Module) x.ty.results sc₁.frame.types.length).2.2 := hP₂.2.2.1
  rw [exportDefsAt_eq, ← hl₁, ← hl₂]
  have hinv₂ : ExpInvAt es₀ ix base i sc₂.frame := hP₂.expInvAt (hP₁.expInvAt hinv)
  have hft : resolveFuncType? sc₂.frame
      { params := labels "a" (emitTys (M := (core3P Pf).Module) x.ty.params
          sc.frame.types.length).1,
        result := (emitTys (M := (core3P Pf).Module) x.ty.results
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
  have h₅ := lift_run (R := R) (inst := inst) (outer := outer) (args := args)
    { sc₂ with frame := { sc₂.frame with
        types := sc₂.frame.types ++ [Types.TypeDef.func (liftedFt x)],
        coreFuncs := sc₂.frame.coreFuncs ++ [a] } } cfg hs hcf hty
  have hfn : (sc₂.frame.funcs ++ [(⟨base + i⟩ : FuncId)])[base + 2 * i]? = some ⟨base + i⟩ := by
    rw [List.getElem?_append_right (by rw [hinv₂.fn]), hinv₂.fn, Nat.sub_self]
    rfl
  have h₆ := instDef_funcExport (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    (nm := { name := x.name })
    { sc₂ with frame := liftFrame sc₂.frame (liftedFt x) a (base + i) } hfn
  refine ⟨_, TRuns.foldlM_append (TRuns.foldlM_append (TRuns.ofPure hP₁ cfg)
    (TRuns.ofPure hP₂ cfg)) (TRuns.foldlM_cons (TRuns.of_eq cfg h₃)
    (TRuns.foldlM_cons (TRuns.of_eq cfg h₄) (TRuns.foldlM_cons h₅
    (TRuns.foldlM_cons (TRuns.of_eq _ h₆) (TRuns.foldlM_nil _ _))))), ?_, ?_, ?_, ?_⟩
  · exact ⟨hinv₂.ci, by simp [liftFrame, hinv₂.cf]; omega, by simp [liftFrame, hinv₂.fn]; omega⟩
  · simp [liftFrame]
  · have hx : funcExports sc₂.exports = funcExports sc.exports := hP₂.2.2.2.1.trans hP₁.2.2.2.1
    rw [funcExports_append_func, hx]
  · exact (hP₁.2.2.2.2.append hP₂.2.2.2.2).append
      (noImport_tail _ _ _ _ _ (fun _ _ e => by cases e) (fun _ _ e => by cases e)
        (fun _ _ e => by cases e))

theorem exportsDefsAt_cons (names : CoreIface) (ix base i : Nat) (x : SimpleExport)
    (xs : List SimpleExport) (n : Nat) :
    SimpleI.exportsDefsAt names ix base i (x :: xs) n =
      (SimpleI.exportDefsAt names ix base i x n).1 ++
        SimpleI.exportsDefsAt names ix base (i + 1) xs (SimpleI.exportDefsAt names ix base i x n).2 := by
  simp only [SimpleI.exportsDefsAt]

theorem mapIdx_shift_at (xs : List SimpleExport) (b : Nat) :
    (xs.mapIdx fun k x => (x.name, (⟨b + 1 + k⟩ : FuncId))) =
      xs.mapIdx fun k x => (x.name, (⟨b + (k + 1)⟩ : FuncId)) := by
  congr 1
  funext k x
  rw [Nat.add_assoc, Nat.add_comm 1 k]

/-- **The definitions of all shifted exports run silently**, appending the lifted functions
to the component functions and recording their exports at `base + i + k`. -/
theorem exportsDefsAt_run (names : CoreIface) (ix base : Nat) (addr : Nat → (core3P Pf).FuncAddr)
    {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} :
    ∀ (xs : List SimpleExport) (i : Nat) (sc : Scope (core3P Pf))
      (cfg : Machine.Config (core3P Pf) σ), ExpInvAt es₀ ix base i sc.frame →
      cfg.store.funcs.length = base + i →
      (∀ x ∈ xs, lookupExport? es₀ (((names[x.core]?).map (·.1)).getD "") =
        some (.func (addr x.core))) →
      ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
          (SimpleI.exportsDefsAt names ix base i xs sc.frame.types.length)) cfg sc'
          { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst xs } } ∧
        funcExports sc'.exports =
          funcExports sc.exports ++ xs.mapIdx (fun k x => (x.name, ⟨base + i + k⟩)) ∧
        NoImport (SimpleI.exportsDefsAt names ix base i xs sc.frame.types.length)
  | [], i, sc, cfg, _, _, _ => by
    refine ⟨sc, ?_, by rw [List.mapIdx_nil, List.append_nil], fun _ h => by cases h⟩
    simp only [liftedList, List.map_nil, List.append_nil]
    exact TRuns.foldlM_nil sc cfg
  | x :: xs, i, sc, cfg, hinv, hs, hlk => by
    obtain ⟨sc₁, hr₁, hinv₁, hl₁, hx₁, hn₁⟩ := exportDefsAt_run (R := R) (inst := inst)
      (outer := outer) (args := args) names ix base i x sc cfg hinv hs (hlk x List.mem_cons_self)
    have hs₁ : (cfg.store.funcs ++ liftedList addr inst [x]).length = base + (i + 1) := by
      rw [List.length_append, hs]
      rfl
    obtain ⟨sc₂, hr₂, hx₂, hn₂⟩ := exportsDefsAt_run names ix base addr xs (i + 1) sc₁
      { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst [x] } }
      hinv₁ hs₁
      (fun y hy => hlk y (List.mem_cons_of_mem _ hy))
    rw [exportsDefsAt_cons]
    refine ⟨sc₂, ?_, ?_, hn₁.append (hl₁ ▸ hn₂)⟩
    · rw [liftedList_cons, ← List.append_assoc]
      exact TRuns.foldlM_append hr₁ (hl₁ ▸ hr₂)
    · rw [hx₂, hx₁, List.mapIdx_cons, List.append_assoc, Nat.add_zero, ← Nat.add_assoc,
        mapIdx_shift_at]
      rfl

/-! ## The `canon lower` definitions -/

theorem TRuns.getObj {Id α : Type} (F : ArenaField (core3P Pf) Id α) (i : Id) {x : α}
    (m : Machine.Config (core3P Pf) σ) (h : F.get? m.store i = some x) :
    TRuns (Canon.getObj F i : P (core3P Pf) σ α) m x m := by
  refine .get ?_
  show TRuns (match F.get? m.store i with
    | some x => Pure.pure x | none => internal "dangling arena id") m x m
  rw [h]
  exact TRuns.pure x m

theorem TRuns.allocCoreHost (h : CanonHost (core3P Pf)) (m : Machine.Config (core3P Pf) σ) :
    TRuns (Instantiate.allocCoreHost h : P (core3P Pf) σ _) m
      ((core3P Pf).allocHost m.store.core (h.coreType (addrTypesOf m.store)) h).2
      { m with store := allocHostSt (h.coreType (addrTypesOf m.store)) h m.store } :=
  (TRuns.getStore m).bind ((TRuns.modifyStore
    (f := allocHostSt (h.coreType (addrTypesOf m.store)) h) (fun _ => rfl) m).bind
    (TRuns.pure _ _))

/-- `canon lower` of component function `fid` without options allocates its trampoline. -/
theorem lower_run (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ) {k : Nat}
    {fid : FuncId} {fi : CFuncInst (core3P Pf)} {ty : Silmaril.Wasm.V1.FuncType}
    (hf : sc.frame.funcs[k]? = some fid) (hs : ArenaField.funcs.get? cfg.store fid = some fi)
    (hty : (CanonHost.lowered fid fi.ft {} inst).coreType (addrTypesOf cfg.store) = ty) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lower k []))) cfg
      { sc with frame := { sc.frame with coreFuncs := sc.frame.coreFuncs ++
                             [((core3P Pf).allocHost cfg.store.core ty (.lowered fid fi.ft {} inst)).2] } }
      { cfg with store := allocHostSt ty (.lowered fid fi.ft {} inst) cfg.store } := by
  have hr : resolveLower? sc.frame k [] = some (fid, {}) := by
    simp only [resolveLower?, Frame.func?, hf, resolveOpts?_nil]
    rfl
  simp only [instantiateDef, hr, need, orTrap, pure_bind]
  have ha := TRuns.allocCoreHost (σ := σ) (CanonHost.lowered fid fi.ft {} inst) cfg
  rw [hty] at ha
  refine (TRuns.getObj ArenaField.funcs fid cfg hs).bind (ha.bind ?_)
  simp only [pushEntry, Frame.push, need, orTrap, pure_bind]
  exact TRuns.pure _ _

/-- The host functions of the imports `ims`, from function `k` on. -/
noncomputable def hostList (k : Nat) (ims : Iface) : List (CFuncInst (core3P Pf)) :=
  ims.mapIdx fun j p => .host (witFt p.2) ⟨k + j⟩

theorem trampStore_take_succ (ims : Iface) (k : Nat) (hk : k < ims.length) :
    trampStore Pf (ims.take (k + 1)) =
      { trampStore Pf (ims.take k) with
        funcs := (trampStore Pf (ims.take k)).funcs ++ [trampFI Pf k ims[k]] } := by
  have hl : (ims.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  simp only [trampStore, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
    List.mapIdx_append, hl, List.mapIdx_singleton, Nat.zero_add]

/-- **The `canon lower` of import `k`** appends its trampoline at core address `k`. -/
theorem lower_step {c : SimpleI} (har : ∀ p ∈ c.imports, (ValTy.flatList p.2.params).length ≤ 16 ∧
      (ValTy.flatList p.2.results).length ≤ 1 ∧ p.2.results.length ≤ 1)
    (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ) (k : Nat)
    (hk : k < c.imports.length) (hf : sc.frame.funcs[k]? = some ⟨k⟩)
    (hcore : cfg.store.core = trampStore Pf (c.imports.take k))
    (hs : ArenaField.funcs.get? cfg.store ⟨k⟩ = some (.host (witFt c.imports[k].2) ⟨k⟩)) :
    TRuns (instantiateDef R ⟨0⟩ outer args sc (.canon (.lower k []))) cfg
      { sc with frame := { sc.frame with coreFuncs := sc.frame.coreFuncs ++ ([k] : List (core3P Pf).FuncAddr) } }
      { cfg with store := { cfg.store with core := trampStore Pf (c.imports.take (k + 1)) } } := by
  obtain ⟨h₁, h₂, h₃⟩ := har _ (List.getElem_mem hk)
  have hty : (CanonHost.lowered (E := core3P Pf) ⟨k⟩ (witFt c.imports[k].2) {} ⟨0⟩).coreType
      (addrTypesOf cfg.store) = flatV1 c.imports[k].2 :=
    coreType_lowered _ _ _ _ h₁ h₂ h₃
  have hl : (c.imports.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk)
  have r := lower_run (R := R) (inst := ⟨0⟩) (outer := outer) (args := args) sc cfg hf hs hty
  have ha : ((core3P Pf).allocHost cfg.store.core (flatV1 c.imports[k].2)
      (.lowered ⟨k⟩ (witFt c.imports[k].2) {} ⟨0⟩)).2 = k := by
    show (cfg.store.core : Silmaril.Wasm.Execution.Core.Store _).funcs.length = k
    rw [hcore]
    simp only [trampStore, List.length_mapIdx, hl]
  have hst : allocHostSt (flatV1 c.imports[k].2) (.lowered ⟨k⟩ (witFt c.imports[k].2) {} ⟨0⟩)
      cfg.store = { cfg.store with core := trampStore Pf (c.imports.take (k + 1)) } := by
    rw [trampStore_take_succ _ _ hk, ← hcore]
    rfl
  simp only [CFuncInst.ft] at r
  rw [ha, hst] at r
  exact r

/-- Natural numbers as core function addresses of `core3P Pf`. -/
def addrList (Pf : Silmaril.Wasm.Numerics.Profile) (l : List Nat) : List (core3P Pf).FuncAddr := l

theorem lowers_eq (ims : Iface) :
    (ims.mapIdx fun k _ => (.canon (.lower k []) : Syntax.Definition (core3P Pf).Module)) =
      (List.range' 0 ims.length).map fun j => .canon (.lower j []) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp

/-- **The `canon lower` definitions run silently**, allocating the trampolines `k, …, n - 1`
at core addresses `k, …, n - 1`. -/
theorem lowers_run {c : SimpleI} (har : ∀ p ∈ c.imports, (ValTy.flatList p.2.params).length ≤ 16 ∧
      (ValTy.flatList p.2.results).length ≤ 1 ∧ p.2.results.length ≤ 1) :
    ∀ (m k : Nat) (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ),
      k + m = c.imports.length → (∀ j < c.imports.length, sc.frame.funcs[j]? = some ⟨j⟩) →
      cfg.store.core = trampStore Pf (c.imports.take k) →
      (∀ j (hj : j < c.imports.length),
        ArenaField.funcs.get? cfg.store ⟨j⟩ = some (.host (witFt c.imports[j].2) ⟨j⟩)) →
      TRuns (List.foldlM (instantiateDef R ⟨0⟩ outer args) sc
          ((List.range' k m).map fun j => .canon (.lower j [])))
        cfg { sc with frame := { sc.frame with
          coreFuncs := sc.frame.coreFuncs ++ addrList Pf (List.range' k m) } }
        { cfg with store := { cfg.store with core := trampStore Pf c.imports } }
  | 0, k, sc, cfg, hkm, _, hcore, _ => by
    have hk : k = c.imports.length := hkm
    have hst : { cfg.store with core := trampStore Pf c.imports } = cfg.store := by
      rw [← List.take_length (l := c.imports), ← hk, ← hcore]
    have hfr : { sc with frame := { sc.frame with
        coreFuncs := sc.frame.coreFuncs ++ addrList Pf (List.range' k 0) } } = sc := by
      have e : sc.frame.coreFuncs ++ addrList Pf (List.range' k 0) = sc.frame.coreFuncs :=
        List.append_nil _
      rw [e]
      obtain ⟨⟨⟩, _⟩ := sc
      rfl
    rw [hst, hfr]
    exact TRuns.foldlM_nil sc cfg
  | m + 1, k, sc, cfg, hkm, hf, hcore, hs => by
    have hk : k < c.imports.length := by omega
    have r₁ := lower_step (R := R) (outer := outer) (args := args) har sc cfg k hk (hf k hk)
      hcore (hs k hk)
    have r₂ := lowers_run har m (k + 1)
      { sc with frame := { sc.frame with coreFuncs := sc.frame.coreFuncs ++ ([k] : List (core3P Pf).FuncAddr) } }
      { cfg with store := { cfg.store with core := trampStore Pf (c.imports.take (k + 1)) } }
      (by omega) hf rfl hs
    have hfr : sc.frame.coreFuncs ++ ([k] : List (core3P Pf).FuncAddr) ++
        addrList Pf (List.range' (k + 1) m) = sc.frame.coreFuncs ++ addrList Pf (List.range' k (m + 1)) :=
      List.append_assoc _ _ _
    have key : { sc with frame := { sc.frame with
                   coreFuncs := sc.frame.coreFuncs ++ addrList Pf (List.range' k (m + 1)) } } =
        { sc with frame := { sc.frame with
            coreFuncs := sc.frame.coreFuncs ++ ([k] : List (core3P Pf).FuncAddr) ++
              addrList Pf (List.range' (k + 1) m) } } := by
      rw [hfr]
    rw [key]
    exact TRuns.foldlM_cons r₁ r₂

/-! ## The core instances -/

/-- The inline core instance exporting core functions `0, …, n - 1` under the names `ps`. -/
theorem coreExports_run (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ)
    (ps : CoreIface) (hcf : sc.frame.coreFuncs = List.range ps.length) :
    TRuns (instantiateDef R inst outer args sc
        (.coreInstance (.exports (ps.mapIdx fun k p => (p.1, ⟨.func, k⟩))))) cfg
      { sc with frame := { sc.frame with
        coreInstances := sc.frame.coreInstances ++
                           ([envExports ps] : List (List (String × (core3P Pf).ExternVal))) } } cfg := by
  have hm : (ps.mapIdx fun k p => (p.1, (⟨.func, k⟩ : Syntax.SortIdx Syntax.CoreSort))).mapM
      (fun (x : String × Syntax.SortIdx Syntax.CoreSort) =>
        (x.1, ·) <$> externAt? sc.frame x.2) = some (envExports ps) := by
    refine mapM_eq_some_of_getElem (List.length_mapIdx.trans List.length_mapIdx.symm)
      fun i hi => ?_
    have hi' : i < ps.length := by simpa using hi
    simp only [List.getElem_mapIdx, envExports, externAt?, Frame.get?, Frame.coreFunc?, hcf]
    erw [List.getElem?_range hi', List.getElem_mapIdx]
    rfl
  simp only [instantiateDef, hm, need, orTrap, pure_bind, pushEntry, Frame.push]
  exact TRuns.pure _ _

/-- `core instance (instantiate 0 (with "env" 0))` of a start-free instantiation. -/
theorem instantiateEnv_run (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ)
    {m : Silmaril.Wasm.Module} {xas : List (core3P Pf).ExternVal}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hm : sc.frame.coreModules = [m])
    (himp : coreImportsFor? cfg.store.core m [("env", 0)] sc.frame = some xas)
    (hp : (core3P Pf).prepare? cfg.store.core m xas = some (cs, ci, none)) :
    TRuns (instantiateDef R inst outer args sc (.coreInstance (.instantiate 0 [("env", 0)])))
      cfg { sc with frame := { sc.frame with
        coreInstances := sc.frame.coreInstances ++ [(core3P Pf).exports ci] } }
      { cfg with store := setCoreSt cs cfg.store } := by
  have hmod : sc.frame.coreModule? 0 = some m := by rw [Frame.coreModule?, hm]; rfl
  have hc : TRuns (instantiateCore inst sc.frame 0 [("env", 0)] : P (core3P Pf) σ _) cfg
      ((core3P Pf).exports ci) { cfg with store := setCoreSt cs cfg.store } := by
    unfold instantiateCore
    rw [hmod]
    refine (TRuns.pure _ cfg).bind ((TRuns.getStore cfg).bind ?_)
    rw [himp]
    refine (TRuns.pure _ cfg).bind ?_
    dsimp only
    rw [hp]
    exact (TRuns.modifyStore (f := setCoreSt cs) (fun _ => rfl) cfg).bind (TRuns.pure _ _)
  exact hc.bind (TRuns.pure _ _)

end Silmaril.Proofs.Wasm.Component.Reference
