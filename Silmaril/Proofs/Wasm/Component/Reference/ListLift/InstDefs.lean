module

public import Silmaril.Proofs.Wasm.Component.Reference.ListLift.InstTypes

/-!
# Instantiating the definitions of `ListComp.toRef`

The definitions of `ListComp.toRef` run silently (`TRuns`) from the empty frame:

* the core module and the core instance (`instDef_coreModule`, `instDef_coreInstance`);
* `alias core export 0 memName (core memory)`: core memory `0` is memory address `memIdx`
  (`instDef_aliasMem`); the allocator alias and the aliases of the lifted core functions
  (`aliases_eq`), so that core function `0` is the allocator and core function `i + 1` the core
  function of export `i`;
* the type definitions (`typeDefs_run`);
* `canon lift (core func i+1) (memory 0) (realloc 0) (type t)`: the options resolve to memory
  address `memIdx` and the allocator's address, and each lift allocates the next component function
  (`instDef_liftL`, `lifts_run`);
* the exports of the lifted functions (`exports_eq`).

`toRefDefs_runL` assembles them.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.ListLift
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.DefValType)
open Silmaril.Wasm.Numerics (Profile)

/-! ## The shape of `toRef` -/

/-- The `canon lift` of export `i` (core function `i + 1`) at function type `t`. -/
def liftDefL {M : Type} (p : (ListExport × Nat) × Nat) : Syntax.Definition M :=
  .canon (.lift (p.1.2 + 1) [.memory 0, .realloc 0] p.2)

/-- The export of component function `i` under the name of export `x`. -/
def exportDefL {M : Type} (p : ListExport × Nat) : Syntax.Definition M :=
  .export_ { name := p.1.name } ⟨.func, p.2⟩ none

/-- The prefix of `toRef`: the core module, the core instance and the aliases of the memory and
the allocator. -/
def prefixDefsL (c : ListComp) : List (Syntax.Definition Silmaril.Wasm.Module) :=
  [.coreModule c.mod, .coreInstance (.instantiate 0 []),
    .alias (.coreExport 0 c.memName .memory), .alias (.coreExport 0 c.reallocName .func)]

theorem toRef_eq (c : ListComp) :
    c.toRef = prefixDefsL c ++ c.exports.map (fun x => .alias (.coreExport 0 x.core .func)) ++
      ListComp.typeDefs c.exports 0 ++
      (c.exports.zipIdx.zip (ListComp.funcTypeIdx c.exports 0)).map liftDefL ++
      c.exports.zipIdx.map exportDefL := by
  unfold ListComp.toRef
  congr 2

theorem NoImport.map {M α : Type} (L : List α) (g : α → Syntax.Definition M)
    (h : ∀ a n x, g a ≠ .import_ n x) : NoImport (L.map g) := by
  intro d hd
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hd
  exact h a

/-! ## Single definitions -/

section Generic

variable {E : CoreEngine} {σ : Type} [∀ a b, Decidable (E.ExternSub a b)] {R : Recurse E σ}
  {inst : InstId} {outer : List (Frame E)} {args : Exports E}

/-- A definition without a machine operation, then the others. -/
theorem foldlM_cons_pure {sc sc₁ : Scope E} {d : Syntax.Definition E.Module}
    {ds : List (Syntax.Definition E.Module)}
    (h : instantiateDef R inst outer args sc d = (Pure.pure sc₁ : P E σ (Scope E))) :
    (d :: ds).foldlM (instantiateDef R inst outer args) sc =
      ds.foldlM (instantiateDef R inst outer args) sc₁ := by
  rw [List.foldlM_cons, h, pure_bind]

/-- `alias core export` of a memory. -/
theorem instDef_aliasMem (sc : Scope E) {i : Nat} {name : String}
    {es : List (String × E.ExternVal)} {x : E.ExternVal} {a : E.MemAddr}
    (hi : sc.frame.coreInstance? i = some es) (hl : lookupExport? es name = some x)
    (hx : E.asMemory? x = some a) :
    instantiateDef R inst outer args sc (.alias (.coreExport i name .memory)) =
      (Pure.pure { sc with frame := { sc.frame with coreMems := sc.frame.coreMems ++ [x] } } :
        P E σ (Scope E)) := by
  simp only [instantiateDef, hi, pure_bind, hl, need, orTrap, Entry.ofExtern?, hx,
    Option.map_some, pushEntry, Frame.push]

/-- The aliases of the lifted core functions append their addresses. -/
theorem aliases_eq (es₀ : List (String × E.ExternVal)) (addr : String → E.FuncAddr) :
    ∀ (xs : List ListExport) (sc : Scope E), sc.frame.coreInstance? 0 = some es₀ →
      (∀ x ∈ xs, ∃ v, lookupExport? es₀ x.core = some v ∧ E.asFunc? v = some (addr x.core)) →
      (xs.map fun x => (.alias (.coreExport 0 x.core .func) :
          Syntax.Definition E.Module)).foldlM (instantiateDef R inst outer args) sc =
        (Pure.pure { sc with frame := { sc.frame with
          coreFuncs := sc.frame.coreFuncs ++ xs.map fun x => addr x.core } } : P E σ (Scope E))
  | [], sc, _, _ => by
    simp only [List.map_nil, List.append_nil, List.foldlM_nil]
    rcases sc with ⟨⟨⟩, _⟩
    rfl
  | x :: xs, sc, hi, hl => by
    obtain ⟨v, hv, ha⟩ := hl x List.mem_cons_self
    rw [List.map_cons, foldlM_cons_pure (instDef_alias sc hi hv ha),
      aliases_eq es₀ addr xs
        { sc with frame := { sc.frame with coreFuncs := sc.frame.coreFuncs ++ [addr x.core] } } hi
        (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

/-- `canon lift` with the options `(memory 0) (realloc 0)` allocates the lifted function with
the memory and the allocator of core memory `0` and core function `0`. -/
theorem instDef_liftL (sc : Scope E) {cf ft : Nat} {a ra : E.FuncAddr} {x : E.ExternVal}
    {ma : E.MemAddr} {t : Types.FuncType RtId} (ha : sc.frame.coreFuncs[cf]? = some a)
    (ht : sc.frame.types[ft]? = some (.func t))
    (hm : sc.frame.coreMems[0]? = some x) (hx : E.asMemory? x = some ma)
    (hr : sc.frame.coreFuncs[0]? = some ra) :
    instantiateDef R inst outer args sc (.canon (.lift cf [.memory 0, .realloc 0] ft)) =
      (allocFunc (.lifted a t { memory := some ma, realloc := some ra } inst) >>= fun fid =>
        Pure.pure { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [fid] } } :
        P E σ (Scope E)) := by
  have hr' : resolveLift? sc.frame cf [.memory 0, .realloc 0] ft =
      some (a, t, { memory := some ma, realloc := some ra }) := by
    simp [resolveLift?, Frame.coreFunc?, ha, funcTypeAt?, Frame.type?, ht, resolveOpts?,
      canonOptKind, applyOpt, Frame.memAddr?, Frame.coreMem?, hm, hx, hr]
  simp only [instantiateDef, hr', need, orTrap, pushEntry, Frame.push]
  rfl

end Generic

/-! ## The lifts and the exports over `core3P` -/

section Core3P

variable {Pf : Profile} {σ : Type} {R : Recurse (core3P Pf) σ} {inst : InstId}
  {outer : List (Frame (core3P Pf))} {args : Exports (core3P Pf)}

/-- The `canon lift` of export `k` allocates component function `k`. -/
theorem lift_runL (sc : Scope (core3P Pf)) (cfg : Machine.Config (core3P Pf) σ)
    {k ft a ma ra : Nat} {t : Types.FuncType RtId} (hs : cfg.store.funcs.length = k)
    (ha : sc.frame.coreFuncs[k + 1]? = some a) (ht : sc.frame.types[ft]? = some (.func t))
    (hm : sc.frame.coreMems[0]? = some (Silmaril.Wasm.Execution.Core.ExternAddr.mem ma))
    (hr : sc.frame.coreFuncs[0]? = some ra) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lift (k + 1) [.memory 0, .realloc 0] ft)))
      cfg { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨k⟩] } }
      { cfg with store := (ArenaOps.allocSt ArenaField.funcs
          (.lifted a t { memory := some ma, realloc := some ra } inst) cfg.store) } := by
  rw [instDef_liftL sc ha ht hm rfl hr, ← hs]
  exact (TRuns.allocObj _ (fun _ _ => rfl) _ cfg).bind (TRuns.pure _ _)

/-- The lifted functions of the exports, with the memory `ma` and the allocator `ra`. -/
def liftedListL (addr : String → Nat) (ma ra : Nat) (inst : InstId) (xs : List ListExport) :
    List (CFuncInst (core3P Pf)) :=
  xs.map fun x => .lifted (addr x.core) (liftedFtL x)
    { memory := some (show (core3P Pf).MemAddr from ma), realloc := some ra } inst

/-- **The lifts run silently**, allocating one component function per export. -/
theorem lifts_run (ma ra : Nat) (addr : String → Nat) :
    ∀ (xs : List ListExport) (k : Nat) (ts : List Nat) (sc : Scope (core3P Pf))
      (cfg : Machine.Config (core3P Pf) σ),
      sc.frame.coreMems[0]? = some (Silmaril.Wasm.Execution.Core.ExternAddr.mem ma) →
      sc.frame.coreFuncs[0]? = some ra →
      (∀ j (hj : j < xs.length), sc.frame.coreFuncs[k + j + 1]? = some (addr xs[j].core)) →
      List.Forall₂ (fun t x => sc.frame.types[t]? = some (.func (liftedFtL x))) ts xs →
      cfg.store.funcs.length = k →
      ∃ sc', TRuns ((((xs.zipIdx k).zip ts).map liftDefL).foldlM
          (instantiateDef R inst outer args) sc) cfg sc'
          { cfg with store := { cfg.store with
              funcs := cfg.store.funcs ++ liftedListL (Pf := Pf) addr ma ra inst xs } } ∧
        sc'.exports = sc.exports ∧
        sc'.frame.funcs = sc.frame.funcs ++ (List.range' k xs.length).map FuncId.mk
  | [], k, ts, sc, cfg, _, _, _, hts, _ => by
    rw [List.forall₂_nil_right_iff.1 hts]
    refine ⟨sc, ?_, rfl, by simp⟩
    simp only [liftedListL, List.map_nil, List.append_nil]
    exact TRuns.foldlM_nil sc cfg
  | x :: xs, k, ts, sc, cfg, hm, hr, ha, hts, hs => by
    obtain ⟨t, ts', ht, hts', rfl⟩ := List.forall₂_cons_right_iff.1 hts
    have ha₀ : sc.frame.coreFuncs[k + 1]? = some (addr x.core) := ha 0 (by simp)
    have h₁ := lift_runL (R := R) (inst := inst) (outer := outer) (args := args) sc cfg hs ha₀ ht
      hm hr
    have hs₁ : (cfg.store.funcs ++ liftedListL (Pf := Pf) addr ma ra inst [x]).length = k + 1 := by
      rw [List.length_append, hs]
      rfl
    obtain ⟨sc₂, h₂, hx₂, hf₂⟩ := lifts_run ma ra addr xs (k + 1) ts'
      { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨k⟩] } }
      { cfg with store := { cfg.store with
          funcs := cfg.store.funcs ++ liftedListL (Pf := Pf) addr ma ra inst [x] } }
      hm hr (fun j hj => by
        have := ha (j + 1) (by simp; omega)
        rw [show k + (j + 1) + 1 = k + 1 + j + 1 by omega] at this
        simpa using this) hts' hs₁
    refine ⟨sc₂, ?_, hx₂, ?_⟩
    · rw [List.zipIdx_cons, List.zip_cons_cons, List.map_cons]
      have e : liftedListL (Pf := Pf) addr ma ra inst (x :: xs) =
          liftedListL (Pf := Pf) addr ma ra inst [x] ++ liftedListL (Pf := Pf) addr ma ra inst xs :=
        rfl
      rw [e, ← List.append_assoc]
      exact TRuns.foldlM_cons h₁ h₂
    · rw [hf₂]
      simp [List.range'_succ, List.append_assoc]

/-- **The exports of the lifted functions record them**, without a machine operation. -/
theorem exports_eq :
    ∀ (xs : List ListExport) (k : Nat) (sc : Scope (core3P Pf)),
      (∀ j, k ≤ j → j < k + xs.length → sc.frame.funcs[j]? = some ⟨j⟩) →
      ∃ sc', ((xs.zipIdx k).map exportDefL).foldlM (instantiateDef R inst outer args) sc =
          (Pure.pure sc' : P (core3P Pf) σ (Scope (core3P Pf))) ∧
        funcExports sc'.exports =
          funcExports sc.exports ++ xs.mapIdx (fun i x => (x.name, (⟨k + i⟩ : FuncId)))
  | [], k, sc, _ => ⟨sc, rfl, by simp⟩
  | x :: xs, k, sc, hf => by
    have hk : sc.frame.funcs[k]? = some ⟨k⟩ := hf k (Nat.le_refl _) (by simp)
    have h₁ := instDef_funcExport (R := R) (inst := inst) (outer := outer) (args := args)
      (σ := σ) (nm := { name := x.name }) sc hk
    have hlen : k < sc.frame.funcs.length := (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨sc₂, h₂, hx₂⟩ := exports_eq xs (k + 1)
      { frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨k⟩] },
        exports := sc.exports ++ [(x.name, .func ⟨k⟩)] }
      (fun j hj₁ hj₂ => by
        have hj := hf j (by omega) (by simp; omega)
        have hjl : j < sc.frame.funcs.length := (List.getElem?_eq_some_iff.1 hj).1
        show (sc.frame.funcs ++ [⟨k⟩])[j]? = _
        rw [List.getElem?_append_left hjl, hj])
    refine ⟨sc₂, ?_, ?_⟩
    · rw [List.zipIdx_cons, List.map_cons]
      exact (foldlM_cons_pure h₁).trans h₂
    · have e : (fun i (y : ListExport) => (y.name, (⟨k + 1 + i⟩ : FuncId))) =
          (fun i y => (y.name, ⟨k + (i + 1)⟩)) := by
        funext i y
        rw [Nat.add_assoc, Nat.add_comm 1 i]
      rw [hx₂, e, funcExports_append_func, List.mapIdx_cons, List.append_assoc, Nat.add_zero]
      rfl

/-! ## All definitions -/

/-- The frame after the core module, the core instance, the memories `mems` and the core
functions `funcs`. -/
noncomputable def prefixFrameL (c : ListComp) (es₀ : List (String × (core3P Pf).ExternVal))
    (mems : List (core3P Pf).ExternVal) (funcs : List Nat) : Frame (core3P Pf) :=
  { (Frame.empty : Frame (core3P Pf)) with
    coreModules := [c.mod]
    coreInstances := [es₀]
    coreMems := mems
    coreFuncs := funcs }

/-- The scope after the core module, the core instance and the memory and allocator aliases. -/
noncomputable def prefixScopeL (c : ListComp) (es₀ : List (String × (core3P Pf).ExternVal))
    (ra : Nat) : Scope (core3P Pf) :=
  { frame := prefixFrameL c es₀ [Silmaril.Wasm.Execution.Core.ExternAddr.mem c.memIdx] [ra] }

/-- **The definitions of `c.toRef` run silently** from a store with the empty core store and
no component function: the core instance, then the lifted functions of the exports. -/
theorem toRefDefs_runL {c : ListComp} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst}
    (hF : CoreFactsL c I cs ci) (hi : c.Inst I) (cfg : Machine.Config (core3P Pf) σ)
    (hcore : cfg.core = (core3P Pf).empty _) (hfuncs : cfg.store.funcs = []) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) {} c.toRef) cfg sc'
        { cfg with core := cs, store := (liftStore cfg.store
            (liftedListL (Pf := Pf) (c.coreAddr I) c.memIdx (c.coreAddr I c.reallocName) inst
              c.exports)) } ∧
      funcExports sc'.exports = exportMapL c ∧ NoImport c.toRef := by
  have hp : (core3P Pf).prepare? cfg.core c.mod [] = some (cs, ci, none) := by
    rw [hcore]
    exact hF.prepare
  set ra := c.coreAddr I c.reallocName
  set es₀ := (core3P Pf).exports ci
  have h₁ := instDef_coreModule (R := R) (inst := inst) (outer := outer) (args := args) {} c.mod
  have h₂ := instDef_coreInstance (R := R) (inst := inst) (outer := outer) (args := args)
    { frame := { (Frame.empty : Frame (core3P Pf)) with coreModules := [] ++ [c.mod] },
      exports := [] } cfg rfl hF.imports hp
  have h₃ := instDef_aliasMem (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    { frame := prefixFrameL c es₀ [] [] } (i := 0) rfl hF.mem
    (show (core3P Pf).asMemory? (Silmaril.Wasm.Execution.Core.ExternAddr.mem c.memIdx) =
      some c.memIdx from rfl)
  have h₄ := instDef_alias (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    { frame := prefixFrameL c es₀ [Silmaril.Wasm.Execution.Core.ExternAddr.mem c.memIdx] [] }
    (i := 0) rfl
    (hF.func _ hi.reallocFunc) (rfl : (core3P Pf).asFunc? (.func ra) = some ra)
  have h₅ := aliases_eq (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ) es₀
    (c.coreAddr I) c.exports (prefixScopeL c es₀ ra) rfl
    (fun x hx => ⟨_, hF.func _ (hi.coreFuncs x hx), rfl⟩)
  obtain ⟨sc₆, n₆, hP₆, hR₆⟩ := typeDefs_run (R := R) (inst := inst) (outer := outer)
    (args := args) c.exports
    { prefixScopeL c es₀ ra with frame := { (prefixScopeL c es₀ ra).frame with
        coreFuncs := List.append (prefixScopeL c es₀ ra).frame.coreFuncs
          (c.exports.map fun x => c.coreAddr I x.core) } }
  obtain ⟨new, hf₆⟩ := hP₆.2.1
  obtain ⟨sc₇, hr₇, hx₇, hf₇⟩ := lifts_run (R := R) (inst := inst) (outer := outer)
    (args := args) c.memIdx ra (c.coreAddr I) c.exports 0 (ListComp.funcTypeIdx c.exports 0) sc₆
    { cfg with core := cs }
    (by rw [hf₆]; rfl) (by rw [hf₆]; rfl)
    (fun j hj => by
      rw [hf₆]
      show ([ra] ++ c.exports.map fun x => c.coreAddr I x.core)[0 + j + 1]? = _
      simp [List.getElem?_eq_getElem hj])
    hR₆ (by show cfg.store.funcs.length = 0; rw [hfuncs]; rfl)
  obtain ⟨sc₈, h₈, hx₈⟩ := exports_eq (R := R) (inst := inst) (outer := outer) (args := args)
    (σ := σ) c.exports 0 sc₇ (fun j _ hj => by
      rw [hf₇, hf₆]
      show ([] ++ (List.range' 0 c.exports.length).map FuncId.mk)[j]? = _
      simp only [List.nil_append, List.getElem?_map]
      rw [List.getElem?_range' (by omega)]
      simp)
  have hx₆ : funcExports sc₆.exports = [] := hP₆.2.2.2.1
  refine ⟨sc₈, ?_, ?_, ?_⟩
  · rw [toRef_eq]
    refine TRuns.foldlM_append (TRuns.foldlM_append (TRuns.foldlM_append (TRuns.foldlM_append
      (TRuns.foldlM_cons (TRuns.of_eq cfg h₁) (TRuns.foldlM_cons h₂
        (TRuns.foldlM_cons (TRuns.of_eq _ h₃) (TRuns.foldlM_cons (TRuns.of_eq _ h₄)
          (TRuns.foldlM_nil _ _))))) (TRuns.of_eq _ h₅)) (TRuns.ofPure hP₆ _)) hr₇)
      (TRuns.of_eq _ h₈)
  · rw [hx₈, hx₇, hx₆, List.nil_append, exportMapL]
    simp only [Nat.zero_add]
  · have hpre : NoImport (prefixDefsL c) := by
      intro d hd
      simp only [prefixDefsL, List.mem_cons, List.mem_nil_iff, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> intro _ _ e <;> cases e
    rw [toRef_eq]
    exact NoImport.append (NoImport.append (NoImport.append (NoImport.append hpre
      (NoImport.map _ _ fun _ _ _ e => by cases e)) hP₆.2.2.2.2)
      (NoImport.map _ _ fun _ _ _ e => by cases e)) (NoImport.map _ _ fun _ _ _ e => by cases e)

end Core3P

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
