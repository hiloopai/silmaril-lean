module

public import Silmaril.Proofs.Wasm.Component.Param.Core3R.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.InstRun
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The instantiation phase over `core3R P V I`

The `core3P`-specific sections of `Silmaril.Proofs.Wasm.Component.Reference.InstExport` (section
`Core3P`) and `Silmaril.Proofs.Wasm.Component.Reference.InstRun` (section `Core3P`), with
`core3P P` replaced by `core3R P V IR` (provenance: copies of these sections; the proofs are
unchanged). Instantiating `Simple.toRef` runs no core code, so the internal step `IR` plays no
part: `instPhase : InstPhase` holds for every `V` and `IR`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.Core3R

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.DefValType)

section Core3P

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

variable (Pf : Silmaril.Wasm.Numerics.Profile)

theorem exportDefs_eq (m : NumModule) (i : Nat) (x : SimpleExport) (n : Nat) :
    (Simple.exportDefs m i x n : List (Syntax.Definition (core3R Pf V IR).Module) × Nat) =
      ((emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.1 ++
        (emitTys (M := (core3R Pf V IR).Module) x.ty.results
          (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.2).2.1 ++
        [.type (.func { params := labels "a" (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).1,
                        result := (emitTys (M := (core3R Pf V IR).Module) x.ty.results
                          (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.2).1.head? }),
         .alias (.coreExport 0 (((m.exports[x.core]?).map (·.1)).getD "") .func),
         .canon (.lift i [] (emitTys (M := (core3R Pf V IR).Module) x.ty.results
           (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.2).2.2),
         .export_ { name := x.name } ⟨.func, 2 * i⟩ none],
        (emitTys (M := (core3R Pf V IR).Module) x.ty.results
          (emitTys (M := (core3R Pf V IR).Module) x.ty.params n).2.2).2.2 + 1) := by
  simp only [Simple.exportDefs]
  rfl

variable {Pf} {σ : Type}
  {R : Recurse (core3R Pf V IR) σ} {inst : InstId} {outer : List (Frame (core3R Pf V IR))}
  {args : Exports (core3R Pf V IR)}

theorem funcExports_append_func (l : Exports (core3R Pf V IR)) (n : String) (f : FuncId) :
    funcExports (l ++ [(n, .func f)]) = funcExports l ++ [(n, f)] := by
  simp only [funcExports, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]

/-- The four definitions after the type definitions of an export are no imports. -/
theorem noImport_tail {M : Type} (d₁ d₂ d₃ : Syntax.Definition M) (nm : Syntax.ExternName)
    (si : Syntax.SortIdx Syntax.Sort_) (h₁ : ∀ n x, d₁ ≠ .import_ n x)
    (h₂ : ∀ n x, d₂ ≠ .import_ n x) (h₃ : ∀ n x, d₃ ≠ .import_ n x) :
    NoImport [d₁, d₂, d₃, .export_ nm si none] := by
  intro d hd
  rcases List.mem_cons.1 hd with rfl | hd
  · exact h₁
  rcases List.mem_cons.1 hd with rfl | hd
  · exact h₂
  rcases List.mem_cons.1 hd with rfl | hd
  · exact h₃
  rw [List.mem_singleton.1 hd]
  intro _ _ e
  cases e

/-- The `canon lift` of export `i` allocates component function `i`. -/
theorem lift_run (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ) {i ft a : Nat}
    {t : Types.FuncType RtId} (hs : cfg.store.funcs.length = i)
    (ha : sc.frame.coreFuncs[i]? = some a) (ht : sc.frame.types[ft]? = some (.func t)) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lift i [] ft))) cfg
      { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨i⟩] } }
      { cfg with store := ArenaOps.allocSt ArenaField.funcs (.lifted a t {} inst) cfg.store } := by
  rw [instDef_lift sc ha ht, ← hs]
  exact (TRuns.allocObj _ (fun _ _ => rfl) _ cfg).bind (TRuns.pure _ _)

/-- The frame after the function type, the alias and the lift of an export. -/
def liftFrame (f : Frame (core3R Pf V IR)) (t : Types.FuncType RtId) (a : (core3R Pf V IR).FuncAddr)
    (i : Nat) :
    Frame (core3R Pf V IR) :=
  { f with types := f.types ++ [.func t], coreFuncs := f.coreFuncs ++ [a],
           funcs := f.funcs ++ [⟨i⟩] }

/-- **The definitions of one export run silently**: from the frame invariant of export `i`,
they allocate the lifted function `i` and record its export. -/
theorem exportDefs_run (m : NumModule) (i : Nat) (x : SimpleExport) (sc : Scope (core3R Pf V IR))
    (cfg : Machine.Config (core3R Pf V IR) σ) {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)}
    {a : (core3R Pf V IR).FuncAddr} (hinv : ExpInv es₀ i sc.frame) (hs : cfg.store.funcs.length = i)
    (hlk : lookupExport? es₀ (((m.exports[x.core]?).map (·.1)).getD "") = some (.func a)) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        (Simple.exportDefs m i x sc.frame.types.length).1) cfg sc'
        { cfg with store :=
            ArenaOps.allocSt ArenaField.funcs (.lifted a (liftedFt x) {} inst) cfg.store } ∧
      ExpInv es₀ (i + 1) sc'.frame ∧
      sc'.frame.types.length = (Simple.exportDefs m i x sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports ++ [(x.name, ⟨i⟩)] ∧
      NoImport (Simple.exportDefs m i x sc.frame.types.length).1 := by
  obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.params sc
  obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.results sc₁
  have hl₁ : sc₁.frame.types.length =
      (emitTys (M := (core3R Pf V IR).Module) x.ty.params sc.frame.types.length).2.2 := hP₁.2.2.1
  have hl₂ : sc₂.frame.types.length =
      (emitTys (M := (core3R Pf V IR).Module) x.ty.results sc₁.frame.types.length).2.2 := hP₂.2.2.1
  rw [exportDefs_eq, ← hl₁, ← hl₂]
  have hinv₂ : ExpInv es₀ i sc₂.frame := hP₂.expInv (hP₁.expInv hinv)
  have hft : resolveFuncType? sc₂.frame
      { params := labels "a" (emitTys (M := (core3R Pf V IR).Module) x.ty.params
          sc.frame.types.length).1,
        result := (emitTys (M := (core3R Pf V IR).Module) x.ty.results
          sc₁.frame.types.length).1.head? } = some (liftedFt x) :=
    resolveFuncType_lifted (hR₁.imp fun _ _ h => h.mono hP₂.prefix) hR₂
  have h₃ := instDef_func (R := R) (inst := inst) (outer := outer) (args := args) sc₂ hft
  have hci : (Frame.coreInstance? { sc₂.frame with types := sc₂.frame.types ++
      [.func (liftedFt x)] } 0) = some es₀ := by
    show sc₂.frame.coreInstances[0]? = some es₀
    rw [hinv₂.ci]
    rfl
  have h₄ := instDef_alias (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    { sc₂ with frame := { sc₂.frame with types := sc₂.frame.types ++ [.func (liftedFt x)] } }
    hci hlk rfl
  have hcf : (sc₂.frame.coreFuncs ++ [a])[i]? = some a := by
    rw [List.getElem?_append_right (by rw [hinv₂.cf]), hinv₂.cf, Nat.sub_self]
    rfl
  have hty : (sc₂.frame.types ++ [.func (liftedFt x)])[sc₂.frame.types.length]? =
      some (.func (liftedFt x)) := by simp
  have h₅ := lift_run (R := R) (inst := inst) (outer := outer) (args := args)
    { sc₂ with frame := { sc₂.frame with
        types := sc₂.frame.types ++ [Types.TypeDef.func (liftedFt x)],
        coreFuncs := sc₂.frame.coreFuncs ++ [a] } } cfg hs hcf hty
  have hfn : (sc₂.frame.funcs ++ [(⟨i⟩ : FuncId)])[2 * i]? = some ⟨i⟩ := by
    rw [List.getElem?_append_right (by rw [hinv₂.fn]), hinv₂.fn, Nat.sub_self]
    rfl
  have h₆ := instDef_funcExport (R := R) (inst := inst) (outer := outer) (args := args) (σ := σ)
    (nm := { name := x.name })
    { sc₂ with frame := liftFrame sc₂.frame (liftedFt x) a i } hfn
  refine ⟨_, TRuns.foldlM_append (TRuns.foldlM_append (TRuns.ofPure hP₁ cfg)
    (TRuns.ofPure hP₂ cfg)) (TRuns.foldlM_cons (TRuns.of_eq cfg h₃)
    (TRuns.foldlM_cons (TRuns.of_eq cfg h₄) (TRuns.foldlM_cons h₅
    (TRuns.foldlM_cons (TRuns.of_eq _ h₆) (TRuns.foldlM_nil _ _))))), ?_, ?_, ?_, ?_⟩
  · exact ⟨hinv₂.ci, by simp [liftFrame, hinv₂.cf], by simp [liftFrame, hinv₂.fn]; omega⟩
  · simp [liftFrame]
  · have hx : funcExports sc₂.exports = funcExports sc.exports := hP₂.2.2.2.1.trans hP₁.2.2.2.1
    rw [funcExports_append_func, hx]
  · exact (hP₁.2.2.2.2.append hP₂.2.2.2.2).append
      (noImport_tail _ _ _ _ _ (fun _ _ e => by cases e) (fun _ _ e => by cases e)
        (fun _ _ e => by cases e))

theorem exportsDefs_cons (m : NumModule) (i : Nat) (x : SimpleExport) (xs : List SimpleExport)
    (n : Nat) :
    Simple.exportsDefs m i (x :: xs) n =
      (Simple.exportDefs m i x n).1 ++ Simple.exportsDefs m (i + 1) xs (Simple.exportDefs m i x n).2 := by
  simp only [Simple.exportsDefs]

/-- The lifted functions of the exports `xs`. -/
def liftedList (addr : Nat → (core3R Pf V IR).FuncAddr) (inst : InstId) (xs : List SimpleExport) :
    List (CFuncInst (core3R Pf V IR)) :=
  xs.map fun x => .lifted (addr x.core) (liftedFt x) {} inst

theorem liftedList_cons (addr : Nat → (core3R Pf V IR).FuncAddr) (inst : InstId) (x : SimpleExport)
    (xs : List SimpleExport) :
    liftedList addr inst (x :: xs) = liftedList addr inst [x] ++ liftedList addr inst xs := rfl

/-- The name of the core export lifted by `x`. -/
def coreName (m : NumModule) (x : SimpleExport) : String :=
  ((m.exports[x.core]?).map (·.1)).getD ""

theorem mapIdx_shift (xs : List SimpleExport) (i : Nat) :
    (xs.mapIdx fun k x => (x.name, (⟨i + 1 + k⟩ : FuncId))) =
      xs.mapIdx fun k x => (x.name, (⟨i + (k + 1)⟩ : FuncId)) := by
  congr 1
  funext k x
  rw [Nat.add_assoc, Nat.add_comm 1 k]

/-- **The definitions of all exports run silently**, appending the lifted functions to the
component functions and recording their exports. -/
theorem exportsDefs_run (m : NumModule) (addr : Nat → (core3R Pf V IR).FuncAddr)
    {es₀ : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} :
    ∀ (xs : List SimpleExport) (i : Nat) (sc : Scope (core3R Pf V IR))
      (cfg : Machine.Config (core3R Pf V IR) σ), ExpInv es₀ i sc.frame →
      cfg.store.funcs.length = i →
      (∀ x ∈ xs, lookupExport? es₀ (coreName m x) = some (.func (addr x.core))) →
      ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
          (Simple.exportsDefs m i xs sc.frame.types.length)) cfg sc'
          { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst xs } } ∧
        funcExports sc'.exports =
          funcExports sc.exports ++ xs.mapIdx (fun k x => (x.name, ⟨i + k⟩)) ∧
        NoImport (Simple.exportsDefs m i xs sc.frame.types.length)
  | [], i, sc, cfg, _, _, _ => by
    refine ⟨sc, ?_, by rw [List.mapIdx_nil, List.append_nil], fun _ h => by cases h⟩
    simp only [liftedList, List.map_nil, List.append_nil]
    exact TRuns.foldlM_nil sc cfg
  | x :: xs, i, sc, cfg, hinv, hs, hlk => by
    obtain ⟨sc₁, hr₁, hinv₁, hl₁, hx₁, hn₁⟩ := exportDefs_run (R := R) (inst := inst)
      (outer := outer) (args := args) m i x sc cfg hinv hs (hlk x List.mem_cons_self)
    have hs₁ : (cfg.store.funcs ++ liftedList addr inst [x]).length =
        i + 1 := by
      rw [List.length_append, hs]
      rfl
    obtain ⟨sc₂, hr₂, hx₂, hn₂⟩ := exportsDefs_run m addr xs (i + 1) sc₁
      { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst [x] } }
      hinv₁ hs₁
      (fun y hy => hlk y (List.mem_cons_of_mem _ hy))
    rw [exportsDefs_cons]
    refine ⟨sc₂, ?_, ?_, hn₁.append (hl₁ ▸ hn₂)⟩
    · rw [liftedList_cons, ← List.append_assoc]
      exact TRuns.foldlM_append hr₁ (hl₁ ▸ hr₂)
    · rw [hx₂, hx₁, List.mapIdx_cons, List.append_assoc, Nat.add_zero, mapIdx_shift]
      rfl

end Core3P

/-! ## The core instance -/

section Core3P

variable {V : Silmaril.Wasm.Module → Prop} {IR : {H : Type} → Cfg3 H → Cfg3 H → Prop}

variable {Pf : Silmaril.Wasm.Numerics.Profile} {σ : Type} {R : Recurse (core3R Pf V IR) σ}
  {inst : InstId} {outer : List (Frame (core3R Pf V IR))} {args : Exports (core3R Pf V IR)}

/-- `instantiateCore` of an import-free, start-free module: one store read and the update of
the core store. -/
theorem instantiateCore_run (f : Frame (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ)
    {m : Silmaril.Wasm.Module} {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))}
    {ci : (core3R Pf V IR).Inst} (hm : f.coreModules = [m])
    (himp : (core3R Pf V IR).importTypes m = [])
    (hp : (core3R Pf V IR).prepare? cfg.store.core m [] = some (cs, ci, none)) :
    TRuns (instantiateCore inst f 0 [] : P (core3R Pf V IR) σ _) cfg ((core3R Pf V IR).exports ci)
      { cfg with store := setCoreSt cs cfg.store } := by
  have hmod : f.coreModule? 0 = some m := by rw [Frame.coreModule?, hm]; rfl
  have himps : coreImportsFor? cfg.store.core m [] f = some [] := by
    unfold coreImportsFor?
    rw [himp]
    rfl
  unfold instantiateCore
  rw [hmod]
  refine (TRuns.pure _ cfg).bind ((TRuns.getStore cfg).bind ?_)
  rw [himps]
  refine (TRuns.pure _ cfg).bind ?_
  dsimp only
  rw [hp]
  exact (TRuns.modifyStore (f := setCoreSt cs) (fun _ => rfl) cfg).bind (TRuns.pure _ _)

theorem instDef_coreModule (sc : Scope (core3R Pf V IR)) (m : (core3R Pf V IR).Module) :
    instantiateDef R inst outer args sc (.coreModule m) =
      (Pure.pure { sc with frame := { sc.frame with coreModules := sc.frame.coreModules ++ [m] } } :
        P (core3R Pf V IR) σ (Scope (core3R Pf V IR))) := by
  simp only [instantiateDef, pushEntry, need, Frame.push, orTrap]
  rfl

/-- The frame after the core module and the core instance. -/
noncomputable def coreFrame (m : (core3R Pf V IR).Module) (es₀ : List (String × (core3R Pf V IR).ExternVal)) :
    Frame (core3R Pf V IR) :=
  { (Frame.empty : Frame (core3R Pf V IR)) with coreModules := [m], coreInstances := [es₀] }

/-- The core facts of `Simple.Inst`, over `core3R Pf V IR`. -/
structure CoreFacts (c : Simple) (I : Silmaril.Wasm.Game.ScalarInstance)
    (cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (ci : (core3R Pf V IR).Inst) : Prop where
  isInst : c.mod.IsInst I
  store : Store.mapH (fun _ => 0) cs = I.store
  imports : (core3R Pf V IR).importTypes c.mod.mod = []
  prepare : (core3R Pf V IR).prepare? ((core3R Pf V IR).empty _) c.mod.mod [] = some (cs, ci, none)
  lookup : ∀ x ∈ c.exports, lookupExport? ((core3R Pf V IR).exports ci) (coreName c.mod x) =
    some (.func (I.addrs.getD x.core 0))

/-- **The core facts hold** for a `Simple.Inst` component in the fragment. -/
theorem coreFacts {c : Simple} (hc : c.Good) (hi : c.Inst) :
    ∃ I cs ci, CoreFacts (Pf := Pf) (V := V) (IR := IR) c I cs ci := by
  obtain ⟨I, mt, cs, f', hI, hv, hmt, ho, hs, ha⟩ := inst_once
    (H := CanonHost (core3R Pf V IR)) (fun _ => 0) hi
  refine ⟨I, cs, f'.module, ⟨hI, hs, importTypes_core3R Pf hv hmt,
    prepare_core3R Pf hv hmt ho, fun x hx => ?_⟩⟩
  obtain ⟨n, hn⟩ := hc.core x hx
  have hname : coreName c.mod x = n := by rw [coreName, hn]; rfl
  rw [hname, exports_core3R]
  exact lookup_funcExport hi hv ho ha hn

/-- The `core instance` definition of `Simple.toRef`. -/
theorem instDef_coreInstance (sc : Scope (core3R Pf V IR)) (cfg : Machine.Config (core3R Pf V IR) σ)
    {m : (core3R Pf V IR).Module} {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))}
    {ci : (core3R Pf V IR).Inst} (hm : sc.frame.coreModules = [m])
    (himp : (core3R Pf V IR).importTypes m = [])
    (hp : (core3R Pf V IR).prepare? cfg.store.core m [] = some (cs, ci, none)) :
    TRuns (instantiateDef R inst outer args sc (.coreInstance (.instantiate 0 [])))
      cfg { sc with frame := { sc.frame with
        coreInstances := sc.frame.coreInstances ++ [(core3R Pf V IR).exports ci] } }
      { cfg with store := setCoreSt cs cfg.store } :=
  (instantiateCore_run (inst := inst) sc.frame cfg hm himp hp).bind (TRuns.pure _ _)

/-- The store after the core instance and the lifted functions `fs`. -/
noncomputable def liftStore (cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))) (s : CStore (core3R Pf V IR))
    (fs : List (CFuncInst (core3R Pf V IR))) : CStore (core3R Pf V IR) :=
  { setCoreSt cs s with funcs := s.funcs ++ fs }

/-- **The definitions of `c.toRef` run silently** from a store with the empty core store and
no component function: the core instance, then the lifted functions of the exports. -/
theorem toRefDefs_run {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hF : CoreFacts c I cs ci) (cfg : Machine.Config (core3R Pf V IR) σ)
    (hcore : cfg.store.core = (core3R Pf V IR).empty _) (hfuncs : cfg.store.funcs = []) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) {} c.toRef) cfg sc'
        { cfg with store :=
            liftStore cs cfg.store (liftedList (fun k => I.addrs.getD k 0) inst c.exports) } ∧
      funcExports sc'.exports = c.exports.mapIdx (fun k x => (x.name, ⟨0 + k⟩)) ∧
      NoImport c.toRef := by
  have hp : (core3R Pf V IR).prepare? cfg.store.core c.mod.mod [] = some (cs, ci, none) := by
    rw [hcore]
    exact hF.prepare
  have h₁ := instDef_coreModule (R := R) (inst := inst) (outer := outer) (args := args) {}
    c.mod.mod
  have h₂ := instDef_coreInstance (R := R) (inst := inst) (outer := outer) (args := args)
    { frame := { (Frame.empty : Frame (core3R Pf V IR)) with coreModules := [] ++ [c.mod.mod] },
      exports := [] } cfg rfl hF.imports hp
  have hinv : ExpInv ((core3R Pf V IR).exports ci) 0 (coreFrame c.mod.mod ((core3R Pf V IR).exports ci)) :=
    ⟨rfl, rfl, rfl⟩
  have hs : (setCoreSt cs cfg.store).funcs.length = 0 := by
    show cfg.store.funcs.length = 0
    rw [hfuncs]
    rfl
  obtain ⟨sc', hr, hx, hn⟩ := exportsDefs_run (R := R) (inst := inst) (outer := outer)
    (args := args) c.mod (fun k => I.addrs.getD k 0) c.exports 0
    { frame := coreFrame c.mod.mod ((core3R Pf V IR).exports ci), exports := [] }
    { cfg with store := setCoreSt cs cfg.store } hinv hs hF.lookup
  have hn' : NoImport c.toRef := by
    unfold Simple.toRef
    refine NoImport.append (fun d hd => ?_) hn
    rcases List.mem_cons.1 hd with rfl | hd
    · intro _ _ e
      cases e
    · rw [List.mem_singleton.1 hd]
      intro _ _ e
      cases e
  refine ⟨sc', ?_, hx, hn'⟩
  unfold Simple.toRef
  exact TRuns.foldlM_append (TRuns.foldlM_cons (TRuns.of_eq cfg h₁)
    (TRuns.foldlM_cons h₂ (TRuns.foldlM_nil _ _))) hr

theorem trapIf_run {b : Bool} (hb : b = false) (r : TrapReason)
    (m : Machine.Config (core3R Pf V IR) σ) : TRuns (trapIf b r : P (core3R Pf V IR) σ Unit) m () m := by
  subst hb
  exact TRuns.pure () m

theorem checkImport_run {r : Except String Unit} (hr : r = .ok ())
    (m : Machine.Config (core3R Pf V IR) σ) :
    TRuns (checkImport r : P (core3R Pf V IR) σ Unit) m () m := by
  subst hr
  exact TRuns.pure () m

/-- The store after root instantiation: instance `0`, the core store and the lifted
functions. -/
noncomputable def instStore (cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR)))
    (s : CStore (core3R Pf V IR)) (addr : Nat → Nat) (c : Simple) : CStore (core3R Pf V IR) :=
  liftStore cs (ArenaOps.allocSt ArenaField.insts {} s) (liftedList addr ⟨0⟩ c.exports)

/-- **Root instantiation of `c.toRef` runs silently**: the root checks pass, instance `0` is
allocated, and the definitions run (`toRefDefs_run`). -/
theorem rootCall_run {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hF : CoreFacts c I cs ci) (cfg : Machine.Config (core3R Pf V IR) σ)
    (hcore : cfg.store.core = (core3R Pf V IR).empty _) (hfuncs : cfg.store.funcs = [])
    (hinsts : cfg.store.insts = []) :
    ∃ es, funcExports es = exportMap c ∧
      TRuns (instantiateRootCall c.toRef [] : P (core3R Pf V IR) σ _) cfg (⟨0⟩, es)
        { cfg with store := instStore cs cfg.store (fun k => I.addrs.getD k 0) c } := by
  obtain ⟨sc', hr, hx, hn⟩ := toRefDefs_run (R := callRecurse) (inst := ⟨0⟩) (outer := [])
    (args := []) hF { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store }
    hcore hfuncs
  have hac : argsComplete c.toRef ([] : Exports (core3R Pf V IR)) = true := by
    rw [argsComplete, importNames_nil hn]
    rfl
  have hpre : ∀ s : CStore (core3R Pf V IR), precheckImports s [] Frame.empty c.toRef = .ok () :=
    fun s => precheckImports_ok s [] _ _ hn
  have hid : (ArenaField.insts (E := core3R Pf V IR)).mkId (ArenaField.insts.size cfg.store) =
      (⟨0⟩ : InstId) := by
    simp only [ArenaField.size, ArenaField.insts, hinsts, List.length_nil]
  have hmap : funcExports sc'.exports = exportMap c := by
    rw [hx, exportMap]
    simp only [Nat.zero_add]
  refine ⟨sc'.exports, hmap, ?_⟩
  unfold instantiateRootCall instantiateRoot
  refine (trapIf_run ((congrArg (!·) hac).trans rfl) _ cfg).bind ((TRuns.getStore cfg).bind ?_)
  refine (checkImport_run (hpre _) cfg).bind
    ((TRuns.allocObj ArenaField.insts (fun _ _ => rfl) {} cfg).bind ?_)
  rw [hid]
  exact (hr.bind (f := fun sc => Pure.pure sc.exports) (TRuns.pure _ _)).bind
    (f := fun es => Pure.pure ((⟨0⟩ : InstId), es)) (TRuns.pure _ _)

/-- **The instantiation program of `c.toRef` runs silently** from the initial configuration
to `afterInst`, observing the root instance `0` and the export map. -/
theorem instProg_run {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hF : CoreFacts c I cs ci) :
    SRuns (instantiateProg c.toRef [] : P (core3R Pf V IR) Unit (Ret (core3R Pf V IR))) (initConfig ())
      [instantiatedObs ⟨0⟩ (exportMap c)] .unit
      (afterInst Pf V IR cs (liftedFuncs Pf V IR (fun k => I.addrs.getD k 0) c)) := by
  obtain ⟨es, hes, hr⟩ := rootCall_run hF
    { (initConfig () : Machine.Config (core3R Pf V IR) Unit) with
      store := DispatchSt.incNestingSt (initConfig () : Machine.Config (core3R Pf V IR) Unit).store }
    rfl rfl rfl
  unfold instantiateProg
  refine SRuns.bind (os₁ := [])
    (TRuns.modifyStore (f := DispatchSt.incNestingSt) (fun _ => rfl) _) ?_
  refine SRuns.bind (os₁ := []) hr ?_
  dsimp only
  rw [hes]
  exact SRuns.bind (os₁ := []) (TRuns.modifyStore (f := DispatchSt.decNestingSt) (fun _ => rfl) _)
    (.emit (.pure _ _))

/-! ## The machine runs of the instantiation -/

variable {prof : ProfileKind} {σ : Type} {hr : HostReady σ}
  {D : Call (core3R Pf V IR) → P (core3R Pf V IR) σ (Ret (core3R Pf V IR))}

/-- The configuration after the instantiation host event. -/
noncomputable def instStart (c : Simple) : Machine.Config (core3R Pf V IR) Unit :=
  { (initConfig () : Machine.Config (core3R Pf V IR) Unit) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg c.toRef []))] }

/-- **The instantiation is one deterministic run** from the host event to `afterInst`. -/
theorem inst_detRunL {hr : HostReady Unit}
    {D : Call (core3R Pf V IR) → P (core3R Pf V IR) Unit (Ret (core3R Pf V IR))} {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hF : CoreFacts c I cs ci) :
    ∃ tr, SRuns.Quiet tr ∧ traceObs tr = [instantiatedObs ⟨0⟩ (exportMap c)] ∧
      DetRunL prof hr D (instStart c)
        tr (afterInst Pf V IR cs (liftedFuncs Pf V IR (fun k => I.addrs.getD k 0) c)) := by
  obtain ⟨tr, hq, ho, d⟩ := (instProg_run hF).detRunL (prof := prof) (hr := hr) (dispatch := D)
    rfl none (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { afterInst Pf V IR cs (liftedFuncs Pf V IR (fun k => I.addrs.getD k 0) c) with
        ctl := [⟨none, .prog (Pure.pure .unit), []⟩] } .tau
      (afterInst Pf V IR cs (liftedFuncs Pf V IR (fun k => I.addrs.getD k 0) c)) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  refine ⟨tr ++ [.tau], fun l hl => ?_, ?_, d.trans (.cons rfl s (.refl rfl))⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hq l hl
    · exact .inl (List.mem_singleton.1 hl)
  · rw [traceObs_append, ho]
    rfl

/-- The instantiation host event goes to `instStart`. -/
theorem hostRun_inv {m m' : Machine.Config (core3R Pf V IR) σ}
    {p : P (core3R Pf V IR) σ (Ret (core3R Pf V IR))}
    (h : Machine.Step prof hr D m (.host (.run p)) m') :
    m' = { m with ctl := [.ofProg none (StepDefs.runProg p)] } := by
  cases h
  rfl

/-- From a host-in-control configuration, runs without host events do nothing. -/
theorem steps_ctl_nil {m m' : Machine.Config (core3R Pf V IR) σ}
    {tr : List (Label (core3R Pf V IR) σ)} (hc : m.ctl = [])
    (h : Machine.Steps prof hr D m tr m') (hn : ∀ ev, Label.host ev ∉ tr) :
    tr = [] ∧ m' = m := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | cons s _ =>
    obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc s
    exact absurd List.mem_cons_self (hn ev)

/-- A quiet deterministic run that ends with the host in control: every run without host
events from its start that ends with the host in control is that run. -/
theorem detRunL_end {m m₂ m' : Machine.Config (core3R Pf V IR) σ}
    {tr tr' : List (Label (core3R Pf V IR) σ)} (d : DetRunL prof hr D m tr m₂)
    (hq : SRuns.Quiet tr) (hc₂ : m₂.ctl = []) (h : Machine.Steps prof hr D m tr' m')
    (hn : ∀ ev, Label.host ev ∉ tr') (hc : m'.ctl = [] ∨ m'.store.lockdown = true) :
    tr' = tr ∧ m' = m₂ := by
  rcases d.inv h with ⟨tr₂, htr, d₂⟩ | ⟨tr'', htr, h''⟩
  · cases d₂ with
    | refl _ => exact ⟨by rw [htr, List.append_nil], rfl⟩
    | cons hl s _ =>
      have hl' : _ ∈ tr := htr ▸ List.mem_append_right tr' List.mem_cons_self
      rcases hc with hc | hc
      · obtain ⟨ev, he⟩ := Step.host_of_ctl_nil hc s.1
        rcases hq _ hl' with e | ⟨o, e⟩ <;> rw [he] at e <;> cases e
      · rw [hc] at hl
        cases hl
  · have hn'' : ∀ ev, Label.host ev ∉ tr'' := fun ev he => hn ev (htr ▸ List.mem_append_right _ he)
    obtain ⟨rfl, rfl⟩ := steps_ctl_nil hc₂ h'' hn''
    exact ⟨by rw [htr, List.append_nil], rfl⟩

/-- **The results of instantiating `c.toRef`**: the only one is the instance at `afterInst`
with root instance `0` and the export map `exportMap c`. -/
theorem instBehaviours_toRef {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3R Pf V IR).Store (CanonHost (core3R Pf V IR))} {ci : (core3R Pf V IR).Inst}
    (hF : CoreFacts c I cs ci) (prof : ProfileKind) :
    ∀ r ∈ instBehaviours prof (refHostR Pf V IR) (initConfig ()) c.toRef [],
      r = .instance (afterInst Pf V IR cs (liftedFuncs Pf V IR (fun k => I.addrs.getD k 0) c)) ⟨0⟩
        (exportMap c) := by
  obtain ⟨trD, hq, ho, d⟩ := inst_detRunL (prof := prof) (hr := (refHostR Pf V IR).hr)
    (D := (refHostR Pf V IR).dispatch) hF
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn, hc, -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStart c := hostRun_inv s₁
    obtain ⟨htr, hm⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn (.inl hc)
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, exportMap c) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), exportMap c) := Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStart c := hostRun_inv s₁
    obtain ⟨-, rfl⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn (.inr ht)
    cases ht
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = instStart c := hostRun_inv s₁
    exact absurd (d.toDetRun.diverges (he ▸ dv)) (not_diverges_of_ctl_nil rfl)

/-- **The instantiation phase** (`InstPhase`). -/
theorem instPhase : InstPhase := by
  intro Pf V IR prof c hc hi
  obtain ⟨I, cs, ci, hF⟩ := coreFacts (Pf := Pf) hc hi
  exact ⟨I, cs, hF.isInst, hF.store, instBehaviours_toRef hF prof⟩

end Core3P

end Silmaril.Proofs.Wasm.Component.Param.Core3R
