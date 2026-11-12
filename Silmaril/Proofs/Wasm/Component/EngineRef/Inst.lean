module

public import Silmaril.Wasm.Component.EngineRef.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.InstRun
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The instantiation phase over any engine

The `core3P`-specific sections of `Silmaril.Proofs.Wasm.Component.Reference.InstExport` and
`Silmaril.Proofs.Wasm.Component.Reference.InstRun` (section `Core3P`), over an arbitrary engine `E`
and the component `c.toRef.map ofCore` (provenance: copies of `Param.Core3R.Inst`, which copies
these sections, with `core3R P V IR` replaced by `E`). The engine-specific facts (`CoreFacts`:
`prepare?`, `importTypes`, `exports` of the core module) are the hypothesis
`EngineRef.InstFacts`. The one new ingredient is `toRef_map`: mapping the core module of
`c.toRef` along `ofCore` leaves the emitted type and export definitions unchanged
(`emitTy_map`, `exportDefs_map`).

New proofs (copied structure).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.EngineRef

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.EngineRef Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component (Syntax.Definition Syntax.VT Syntax.DefValType)

/-! ## Changing the core module type of the emitted definitions -/

section Map

variable {A B : Type} (f : A → B)

mutual
/-- The emitted definitions of a type do not depend on the core module type. -/
theorem emitTy_map : ∀ (t : ValTy) (n : Nat),
    (emitTy (M := A) t n).1 = (emitTy (M := B) t n).1 ∧
      (emitTy (M := A) t n).2.1.map (Syntax.Definition.map f) = (emitTy (M := B) t n).2.1 ∧
      (emitTy (M := A) t n).2.2 = (emitTy (M := B) t n).2.2
  | .bool, _ | .s8, _ | .u8, _ | .s16, _ | .u16, _ | .s32, _ | .u32, _ | .s64, _ | .u64, _
  | .f32, _ | .f64, _ | .char, _ => ⟨rfl, rfl, rfl⟩
  | .record ts, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitTys_map ts n
    rw [emitTy_record, emitTy_record]
    refine ⟨by rw [h₃], ?_, by rw [h₃]⟩
    simp only [List.map_append, h₂, List.map_cons, List.map_nil, Syntax.Definition.map,
      typeExport, h₁, h₃]
  | .variant cs, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitCases_map cs n
    rw [emitTy_variant, emitTy_variant]
    refine ⟨by rw [h₃], ?_, by rw [h₃]⟩
    simp only [List.map_append, h₂, List.map_cons, List.map_nil, Syntax.Definition.map,
      typeExport, h₁, h₃]

/-- `emitTy_map` on lists. -/
theorem emitTys_map : ∀ (ts : List ValTy) (n : Nat),
    (emitTys (M := A) ts n).1 = (emitTys (M := B) ts n).1 ∧
      (emitTys (M := A) ts n).2.1.map (Syntax.Definition.map f) = (emitTys (M := B) ts n).2.1 ∧
      (emitTys (M := A) ts n).2.2 = (emitTys (M := B) ts n).2.2
  | [], _ => ⟨rfl, rfl, rfl⟩
  | t :: ts, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitTy_map t n
    obtain ⟨k₁, k₂, k₃⟩ := emitTys_map ts (emitTy (M := A) t n).2.2
    rw [emitTys_cons, emitTys_cons]
    dsimp only
    exact ⟨by rw [h₁, k₁, h₃], by rw [List.map_append, h₂, k₂, h₃], by rw [k₃, h₃]⟩

/-- `emitTy_map` on variant cases. -/
theorem emitCases_map : ∀ (cs : List (Option ValTy)) (n : Nat),
    (emitCases (M := A) cs n).1 = (emitCases (M := B) cs n).1 ∧
      (emitCases (M := A) cs n).2.1.map (Syntax.Definition.map f) =
        (emitCases (M := B) cs n).2.1 ∧
      (emitCases (M := A) cs n).2.2 = (emitCases (M := B) cs n).2.2
  | [], _ => ⟨rfl, rfl, rfl⟩
  | none :: cs, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitCases_map cs n
    rw [emitCases_none, emitCases_none]
    exact ⟨by rw [h₁], h₂, h₃⟩
  | some t :: cs, n => by
    obtain ⟨h₁, h₂, h₃⟩ := emitTy_map t n
    obtain ⟨k₁, k₂, k₃⟩ := emitCases_map cs (emitTy (M := A) t n).2.2
    rw [emitCases_some, emitCases_some]
    dsimp only
    exact ⟨by rw [h₁, k₁, h₃], by rw [List.map_append, h₂, k₂, h₃], by rw [k₃, h₃]⟩
end

end Map

/-! ## The definitions of one export over `E` -/

section Exports

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]

theorem exportDefs_eq0 (m : NumModule) (i : Nat) (x : SimpleExport) (n : Nat) :
    Simple.exportDefs m i x n =
      ((emitTys (M := Silmaril.Wasm.Module) x.ty.params n).2.1 ++
        (emitTys (M := Silmaril.Wasm.Module) x.ty.results
          (emitTys (M := Silmaril.Wasm.Module) x.ty.params n).2.2).2.1 ++
        [.type (.func { params := labels "a" (emitTys (M := Silmaril.Wasm.Module) x.ty.params n).1,
                        result := (emitTys (M := Silmaril.Wasm.Module) x.ty.results
                          (emitTys (M := Silmaril.Wasm.Module) x.ty.params n).2.2).1.head? }),
         .alias (.coreExport 0 (coreNameE m x) .func),
         .canon (.lift i [] (emitTys (M := Silmaril.Wasm.Module) x.ty.results
           (emitTys (M := Silmaril.Wasm.Module) x.ty.params n).2.2).2.2),
         .export_ { name := x.name } ⟨.func, 2 * i⟩ none],
        (emitTys (M := Silmaril.Wasm.Module) x.ty.results
          (emitTys (M := Silmaril.Wasm.Module) x.ty.params n).2.2).2.2 + 1) := by
  simp only [Simple.exportDefs]
  rfl

/-- **The definitions of one export, mapped to the module type `N`.** -/
theorem exportDefs_map {N : Type} (g : Silmaril.Wasm.Module → N) (m : NumModule) (i : Nat)
    (x : SimpleExport) (n : Nat) :
    (Simple.exportDefs m i x n).1.map (Syntax.Definition.map g) =
      (emitTys (M := N) x.ty.params n).2.1 ++
        (emitTys (M := N) x.ty.results (emitTys (M := N) x.ty.params n).2.2).2.1 ++
        [.type (.func { params := labels "a" (emitTys (M := N) x.ty.params n).1,
                        result := (emitTys (M := N) x.ty.results
                          (emitTys (M := N) x.ty.params n).2.2).1.head? }),
         .alias (.coreExport 0 (coreNameE m x) .func),
         .canon (.lift i [] (emitTys (M := N) x.ty.results
           (emitTys (M := N) x.ty.params n).2.2).2.2),
         .export_ { name := x.name } ⟨.func, 2 * i⟩ none] ∧
    (Simple.exportDefs m i x n).2 =
      (emitTys (M := N) x.ty.results (emitTys (M := N) x.ty.params n).2.2).2.2 + 1 := by
  obtain ⟨p₁, p₂, p₃⟩ := emitTys_map g x.ty.params n
  obtain ⟨r₁, r₂, r₃⟩ := emitTys_map g x.ty.results
    (emitTys (M := Silmaril.Wasm.Module) x.ty.params n).2.2
  rw [exportDefs_eq0]
  dsimp only
  refine ⟨?_, by rw [r₃, p₃]⟩
  simp only [List.map_append, List.map_cons, List.map_nil, Syntax.Definition.map]
  rw [p₂, r₂, r₁, r₃, p₁, p₃]

variable {σ : Type} {R : Recurse E σ} {inst : InstId} {outer : List (Frame E)}
  {args : Exports E}

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem funcExports_append_func (l : Exports E) (n : String) (f : FuncId) :
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
theorem lift_run (sc : Scope E) (cfg : Machine.Config E σ) {i ft : Nat} {a : E.FuncAddr}
    {t : Types.FuncType RtId} (hs : cfg.store.funcs.length = i)
    (ha : sc.frame.coreFuncs[i]? = some a) (ht : sc.frame.types[ft]? = some (.func t)) :
    TRuns (instantiateDef R inst outer args sc (.canon (.lift i [] ft))) cfg
      { sc with frame := { sc.frame with funcs := sc.frame.funcs ++ [⟨i⟩] } }
      { cfg with store := ArenaOps.allocSt ArenaField.funcs (.lifted a t {} inst) cfg.store } := by
  rw [instDef_lift sc ha ht, ← hs]
  exact (TRuns.allocObj _ (fun _ _ => rfl) _ cfg).bind (TRuns.pure _ _)

/-- The frame after the function type, the alias and the lift of an export. -/
def liftFrame (f : Frame E) (t : Types.FuncType RtId) (a : E.FuncAddr) (i : Nat) : Frame E :=
  { f with types := f.types ++ [.func t], coreFuncs := f.coreFuncs ++ [a],
           funcs := f.funcs ++ [⟨i⟩] }

/-- **The definitions of one export run silently**: from the frame invariant of export `i`,
they allocate the lifted function `i` and record its export. -/
theorem exportDefs_run (ofCore : Silmaril.Wasm.Module → E.Module) (m : NumModule) (i : Nat)
    (x : SimpleExport) (sc : Scope E) (cfg : Machine.Config E σ)
    {es₀ : List (String × E.ExternVal)} {v : E.ExternVal} {a : E.FuncAddr}
    (hinv : ExpInv es₀ i sc.frame) (hs : cfg.store.funcs.length = i)
    (hlk : lookupExport? es₀ (coreNameE m x) = some v) (hv : E.asFunc? v = some a) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
        ((Simple.exportDefs m i x sc.frame.types.length).1.map
          (Syntax.Definition.map ofCore))) cfg sc'
        { cfg with store :=
            ArenaOps.allocSt ArenaField.funcs (.lifted a (liftedFt x) {} inst) cfg.store } ∧
      ExpInv es₀ (i + 1) sc'.frame ∧
      sc'.frame.types.length = (Simple.exportDefs m i x sc.frame.types.length).2 ∧
      funcExports sc'.exports = funcExports sc.exports ++ [(x.name, ⟨i⟩)] ∧
      NoImport ((Simple.exportDefs m i x sc.frame.types.length).1.map
        (Syntax.Definition.map ofCore)) := by
  obtain ⟨sc₁, hP₁, hR₁⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.params sc
  obtain ⟨sc₂, hP₂, hR₂⟩ := emitTys_run (R := R) (inst := inst) (outer := outer) (args := args)
    x.ty.results sc₁
  have hl₁ : sc₁.frame.types.length =
      (emitTys (M := E.Module) x.ty.params sc.frame.types.length).2.2 := hP₁.2.2.1
  have hl₂ : sc₂.frame.types.length =
      (emitTys (M := E.Module) x.ty.results sc₁.frame.types.length).2.2 := hP₂.2.2.1
  obtain ⟨hm₁, hm₂⟩ := exportDefs_map ofCore m i x sc.frame.types.length
  rw [hm₁, hm₂, ← hl₁, ← hl₂]
  have hinv₂ : ExpInv es₀ i sc₂.frame := hP₂.expInv (hP₁.expInv hinv)
  have hft : resolveFuncType? sc₂.frame
      { params := labels "a" (emitTys (M := E.Module) x.ty.params sc.frame.types.length).1,
        result := (emitTys (M := E.Module) x.ty.results
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
    hci hlk hv
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
def liftedList (addr : Nat → E.FuncAddr) (inst : InstId) (xs : List SimpleExport) :
    List (CFuncInst E) :=
  xs.map fun x => .lifted (addr x.core) (liftedFt x) {} inst

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem liftedList_cons (addr : Nat → E.FuncAddr) (inst : InstId) (x : SimpleExport)
    (xs : List SimpleExport) :
    liftedList addr inst (x :: xs) = liftedList addr inst [x] ++ liftedList addr inst xs := rfl

theorem mapIdx_shift (xs : List SimpleExport) (i : Nat) :
    (xs.mapIdx fun k x => (x.name, (⟨i + 1 + k⟩ : FuncId))) =
      xs.mapIdx fun k x => (x.name, (⟨i + (k + 1)⟩ : FuncId)) := by
  congr 1
  funext k x
  rw [Nat.add_assoc, Nat.add_comm 1 k]

/-- **The definitions of all exports run silently**, appending the lifted functions to the
component functions and recording their exports. -/
theorem exportsDefs_run (ofCore : Silmaril.Wasm.Module → E.Module) (m : NumModule)
    (addr : Nat → E.FuncAddr) {es₀ : List (String × E.ExternVal)} :
    ∀ (xs : List SimpleExport) (i : Nat) (sc : Scope E) (cfg : Machine.Config E σ),
      ExpInv es₀ i sc.frame → cfg.store.funcs.length = i →
      (∀ x ∈ xs, ∃ v, lookupExport? es₀ (coreNameE m x) = some v ∧
        E.asFunc? v = some (addr x.core)) →
      ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) sc
          ((Simple.exportsDefs m i xs sc.frame.types.length).map
            (Syntax.Definition.map ofCore))) cfg sc'
          { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst xs } } ∧
        funcExports sc'.exports =
          funcExports sc.exports ++ xs.mapIdx (fun k x => (x.name, ⟨i + k⟩)) ∧
        NoImport ((Simple.exportsDefs m i xs sc.frame.types.length).map
          (Syntax.Definition.map ofCore))
  | [], i, sc, cfg, _, _, _ => by
    refine ⟨sc, ?_, by rw [List.mapIdx_nil, List.append_nil], fun _ h => by
      simp [Simple.exportsDefs] at h⟩
    simp only [liftedList, List.map_nil, List.append_nil, Simple.exportsDefs]
    exact TRuns.foldlM_nil sc cfg
  | x :: xs, i, sc, cfg, hinv, hs, hlk => by
    obtain ⟨v, hlv, hv⟩ := hlk x List.mem_cons_self
    obtain ⟨sc₁, hr₁, hinv₁, hl₁, hx₁, hn₁⟩ := exportDefs_run (R := R) (inst := inst)
      (outer := outer) (args := args) ofCore m i x sc cfg hinv hs hlv hv
    have hs₁ : (cfg.store.funcs ++ liftedList addr inst [x]).length = i + 1 := by
      rw [List.length_append, hs]
      rfl
    obtain ⟨sc₂, hr₂, hx₂, hn₂⟩ := exportsDefs_run ofCore m addr xs (i + 1) sc₁
      { cfg with store := { cfg.store with funcs := cfg.store.funcs ++ liftedList addr inst [x] } }
      hinv₁ hs₁
      (fun y hy => hlk y (List.mem_cons_of_mem _ hy))
    rw [exportsDefs_cons, List.map_append]
    refine ⟨sc₂, ?_, ?_, hn₁.append (hl₁ ▸ hn₂)⟩
    · rw [liftedList_cons, ← List.append_assoc]
      exact TRuns.foldlM_append hr₁ (hl₁ ▸ hr₂)
    · rw [hx₂, hx₁, List.mapIdx_cons, List.append_assoc, Nat.add_zero, mapIdx_shift]
      rfl

end Exports

/-! ## The core instance -/

section Core

variable {E : Engine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type} {R : Recurse E σ}
  {inst : InstId} {outer : List (Frame E)} {args : Exports E}

/-- `instantiateCore` of an import-free, start-free module: one store read and the update of
the core store. -/
theorem instantiateCore_run (f : Frame E) (cfg : Machine.Config E σ) {m : E.Module}
    {cs : E.Store (CanonHost E)} {ci : E.Inst} (hm : f.coreModules = [m])
    (himp : E.importTypes m = [])
    (hp : E.prepare? cfg.store.core m [] = some (cs, ci, none)) :
    TRuns (instantiateCore inst f 0 [] : P E σ _) cfg (E.exports ci)
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

theorem instDef_coreModule (sc : Scope E) (m : E.Module) :
    instantiateDef R inst outer args sc (.coreModule m) =
      (Pure.pure { sc with frame := { sc.frame with coreModules := sc.frame.coreModules ++ [m] } } :
        P E σ (Scope E)) := by
  simp only [instantiateDef, pushEntry, need, Frame.push, orTrap]
  rfl

/-- The frame after the core module and the core instance. -/
noncomputable def coreFrame (m : E.Module) (es₀ : List (String × E.ExternVal)) : Frame E :=
  { (Frame.empty : Frame E) with coreModules := [m], coreInstances := [es₀] }

/-- The `core instance` definition of `Simple.toRef`. -/
theorem instDef_coreInstance (sc : Scope E) (cfg : Machine.Config E σ) {m : E.Module}
    {cs : E.Store (CanonHost E)} {ci : E.Inst} (hm : sc.frame.coreModules = [m])
    (himp : E.importTypes m = [])
    (hp : E.prepare? cfg.store.core m [] = some (cs, ci, none)) :
    TRuns (instantiateDef R inst outer args sc (.coreInstance (.instantiate 0 [])))
      cfg { sc with frame := { sc.frame with
        coreInstances := sc.frame.coreInstances ++ [E.exports ci] } }
      { cfg with store := setCoreSt cs cfg.store } :=
  (instantiateCore_run (inst := inst) sc.frame cfg hm himp hp).bind (TRuns.pure _ _)

/-- The store after the core instance and the lifted functions `fs`. -/
noncomputable def liftStore (cs : E.Store (CanonHost E)) (s : CStore E)
    (fs : List (CFuncInst E)) : CStore E :=
  { setCoreSt cs s with funcs := s.funcs ++ fs }

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- `c.toRef` mapped along `ofCore`. -/
theorem toRef_map (ofCore : Silmaril.Wasm.Module → E.Module) (c : Simple) :
    (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef : List (Syntax.Definition E.Module)) =
      [.coreModule (ofCore c.mod.mod), .coreInstance (.instantiate 0 [])] ++
        (Simple.exportsDefs c.mod 0 c.exports 0).map (Syntax.Definition.map ofCore) := by
  rw [Silmaril.Wasm.Component.Syntax.Component.map, Syntax.Definition.mapList_eq, Simple.toRef,
    List.map_append]
  rfl

/-- **The definitions of `c.toRef.map ofCore` run silently** from a store with the empty core
store and no component function: the core instance, then the lifted functions of the exports. -/
theorem toRefDefs_run {ofCore : Silmaril.Wasm.Module → E.Module} {c : Simple}
    {cs : E.Store (CanonHost E)} {ci : E.Inst} {addr : Nat → E.FuncAddr}
    (hF : InstFacts E ofCore c cs ci addr) (cfg : Machine.Config E σ)
    (hcore : cfg.store.core = E.empty _) (hfuncs : cfg.store.funcs = []) :
    ∃ sc', TRuns (List.foldlM (instantiateDef R inst outer args) {}
          (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef)) cfg sc'
        { cfg with store := liftStore cs cfg.store (liftedList addr inst c.exports) } ∧
      funcExports sc'.exports = c.exports.mapIdx (fun k x => (x.name, ⟨0 + k⟩)) ∧
      NoImport (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef) := by
  have hp : E.prepare? cfg.store.core (ofCore c.mod.mod) [] = some (cs, ci, none) := by
    rw [hcore]
    exact hF.prepare
  have h₁ := instDef_coreModule (R := R) (inst := inst) (outer := outer) (args := args) {}
    (ofCore c.mod.mod)
  have h₂ := instDef_coreInstance (R := R) (inst := inst) (outer := outer) (args := args)
    { frame := { (Frame.empty : Frame E) with coreModules := [] ++ [ofCore c.mod.mod] },
      exports := [] } cfg rfl hF.imports hp
  have hinv : ExpInv (E.exports ci) 0 (coreFrame (ofCore c.mod.mod) (E.exports ci)) :=
    ⟨rfl, rfl, rfl⟩
  have hs : (setCoreSt cs cfg.store).funcs.length = 0 := by
    show cfg.store.funcs.length = 0
    rw [hfuncs]
    rfl
  obtain ⟨sc', hr, hx, hn⟩ := exportsDefs_run (R := R) (inst := inst) (outer := outer)
    (args := args) ofCore c.mod addr c.exports 0
    { frame := coreFrame (ofCore c.mod.mod) (E.exports ci), exports := [] }
    { cfg with store := setCoreSt cs cfg.store } hinv hs hF.lookup
  have hn' : NoImport (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef) := by
    rw [toRef_map]
    refine NoImport.append (fun d hd => ?_) hn
    rcases List.mem_cons.1 hd with rfl | hd
    · intro _ _ e
      cases e
    · rw [List.mem_singleton.1 hd]
      intro _ _ e
      cases e
  refine ⟨sc', ?_, hx, hn'⟩
  rw [toRef_map]
  exact TRuns.foldlM_append (TRuns.foldlM_cons (TRuns.of_eq cfg h₁)
    (TRuns.foldlM_cons h₂ (TRuns.foldlM_nil _ _))) hr

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem trapIf_run {b : Bool} (hb : b = false) (r : TrapReason)
    (m : Machine.Config E σ) : TRuns (trapIf b r : P E σ Unit) m () m := by
  subst hb
  exact TRuns.pure () m

omit [∀ a b, Decidable (E.ExternSub a b)] in
theorem checkImport_run {r : Except String Unit} (hr : r = .ok ())
    (m : Machine.Config E σ) :
    TRuns (checkImport r : P E σ Unit) m () m := by
  subst hr
  exact TRuns.pure () m

/-- The store after root instantiation: instance `0`, the core store and the lifted
functions. -/
noncomputable def instStore (cs : E.Store (CanonHost E)) (s : CStore E)
    (addr : Nat → E.FuncAddr) (c : Simple) : CStore E :=
  liftStore cs (ArenaOps.allocSt ArenaField.insts {} s) (liftedList addr ⟨0⟩ c.exports)

/-- **Root instantiation of `c.toRef.map ofCore` runs silently**. -/
theorem rootCall_run {ofCore : Silmaril.Wasm.Module → E.Module} {c : Simple}
    {cs : E.Store (CanonHost E)} {ci : E.Inst} {addr : Nat → E.FuncAddr}
    (hF : InstFacts E ofCore c cs ci addr) (cfg : Machine.Config E σ)
    (hcore : cfg.store.core = E.empty _) (hfuncs : cfg.store.funcs = [])
    (hinsts : cfg.store.insts = []) :
    ∃ es, funcExports es = exportMap c ∧
      TRuns (instantiateRootCall (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef) [] :
          P E σ _) cfg (⟨0⟩, es)
        { cfg with store := instStore cs cfg.store addr c } := by
  obtain ⟨sc', hr, hx, hn⟩ := toRefDefs_run (R := callRecurse) (inst := ⟨0⟩) (outer := [])
    (args := []) hF { cfg with store := ArenaOps.allocSt ArenaField.insts {} cfg.store }
    hcore hfuncs
  have hac : argsComplete (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef)
      ([] : Exports E) = true := by
    rw [argsComplete, importNames_nil hn]
    rfl
  have hpre : ∀ s : CStore E, precheckImports s [] Frame.empty
      (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef) = .ok () :=
    fun s => precheckImports_ok s [] _ _ hn
  have hid : (ArenaField.insts (E := E)).mkId (ArenaField.insts.size cfg.store) =
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

/-- The configuration after instantiation. -/
noncomputable def afterInstE (cs : E.Store (CanonHost E)) (fs : List (CFuncInst E)) :
    Machine.Config E Unit :=
  Config.init { core := cs, insts := [{}], funcs := fs } ()

/-- The lifted functions of the exports of `c`, at the core addresses `addr x.core`. -/
noncomputable def liftedFuncsE (addr : Nat → E.FuncAddr) (c : Simple) : List (CFuncInst E) :=
  c.exports.map fun x => .lifted (addr x.core) (liftedFt x) {} ⟨0⟩

/-- **The instantiation program runs silently** from the initial configuration to `afterInstE`,
observing the root instance `0` and the export map. -/
theorem instProg_run {ofCore : Silmaril.Wasm.Module → E.Module} {c : Simple}
    {cs : E.Store (CanonHost E)} {ci : E.Inst} {addr : Nat → E.FuncAddr}
    (hF : InstFacts E ofCore c cs ci addr) :
    SRuns (instantiateProg (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef) [] :
        P E Unit (Ret E)) (initConfig ())
      [instantiatedObs ⟨0⟩ (exportMap c)] .unit (afterInstE cs (liftedFuncsE addr c)) := by
  obtain ⟨es, hes, hr⟩ := rootCall_run hF
    { (initConfig () : Machine.Config E Unit) with
      store := DispatchSt.incNestingSt (initConfig () : Machine.Config E Unit).store }
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

variable {prof : ProfileKind}

/-- The configuration after the instantiation host event. -/
noncomputable def instStart (ofCore : Silmaril.Wasm.Module → E.Module) (c : Simple) :
    Machine.Config E Unit :=
  { (initConfig () : Machine.Config E Unit) with
    ctl := [.ofProg none (StepDefs.runProg (instantiateProg
      (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef) []))] }

/-- **The instantiation is one deterministic run** from the host event to `afterInstE`. -/
theorem inst_detRunL {hr : HostReady Unit} {D : Call E → P E Unit (Ret E)}
    {ofCore : Silmaril.Wasm.Module → E.Module} {c : Simple}
    {cs : E.Store (CanonHost E)} {ci : E.Inst} {addr : Nat → E.FuncAddr}
    (hF : InstFacts E ofCore c cs ci addr) :
    ∃ tr, SRuns.Quiet tr ∧ traceObs tr = [instantiatedObs ⟨0⟩ (exportMap c)] ∧
      DetRunL prof hr D (instStart ofCore c) tr (afterInstE cs (liftedFuncsE addr c)) := by
  obtain ⟨tr, hq, ho, d⟩ := (instProg_run hF).detRunL (prof := prof) (hr := hr) (dispatch := D)
    rfl none (fun _ => Pure.pure .unit) [] []
  have s : UniqueStep prof hr D
      { afterInstE cs (liftedFuncsE addr c) with ctl := [⟨none, .prog (Pure.pure .unit), []⟩] }
      .tau (afterInstE cs (liftedFuncsE addr c)) :=
    .of_prog rfl (fun _ _ e => by cases e) (.hostDone (r := .unit) (rest := []) rfl)
  refine ⟨tr ++ [.tau], fun l hl => ?_, ?_, d.trans (.cons rfl s (.refl rfl))⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hq l hl
    · exact .inl (List.mem_singleton.1 hl)
  · rw [traceObs_append, ho]
    rfl

variable {hr : HostReady σ} {D : Call E → P E σ (Ret E)}

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- The instantiation host event goes to `instStart`. -/
theorem hostRun_inv {m m' : Machine.Config E σ} {p : P E σ (Ret E)}
    (h : Machine.Step prof hr D m (.host (.run p)) m') :
    m' = { m with ctl := [.ofProg none (StepDefs.runProg p)] } := by
  cases h
  rfl

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- From a host-in-control configuration, runs without host events do nothing. -/
theorem steps_ctl_nil {m m' : Machine.Config E σ} {tr : List (Label E σ)} (hc : m.ctl = [])
    (h : Machine.Steps prof hr D m tr m') (hn : ∀ ev, Label.host ev ∉ tr) :
    tr = [] ∧ m' = m := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | cons s _ =>
    obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc s
    exact absurd List.mem_cons_self (hn ev)

omit [∀ a b, Decidable (E.ExternSub a b)] in
/-- A quiet deterministic run that ends with the host in control: every run without host
events from its start that ends with the host in control is that run. -/
theorem detRunL_end {m m₂ m' : Machine.Config E σ} {tr tr' : List (Label E σ)}
    (d : DetRunL prof hr D m tr m₂) (hq : SRuns.Quiet tr) (hc₂ : m₂.ctl = [])
    (h : Machine.Steps prof hr D m tr' m') (hn : ∀ ev, Label.host ev ∉ tr')
    (hc : m'.ctl = [] ∨ m'.store.lockdown = true) : tr' = tr ∧ m' = m₂ := by
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

/-- **The results of instantiating `c.toRef.map ofCore`**: the only one is the instance at
`afterInstE` with root instance `0` and the export map `exportMap c`. -/
theorem instBehaviours_toRef {ofCore : Silmaril.Wasm.Module → E.Module} {c : Simple}
    {cs : E.Store (CanonHost E)} {ci : E.Inst} {addr : Nat → E.FuncAddr}
    (hF : InstFacts E ofCore c cs ci addr) (prof : ProfileKind) :
    ∀ r ∈ instBehaviours prof (refHostE E) (initConfig ())
        (Silmaril.Wasm.Component.Syntax.Component.map ofCore c.toRef) [],
      r = .instance (afterInstE cs (liftedFuncsE addr c)) ⟨0⟩ (exportMap c) := by
  obtain ⟨trD, hq, ho, d⟩ := inst_detRunL (prof := prof) (hr := (refHostE E).hr)
    (D := (refHostE E).dispatch) hF
  intro r hr
  cases r with
  | «instance» m' inst es =>
    show InstResult.instance m' inst es = _
    obtain ⟨tr, hs, hn, hc, -, hobs⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStart ofCore c := hostRun_inv s₁
    obtain ⟨htr, hm⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn (.inl hc)
    have hdec : (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, exportMap c) := by
      rw [htr, ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
    have hie : (inst, es) = ((⟨0⟩ : InstId), exportMap c) := Option.some.inj (hobs.symm.trans hdec)
    rw [hm, (Prod.mk.inj hie).1, (Prod.mk.inj hie).2]
  | traps =>
    obtain ⟨m', tr, hs, hn, -, ht⟩ := hr
    obtain ⟨m₁, s₁, hs₁⟩ := Machine.Steps.cons_iff.1 hs
    have he : m₁ = instStart ofCore c := hostRun_inv s₁
    obtain ⟨-, rfl⟩ := detRunL_end d hq rfl (he ▸ hs₁) hn (.inr ht)
    cases ht
  | diverges =>
    obtain ⟨m₁, s₁, dv⟩ := hr
    have he : m₁ = instStart ofCore c := hostRun_inv s₁
    exact absurd (d.toDetRun.diverges (he ▸ dv)) (not_diverges_of_ctl_nil rfl)

end Core

end Silmaril.Proofs.Wasm.Component.EngineRef
