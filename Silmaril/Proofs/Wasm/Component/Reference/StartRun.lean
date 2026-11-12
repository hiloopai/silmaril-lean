module

public import Silmaril.Proofs.Wasm.Component.Reference.StartInst

/-!
# The instantiation program of a simple component with a start function, to the hole

`inst_reaches`: the instantiation program of `c.toRef` (a module whose start function is at
`a`) runs deterministically, without observations, from the instantiation host event to
`runStart ⟨0⟩ a` at `holeCfg cs` (instance `0` allocated, the core store `cs` installed); after
the start function, it runs to `afterStartCfg`, observing `instantiatedObs ⟨0⟩ (exportMapS c)`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- A silent run before a hole. -/
theorem Reaches.seqT {th : Option ThreadId} {X : Canon.P E σ Unit} {α β : Type}
    {p : Canon.P E σ β} {g : β → Canon.P E σ α} {m m₁ m₂ : Config E σ} {tr : List (Label E σ)}
    {b : β} {Post : Config E σ → List (Label E σ) → α → Config E σ → Prop}
    (h₁ : TRuns p m b m₁) (h₂ : Reaches prof hr dispatch th X (g b) m₁ tr m₂ Post) :
    ∃ tr', Reaches prof hr dispatch th X (p >>= g) m tr' m₂ Post ∧ traceObs tr' = traceObs tr := by
  obtain ⟨tr₁, h, ho⟩ := SRuns.runsQO (dispatch := dispatch) h₁ th
  exact ⟨tr₁ ++ tr, .seq h h₂, by rw [traceObs_append, ho, List.nil_append]⟩

/-! ## The configurations -/

variable {Pf : Profile}

/-- The store at the start function: instance `0` allocated, the core store `cs`. -/
def holeStore (cs : (core3P Pf).Store (CanonHost (core3P Pf))) : CStore (core3P Pf) :=
  setCoreSt cs (ArenaOps.allocSt ArenaField.insts {}
    (DispatchSt.incNestingSt (initConfig () : Machine.Config (core3P Pf) Unit).store))

/-- The configuration at the start function. -/
def holeCfg (cs : (core3P Pf).Store (CanonHost (core3P Pf))) : Machine.Config (core3P Pf) Unit :=
  { (initConfig () : Machine.Config (core3P Pf) Unit) with store := holeStore cs }

/-- The export map after the start function: export `i` is function `1 + i`. -/
def exportMapS (c : Simple) : List (String × FuncId) :=
  c.exports.mapIdx fun k x => (x.name, ⟨1 + k⟩)

/-- The instance state after the start function. -/
def instAfterStart : InstState := InstState.removeThread 1 (enterInst {} ⟨0⟩)

/-- The leftovers of the start function. -/
def startGarb (P : Profile) (a : Nat) : Garb P where
  tasks := [task₂ startEx [] ⟨0⟩]
  threads := [{ (thread₁ ([] : List (Runtime.Task (E3 P)))).withIndex 1 with status := .exited }]
  callers := [.sub .start]
  conts := Config.setSlot (Config.setSlot [] 0
    (some (threadAct (D P) ⟨0⟩ (.liftImplicit ⟨0⟩ a)))) 0 none
  pending := []
  results := []
  cancels := []

/-- **The configuration after instantiation with a start function**: between calls, with the
start function's leftovers and the functions `startFn a :: liftedFuncs`. -/
def afterStartCfg (P : Profile) (cs' : (core3P P).Store (CanonHost (core3P P))) (a : Nat)
    (addr : Nat → Nat) (c : Simple) : Machine.Config (core3P P) Unit :=
  readyCfg cs' instAfterStart (startFn a :: liftedFuncs P addr c) (startGarb P a)

end Silmaril.Proofs.Wasm.Component.Reference

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Instantiate
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

variable {Pf : Profile} {prof : ProfileKind}

/-- **`instantiateCore` of a module with a start function reaches the start function.** -/
theorem core_reaches {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hF : CoreFactsS c I cs ci (some a)) (f : Frame (core3P Pf))
    (hm : f.coreModules = [c.mod.mod]) (m : Machine.Config (core3P Pf) Unit)
    (hcore : m.store.core = (core3P Pf).empty _) :
    ∃ tr, Reaches prof (refHost Pf).hr (D Pf) none (runStart ⟨0⟩ a)
      (instantiateCore ⟨0⟩ f 0 [] : Canon.P (core3P Pf) Unit _) m tr
      { m with store := setCoreSt cs m.store }
      (fun m₂ tr' r m' => RunsQ (D Pf) none (pure ((core3P Pf).exports ci)) m₂ tr' r m') ∧
      traceObs tr = [] := by
  have hmod : f.coreModule? 0 = some c.mod.mod := by rw [Frame.coreModule?, hm]; rfl
  have himps : coreImportsFor? m.store.core c.mod.mod [] f = some [] := by
    unfold coreImportsFor?
    rw [hF.imports]
    rfl
  have hp : (core3P Pf).prepare? m.store.core c.mod.mod [] = some (cs, ci, some a) := by
    rw [hcore]
    exact hF.prepare
  have R₄ := Reaches.here (prof := prof) (hr := (refHost Pf).hr) (dispatch := D Pf) (th := none)
    (X := runStart ⟨0⟩ a) (fun _ => (pure ((core3P Pf).exports ci) : Canon.P (core3P Pf) Unit _))
    { m with store := setCoreSt cs m.store }
  have R₃ : Reaches prof (refHost Pf).hr (D Pf) none (runStart ⟨0⟩ a)
      (Canon.modifyStore (setCoreSt cs) >>= fun _ =>
        (runStart ⟨0⟩ a >>= fun _ => (pure ((core3P Pf).exports ci) : Canon.P (core3P Pf) Unit _)))
      m ([.tau] ++ []) { m with store := setCoreSt cs m.store }
      (fun m₂ tr' r m' => RunsQ (D Pf) none (pure ((core3P Pf).exports ci)) m₂ tr' r m') :=
    Reaches.seq (RunsQ.modify rfl (.pure () _)) R₄
  unfold instantiateCore
  rw [hmod]
  apply Exists.intro
  apply And.intro
  · apply Reaches.seq (RunsQ.pure _ _)
    apply Reaches.seq (RunsQ.get (.pure _ _))
    dsimp only
    rw [himps]
    apply Reaches.seq (RunsQ.pure _ _)
    rw [hp]
    exact R₃
  · simp [traceObs, Label.obs?]

/-- The definitions of `c.toRef` contain no import. -/
theorem noImport_toRefS {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {st : Option Nat}
    (hF : CoreFactsS c I cs ci st) :
    NoImport (c.toRef : List (Syntax.Definition (core3P Pf).Module)) := by
  obtain ⟨-, -, -, hn⟩ := exportsDefs_run (R := callRecurse) (inst := ⟨0⟩) (outer := [])
    (args := []) (σ := Unit) c.mod (fun k => I.addrs.getD k 0) c.exports 0
    { frame := coreFrame c.mod.mod ((core3P Pf).exports ci), exports := [] }
    (initConfig () : Machine.Config (core3P Pf) Unit) ⟨rfl, rfl, rfl⟩ rfl hF.lookup
  unfold Simple.toRef
  refine NoImport.append (fun d hd => ?_) hn
  rcases List.mem_cons.1 hd with rfl | hd
  · intro _ _ e
    cases e
  · rw [List.mem_singleton.1 hd]
    intro _ _ e
    cases e

/-- The frame after the core module. -/
def modFrame (c : Simple) : Frame (core3P Pf) :=
  { (Frame.empty : Frame (core3P Pf)) with coreModules := [] ++ [c.mod.mod] }

/-- The scope after the core module and the core instance `es`. -/
def coreScope (c : Simple) (es : List (String × (core3P Pf).ExternVal)) : Scope (core3P Pf) :=
  { frame := { modFrame c with coreInstances := [] ++ [es] }, exports := [] }

/-- **The definitions of `c.toRef` reach the start function**; after it, they run to the
lifted exports. -/
theorem defs_reaches {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hF : CoreFactsS c I cs ci (some a)) (m : Machine.Config (core3P Pf) Unit)
    (hcore : m.store.core = (core3P Pf).empty _) :
    ∃ tr Post, Reaches prof (refHost Pf).hr (D Pf) none (runStart ⟨0⟩ a)
      (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] []) {} c.toRef) m tr
      { m with store := setCoreSt cs m.store } Post ∧ traceObs tr = [] ∧
      ∀ m₂ : Machine.Config (core3P Pf) Unit, m₂.store.funcs.length = 1 →
        ∃ tr' sc', Post m₂ tr' sc' { m₂ with store := { m₂.store with
          funcs := m₂.store.funcs ++ liftedList (fun k => I.addrs.getD k 0) ⟨0⟩ c.exports } } ∧
          traceObs tr' = [] ∧ funcExports sc'.exports = exportMapS c := by
  have hm₁ := instDef_coreModule (R := callRecurse) (inst := ⟨0⟩) (outer := []) (args := [])
    (σ := Unit) ({} : Scope (core3P Pf)) c.mod.mod
  obtain ⟨tr₀, R₀, ho₀⟩ := core_reaches (prof := prof) hF (modFrame c) rfl m hcore
  have R₁ := Reaches.left (g := fun es => (Pure.pure (coreScope c es) :
        Canon.P (core3P Pf) Unit (Scope (core3P Pf)))) R₀
  have R₂ := Reaches.left (g := fun sc₂ => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] []) sc₂
    (Simple.exportsDefs c.mod 0 c.exports 0)) R₁
  refine ⟨_, ?Post, ?R, ho₀, ?P⟩
  case R =>
    unfold Simple.toRef
    rw [List.cons_append, List.cons_append, List.nil_append]
    dsimp only [List.foldlM]
    have h₀ : RunsQ (D Pf) none (instantiateDef callRecurse ⟨0⟩ [] [] {} (.coreModule c.mod.mod))
        m [] ({ frame := modFrame c, exports := [] } : Scope (core3P Pf)) m := by
      rw [hm₁]
      exact .pure _ _
    refine Reaches.seq (tr₂ := tr₀) h₀ ?_
    show Reaches prof (refHost Pf).hr (D Pf) none (runStart ⟨0⟩ a)
      ((instantiateCore ⟨0⟩ (modFrame c) 0 [] >>= fun es => (pure (coreScope c es) :
        Canon.P (core3P Pf) Unit (Scope (core3P Pf)))) >>= fun sc₂ =>
          List.foldlM (instantiateDef callRecurse ⟨0⟩ [] []) sc₂
            (Simple.exportsDefs c.mod 0 c.exports 0)) _ _ _ _
    exact R₂
  case P =>
    intro m₂ hf
    obtain ⟨sc', hr, hx⟩ := exportsDefs_runO (R := callRecurse) (inst := ⟨0⟩) (outer := [])
      (args := []) c.mod 1 (fun k => I.addrs.getD k 0) c.exports 0
      (coreScope c ((core3P Pf).exports ci)) m₂
      ⟨rfl, rfl, rfl⟩ hf hF.lookup
    obtain ⟨tr₂, hr₂, ho₂⟩ := SRuns.runsQO (dispatch := D Pf) hr none
    refine ⟨_, sc', ⟨_, _, _, _, ⟨_, _, _, _, .pure _ _, .pure _ _, rfl⟩, hr₂, rfl⟩, ?_, ?_⟩
    · simpa [traceObs] using ho₂
    · rw [hx]
      simp [exportMapS, funcExports, coreScope]

theorem runsQ_checkImport {th : Option ThreadId} {r : Except String Unit} (hr : r = .ok ())
    (m : Machine.Config (core3P Pf) Unit) :
    RunsQ (D Pf) th (checkImport r : Canon.P (core3P Pf) Unit Unit) m [] () m := by
  subst hr
  exact .pure _ _

/-- The configuration at the start of the definitions (instance `0` allocated). -/
def allocCfg : Machine.Config (core3P Pf) Unit :=
  { (initConfig () : Machine.Config (core3P Pf) Unit) with
    store := ArenaOps.allocSt ArenaField.insts {}
      (DispatchSt.incNestingSt (initConfig () : Machine.Config (core3P Pf) Unit).store) }

/-- The configuration at the end of the instantiation program, from the configuration `m₂` after
the start function. -/
def endCfg (m₂ : Machine.Config (core3P Pf) Unit) (addr : Nat → Nat) (c : Simple) :
    Machine.Config (core3P Pf) Unit :=
  let s : CStore (core3P Pf) :=
    { m₂.store with funcs := m₂.store.funcs ++ liftedList addr ⟨0⟩ c.exports }
  { m₂ with store := DispatchSt.decNestingSt s }

/-- **The instantiation program reaches the start function**, without observations; after it,
the program runs to `endCfg`, observing the instance and the export map `exportMapS c`. -/
theorem inst_reaches {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    {cs : (core3P Pf).Store (CanonHost (core3P Pf))} {ci : (core3P Pf).Inst} {a : Nat}
    (hF : CoreFactsS c I cs ci (some a)) :
    ∃ tr Post, Reaches prof (refHost Pf).hr (D Pf) none (runStart ⟨0⟩ a)
      (instantiateProg c.toRef [] : Canon.P (core3P Pf) Unit _) (initConfig ()) tr
      { (allocCfg : Machine.Config (core3P Pf) Unit) with
        store := setCoreSt cs (allocCfg : Machine.Config (core3P Pf) Unit).store } Post ∧
      traceObs tr = [] ∧
      ∀ m₂ : Machine.Config (core3P Pf) Unit, m₂.store.funcs.length = 1 →
        ∃ tr', Post m₂ tr' .unit (endCfg m₂ (fun k => I.addrs.getD k 0) c) ∧
          traceObs tr' = [instantiatedObs ⟨0⟩ (exportMapS c)] := by
  obtain ⟨tr₀, Post₀, R₀, ho₀, hP₀⟩ := defs_reaches (prof := prof) hF allocCfg rfl
  have R₁ := Reaches.left (g := fun sc => (pure sc.exports :
    Canon.P (core3P Pf) Unit (Exports (core3P Pf)))) R₀
  have R₂ := Reaches.left (g := fun es => (pure ((⟨0⟩ : InstId), es) :
    Canon.P (core3P Pf) Unit (InstId × Exports (core3P Pf)))) R₁
  have hn := noImport_toRefS hF
  have hac : argsComplete c.toRef ([] : Exports (core3P Pf)) = true := by
    rw [argsComplete, importNames_nil hn]
    rfl
  exact ⟨_, _, by
    unfold instantiateProg
    apply Reaches.seq (runs_modifyStore DispatchSt.incNestingSt
      (initConfig () : Machine.Config (core3P Pf) Unit) rfl)
    dsimp only
    apply Reaches.left
    unfold instantiateRootCall instantiateRoot
    apply Reaches.seq (runs_trapIf ((congrArg (!·) hac).trans rfl) _ _)
    apply Reaches.seq (RunsQ.get (.pure _ _))
    apply Reaches.seq (runsQ_checkImport (precheckImports_ok _ _ _ _ hn) _)
    apply Reaches.seq (runs_allocObj ArenaField.insts {} _ rfl)
    exact R₂, by simpa [traceObs, Label.obs?] using ho₀, by
    intro m₂ hf
    obtain ⟨tr', sc', hP, ho', hx⟩ := hP₀ m₂ hf
    refine ⟨_, ⟨_, _, _, _, ⟨_, _, _, _, ⟨_, _, _, _, hP, .pure _ _, rfl⟩, .pure _ _, rfl⟩,
      RunsQ.modify rfl (RunsQ.emit (.pure _ _)), rfl⟩, ?_⟩
    simp only [traceObs_append, ho']
    simp only [traceObs, List.nil_append, hx]
    rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference
