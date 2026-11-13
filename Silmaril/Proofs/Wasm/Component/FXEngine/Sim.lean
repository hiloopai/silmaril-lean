module

public import Silmaril.Proofs.Wasm.Component.FXEngine.HostMap

/-!
# On numeric modules the WasmFX game semantics is the Core 3.0 game semantics

Proofs for `Silmaril.Wasm.Component.FXEngine.Thms` (`fxG_sem_eq_core3G`).

* `instOf_ofNum`: the FX engine instance of a numeric module (with no FX functions) is the
  `core3P P` instance with its store `SFX` (host code `h` read as `FXCode.host h`);
* `steps_core_SFX`, `steps_of_SFX`: runs of Core threads in `SFX` stores are `core3P P` runs,
  both ways (`internalFX_core_SFX_iff`);
* `simCF`, `simFC`: the transition systems of the two engine instances simulate each other,
  through `mapE` (stores by `SFX`, threads by `ThreadFX.core`), move for move: statuses agree
  (`statusFX_core_SFX`) and so does resumption (`resumeFX_core_SFX`);
* `engineStrategy_SFX`: so their strategies are equal.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXEngine

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component.Reference (NumModule core3P)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (Thread)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile}

/-! ## Instances -/

theorem prepareE?_SFX_nil (s : Store Nat) (m : Silmaril.Wasm.Module) :
    Silmaril.Wasm.Component.Engine.Core3.prepareE? (SFX s) m [] =
      (Silmaril.Wasm.Component.Engine.Core3.prepareE? s m []).map
        fun p => (SFX p.1, p.2.1, p.2.2) := by
  unfold Silmaril.Wasm.Component.Engine.Core3.prepareE?
  cases Silmaril.Wasm.Validation.validate? m with
  | none => rfl
  | some mt =>
    dsimp only
    have he : Silmaril.Wasm.Execution.Core.externAddrsOk? (SFX s) [] mt.imports =
        Silmaril.Wasm.Execution.Core.externAddrsOk? s [] mt.imports := by
      cases mt.imports <;> rfl
    rw [he, Silmaril.Proofs.Wasm.Component.Reference.instantiateOnce?_mapH]
    split
    · cases Silmaril.Wasm.Execution.Core.instantiateOnce? s m [] with
      | none => rfl
      | some p =>
        rcases p with ⟨s', f', _ | x⟩
        · rfl
        · show Option.map _ _ = Option.map _ (Option.map _ _)
          rw [Option.map_map]
          rfl
    · rfl

theorem exportAddrs_fx (inst : Silmaril.Wasm.Execution.Core.ModuleInst) (exps : CoreIface) :
    exportAddrs (fxE P) ⟨inst, []⟩ exps = exportAddrs (core3P P) inst exps := by
  unfold exportAddrs
  simp only [fxE, List.append_nil]
  rfl

theorem prepare_ofNum (m : NumModule) :
    (fxE P).prepare? ((fxE P).empty Nat) (ofNum m) [] =
      (Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m.mod []).map
        fun p => (SFX p.1, (⟨p.2.1, []⟩ : InstFX), p.2.2) := by
  show prepareFX? (SFX {}) (ofNum m) [] = _
  unfold prepareFX?
  rw [show (ofNum m).core = m.mod from rfl, prepareE?_SFX_nil]
  cases Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m.mod [] with
  | none => rfl
  | some p => rfl

/-- **The FX instance of a numeric module is its Core 3.0 instance in an `SFX` store.** -/
theorem instOf_ofNum (m : NumModule) :
    instOf (fxE P) (ofNum m) [] m.exports =
      (instOf (core3P P) m.mod [] m.exports).map fun I => ⟨SFX I.store, I.addrs⟩ := by
  have hco : (core3P P).prepare? ((core3P P).empty Nat) m.mod [] =
      Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m.mod [] := rfl
  unfold instOf
  simp only [allocHosts, List.map_nil]
  rw [prepare_ofNum, hco]
  cases Silmaril.Wasm.Component.Engine.Core3.prepareE? ({} : Store Nat) m.mod [] with
  | none => rfl
  | some p =>
    rcases p with ⟨s', inst, _ | st⟩
    · show Option.map _ (exportAddrs (fxE P) ⟨inst, []⟩ m.exports) =
        Option.map _ (Option.map _ (exportAddrs (core3P P) inst m.exports))
      rw [exportAddrs_fx, Option.map_map]
      rfl
    · rfl

/-! ## Runs -/

theorem internalFX_core_SFX {s s' : Store Nat} {t t' : Thread}
    (h : Silmaril.Wasm.Game.InternalP P (s, t) (s', t')) :
    (fxE P).Internal (SFX s, ThreadFX.core t) (SFX s', ThreadFX.core t') :=
  internalFX_core_SFX_iff.2 ⟨s', t', rfl, h⟩

theorem steps_core_SFX {s s' : Store Nat} {t t' : Thread}
    (h : Steps (core3P P) (s, t) (s', t')) :
    Steps (fxE P) (SFX s, ThreadFX.core t) (SFX s', ThreadFX.core t') :=
  Relation.ReflTransGen.lift (p := (fxE P).Internal)
    (fun x : Store Nat × Thread => (SFX x.1, ThreadFX.core x.2))
    (fun x y h => internalFX_core_SFX (s := x.1) (t := x.2) (s' := y.1) (t' := y.2) h)
    (s, t) (s', t') h

theorem steps_of_SFX {s : Store Nat} {t : Thread} {y : Store (FXCode Nat) × ThreadFX Nat}
    (h : Steps (fxE P) (SFX s, ThreadFX.core t) y) :
    ∃ s' t', y = (SFX s', ThreadFX.core t') ∧ Steps (core3P P) (s, t) (s', t') := by
  induction h with
  | refl => exact ⟨s, t, rfl, .refl⟩
  | tail _ hstep ih =>
    obtain ⟨s₁, t₁, rfl, h₁⟩ := ih
    obtain ⟨s₂, t₂, rfl, h₂⟩ := internalFX_core_SFX_iff.1 hstep
    exact ⟨s₂, t₂, rfl, h₁.tail h₂⟩

/-! ## The simulations -/

theorem fx_resume_core_SFX (s : Store Nat) (t : Thread)
    (r : Silmaril.Wasm.Component.Engine.CallResult) :
    (fxE P).resume (SFX s) (ThreadFX.core t) r = ThreadFX.core ((core3P P).resume s t r) :=
  resumeFX_core_SFX s t r

/-- A hidden state of the Core 3.0 instance as a hidden state of the FX instance. -/
def mapE {n k : Nat} : EState (core3P P) n k → EState (fxE P) n k
  | .idle s => .idle (SFX s)
  | .running q s t => .running q (SFX s) (.core t)
  | .waiting q s t e => .waiting q (SFX s) (.core t) e
  | .refusing q s => .refusing q (SFX s)

/-- Every Core 3.0 move is an FX move. -/
theorem etrans_mapE {addrs : List Nat} {imps exps : CoreIface}
    {x x' : EState (core3P P) imps.length exps.length} {m : Move (sigN imps.length) (sigN exps.length)}
    (h : ETrans (core3P P) addrs imps exps x m x') :
    ETrans (fxE P) addrs imps exps (mapE x) m (mapE x') := by
  cases h with
  | call hc => exact .call hc
  | refuse hc => exact .refuse hc
  | refused => exact .refused
  | ucall run hco hh =>
    exact .ucall (steps_core_SFX run) ((statusFX_core_SFX _ _).trans hco) hh
  | @uret q s t e r =>
    have h := ETrans.uret (E := fxE P) (addrs := addrs) (imps := imps) (exps := exps) (q := q)
      (s := SFX s) (t := ThreadFX.core t) (e := e) r
    have e' := fx_resume_core_SFX (P := P) s t (resultOf imps[e.1].2.results r)
    show ETrans (fxE P) addrs imps exps (EState.waiting q (SFX s) (ThreadFX.core t) e) _
      (EState.running q (SFX s) (ThreadFX.core ((core3P P).resume s t _)))
    exact e' ▸ h
  | oret run hf => exact .oret (steps_core_SFX run) ((statusFX_core_SFX _ _).trans hf)
  | otrap run hf => exact .otrap (steps_core_SFX run) ((statusFX_core_SFX _ _).trans hf)

/-- A run of a Core thread in an `SFX` store is a `core3P P` run, with the same final status. -/
theorem run_of_mapE {s : Store Nat} {t : Thread} {s₁ : Store (FXCode Nat)} {t₁ : ThreadFX Nat}
    (run : Steps (fxE P) (SFX s, ThreadFX.core t) (s₁, t₁)) :
    ∃ s' t', s₁ = SFX s' ∧ t₁ = ThreadFX.core t' ∧ Steps (core3P P) (s, t) (s', t') ∧
      (fxE P).status s₁ t₁ = (core3P P).status s' t' := by
  obtain ⟨s', t', he, run'⟩ : ∃ s' t', (s₁, t₁) = (SFX s', ThreadFX.core t') ∧
      Steps (core3P P) (s, t) (s', t') := steps_of_SFX run
  have h1 : s₁ = SFX s' := congrArg Prod.fst he
  have h2 : t₁ = ThreadFX.core t' := congrArg Prod.snd he
  have hst : (fxE P).status (SFX s') (ThreadFX.core t') = (core3P P).status s' t' :=
    statusFX_core_SFX s' t'
  exact ⟨s', t', h1, h2, run', h1 ▸ h2 ▸ hst⟩

/-- Every FX move of a running Core thread in an `SFX` store is the image of a Core 3.0 move. -/
theorem etrans_of_mapE_running {addrs : List Nat} {imps exps : CoreIface}
    {q : (sigN exps.length).Op} {s : Store Nat} {t : Thread}
    {y' : EState (fxE P) imps.length exps.length} {m : Move (sigN imps.length) (sigN exps.length)}
    (h : ETrans (fxE P) addrs imps exps (.running q (SFX s) (ThreadFX.core t)) m y') :
    ∃ x', ETrans (core3P P) addrs imps exps (.running q s t) m x' ∧ y' = mapE x' := by
  cases h with
  | ucall run hco hh =>
    obtain ⟨s', t', h1, h2, run', hst⟩ := run_of_mapE run
    exact ⟨_, .ucall run' (hst.symm.trans hco) hh, by rw [h1, h2]; rfl⟩
  | oret run hf =>
    obtain ⟨s', t', h1, -, run', hst⟩ := run_of_mapE run
    exact ⟨_, .oret run' (hst.symm.trans hf), by rw [h1]; rfl⟩
  | otrap run hf =>
    obtain ⟨s', t', h1, -, run', hst⟩ := run_of_mapE run
    exact ⟨_, .otrap run' (hst.symm.trans hf), by rw [h1]; rfl⟩

/-- Every FX move from the image of a Core 3.0 state is the image of a Core 3.0 move. -/
theorem etrans_of_mapE {addrs : List Nat} {imps exps : CoreIface}
    {x : EState (core3P P) imps.length exps.length} {y' : EState (fxE P) imps.length exps.length}
    {m : Move (sigN imps.length) (sigN exps.length)}
    (h : ETrans (fxE P) addrs imps exps (mapE x) m y') :
    ∃ x', ETrans (core3P P) addrs imps exps x m x' ∧ y' = mapE x' := by
  cases x with
  | idle s =>
    cases h with
    | call hc => exact ⟨_, .call hc, rfl⟩
    | refuse hc => exact ⟨_, .refuse hc, rfl⟩
  | refusing q s =>
    cases h with
    | refused => exact ⟨_, .refused, rfl⟩
  | waiting q s t e =>
    cases h with
    | uret r =>
      have e' := fx_resume_core_SFX (P := P) s t (resultOf imps[e.1].2.results r)
      exact ⟨_, .uret r, congrArg (EState.running q (SFX s)) e'⟩
  | running q s t => exact etrans_of_mapE_running h

/-- The Core 3.0 instance is simulated by the FX instance. -/
def simCF (I : EInstance (core3P P)) (imps exps : CoreIface) :
    (engineLTS (core3P P) I imps exps).Simulation
      (engineLTS (fxE P) ⟨SFX I.store, I.addrs⟩ imps exps) where
  R x y := y = mapE x
  init := rfl
  step := by
    rintro x x' y l rfl ⟨m, rfl, h⟩
    exact ⟨mapE x', .vis ⟨m, rfl, etrans_mapE h⟩ (.nil _), rfl⟩

/-- The FX instance is simulated by the Core 3.0 instance. -/
def simFC (I : EInstance (core3P P)) (imps exps : CoreIface) :
    (engineLTS (fxE P) ⟨SFX I.store, I.addrs⟩ imps exps).Simulation
      (engineLTS (core3P P) I imps exps) where
  R y x := y = mapE x
  init := rfl
  step := by
    rintro y y' x l rfl ⟨m, rfl, h⟩
    obtain ⟨x', hx, rfl⟩ := etrans_of_mapE h
    exact ⟨x', .vis ⟨m, rfl, hx⟩ (.nil _), rfl⟩

/-- **The strategies of the two instances are equal.** -/
theorem engineStrategy_SFX (I : EInstance (core3P P)) (imps exps : CoreIface) :
    engineStrategy (fxE P) ⟨SFX I.store, I.addrs⟩ imps exps =
      engineStrategy (core3P P) I imps exps :=
  le_antisymm (simFC I imps exps).ofLTS_le (simCF I imps exps).ofLTS_le

end Silmaril.Proofs.Wasm.Component.FXEngine
