module

public import Silmaril.Wasm.Component.Lime1RefE.Defs
public import Silmaril.Wasm.Component.EngineRef.Thms
public import Silmaril.Proofs.Wasm.Component.Lime1RefE.Prepare
import Silmaril.Proofs.Wasm.Component.Reference.InstCore
import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR

/-!
# The engine facts of `lime1`, and the machine half for Lime1 from the two open ones

* `imports_nil`, `ofCore_imports`: a `Simple.Inst` component's Core module has no imports, and
  neither has its Lime1 decoding;
* `instOf_lime1`, `prepare_canon`: an engine instance of `lime1` (at host type `Nat`) comes from
  a preparation in the empty store, which also succeeds at the machine's host type
  `CanonHost lime1` with a store relabelling to the instance store (`lime1_prepare_relabel`);
* `instFacts_lime1`: **the instantiation facts** (`EngineRef.InstFacts`) of `lime1` for every
  component of the Lime1 domain with an engine instance;
* `runFacts_lime1`: **the run facts** (`EngineRef.RunFacts`) of a typed call, from
  `Lime1TypedOk`: no callout (the prepared store has no host function and host-free runs keep
  the function list), returned and trapping runs and divergence relabel to runs of the engine
  instance (`engineOut`, `engineDiverges`);
* `specOut_sub`: these outcomes are in `exportSpecE lime1 Lime1G.lime1G.emb`;
* `refToSpecE_lime1_of`: **`RefToSpecELime1` from `Lime1InstOk` and
  `Lime1TypedOk`**, through `EngineRef.refToSpecEOn_of_facts`.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Lime1Ref Silmaril.Wasm.Component.EngineRef Silmaril.Wasm.Component.Lime1RefE
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)
open Silmaril.Wasm.Component.Runtime (CanonHost)

namespace Silmaril.Proofs.Wasm.Component.Lime1RefE

/-- The Core module of a `Simple.Inst` component has no imports. -/
theorem imports_nil {c : Simple} (hi : c.Inst) : c.mod.mod.imports = [] := by
  obtain ⟨I, mt, cs, f', -, hv, hmt, -⟩ :=
    Silmaril.Proofs.Wasm.Component.Reference.inst_once (H := Nat) id hi
  cases Silmaril.Wasm.Validation.validate?_sound hv with
  | mk _ himports =>
    subst hmt
    exact List.forall₂_nil_right_iff.1 himports

theorem ofCore_imports {m : Silmaril.Wasm.Module} {l : Silmaril.Wasm.Lime1.Module}
    (h : Silmaril.Wasm.Lime1.Module.ofCore? m = some l) (hm : m.imports = []) : l.imports = [] := by
  unfold Silmaril.Wasm.Lime1.Module.ofCore? at h
  rw [hm] at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, List.mapM_nil] at h
    obtain ⟨_, -, _, h₁, _, -, _, -, _, -, _, -, _, -, _, -, _, -, h⟩ := h
    cases h₁
    cases h
    rfl

theorem mapM_getElem? {α β : Type} {f : α → Option β} :
    ∀ {L : List α} {R : List β}, L.mapM f = some R → ∀ {k : Nat} {x : α}, L[k]? = some x →
      ∃ y, f x = some y ∧ R[k]? = some y
  | [], _, _, _, _, hx => by simp at hx
  | a :: L, R, h, k, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨b, hb, R', hR', e⟩ := h
    cases e
    cases k with
    | zero =>
      cases (Option.some.inj hx)
      exact ⟨b, hb, rfl⟩
    | succ k => exact mapM_getElem? hR' hx

theorem instOf_lime1 {m : Silmaril.Wasm.Lime1.Module} {exps : CoreIface} {I : EInstance lime1}
    (h : instOf lime1 m [] exps = some I) :
    ∃ inst, lime1.prepare? (lime1.empty Nat) m [] = some (I.store, inst, none) ∧
      exportAddrs lime1 inst exps = some I.addrs := by
  unfold instOf at h
  simp only [allocHosts, List.map_nil] at h
  split at h
  · rename_i s' inst heq
    obtain ⟨addrs, ha, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨inst, heq, ha⟩
  · cases h

theorem prepare_canon {m : Silmaril.Wasm.Lime1.Module} {s' : lime1.Store Nat} {inst : lime1.Inst}
    (h : lime1.prepare? (lime1.empty Nat) m [] = some (s', inst, none)) :
    ∃ cs : lime1.Store (CanonHost lime1),
      lime1.prepare? (lime1.empty _) m [] = some (cs, inst, none) ∧
      Store.relabel (fun _ => (0 : Nat)) cs = s' := by
  have e := lime1_prepare_relabel (fun _ : CanonHost lime1 => (0 : Nat)) {} m []
  change lime1.prepare? (lime1.empty Nat) m [] = _ at e
  rw [h] at e
  obtain ⟨⟨cs, inst', o⟩, hp, he⟩ := Option.map_eq_some_iff.1 e.symm
  simp only [Prod.mk.injEq] at he
  obtain ⟨hs, rfl, rfl⟩ := he
  exact ⟨cs, hp, hs⟩

/-- The relabelling from the machine's host type to `Nat`. -/
abbrev g0 : CanonHost lime1 → Nat := fun _ => 0

/-- **The instantiation facts of `lime1`** from an engine instance. -/
theorem instFacts_lime1 {c : Simple} (hD : Lime1Dom c) (hc : c.Good) (hi : c.Inst)
    {I : EInstance lime1}
    (hI : instOf lime1 (ofCoreL c.mod.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some I) :
    ∃ (cs : lime1.Store (CanonHost lime1)) (ci : lime1.Inst),
      InstFacts lime1 ofCoreL c cs ci (fun k => I.addrs.getD k ⟨0⟩) ∧
      Store.relabel g0 cs = I.store ∧ NoHost cs ∧
      ∀ (k : Nat) (nm : String) (ft : CoreFuncTy), c.mod.exports[k]? = some (nm, ft) →
        ∃ a, I.addrs[k]? = some a := by
  obtain ⟨inst, hp, ha⟩ := instOf_lime1 hI
  obtain ⟨cs, hpc, hrel⟩ := prepare_canon hp
  have hlook : ∀ (k : Nat) (nm : String) (ft : CoreFuncTy), c.mod.exports[k]? = some (nm, ft) →
      ∃ a, ((lime1.exports inst).lookup nm).bind lime1.asFunc? = some a ∧ I.addrs[k]? = some a :=
    fun k nm ft hk => mapM_getElem? ha hk
  refine ⟨cs, inst, ⟨?_, hpc, fun x hx => ?_⟩, hrel, lime1_prepare_noHost noHost_empty hpc,
    fun k nm ft hk => (hlook k nm ft hk).imp fun _ h => h.2⟩
  · obtain ⟨l, hl, -⟩ := hD
    have he : ofCoreL c.mod.mod = l := by simp only [ofCoreL, hl, Option.getD_some]
    rw [he]
    change l.imports.filterMap _ = []
    rw [ofCore_imports hl (imports_nil hi)]
    rfl
  · obtain ⟨n, hn⟩ := hc.core x hx
    obtain ⟨a, hy, hk⟩ := hlook _ _ _ hn
    obtain ⟨v, hv, hva⟩ := Option.bind_eq_some_iff.1 hy
    refine ⟨v, ?_, ?_⟩
    · rw [coreNameE, hn]
      exact hv
    · rw [List.getD_eq_getElem?_getD, hk]
      exact hva

/-- **The run facts of `lime1`** for a typed call of an export of the instance. -/
theorem runFacts_lime1 (hT : Lime1TypedOk) {c : Simple} (hD : Lime1Dom c) (hc : c.Good)
    (hi : c.Inst) {I : EInstance lime1}
    (hI : instOf lime1 (ofCoreL c.mod.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some I)
    {cs : lime1.Store (CanonHost lime1)} (hrel : Store.relabel g0 cs = I.store)
    (hnh : NoHost cs) {x : SimpleExport} {n : String}
    (hn : c.mod.exports[x.core]? = some (n, x.ty.flat)) {a : lime1.FuncAddr}
    (hk : I.addrs[x.core]? = some a) {xs : List Flat}
    (hxs : xs.map (·.type) = ValTy.flatList x.ty.params) :
    RunFacts lime1 cs a xs (ValTy.flatList x.ty.results) (engineOut lime1 I x.core xs)
      (engineDiverges lime1 I x.core xs) := by
  have e₀ : cfgRelabel g0 (cs, lime1.invoke a xs) = (I.store, lime1.invoke a xs) := by
    rw [← hrel]
    rfl
  have hrun : ∀ {s' : lime1.Store (CanonHost lime1)} {t' : lime1.Thread (CanonHost lime1)},
      Silmaril.Wasm.Component.Engine.CoreEngine.Steps lime1 (cs, lime1.invoke a xs) (s', t') →
      Silmaril.Wasm.Component.Engine.CoreEngine.Steps lime1 (I.store, lime1.invoke a xs)
        (Store.relabel g0 s', ⟨t'.frame, t'.code⟩) :=
    fun run => e₀ ▸ steps_relabel (g := g0) run
  refine ⟨@fun s' t' h args run => ?_, @fun s' t' ys run hst => ?_, @fun s' t' run hst => ?_,
    fun hd => ?_⟩
  · have hf : s'.funcs = cs.funcs := steps_funcs run
    have hnh' : NoHost s' := fun i ft hh => hf ▸ hnh i ft hh
    exact status_ne_callout hnh' t' h args
  · have hst' : lime1.status (Store.relabel g0 s') ⟨t'.frame, t'.code⟩ = .returned (.values ys) :=
      status_returned (t := t') (Store.relabel g0 s') ⟨t'.frame, t'.code⟩ rfl hst
    have hty : ys.map (·.type) = ValTy.flatList x.ty.results :=
      hT c hD hc hi I hI x.core n x.ty.flat hn a hk xs hxs _ _ ys (hrun run) hst'
    exact ⟨⟨a, _, _, hk, hrun run, Or.inl ⟨ys, hst', rfl⟩⟩, hty⟩
  · have hst' : lime1.status (Store.relabel g0 s') ⟨t'.frame, t'.code⟩ = .returned .trap :=
      status_returned (t := t') (Store.relabel g0 s') ⟨t'.frame, t'.code⟩ rfl hst
    exact ⟨a, _, _, hk, hrun run, Or.inr ⟨hst', rfl⟩⟩
  · have hd' : Silmaril.Wasm.Component.Engine.CoreEngine.Diverges lime1
        (I.store, lime1.invoke a xs) := e₀ ▸ diverges_relabel (g := g0) hd
    exact ⟨a, hk, hd'⟩

/-- The run outcomes of a typed call are in the engine's specification. -/
theorem specOut_sub {c : Simple} {I : EInstance lime1}
    (hI : instOf lime1 (ofCoreL c.mod.mod) (CoreModule.imports c.mod) (CoreModule.exports c.mod) =
      some I) (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList x.ty.params vs = true) :
    specOut x (engineOut lime1 I x.core (lowerArgs x.ty.params vs))
        (engineDiverges lime1 I x.core (lowerArgs x.ty.params vs)) ⊆
      exportSpecE lime1 Lime1G.lime1G.emb c x vs := by
  have hl : checkLower x.ty.params vs = some (lowerArgs x.ty.params vs) := by
    unfold checkLower
    rw [ite_eq_left_iff.mpr (fun h => absurd hvs h)]
  intro b hb
  unfold exportSpecE
  rw [hl]
  rcases hb with ⟨r, hr, rfl⟩ | ⟨rfl, hd⟩
  · exact Or.inl ⟨I, hI, r, hr, rfl⟩
  · exact Or.inr ⟨rfl, I, hI, hd⟩

/-- **The machine half for Lime1 from the two open engine facts.** -/
theorem refToSpecE_lime1_of (hI : Lime1InstOk) (hT : Lime1TypedOk) :
    RefToSpecELime1 := by
  refine refToSpecEOn_of_facts fun c hD hc hf hi ha => ?_
  obtain ⟨I, hI'⟩ := hI c hD hc hi
  obtain ⟨cs, ci, hF, hrel, hnh, haddr⟩ := instFacts_lime1 hD hc hi hI'
  refine ⟨cs, ci, _, hF, fun x hx vs hvs => ⟨_, _, ?_, specOut_sub hI' x vs hvs⟩⟩
  obtain ⟨n, hn⟩ := hc.core x hx
  obtain ⟨a, hk⟩ := haddr _ _ _ hn
  have hget : I.addrs.getD x.core ⟨0⟩ = a := by
    rw [List.getD_eq_getElem?_getD, hk]
    rfl
  rw [hget]
  exact runFacts_lime1 hT hD hc hi hI' hrel hnh hn hk
    (Silmaril.Proofs.Wasm.Component.Reference.lowerList_types _ _ hvs)

end Silmaril.Proofs.Wasm.Component.Lime1RefE
