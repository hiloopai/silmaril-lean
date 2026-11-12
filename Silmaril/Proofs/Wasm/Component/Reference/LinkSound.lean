module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkCall
public import Silmaril.Proofs.Wasm.Component.Reference.LinkIR
public import Silmaril.Wasm.Component.Reference.LinkSound.Defs

/-!
# Soundness of two linked components, assembled

The call phase of `Linked2.toRef` (`linkCallPhase`): from `afterLink`, the importer's
top-level call runs to its core activation (`call_atL`); every run of it ending where a call
outcome holds is, by `lsegs_inv` (with `LinkOk` from `LInv.linkOk`), a segmented run of the
importer with nested exporter calls followed by an exit of the core phase, or a failing callout.
From `LInv` at the start (`linv_afterLink`) and `LStat` (`lstat_init`), the segmented run is an
importer play whose component import calls are answered by the exporter from its instance's
store (`LPlay`: `lplay_values`, `lplay_trap`, `lplay_fail`), and `linked2_specToIR` turns it
into the two-move play of `l.toComp`; the machine outcome of the exit is the lifted results
(`CallAtL.ret`, `out_of_resolvesD`) or a trap. With the instantiation (`instBehavioursL_inst`)
this is `linked2_sound`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN)

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## Outcomes under `DI P impl` -/

theorem out_of_resolvesD {m₁ m' : Machine.Config (E3 P) σ} {rs : List Silmaril.Wasm.Component.Reference.Val}
    {tr : List (Label (E3 P) σ)} {out : CallOutcome} (hR : ResolvesD prof P impl m₁ rs)
    (hs : Steps prof (fun _ _ => false) (DI P impl) m₁ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (fun _ _ => false) ⟨0⟩ m') : out = .resolved (some rs) := by
  obtain ⟨tr₃, mE, hlr, hctl, hlock, hres, htick⟩ := hR
  rcases hlr.inv hs with hl | ⟨tr₄, e, r⟩
  · exact absurd ho (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₄ → CallHostEvent ⟨0⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  have hq := quiet hctl (by rw [hres]; simp) htick _ tr₄ m' le_rfl r hev'
  rcases hq with rfl | hl
  · cases out with
    | resolved r => exact congrArg _ (Option.some.inj (ho.2.2.symm.trans hres))
    | trap => exact absurd (ho.symm.trans hlock) (by decide)
    | deadlock => exact absurd (ho.2.symm.trans hres) (by simp)
  · exact absurd ho (hl.not_holds _ _)

/-! ## The IR play -/

section IR

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}

/-- **An importer play answered by the exporter is a play of the linked IR**, with the lifted
answer. -/
theorem ir_of_lplay (hEg : l.exp.Good) (hIg : l.imp.Good) (hIe : l.exp.mod.IsInst Ie)
    (hI : l.imp.mod.IsInst Ii) (j : Fin l.imp.exports.length) {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) {f : Ii.F.Op}
    (hf₁ : f.1.val = l.imp.exports[j].core)
    (hf₂ : f.2.1 = (lowerArgs l.imp.exports[j].ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat)
    {w : Ii.F.Ar f} (hP : LPlay P l Ie Ii Ii.store Ie.store f w) :
    [.inr (.ask (⟨j, by simp [Linked2.exports_length_toComp]⟩, .vals vs)),
      .inr (.ans (m := (⟨j, by simp [Linked2.exports_length_toComp]⟩, .vals vs))
        ((answerPayload w).bind (Silmaril.Wasm.Component.Adapter.up (.lift l.imp.exports[j].ty))))] ∈
      l.toComp.den (impSem P) := by
  obtain ⟨rounds, q, dss, hpath, hrel, hexp⟩ := hP
  have hck : checkLower l.imp.exports[j].ty.params vs =
      some (lowerArgs l.imp.exports[j].ty.params vs) := by
    simp only [checkLower, hvs, ↓reduceIte]
  exact (linked2_specToIR P l hEg hIg Ie hIe Ii hI j vs).2 _ hck f hf₁ hf₂ rounds w q hpath dss
    hrel hexp

end IR

/-! ## The call phase -/

section Call

variable {l : Linked2}

/-- The importer's lifted export `j` among the component functions of `afterLink`. -/
theorem afterLink_lifted (addrE addrI : Nat → Nat) (j : Fin l.imp.exports.length) :
    (liftedList (Pf := P) addrE ⟨1⟩ l.exp.exports ++ liftedList addrI ⟨2⟩ l.imp.exports)[
      l.exp.exports.length + j]? =
      some (.lifted (addrI l.imp.exports[j].core) (liftedFt l.imp.exports[j]) {} ⟨2⟩) := by
  rw [List.getElem?_append_right (by simp [liftedList])]
  simp [liftedList]

/-- The exporter's core store has as many functions as its instance's store. -/
theorem coreFacts_length {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (E3 P).Store (CanonHost (E3 P))} {cie : (E3 P).Inst}
    (hFe : CoreFacts (Pf := P) l.exp Ie cse cie) :
    (cse : Store (CanonHost (E3 P))).funcs.length = Ie.store.funcs.length := by
  rw [← hFe.store]
  simp [Store.mapH]

/-- The shared address of the importer's export `k`. -/
theorem addrL_eq {Ii : Silmaril.Wasm.Game.ScalarInstance} (b : Nat) {k : Nat}
    (hk : k < Ii.addrs.length) : addrL b Ii k = b + Ii.addrs.getD k 0 := by
  simp [addrL, List.getD_eq_getElem?_getD, hk]

/-- **The call phase of a linked component**: from the configuration after instantiating
`l.toRef` (the core facts of the exporter, the importer's game instance `Ii` and its store `r` of
`instBehavioursL_inst`), every behaviour of the call of the importer's export `j` on the images
of well-typed values, under `linkHost impl`, is matched by the linked IR. -/
theorem linkCallPhase (hEg : l.exp.Good) (hIg : l.imp.Good) (har : l.imp.Arity)
    (hff : l.imp.FloatFree) (hW : l.WireTy) (hn : l.WireNodup) (hS : l.SplitOk)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P).Store (CanonHost (E3 P))}
    {cie : (E3 P).Inst} (hFe : CoreFacts (Pf := P) l.exp Ie cse cie) (hI : l.imp.mod.IsInst Ii)
    {r : Store (CanonHost (E3 P) × Nat)} (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r)
    (h₀ : σ) (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    ∀ b ∈ callBehaviours prof (linkHost impl)
        (afterLink P (reloc cse (Store.mapH Prod.fst r)) (fun k => Ie.addrs.getD k 0)
          (addrL (cse : Store _).funcs.length Ii) l h₀) ⟨0⟩
        ⟨l.exp.exports.length + j⟩ (vs.map toRefVal),
      Linked2.IRObs P l j vs b := by
  have hx : l.imp.exports[j] ∈ l.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := hIg.core _ hx
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : l.imp.mod.exports[l.imp.exports[j].core] = (nm, l.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs l.imp.exports[j].ty.params vs).map (·.type) =
      l.imp.mod.exports[l.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI hI hk hxs
  have hft' : Ii.exports.get f.1 = fnOf l.imp.exports[j].ty.flat := by rw [hft, hflat]
  obtain ⟨hmax, hmaxr, hres⟩ := har.1 _ hx
  obtain ⟨hpf, hrf⟩ := hff.1 _ hx
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atL (impl := impl) prof
    (reloc cse (Store.mapH Prod.fst r))
    (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
      liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) h₀
    (l.exp.exports.length + j) _ l.imp.exports[j] vs hpf hvs hmax hres hmaxr hrf
    (afterLink_lifted _ _ j)
  have hlen : f.1.val < Ii.addrs.length := by
    rw [hI.1.choose_spec.ok.addrs_length]
    exact f.1.isLt
  have ha : addrL (cse : Store _).funcs.length Ii l.imp.exports[j].core =
      Ie.store.funcs.length + Ii.addr f.1 := by
    rw [← hf₁, addrL_eq _ hlen, coreFacts_length hFe]
    rfl
  have S : LStat P l Ie Ii Ii.store (reloc (cse : Store (CanonHost (E3 P)))
      (Store.mapH Prod.fst r)).funcs M₀ (ownOf Ie.store) :=
    lstat_init hEg hIg hW hn har hff hFe hI hh _ hat.funcs
  have hI₀ := linv_afterLink hS hn hW hFe hI hrs hh hf₂
  rw [← ha] at hI₀
  intro b hb
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, -⟩
  · obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
    obtain ⟨m₂, s, r₁⟩ := Steps.cons_iff.mp hs
    have r₀ := invoke_inv3 s ▸ r₁
    rcases hpre.inv r₀ with hl | ⟨tr'', e, r'⟩
    · exact absurd ho (hl.not_holds _ _)
    have r'' : Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN M₀ {} [] M₀.conts) th K
        segs rest (reloc cse (Store.mapH Prod.fst r), Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
          (addrL (cse : Store _).funcs.length Ii l.imp.exports[j].core)
          (lowerArgs l.imp.exports[j].ty.params vs))) tr'' m' := by
      rw [← hat.start]
      exact r'
    have hev' : ∀ ev, Label.host ev ∈ tr'' → CallHostEvent ⟨0⟩ ev :=
      fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
    obtain ⟨recs, y, hseg, hexit | hfail⟩ := lsegs_inv (cid := ⟨0⟩) hat.frame tr''.length {} []
      M₀.conts _ tr'' m' out le_rfl threadsOk_empty (LInv.linkOk S hI₀) r'' ho
    · obtain ⟨ιe', N', C', pre, l', m₁, tr₂, rfl, -, hnco, hx', r₂⟩ := hexit
      have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev :=
        fun ev hm => hev' ev (List.mem_append_right _ hm)
      rcases hx' with ⟨zs, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h', ys', hc'⟩
      · obtain ⟨w, cvs, hP, hm, hw⟩ := lplay_values S hI₀ hseg hst
        have hty := results_typed hft' hw hm
        have hR := lifted_answer (x := l.imp.exports[j]) hw hm
        have hir := ir_of_lplay hEg hIg hFe.isInst hI j hvs hf₁ hf₂ hP
        cases hl : liftArgs l.imp.exports[j].ty.results zs with
        | some ws =>
          rw [out_of_resolvesD (hat.ret ιe' N' C' y zs ws hty hl) r₂ hev₂ ho]
          rw [hR, hl] at hir
          exact ⟨ws, rfl, hir⟩
        | none =>
          rw [(hat.trap ιe' N' C' y zs hty hl).trapsFrom.out r₂ ho]
          rw [hR, hl] at hir
          exact hir
      · rw [steps_of_locked rfl rfl r₂] at ho
        rw [holds_trapCfgD ho]
        obtain ⟨w, hP, hnone⟩ := lplay_trap S hI₀ hseg hst
        have hir := ir_of_lplay hEg hIg hFe.isInst hI j hvs hf₁ hf₂ hP
        rw [hnone] at hir
        exact hir
      · exact absurd hc' (hnco h' ys')
    · obtain ⟨fid, a, p, ys, hst, hf, hp, rfl, hfl⟩ := hfail
      exact ir_of_lplay hEg hIg hFe.isInst hI j hvs hf₁ hf₂ (lplay_fail S hI₀ hseg hst hf hp hfl)
  · trivial

/-- The export map of `l.toRef` finds the importer's export `j` at function `n + j`, `n` the
number of the exporter's exports. -/
theorem exportMapL_lookup (hIg : l.imp.Good) (j : Fin l.imp.exports.length) :
    (exportMapL l).lookup l.imp.exports[j].name = some ⟨l.exp.exports.length + j⟩ :=
  lookup_mapIdx_val (·.name) (fun i => (⟨i⟩ : FuncId)) l.exp.exports.length l.imp.exports j j.isLt
    hIg.names

/-- **Soundness of two linked components for single calls** (every profile and component choice
profile): for an exporter and an importer in the instantiation fragment (`Good`, `Inst`), the
importer float-free and within the flat arities, the wiring well typed (`WireTy`) and injective
(`WireNodup`), export names avoiding generated type names (`NamesOk`) and both core modules in
the split fragment (`SplitOk`), every behaviour of instantiating `l.toRef` and calling the
importer's export `j` on the reference images of well-typed IR values, under `linkHost impl`
from any host state, is matched by the linked IR denotation over `impSem P`
(`Linked2.IRObs`). -/
theorem linked2_sound (P : Profile) (prof : ProfileKind) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hff : l.imp.FloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehaviours prof (linkHost impl) h₀ l.toRef [] l.imp.exports[j].name
        (vs.map toRefVal),
      Linked2.IRObs P l j vs b := by
  obtain ⟨Ie, cse, cie, hFe, hall⟩ := instBehavioursL_inst (Pf := P) (σ := σ) hEg hEi hIg hIi har
    ⟨hS.imp.data, hS.imp.elems⟩ hW hN
  obtain ⟨Ii, hI⟩ := hIi.inst
  obtain ⟨r, hrs, hh, hres⟩ := hall Ii hI
  have hcall := linkCallPhase (prof := prof) (impl := impl) hEg hIg har hff hW hn hS hFe hI hrs
    hh h₀ j vs hvs
  intro b hb
  rcases hb with ⟨m₁, inst, es, f, hr, hl, hb⟩ | ⟨-, hr⟩ | ⟨-, hr⟩
  · have he := hres prof (linkHost impl) h₀ _ hr
    obtain ⟨rfl, rfl, rfl⟩ : m₁ = afterLink P (reloc cse (Store.mapH Prod.fst r))
        (fun k => Ie.addrs.getD k 0) (addrL (cse : Store _).funcs.length Ii) l h₀ ∧
        inst = ⟨0⟩ ∧ es = exportMapL l := by
      simpa only [InstResult.instance.injEq] using he
    have hf : f = ⟨l.exp.exports.length + j⟩ :=
      Option.some.inj (hl.symm.trans (exportMapL_lookup hIg j))
    exact hcall b (hf ▸ hb)
  · exact absurd (hres prof (linkHost impl) h₀ _ hr) (by simp)
  · exact absurd (hres prof (linkHost impl) h₀ _ hr) (by simp)

end Call

end Silmaril.Proofs.Wasm.Component.Reference
