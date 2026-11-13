module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkFloatCall
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSound
public import Silmaril.Wasm.Component.Reference.LinkFloat.Defs

/-!
# Soundness of two linked components with floats in the importer's exports

`linkCallPhase` (`LinkSound`) with floats at every type in the importer's exports and
float-free imports (`Linked2.ImportsFloatFree`). The top-level call branches over the NaN
choices of lowering the arguments (`call_trunL`); each branch reaches the importer's core
activation on `lowerArgs params vs'` for an admissible lowering `vs'` and continues as in
`linkCallPhase` (`linkBranchV`), with the results canonicalised by the lift (`CallAtLV`).

The importer-side invariants (`LStat`, `LInv`, `LPlay`) are taken for `l.dropExports`, the linked
component with the importer's exports removed: `LStat` records `l.imp.FloatFree`, but the
segmented run of the importer and its nested exporter calls depend only on the imports, the
wiring and the exporter, so `LStat` of `l.dropExports` asks float-freedom of the imports only;
`lplay_dropExports` transports the resulting play back to `l`.
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

/-! ## The importer without its exports -/

/-- The linked component with the importer's exports removed. -/
def _root_.Silmaril.Wasm.Component.Reference.Linked2.dropExports (l : Linked2) : Linked2 :=
  ⟨l.exp, { l.imp with exports := [] }, l.wire⟩

section Drop

variable {l : Linked2}

theorem expRun_dropExports {Ie : Silmaril.Wasm.Game.ScalarInstance} {s : Store Nat}
    {ds : List (Σ _ : (sigN l.dropExports.imp.imports.length).Op, Option Payload)}
    (h : Linked2.ExpRun P l.dropExports Ie s ds) : Linked2.ExpRun P l Ie s ds := by
  induction h with
  | nil s => exact .nil s
  | ret w hw hr _ ih => exact .ret w hw hr ih
  | trap w hw ht => exact .trap w hw ht

theorem lplay_dropExports {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ π₀ : Store Nat}
    {f : Ii.F.Op} {w : Ii.F.Ar f} (h : LPlay P l.dropExports Ie Ii u₀ π₀ f w) :
    LPlay P l Ie Ii u₀ π₀ f w := by
  obtain ⟨rounds, q, dss, hp, hr, he⟩ := h
  exact ⟨rounds, q, dss, hp, hr, expRun_dropExports he⟩

theorem good_dropExports (h : l.imp.Good) : l.dropExports.imp.Good :=
  ⟨List.nodup_nil, fun _ hx => absurd hx List.not_mem_nil, h.imports⟩

theorem arity_dropExports (h : l.imp.Arity) : l.dropExports.imp.Arity :=
  ⟨fun _ hx => absurd hx List.not_mem_nil, h.2⟩

theorem floatFree_dropExports (h : l.ImportsFloatFree) : l.dropExports.imp.FloatFree :=
  ⟨fun _ hx => absurd hx List.not_mem_nil, h⟩

theorem wireTy_dropExports (h : l.WireTy) : l.dropExports.WireTy := ⟨h.length, h.ty⟩

theorem splitOk_dropExports (h : l.SplitOk) : l.dropExports.SplitOk := ⟨h.exp, h.imp⟩

end Drop

/-! ## One branch of the call -/

section Call

variable {l : Linked2}

/-- **A branch of the linked call with floats**: from the importer's core activation on the
lowering of an admissible argument list `vs'` (`CallAtLV`), every run ending where a call outcome
holds is matched by the linked IR on `vs'`. -/
theorem linkBranchV (hEg : l.exp.Good) (hIg : l.imp.Good) (har : l.imp.Arity)
    (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hn : l.WireNodup) (hS : l.SplitOk)
    {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {cse : (E3 P).Store (CanonHost (E3 P))}
    {cie : (E3 P).Inst} (hFe : CoreFacts (Pf := P) l.exp Ie cse cie) (hI : l.imp.mod.IsInst Ii)
    {r : Store (CanonHost (E3 P) × Nat)} (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : HostsSat (fun h => ∃ (k : Nat) (hk : k < l.imp.imports.length),
      h = (.lowered (l.wireFid k) (witFt l.imp.imports[k].2) {} ⟨2⟩, k)) r)
    (j : Fin l.imp.exports.length) {vs' : List Silmaril.Wasm.Component.Val}
    (hvs' : ValTy.checkList l.imp.exports[j].ty.params vs' = true)
    {M₀ : Machine.Config (E3 P) σ} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) σ (Ret (E3 P))} {segs : List (Seg (E3 P) σ)}
    {rest : List (Activation (E3 P) σ)}
    (hat : CallAtLV prof P impl (reloc cse (Store.mapH Prod.fst r))
      (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
        liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports)
      l.imp.exports[j] (addrL (cse : Store _).funcs.length Ii l.imp.exports[j].core)
      (lowerArgs l.imp.exports[j].ty.params vs') M₀ th K segs rest)
    {tr : List (Label (E3 P) σ)} {m' : Machine.Config (E3 P) σ} {out : CallOutcome}
    (r' : Steps prof (fun _ _ => false) (DI P impl) M₀ tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨0⟩ ev)
    (ho : out.Holds (fun _ _ => false) ⟨0⟩ m') :
    Linked2.IRObsV P l j vs' (Outcome.ofCall out) := by
  have hx : l.imp.exports[j] ∈ l.imp.exports := List.getElem_mem j.isLt
  obtain ⟨nm, hcore⟩ := hIg.core _ hx
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hflat : l.imp.mod.exports[l.imp.exports[j].core] = (nm, l.imp.exports[j].ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcore).2
  have hxs : (lowerArgs l.imp.exports[j].ty.params vs').map (·.type) =
      l.imp.mod.exports[l.imp.exports[j].core].2.params := by
    rw [hflat]
    exact lowerList_types _ _ hvs'
  obtain ⟨f, hf₁, hf₂, hft⟩ := typedCallI hI hk hxs
  have hft' : Ii.exports.get f.1 = fnOf l.imp.exports[j].ty.flat := by rw [hft, hflat]
  have hlen : f.1.val < Ii.addrs.length := by
    rw [hI.1.choose_spec.ok.addrs_length]
    exact f.1.isLt
  have ha : addrL (cse : Store _).funcs.length Ii l.imp.exports[j].core =
      Ie.store.funcs.length + Ii.addr f.1 := by
    rw [← hf₁, addrL_eq _ hlen, coreFacts_length hFe]
    rfl
  have S : LStat P l.dropExports Ie Ii Ii.store (reloc (cse : Store (CanonHost (E3 P)))
      (Store.mapH Prod.fst r)).funcs M₀ (ownOf Ie.store) :=
    lstat_init (l := l.dropExports) hEg (good_dropExports hIg) (wireTy_dropExports hW) hn
      (arity_dropExports har) (floatFree_dropExports hfi) hFe hI hh _ hat.funcs
  have hI₀ := linv_afterLink (l := l.dropExports) (splitOk_dropExports hS) hn
    (wireTy_dropExports hW) hFe hI hrs hh hf₂
  rw [← ha] at hI₀
  have r'' : Steps prof (fun _ _ => false) (DI P impl) (coreCfg (extN M₀ {} [] M₀.conts) th K
      segs rest (reloc cse (Store.mapH Prod.fst r), Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
        (addrL (cse : Store _).funcs.length Ii l.imp.exports[j].core)
        (lowerArgs l.imp.exports[j].ty.params vs'))) tr m' := by
    rw [← hat.start]
    exact r'
  obtain ⟨recs, y, hseg, hexit | hfail⟩ := lsegs_inv (cid := ⟨0⟩) hat.frame tr.length {} []
    M₀.conts _ tr m' out le_rfl threadsOk_empty (LInv.linkOk S hI₀) r'' ho
  · obtain ⟨ιe', N', C', pre, l', m₁, tr₂, rfl, -, hnco, hx', r₂⟩ := hexit
    have hev₂ : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev :=
      fun ev hm => hev ev (List.mem_append_right _ hm)
    rcases hx' with ⟨zs, hst, -, rfl⟩ | ⟨hst, -, rfl⟩ | ⟨h', ys', hc'⟩
    · obtain ⟨w, cvs, hP, hm, hw⟩ := lplay_values S hI₀ hseg hst
      have hty := results_typed hft' hw hm
      have hR := lifted_answer (x := l.imp.exports[j]) hw hm
      have hir := ir_of_lplay hEg hIg hFe.isInst hI j hvs' hf₁ hf₂ (lplay_dropExports hP)
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
      have hir := ir_of_lplay hEg hIg hFe.isInst hI j hvs' hf₁ hf₂ (lplay_dropExports hP)
      rw [hnone] at hir
      exact hir
    · exact absurd hc' (hnco h' ys')
  · obtain ⟨fid, a, p, ys, hst, hf, hp, rfl, hfl⟩ := hfail
    exact ir_of_lplay hEg hIg hFe.isInst hI j hvs' hf₁ hf₂
      (lplay_dropExports (lplay_fail S hI₀ hseg hst hf hp hfl))

/-- **The call phase of a linked component with floats in the importer's exports**: every
behaviour of the call of the importer's export `j` on the images of well-typed values is matched
by the linked IR on an admissible lowering `vs'` of the arguments, returned values
canonicalised. -/
theorem linkCallPhaseV (hEg : l.exp.Good) (hIg : l.imp.Good) (har : l.imp.Arity)
    (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hn : l.WireNodup) (hS : l.SplitOk)
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
      ∃ vs', NanAtVList prof l.imp.exports[j].ty.params vs vs' ∧
        ValTy.checkList l.imp.exports[j].ty.params vs' = true ∧ Linked2.IRObsV P l j vs' b := by
  have hx : l.imp.exports[j] ∈ l.imp.exports := List.getElem_mem j.isLt
  obtain ⟨hmax, hmaxr, hres⟩ := har.1 _ hx
  have hT := call_trunL (impl := impl) prof (reloc cse (Store.mapH Prod.fst r))
    (liftedList (fun k => Ie.addrs.getD k 0) ⟨1⟩ l.exp.exports ++
      liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports) h₀
    (l.exp.exports.length + j) _ l.imp.exports[j] vs hvs hmax hres hmaxr
    (afterLink_lifted _ _ j)
  intro b hb
  rcases hb with ⟨m', out, hcalls, rfl⟩ | ⟨rfl, m₁, s, hd⟩
  · obtain ⟨tr, hs, hev, -, ho⟩ := hcalls
    obtain ⟨m₂, s, r₁⟩ := Steps.cons_iff.mp hs
    have r₀ := invoke_inv3 s ▸ r₁
    rcases hT.inv r₀ with hl | ⟨mq, tr₁, tr₂, hq, e, r'⟩
    · exact absurd ho (hl.not_holds _ _)
    obtain ⟨vs', th, K, segs, rest, hnan, hck', hat⟩ := hq
    have hev' : ∀ ev, Label.host ev ∈ tr₂ → CallHostEvent ⟨0⟩ ev :=
      fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
    exact ⟨vs', hnan, hck', linkBranchV hEg hIg har hfi hW hn hS hFe hI hrs hh j hck' hat r'
      hev' ho⟩
  · obtain ⟨mq, hq, -⟩ := hT.diverges (invoke_inv3 s ▸ hd)
    obtain ⟨vs', -, -, -, -, hnan, hck', -⟩ := hq
    exact ⟨vs', hnan, hck', trivial⟩

/-- **Soundness of two linked components with floats in the importer's exports** (every profile
and component choice profile): `linked2_sound` with `l.imp.FloatFree` weakened to float-free
imports; the IR is called on an admissible lowering `vs'` of the arguments (`NanAtVList prof`),
returned values canonicalised (`Linked2.IRObsV`). -/
theorem linked2_sound_floatV (P : Profile) (prof : ProfileKind) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehaviours prof (linkHost impl) h₀ l.toRef [] l.imp.exports[j].name
        (vs.map toRefVal),
      ∃ vs', NanAtVList prof l.imp.exports[j].ty.params vs vs' ∧
        ValTy.checkList l.imp.exports[j].ty.params vs' = true ∧ Linked2.IRObsV P l j vs' b := by
  obtain ⟨Ie, cse, cie, hFe, hall⟩ := instBehavioursL_inst (Pf := P) (σ := σ) hEg hEi hIg hIi har
    ⟨hS.imp.data, hS.imp.elems⟩ hW hN
  obtain ⟨Ii, hI⟩ := hIi.inst
  obtain ⟨r, hrs, hh, hres⟩ := hall Ii hI
  have hcall := linkCallPhaseV (prof := prof) (impl := impl) hEg hIg har hfi hW hn hS hFe hI hrs
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

/-- **Under the deterministic component profile** the IR is called on the canonicalised
arguments. -/
theorem linked2_sound_floatV_deterministic (P : Profile) (l : Linked2) (hEg : l.exp.Good)
    (hEi : l.exp.Inst) (hIg : l.imp.Good) (hIi : l.imp.Inst) (har : l.imp.Arity)
    (hfi : l.ImportsFloatFree) (hW : l.WireTy) (hN : l.NamesOk) (hn : l.WireNodup)
    (hS : l.SplitOk) {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (j : Fin l.imp.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList l.imp.exports[j].ty.params vs = true) :
    ∀ b ∈ exportBehaviours .deterministic (linkHost impl) h₀ l.toRef [] l.imp.exports[j].name
        (vs.map toRefVal),
      Linked2.IRObsV P l j (canonAtVList l.imp.exports[j].ty.params vs) b := by
  intro b hb
  obtain ⟨vs', hnan, -, ho⟩ := linked2_sound_floatV P .deterministic l hEg hEi hIg hIi har hfi hW
    hN hn hS impl h₀ j vs hvs b hb
  rw [← nanAtVList_deterministic _ _ _ hnan]
  exact ho

end Call

end Silmaril.Proofs.Wasm.Component.Reference
