module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv.Round
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Sess

/-!
# Diverging linked calls through an abstract exporter, forward: calls and sessions

* `linkDiv_fwdB`: from a configuration between calls (`ReadyB` at the importer's store `u` and
  the exporter's state `π`), a round that never answers (`LinkedG.RoundDiv`) is a diverging
  top-level call: the host's invocation (`invoke_stepG`), the importer's `canon lift` up to its
  core activation (`call_atG`), the round's prefix (`roundsPre_fwdB`) and one of the three
  sources (`divB_coreG`, `divA_coreG`, `chatter_coreG`). When the prefix dooms the importer, no
  source applies (`not_divB_doomed`, `doomed_no_ask`, `doomed_no_call`);
* `sessDiv_fwdB`: a `LinkedG.SessSpec` session from a configuration between calls followed by a
  round that never answers is a diverging resumable session (`SessDiv`), each round by
  `linkCall_fwdB`;
* `divSpecToRefG`: from instantiation (`instG_run`, `readyB_init`), `LinkedG.sessDivs ⊆
  LinkedG.refDivs`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDiv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload checkLower sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

section Call

variable {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {ii : Nat} {Ii : SInst}
  {s₀ ui : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {fs : List (CFuncInst (core3P P))}
  {jf : Nat → Nat}

/-- **A specification round that never answers is a diverging call of the reference machine.** -/
theorem linkDiv_fwdB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hFw : d.Fwd) (hB : d.Bounded) (hDv : d.Div) {m : Machine.Config (E3 P) σ}
    {s : lg.exp.St} {u : Store Nat} {k : Nat}
    (R : ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k) {j : Fin lg.imp.exports.length}
    {vs : List IVal} (hd : LinkedG.RoundDiv P lg Ii u s j vs) :
    CallDiverges prof (fun _ _ => false) (DI P impl) m ⟨k⟩ ⟨jf j⟩ (vs.map toRefVal) := by
  obtain ⟨dr, sB, tB, π₁, rfl, rfl, hok, hpath, hexp, hsrc⟩ := hd
  obtain ⟨xs, hck, hf₁, hf₂, hrel⟩ := hok
  have hvs : ValTy.checkList lg.imp.exports[dr.j].ty.params dr.vs = true := by
    unfold checkLower at hck
    split_ifs at hck with h
    exact h
  have hxs : xs = lowerArgs lg.imp.exports[dr.j].ty.params dr.vs := by
    simp only [checkLower, hvs, ↓reduceIte, Option.some.injEq] at hck
    exact hck.symm
  subst hxs
  have SI := ST.imp
  have hx : lg.imp.exports[dr.j] ∈ lg.imp.exports := List.getElem_mem dr.j.isLt
  obtain ⟨hmax, hmaxr, hres⟩ := ST.wire.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := ST.wire.floats.1 _ hx
  have ha : Ii.addrs.getD lg.imp.exports[dr.j].core 0 = Ii.addr dr.f.1 := by
    rw [← hf₁]
    rfl
  have hfj : m.store.funcs[jf dr.j]? = some (.lifted (s₀.funcs.length + Ii.addr dr.f.1)
      (liftedFt lg.imp.exports[dr.j]) {} ⟨ii⟩) := by
    rw [R.funcs, ← ha]
    exact ST.lifted dr.j
  obtain ⟨ιi, hii, hth, hleave⟩ := R.imp
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atG (impl := impl) prof m R.lock k
    (jf dr.j) _ ii lg.imp.exports[dr.j] dr.vs hpf hvs hmax hres hmaxr hrf hii hth hfj
  -- the invariants at the start of the importer's core activation
  have hR₀ : LReadyG d pl Ii s₀ ui F₀ g Oc₀ M₀.ref s u := by
    refine lready_frame hFr R.inv hat.core (by show M₀.store.funcs = _; rw [hat.store]; rfl) ?_
    intro i hi
    show M₀.store.insts[i]? = _
    rw [hat.store]
    exact List.getElem?_set_ne (fun h => ST.out (by rw [h]; exact hi))
  obtain ⟨F, hI₀⟩ := linv_readyG hR₀ ST.own (f := dr.f) hf₂
  have SIu : ImpStatG P lg.imp Ii u F₀ g tr := ⟨SI.good, SI.inst, R.inv.wfI, SI.tramp, SI.inv⟩
  obtain ⟨F₁, -, -, -, -, -, -, hH₀⟩ := R.inv.rel
  have hFG₀ : FrameG d pl ii th M₀.store := by
    refine ⟨by rw [hat.store]; exact R.lock, ?_, ?_, ST.out, ?_⟩
    · rw [hat.store, hat.thread]
      have h₁ : ArenaField.threads.get? (storeG₃ m.store lg.imp.exports[dr.j] ii
          (enterInst ιi ⟨m.store.threads.length⟩) k (dr.vs.map toRefVal))
          ⟨m.store.threads.length⟩ = some ((thread₁ m.store.tasks).withIndex 1) :=
        threads_get_last rfl
      have h₂ : ArenaField.tasks.get? (storeG₃ m.store lg.imp.exports[dr.j] ii
          (enterInst ιi ⟨m.store.threads.length⟩) k (dr.vs.map toRefVal))
          ((thread₁ m.store.tasks).withIndex 1).task =
          some ((taskG₁ lg.imp.exports[dr.j] ii m.store.callers
            ⟨m.store.threads.length⟩).withState .started) :=
        tasks_get_last rfl
      simp only [instOfThread?, h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
    · rw [hat.store]
      exact ⟨enterInst ιi ⟨m.store.threads.length⟩, List.getElem?_set_self (lt_of_getElem? hii),
        hleave⟩
    · intro w hw
      obtain ⟨xe, hxe⟩ := hw
      obtain ⟨-, hblk⟩ := hFr.lifted pl s m.ref F₁ w xe hH₀ hxe
      rw [hat.store]
      show ∃ ι, (List.set m.store.insts ii (enterInst ιi ⟨m.store.threads.length⟩))[d.inst pl w]? =
        some ι ∧ _
      have hne : ii ≠ d.inst pl w := fun h => ST.out (by rw [h]; exact hblk)
      rw [List.getElem?_set_ne hne]
      exact R.exp w ⟨xe, hxe⟩
  -- the instance's play
  have hpath' : Ii.Path P (.running dr.f u (Ii.initThread dr.f)) (callMoves dr.cs)
      (.running dr.f sB tB) := by
    have h : Ii.Path P (.idle u) (.inr (.ask dr.f) :: callMoves dr.cs) (.running dr.f sB tB) :=
      hpath
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      exact h₂
  have hM₀ : M₀ = coreCfg M₀ th K segs rest (M₀.ref.core,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr dr.f.1)
        (lowerArgs lg.imp.exports[dr.j].ty.params dr.vs)) := eq_coreCfg hat.ctl
  have hlive₀ : Live M₀ := ⟨by rw [hat.ctl]; exact List.cons_ne_nil _ _, by
    rw [hat.store]; exact R.lock⟩
  have hq₁ := Quiet.of_lrun hpre hlive₀
  rcases roundsPre_fwdB (prof := prof) (impl := impl) SIu ST.wire hFr hFw hB th K segs rest
      dr.cs dr.dss M₀ s π₁ F _ _ sB tB hI₀ hFG₀ hrel hexp hpath' with
    ⟨trc, C', S'', F', yc, hrun, hnh, -, hIc, hFG'⟩ | hdm
  · rw [← hM₀] at hrun
    refine ⟨_, invoke_stepG R.ctl R.lock R.nest R.pending _ _, steps_diverges
      (Adequacy.steps_append hpre.steps hrun)
      (fun ev hm => (List.mem_append.mp hm).elim (hq₁.1 ev) (hnh ev)) ?_⟩
    let M₁ : Machine.Config (E3 P) σ :=
      { M₀ with conts := C', store := S''.toCStore, core := S''.core }
    show Machine.Diverges prof (fun _ _ => false) (DI P impl) (coreCfg M₁ th K segs rest yc)
    rcases hsrc with h | h | h
    · exact divB_coreG (M := M₁) SIu hIc h th K segs rest
    · exact divA_coreG (M := M₁) SIu ST.wire hFr hDv hIc th hFG' h K segs rest
    · exact chatter_coreG (M := M₁) SIu ST.wire hFr hFw hB hIc th hFG' h K segs rest
  · exfalso
    rcases hsrc with h | ⟨e, s', t', nm, ft, ws, w, h, _⟩ | ⟨q, c, ds, st, hq0, _, hc⟩
    · exact not_divB_doomed hdm h
    · exact doomed_no_ask hdm h
    · have h₀ := (hc 0).1
      rw [hq0] at h₀
      exact doomed_no_call hdm h₀

/-- **Specification sessions ending in a round that never answers are diverging resumable
sessions of the machine between calls.** -/
theorem sessDiv_fwdB (ST : StatB P lg d pl ii Ii s₀ ui F₀ g tr Oc₀ fs jf) (hFr : d.Frame)
    (hFw : d.Fwd) (hRes : d.Resume) (hB : d.Bounded) (hDv : d.Div)
    {calls : List (Fin lg.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {u : Store Nat} {s : lg.exp.St} {u' : Store Nat} {s' : lg.exp.St}
    (hspec : LinkedG.SessSpec P lg Ii u s calls outs u' s') {j : Fin lg.imp.exports.length}
    {vs : List IVal} (hd : LinkedG.RoundDiv P lg Ii u' s' j vs) :
    ∀ (m : Machine.Config (E3 P) σ) (k : Nat), ReadyB d pl ii Ii s₀ ui F₀ g Oc₀ fs m s u k →
      SessDiv prof (linkHost impl) m k (callArgsG lg jf calls) (refOuts outs) ⟨jf j⟩
        (vs.map toRefVal) := by
  induction hspec with
  | nil => intro m k R; exact .div (linkDiv_fwdB ST hFr hFw hB hDv R hd)
  | @round u u₁ u' s s₁ s' cs outs o dr hok hpath hexp hans _ ih =>
    intro m k R
    cases o with
    | some ws =>
      obtain ⟨m', hc, R'⟩ := linkCall_fwdB (prof := prof) (impl := impl) ST hFr hFw hRes hB R dr
        hok hpath hexp hans
      exact .ret hc (ih hd _ _ R')
    | none =>
      obtain ⟨m', hc, R'⟩ := linkCall_fwdB (prof := prof) (impl := impl) ST hFr hFw hRes hB R dr
        hok hpath hexp hans
      exact .trap hc (ih hd _ _ R')

end Call

/-! ## From instantiation -/

variable {lg : LinkedG}

theorem zip_callArgsG' (fb : Nat) (calls : List (Fin lg.imp.exports.length × List IVal)) :
    (calls.map fun q => (⟨fb + q.1⟩ : FuncId)).zip (calls.map fun q => q.2.map toRefVal) =
      callArgsG lg (fun j => fb + j) calls := by
  induction calls with
  | nil => rfl
  | cons q calls ih =>
    simp only [List.map_cons, List.zip_cons_cons, ih]
    rfl

/-- **Specification divergence of a linked component with an abstract exporter is reference
divergence**: for an exporter meeting R1, R2, R4 (`InitSX`), R5, R6 and R7, and an importer as
in `Linked2`, `LinkedG.sessDivs ⊆ LinkedG.refDivs`. -/
theorem divSpecToRefG (P : Profile) (prof : ProfileKind) {d : lg.exp.RefData P}
    (hInit : d.InitSX) (hFr : d.Frame) (hFw : d.Fwd) (hRes : d.Resume) (hB : d.Bounded)
    (hDv : d.Div) (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (j : Fin lg.imp.exports.length) (vs : List IVal) {Ii : SInst} (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.sessDivs P lg Ii calls j vs ⊆ LinkedG.refDivs P prof lg impl h₀ calls j vs := by
  rintro outs ⟨u', s', hspec, hd⟩
  obtain ⟨tr, m₁, pl, F, es, r, hA, hrs, hh, hs, hnh, ho⟩ :=
    instG_run (prof := prof) (impl := impl) hInit hFr hW hIg hIi hIa ⟨hS.data, hS.elems⟩ hNI hI h₀
  have ST := statB_init hW hn hIg hIa hff hI hA hh
  have R := readyB_init hFr hB hW hn hI hS hA rfl rfl rfl hrs hh
  have hSq := sessDiv_fwdB (prof := prof) (impl := impl) ST hFr hFw hRes hB hDv hspec hd _ 0 R
  refine ⟨afterG lg Ii m₁ r, ⟨0⟩, exportMapG lg m₁.store.funcs.length,
    calls.map fun q => (⟨m₁.store.funcs.length + q.1⟩ : FuncId), ⟨m₁.store.funcs.length + j⟩,
    ?_, mapM_lookupG hIg _ calls, exportMapG_lookup hIg _ j, ?_⟩
  · refine ⟨tr, hs, hnh, rfl, R.lock, ?_⟩
    rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
  · rw [zip_callArgsG']
    exact hSq

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGDiv
