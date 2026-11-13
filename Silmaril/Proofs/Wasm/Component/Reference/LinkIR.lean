module

public import Silmaril.Wasm.Component.Reference.Link.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.SeqIRI

/-!
# The IR side of two linked components

`linked2_specToIR : Linked2.SpecToIR`: a play of the importer's core instance answering an export
call after import calls, whose component import calls are answered by the exporter's
specification with its Core store threaded (`ExpRun`), is a two-move play of the linked IR
`l.toComp.den (impSem P)`. The layers, from the bottom:

* the exporter: its returned calls are complete activations of its instance from store to store
  (`retAt_rounds`), a last trap a play at the store reached (`last_rounds`); through `modSem`,
  the core node and the export handler they are rounds of `exp.toComp.denU (modSem P)`, which is
  the denotation of the nested exporter `(SimpleI.ofSimple exp).toComp` over `impSem P`
  (`denU_ofSimple`); then the exporter's node and the first environment (`expEnv_rounds`);
* the importer: `denU_of_sem` (`ImpIR`) at the untyped interface, its import calls renamed to
  the wired exporter exports by its node's wiring (`expRun_rounds`: `implsH` of the forwarding
  `Impl`s);
* the composition of the second environment over the first, whose rounds serve the importer's
  lower calls (`cplay_comp_serve`: a strategy below answering each lower call without calls of
  its own);
* the linked export handler and `atSizes` (`den_of_denU`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## A strategy below serving the lower calls -/

section Serve

variable {E F G : Sig.{0}}

/-- The lower calls `cs` of the strategy on top, answered by complete rounds of the strategy
below, are hidden. -/
theorem zip_twos_calls {s : List (Move E F)} {t : List (Move F G)} {p : List (Move E G)}
    (h : Zip s t p) : ∀ cs : List (Round F),
      Zip (twos (E := E) cs ++ s) (callMoves (F := G) cs ++ t) p
  | [] => h
  | ⟨_, _⟩ :: cs => .sync _ (.sync _ (zip_twos_calls h cs))

/-- A round with its lower calls hidden. -/
def CRound.hide (r : CRound F G) : CRound E G := ⟨r.q, [], r.a⟩

theorem zip_serve : ∀ l : List (CRound F G),
    Zip (twos (E := E) (l.flatMap (·.cs))) (cplay l) (cplay (l.map CRound.hide))
  | [] => .nil
  | r :: l => by
    rw [List.flatMap_cons, twos_append]
    exact .right _ (zip_twos_calls (.right _ (zip_serve l)) r.cs)

/-- **A strategy below serving the lower calls**: when `σ` answers the lower calls of the
rounds `l` of `τ`, in order, each without calls of its own, `σ.comp τ` plays the rounds with
the lower calls hidden. -/
theorem cplay_comp_serve {σ : Strategy E F} {τ : Strategy F G} {l : List (CRound F G)}
    (hσ : twos (l.flatMap (·.cs)) ∈ σ) (hτ : cplay l ∈ τ) :
    cplay (l.map CRound.hide) ∈ σ.comp τ :=
  ⟨_, hσ, _, hτ, zip_serve l⟩

end Serve

/-! ## The linked denotation -/

/-- The nested exporter over `impSem` is the exporter over `modSem`. -/
theorem denU_ofSimple (P : Profile) (c : Simple) :
    (SimpleI.ofSimple c).toComp.denU (impSem P) = c.toComp.denU (modSem P) := by
  rw [denU_toCompI, denU_toComp]
  simp only [SimpleI.ofSimple, SimpleI.toComp, Simple.toComp, List.length_nil, Nat.zero_add,
    Nat.add_zero, SimpleI.lowerArgs, List.mapIdx_nil]
  rfl

theorem exports_length_ofSimple (c : Simple) :
    (SimpleI.ofSimple c).toComp.exports.length = c.exports.length := by
  simp [SimpleI.ofSimple, SimpleI.toComp]

theorem SimpleI.exports_length_toComp (c : SimpleI) :
    c.toComp.exports.length = c.exports.length := by
  simp [SimpleI.toComp]

/-- The node of the exporter. -/
abbrev expNode (C : CoreSem ImpModule) (l : Linked2) : Strategy sigU sigU :=
  (Strategy.ofHandler (implsH 0 [])).comp ((SimpleI.ofSimple l.exp).toComp.denU C)

/-- The wiring of the importer's imports to the exporter's exports. -/
abbrev wireArgs (l : Linked2) : List Impl := l.wire.map fun w => ⟨[], .call w⟩

/-- The node of the importer. -/
abbrev impNode (C : CoreSem ImpModule) (l : Linked2) : Strategy sigU sigU :=
  (Strategy.ofHandler (implsH l.exp.exports.length (wireArgs l))).comp (l.imp.toComp.denU C)

/-- The environment of the linked component's exports: the exporter, then the importer. -/
abbrev envL (C : CoreSem ImpModule) (l : Linked2) : Strategy sigU sigU :=
  ext l.exp.exports.length (ext 0 (Strategy.ofHandler (maskH 0)) (expNode C l)) (impNode C l)

theorem denU_toCompL (C : CoreSem ImpModule) (l : Linked2) :
    l.toComp.denU C = (envL C l).comp (Strategy.ofHandler
      (exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports)) := by
  simp only [Linked2.toComp, Comp.denU, denNodes, Node.den, envAfter, Node.width,
    Comp.exports_mk, List.length_nil, Nat.zero_add, SimpleI.exports_length_toComp]
  rfl

/-! ## The exporter -/

/-- The importer's node forwards a call of import `k` to the wired export `w`. -/
theorem implsH_wire {l : Linked2} {k : Nat} {w : Fin l.exp.exports.length}
    (hw : l.wire[k]? = some w.val) (p : Payload) :
    implsH l.exp.exports.length (wireArgs l) (k, p) = .call (w.val, p) fun n => .pure n := by
  have hget : (wireArgs l)[k]? = some ⟨[], .call w.val⟩ := by
    simp [wireArgs, hw]
  simp only [implsH, hget, Impl.prog, runChain, Target.prog, ite_eq_left w.isLt]

/-- An import call of the importer, renamed to the wired export of the exporter. -/
def wireRound (l : Linked2) (d : Round (sigN l.imp.imports.length)) : Round sigU :=
  ⟨(l.wire.getD d.1.1.val 0, d.1.2), d.2⟩

theorem wire_getD {l : Linked2} {k : Nat} {w : Nat} (hw : l.wire[k]? = some w) :
    l.wire.getD k 0 = w := by
  simp [List.getD_eq_getElem?_getD, hw]

/-- Every import call of an `ExpRun` is wired to an export of the exporter. -/
theorem expRun_wire {P : Profile} {l : Linked2} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s : Store Nat} {ds : List (Round (sigN l.imp.imports.length))}, Linked2.ExpRun P l I s ds →
      ∀ d ∈ ds, ∃ w : Fin l.exp.exports.length, l.wire[d.1.1.val]? = some w.val
  | _, _, .nil _, _, hd => nomatch hd
  | _, _, .ret w hw _ hrun, d, hd => by
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨w, hw⟩
    · exact expRun_wire hrun d hd
  | _, _, .trap w hw _, d, hd => by
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨w, hw⟩
    · exact nomatch hd

/-- The importer's node forwards wired import calls to the exporter. -/
theorem hrounds_wire {l : Linked2} :
    ∀ {ds : List (Round (sigN l.imp.imports.length))},
      (∀ d ∈ ds, ∃ w : Fin l.exp.exports.length, l.wire[d.1.1.val]? = some w.val) →
      HRounds (implsH l.exp.exports.length (wireArgs l)) (ds.map Round.forget)
        (ds.map (wireRound l))
  | [], _ => .nil
  | ⟨(k, p), R⟩ :: ds, H => by
    obtain ⟨w, hw⟩ := H _ List.mem_cons_self
    have e : wireRound l ⟨(k, p), R⟩ = ⟨(w.val, p), R⟩ := by
      simp only [wireRound, wire_getD hw]
    rw [List.map_cons, List.map_cons, e]
    exact .call (h := implsH _ _) (q := (k.val, p)) (q' := (w.val, p)) (k := fun n => .pure n)
      (implsH_wire hw _) rfl (hrounds_wire fun d hd => H d (List.mem_cons_of_mem _ hd))

/-- **The exporter's answers**: import calls answered by the exporter's specification from a
well-formed store, renamed to the wired exports, are rounds of the exporter's IR export handler,
played by its instance from that store. -/
theorem expRun_rounds {P : Profile} {l : Linked2} (hc : l.exp.Good)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : l.exp.mod.IsInst I) :
    ∀ {s : Store Nat} {ds : List (Round (sigN l.imp.imports.length))}, Linked2.ExpRun P l I s ds →
      I.WellFormed s →
      ∃ (li : List (Round I.F)) (lc : List (Round (CoreIface.sig (CoreModule.exports l.exp.mod)))),
        twos li ∈ I.strategy P s ∧ HRounds (exportH (instNum hI)) lc li ∧
        HRounds (exportsH l.exp.mod.exports.length l.exp.toComp.exports) (ds.map (wireRound l))
          (lc.map Round.forget)
  | _, _, .nil s, _ => ⟨[], [], (I.strategy P s).nil_mem, .nil, .nil⟩
  | _, _, .ret (k := k) (ws := ws) (us := us) w hw hret hrun, hwf => by
    have hwf' : I.WellFormed _ := hret.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) hwf
    obtain ⟨li₁, lc₁, hact, H₁, X₁⟩ := retAt_rounds hc hI hwf hret
    obtain ⟨li, lc, hli, H, X⟩ := expRun_rounds hc hI hrun hwf'
    have e : wireRound l ⟨(k, .vals ws), some (.vals us)⟩ = ⟨(w.val, .vals ws), some (.vals us)⟩ := by
      simp only [wireRound, wire_getD hw]
    refine ⟨li₁ ++ li, lc₁ ++ lc, ?_, H₁.append H, ?_⟩
    · rw [twos_append]
      exact Silmaril.Wasm.Game.ScalarInstance.append_mem_of hact hli
    · rw [List.map_cons, e, List.map_append]
      exact X₁.append X
  | _, _, .trap (k := k) (ws := ws) w hw htrap, hwf => by
    obtain hd | ⟨A, li, lc, hA, hli, H, X⟩ := last_rounds hc hI hwf htrap
    · cases hd
    · have hA' : A = none := hA
      subst hA'
      have e : wireRound l ⟨(k, .vals ws), none⟩ = ⟨(w.val, .vals ws), none⟩ := by
        simp only [wireRound, wire_getD hw]
      refine ⟨li, lc, hli, H, ?_⟩
      rw [List.map_cons, List.map_nil, e]
      exact X

/-- The exporter's rounds in the first environment of the linked component. -/
theorem expEnv_rounds {P : Profile} {l : Linked2} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : l.exp.mod.IsInst I) {low : List (Round sigU)} {li : List (Round I.F)}
    {lc : List (Round (CoreIface.sig (CoreModule.exports l.exp.mod)))}
    (hli : twos li ∈ I.strategy P I.store) (H : HRounds (exportH (instNum hI)) lc li)
    (X : HRounds (exportsH l.exp.mod.exports.length l.exp.toComp.exports) low
      (lc.map Round.forget)) :
    twos low ∈ ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l) := by
  have hsem : twos lc ∈ (modSem P).sem l.exp.mod := sem_rounds hI H hli
  have hden : twos low ∈ l.exp.toComp.denU (modSem P) := by
    rw [denU_toComp]
    exact twos_comp_ofHandler X (envS_rounds (modSem P) l.exp hsem)
  have hN : twos low ∈ expNode (impSem P) l := by
    refine twos_comp_upper ?_
    rw [denU_ofSimple]
    exact hden
  have hP : twos (low.map (Round.inr (F₁ := sigU))) ∈ (Strategy.id sigU).pair (expNode (impSem P) l) :=
    twos_pair_inr hN
  unfold ext
  exact twos_comp_upper (twos_comp_ofHandler (hrounds_splitH _) hP)

/-! ## The linked call -/

theorem splitH_shift' (n i : Nat) (p : Payload) :
    splitH n (n + i, p) = .call (.inr (i, p)) fun r => .pure r := by
  rw [Nat.add_comm]
  exact splitH_shift n i p

/-- The linked export handler forwards export `j` to the importer's export `j`. -/
theorem exportsH_toCompL (l : Linked2) {j : Nat} (hj : j < l.imp.exports.length) (p : Payload) :
    exportsH (l.exp.exports.length + l.imp.exports.length) l.toComp.exports (j, p) =
      .call (l.exp.exports.length + j, p) fun n => .pure n := by
  have hget : (l.toComp.exports.map Export.impl)[j]? =
      some ⟨[], .call (l.exp.exports.length + j)⟩ := by
    simp [Linked2.toComp, hj]
  simp only [exportsH, implsH, hget, Impl.prog, runChain, Target.prog,
    ite_eq_left (Nat.add_lt_add_left hj _)]

/-- **A linked call**: a round of the importer whose import calls are answered by the exporter's
specification from its initial store is a two-move play of the linked component. -/
theorem link_of_imp {P : Profile} {l : Linked2} (hc : l.exp.Good)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : l.exp.mod.IsInst I) {j : Fin l.imp.exports.length}
    {p : Payload} {ds : List (Round (sigN l.imp.imports.length))} {A : Option Payload}
    (himp : cplay [⟨(j.val, p), ds.map Round.forget, A⟩] ∈ l.imp.toComp.denU (impSem P))
    (hrun : Linked2.ExpRun P l I I.store ds) :
    two (E := sigU) (F := sigU) (j.val, p) A ∈ l.toComp.denU (impSem P) := by
  obtain ⟨li, lc, hli, H, X⟩ := expRun_rounds hc hI hrun hI.1.choose_spec.ok
  have hexp := expEnv_rounds hI hli H X
  have hN : cplay [⟨(j.val, p), ds.map (wireRound l), A⟩] ∈ impNode (impSem P) l :=
    cplay_ofHandler_comp (.cons (hrounds_wire (expRun_wire hrun)) .nil) himp
  have hP := cplay_pair_inr (σ₁ := Strategy.id sigU) hN
  have hS : cplay [⟨(l.exp.exports.length + j.val, p), ds.map (wireRound l), A⟩] ∈
      ((Strategy.id sigU).pair (impNode (impSem P) l)).comp
        (Strategy.ofHandler (splitH l.exp.exports.length)) :=
    cplay_comp_ofHandler (.call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) hP
  have hE : cplay [(⟨(l.exp.exports.length + j.val, p), [], A⟩ : CRound sigU sigU)] ∈
      envL (impSem P) l := by
    refine cplay_comp_serve (E := sigU) (F := sigU) (G := sigU)
      (l := [⟨(l.exp.exports.length + j.val, p), ds.map (wireRound l), A⟩]) ?_ hS
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hexp
  rw [denU_toCompL]
  show cplay [(⟨(j.val, p), [], A⟩ : CRound sigU sigU)] ∈ _
  exact cplay_comp_ofHandler (.call (h := exportsH _ _) (q := (j.val, p))
    (q' := (l.exp.exports.length + j.val, p))
    (k := fun n => .pure n)
    (exportsH_toCompL l j.isLt p) rfl .nil) hE

/-- **The IR side of two linked components** (proved). -/
theorem linked2_specToIR : Linked2.SpecToIR := by
  intro P l he hi Ie hIe Ii hIi j vs
  obtain ⟨nm, hcore⟩ := hi.core _ (List.getElem_mem j.isLt)
  have hk : l.imp.exports[j].core < l.imp.mod.exports.length :=
    (List.getElem?_eq_some_iff.mp hcore).1
  have hj : j.val < l.toComp.exports.length := by simp [Linked2.exports_length_toComp]
  refine ⟨fun hl => den_of_denU (impSem P) l.toComp hj (.vals vs) none
    (link_of_imp he hIe (ds := []) (denU_trapI hk hl) (.nil _)), ?_⟩
  intro xs hl f h₁ h₂ cs w q hpath dss hrel hrun
  obtain ⟨cs₂, H₁, H₂⟩ := imp_calls hIi hrel
  have hinst : cplay [⟨f, cs, w⟩] ∈ Ii.strategy P Ii.store := cplay_mem_strategy hpath
  have hx : cplay [⟨(⟨l.imp.exports[j].core, hk⟩, .flat xs), cs, answerPayload w⟩] ∈
      (Ii.strategy P Ii.store).comp (Strategy.ofHandler (exportH (instNumI hIi))) :=
    cplay_comp_ofHandler (.call (exportH_op hIi hk f h₁ h₂) rfl .nil) hinst
  have hsem : cplay [⟨(⟨l.imp.exports[j].core, hk⟩, .flat xs), cs₂, answerPayload w⟩] ∈
      (impSem P).sem l.imp.mod := by
    rw [impSem_sem hIi]
    exact cplay_ofHandler_comp (.cons H₁ .nil) hx
  exact den_of_denU (impSem P) l.toComp hj (.vals vs) _
    (link_of_imp he hIe (denU_of_sem hk hl H₂ hsem) hrun)

/-! ## Sequences of linked calls -/

section Seq

variable {P : Profile} {l : Linked2} {Ii : Silmaril.Wasm.Game.ScalarInstance}

/-- **The importer's export layer at the untyped interface**, round by round. -/
theorem layers_denU (hI : l.imp.mod.IsInst Ii) {L : List (LayerI l.imp Ii)}
    (hL : ∀ d ∈ L, d.Ok hI) (h : cplay (L.map LayerI.l₅) ∈ envSI (impSem P) l.imp) :
    cplay (L.map LayerI.l₆) ∈ l.imp.toComp.denU (impSem P) := by
  rw [denU_toCompI]
  refine cplay_comp_ofHandler (HC.of_map _ _ L fun d hd => ?_) h
  have hl' : checkLower l.imp.exports[d.j.val].ty.params d.vs = some d.xs := (hL d hd).lower
  refine .call (h := exportsH _ _) (q' := (l.imp.exports[d.j].core + l.imp.imports.length, .flat d.xs))
    (k := fun n => .pure (n.bind (Adapter.up (.lift l.imp.exports[d.j].ty)))) ?_ rfl .nil
  rw [exportsH_toCompI l.imp d.j.isLt d.vs d.hk, hl']
  rfl

/-- The importer round with its import calls renamed to the wired exports. -/
def LayerI.wired (d : LayerI l.imp Ii) : CRound sigU sigU :=
  ⟨(l.exp.exports.length + d.j.val, .vals d.vs), d.dss.flatten.map (wireRound l), d.ans⟩

theorem flatMap_wired (L : List (LayerI l.imp Ii)) :
    (L.map LayerI.wired).flatMap (·.cs) =
      (L.flatMap fun d => d.dss.flatten).map (wireRound l) := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih, List.map_append]
    rfl

/-- **Linked calls, one after another**: rounds of the importer whose import calls, all
together, are answered by the exporter's specification from its instance's store are rounds of
the linked component without lower calls. -/
theorem link_layers (hc : l.exp.Good) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) {L : List (LayerI l.imp Ii)}
    (himp : cplay (L.map LayerI.l₆) ∈ l.imp.toComp.denU (impSem P))
    (hrun : Linked2.ExpRun P l Ie Ie.store (L.flatMap fun d => d.dss.flatten)) :
    cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), [], d.ans⟩ : CRound sigU sigU)) ∈
      l.toComp.denU (impSem P) := by
  obtain ⟨li, lc, hli, H, X⟩ := expRun_rounds hc hIe hrun hIe.1.choose_spec.ok
  have hexp : twos ((L.flatMap fun d => d.dss.flatten).map (wireRound l)) ∈
      ext 0 (Strategy.ofHandler (maskH 0)) (expNode (impSem P) l) := expEnv_rounds hIe hli H X
  have hwire : ∀ x ∈ L.flatMap (fun d => d.dss.flatten),
      ∃ w : Fin l.exp.exports.length, l.wire[x.1.1.val]? = some w.val := expRun_wire hrun
  have hN : cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), d.dss.flatten.map (wireRound l),
      d.ans⟩ : CRound sigU sigU)) ∈ impNode (impSem P) l :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d hd => .cons (hrounds_wire fun x hx =>
      hwire x (List.mem_flatMap.mpr ⟨d, hd, hx⟩)) .nil) himp
  have hP : cplay (L.map fun d => (⟨.inr (d.j.val, .vals d.vs), d.dss.flatten.map (wireRound l),
      d.ans⟩ : CRound sigU (sigU ⊕ₛ sigU))) ∈ (Strategy.id sigU).pair (impNode (impSem P) l) :=
    by have h := cplay_pair_inr (σ₁ := Strategy.id sigU) hN; rwa [List.map_map] at h
  have hS : cplay (L.map LayerI.wired) ∈ ((Strategy.id sigU).pair (impNode (impSem P) l)).comp
      (Strategy.ofHandler (splitH l.exp.exports.length)) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := splitH _) (splitH_shift' _ _ _) rfl .nil) hP
  have hE : cplay ((L.map LayerI.wired).map (CRound.hide (E := sigU))) ∈ envL (impSem P) l := by
    refine cplay_comp_serve ?_ hS
    rw [flatMap_wired]
    exact hexp
  have hE' : cplay (L.map fun d => (⟨(l.exp.exports.length + d.j.val, .vals d.vs), [], d.ans⟩ :
      CRound sigU sigU)) ∈ envL (impSem P) l := by rwa [List.map_map] at hE
  rw [denU_toCompL]
  exact cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
    .call (h := exportsH _ _) (q := (d.j.val, .vals d.vs))
      (q' := (l.exp.exports.length + d.j.val, .vals d.vs)) (k := fun n => .pure n)
      (exportsH_toCompL l d.j.isLt _) rfl .nil) hE'

end Seq

/-- The linked IR round of an IR round of the importer: the export question and answer, the
import calls hidden inside the linked component. -/
def Linked2.linkRound (l : Linked2)
    (u : CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length)) :
    CRound (l.toComp.imports.sig) (sigN l.toComp.exports.length) :=
  ⟨(⟨u.q.1.val, by simpa [Linked2.exports_length_toComp, SimpleI.exports_length_toComp]
      using u.q.1.isLt⟩, u.q.2), [], u.a⟩

/-- **The IR side for sequences of linked calls**: rounds of the importer's core instance played
one after another from its store, related to IR rounds `lu` of the importer by `IRRoundI`, whose
component import calls, all together and in order, are answered by the exporter's specification
from the exporter instance's store (`ExpRun`, the exporter's Core store threaded across calls),
are a play of the linked IR, the import calls hidden. -/
theorem linked_seq_den {P : Profile} {l : Linked2} (he : l.exp.Good) (hi : l.imp.Good)
    {Ie : Silmaril.Wasm.Game.ScalarInstance} (hIe : l.exp.mod.IsInst Ie)
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hIi : l.imp.mod.IsInst Ii)
    {lr : List (CRound Ii.E Ii.F)}
    {lu : List (CRound (sigN l.imp.imports.length) (sigN l.imp.toComp.exports.length))}
    (hrel : List.Forall₂ (fun r u => ∃ j vs, IRRoundI l.imp Ii j vs r u) lr lu)
    (h : cplay lr ∈ Ii.strategy P Ii.store)
    (hrun : Linked2.ExpRun P l Ie Ie.store (lu.flatMap (·.cs))) :
    cplay (lu.map (Linked2.linkRound l)) ∈ l.toComp.den (impSem P) := by
  obtain ⟨L, hL, rfl, rfl⟩ := layers_of hi hIi hrel
  have himp := layers_denU hIi hL (layers_env hIi hL (layers_sem hIi hL h))
  rw [List.flatMap_map] at hrun
  have hU := link_layers he hIe himp hrun
  have hW : cplay (L.map fun d => (⟨(d.j.val, .vals d.vs), [], d.ans⟩ :
      CRound (l.toComp.imports.sig) sigU)) ∈
      (Strategy.ofHandler (widenH l.toComp.imports.length)).comp (l.toComp.denU (impSem P)) :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun _ _ => .cons .nil .nil) hU
  rw [List.map_map]
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (HC.of_map _ _ L fun _ _ => .call (h := narrowH _) rfl rfl .nil) hW

end Silmaril.Proofs.Wasm.Component.Reference
