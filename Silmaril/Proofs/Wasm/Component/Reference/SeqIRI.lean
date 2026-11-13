module

public import Silmaril.Proofs.Wasm.Component.Reference.ImpIR

/-!
# The IR side for sequences of calls with imports

`seqI_den`: plays of the core instance answering several export calls one after another, each
after its import calls, are, through every layer of the IR denotation over `impSem P`, the
multi-question IR play of the export questions, the component import calls (`ImpRel`) and the
lifted answers. The layers are those of `simpleI_specToIR` (`ImpIR`); the handler relations
`HC`, `HB` of the single round are put together round by round (`HC.of_map`, `HB.of_map`), the
instance's state persisting between questions.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## Rounds with lower calls, one after another -/

section Rounds

variable {E F G : Sig.{0}}

theorem cplay_append : ∀ (l l' : List (CRound E F)), cplay (l ++ l') = cplay l ++ cplay l'
  | [], _ => rfl
  | r :: l, l' => by
    show .inr (.ask r.q) :: (callMoves r.cs ++ (.inr (.ans r.q r.a) :: cplay (l ++ l'))) =
      .inr (.ask r.q) :: (callMoves r.cs ++ (.inr (.ans r.q r.a) :: cplay l)) ++ cplay l'
    rw [cplay_append l l', List.cons_append, List.append_assoc, List.cons_append]

theorem HC.append {h : Handler F G} {up up' : List (CRound E G)} {low low' : List (CRound E F)}
    (H : HC h up low) (H' : HC h up' low') : HC h (up ++ up') (low ++ low') := by
  induction H with
  | nil => exact H'
  | pure hq _ ih => exact .pure hq ih
  | call hq hk _ ih => exact .call hq hk ih

theorem HB.append {h : Handler E F} {up up' : List (CRound F G)} {low low' : List (CRound E G)}
    (H : HB h up low) (H' : HB h up' low') : HB h (up ++ up') (low ++ low') := by
  induction H with
  | nil => exact H'
  | cons Hc _ ih => exact .cons Hc ih

/-- `HC` round by round. -/
theorem HC.of_map {α : Type} {h : Handler F G} (f : α → CRound E G) (f' : α → CRound E F) :
    ∀ L : List α, (∀ d ∈ L, HC h [f d] [f' d]) → HC h (L.map f) (L.map f')
  | [], _ => .nil
  | d :: L, H => (H d List.mem_cons_self).append
      (HC.of_map f f' L fun d' hd' => H d' (List.mem_cons_of_mem _ hd'))

/-- `HB` round by round. -/
theorem HB.of_map {α : Type} {h : Handler E F} (f : α → CRound F G) (f' : α → CRound E G) :
    ∀ L : List α, (∀ d ∈ L, HB h [f d] [f' d]) → HB h (L.map f) (L.map f')
  | [], _ => .nil
  | d :: L, H => (H d List.mem_cons_self).append
      (HB.of_map f f' L fun d' hd' => H d' (List.mem_cons_of_mem _ hd'))

end Rounds

/-! ## One export round of a component with imports -/

variable {P : Profile} {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-- **An export round of the instance and its IR round**: the instance round `r` answers the
core export of export `j` of `c` on the lowered arguments of `vs`, after import calls related to
the component import calls `dss` by `ImpRel`; the IR round `u` asks export `j` on `vs`, makes the
component import calls and answers the lifted answer. -/
def IRRoundI (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (r : CRound I.E I.F)
    (u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length)) : Prop :=
  ∃ (xs : List Flat) (dss : List (List (Round (sigN c.imports.length)))),
    checkLower c.exports[j].ty.params vs = some xs ∧ r.q.1.val = c.exports[j].core ∧
    r.q.2.1 = xs.map ofFlat ∧ List.Forall₂ (ImpRel c I) r.cs dss ∧
    u = ⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), dss.flatten,
      (answerPayload r.a).bind (Adapter.up (.lift c.exports[j].ty))⟩

/-- The data of one export round through the layers. -/
structure LayerI (c : SimpleI) (I : Silmaril.Wasm.Game.ScalarInstance) where
  /-- The instance round. -/
  r : CRound I.E I.F
  /-- The export. -/
  j : Fin c.exports.length
  /-- The IR arguments. -/
  vs : List Silmaril.Wasm.Component.Val
  /-- The lowered arguments. -/
  xs : List Flat
  /-- The core export exists. -/
  hk : c.exports[j].core < c.mod.exports.length
  /-- The core import calls. -/
  cs₂ : List (Round (CoreIface.sig (CoreModule.imports c.mod)))
  /-- The component import calls. -/
  dss : List (List (Round (sigN c.imports.length)))

namespace LayerI

variable (d : LayerI c I)

/-- The lifted answer. -/
def ans : Option Payload := (answerPayload d.r.a).bind (Adapter.up (.lift c.exports[d.j].ty))

/-- The round of `core3Sem`'s export handler. -/
def l₁ : CRound I.E (CoreIface.sig (CoreModule.exports c.mod)) :=
  ⟨(⟨c.exports[d.j].core, d.hk⟩, .flat d.xs), d.r.cs, answerPayload d.r.a⟩

/-- The round of the module's semantics. -/
def l₂ : CRound (CoreIface.sig (CoreModule.imports c.mod)) (CoreIface.sig (CoreModule.exports c.mod)) :=
  ⟨(⟨c.exports[d.j].core, d.hk⟩, .flat d.xs), d.cs₂, answerPayload d.r.a⟩

/-- The round of the module below `widenH`. -/
def l₃ : CRound (CoreIface.sig (CoreModule.imports c.mod)) sigU :=
  ⟨(c.exports[d.j].core, .flat d.xs), d.cs₂, answerPayload d.r.a⟩

/-- The round of the core node. -/
def l₄ : CRound sigU sigU :=
  ⟨(c.exports[d.j].core, .flat d.xs), d.dss.flatten.map Round.forget, answerPayload d.r.a⟩

/-- The round of the environment. -/
def l₅ : CRound sigU sigU :=
  ⟨(c.exports[d.j].core + c.imports.length, .flat d.xs), d.dss.flatten.map Round.forget,
    answerPayload d.r.a⟩

/-- The round of the untyped denotation. -/
def l₆ : CRound sigU sigU :=
  ⟨(d.j.val, .vals d.vs), d.dss.flatten.map Round.forget, d.ans⟩

/-- The round below `narrowH`. -/
def l₇ : CRound (sigN c.imports.length) sigU :=
  ⟨(d.j.val, .vals d.vs), d.dss.flatten, d.ans⟩

/-- The IR round. -/
def u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length) :=
  ⟨(⟨d.j, by simp [SimpleI.toComp]⟩, .vals d.vs), d.dss.flatten, d.ans⟩

end LayerI

/-- The facts of one export round through the layers. -/
structure LayerI.Ok (hI : c.mod.IsInst I) (d : LayerI c I) : Prop where
  lower : checkLower c.exports[d.j].ty.params d.vs = some d.xs
  core : d.r.q.1.val = c.exports[d.j].core
  args : d.r.q.2.1 = d.xs.map ofFlat
  imp : HRounds (importH (instNumI hI)) d.r.cs d.cs₂
  impls : HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
    (CoreModule.imports c.mod).length) d.cs₂ (d.dss.flatten.map Round.forget)

/-- An IR round of the instance has its data through the layers. -/
theorem layer_of (hc : c.Good) (hI : c.mod.IsInst I) {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {r : CRound I.E I.F}
    {u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length)}
    (h : IRRoundI c I j vs r u) : ∃ d : LayerI c I, d.Ok hI ∧ d.r = r ∧ d.u = u := by
  obtain ⟨xs, dss, hl, h₁, h₂, hrel, rfl⟩ := h
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  obtain ⟨cs₂, H₁, H₂⟩ := imp_calls hI hrel
  exact ⟨⟨r, j, vs, xs, hk, cs₂, dss⟩, ⟨hl, h₁, h₂, H₁, H₂⟩, rfl, rfl⟩

/-- Lists of IR rounds of the instance have their data through the layers. -/
theorem layers_of (hc : c.Good) (hI : c.mod.IsInst I) :
    ∀ {lr : List (CRound I.E I.F)}
      {lu : List (CRound (sigN c.imports.length) (sigN c.toComp.exports.length))},
      List.Forall₂ (fun r u => ∃ j vs, IRRoundI c I j vs r u) lr lu →
      ∃ L : List (LayerI c I), (∀ d ∈ L, d.Ok hI) ∧ L.map LayerI.r = lr ∧ L.map LayerI.u = lu
  | [], [], .nil => ⟨[], (fun _ h => nomatch h), rfl, rfl⟩
  | _ :: _, _ :: _, .cons ⟨_, _, h⟩ hs => by
    obtain ⟨d, hd, rfl, rfl⟩ := layer_of hc hI h
    obtain ⟨L, hL, rfl, rfl⟩ := layers_of hc hI hs
    refine ⟨d :: L, fun d' hd' => ?_, rfl, rfl⟩
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact hd
    · exact hL d' hd'

/-! ## The layers, round by round -/

/-- **The core layer**: rounds of the instance are rounds of the module's semantics. -/
theorem layers_sem (hI : c.mod.IsInst I) {L : List (LayerI c I)} (hL : ∀ d ∈ L, d.Ok hI)
    (h : cplay (L.map LayerI.r) ∈ I.strategy P I.store) :
    cplay (L.map LayerI.l₂) ∈ (impSem P).sem c.mod := by
  have hx : cplay (L.map LayerI.l₁) ∈
      (I.strategy P I.store).comp (Strategy.ofHandler (exportH (instNumI hI))) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d hd =>
      .call (exportH_op hI d.hk d.r.q (hL d hd).core (hL d hd).args) rfl .nil) h
  rw [impSem_sem hI]
  exact cplay_ofHandler_comp (HB.of_map _ _ L fun d hd => .cons (hL d hd).imp .nil) hx

/-- **The environment**: the core node, the pairing, `splitH` and the import mask. -/
theorem layers_env (hI : c.mod.IsInst I) {L : List (LayerI c I)} (hL : ∀ d ∈ L, d.Ok hI)
    (h : cplay (L.map LayerI.l₂) ∈ (impSem P).sem c.mod) :
    cplay (L.map LayerI.l₅) ∈ envSI (impSem P) c := by
  have hN₁ : cplay (L.map LayerI.l₃) ∈ ((impSem P).sem c.mod).comp
      (Strategy.ofHandler (widenH (CoreModule.exports c.mod).length)) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := widenH _) (dite_eq_left d.hk) rfl .nil) h
  have hN : cplay (L.map LayerI.l₄) ∈
      coreNode (impSem P) c.imports.length c.mod (SimpleI.lowerArgs c.imports) :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d hd => .cons (hL d hd).impls .nil) hN₁
  have hP : cplay ((L.map LayerI.l₄).map (CRound.inr (F₁ := sigU))) ∈ (Strategy.id sigU).pair
      (coreNode (impSem P) c.imports.length c.mod (SimpleI.lowerArgs c.imports)) :=
    cplay_pair_inr hN
  rw [List.map_map] at hP
  have hS : cplay (L.map LayerI.l₅) ∈ ((Strategy.id sigU).pair (coreNode (impSem P)
      c.imports.length c.mod (SimpleI.lowerArgs c.imports))).comp
        (Strategy.ofHandler (splitH c.imports.length)) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := splitH _) (splitH_shift _ _ _) rfl .nil) hP
  exact cplay_ofHandler_comp (HB.of_map _ _ L fun d _ => .cons (hrounds_maskH _ _) .nil) hS

/-- **The export layer and `atSizes`.** -/
theorem layers_den (hI : c.mod.IsInst I) {L : List (LayerI c I)} (hL : ∀ d ∈ L, d.Ok hI)
    (h : cplay (L.map LayerI.l₅) ∈ envSI (impSem P) c) :
    cplay (L.map LayerI.u) ∈ c.toComp.den (impSem P) := by
  have hU : cplay (L.map LayerI.l₆) ∈ c.toComp.denU (impSem P) := by
    rw [denU_toCompI]
    refine cplay_comp_ofHandler (HC.of_map _ _ L fun d hd => ?_) h
    have hl' : checkLower c.exports[d.j.val].ty.params d.vs = some d.xs := (hL d hd).lower
    refine .call (h := exportsH _ _) (q' := (c.exports[d.j].core + c.imports.length, .flat d.xs))
      (k := fun n => .pure (n.bind (Adapter.up (.lift c.exports[d.j].ty)))) ?_ rfl .nil
    rw [exportsH_toCompI c d.j.isLt d.vs d.hk, hl']
    rfl
  have hW : cplay (L.map LayerI.l₇) ∈
      (Strategy.ofHandler (widenH c.imports.length)).comp (c.toComp.denU (impSem P)) :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d _ => .cons (hrounds_widenH _ _) .nil) hU
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (HC.of_map _ _ L fun d _ => .call (h := narrowH _) rfl rfl .nil) hW

/-- **The IR side for sequences of calls with imports**: rounds of the core instance played one
after another from its store are, as IR rounds, a play of the IR denotation over `impSem P`. -/
theorem seqI_den (hc : c.Good) (hI : c.mod.IsInst I) {lr : List (CRound I.E I.F)}
    {lu : List (CRound (sigN c.imports.length) (sigN c.toComp.exports.length))}
    (hrel : List.Forall₂ (fun r u => ∃ j vs, IRRoundI c I j vs r u) lr lu)
    (h : cplay lr ∈ I.strategy P I.store) : cplay lu ∈ c.toComp.den (impSem P) := by
  obtain ⟨L, hL, rfl, rfl⟩ := layers_of hc hI hrel
  exact layers_den hI hL (layers_env hI hL (layers_sem hI hL h))

end Silmaril.Proofs.Wasm.Component.Reference
