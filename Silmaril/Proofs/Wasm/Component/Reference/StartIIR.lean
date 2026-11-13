module

public import Silmaril.Proofs.Wasm.Component.Reference.StartISeq
public import Silmaril.Proofs.Wasm.Component.Reference.StartIBase

/-!
# The IR side with imports and a start function

* `denU_of_semG`, `den_of_semG`, `denU_trapIG`, `den_trapIG`, `layers_envG`, `layers_denG`: the
  layers of `ImpIR`/`SeqIRI` above the module's semantics, for any core semantics (the proofs
  are those of `ImpIR`/`SeqIRI`, which state them for `impSem P`);
* `LayerI.OkS`, `layers_ofS`: the layer data of IR rounds of an instance of the module without
  its start function;
* `layers_semS`: rounds of the instance played from a store the start phase returns at are
  rounds of `impSemS P`; `trap_memI`: when the start phase may fail, `impSemS P` traps on every
  question;
* `seqI_denS`: rounds of the instance from such a store are a play of `c.toComp.den (impSemS P)`;
  `trap_denIS`: when the start phase may fail, the IR traps on every export call.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## The layers above the core semantics, for any core semantics -/

/-- The layers above the core instance, for one export round, at the untyped interface. -/
theorem denU_of_semG (S : CoreSem ImpModule) {c : SimpleI} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = some xs)
    {cs₂ : List (Round (CoreIface.sig (CoreModule.imports c.mod)))}
    {dss : List (List (Round (sigN c.imports.length)))}
    (H₂ : HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) cs₂ (dss.flatten.map Round.forget))
    {R : Option Payload}
    (h : cplay [⟨(⟨c.exports[j].core, hcore⟩, .flat xs), cs₂, R⟩] ∈ S.sem c.mod) :
    cplay [⟨(j.val, .vals vs), dss.flatten.map Round.forget,
      R.bind (Adapter.up (.lift c.exports[j].ty))⟩] ∈ c.toComp.denU S := by
  have hN₁ : cplay [⟨(c.exports[j].core, .flat xs), cs₂, R⟩] ∈
      (S.sem c.mod).comp (Strategy.ofHandler (widenH (CoreModule.exports c.mod).length)) :=
    cplay_comp_ofHandler (.call (h := widenH _) (dite_eq_left hcore) rfl .nil) h
  have hN : cplay [⟨(c.exports[j].core, .flat xs), dss.flatten.map Round.forget, R⟩] ∈
      coreNode S c.imports.length c.mod (SimpleI.lowerArgs c.imports) :=
    cplay_ofHandler_comp (.cons H₂ .nil) hN₁
  have hP := cplay_pair_inr (σ₁ := Strategy.id sigU) hN
  have hS : cplay [⟨(c.exports[j].core + c.imports.length, .flat xs),
      dss.flatten.map Round.forget, R⟩] ∈ ((Strategy.id sigU).pair (coreNode S
        c.imports.length c.mod (SimpleI.lowerArgs c.imports))).comp
          (Strategy.ofHandler (splitH c.imports.length)) :=
    cplay_comp_ofHandler (.call (h := splitH _) (splitH_shift _ _ _) rfl .nil) hP
  have hE : cplay [⟨(c.exports[j].core + c.imports.length, .flat xs),
      dss.flatten.map Round.forget, R⟩] ∈ envSI S c :=
    cplay_ofHandler_comp (.cons (hrounds_maskH _ _) .nil) hS
  have hl' : checkLower c.exports[j.val].ty.params vs = some xs := hl
  rw [denU_toCompI]
  refine cplay_comp_ofHandler (.call (h := exportsH _ _)
    (q' := (c.exports[j].core + c.imports.length, .flat xs))
    (k := fun n => .pure (n.bind (Adapter.up (.lift c.exports[j].ty)))) ?_ rfl .nil) hE
  rw [exportsH_toCompI c j.isLt vs hcore, hl']
  rfl

/-- The layers above the core instance, for one export round. -/
theorem den_of_semG (S : CoreSem ImpModule) {c : SimpleI} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = some xs)
    {cs₂ : List (Round (CoreIface.sig (CoreModule.imports c.mod)))}
    {dss : List (List (Round (sigN c.imports.length)))}
    (H₂ : HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) cs₂ (dss.flatten.map Round.forget))
    {R : Option Payload}
    (h : cplay [⟨(⟨c.exports[j].core, hcore⟩, .flat xs), cs₂, R⟩] ∈ S.sem c.mod) :
    cplay [⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), dss.flatten,
      R.bind (Adapter.up (.lift c.exports[j].ty))⟩] ∈ c.toComp.den S := by
  have hU := denU_of_semG S hcore hl H₂ h
  have hW : cplay [⟨(j.val, .vals vs), dss.flatten, R.bind (Adapter.up (.lift c.exports[j].ty))⟩] ∈
      (Strategy.ofHandler (widenH c.imports.length)).comp (c.toComp.denU S) :=
    cplay_ofHandler_comp (.cons (hrounds_widenH _ _) .nil) hU
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (.call (h := narrowH _) rfl rfl .nil) hW

/-- A trap of the argument check, at the untyped interface. -/
theorem denU_trapIG (S : CoreSem ImpModule) {c : SimpleI} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = none) :
    cplay [(⟨(j.val, .vals vs), [], none⟩ : CRound sigU sigU)] ∈ c.toComp.denU S := by
  have hl' : checkLower c.exports[j.val].ty.params vs = none := hl
  rw [denU_toCompI]
  refine cplay_comp_ofHandler (.pure (h := exportsH _ _) ?_ .nil) (Strategy.nil_mem _)
  rw [exportsH_toCompI c j.isLt vs hcore, hl']

/-- A trap of the argument check. -/
theorem den_trapIG (S : CoreSem ImpModule) {c : SimpleI} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = none) :
    cplay [⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), [], none⟩] ∈ c.toComp.den S := by
  have hU := denU_trapIG S hcore hl
  have hW : cplay [(⟨(j.val, .vals vs), [], none⟩ : CRound (sigN c.imports.length) sigU)] ∈
      (Strategy.ofHandler (widenH c.imports.length)).comp (c.toComp.denU S) :=
    cplay_ofHandler_comp (.cons .nil .nil) hU
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (.call (h := narrowH _) rfl rfl .nil) hW


/-! ## Layers of rounds of an instance before its start function -/

variable {P : Profile} {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance}

/-- The facts of one export round through the layers. -/
structure LayerI.OkS (hI : c.mod.noStart.IsInst I) (d : LayerI c I) : Prop where
  lower : checkLower c.exports[d.j].ty.params d.vs = some d.xs
  core : d.r.q.1.val = c.exports[d.j].core
  args : d.r.q.2.1 = d.xs.map ofFlat
  imp : HRounds (importH (instNumI hI)) d.r.cs d.cs₂
  impls : HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
    (CoreModule.imports c.mod).length) d.cs₂ (d.dss.flatten.map Round.forget)

/-- An IR round of the instance has its data through the layers. -/
theorem layer_ofS (hc : c.Good) (hI : c.mod.noStart.IsInst I) {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {r : CRound I.E I.F}
    {u : CRound (sigN c.imports.length) (sigN c.toComp.exports.length)}
    (h : IRRoundI c I j vs r u) : ∃ d : LayerI c I, d.OkS hI ∧ d.r = r ∧ d.u = u := by
  obtain ⟨xs, dss, hl, h₁, h₂, hrel, rfl⟩ := h
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  obtain ⟨cs₂, H₁, H₂⟩ := imp_calls (c := c.noStart) hI hrel
  exact ⟨⟨r, j, vs, xs, hk, cs₂, dss⟩, ⟨hl, h₁, h₂, H₁, H₂⟩, rfl, rfl⟩

/-- Lists of IR rounds of the instance have their data through the layers. -/
theorem layers_ofS (hc : c.Good) (hI : c.mod.noStart.IsInst I) :
    ∀ {lr : List (CRound I.E I.F)}
      {lu : List (CRound (sigN c.imports.length) (sigN c.toComp.exports.length))},
      List.Forall₂ (fun r u => ∃ j vs, IRRoundI c I j vs r u) lr lu →
      ∃ L : List (LayerI c I), (∀ d ∈ L, d.OkS hI) ∧ L.map LayerI.r = lr ∧ L.map LayerI.u = lu
  | [], [], .nil => ⟨[], (fun _ h => nomatch h), rfl, rfl⟩
  | _ :: _, _ :: _, .cons ⟨_, _, h⟩ hs => by
    obtain ⟨d, hd, rfl, rfl⟩ := layer_ofS hc hI h
    obtain ⟨L, hL, rfl, rfl⟩ := layers_ofS hc hI hs
    refine ⟨d :: L, fun d' hd' => ?_, rfl, rfl⟩
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact hd
    · exact hL d' hd'

/-! ## The layers, round by round -/

/-- **The environment**: the core node, the pairing, `splitH` and the import mask. -/
theorem layers_envG (S : CoreSem ImpModule) (hI : c.mod.noStart.IsInst I) {L : List (LayerI c I)}
    (hL : ∀ d ∈ L, d.OkS hI) (h : cplay (L.map LayerI.l₂) ∈ S.sem c.mod) :
    cplay (L.map LayerI.l₅) ∈ envSI S c := by
  have hN₁ : cplay (L.map LayerI.l₃) ∈ (S.sem c.mod).comp
      (Strategy.ofHandler (widenH (CoreModule.exports c.mod).length)) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := widenH _) (dite_eq_left d.hk) rfl .nil) h
  have hN : cplay (L.map LayerI.l₄) ∈
      coreNode S c.imports.length c.mod (SimpleI.lowerArgs c.imports) :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d hd => .cons (hL d hd).impls .nil) hN₁
  have hP : cplay ((L.map LayerI.l₄).map (CRound.inr (F₁ := sigU))) ∈ (Strategy.id sigU).pair
      (coreNode S c.imports.length c.mod (SimpleI.lowerArgs c.imports)) :=
    cplay_pair_inr hN
  rw [List.map_map] at hP
  have hS : cplay (L.map LayerI.l₅) ∈ ((Strategy.id sigU).pair (coreNode S
      c.imports.length c.mod (SimpleI.lowerArgs c.imports))).comp
        (Strategy.ofHandler (splitH c.imports.length)) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d _ =>
      .call (h := splitH _) (splitH_shift _ _ _) rfl .nil) hP
  exact cplay_ofHandler_comp (HB.of_map _ _ L fun d _ => .cons (hrounds_maskH _ _) .nil) hS

/-- **The export layer and `atSizes`.** -/
theorem layers_denG (S : CoreSem ImpModule) (hI : c.mod.noStart.IsInst I) {L : List (LayerI c I)}
    (hL : ∀ d ∈ L, d.OkS hI) (h : cplay (L.map LayerI.l₅) ∈ envSI S c) :
    cplay (L.map LayerI.u) ∈ c.toComp.den S := by
  have hU : cplay (L.map LayerI.l₆) ∈ c.toComp.denU S := by
    rw [denU_toCompI]
    refine cplay_comp_ofHandler (HC.of_map _ _ L fun d hd => ?_) h
    have hl' : checkLower c.exports[d.j.val].ty.params d.vs = some d.xs := (hL d hd).lower
    refine .call (h := exportsH _ _) (q' := (c.exports[d.j].core + c.imports.length, .flat d.xs))
      (k := fun n => .pure (n.bind (Adapter.up (.lift c.exports[d.j].ty)))) ?_ rfl .nil
    rw [exportsH_toCompI c d.j.isLt d.vs d.hk, hl']
    rfl
  have hW : cplay (L.map LayerI.l₇) ∈
      (Strategy.ofHandler (widenH c.imports.length)).comp (c.toComp.denU S) :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d _ => .cons (hrounds_widenH _ _) .nil) hU
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (HC.of_map _ _ L fun d _ => .call (h := narrowH _) rfl rfl .nil) hW


/-! ## `impSemS` -/

/-- **The core layer with a start function**: rounds of the instance played from a store the
start phase returns at are rounds of `impSemS P`. -/
theorem layers_semS {st : Option Nat} {s₀ : Store Nat} (hI : c.mod.IsInstS I st)
    (h₀ : Silmaril.Wasm.Game.StartsTo P Det.noHost I.store st s₀) {L : List (LayerI c I)}
    (hL : ∀ d ∈ L, d.OkS hI.noStart) (h : cplay (L.map LayerI.r) ∈ I.strategy P s₀) :
    cplay (L.map LayerI.l₂) ∈ (impSemS P).sem c.mod := by
  have hx : cplay (L.map LayerI.l₁) ∈
      (I.strategy P s₀).comp (Strategy.ofHandler (exportH (instNumI hI.noStart))) :=
    cplay_comp_ofHandler (HC.of_map _ _ L fun d hd =>
      .call (exportH_op hI.noStart d.hk d.r.q (hL d hd).core (hL d hd).args) rfl .nil) h
  have hy : cplay (L.map LayerI.l₂) ∈ core3SemAt P (c.mod.numAt I hI.2) s₀ :=
    cplay_ofHandler_comp (HB.of_map _ _ L fun d hd => .cons (hL d hd).imp .nil) hx
  show _ ∈ sSup (impStartStrategies P c.mod)
  rw [Strategy.mem_sSup]
  exact .inr ⟨_, .inl ⟨I, st, s₀, hI, h₀, rfl⟩, hy⟩

/-- **`impSemS` traps on every question when the start phase may fail** (or there is no
instance). -/
theorem trap_memI {m : ImpModule}
    (hfail : (¬ ∃ I st, m.IsInstS I st) ∨ m.StartFails P)
    (q : (CoreIface.sig (CoreModule.exports m)).Op) :
    cplay (E := CoreIface.sig (CoreModule.imports m)) [⟨q, [], none⟩] ∈ (impSemS P).sem m := by
  show twos [⟨q, none⟩] ∈ sSup (impStartStrategies P m)
  rw [Strategy.mem_sSup]
  refine .inr ⟨trapAll _ _, .inr ⟨rfl, hfail⟩, ?_⟩
  have hr : (Handler.toReduction (fun _ => (.pure none : Prog (CoreIface.sig (CoreModule.imports m))
      (Option Payload)) : Handler (CoreIface.sig (CoreModule.imports m))
        (CoreIface.sig (CoreModule.exports m)))).toLTS.Run .idle (twos [⟨q, none⟩]) .idle :=
    .vis (.ask q) (.vis (.ret (show _ = Prog.pure none from rfl)) (.nil _))
  exact Strategy.mem_ofHandler.mpr ⟨_, hr⟩

/-- **The IR side for sequences of calls with imports and a start function**: rounds of the core
instance played one after another from a store the start phase returns at are, as IR rounds, a
play of the IR denotation over `impSemS P`. -/
theorem seqI_denS (hc : c.Good) {st : Option Nat} {s₀ : Store Nat} (hI : c.mod.IsInstS I st)
    (h₀ : Silmaril.Wasm.Game.StartsTo P Det.noHost I.store st s₀) {lr : List (CRound I.E I.F)}
    {lu : List (CRound (sigN c.imports.length) (sigN c.toComp.exports.length))}
    (hrel : List.Forall₂ (fun r u => ∃ j vs, IRRoundI c I j vs r u) lr lu)
    (h : cplay lr ∈ I.strategy P s₀) : cplay lu ∈ c.toComp.den (impSemS P) := by
  obtain ⟨L, hL, rfl, rfl⟩ := layers_ofS hc hI.noStart hrel
  exact layers_denG _ hI.noStart hL (layers_envG _ hI.noStart hL (layers_semS hI h₀ hL h))

/-- **When the start phase may fail, the IR traps on every export call.** -/
theorem trap_denIS (hc : c.Good) (hfail : c.mod.StartFails P) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) :
    cplay [⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), [], none⟩] ∈
      c.toComp.den (impSemS P) := by
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  cases hl : checkLower c.exports[j].ty.params vs with
  | none => exact den_trapIG _ hk hl
  | some xs =>
    have h := den_of_semG (impSemS P) (dss := []) hk hl .nil
      (trap_memI (.inr hfail) (⟨c.exports[j].core, hk⟩, .flat xs))
    exact h

end Silmaril.Proofs.Wasm.Component.Reference
