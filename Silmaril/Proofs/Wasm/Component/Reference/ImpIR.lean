module

public import Silmaril.Proofs.Wasm.Component.Reference.ImpGames
public import Silmaril.Proofs.Wasm.Component.Reference.MultiIR

/-!
# The IR side with imports

`simpleI_specToIR : SimpleI.SpecToIR`: for a simple component with imports (`SimpleI`, core
import `k` the `canon lower` of component import `k`), a play of the core instance answering an
export call after import calls is, through every layer of the IR denotation over `impSem P`,
the IR play of the export question, the component import calls (`ImpRel`) and the lifted
answer. The layers, from the bottom:

* the instance's play (`cplay_mem_strategy`), `core3Sem`'s export handler (`exportH_op`) and
  import handler (`importH`: each core import call is one call of the import interface);
* the core node: `widenH` on top, the wiring `implsN` of the `canon lower` adapters below
  (`implsN_lower_none`, `implsN_lower_some`: the argument lift traps at once or calls component
  import `k`);
* the pairing, `splitH` at the number of imports (`splitH_shift`), the environment of imports
  (`maskH`, `hrounds_maskH`);
* the export handler with the lift adapter (`exportsH_toCompI`);
* `atSizes`: `widenH` below (the component import moves) and `narrowH` on top.

`impSem_toImp`: on import-free modules `impSem P` is `modSem P`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-! ## `impSem` -/

/-- Instances of a module with imports are unique. -/
theorem ImpModule.IsInst.unique {m : ImpModule} {I J : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) (hJ : m.IsInst J) : I = J := by
  obtain ⟨⟨mt, hmt⟩, _, _⟩ := hI
  obtain ⟨⟨mt', hmt'⟩, _, _⟩ := hJ
  have hv : some mt = some mt' := hmt.valid.symm.trans hmt'.valid
  cases Option.some.inj hv
  exact Silmaril.Wasm.Game.IsInstance.unique hmt hmt'

/-- The numeric instance of a module with its instance. -/
abbrev instNumI {m : ImpModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I) :
    NumInstance :=
  { inst := I, imports := m.imports, exports := m.exports, imports_eq := hI.2.1,
    exports_eq := hI.2.2 }

theorem impSem_sem {P : Profile} {m : ImpModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) : (impSem P).sem m = (core3Sem P).sem (instNumI hI) := by
  have hex : ∃ J, m.IsInst J := ⟨I, hI⟩
  have key : ∀ J (hJ : m.IsInst J), (core3Sem P).sem (instNumI hJ) =
      (core3Sem P).sem (instNumI hI) := by
    intro J hJ
    obtain rfl := ImpModule.IsInst.unique hJ hI
    rfl
  simp only [impSem, dite_eq_left hex]
  exact key _ hex.choose_spec

/-- On import-free modules `impSem` is `modSem`. -/
theorem impSem_toImp (P : Profile) (m : NumModule) :
    (impSem P).sem m.toImp = (modSem P).sem m := rfl

/-! ## The core layer -/

/-- `core3Sem`'s export handler on a call of core export `k`, for the instance's question `f`
of that export on the flat arguments `xs`. -/
theorem exportH_op {m : ImpModule} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I)
    {k : Nat} (hk : k < m.exports.length) {xs : List Flat} (f : I.F.Op) (h₁ : f.1.val = k)
    (h₂ : f.2.1 = xs.map ofFlat) :
    exportH (instNumI hI) (⟨k, hk⟩, .flat xs) = .call f fun a => .pure (answerPayload a) := by
  obtain ⟨fi, fa⟩ := f
  have hfi : fi = Fin.cast (instNumI hI).exports_length ⟨k, hk⟩ := Fin.ext h₁
  subst hfi
  have ht : typed? (I.exports.get (Fin.cast (instNumI hI).exports_length ⟨k, hk⟩)).params
      (xs.map ofFlat) = some fa := by
    unfold typed?
    rw [dite_eq_left (h₂ ▸ fa.2)]
    exact congrArg some (Subtype.ext h₂.symm)
  unfold exportH
  dsimp only
  erw [ht]

/-- The wiring of core import `k` when the argument lift fails: a trap, no call. -/
theorem implsN_lower_none {e t : Nat} {ims : Iface} {k : Nat} {nm : String} {ft : FuncTy}
    (hft : ims[k]? = some (nm, ft)) (hk : k < t) {xs : List Flat}
    (hl : liftArgs ft.params xs = none) :
    implsN e (SimpleI.lowerArgs ims) t (⟨k, hk⟩, .flat xs) = .pure none := by
  have ha : (SimpleI.lowerArgs ims)[k]? = some ⟨[.lower ft], .call k⟩ := by
    simp only [SimpleI.lowerArgs, List.getElem?_mapIdx, hft, Option.map_some]
  simp only [implsN, implsH, ha, Impl.prog, runChain, Adapter.down, hl, Option.map_none]

/-- The wiring of core import `k` when the arguments lift to `ws`: one call of component
import `k`, its answer lowered. -/
theorem implsN_lower_some {e t : Nat} {ims : Iface} {k : Nat} {nm : String} {ft : FuncTy}
    (hft : ims[k]? = some (nm, ft)) (hk : k < t) (he : k < e) {xs : List Flat}
    {ws : List Silmaril.Wasm.Component.Val} (hl : liftArgs ft.params xs = some ws) :
    implsN e (SimpleI.lowerArgs ims) t (⟨k, hk⟩, .flat xs) =
      .call (k, .vals ws) fun r => .pure (r.bind (Adapter.lower ft).up) := by
  have ha : (SimpleI.lowerArgs ims)[k]? = some ⟨[.lower ft], .call k⟩ := by
    simp only [SimpleI.lowerArgs, List.getElem?_mapIdx, hft, Option.map_some]
  simp only [implsN, implsH, ha, Impl.prog, runChain, Adapter.down, hl, Option.map_some,
    Target.prog, ite_eq_left he]
  rfl

/-- **One import call** through `core3Sem`'s import handler and the `canon lower` wiring. -/
theorem imp_call {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    {x : Round I.E} {ds : List (Round (sigN c.imports.length))} (h : ImpRel c I x ds) :
    ∃ x₂ : Round (CoreIface.sig (CoreModule.imports c.mod)),
      HRounds (importH (instNumI hI)) [x] [x₂] ∧
      HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
        (CoreModule.imports c.mod).length) [x₂] (ds.map Round.forget) := by
  obtain ⟨nm, ft, A, hft, hv, hrel⟩ := h
  have hk : x.1.1.val < (CoreModule.imports c.mod).length :=
    lt_of_lt_of_eq x.1.1.isLt (instNumI hI).imports_length.symm
  have H₁ : HRounds (importH (instNumI hI)) [x]
      [⟨(⟨x.1.1.val, hk⟩, .flat (x.1.2.1.filterMap toFlat?)), A⟩] :=
    .call (h := importH (instNumI hI)) (k := fun r => .pure (payloadAnswer _ r)) rfl
      (by rw [hv]) .nil
  refine ⟨_, H₁, ?_⟩
  revert hrel
  cases hl : liftArgs ft.params (x.1.2.1.filterMap toFlat?) with
  | none =>
    intro hrel
    obtain ⟨rfl, rfl⟩ := hrel
    exact .pure (implsN_lower_none hft hk hl) .nil
  | some ws =>
    intro hrel
    obtain ⟨hk', R, rfl, rfl⟩ := hrel
    exact .call (implsN_lower_some hft hk hk' hl) rfl .nil

/-- **The import calls** of an export call. -/
theorem imp_calls {c : SimpleI} {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I) :
    ∀ {cs : List (Round I.E)} {dss : List (List (Round (sigN c.imports.length)))},
      List.Forall₂ (ImpRel c I) cs dss →
      ∃ cs₂ : List (Round (CoreIface.sig (CoreModule.imports c.mod))),
        HRounds (importH (instNumI hI)) cs cs₂ ∧
        HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
          (CoreModule.imports c.mod).length) cs₂ (dss.flatten.map Round.forget)
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons h hs => by
    obtain ⟨x₂, H₁, H₂⟩ := imp_call hI h
    obtain ⟨cs₂, H₁', H₂'⟩ := imp_calls hI hs
    refine ⟨x₂ :: cs₂, H₁.append H₁', ?_⟩
    rw [List.flatten_cons, List.map_append]
    exact H₂.append H₂'

/-! ## The environment and the export layer -/

theorem splitH_shift (n i : Nat) (p : Payload) :
    splitH n (i + n, p) = .call (.inr (i, p)) fun r => .pure r := by
  simp only [splitH]
  rw [ite_eq_right (by omega), Nat.add_sub_cancel]

theorem hrounds_maskH (n : Nat) :
    ∀ l : List (Round (sigN n)), HRounds (maskH n) (l.map Round.forget) (l.map Round.forget)
  | [] => .nil
  | ⟨q, a⟩ :: l => by
    show HRounds (maskH n) (⟨(q.1.val, q.2), a⟩ :: l.map Round.forget)
      (⟨(q.1.val, q.2), a⟩ :: l.map Round.forget)
    exact .call (h := maskH n) (q' := (q.1.val, q.2)) (k := fun r => .pure r)
      (ite_eq_left q.1.isLt) rfl (hrounds_maskH n l)

/-- The environment of a simple component with imports: the imports, then the core instance. -/
abbrev envSI (C : CoreSem ImpModule) (c : SimpleI) : Strategy sigU sigU :=
  ext c.imports.length (Strategy.ofHandler (maskH c.imports.length))
    (coreNode C c.imports.length c.mod (SimpleI.lowerArgs c.imports))

theorem denU_toCompI (C : CoreSem ImpModule) (c : SimpleI) :
    c.toComp.denU C = (envSI C c).comp (Strategy.ofHandler
      (exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports)) := by
  simp only [SimpleI.toComp, Comp.denU, denNodes, Node.den, envAfter, Node.width,
    Comp.exports_mk]
  rfl

/-- The export handler on export `j` of a simple component with imports. -/
theorem exportsH_toCompI (c : SimpleI) {j : Nat} (hj : j < c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (hcore : c.exports[j].core < c.mod.exports.length) :
    exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports (j, .vals vs) =
      match checkLower c.exports[j].ty.params vs with
      | none => .pure none
      | some xs => .call (c.exports[j].core + c.imports.length, .flat xs)
          fun n => .pure (n.bind (Adapter.up (.lift c.exports[j].ty))) := by
  have hget : (c.toComp.exports.map Silmaril.Wasm.Component.Export.impl)[j]? =
      some ⟨[.lift c.exports[j].ty], .call (c.exports[j].core + c.imports.length)⟩ := by
    simp [SimpleI.toComp, hj]
  have hlt : c.exports[j].core + c.imports.length < c.imports.length + c.mod.exports.length := by
    omega
  simp only [exportsH, implsH, hget, Impl.prog, runChain, Adapter.down]
  cases checkLower c.exports[j].ty.params vs with
  | none => rfl
  | some xs => simp [Target.prog, hlt, Prog.bind]

/-! ## The theorem -/

/-- The layers above the core instance, for one export round, at the untyped interface. -/
theorem denU_of_sem {P : Profile} {c : SimpleI} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = some xs)
    {cs₂ : List (Round (CoreIface.sig (CoreModule.imports c.mod)))}
    {dss : List (List (Round (sigN c.imports.length)))}
    (H₂ : HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) cs₂ (dss.flatten.map Round.forget))
    {R : Option Payload}
    (h : cplay [⟨(⟨c.exports[j].core, hcore⟩, .flat xs), cs₂, R⟩] ∈ (impSem P).sem c.mod) :
    cplay [⟨(j.val, .vals vs), dss.flatten.map Round.forget,
      R.bind (Adapter.up (.lift c.exports[j].ty))⟩] ∈ c.toComp.denU (impSem P) := by
  have hN₁ : cplay [⟨(c.exports[j].core, .flat xs), cs₂, R⟩] ∈
      ((impSem P).sem c.mod).comp (Strategy.ofHandler (widenH (CoreModule.exports c.mod).length)) :=
    cplay_comp_ofHandler (.call (h := widenH _) (dite_eq_left hcore) rfl .nil) h
  have hN : cplay [⟨(c.exports[j].core, .flat xs), dss.flatten.map Round.forget, R⟩] ∈
      coreNode (impSem P) c.imports.length c.mod (SimpleI.lowerArgs c.imports) :=
    cplay_ofHandler_comp (.cons H₂ .nil) hN₁
  have hP := cplay_pair_inr (σ₁ := Strategy.id sigU) hN
  have hS : cplay [⟨(c.exports[j].core + c.imports.length, .flat xs),
      dss.flatten.map Round.forget, R⟩] ∈ ((Strategy.id sigU).pair (coreNode (impSem P)
        c.imports.length c.mod (SimpleI.lowerArgs c.imports))).comp
          (Strategy.ofHandler (splitH c.imports.length)) :=
    cplay_comp_ofHandler (.call (h := splitH _) (splitH_shift _ _ _) rfl .nil) hP
  have hE : cplay [⟨(c.exports[j].core + c.imports.length, .flat xs),
      dss.flatten.map Round.forget, R⟩] ∈ envSI (impSem P) c :=
    cplay_ofHandler_comp (.cons (hrounds_maskH _ _) .nil) hS
  have hl' : checkLower c.exports[j.val].ty.params vs = some xs := hl
  rw [denU_toCompI]
  refine cplay_comp_ofHandler (.call (h := exportsH _ _)
    (q' := (c.exports[j].core + c.imports.length, .flat xs))
    (k := fun n => .pure (n.bind (Adapter.up (.lift c.exports[j].ty)))) ?_ rfl .nil) hE
  rw [exportsH_toCompI c j.isLt vs hcore, hl']
  rfl

/-- The layers above the core instance, for one export round. -/
theorem den_of_sem {P : Profile} {c : SimpleI} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} {xs : List Flat}
    (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = some xs)
    {cs₂ : List (Round (CoreIface.sig (CoreModule.imports c.mod)))}
    {dss : List (List (Round (sigN c.imports.length)))}
    (H₂ : HRounds (implsN c.imports.length (SimpleI.lowerArgs c.imports)
      (CoreModule.imports c.mod).length) cs₂ (dss.flatten.map Round.forget))
    {R : Option Payload}
    (h : cplay [⟨(⟨c.exports[j].core, hcore⟩, .flat xs), cs₂, R⟩] ∈ (impSem P).sem c.mod) :
    cplay [⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), dss.flatten,
      R.bind (Adapter.up (.lift c.exports[j].ty))⟩] ∈ c.toComp.den (impSem P) := by
  have hU := denU_of_sem hcore hl H₂ h
  have hW : cplay [⟨(j.val, .vals vs), dss.flatten, R.bind (Adapter.up (.lift c.exports[j].ty))⟩] ∈
      (Strategy.ofHandler (widenH c.imports.length)).comp (c.toComp.denU (impSem P)) :=
    cplay_ofHandler_comp (.cons (hrounds_widenH _ _) .nil) hU
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (.call (h := narrowH _) rfl rfl .nil) hW

/-- A trap of the argument check, at the untyped interface. -/
theorem denU_trapI {P : Profile} {c : SimpleI} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = none) :
    cplay [(⟨(j.val, .vals vs), [], none⟩ : CRound sigU sigU)] ∈ c.toComp.denU (impSem P) := by
  have hl' : checkLower c.exports[j.val].ty.params vs = none := hl
  rw [denU_toCompI]
  refine cplay_comp_ofHandler (.pure (h := exportsH _ _) ?_ .nil) (Strategy.nil_mem _)
  rw [exportsH_toCompI c j.isLt vs hcore, hl']

/-- A trap of the argument check. -/
theorem den_trapI {P : Profile} {c : SimpleI} {j : Fin c.exports.length}
    {vs : List Silmaril.Wasm.Component.Val} (hcore : c.exports[j].core < c.mod.exports.length)
    (hl : checkLower c.exports[j].ty.params vs = none) :
    cplay [⟨(⟨j, by simp [SimpleI.toComp]⟩, .vals vs), [], none⟩] ∈ c.toComp.den (impSem P) := by
  have hU := denU_trapI (P := P) hcore hl
  have hW : cplay [(⟨(j.val, .vals vs), [], none⟩ : CRound (sigN c.imports.length) sigU)] ∈
      (Strategy.ofHandler (widenH c.imports.length)).comp (c.toComp.denU (impSem P)) :=
    cplay_ofHandler_comp (.cons .nil .nil) hU
  unfold Comp.den atSizes
  exact cplay_comp_ofHandler (.call (h := narrowH _) rfl rfl .nil) hW

/-- **The IR side with imports** (proved). -/
theorem simpleI_specToIR : SimpleI.SpecToIR := by
  intro P c hc I hI j vs
  obtain ⟨nm, hcore⟩ := hc.core _ (List.getElem_mem j.isLt)
  have hk : c.exports[j].core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcore).1
  refine ⟨fun hl => den_trapI hk hl, ?_⟩
  intro xs hl f h₁ h₂ cs w q hpath dss hrel
  obtain ⟨cs₂, H₁, H₂⟩ := imp_calls hI hrel
  have hinst : cplay [⟨f, cs, w⟩] ∈ I.strategy P I.store := cplay_mem_strategy hpath
  have hx : cplay [⟨(⟨c.exports[j].core, hk⟩, .flat xs), cs, answerPayload w⟩] ∈
      (I.strategy P I.store).comp (Strategy.ofHandler (exportH (instNumI hI))) :=
    cplay_comp_ofHandler (.call (exportH_op hI hk f h₁ h₂) rfl .nil) hinst
  have hsem : cplay [⟨(⟨c.exports[j].core, hk⟩, .flat xs), cs₂, answerPayload w⟩] ∈
      (impSem P).sem c.mod := by
    rw [impSem_sem hI]
    exact cplay_ofHandler_comp (.cons H₁ .nil) hx
  exact den_of_sem hk hl H₂ hsem

end Silmaril.Proofs.Wasm.Component.Reference
