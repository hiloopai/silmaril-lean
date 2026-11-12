module

public import Silmaril.Wasm.SpecTec.Institution.Nondet.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Target.Thms

/-!
# Choice cover on round 6's domain: the exact forward simulation

Round 6's forward half is "up to Core's choice" (`Round6.Target.forwardR`) for one reason only:
`vcvtop` (`Round5.Convert.fwd_convertR`), where SpecTec's `$vcvtop__` is a function and Core's
`VecConvertRel` a relation. On `BoundedSel` code that reason is gone: the only `vcvtop`
operators that are not `FloatMissel` are the `extend` ones, and `VecConvertRel` is a function
there (`vecConvertRel_extend_fun`). This file redoes the target recursion with that
observation and gets the forward half **exactly**:

* `fwd_vectorSel`: every Core vector step from `AdminsSel` code is matched exactly (a copy of
  `Round5.Convert.fwd_vectorR`, with the `vecConvert` case made exact);
* `forwardSel`: every Core step from bounded code that is not a cast redex and has no
  `FloatMissel` instruction is matched exactly, up to `ConfigEq` (a copy of
  `Round6.Target.forwardR`, with motive `FwdUp` instead of `FwdUp ∨ FwdUpR`; the leaves are the
  same lemmas);
* `fwd_exact`: at the concrete primitives `Round4Int.BI`, on `Dom`, every Core successor is a
  step fact of `stepModel BI` up to `ConfigEq` (casts from `Round6.Int.openR_backend`'s cast
  leaf, the rest from `forwardSel` and the transfer lemma);
* `choiceCover`: hence the frozen `Nondet.Task.choiceCover` holds, with the single admissible
  choice `B := BI` for every successor.

No primitive had to be made a parameter: on `Dom` the concrete `BI` already covers every Core
successor.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Cover

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecVector (HasVectorRules)
open Silmaril.SpecTec.Equiv.ExecStepRules (pureRule)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Target
open Silmaril.Wasm.SpecTec.Sim.Round5.Convert (fwdN_vecConvertR)
open Silmaril.Wasm.SpecTec.Institution.Nondet
open Silmaril.Wasm.SpecTec.Institution.Wasm30
open Round4 (Bounded)
open Round4Int (BI)
open FwdMem (FwdUp fwdUp_of_fwdP)
open Round5.Target (AdminsSel AdminSel instrSel instrsSel)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## `AdminsSel` in evaluation contexts -/

/-- The hole of `ctxt-instrs`. -/
theorem adminsSel_mid {vs : List Val} {b c : List Admin} (h : AdminsSel (vals vs ++ b ++ c)) :
    AdminsSel b :=
  (Round5.Target.adminsSel_append.1 (Round5.Target.adminsSel_append.1 h).1).2

/-- The body of a label. -/
theorem adminsSel_label {n : Nat} {cont : List Instr} {b : List Admin}
    (h : AdminsSel [.label n cont b]) : AdminsSel b := by
  simp only [AdminsSel, AdminSel] at h
  exact h.1.2

/-- The body of a handler. -/
theorem adminsSel_handler {n : Nat} {cs : List Catch} {b : List Admin}
    (h : AdminsSel [.handler n cs b]) : AdminsSel b := by
  simp only [AdminsSel, AdminSel] at h
  exact h.1

/-- The body of a frame. -/
theorem adminsSel_frame {n : Nat} {fi : Frame} {b : List Admin}
    (h : AdminsSel [.frame n fi b]) : AdminsSel b := by
  simp only [AdminsSel, AdminSel] at h
  exact h.1

/-! ## `vcvtop` on `BoundedSel` code -/

/-- **`VecConvertRel` is a function at the `extend` operators**, under every profile. -/
theorem vecConvertRel_extend_fun {src tgt : Shape} {hf : Half} {sg : Signedness} {a r₁ r₂ : V128}
    (h₁ : VecConvertRel P src tgt (.extend hf sg) a r₁)
    (h₂ : VecConvertRel P src tgt (.extend hf sg) a r₂) : r₁ = r₂ := by
  unfold VecConvertRel at h₁ h₂
  cases hP : P.nan <;> simp only [hP, vcvtopRel] at h₁ h₂ <;>
    exact Option.some.inj (h₁.symm.trans h₂)

/-- **The `vcvtop` operators allowed in `AdminsSel` code are the `extend` ones.** -/
theorem extend_of_instrSel {src tgt : Shape} {op : VecConvertOp}
    (h : instrSel (.vecConvert src tgt op) = true) : ∃ hf sg, op = .extend hf sg := by
  cases op with
  | extend hf sg => exact ⟨hf, sg, rfl⟩
  | _ => simp [instrSel, Round5.SimdTy.FloatMissel] at h

/-! ## The vector steps, exactly -/

section

variable {s : Store H} {f : Frame}

/-- **`vcvtop` from `AdminsSel` code, forward exactly**: the operator is an `extend` one, where
the result `$vcvtop__` picks is Core's only one. -/
theorem fwd_vecConvertSel {sh₁ sh₂ : Shape} {op : VecConvertOp} {a r : V128}
    (hc : VecConvertRel P sh₁ sh₂ op a r)
    (hsel : AdminsSel [vconst a, .plain (.vecConvert sh₁ sh₂ op)]) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, [vconst a, .plain (.vecConvert sh₁ sh₂ op)]⟩
      ⟨s, f, [vconst r]⟩ := by
  have hi : instrSel (.vecConvert sh₁ sh₂ op) = true := by
    simpa only [AdminsSel, AdminSel, and_true] using hsel.2
  obtain ⟨hf, sg, rfl⟩ := extend_of_instrSel hi
  have C : Round5.Simd.VecConvertR (simEnv (BI P hn host)) P :=
    Round5.Convert.vecConvertR_builtins
  obtain ⟨c, hcv⟩ := C.total sh₁ sh₂ _ a r hc
  obtain ⟨r', hr', rfl⟩ := C.sound sh₁ sh₂ _ a c hcv
  obtain rfl : r = r' := vecConvertRel_extend_fun hc hr'
  exact fwdN_vecConvertR (Typing.typingFacts_simEnv _ hn) (hasStepRules_simEnv _).pure
    (Vec.hasVectorRules_simEnv _) (Round5.SimdTy.vecTypingL P hn host) hcv

/-- **Every Core vector step from `AdminsSel` code, forward exactly**, at the concrete
primitives. A copy of `Round5.Convert.fwd_vectorR`, whose `vecConvert` case is now exact
(`fwd_vecConvertSel`). -/
theorem fwd_vectorSel {is is' : List Admin} (h : VectorStep P is is') (hsel : AdminsSel is) :
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have hr : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 0 pureRule :=
    (hasStepRules_simEnv _).pure
  have V : HasVectorRules (simEnv (BI P hn host)) := Vec.hasVectorRules_simEnv _
  have Ty : Round5.SimdTy.VecTypingL (simEnv (BI P hn host)) :=
    Round5.SimdTy.vecTypingL P hn host
  have A : Round5.Convert.VecAgreeNC (simEnv (BI P hn host)) P :=
    Round5.Convert.vecAgreeNC_builtins
  have Fy : Vec.FloatTyping (simEnv (BI P hn host)) := Floats.floatTyping_simEnv _
  cases h with
  | vecConvert hc => exact fwd_vecConvertSel hc hsel
  | vecUnOp op a => exact Round5.Convert.fwdN_vecUnOp T hr V Ty A op a
  | vecBinOp op a b => exact Round5.Convert.fwdN_vecBinOp T hr V Ty A op a b
  | vecTernOp op a b c => exact Round5.Convert.fwdN_vecTernOp T hr V Ty A op a b c
  | vecTestOp op a => exact Round5.Convert.fwdN_vecTestOp T hr V Ty A op a
  | vecIntUnOp sh op a => exact Round5.Convert.fwdN_vecIntUnOp T hr V Ty A sh op a
  | vecFloatUnOp h => exact Round5.Convert.fwdN_vecFloatUnOp T hr V Ty A h
  | vecFloatUnOpTrap h => exact Round5.Convert.fwdN_vecFloatUnOpTrap T hr V Ty A h
  | vecIntBinOp sh op a b => exact Round5.Convert.fwdN_vecIntBinOp T hr V Ty A sh op a b
  | vecFloatBinOp h => exact Round5.Convert.fwdN_vecFloatBinOp T hr V Ty A h
  | vecFloatBinOpTrap h => exact Round5.Convert.fwdN_vecFloatBinOpTrap T hr V Ty A h
  | vecIntTernOp sh op a b c => exact Round5.Convert.fwdN_vecIntTernOp T hr V Ty A sh op a b c
  | vecFloatTernOp h => exact Round5.Convert.fwdN_vecFloatTernOp T hr V Ty A h
  | vecFloatTernOpTrap h => exact Round5.Convert.fwdN_vecFloatTernOpTrap T hr V Ty A h
  | vecAllTrue sh a => exact Round5.Convert.fwdN_vecAllTrue T hr V Ty A sh a
  | vecIntRelOp sh op a b => exact Round5.Convert.fwdN_vecIntRelOp T hr V Ty A sh op a b
  | vecFloatRelOp sh op a b => exact Round5.Convert.fwdN_vecFloatRelOp T hr V Ty A sh op a b
  | vecShiftOp sh op a n => exact Round5.Convert.fwdN_vecShiftOp T hr V Ty A sh op a n
  | vecBitmask sh a => exact Round5.Convert.fwdN_vecBitmask T hr V Ty A sh a
  | vecSwizzle a b => exact Round5.Convert.fwdN_vecSwizzle T hr V Ty A a b
  | vecRelaxedSwizzle a b => exact Round5.Convert.fwdN_vecRelaxedSwizzle T hr V Ty A a b
  | vecShuffle idx a b hidx => exact Round5.Convert.fwdN_vecShuffle T hr V Ty A idx a b hidx
  | vecSplat sh x => exact Round5.Convert.fwdN_vecSplat T hr V Ty A sh x
  | vecExtractLane sh sx i a hi =>
    exact Round5.Convert.fwdN_vecExtractLane T hr V Ty A Fy sh sx i a hi
  | vecReplaceLane sh i a x hi => exact Round5.Convert.fwdN_vecReplaceLane T hr V Ty A sh i a x hi
  | vecExtUnOp h => exact Round5.Convert.fwdN_vecExtUnOp T hr V Ty A h
  | vecExtBinOp h => exact Round5.Convert.fwdN_vecExtBinOp T hr V Ty A h
  | vecExtTernOp h => exact Round5.Convert.fwdN_vecExtTernOp T hr V Ty A h
  | vecNarrow h => exact Round5.Convert.fwdN_vecNarrow T hr V Ty A h

end

/-! ## The recursion -/

/-- **The forward simulation, exactly, from bounded `AdminsSel` code whose redex is not a
cast**, at the concrete primitives, for an injective encoding and a finite host. the target
`Round6.Target.forwardR` with motive `FwdUp`: every leaf is the lemma `forwardR` uses, the
vector leaf is `fwd_vectorSel`, and the context rules are `FwdMem.fwdUp_ctxt…`. -/
theorem forwardSel (hinj : Function.Injective hn) (hf : HostFinite host) {c c' : Config H}
    (h : Step P host c c') : Bounded c → ¬ CastRedex c.code → AdminsSel c.code →
      FwdUp (simEnv (BI P hn host)) hn c c' :=
  have T := Typing.typingFacts_simEnv (BI P hn host) hn
  have Ty := Typing.ctrlTyping_simEnv (BI P hn host)
  have St := Typing.stateTyping_simEnv (BI P hn host)
  have X := Typing.exnTyping_simEnv' (BI P hn host)
  have TB := Round5.Int.typesB (BI P hn host)
  have hr := Round5.FwdRef2.hostRespectsT_all (BI P hn host) hinj host
  Step.rec (motive := fun c c' _ => Bounded c → ¬ CastRedex c.code → AdminsSel c.code →
      FwdUp (simEnv (BI P hn host)) hn c c')
    (fun hs _ _ _ => fwdUp_of_fwdP (IntNumeric.fwd_parametric T hs))
    (fun hs _ _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_numeric5 hs))
    (fun hs _ _ hs' => fwdUp_of_fwdP (fwd_vectorSel hs hs'))
    (fun hs _ _ _ => fwdUp_of_fwdP (State.fwd_variable_ _ T St hs))
    (fun hs hb _ _ => fwdUp_of_fwdP (Memory.fwd_table_bounded _ T St (ConfigOk.memTyping_simEnv _)
      (RefOk.growFuns_builtins hn host) (ConfigOk.instTyping_simEnv _) hs hb.store.tables))
    (fun hs hb _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_memory5 hs hb))
    (fun hs hb hx _ => fwdUp_of_fwdP (fwd_referenceNC hs hb hx))
    (fun hs hb _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_aggregate5 (Round5.Fwd.aggTypesB_of TB)
      (Round5.FwdRef.newDataNumB_builtins hn host) (Round5.Fwd.initDataZeroB_builtins hn host)
      hs hb))
    (fun _ hne ih hb hx hs' => FwdMem.fwdUp_ctxtInstrs T hne
      (ih (Round5.Fwd.bounded_ctxtInstrs hb) (not_castRedex_mid hx) (adminsSel_mid hs')))
    (fun _ ih hb hx hs' => FwdMem.fwdUp_ctxtLabel T
      (ih (Round5.Fwd.bounded_ctxtLabel hb) (not_castRedex_label hx) (adminsSel_label hs')))
    (fun _ ih hb hx hs' => FwdMem.fwdUp_ctxtHandler T
      (ih (Round5.Fwd.bounded_ctxtHandler hb) (not_castRedex_handler hx) (adminsSel_handler hs')))
    (fun _ ih hb hx hs' => FwdMem.fwdUp_ctxtFrame T
      (ih (Round5.Fwd.bounded_ctxtFrame hb) (not_castRedex_frame hx) (adminsSel_frame hs')))
    (fun h₁ h₂ hb _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_block5 TB h₁ h₂ hb.frame))
    (fun h₁ h₂ hb _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_loop5 TB h₁ h₂ hb.frame))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_ifTrue _ T Ty h₁))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_ifFalse _ T Ty))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_labelVals _ T))
    (fun h₁ h₂ _ _ _ => fwdUp_of_fwdP (fwd_brLabelZero _ T Ty h₁ h₂))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_brLabelSucc _ T Ty h₁))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_brHandler _ T Ty))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_brIfTrue _ T Ty h₁))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_brIfFalse _ T Ty))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_brTableLt _ T Ty h₁))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_brTableGe _ T Ty h₁))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_brOnNullNull _ T Ty))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_brOnNullAddr _ T Ty h₁))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_brOnNonNullNull _ T Ty))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_brOnNonNullAddr _ T Ty h₁))
    (fun _ _ hx => absurd castRedex_brOnCast hx)
    (fun _ _ hx => absurd castRedex_brOnCast hx)
    (fun _ _ hx => absurd castRedex_brOnCastFail hx)
    (fun _ _ hx => absurd castRedex_brOnCastFail hx)
    (fun h₁ h₂ _ _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_call5 h₁ h₂))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_callRefNull _ T Ty h₁))
    (fun hc hfa hex hlen hcode hb _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_callRefFunc5 TB hc hfa hex hlen hcode
      (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)))
    (fun hc hfa hex hlen hcode hh hb _ _ => fwdUp_of_fwdP (Round5.FwdRef.fwd_callRefHostT TB hf hr hc hfa hex
      hlen hcode hh (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)))
    (fun hc hfa hex hlen hcode hh hb _ _ => fwdUp_of_fwdP (Round5.FwdRef.fwd_callRefHostDivT TB hf hr hc hfa
      hex hlen hcode hh (Round5.Fwd.tyBnd_funcType hb.storeBnd hfa)))
    (fun h₁ h₂ _ _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_returnCall5 h₁ h₂))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_returnCallRefLabel _ T Ty h₁))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_returnCallRefHandler _ T Ty h₁))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_returnCallRefFrameNull _ T Ty h₁))
    (fun hc hfn hex hlen hb _ _ => (Round5.Fwd.fwdUp_returnCallRefFrameAddr5 TB hc hfn hex hlen
      (Round5.Fwd.tyBnd_funcType hb.storeBnd hfn)))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_callIndirect _ T Ty))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_returnCallIndirect _ T Ty))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_frameVals _ T h₁))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_returnFrame _ T Ty h₁))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_returnLabel _ T))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_returnHandler _ T))
    (fun htag hex hlen hb _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_throw5 TB htag hex hlen hb.storeBnd))
    (fun _ _ _ => fwdUp_of_fwdP (Exn.fwd_throwRefNull _ T))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (Exn.fwd_throwRefInstrs _ T X h₁))
    (fun _ _ _ => fwdUp_of_fwdP (Exn.fwd_throwRefLabel _ T X))
    (fun _ _ _ => fwdUp_of_fwdP (Exn.fwd_throwRefFrame _ T X))
    (fun _ _ _ => fwdUp_of_fwdP (Exn.fwd_throwRefHandlerEmpty _ T X))
    (fun he ht _ _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_throwRefHandlerCatch5 he ht))
    (fun he ht _ _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_throwRefHandlerCatchRef5 he ht))
    (fun _ _ _ => fwdUp_of_fwdP (Exn.fwd_throwRefHandlerCatchAll _ T X))
    (fun _ _ _ => fwdUp_of_fwdP (Exn.fwd_throwRefHandlerCatchAllRef _ T X))
    (fun hnm _ _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_throwRefHandlerNext5 hnm))
    (fun h₁ h₂ hb _ _ => fwdUp_of_fwdP (Round5.Fwd.fwd_tryTable5 TB h₁ h₂ hb.frame))
    (fun _ _ _ => fwdUp_of_fwdP (Exn.fwd_handlerVals _ T))
    (fun h₁ _ _ _ => fwdUp_of_fwdP (fwd_trapInstrs _ T h₁))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_trapLabel _ T))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_trapHandler _ T))
    (fun _ _ _ => fwdUp_of_fwdP (fwd_trapFrame _ T))

    h

/-! ## Every Core successor on `Dom`, at the concrete primitives -/

/-- **The exact forward half on `Dom`**, at the concrete primitives `Round4Int.BI`: every Core
successor of a point of `Dom` is, up to `ConfigEq`, a step fact of `stepModel BI`. Cast redexes
use the cast leaf of `Round6.Int.openR_backend`; every other step uses `forwardSel` and the
transfer lemma. -/
theorem fwd_exact (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {nd : Bool} {r : RelaxedChoice} {c c' : Config H} (hc : Dom (Profile.spec nd r) host c)
    (hs : Step (Profile.spec nd r) host c c') :
    ∃ d', Bwd.ConfigEq c' d' ∧
      MStep (BI (Profile.spec nd r) hn host) (configV hn c) (configV hn d') := by
  obtain ⟨⟨ts, hok⟩, hb, hsucc⟩ := hc
  have O := Round6.Int.openR_backend (nd := nd) (r := r) hinj hf hh
  have htc := Round5.Target.typed_of_configOk_sel (BI (Profile.spec nd r) hn host) hn hok hb
  have hr : Round4.SimRel (BI (Profile.spec nd r) hn host) hn c c := ⟨Bwd.ConfigEq.refl c, htc⟩
  by_cases hx : CastRedex c.code
  · obtain ⟨d', hd', hst⟩ := O.casts.fwd c c c' ts hok hb hsucc hr hx hs
    exact ⟨d', hd'.1, hst⟩
  · have htc' := Round5.Target.typed_of_configOk_sel (BI (Profile.spec nd r) hn host) hn
      (Step.preservation hh hok hs).1 (hsucc c' hs)
    obtain ⟨d', hd', -, hst⟩ := forwardSel hinj hf hs hb.1.1 hx hb.2.code htc htc'
    exact ⟨d', hd', O.transfer.fwd c c ts _ hok hb hr hx hst⟩

/-- **`Nondet.Task.choiceCover` holds**, with the one admissible choice `Round4Int.BI` for every
Core successor (`Nondet.halves_BI`, `fwd_exact`). -/
theorem choiceCover : Task.choiceCover := by
  intro H hn hinj host hf hh nd r c hc c' hs
  obtain ⟨d', he, hd⟩ := fwd_exact hinj hf hh hc hs
  exact ⟨_, halves_BI hinj hf hh nd r, d', he, hd⟩

/-! ## The comorphism on all of `Dom` -/

/-- **Two-sided on all of `Dom`, pointwise**, at the concrete primitives: every
`CfgRel`-respecting step sentence holds in Core iff it holds in `stepModel BI`. No choice
independence is needed: the forward half is exact (`fwd_exact`). -/
theorem sat_iff_dom (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    {nd : Bool} {r : RelaxedChoice} {c : Config H} (hc : Dom (Profile.spec nd r) host c)
    {s : Atlas.BSen Unit Value} (hs : s.Respects (Atlas.SpecTec.CfgRel hn)) :
    (Atlas.SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host)).Sat c s ↔
      (modelChart (stepModel (BI (Profile.spec nd r) hn host))).Sat (configV hn c) s := by
  refine Atlas.BSen.sat_iff_upto (fun u => ?_) (bwd_rel (halves_BI hinj hf hh nd r) hc) hs
  rintro b ⟨c', hs', rfl⟩
  obtain ⟨d', he, hd⟩ := fwd_exact hinj hf hh hc hs'
  exact ⟨configV hn d', hd, c', d', he, rfl, rfl⟩

/-- **The wasm-3.0 comorphism on all 's domain**: an `equal` transition from the Core
step chart on `Dom` to `modelChart (stepModel BI)`, on every `CfgRel`-respecting sentence. It
extends `Wasm30.toModel` from `DomDet` to `Dom`. -/
def toModelDom (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (nd : Bool) (r : RelaxedChoice) :
    Atlas.Transition
      (Atlas.SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host))
      (modelChart (stepModel (BI (Profile.spec nd r) hn host))) :=
  Atlas.BTrans.ofUpTo (Atlas.SpecTec.CfgRel hn) (configV hn) id (fun _ _ => trivial)
    (fun c hc u => by
      rintro b ⟨c', hs, rfl⟩
      obtain ⟨d', he, hd⟩ := fwd_exact hinj hf hh hc hs
      exact ⟨configV hn d', hd, c', d', he, rfl, rfl⟩)
    (fun _ hc u => bwd_rel (halves_BI hinj hf hh nd r) hc u)

theorem toModelDom_dir (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host)
    (nd : Bool) (r : RelaxedChoice) : (toModelDom hinj hf hh nd r).dir = .equal := rfl

/-- **The set-valued model, unconditionally**: `Nondet.toUnion` at the proved `choiceCover`. -/
def toUnion (hinj : Function.Injective hn) (hf : HostFinite host) (hh : HostOk host) (nd : Bool)
    (r : RelaxedChoice) :
    Atlas.Transition
      (Atlas.SpecTec.coreChart (Profile.spec nd r) host hn (Dom (Profile.spec nd r) host))
      (unionChart hn (Profile.spec nd r) host) :=
  Nondet.toUnion choiceCover hinj hf hh nd r

end Silmaril.Wasm.SpecTec.Institution.Cover
