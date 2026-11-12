module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.Reading.Casts
public import Silmaril.Wasm.SpecTec.Sim.Round6.CastsV.Defs

/-!
# Round 6: the four cast rules, forward, from `RefOkBB`

`Round5.Fwd.fwd_refTest5` & co. (`Round5Fwd/Refs.lean`), copied for the new reading: from
`RefOkBB` (`Ref_ok` under `DDerivesB` is Core's `RefOk` on typed stores and bounded types), each
cast instruction steps forward under `SStepB` exactly as in Core. `castsFwdB_of` assembles them
into `CastsFwdB`, the cast fields of `Round5.Fwd.Rest` restated for `FwdPB`.

Round 6, track casts-v: each cast lemma is proved from a `CastsV.CastRefOk` hypothesis at a
configuration predicate `V` (`fwd_refTestG` & co.), which asks `RefOkAtB` only at the casts that
satisfy `V`. The `RefOkBB` statements are the instances at `V c := ModuleBnd c.frame.module`
(`castRefOk_bnd`), unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Reading

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.ExecStepRules (readRule)
open Silmaril.SpecTec.Equiv.Execution (evalExp_iterPat)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4 (Bounded tyBnd ModuleBnd)
open Round4Int (BI)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## `Step/read` under the new reading -/

/-- **`Step/read`, under the new reading** (`Sim.sstep_read` for `SStepB`). -/
theorem sstepB_read {env : Env} (h : HasRuleAt env "Step" "%~>%" 1 readRule) {z : Value}
    {is js : List Value} (hz : TypedV env stateT z) (his : TypedV env instrsT (.list is))
    (hjs : TypedV env instrsT (.list js)) (hp : SReadB env (cfgV z is) js) :
    SStepB env (cfgV z is) (cfgV z js) := by
  let ρ := VarEnv.empty.bindVals [("z", z), ("instr*", .list is), ("instr'*", .list js)]
  have hρ : ValsOnly ρ := ⟨rfl, rfl, rfl⟩
  have fz : ρ.findVal? "z" = some z := rfl
  have fi : ρ.findVal? "instr*" = some (.list is) := rfl
  have fj : ρ.findVal? "instr'*" = some (.list js) := rfl
  have hq : QuantsOk env ρ [.expP "z" stateT, .expP "instr*" instrsT, .expP "instr'*" instrsT] :=
    QuantsOk.cons fz (hz ρ hρ)
      (QuantsOk.cons fi (his ρ hρ) (QuantsOk.cons fj (hjs ρ hρ) QuantsOk.nil))
  have ei : EvalExp env ρ (.iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")]))
      (.list is) := evalExp_iterPat (by decide) fi
  have ej : EvalExp env ρ (.iterE (.varE "instr'") (.mk .list [.mk "instr'" (.varE "instr'*")]))
      (.list js) := evalExp_iterPat (by decide) fj
  exact dderivesB_of_ruleAt h (self_mem_conclAlts _) _ hq
    (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei))
      (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ej)))
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup2 (evalExp_case (op := "%;%") (evalExp_tup2 (evalExp_var fz) ei)) ej) hp))

/-- A `Step_read` step under the new reading gives a forward step (`RefsGC.fwd_of_sread`). -/
theorem fwd_of_sreadB {env : Env} (T : TypingFacts env hn)
    (hr : HasRuleAt env "Step" "%~>%" 1 readRule) {s : Store H} {f : Frame}
    {is is' : List Admin}
    (hp : TypedV env stateT (stateV hn s f) → TypedV env instrsT (.list (adminsToV is)) →
      SReadB env (configV hn ⟨s, f, is⟩) (adminsToV is')) :
    FwdPB env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hst, hcode⟩ := (T.config _).1 hc
  obtain ⟨-, hcode'⟩ := (T.config _).1 hc'
  exact sstepB_read hr hst hcode hcode' (hp hst hcode)

/-- `RefOkBB` at the store and instantiated type of a step from a typed state. -/
theorem refOkAtB_of {KB : RefOkBB (simEnv (BI P hn host))} {s : Store H} {f : Frame}
    (hM : ModuleBnd f.module) (hz : TypedV (simEnv (BI P hn host)) stateT (stateV hn s f))
    (rt : RefType) : RefOkAtB (simEnv (BI P hn host)) hn s (f.module.instRef rt) :=
  KB.refOk hn s _ ((Typing.typingFacts_simEnv (BI P hn host) hn).state s f |>.1 hz).1
    (Round5.Fwd.tyBnd_instRef hM rt)

/-- `RefOkBB` gives `CastRefOk` at every predicate that implies a bounded frame module. -/
theorem castRefOk_bnd {env : Env} {V : Config H → Prop} (KB : RefOkBB env)
    (hM : ∀ c, V c → ModuleBnd c.frame.module) : CastsV.CastRefOk env hn V where
  refOk s _ _ _ rt _ hv hs := KB.refOk hn s _ hs (Round5.Fwd.tyBnd_instRef (hM _ hv) rt)

/-- `RefOkBB` gives `CastRefOk` at the bounded frame modules. -/
theorem castRefOk_bndM {env : Env} (KB : RefOkBB env) :
    CastsV.CastRefOk env hn (fun c : Config H => ModuleBnd c.frame.module) :=
  castRefOk_bnd KB fun _ h => h

/-- `CastRefOk` at the store and instantiated type of a cast pair, from a typed state. -/
theorem refOkAtG {V : Config H → Prop} (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V)
    {s : Store H} {f : Frame} {r : Ref} {i : Instr} {rt : RefType}
    (hv : V ⟨s, f, [.ref r, .plain i]⟩) (hi : CastsV.castTy? i = some rt)
    (hz : TypedV (simEnv (BI P hn host)) stateT (stateV hn s f)) :
    RefOkAtB (simEnv (BI P hn host)) hn s (f.module.instRef rt) :=
  K.refOk s f r i rt hi hv ((Typing.typingFacts_simEnv (BI P hn host) hn).state s f |>.1 hz).1

/-! ## The four cast rules -/

/-- `ref.test`, both outcomes. -/
theorem fwd_refTestG {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) (s : Store H) (f : Frame) (r : Ref)
    (rt : RefType) (hv : V ⟨s, f, [.ref r, .plain (.refTest rt)]⟩) :
    (RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩
        ⟨s, f, [constI32 1]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩
        ⟨s, f, [constI32 0]⟩) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  have Q : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 1 Equiv.ExecStepRules.readRule :=
    (hasStepRules_simEnv _).read
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  refine ⟨fun hok => fwd_of_sreadB T Q fun hz hc => ?_,
    fun hok => fwd_of_sreadB T Q fun hz hc => ?_⟩
  · exact sread_refTestTrueB (hasRuleAt_simEnv _ rd.refTestTrue) T R G
      (refOkAtG K hv rfl hz) hok hz hc
  · exact sread_refTestFalseB (hasRuleAt_simEnv _ rd.refTestFalse)
      (hasRuleAt_simEnv _ rd.refTestTrue) (RefsGC.readTable_simEnv _) (noOpt_read_at _) T R G
      (refOkAtG K hv rfl hz) hok hz hc

/-- `ref.test`, both outcomes. -/
theorem fwd_refTestB (KB : RefOkBB (simEnv (BI P hn host))) (s : Store H) (f : Frame) (r : Ref)
    (rt : RefType) (hM : ModuleBnd f.module) :
    (RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩
        ⟨s, f, [constI32 1]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refTest rt)]⟩
        ⟨s, f, [constI32 0]⟩) :=
  fwd_refTestG (castRefOk_bndM KB) s f r rt hM

/-- `ref.cast`, both outcomes. -/
theorem fwd_refCastG {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) (s : Store H) (f : Frame) (r : Ref)
    (rt : RefType) (hv : V ⟨s, f, [.ref r, .plain (.refCast rt)]⟩) :
    (RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  have Q : HasRuleAt (simEnv (BI P hn host)) "Step" "%~>%" 1 Equiv.ExecStepRules.readRule :=
    (hasStepRules_simEnv _).read
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  refine ⟨fun hok => fwd_of_sreadB T Q fun hz hc => ?_,
    fun hok => fwd_of_sreadB T Q fun hz hc => ?_⟩
  · exact sread_refCastSucceedB (hasRuleAt_simEnv _ rd.refCastSucceed) T R G
      (refOkAtG K hv rfl hz) hok hz hc
  · exact sread_refCastFailB (hasRuleAt_simEnv _ rd.refCastFail)
      (hasRuleAt_simEnv _ rd.refCastSucceed) (RefsGC.readTable_simEnv _) (noOpt_read_at _) T R G
      (refOkAtG K hv rfl hz) hok hz hc

/-- `ref.cast`, both outcomes. -/
theorem fwd_refCastB (KB : RefOkBB (simEnv (BI P hn host))) (s : Store H) (f : Frame) (r : Ref)
    (rt : RefType) (hM : ModuleBnd f.module) :
    (RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩) :=
  fwd_refCastG (castRefOk_bndM KB) s f r rt hM

/-- `br_on_cast`, both outcomes. -/
theorem fwd_brOnCastG {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) (s : Store H) (f : Frame) (r : Ref)
    (l : LabelIdx) (rt₁ rt₂ : RefType) (hv : V ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩) :
    (RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r]⟩) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  refine ⟨fun hok => fwd_of_sreadB T (hasStepRules_simEnv _).read fun hz hc => ?_,
    fun hok => fwd_of_sreadB T (hasStepRules_simEnv _).read fun hz hc => ?_⟩
  · exact sread_brOnCastSucceedB (hasRuleAt_simEnv _ rd.brOnCastSucceed) T R G
      (refOkAtG K hv rfl hz) hok hz hc
  · exact sread_brOnCastFailB (hasRuleAt_simEnv _ rd.brOnCastFail)
      (hasRuleAt_simEnv _ rd.brOnCastSucceed) (RefsGC.readTable_simEnv _) (noOpt_read_at _) T R G
      (refOkAtG K hv rfl hz) hok hz hc

/-- `br_on_cast`, both outcomes. -/
theorem fwd_brOnCastB (KB : RefOkBB (simEnv (BI P hn host))) (s : Store H) (f : Frame) (r : Ref)
    (l : LabelIdx) (rt₁ rt₂ : RefType) (hM : ModuleBnd f.module) :
    (RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r]⟩) :=
  fwd_brOnCastG (castRefOk_bndM KB) s f r l rt₁ rt₂ hM

/-- `br_on_cast_fail`, both outcomes. -/
theorem fwd_brOnCastFailG {V : Config H → Prop}
    (K : CastsV.CastRefOk (simEnv (BI P hn host)) hn V) (s : Store H) (f : Frame)
    (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType)
    (hv : V ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩) :
    (RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) := by
  have T : TypingFacts (simEnv (BI P hn host)) hn := Typing.typingFacts_simEnv _ hn
  have R : RefsGC.RTyping (simEnv (BI P hn host)) := Typing.rTyping_simEnv _
  have G : RefsGC.RStoreFuns (simEnv (BI P hn host)) := Round5.Fwd.rStore_builtins hn host
  have rd : Equiv.ExecRead.HasReadRules (envOfScript Specs.wasm30) :=
    Equiv.ExecRead.hasReadRules_wasm30
  refine ⟨fun hok => fwd_of_sreadB T (hasStepRules_simEnv _).read fun hz hc => ?_,
    fun hok => fwd_of_sreadB T (hasStepRules_simEnv _).read fun hz hc => ?_⟩
  · exact sread_brOnCastFailSucceedB (hasRuleAt_simEnv _ rd.brOnCastFailSucceed) T R G
      (refOkAtG K hv rfl hz) hok hz hc
  · exact sread_brOnCastFailFailB (hasRuleAt_simEnv _ rd.brOnCastFailFail)
      (hasRuleAt_simEnv _ rd.brOnCastFailSucceed) (RefsGC.readTable_simEnv _) (noOpt_read_at _) T R G
      (refOkAtG K hv rfl hz) hok hz hc

/-- `br_on_cast_fail`, both outcomes. -/
theorem fwd_brOnCastFailB (KB : RefOkBB (simEnv (BI P hn host))) (s : Store H) (f : Frame)
    (r : Ref) (l : LabelIdx) (rt₁ rt₂ : RefType) (hM : ModuleBnd f.module) :
    (RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r]⟩) ∧
    (¬ RefOk s r (f.module.instRef rt₂) →
      FwdPB (simEnv (BI P hn host)) hn ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩) :=
  fwd_brOnCastFailG (castRefOk_bndM KB) s f r l rt₁ rt₂ hM

/-- **The cast rules, forward, under the new reading, from `RefOkBB`.** -/
theorem castsFwdB_of (KB : RefOkBB (simEnv (BI P hn host))) : CastsFwdB (BI P hn host) hn where
  refTest s f r rt hb := fwd_refTestB KB s f r rt hb.frame
  refCast s f r rt hb := fwd_refCastB KB s f r rt hb.frame
  brOnCast s f r l rt₁ rt₂ hb := fwd_brOnCastB KB s f r l rt₁ rt₂ hb.frame
  brOnCastFail s f r l rt₁ rt₂ hb := fwd_brOnCastFailB KB s f r l rt₁ rt₂ hb.frame

end Silmaril.Wasm.SpecTec.Sim.Round6.Reading
