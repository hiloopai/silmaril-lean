module

public import Silmaril.Proofs.Wasm.Models.FXTRun.Heads

/-!
# The `StepFXT` interpreter is sound

* `callIntr_sound`, `callFx_sound`, `callTo_sound`, `callHead_sound`: a call of an intrinsic is a
  `StepFXT.intr` step, a call of an FX function an `invoke` step; `coreHead_sound`: also
  `ref.func x` (a Core step) and `drop` of a continuation; `blockHead_sound`, `loopHead_sound`,
  `ifHead_sound`, `contNewHead_sound`, `resumeHead_sound`, `fxHead_sound`;
* **`head_sound`**: every head step is a `StepFXT` step on `vs; e`;
* **`tstep_sound`**: every step computed by `tstep` is a `StepFXT` step (store and frame
  unchanged); `stepC_sound`, **`runT_sound`**: a computed run is a `StepsT` run;
* **`checkT_mem`**: if the computed run ends with empty code and log `log`, then
  `ObsT.ret log (returns [])` is a `StepFXT` behaviour, at every profile and host.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXTRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXT Silmaril.Wasm.Models.FXTRun
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}
  {intr : H → Option Intr} {s : Store H}

variable {f : Frame} {K K' : List (Option ContFX)} {t t' : Tbl} {vs u : List FVal}
  {r : List AdminFX}

/-! ## Calls -/

/-- **A call of an intrinsic is a step.** -/
theorem callIntr_sound {a : Nat} {fi : FuncInst H} {h₀ : H} {op : Intr} {cc : Admin}
    (hc : cc.IsCallRef) (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .host h₀)
    (hop : intr h₀ = some op) (h : callIntr op K t vs = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.core (.ref (.func a)), .core cc]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold callIntr at h
  split at h
  · rename_i u₁ args hse
    split at h
    · rename_i res t₁ hrun
      cases h
      have st := StepFXT.intr (P := P) (host := host) (fx := fx) (s := s) (K := K) (f := f)
        (E := .seq u .hole []) hc hfi hcode hop hrun
      refine T_conv st ?_ (by simp [CtxV.plug])
      rw [(splitEnd_eq hse).1]
      simp [CtxV.plug]
    · cases h
  · cases h

/-- **A call of an FX function is a step** (`invoke`). -/
theorem callFx_sound {a : Nat} {fi : FuncInst H} {h₀ : H} {F : FuncFX} {cc : Admin}
    (hc : cc.IsCallRef) (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .host h₀)
    (hF : fx h₀ = some F) (h : callFx F K t vs = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.core (.ref (.func a)), .core cc]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold callFx at h
  split at h
  · rename_i u₁ args hse
    obtain ⟨hu, hn⟩ := splitEnd_eq hse
    split at h
    · rename_i cs hcs
      cases h
      have ha : args = liftV cs := coreVals_eq hcs
      have hn' : cs.length = F.nparams := by rw [← hn, ha]; simp [liftV]
      have st : StepFXT P host fx intr
          ⟨⟨s, K, f, cvals cs ++ [.core (.ref (.func a)), .core cc]⟩, t⟩
          ⟨⟨s, K, f, [.frame F.nresults (Frame.forCall F.module cs F.locals)
            [.label F.nresults [] (F.body.map InstrFX.toAdmin)]]⟩, t⟩ :=
        .lift (.invoke hc hfi hcode hF hn')
      refine T_conv (T_pre u st) ?_ rfl
      rw [hu, ha, cvals_liftV]
      simp
    · cases h
  · cases h

/-- **A call of the function at address `a` is a step.** -/
theorem callTo_sound {a : Nat} {cc : Admin} (hc : cc.IsCallRef)
    (h : callTo s fx intr K t vs a = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.core (.ref (.func a)), .core cc]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold callTo at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i h₀ hcode
      split at h
      · rename_i op hop
        exact callIntr_sound hc hfi hcode hop h
      · split at h
        · rename_i F hF
          exact callFx_sound hc hfi hcode hF h
        · cases h
    · cases h
  · cases h

/-- **A call is a step.** -/
theorem callHead_sound {cc : Admin} (hc : cc.IsCallRef)
    (h : callHead s fx intr K t vs = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.core cc]⟩, t⟩ ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold callHead at h
  split at h
  · rename_i u₀ a hl
    refine T_conv (callTo_sound hc h) ?_ rfl
    rw [lastFunc_eq hl]
    simp [fvals, FVal.toAdmin, Val.toAdmin]
  · cases h

/-! ## Core instructions -/

theorem refFuncHead_sound {x : FuncIdx} (h : refFuncHead f K t vs x = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.core (.plain (.refFunc x))]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold refFuncHead at h
  split at h
  · rename_i b hx
    cases h
    have st : StepFXT P host fx intr ⟨⟨s, K, f, [.core (.plain (.refFunc x))]⟩, t⟩
        ⟨⟨s, K, f, [.core (.ref (.func b))]⟩, t⟩ :=
      .lift (.core (cs := [.plain (.refFunc x)]) (cs' := [.ref (.func b)])
        (Step.reference (.refFunc hx)))
    exact T_pre vs st
  · cases h

theorem dropHead_sound (h : dropHead K t vs = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.core (.plain .drop)]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold dropHead at h
  split at h
  · rename_i u₀ k hl
    cases h
    have st : StepFXT P host fx intr ⟨⟨s, K, f, [.contRef k, .core (.plain .drop)]⟩, t⟩
        ⟨⟨s, K, f, []⟩, t⟩ := .lift .dropCont
    refine T_conv (T_pre u st) ?_ rfl
    rw [lastCont_eq hl]
    simp [fvals, FVal.toAdmin]
  · cases h

/-- **A Core head is a step.** -/
theorem coreHead_sound {a : Admin} (h : coreHead s fx intr f K t vs a = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.core a]⟩, t⟩ ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold coreHead at h
  split at h
  · exact refFuncHead_sound h
  · exact dropHead_sound h
  · exact callHead_sound trivial h
  · exact callHead_sound trivial h
  · cases h

/-! ## Structured control and stack switching -/

theorem blockHead_sound {bt : BlockType} {body : List InstrFX}
    (h : blockHead f K t vs bt body = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.block bt body]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold blockHead at h
  split at h
  · rename_i t₂ hbt
    cases h
    exact T_pre vs (.lift (.block (vs := []) hbt rfl))
  · cases h

theorem loopHead_sound {bt : BlockType} {body : List InstrFX}
    (h : loopHead f K t vs bt body = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.loop bt body]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold loopHead at h
  split at h
  · rename_i t₂ hbt
    cases h
    exact T_pre vs (.lift (.loop (vs := []) hbt rfl))
  · cases h

theorem ifHead_sound {bt : BlockType} {b₁ b₂ : List InstrFX}
    (h : ifHead K t vs bt b₁ b₂ = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.if_ bt b₁ b₂]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold ifHead at h
  split at h
  · rename_i u₀ c hl
    cases h
    have hvs : fvals vs ++ [.if_ bt b₁ b₂] = fvals u ++ [.core (constI32 c), .if_ bt b₁ b₂] := by
      rw [lastI32_eq hl]
      simp [fvals, FVal.toAdmin, Val.toAdmin, constI32, Val.i32]
    rw [hvs]
    split
    · rename_i h0
      subst h0
      exact T_pre u (.lift .ifFalse)
    · exact T_pre u (.lift (.ifTrue (by assumption)))
  · cases h

theorem contNewHead_sound {ct : TypeIdx} (h : contNewHead s K t vs = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.fx (.contNew ct)]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold contNewHead at h
  split at h
  · rename_i u₀ a hl
    split at h
    · rename_i fi hfi
      cases h
      have st : StepFXT P host fx intr
          ⟨⟨s, K, f, [.core (.ref (.func a)), .fx (.contNew ct)]⟩, t⟩
          ⟨⟨s, K ++ [some (newC a fi)], f, [.contRef K.length]⟩, t⟩ := .lift (.contNew hfi)
      refine T_conv (T_pre u st) ?_ rfl
      rw [lastFunc_eq hl]
      simp [fvals, FVal.toAdmin, Val.toAdmin]
    · cases h
  · cases h

theorem resumeHead_sound {ct : TypeIdx} {hs : List OnClause}
    (h : resumeHead s f K t vs hs = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.fx (.resume ct hs)]⟩, t⟩
      ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold resumeHead at h
  split at h
  · rename_i u₀ k hl
    split at h
    · rename_i C hC
      split at h
      · rename_i hs' hr
        cases h
        have st : StepFXT P host fx intr
            ⟨⟨s, K, f, fvals [] ++ [.contRef k, .fx (.resume ct hs)]⟩, t⟩
            ⟨⟨s, K.set k none, f, [.handler hs' (C.plug (fvals []))]⟩, t⟩ := .lift (.resume hC hr)
        refine T_conv (T_pre u st) ?_ rfl
        rw [lastCont_eq hl]
        simp [fvals, FVal.toAdmin]
      · cases h
    · cases h
  · cases h

theorem fxHead_sound {i : FXInstr} (h : fxHead s f K t vs i = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [.fx i]⟩, t⟩ ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold fxHead at h
  split at h
  · exact contNewHead_sound h
  · exact resumeHead_sound h
  · cases h

/-- A head step under a wrapper (label, frame, handler) keeps the values below it. -/
theorem wrapHead_sound {e : AdminFX} {g : ERes → HRes} (hg : ∀ x, g x = (x.1, x.2.1, vs, x.2.2))
    {o : Option ERes} (h : o.map g = some (K', t', u, r))
    (hs : ∀ K₁ t₁ b, o = some (K₁, t₁, b) →
      StepFXT P host fx intr ⟨⟨s, K, f, [e]⟩, t⟩ ⟨⟨s, K₁, f, b⟩, t₁⟩) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [e]⟩, t⟩ ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  obtain ⟨⟨K₁, t₁, b⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
  rw [hg] at h2
  cases h2
  exact T_pre vs (hs K₁ t₁ b h1)

/-- **A head step is a step** on `vs; e`. -/
theorem head_sound {tar : Nat → Nat} {rec : Stepper} (hrec : Sound P host fx intr s rec)
    {d : Nat} {e : AdminFX} (h : head tar s fx intr rec d f K t vs e = some (K', t', u, r)) :
    StepFXT P host fx intr ⟨⟨s, K, f, fvals vs ++ [e]⟩, t⟩ ⟨⟨s, K', f, fvals u ++ r⟩, t'⟩ := by
  unfold head at h
  split at h
  · exact blockHead_sound h
  · exact loopHead_sound h
  · exact ifHead_sound h
  · exact wrapHead_sound (fun _ => rfl) h fun _ _ _ h1 => labelHead_sound hrec h1
  · exact wrapHead_sound (fun _ => rfl) h fun _ _ _ h1 => frameHead_sound hrec h1
  · exact wrapHead_sound (fun _ => rfl) h fun _ _ _ h1 => handlerHead_sound hrec h1
  · exact fxHead_sound h
  · exact coreHead_sound h
  · cases h

/-- **Every computed step is a `StepFXT` step.** -/
theorem tstep_sound {tar : Nat → Nat} :
    ∀ d : Nat, Sound P host fx intr s (tstep tar s fx intr d)
  | 0 => fun _ _ _ _ _ _ _ h => absurd h (by simp [tstep])
  | d + 1 => by
    intro f K t code K' t' c' h
    unfold tstep at h
    split at h
    · exact absurd h (by simp)
    · rename_i vs e rest hsp
      obtain ⟨⟨K₁, t₁, u, r⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl, rfl⟩ := h2
      have st := head_sound (tstep_sound d) h1
      refine T_conv (T_seq [] rest st) ?_ ?_
      · rw [splitV_eq hsp]
        simp
      · simp

/-- A computed configuration step is a `StepFXT` step. -/
theorem stepC_sound {tar : Nat → Nat} {d : Nat} {c c' : ConfigT H}
    (h : stepC tar fx intr d c = some c') : StepFXT P host fx intr c c' := by
  unfold stepC at h
  obtain ⟨⟨K', t', code'⟩, h1, rfl⟩ := Option.map_eq_some_iff.mp h
  exact tstep_sound d c.cfg.frame c.cfg.conts c.tbl c.cfg.code K' t' code' h1

/-- **A computed run is a `StepFXT` run.** -/
theorem runT_sound {tar : Nat → Nat} {d : Nat} :
    ∀ (n : Nat) (c : ConfigT H), StepsT P host fx intr c (runT tar fx intr d n c)
  | 0, _ => .refl
  | n + 1, c => by
    unfold runT
    split
    · rename_i c' hc
      exact Relation.ReflTransGen.head (stepC_sound hc) (runT_sound n c')
    · exact .refl

/-- **A checked run gives a behaviour**: ending with empty code and the log `log`. -/
theorem checkT_mem {tar : Nat → Nat} {d n : Nat} {c : ConfigT H} {log : List Val}
    (h : checkT tar fx intr d n c log = true) :
    ObsT.ret log (.returns []) ∈ behavioursT P host fx intr c := by
  unfold checkT at h
  simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at h
  obtain ⟨hcode, hlog⟩ := h
  refine Or.inl ⟨runT tar fx intr d n c, .values [], runT_sound n c, ?_, ?_⟩
  · rw [hcode]
    rfl
  · rw [hlog]
    rfl

end Silmaril.Proofs.Wasm.Models.FXTRun
