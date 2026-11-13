module

public import Silmaril.Proofs.Wasm.Models.FXPresI.ProgFX

/-!
# Progress for `envP`: labels, frames and handler frames

A label, frame or handler frame steps inside, or its body halts; each halting body either makes
the construct step (`label-vals`, `br`, `return`, `trap`, exceptions, a handled `suspend`) or
halts with the construct in the context.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {s : Store H} {Γ : List TypeIdx}
  {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX} {K : List (Option ContFX)}

/-- Typed values from the empty stack. -/
theorem vals_ty {Ls : List (List FTy)} {R : Option (List FTy)} {ws : List FVal} {o : List FTy}
    (h : TL (envP m₀) s Γ Ls R (fvals ws) [] o) : ValsTy (envP m₀) s Γ ws o := by
  obtain ⟨T, rfl, hT⟩ := TL.vals_inv (E := envP m₀) (fun h => ctI_val h) h
  simpa using hT

/-- A typed `br l` after values: the label exists and the values end with its types. -/
theorem br_inv {Ls : List (List FTy)} {R : Option (List FTy)} {ws : List FVal} {l : LabelIdx}
    {rest : List AdminFX} {o : List FTy}
    (h : TL (envP m₀) s Γ Ls R (fvals ws ++ [.core (.plain (.br l))] ++ rest) [] o) :
    ∃ ts ws₁ ws₂, Ls[l.toNat]? = some ts ∧ ws = ws₁ ++ ws₂ ∧ ws₂.length = ts.length := by
  obtain ⟨m₁, m₂, hv, hb, -⟩ := TL.split3 h
  have hT := vals_ty hv
  cases hb with
  | br hl _ =>
    obtain ⟨ws₁, ws₂, rfl, -, h₂⟩ := valsTy_split hT
    exact ⟨_, ws₁, ws₂, hl, rfl, valsTy_length h₂⟩
  | core _ hn _ => exact (hn trivial).elim

/-- A typed `return` after values: the return type exists and the values end with it. -/
theorem ret_inv {Ls : List (List FTy)} {R : Option (List FTy)} {ws : List FVal}
    {rest : List AdminFX} {o : List FTy}
    (h : TL (envP m₀) s Γ Ls R (fvals ws ++ [.core (.plain .return_)] ++ rest) [] o) :
    ∃ ts ws₁ ws₂, R = some ts ∧ ws = ws₁ ++ ws₂ ∧ ws₂.length = ts.length := by
  obtain ⟨m₁, m₂, hv, hb, -⟩ := TL.split3 h
  have hT := vals_ty hv
  cases hb with
  | ret hR _ =>
    obtain ⟨ws₁, ws₂, rfl, -, h₂⟩ := valsTy_split hT
    exact ⟨_, ws₁, ws₂, hR, rfl, valsTy_length h₂⟩
  | core _ hn _ => exact (hn trivial).elim

/-- `br` out of a label. -/
theorem step_label_br {f : Frame} {n : Nat} {k : List InstrFX} {tl : List FTy}
    {Ls : List (List FTy)} {ws : List FVal} {l : LabelIdx} {rest : List AdminFX}
    (hn : n = tl.length) {R : Option (List FTy)} {te : List FTy}
    (hb : TL (envP m₀) s Γ (tl :: Ls) R (fvals ws ++ [.core (.plain (.br l))] ++ rest) [] te) :
    ∃ c', StepFXS P host fx
      ⟨s, K, f, [.label n k (fvals ws ++ [.core (.plain (.br l))] ++ rest)]⟩ c' := by
  obtain ⟨ts, ws₁, ws₂, hl, rfl, hlen⟩ := br_inv hb
  by_cases h0 : l.toNat = 0
  · rw [h0] at hl
    cases hl
    rw [fvals_append]
    exact ⟨_, .brLabelZero h0 (hlen.trans hn.symm)⟩
  · exact ⟨_, .brLabelSucc (Nat.pos_of_ne_zero h0)⟩

/-- An unhandled `suspend` under a context in front of values and before code. -/
theorem halt_susp_in {f : Frame} {X : CtxV} {vs ws : List FVal} {as : List AdminFX}
    {x : TagIdx} {ta : Nat} {ti : TagInst} (ht : s.tag? (X.frameAt f) x = some (ta, ti))
    (hE : ¬ X.Handles ta) (ha : TagArity ti ws.length) :
    Halt s K f (fvals vs ++ X.plug (fvals ws ++ [.fx (.suspend x)]) ++ as) :=
  Halt.suspend (E := .seq vs X as) ht hE ha

/-- `resume_throw` of a consumed continuation under a context. -/
theorem halt_used_in {f : Frame} {X : CtxV} {vs : List FVal} {ws : List Val}
    {as : List AdminFX} {k : Nat} {ct : TypeIdx} {x : TagIdx} {hs : List OnClause}
    (hk : K[k]? = some none) :
    Halt s K f (fvals vs ++ X.plug (cvals ws ++ [.contRef k, .fx (.resumeThrow ct x hs)]) ++ as) :=
  Halt.usedThrow (E := .seq vs X as) hk

/-- A halting body, read without the empty value prefix. -/
theorem halt_body {f : Frame} {body : List AdminFX} (h : Halt s K f (fvals [] ++ body)) :
    Halt s K f body := by
  simpa [fvals] using h

/-- **A label.** -/
theorem pg_label {n : Nat} {k : List InstrFX} {body : List AdminFX} {tl te : List FTy}
    {Ls : List (List FTy)} {R : Option (List FTy)} {as : List AdminFX} {pre : List FTy}
    (hn : n = tl.length) (hb : TL (envP m₀) s Γ (tl :: Ls) R body [] te)
    (ihb : PG P host fx m₀ s Γ K body []) :
    PG P host fx m₀ s Γ K (.label n k body :: as) pre := by
  intro f vs hf _
  have hctx : ∀ w, (∃ c', StepFXS P host fx ⟨s, K, f, [.label n k w]⟩ c') →
      Halt s K f (fvals vs ++ .label n k w :: as) ∨
        ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs ++ .label n k w :: as⟩ c' :=
    fun w h => .inr (by simpa using step_ctx vs as h)
  rcases ihb f [] hf .nil with hH | ⟨⟨s', K', f', w'⟩, hc⟩
  · show Halt s K f (fvals vs ++ .label n k body :: as) ∨ _
    have hH' : Halt s K f body := halt_body hH
    cases hH' with
    | vals ws => exact hctx _ ⟨_, .labelVals⟩
    | trap => exact hctx _ ⟨_, .trapLabel⟩
    | throw a => exact hctx _ ⟨_, .throwLabel⟩
    | br ws l rest => exact hctx _ (step_label_br hn hb)
    | ret ws rest => exact hctx _ ⟨_, .returnLabel⟩
    | suspend ht hE ha =>
      exact .inl (by simpa [CtxV.plug] using halt_susp_in (X := .label n k _) ht hE ha)
    | usedThrow hk => exact .inl (by simpa [CtxV.plug] using halt_used_in (X := .label n k _) hk)
  · exact hctx _ ⟨_, .ctxLabel (by simpa [fvals] using hc)⟩

/-- `return` out of a frame. -/
theorem step_frame_ret {f fi : Frame} {n : Nat} {ts : List FTy} {ws : List FVal}
    {rest : List AdminFX} (hn : n = ts.length)
    (hb : TL (envP m₀) s Γ [] (some ts) (fvals ws ++ [.core (.plain .return_)] ++ rest) [] ts) :
    ∃ c', StepFXS P host fx
      ⟨s, K, f, [.frame n fi (fvals ws ++ [.core (.plain .return_)] ++ rest)]⟩ c' := by
  obtain ⟨ts', ws₁, ws₂, hR, rfl, hlen⟩ := ret_inv hb
  cases hR
  rw [fvals_append]
  exact ⟨_, .returnFrame (hlen.trans hn.symm)⟩

/-- **A frame.** -/
theorem pg_frame {n : Nat} {fi : Frame} {body : List AdminFX} {ts : List FTy}
    {as : List AdminFX} {pre : List FTy} (hm : fi.module = m₀) (hn : n = ts.length)
    (hb : TL (envP m₀) s Γ [] (some ts) body [] ts) (ihb : PG P host fx m₀ s Γ K body []) :
    PG P host fx m₀ s Γ K (.frame n fi body :: as) pre := by
  intro f vs _ _
  have hctx : ∀ w, (∃ c', StepFXS P host fx ⟨s, K, f, [.frame n fi w]⟩ c') →
      Halt s K f (fvals vs ++ .frame n fi w :: as) ∨
        ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs ++ .frame n fi w :: as⟩ c' :=
    fun w h => .inr (by simpa using step_ctx vs as h)
  rcases ihb fi [] hm .nil with hH | ⟨⟨s', K', f', w'⟩, hc⟩
  · show Halt s K f (fvals vs ++ .frame n fi body :: as) ∨ _
    have hH' : Halt s K fi body := halt_body hH
    cases hH' with
    | vals ws => exact hctx _ ⟨_, .frameVals ((valsTy_length (vals_ty hb)).trans hn.symm)⟩
    | trap => exact hctx _ ⟨_, .trapFrame⟩
    | throw a => exact hctx _ ⟨_, .throwFrame⟩
    | br ws l rest => exact absurd (br_inv hb) (by simp)
    | ret ws rest => exact hctx _ (step_frame_ret hn hb)
    | suspend ht hE ha =>
      exact .inl (by simpa [CtxV.plug] using halt_susp_in (X := .frame n fi _) ht hE ha)
    | usedThrow hk => exact .inl (by simpa [CtxV.plug] using halt_used_in (X := .frame n fi _) hk)
  · exact hctx _ ⟨_, .ctxFrame (by simpa [fvals] using hc)⟩

/-- A `suspend` reaching a handler frame: handled, or past it. -/
theorem handler_suspend {f : Frame} {hs : List HClause} {E' : CtxV} {ws : List FVal}
    {x : TagIdx} {ta : Nat} {ti : TagInst} {Ls : List (List FTy)} {ts : List FTy}
    (hh : ∀ c ∈ hs, HClauseOk (envP m₀) s Ls ts c)
    (ht : s.tag? (E'.frameAt f) x = some (ta, ti)) (hE : ¬ E'.Handles ta)
    (ha : TagArity ti ws.length) :
    (∃ c', StepFXS P host fx ⟨s, K, f, [.handler hs (E'.plug (fvals ws ++ [.fx (.suspend x)]))]⟩
      c') ∨ ¬ ∃ c ∈ hs, c.tag = ta := by
  cases hfind : hs.find? (fun c => c.tag == ta) with
  | none =>
    refine .inr fun ⟨c, hc, he⟩ => ?_
    have hn := List.find?_eq_none.1 hfind c hc
    simp [he] at hn
  | some c =>
    have hc := List.mem_of_find?_eq_some hfind
    have hct : (c.tag == ta) = true := List.find?_some (p := fun c : HClause => c.tag == ta) hfind
    cases c with
    | onLabel ta' l =>
      have he : ta' = ta := by simpa [HClause.tag] using hct
      subst he
      exact .inl ⟨_, .suspend ht hE hfind ha⟩
    | onSwitch ta' => exact (hh _ hc).elim

/-- **A handler frame.** -/
theorem pg_handler {hs : List HClause} {body : List AdminFX} {ts : List FTy}
    {Ls : List (List FTy)} {as : List AdminFX} {pre : List FTy}
    (hh : ∀ c ∈ hs, HClauseOk (envP m₀) s Ls ts c) (hb : TL (envP m₀) s Γ [] none body [] ts)
    (ihb : PG P host fx m₀ s Γ K body []) :
    PG P host fx m₀ s Γ K (.handler hs body :: as) pre := by
  intro f vs hf _
  have hctx : ∀ w, (∃ c', StepFXS P host fx ⟨s, K, f, [.handler hs w]⟩ c') →
      Halt s K f (fvals vs ++ .handler hs w :: as) ∨
        ∃ c', StepFXS P host fx ⟨s, K, f, fvals vs ++ .handler hs w :: as⟩ c' :=
    fun w h => .inr (by simpa using step_ctx vs as h)
  rcases ihb f [] hf .nil with hH | ⟨⟨s', K', f', w'⟩, hc⟩
  · show Halt s K f (fvals vs ++ .handler hs body :: as) ∨ _
    have hH' : Halt s K f body := halt_body hH
    cases hH' with
    | vals ws => exact hctx _ ⟨_, .handlerVals⟩
    | trap => exact hctx _ ⟨_, .trapHandler⟩
    | throw a => exact hctx _ ⟨_, .throwHandler⟩
    | br ws l rest => exact absurd (br_inv hb) (by simp)
    | ret ws rest => exact absurd (ret_inv hb) (by simp)
    | suspend ht hE ha =>
      rcases handler_suspend (P := P) (host := host) (fx := fx) (K := K) hh ht hE ha with
        hst | hno
      · exact hctx _ hst
      · have hE₂ : ¬ (CtxV.handler hs _).Handles _ := fun h => h.elim hno hE
        exact .inl (by simpa [CtxV.plug] using halt_susp_in (X := .handler hs _) ht hE₂ ha)
    | usedThrow hk =>
      exact .inl (by simpa [CtxV.plug] using halt_used_in (X := .handler hs _) hk)
  · exact hctx _ ⟨_, .ctxHandler (by simpa [fvals] using hc)⟩

end Silmaril.Proofs.Wasm.Models.FXPresI
