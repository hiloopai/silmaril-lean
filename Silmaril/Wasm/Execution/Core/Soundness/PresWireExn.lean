module

public import Silmaril.Wasm.Execution.Core.Soundness.PresBasic
public import Silmaril.Wasm.Execution.Core.Soundness.PresExn
public import Silmaril.Wasm.Execution.Core.Soundness.AggregatePres

@[expose] public section

/-! # Preservation: wiring the exception and trap rules

`pres_<ctor>` for the `throw`, `throw_ref-*` and `trap-*` constructors of `Step`,
in the shape of the generalised preservation lemma (`PresConcl`).

`pres_throwRefInstrs` and `pres_trapInstrs` live in `Soundness/PresDivergent.lean`: they
rely on the divergent-inits typing deviation (`AdminOk.trap` with arbitrary initialised
locals, `AdminOk.throwRefInits`; see `Typing/Config.lean`).
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Helpers -/

theorem Expand.detWire {d : DefType} {c₁ c₂ : CCompType} (h₁ : Expand d c₁) (h₂ : Expand d c₂) :
    c₁ = c₂ := by
  rw [Expand.iff] at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- The tag type in a frame context is the type of the tag instance `s.tag?` finds. -/
theorem FrameOk.tag_typeWire {s : Store H} {f : Frame} {C : Context} (hs : StoreOk s)
    (hf : FrameOk s f C) {x : TagIdx} {d : DefType} {ta : Nat} {ti : TagInst}
    (hx : C.tags[x.toNat]? = some d) (ht : s.tag? f x = some (ta, ti)) :
    ti.type = d ∧ s.tags[ta]? = some ti := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ htags =>
    obtain ⟨a, ha, hxa⟩ := forall₂_getElem?_right htags hx
    obtain ⟨ti', hti, hte⟩ := ExternAddrOk.tag_inv hs hxa
    cases hte
    simp [Store.tag?, ha, hti] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨rfl, hti⟩

theorem CtxUnder.tagsWire {Ct Cf : Context} (hu : CtxUnder Ct Cf) : Ct.tags = Cf.tags := by
  rw [hu.eq]

/-- Results of a typed sequence are valid (full regularity). -/
theorem AdminsOk.results_wire {s : Store H} {C : Context} {as : List Admin} {it : InstrType}
    (hs : StoreOk s) (hts : StoreTypesOk s) (hC : C.Wf) (h : AdminsOk s C as it) :
    ResultOk C.toTypeCtx it.results :=
  (AdminsOk.regular hs hts hC h).2.1

/-! ## Exception rules -/

theorem pres_throw {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat}
    {ti : TagInst} {ts : Ty (.list .val)} (ht : s.tag? f x = some (ta, ti))
    (he : Expand ti.type (.func ts .nil)) (hn : vs.length = ts.length) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct (vals vs ++ [.plain (.throw x)]) it →
      PresConcl ⟨s, f, vals vs ++ [.plain (.throw x)]⟩
        ⟨s.addExn ⟨ta, vs⟩, f, throwing s.exns.length⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  have hn' : vs.length = ts.toList.length := hn
  -- The tag's parameter types, as seen from the typing context.
  have hparams : ∀ {d : DefType} {ts' : Ty (.list .val)}, Ct.tags[x.toNat]? = some d →
      Expand d (.func ts' .nil) → ts' = ts ∧ s.tags[ta]? = some ti := by
    intro d ts' hx he'
    rw [hu.tagsWire] at hx
    obtain ⟨rfl, hti⟩ := FrameOk.tag_typeWire hs hf hx ht
    have := Expand.detWire he he'
    cases this
    exact ⟨rfl, hti⟩
  have hI : ∀ it', AdminOk s Ct (.plain (.throw x)) it' →
      it'.inits = [] ∧ vs.length ≤ it'.params.length := by
    intro it' h'
    cases h' with
    | plain h' =>
      cases h' with
      | throw hx he' hok =>
        obtain ⟨e, -⟩ := hparams hx he'
        rw [e]
        refine ⟨rfl, ?_⟩
        simp only [List.length_append]
        omega
      | _ => rename_i hh; cases hh
  obtain ⟨A, B, t₂, tsv, hi, hvs, hB, -⟩ := redex_inv_gen hI hty
  obtain ⟨hB', hti⟩ : B = ts.toList ∧ s.tags[ta]? = some ti := by
    cases hi with
    | plain h' =>
      generalize hP : (⟨A ++ B, [], t₂⟩ : InstrType) = P at h'
      cases h' with
      | throw hx he' hok =>
        obtain ⟨e, hti⟩ := hparams hx he'
        rw [e] at hP
        have hl : B.length = ts.toList.length := by
          rw [← hB.length_eq, ← hvs.length_eq, hn']
        injection hP with hP
        exact ⟨(List.append_inj' hP hl).2, hti⟩
      | _ => rename_i hh; cases hh
  subst hB'
  -- The tag's parameters are valid in `{}`.
  have hty0 : TyOk {} ti.type := (hs.tags ti (List.mem_of_getElem? hti)).1
  have hok := (Expand.func_ok hty0 he).1
  have hst : StateOk s f Cf := ⟨hs, hf⟩
  rw [hu.toTypeCtx] at hB
  have hv : List.Forall₂ (ValOk s) vs ts.toList := by
    clear hi hI hty hn hn'
    generalize ts.toList = L at hB hok
    induction hvs generalizing L with
    | nil => cases hB; exact .nil
    | cons hv _ ih =>
      cases hB with
      | cons hs₁ hs₂ =>
        exact .cons (ValOk.ctxSubAgg hst hts hv hs₁ (hok _ (by simp)))
          (ih _ hs₂ fun t ht' => hok t (List.mem_cons_of_mem _ ht'))
  obtain ⟨hs', hext⟩ := StoreOk.throwExn hs ht he hv
  exact ⟨Cf, Ct, hs', hext, hf.extend_of_storeOk hs hext, rfl, hu, CtxLe.refl _,
    AdminsOk.pres_throwExn hty hwf⟩

theorem pres_throwRefNull {s : Store H} {f : Frame} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.ref .null, .plain .throwRef] it →
      PresConcl ⟨s, f, [.ref .null, .plain .throwRef]⟩ ⟨s, f, [.trap]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (AdminsOk.pres_throwRefNullExn hty hwf)

theorem pres_throwRefLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.label n cont (throwing a)] it →
      PresConcl ⟨s, f, [.label n cont (throwing a)]⟩ ⟨s, f, throwing a⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (AdminsOk.pres_throwRefLabelExn hty hwf)

theorem pres_throwRefFrame {s : Store H} {f fi : Frame} {n : Nat} {a : Nat} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.frame n fi (throwing a)] it →
      PresConcl ⟨s, f, [.frame n fi (throwing a)]⟩ ⟨s, f, throwing a⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  exact PresConcl.same hs hf hu
    (AdminsOk.pres_throwRefFrameExn hty hwf (hty.results_wire hs hts hwf))

theorem pres_throwRefHandlerEmpty {s : Store H} {f : Frame} {n : Nat} {a : Nat} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.handler n [] (throwing a)] it →
      PresConcl ⟨s, f, [.handler n [] (throwing a)]⟩ ⟨s, f, throwing a⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (AdminsOk.pres_throwRefHandlerEmptyExn hty hwf)

theorem pres_throwRefHandlerNext {s : Store H} {f : Frame} {n : Nat} {c : Catch}
    {cs : List Catch} {a : Nat} (_h : ¬ CatchMatches s f a c) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.handler n (c :: cs) (throwing a)] it →
      PresConcl ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩
        ⟨s, f, [.handler n cs (throwing a)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu _ _ hty
  exact PresConcl.same hs hf hu (AdminsOk.pres_throwRefHandlerNextExn hty)

/-! ## Trap rules -/

theorem pres_trapLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.label n cont [.trap]] it →
      PresConcl ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (AdminsOk.pres_trapLabelExn hty hwf)

theorem pres_trapHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.handler n cs [.trap]] it →
      PresConcl ⟨s, f, [.handler n cs [.trap]]⟩ ⟨s, f, [.trap]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (AdminsOk.pres_trapHandlerExn hty hwf)

theorem pres_trapFrame {s : Store H} {f fi : Frame} {n : Nat} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s → AdminsOk s Ct [.frame n fi [.trap]] it →
      PresConcl ⟨s, f, [.frame n fi [.trap]]⟩ ⟨s, f, [.trap]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf hts hty
  exact PresConcl.same hs hf hu
    (AdminsOk.pres_trapFrameExn hty hwf (hty.results_wire hs hts hwf))

end Silmaril.Wasm.Execution.Core
