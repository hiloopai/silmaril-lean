module

public import Silmaril.Wasm.Execution.Core.Soundness.PresBasic
public import Silmaril.Wasm.Execution.Core.Soundness.PresExn

@[expose] public section

/-! # Preservation wiring for the `throw_ref-handler-catch*` rules

`PresConcl`-level preservation for the four catching `throw_ref-handler-*` rules,
wrapping the `AdminsOk`-level lemmas of `PresExn.lean` with `PresConcl.same`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

theorem forall₂_getElem?_rightWC {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {i : Nat} {b : β}, List.Forall₂ R l₁ l₂ → l₂[i]? = some b →
      ∃ a, l₁[i]? = some a ∧ R a b
  | _, _, _, _, .nil, h => by simp at h
  | _, _, 0, _, .cons hab _, h => by simp at h; subst h; exact ⟨_, rfl, hab⟩
  | _, _, i + 1, _, .cons _ ht, h => by simpa using forall₂_getElem?_rightWC ht (by simpa using h)

/-- The fields of a caught exception are typed at the parameters of the tag the
catch clause names (in any typing context under the frame context). -/
theorem exn_fields_ok_of_frame {s : Store H} {f : Frame} {Cf Ct : Context} {x : TagIdx}
    {a : Nat} {e : ExnInst} (hs : StoreOk s) (hf : FrameOk s f Cf) (hu : CtxUnder Ct Cf)
    (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
    ∀ d ts, Ct.tags[x.toNat]? = some d → Expand d (.func ts .nil) →
      List.Forall₂ (ValOk s) e.fields ts.toList := by
  intro d ts hd hexp
  have htags : Ct.tags = Cf.tags := by rw [hu.eq]
  rw [htags] at hd
  obtain ⟨C₀, lts, hm, -, rfl⟩ := hf
  cases hm with
  | mk _ htg =>
    obtain ⟨ti', ts', hti', hexp', hfs⟩ := hs.exns e (List.mem_of_getElem? he)
    obtain ⟨ta, hta, hok⟩ := forall₂_getElem?_rightWC htg hd
    rw [ht] at hta
    cases hta
    obtain ⟨ti, h, hte⟩ := ExternAddrOk.tag_inv hs hok
    cases hte
    rw [h] at hti'
    cases hti'
    cases Expand.func_eq hexp hexp'
    exact hfs

theorem pres_throwRefHandlerCatch {s : Store H}
    {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch} {a : Nat} {e : ExnInst}
    (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.handler n (.catch_ x l :: cs) (throwing a)] it →
      PresConcl ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩
        ⟨s, f, vals e.fields ++ [.plain (.br l)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu
    (hty.pres_throwRefHandlerCatchExn hwf (exn_fields_ok_of_frame hs hf hu he ht))

theorem pres_throwRefHandlerCatchRef {s : Store H}
    {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch} {a : Nat} {e : ExnInst}
    (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.handler n (.catchRef x l :: cs) (throwing a)] it →
      PresConcl ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
        ⟨s, f, vals e.fields ++ [.ref (.exn a), .plain (.br l)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu
    (hty.pres_throwRefHandlerCatchRefExn hwf he (exn_fields_ok_of_frame hs hf hu he ht))

theorem pres_throwRefHandlerCatchAll {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx}
    {cs : List Catch} {a : Nat} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.handler n (.catchAll l :: cs) (throwing a)] it →
      PresConcl ⟨s, f, [.handler n (.catchAll l :: cs) (throwing a)]⟩
        ⟨s, f, [.plain (.br l)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (hty.pres_throwRefHandlerCatchAllExn hwf)

theorem pres_throwRefHandlerCatchAllRef {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx}
    {cs : List Catch} {a : Nat} :
    ∀ {Cf Ct : Context} {it : InstrType}, StoreOk s → FrameOk s f Cf → CtxUnder Ct Cf →
      CtxWf Ct → StoreTypesOk s →
      AdminsOk s Ct [.handler n (.catchAllRef l :: cs) (throwing a)] it →
      PresConcl ⟨s, f, [.handler n (.catchAllRef l :: cs) (throwing a)]⟩
        ⟨s, f, [.ref (.exn a), .plain (.br l)]⟩ Cf Ct it := by
  intro Cf Ct it hs hf hu hwf _ hty
  exact PresConcl.same hs hf hu (hty.pres_throwRefHandlerCatchAllRefExn hwf)

end Silmaril.Wasm.Execution.Core
