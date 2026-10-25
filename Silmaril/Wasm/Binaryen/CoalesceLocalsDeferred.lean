module

public import Silmaril.Wasm.Binaryen.CoalesceLocalsCompletion

@[expose] public section

/-! # Deferred synchronization for the overwritten-local simulation

A source successor may complete one forced local write before its frame agrees
with the target. The stuttering bound always measures the actual successor,
before that completion; this is needed by the ordinary forward-simulation API.
-/

namespace Silmaril.Wasm.Binaryen.CoalesceLocalsLite

open Execution.Core Execution.Core.Sim Validation Numerics

variable {H : Type} {P : Profile}

/-- Synchronize immediately, or after exactly one forced overwrite. -/
inductive Normalizes : Config H → Config H → Prop where
  | refl (c) : Normalizes c c
  | complete {c d} : Completion c d → Normalizes c d

namespace Normalizes

theorem store {c d : Config H} (h : Normalizes c d) : d.store = c.store := by
  cases h with
  | refl => rfl
  | complete h => exact h.store

theorem label {c d : Config H} (h : Normalizes c d) (vs : List Val) (n : Nat)
    (cont : List Instr) (rest : List Admin) :
    Normalizes ⟨c.store, c.frame, vals vs ++ [.label n cont c.code] ++ rest⟩
      ⟨d.store, d.frame, vals vs ++ [.label n cont d.code] ++ rest⟩ := by
  cases h with
  | refl => exact .refl _
  | complete h =>
    obtain ⟨s, f, b⟩ := c
    obtain ⟨t, g, b'⟩ := d
    have he := h.store
    dsimp only at he
    subst he
    exact .complete (.label h vs n cont rest)

theorem handler {c d : Config H} (h : Normalizes c d) (vs : List Val) (n : Nat)
    (cs : List Catch) (rest : List Admin) :
    Normalizes ⟨c.store, c.frame, vals vs ++ [.handler n cs c.code] ++ rest⟩
      ⟨d.store, d.frame, vals vs ++ [.handler n cs d.code] ++ rest⟩ := by
  cases h with
  | refl => exact .refl _
  | complete h =>
    obtain ⟨s, f, b⟩ := c
    obtain ⟨t, g, b'⟩ := d
    have he := h.store
    dsimp only at he
    subst he
    exact .complete (.handler h vs n cs rest)

theorem frame {c d : Config H} (h : Normalizes c d) (f : Frame) (vs : List Val)
    (n : Nat) (rest : List Admin) :
    Normalizes ⟨c.store, f, vals vs ++ [.frame n c.frame c.code] ++ rest⟩
      ⟨d.store, f, vals vs ++ [.frame n d.frame d.code] ++ rest⟩ := by
  cases h with
  | refl => exact .refl _
  | complete h =>
    obtain ⟨s, fi, b⟩ := c
    obtain ⟨t, gi, b'⟩ := d
    have he := h.store
    dsimp only at he
    subst he
    exact .complete (.frame h f vs n rest)

end Normalizes

/-- A matched step whose actual source successor may have one pending overwrite. -/
def DeferredMatched (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (c' d : Config H) (m : Nat) : Prop :=
  ∃ c₁ d', Normalizes c' c₁ ∧
    (Relation.TransGen (Step P closedHost) d d' ∨ (d' = d ∧ aszs c'.code < m)) ∧
    CfgRel F (AdminsRel BI (WithCuts B)) c₁ d'

variable {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

namespace DeferredMatched

theorem of_matched {c' d : Config H} {m : Nat}
    (h : Matched P closedHost F BI B c' d m aszs) :
    DeferredMatched (P := P) F BI B c' d m := by
  obtain ⟨d', hm, hr⟩ := h
  exact ⟨c', d', .refl _, hm, hr⟩

theorem of_steps {c' d d₁ : Config H} {m : Nat} (hs : Steps P closedHost d d₁)
    (h : DeferredMatched (P := P) F BI B c' d₁ m) :
    DeferredMatched (P := P) F BI B c' d m := by
  obtain ⟨c₁, d', hn, hm, hr⟩ := h
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hs with rfl | ht
  · exact ⟨c₁, d', hn, hm, hr⟩
  · refine ⟨c₁, d', hn, Or.inl ?_, hr⟩
    rcases hm with hm | ⟨rfl, -⟩
    · exact ht.trans hm
    · exact ht

/-- Lift a deferred match through two related execution contexts. -/
theorem map {c' d : Config H} {m m' : Nat}
    (h : DeferredMatched (P := P) F BI B c' d m) (g k : Config H → Config H)
    (hnorm : ∀ {a b}, Normalizes a b → Normalizes (g a) (g b))
    (hstep : ∀ {a b}, Step P closedHost a b → Step P closedHost (k a) (k b))
    (hrel : ∀ {a b}, CfgRel F (AdminsRel BI (WithCuts B)) a b →
      CfgRel F (AdminsRel BI (WithCuts B)) (g a) (k b))
    (hlt : aszs c'.code < m → aszs (g c').code < m') :
    DeferredMatched (P := P) F BI B (g c') (k d) m' := by
  obtain ⟨c₁, d', hn, hm, hr⟩ := h
  refine ⟨g c₁, k d', hnorm hn, ?_, hrel hr⟩
  rcases hm with hm | ⟨rfl, hm⟩
  · exact Or.inl (Closure.transGen_map k hstep hm)
  · exact Or.inr ⟨rfl, hlt hm⟩

end DeferredMatched

/-- Base laws permit a real forced overwrite before synchronizing frames. -/
structure DeferredBaseSim (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) : Prop where
  facts : BaseFacts P closedHost F BI B aszs
  step : ∀ {s t s' : Store H} {f f' : Frame} {vs : List Val}
    {x y rest rest' es' : List Admin},
    StoreRel F s t → B x y → AdminsRel BI (WithCuts B) rest rest' →
    Step P closedHost ⟨s, f, vals vs ++ x ++ rest⟩ ⟨s', f', es'⟩ →
    DeferredMatched (P := P) F BI B ⟨s', f', es'⟩
      ⟨t, f, vals vs ++ y ++ rest'⟩ (aszs (vals vs ++ x ++ rest))

namespace DeferredClosure

theorem transGen_handler {c d : Config H}
    (h : Relation.TransGen (Step P closedHost) c d) (n : Nat) (cs : List Catch) :
    Relation.TransGen (Step P closedHost)
      ⟨c.store, c.frame, [.handler n cs c.code]⟩
      ⟨d.store, d.frame, [.handler n cs d.code]⟩ := by
  apply Closure.transGen_map (fun c => ⟨c.store, c.frame, [.handler n cs c.code]⟩) _ h
  intro a b hs
  cases a
  cases b
  exact Step.ctxtHandler hs

theorem label_case (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : BaseFacts P closedHost F BI B aszs)
    {s t s' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cont cont' : List Instr} {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P closedHost ⟨s, f, b⟩ c' →
      DeferredMatched (P := P) F BI B c' ⟨t, f, b'⟩ (aszs b))
    (hst : StoreRel F s t) (hc : InstrsRel BI cont cont')
    (hb : AdminsRel BI (WithCuts B) b b') (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P closedHost ⟨s, f, vals V ++ [.label n cont b] ++ L⟩ ⟨s', f', es'⟩) :
    DeferredMatched (P := P) F BI B ⟨s', f', es'⟩
      ⟨t, f, vals V ++ [.label n cont' b'] ++ L'⟩
      (aszs (vals V ++ [.label n cont b] ++ L)) := by
  classical
  by_cases hbody : ∃ c', Step P closedHost ⟨s, f, b⟩ c'
  · obtain ⟨c₀, hs₀⟩ := hbody
    rw [show vals V ++ [.label n cont b] ++ L = vals V ++ .label n cont b :: L by simp] at h
    rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · obtain ⟨out, hr, rfl⟩ := Closure.Step.label_inv hs
      obtain ⟨z, hz, rfl⟩ := labelRed_ctxt_of_step hs₀ hr
      rw [show vals ws ++ (vals us ++ [Admin.label n cont z]) ++ L =
        vals V ++ [.label n cont z] ++ L by rw [hV]; simp]
      obtain ⟨⟨s₂, g, b₂⟩, ⟨t₂, g₃, b₃⟩, hn, hd, hst₂, hg, hb₂⟩ := ih hz
      dsimp only at hn hd hst₂ hg hb₂
      cases hg
      refine ⟨⟨s₂, g, vals V ++ [.label n cont b₂] ++ L⟩,
        ⟨t₂, g, vals V ++ [.label n cont' b₃] ++ L'⟩,
        hn.label V n cont L, ?_, hst₂, rfl,
        ((AdminsRel.vals V).append (.cons (.label n hc hb₂) .nil)).append hL⟩
      rcases hd with hd | ⟨he, hlt⟩
      · exact Or.inl (Closure.transGen_ctx (Closure.transGen_label hd n cont') V L')
      · cases he
        exact Or.inr ⟨rfl, LawfulCodeRank.label_lt (vals V) L n cont hlt⟩
    · cases he
    · cases he
  · exact .of_matched (Closure.label_case_of_body hF hhost hB
      (fun hs => (hbody ⟨_, hs⟩).elim) hst hc hb hL h)

theorem handler_case (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : BaseFacts P closedHost F BI B aszs)
    {s t s' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cs : List Catch} {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P closedHost ⟨s, f, b⟩ c' →
      DeferredMatched (P := P) F BI B c' ⟨t, f, b'⟩ (aszs b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P closedHost ⟨s, f, vals V ++ [.handler n cs b] ++ L⟩ ⟨s', f', es'⟩) :
    DeferredMatched (P := P) F BI B ⟨s', f', es'⟩
      ⟨t, f, vals V ++ [.handler n cs b'] ++ L'⟩
      (aszs (vals V ++ [.handler n cs b] ++ L)) := by
  classical
  by_cases hbody : ∃ c', Step P closedHost ⟨s, f, b⟩ c'
  · obtain ⟨c₀, hs₀⟩ := hbody
    rw [show vals V ++ [.handler n cs b] ++ L = vals V ++ .handler n cs b :: L by simp] at h
    rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · obtain ⟨out, hr, rfl⟩ := Step.handler_inv hs
      obtain ⟨z, hz, rfl⟩ := handlerInv_ctxt_of_step hs₀ hr
      rw [show vals ws ++ (vals us ++ [Admin.handler n cs z]) ++ L =
        vals V ++ [.handler n cs z] ++ L by rw [hV]; simp]
      obtain ⟨⟨s₂, g, b₂⟩, ⟨t₂, g₃, b₃⟩, hn, hd, hst₂, hg, hb₂⟩ := ih hz
      dsimp only at hn hd hst₂ hg hb₂
      cases hg
      refine ⟨⟨s₂, g, vals V ++ [.handler n cs b₂] ++ L⟩,
        ⟨t₂, g, vals V ++ [.handler n cs b₃] ++ L'⟩,
        hn.handler V n cs L, ?_, hst₂, rfl,
        ((AdminsRel.vals V).append (.cons (.handler n cs hb₂) .nil)).append hL⟩
      rcases hd with hd | ⟨he, hlt⟩
      · exact Or.inl (Closure.transGen_ctx (transGen_handler hd n cs) V L')
      · cases he
        exact Or.inr ⟨rfl, LawfulCodeRank.handler_lt (vals V) L n cs hlt⟩
    · cases he
    · cases he
  · exact .of_matched (Closure.handler_case_of_body hF hhost hB
      (fun hs => (hbody ⟨_, hs⟩).elim) hst hb hL h)

theorem frame_case (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : BaseFacts P closedHost F BI B aszs)
    {s t s' : Store H} {f f' fi : Frame} {V : List Val} {n : Nat}
    {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P closedHost ⟨s, fi, b⟩ c' →
      DeferredMatched (P := P) F BI B c' ⟨t, fi, b'⟩ (aszs b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P closedHost ⟨s, f, vals V ++ [.frame n fi b] ++ L⟩ ⟨s', f', es'⟩) :
    DeferredMatched (P := P) F BI B ⟨s', f', es'⟩
      ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩
      (aszs (vals V ++ [.frame n fi b] ++ L)) := by
  classical
  by_cases hbody : ∃ c', Step P closedHost ⟨s, fi, b⟩ c'
  · obtain ⟨c₀, hs₀⟩ := hbody
    rw [show vals V ++ [.frame n fi b] ++ L = vals V ++ .frame n fi b :: L by simp] at h
    rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · obtain ⟨out, rfl, hr⟩ := Closure.Step.frame_redex_aux hs us n fi b rfl
      obtain ⟨fj, z, hz, hf, rfl⟩ := frameRedex_ctxt_of_step hs₀ hr
      dsimp only at hf hz
      subst f'
      rw [show vals ws ++ (vals us ++ [Admin.frame n fj z]) ++ L =
        vals V ++ [.frame n fj z] ++ L by rw [hV]; simp]
      obtain ⟨⟨s₂, g, b₂⟩, ⟨t₂, g₃, b₃⟩, hn, hd, hst₂, hg, hb₂⟩ := ih hz
      dsimp only at hn hd hst₂ hg hb₂
      cases hg
      refine ⟨⟨s₂, f, vals V ++ [.frame n g b₂] ++ L⟩,
        ⟨t₂, f, vals V ++ [.frame n g b₃] ++ L'⟩,
        hn.frame f V n L, ?_, hst₂, rfl,
        ((AdminsRel.vals V).append (.cons (.frame n g hb₂) .nil)).append hL⟩
      rcases hd with hd | ⟨he, hlt⟩
      · exact Or.inl (Closure.transGen_ctx (Closure.transGen_frame hd) V L')
      · cases he
        refine Or.inr ⟨rfl, ?_⟩
        simp only [aszs_append, aszs_cons, aszs_nil, asz]
        omega
    · cases he
    · cases he
  · exact .of_matched (Closure.frame_case_of_body hF hhost hB
      (fun hs => (hbody ⟨_, hs⟩).elim) hst hb hL h)

end DeferredClosure

end Silmaril.Wasm.Binaryen.CoalesceLocalsLite
