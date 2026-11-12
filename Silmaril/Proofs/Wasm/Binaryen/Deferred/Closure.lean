module

public import Silmaril.Proofs.Wasm.Binaryen.Deferred.Forced
public import Silmaril.Wasm.Binaryen.CoalesceLocalsClosure

@[expose] public section

/-! # Deferred synchronisation through chains of forced local steps

A generalisation of silmaril's `Silmaril.Wasm.Binaryen.CoalesceLocals{Deferred,Closure}`
(pinned silmaril-lean): there the left successor of a matched step may complete
**one** pending `local.set` (`Normalizes`) before its frame agrees with the right
side. Here it may run any finite chain of `Forced` steps (`set`, `get`, `tee`, under
contexts), and the stuttering rank is `fwRank` instead of `aszs`. The closure
proof is silmaril's, restructured into per-context lemmas; it relies only on the
rank-generic closure lemmas of `Silmaril.Wasm.Execution.Core.Sim.Closure`.

The relation `DeferredCfgRel` is a genuine stuttering simulation (`ConfigSim`) at an
arbitrary numerical profile under the closed host: a left configuration still in a
forced chain steps (uniquely) along the chain while the right side stutters.
-/

namespace Silmaril.Wasm.Binaryen.Deferred

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-! ## Chains of forced steps -/

namespace Normalizes

theorem label {c d : Config H} (h : Normalizes c d) (vs : List Val) (n : Nat)
    (cont : List Instr) (rest : List Admin) :
    Normalizes ⟨c.store, c.frame, vals vs ++ [.label n cont c.code] ++ rest⟩
      ⟨d.store, d.frame, vals vs ++ [.label n cont d.code] ++ rest⟩ := by
  refine h.map (fun c => ⟨c.store, c.frame, vals vs ++ [.label n cont c.code] ++ rest⟩) ?_
  rintro ⟨s, f, b⟩ ⟨t, g, b'⟩ hf
  obtain rfl : t = s := hf.store
  exact .label hf vs n cont rest

theorem handler {c d : Config H} (h : Normalizes c d) (vs : List Val) (n : Nat)
    (cs : List Catch) (rest : List Admin) :
    Normalizes ⟨c.store, c.frame, vals vs ++ [.handler n cs c.code] ++ rest⟩
      ⟨d.store, d.frame, vals vs ++ [.handler n cs d.code] ++ rest⟩ := by
  refine h.map (fun c => ⟨c.store, c.frame, vals vs ++ [.handler n cs c.code] ++ rest⟩) ?_
  rintro ⟨s, f, b⟩ ⟨t, g, b'⟩ hf
  obtain rfl : t = s := hf.store
  exact .handler hf vs n cs rest

theorem frame {c d : Config H} (h : Normalizes c d) (f : Frame) (vs : List Val)
    (n : Nat) (rest : List Admin) :
    Normalizes ⟨c.store, f, vals vs ++ [.frame n c.frame c.code] ++ rest⟩
      ⟨d.store, f, vals vs ++ [.frame n d.frame d.code] ++ rest⟩ := by
  refine h.map (fun c => ⟨c.store, f, vals vs ++ [.frame n c.frame c.code] ++ rest⟩) ?_
  rintro ⟨s, fi, b⟩ ⟨t, gi, b'⟩ hf
  obtain rfl : t = s := hf.store
  exact .frame hf f vs n rest

/-- A terminal configuration has no forced step. -/
theorem eq_of_terminal {P : Profile} {c d : Config H} {r : Result} (h : Normalizes c d)
    (hc : c.code = r.toAdmin) : d = c := by
  cases h with
  | refl => rfl
  | cons hf _ =>
    have hs : Step P closedHost c _ := hf.step
    obtain ⟨s, f, code⟩ := c
    dsimp only at hc
    subst code
    cases r with
    | values => exact (SingleThreaded.Det.not_step_vals hs).elim
    | trap => exact (SingleThreaded.Det.not_step_trap hs).elim
    | throw => exact (SingleThreaded.Det.not_step_throwing hs).elim

end Normalizes

/-! ## Deferred matches -/

variable {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

namespace DeferredMatched

theorem of_matched {c' d : Config H} {m : Nat}
    (h : Matched P closedHost F BI B c' d m fwRank) : DeferredMatched P F BI B c' d m := by
  obtain ⟨d', hm, hr⟩ := h
  exact ⟨c', d', .refl _, hm, hr⟩

theorem of_steps {c' d d₁ : Config H} {m : Nat} (hs : Steps P closedHost d d₁)
    (h : DeferredMatched P F BI B c' d₁ m) : DeferredMatched P F BI B c' d m := by
  obtain ⟨c₁, d', hn, hm, hr⟩ := h
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hs with rfl | ht
  · exact ⟨c₁, d', hn, hm, hr⟩
  · refine ⟨c₁, d', hn, Or.inl ?_, hr⟩
    rcases hm with hm | ⟨rfl, -⟩
    · exact ht.trans hm
    · exact ht

/-- Lift a deferred match of a label body to the label. -/
theorem label {s' t : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cont cont' : List Instr} {z b b' L L' : List Admin}
    (h : DeferredMatched P F BI B ⟨s', f', z⟩ ⟨t, f, b'⟩ (fwRank b))
    (hc : InstrsRel BI cont cont') (hL : AdminsRel BI (WithCuts B) L L') :
    DeferredMatched P F BI B ⟨s', f', vals V ++ [.label n cont z] ++ L⟩
      ⟨t, f, vals V ++ [.label n cont' b'] ++ L'⟩ (fwRank (vals V ++ [.label n cont b] ++ L)) := by
  obtain ⟨⟨s₂, g, b₂⟩, ⟨t₂, g₃, b₃⟩, hn, hd, hst₂, hg, hb₂⟩ := h
  dsimp only at hg hst₂
  subst hg
  refine ⟨⟨s₂, g, vals V ++ [.label n cont b₂] ++ L⟩, ⟨t₂, g, vals V ++ [.label n cont' b₃] ++ L'⟩,
    hn.label V n cont L, ?_, hst₂, rfl,
    ((AdminsRel.vals V).append (.cons (.label n hc hb₂) .nil)).append hL⟩
  rcases hd with hd | ⟨he, hlt⟩
  · exact Or.inl (Closure.transGen_ctx (Closure.transGen_label hd n cont') V L')
  · cases he
    exact Or.inr ⟨rfl, LawfulCodeRank.label_lt (vals V) L n cont hlt⟩

/-- Lift a deferred match of a handler body to the handler. -/
theorem handler {s' t : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cs : List Catch} {z b b' L L' : List Admin}
    (h : DeferredMatched P F BI B ⟨s', f', z⟩ ⟨t, f, b'⟩ (fwRank b))
    (hL : AdminsRel BI (WithCuts B) L L') :
    DeferredMatched P F BI B ⟨s', f', vals V ++ [.handler n cs z] ++ L⟩
      ⟨t, f, vals V ++ [.handler n cs b'] ++ L'⟩ (fwRank (vals V ++ [.handler n cs b] ++ L)) := by
  obtain ⟨⟨s₂, g, b₂⟩, ⟨t₂, g₃, b₃⟩, hn, hd, hst₂, hg, hb₂⟩ := h
  dsimp only at hg hst₂
  subst hg
  refine ⟨⟨s₂, g, vals V ++ [.handler n cs b₂] ++ L⟩, ⟨t₂, g, vals V ++ [.handler n cs b₃] ++ L'⟩,
    hn.handler V n cs L, ?_, hst₂, rfl,
    ((AdminsRel.vals V).append (.cons (.handler n cs hb₂) .nil)).append hL⟩
  rcases hd with hd | ⟨he, hlt⟩
  · exact Or.inl (Closure.transGen_ctx
      (CoalesceLocalsLite.DeferredClosure.transGen_handler hd n cs) V L')
  · cases he
    exact Or.inr ⟨rfl, LawfulCodeRank.handler_lt (vals V) L n cs hlt⟩

/-- Lift a deferred match of a frame body to the frame. -/
theorem frame {s' t : Store H} {f fi fj : Frame} {V : List Val} {n : Nat}
    {z b b' L L' : List Admin}
    (h : DeferredMatched P F BI B ⟨s', fj, z⟩ ⟨t, fi, b'⟩ (fwRank b))
    (hL : AdminsRel BI (WithCuts B) L L') :
    DeferredMatched P F BI B ⟨s', f, vals V ++ [.frame n fj z] ++ L⟩
      ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩ (fwRank (vals V ++ [.frame n fi b] ++ L)) := by
  obtain ⟨⟨s₂, g, b₂⟩, ⟨t₂, g₃, b₃⟩, hn, hd, hst₂, hg, hb₂⟩ := h
  dsimp only at hg hst₂
  subst hg
  refine ⟨⟨s₂, f, vals V ++ [.frame n g b₂] ++ L⟩, ⟨t₂, f, vals V ++ [.frame n g b₃] ++ L'⟩,
    hn.frame f V n L, ?_, hst₂, rfl,
    ((AdminsRel.vals V).append (.cons (.frame n g hb₂) .nil)).append hL⟩
  rcases hd with hd | ⟨he, hlt⟩
  · exact Or.inl (Closure.transGen_ctx (Closure.transGen_frame hd) V L')
  · cases he
    exact Or.inr ⟨rfl, fwRank_frame_lt (vals V) L n fi fj hlt⟩

end DeferredMatched

/-! ## The closure -/

def DeferredStepIH (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) (m : Nat) : Prop :=
  ∀ {c d c' : Config H}, fwRank c.code < m → CfgRel F (AdminsRel BI (WithCuts B)) c d →
    Step P closedHost c c' → DeferredMatched P F BI B c' d (fwRank c.code)

namespace DeferredClosure

/-- A step of a label whose body can step is a step of the body. -/
theorem label_step_inv {s s' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cont : List Instr} {b L es' : List Admin} {c₀ : Config H}
    (hs₀ : Step P closedHost ⟨s, f, b⟩ c₀)
    (h : Step P closedHost ⟨s, f, vals V ++ [.label n cont b] ++ L⟩ ⟨s', f', es'⟩) :
    ∃ z, Step P closedHost ⟨s, f, b⟩ ⟨s', f', z⟩ ∧ es' = vals V ++ [.label n cont z] ++ L := by
  have h' : Step P closedHost ⟨s, f, vals V ++ .label n cont b :: L⟩ ⟨s', f', es'⟩ := by
    simpa using h
  rcases Step.split_head rfl h' with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨he, -⟩ | ⟨he, -⟩
  · obtain ⟨out, hr, rfl⟩ := Closure.Step.label_inv hs
    obtain ⟨z, hz, rfl⟩ := CoalesceLocalsLite.labelRed_ctxt_of_step hs₀ hr
    exact ⟨z, hz, by rw [hV]; simp⟩
  · cases he
  · cases he

/-- A step of a handler whose body can step is a step of the body. -/
theorem handler_step_inv {s s' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cs : List Catch} {b L es' : List Admin} {c₀ : Config H}
    (hs₀ : Step P closedHost ⟨s, f, b⟩ c₀)
    (h : Step P closedHost ⟨s, f, vals V ++ [.handler n cs b] ++ L⟩ ⟨s', f', es'⟩) :
    ∃ z, Step P closedHost ⟨s, f, b⟩ ⟨s', f', z⟩ ∧ es' = vals V ++ [.handler n cs z] ++ L := by
  have h' : Step P closedHost ⟨s, f, vals V ++ .handler n cs b :: L⟩ ⟨s', f', es'⟩ := by
    simpa using h
  rcases Step.split_head rfl h' with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨he, -⟩ | ⟨he, -⟩
  · obtain ⟨out, hr, rfl⟩ := Step.handler_inv hs
    obtain ⟨z, hz, rfl⟩ := CoalesceLocalsLite.handlerInv_ctxt_of_step hs₀ hr
    exact ⟨z, hz, by rw [hV]; simp⟩
  · cases he
  · cases he

/-- A step of a frame whose body can step is a step of the body. -/
theorem frame_step_inv {s s' : Store H} {f f' fi : Frame} {V : List Val} {n : Nat}
    {b L es' : List Admin} {c₀ : Config H}
    (hs₀ : Step P closedHost ⟨s, fi, b⟩ c₀)
    (h : Step P closedHost ⟨s, f, vals V ++ [.frame n fi b] ++ L⟩ ⟨s', f', es'⟩) :
    ∃ fj z, Step P closedHost ⟨s, fi, b⟩ ⟨s', fj, z⟩ ∧ f' = f ∧
      es' = vals V ++ [.frame n fj z] ++ L := by
  have h' : Step P closedHost ⟨s, f, vals V ++ .frame n fi b :: L⟩ ⟨s', f', es'⟩ := by
    simpa using h
  rcases Step.split_head rfl h' with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨he, -⟩ | ⟨he, -⟩
  · obtain ⟨out, rfl, hr⟩ := Closure.Step.frame_redex_aux hs us n fi b rfl
    obtain ⟨fj, z, hz, hf, rfl⟩ := CoalesceLocalsLite.frameRedex_ctxt_of_step hs₀ hr
    exact ⟨fj, z, hz, hf, by rw [hV]; simp⟩
  · cases he
  · cases he

variable (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F closedHost)

include hF hhost in
/-- The label case: a body step defers, otherwise silmaril's administrative case. -/
theorem label_case (hB : BaseFacts P closedHost F BI B fwRank)
    {s t s' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cont cont' : List Instr} {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P closedHost ⟨s, f, b⟩ c' →
      DeferredMatched P F BI B c' ⟨t, f, b'⟩ (fwRank b))
    (hst : StoreRel F s t) (hc : InstrsRel BI cont cont')
    (hb : AdminsRel BI (WithCuts B) b b') (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P closedHost ⟨s, f, vals V ++ [.label n cont b] ++ L⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.label n cont' b'] ++ L'⟩
      (fwRank (vals V ++ [.label n cont b] ++ L)) := by
  classical
  by_cases hbody : ∃ c', Step P closedHost ⟨s, f, b⟩ c'
  · obtain ⟨c₀, hs₀⟩ := hbody
    obtain ⟨z, hz, rfl⟩ := label_step_inv hs₀ h
    exact (ih hz).label hc hL
  · exact .of_matched (Closure.label_case_of_body hF hhost hB
      (fun hs => (hbody ⟨_, hs⟩).elim) hst hc hb hL h)

include hF hhost in
/-- The handler case. -/
theorem handler_case (hB : BaseFacts P closedHost F BI B fwRank)
    {s t s' : Store H} {f f' : Frame} {V : List Val} {n : Nat}
    {cs : List Catch} {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P closedHost ⟨s, f, b⟩ c' →
      DeferredMatched P F BI B c' ⟨t, f, b'⟩ (fwRank b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P closedHost ⟨s, f, vals V ++ [.handler n cs b] ++ L⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.handler n cs b'] ++ L'⟩
      (fwRank (vals V ++ [.handler n cs b] ++ L)) := by
  classical
  by_cases hbody : ∃ c', Step P closedHost ⟨s, f, b⟩ c'
  · obtain ⟨c₀, hs₀⟩ := hbody
    obtain ⟨z, hz, rfl⟩ := handler_step_inv hs₀ h
    exact (ih hz).handler hL
  · exact .of_matched (Closure.handler_case_of_body hF hhost hB
      (fun hs => (hbody ⟨_, hs⟩).elim) hst hb hL h)

include hF hhost in
/-- The frame case. -/
theorem frame_case (hB : BaseFacts P closedHost F BI B fwRank)
    {s t s' : Store H} {f f' fi : Frame} {V : List Val} {n : Nat}
    {b b' L L' es' : List Admin}
    (ih : ∀ {c' : Config H}, Step P closedHost ⟨s, fi, b⟩ c' →
      DeferredMatched P F BI B c' ⟨t, fi, b'⟩ (fwRank b))
    (hst : StoreRel F s t) (hb : AdminsRel BI (WithCuts B) b b')
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P closedHost ⟨s, f, vals V ++ [.frame n fi b] ++ L⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [.frame n fi b'] ++ L'⟩
      (fwRank (vals V ++ [.frame n fi b] ++ L)) := by
  classical
  by_cases hbody : ∃ c', Step P closedHost ⟨s, fi, b⟩ c'
  · obtain ⟨c₀, hs₀⟩ := hbody
    obtain ⟨fj, z, hz, rfl, rfl⟩ := frame_step_inv hs₀ h
    exact (ih hz).frame hL
  · exact .of_matched (Closure.frame_case_of_body hF hhost hB
      (fun hs => (hbody ⟨_, hs⟩).elim) hst hb hL h)

include hF hhost in
/-- A context head related to itself or to a related context. -/
theorem ctx_arm (hB : BaseFacts P closedHost F BI B fwRank)
    {s t s' : Store H} {f f' : Frame} {V : List Val} {a b : Admin} {L L' es' : List Admin}
    (ih : DeferredStepIH P F BI B (fwRank (vals V ++ [a] ++ L)))
    (hst : StoreRel F s t) (hab : AdminRel BI (WithCuts B) a b) (hctx : a.IsCtx)
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P closedHost ⟨s, f, vals V ++ [a] ++ L⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [b] ++ L'⟩
      (fwRank (vals V ++ [a] ++ L)) := by
  cases hab with
  | refl =>
    show DeferredMatched P F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ [a] ++ L'⟩
      (fwRank (vals V ++ [a] ++ L))
    cases a with
    | label n cont b =>
      exact label_case hF hhost hB (fun hs => ih (c := ⟨s, f, b⟩) (d := ⟨t, f, b⟩)
        (LawfulCodeRank.label_body_lt (vals V) L n cont b) ⟨hst, rfl, AdminsRel.refl _⟩ hs) hst (InstrsRel.refl _) (AdminsRel.refl _) hL h
    | handler n cs b =>
      exact handler_case hF hhost hB (fun hs => ih (c := ⟨s, f, b⟩) (d := ⟨t, f, b⟩)
        (LawfulCodeRank.handler_body_lt (vals V) L n cs b) ⟨hst, rfl, AdminsRel.refl _⟩ hs) hst (AdminsRel.refl _) hL h
    | frame n fi b =>
      exact frame_case hF hhost hB (fun hs => ih (c := ⟨s, fi, b⟩) (d := ⟨t, fi, b⟩)
        (LawfulCodeRank.frame_body_lt (vals V) L n fi b) ⟨hst, rfl, AdminsRel.refl _⟩ hs) hst (AdminsRel.refl _) hL h
    | _ => exact hctx.elim
  | plain _ => exact hctx.elim
  | @label n cont cont' bd bd' hc hb =>
    exact label_case hF hhost hB (fun hs => ih (c := ⟨s, f, bd⟩) (d := ⟨t, f, bd'⟩)
      (LawfulCodeRank.label_body_lt (vals V) L n cont bd) ⟨hst, rfl, hb⟩ hs) hst hc hb hL h
  | @handler n cs bd bd' hb =>
    exact handler_case hF hhost hB (fun hs => ih (c := ⟨s, f, bd⟩) (d := ⟨t, f, bd'⟩)
      (LawfulCodeRank.handler_body_lt (vals V) L n cs bd) ⟨hst, rfl, hb⟩ hs) hst hb hL h
  | @frame n fi bd bd' hb =>
    exact frame_case hF hhost hB (fun hs => ih (c := ⟨s, fi, bd⟩) (d := ⟨t, fi, bd'⟩)
      (LawfulCodeRank.frame_body_lt (vals V) L n fi bd) ⟨hst, rfl, hb⟩ hs) hst hb hL h

include hF hhost in
/-- One active segment: a single related head, a base pair, or an exit cut. -/
theorem seg_case (hB : DeferredBaseSim P F BI B)
    {s t s' : Store H} {f f' : Frame} {V : List Val} {xs ys L L' es' : List Admin}
    (ih : DeferredStepIH P F BI B (fwRank (vals V ++ xs ++ L)))
    (hst : StoreRel F s t) (hseg : Seg BI (WithCuts B) xs ys) (hact : xs.all Admin.isVal = false)
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P closedHost ⟨s, f, vals V ++ xs ++ L⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F BI B ⟨s', f', es'⟩ ⟨t, f, vals V ++ ys ++ L'⟩
      (fwRank (vals V ++ xs ++ L)) := by
  cases hseg with
  | @one a b hab =>
    have ha : a.val? = none := by simpa [Admin.isVal] using hact
    by_cases hctx : a.IsCtx
    · exact ctx_arm hF hhost hB.facts ih hst hab hctx hL h
    · by_cases hcall : a.IsCallRef
      · exact .of_matched (Closure.call_case hF hhost hst hab hcall hL h)
      · exact .of_matched (Closure.seq_case hst hab ha hctx hcall hL h)
  | base hb =>
    rcases hb with hb | ⟨us, ws, k, x', y', hk, rfl, rfl⟩
    · exact hB.step hst hb hL h
    · exact .of_matched (Closure.cut_case hk hst
        (U := V ++ us) (X := x' ++ L) (W := V ++ ws) (Y := y' ++ L') (by simp) (by simp) h)

include hF hhost in
/-- One step from a related code sequence, given the induction hypothesis at its rank. -/
theorem step_at (hB : DeferredBaseSim P F BI B)
    {s t s' : Store H} {f f' : Frame} {x y es' : List Admin}
    (ih : DeferredStepIH P F BI B (fwRank x)) (hst : StoreRel F s t)
    (hxy : AdminsRel BI (WithCuts B) x y)
    (h : Step P closedHost ⟨s, f, x⟩ ⟨s', f', es'⟩) :
    DeferredMatched P F BI B ⟨s', f', es'⟩ ⟨t, f, y⟩ (fwRank x) := by
  have hsegs : Segs BI (WithCuts B) x y :=
    AdminsRel.segs (fun _ _ hb => Or.inl (hB.facts.src hb)) hxy
  obtain ⟨V, xs, ys, xr, yr, t₁, rfl, hseg, hact, hr, hrun, hst₁⟩ :=
    Closure.split_active hB.facts hsegs h.not_all_isVal [] hst (f := f)
  have hrun' : Steps P closedHost ⟨t, f, y⟩ ⟨t₁, f, vals V ++ ys ++ yr⟩ :=
    Closure.steps_congr hrun (by simp) (by simp)
  exact .of_steps hrun' (seg_case hF hhost hB ih hst₁ hseg hact hr.adminsRel h)

include hF hhost in
theorem step_main (hB : DeferredBaseSim P F BI B) : ∀ m : Nat, DeferredStepIH P F BI B m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  rintro ⟨s, f, x⟩ ⟨t, g, y⟩ ⟨s', f', es'⟩ hm ⟨hst, hfg, hxy⟩ hstep
  obtain rfl : f = g := hfg
  exact step_at hF hhost hB (ihm _ hm) hst hxy hstep

end DeferredClosure

/-- **A genuine stuttering simulation**, including the transient left frames, at
every numerical profile under the closed host. -/
theorem _root_.Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_configSim (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B) :
    ∃ sim : ConfigSim P closedHost (DeferredCfgRel F BI B),
      sim.toForwardSim.measure = fun c => fwRank c.code := by
  refine ⟨⟨⟨fun c => fwRank c.code, ?_⟩, ?_⟩, rfl⟩
  · intro c c' d hs hrel
    obtain ⟨c₁, hn, hr⟩ := hrel
    cases hn with
    | refl =>
      obtain ⟨cn, d', hnorm, hm, hr'⟩ :=
        DeferredClosure.step_main hF hhost hB _ (Nat.lt_succ_self _) hr hs
      exact ⟨d', hm, cn, hnorm, hr'⟩
    | cons hf hrest =>
      obtain rfl := hf.unique c' hs
      exact ⟨d, Or.inr ⟨rfl, hf.rank⟩, _, hrest, hr⟩
  · intro c d r hrel hc
    obtain ⟨c₁, hn, hr⟩ := hrel
    obtain rfl := hn.eq_of_terminal (P := P) hc
    exact Closure.terminal_case hB.facts hr hc

/-- Completed runs retain final stores for subsequent invocations. -/
theorem _root_.Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_run_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B)
    {c d c' : Config H} {r : Result} (h : CfgRel F (AdminsRel BI B) c d)
    (hs : Steps P closedHost c c') (hc : c'.code = r.toAdmin) :
    ∃ d', Steps P closedHost d d' ∧ d'.code = r.toAdmin ∧ StoreRel F c'.store d'.store := by
  obtain ⟨sim, _⟩ := Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_configSim hF hhost hB
  obtain ⟨d₁, hd, cn, hn, hr⟩ := sim.toForwardSim.steps hs
    ⟨c, .refl _, h.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl))⟩
  obtain rfl := hn.eq_of_terminal (P := P) hc
  obtain ⟨d', hd', hc', hst⟩ := Closure.terminal_case_store hB.facts hr hc
  exact ⟨d', hd.trans hd', hc', hst⟩

theorem _root_.Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_diverges_transport (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi)
    (hhost : HostRespects F closedHost) (hB : DeferredBaseSim P F BI B)
    {c d : Config H} (h : CfgRel F (AdminsRel BI B) c d)
    (hd : Diverges P closedHost c) : Diverges P closedHost d := by
  obtain ⟨sim, _⟩ := Silmaril.Proofs.Wasm.Binaryen.Deferred.deferred_closure_configSim hF hhost hB
  exact sim.toForwardSim.diverges hd
    ⟨c, .refl _, h.mono (fun _ _ => AdminsRel.mono (fun _ _ => Or.inl))⟩

end Silmaril.Wasm.Binaryen.Deferred
