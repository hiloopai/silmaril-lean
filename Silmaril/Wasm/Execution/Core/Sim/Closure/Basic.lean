module

public import Silmaril.Wasm.Execution.Core.Sim.Behaviour
public import Silmaril.Wasm.Execution.Core.Sim.CodeRel
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.Execution.Core.Sim.Segments
public import Silmaril.Wasm.Execution.Core.Sim.StepMatch
public import Silmaril.Wasm.Execution.Core.Sim.RankedSegments

@[expose] public section

/-! # Base obligations, exit cuts and the shared lemmas of the closure proof

`BaseSim` (the obligations on base pairs, with an optional rank defaulting to
`codeSize`), `ExitCut`/`WithCuts` (the exit cuts),
and the per-head interface of the proof of `closure_configSim`
(`Sim/Closure.lean`): `Matched`, the one-step obligation with `codeSize`
stuttering, and `StepIH`, the induction hypothesis on the size of the left code.
The helpers in namespace `Closure` (`run_vals`, `split_active`, `exit_lift`,
`cut_case`, `transport_lift`) are shared by the per-head case files
`Sim/Closure/{Struct,Label,Handler,Frame,Call}.lean`, which import only this file
and can be proved independently. -/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type}

/-- The obligations on base pairs. -/
structure BaseSim (P : Profile) (host : HostSemantics H) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (rank : List Admin → Nat := codeSize) : Prop where
  /-- Lowered source base pairs are runtime base pairs. -/
  src : ∀ {x y : List Instr}, BI x y → B (expression x) (expression y)
  /-- One-step matching in an arbitrary value prefix and related suffix. -/
  step : ∀ {s t s' : Store H} {f f' : Frame} {vs : List Val} {x y rest rest' es' : List Admin},
    StoreRel F s t → B x y → AdminsRel BI B rest rest' →
    Step P host ⟨s, f, vals vs ++ x ++ rest⟩ ⟨s', f', es'⟩ →
    ∃ (t' : Store H) (es'' : List Admin),
      (Relation.TransGen (Step P host) ⟨t, f, vals vs ++ y ++ rest'⟩ ⟨t', f', es''⟩ ∨
        (t' = t ∧ f' = f ∧ es'' = vals vs ++ y ++ rest' ∧
          rank es' < rank (vals vs ++ x ++ rest))) ∧
      StoreRel F s' t' ∧ AdminsRel BI B es' es''
  /-- Exits inside a base pair are reached on the right with the same kernel. -/
  exit : ∀ {s t : Store H} {f : Frame} {vs us : List Val} {x y k j : List Admin},
    StoreRel F s t → B x y → Exit k → vals vs ++ x = vals us ++ k ++ j →
    ∃ (t' : Store H) (j' : List Admin),
      Steps P host ⟨t, f, vals vs ++ y⟩ ⟨t', f, vals us ++ k ++ j'⟩ ∧ StoreRel F s t'
  /-- A base pair whose left side is values evaluates on the right to those values. -/
  values : ∀ {s t : Store H} {f : Frame} {vs us : List Val} {x y : List Admin},
    StoreRel F s t → B x y → x = vals us →
    ∃ t' : Store H, Steps P host ⟨t, f, vals vs ++ y⟩ ⟨t', f, vals vs ++ vals us⟩ ∧
      StoreRel F s t'

/-- The source, exit and value laws of a base relation. Context and terminal
transport use these laws without a one-step matching obligation; keeping them
separate also supports simulations whose step law needs a typed reachability
guard. The existing `BaseSim` interface and defaults remain unchanged. -/
structure BaseFacts (P : Profile) (host : HostSemantics H) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (rank : List Admin → Nat := codeSize) : Prop where
  src : ∀ {x y : List Instr}, BI x y → B (expression x) (expression y)
  exit : ∀ {s t : Store H} {f : Frame} {vs us : List Val} {x y k j : List Admin},
    StoreRel F s t → B x y → Exit k → vals vs ++ x = vals us ++ k ++ j →
    ∃ (t' : Store H) (j' : List Admin),
      Steps P host ⟨t, f, vals vs ++ y⟩ ⟨t', f, vals us ++ k ++ j'⟩ ∧ StoreRel F s t'
  values : ∀ {s t : Store H} {f : Frame} {vs us : List Val} {x y : List Admin},
    StoreRel F s t → B x y → x = vals us →
    ∃ t' : Store H, Steps P host ⟨t, f, vals vs ++ y⟩ ⟨t', f, vals vs ++ vals us⟩ ∧
      StoreRel F s t'

theorem BaseSim.toBaseFacts {P : Profile} {host : HostSemantics H}
    {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
    {B : List Admin → List Admin → Prop} {rank : List Admin → Nat}
    (h : BaseSim P host F BI B rank) : BaseFacts P host F BI B rank :=
  ⟨h.src, h.exit, h.values⟩

instance {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    {rank : List Admin → Nat} :
    Coe (BaseSim P host F BI B rank) (BaseFacts P host F BI B rank) := ⟨BaseSim.toBaseFacts⟩

variable {P : Profile} {host : HostSemantics H} {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

/-- Exit cuts: a `trap` or a thrown exception (`REF.EXN_ADDR a; THROW_REF`)
after arbitrary values, followed by arbitrary code, on both sides. Every step of
such a sequence discards code around the kernel (`trap-instrs`,
`throw_ref-instrs`, possibly under `ctxt-instrs`), so what follows the kernel is
unobservable. -/
def ExitCut (x y : List Admin) : Prop :=
  ∃ (us ws : List Val) (k x' y' : List Admin), (k = [.trap] ∨ ∃ a, k = throwing a) ∧
    x = vals us ++ k ++ x' ∧ y = vals ws ++ k ++ y'

theorem ExitCut.symm {x y : List Admin} (h : ExitCut x y) : ExitCut y x := by
  obtain ⟨us, ws, k, x', y', hk, rfl, rfl⟩ := h
  exact ⟨ws, us, k, y', x', hk, rfl, rfl⟩

/-- A runtime base relation together with the exit cuts. -/
def WithCuts (B : List Admin → List Admin → Prop) (x y : List Admin) : Prop :=
  B x y ∨ ExitCut x y

theorem WithCuts.flip {x y : List Admin} (h : WithCuts B x y) :
    WithCuts (fun a b => B b a) y x :=
  h.imp id ExitCut.symm

/-- The one-step obligation at a pair: the right configuration `d` takes at least
one step, or stutters while the measure drops below `m`, to a configuration
related to `c'`. -/
def Matched (P : Profile) (host : HostSemantics H) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (c' d : Config H) (m : Nat) (rank : List Admin → Nat := codeSize) : Prop :=
  ∃ d', (Relation.TransGen (Step P host) d d' ∨ (d' = d ∧ rank c'.code < m)) ∧
    CfgRel F (AdminsRel BI (WithCuts B)) c' d'

/-- Explicit-rank form of `Matched`; the old name defaults to `codeSize`. -/
abbrev RankedMatched (rank : List Admin → Nat) (P : Profile) (host : HostSemantics H)
    (F : FuncInst H → FuncInst H → Prop) (BI : List Instr → List Instr → Prop)
    (B : List Admin → List Admin → Prop) (c' d : Config H) (m : Nat) : Prop :=
  Matched P host F BI B c' d m rank

/-- A right prefix run composes with a matched step. -/
theorem Matched.of_steps {rank : List Admin → Nat} {c' d d₁ : Config H} {m : Nat} (hs : Steps P host d d₁)
    (h : RankedMatched rank P host F BI B c' d₁ m) : RankedMatched rank P host F BI B c' d m := by
  obtain ⟨d', hm, hr⟩ := h
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hs with rfl | ht
  · exact ⟨d', hm, hr⟩
  · refine ⟨d', Or.inl ?_, hr⟩
    rcases hm with h₂ | ⟨rfl, -⟩
    · exact ht.trans h₂
    · exact ht

/-- The induction hypothesis of `step_main`: the one-step obligation for left
code smaller than `m`. -/
def StepIH (P : Profile) (host : HostSemantics H) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) (m : Nat)
    (rank : List Admin → Nat := codeSize) : Prop :=
  ∀ {c d c' : Config H}, rank c.code < m → CfgRel F (AdminsRel BI (WithCuts B)) c d →
    Step P host c c' → Matched P host F BI B c' d (rank c.code) rank

/-- Explicit-rank form of `StepIH`; the old name defaults to `codeSize`. -/
abbrev RankedStepIH (rank : List Admin → Nat) (P : Profile) (host : HostSemantics H)
    (F : FuncInst H → FuncInst H → Prop) (BI : List Instr → List Instr → Prop)
    (B : List Admin → List Admin → Prop) (m : Nat) : Prop :=
  StepIH P host F BI B m rank

variable {rank : List Admin → Nat}

namespace Closure

theorem steps_congr {t t' : Store H} {f f' : Frame} {a a' b b' : List Admin}
    (h : Steps P host ⟨t, f, a⟩ ⟨t', f', b⟩) (ha : a = a') (hb : b = b') :
    Steps P host ⟨t, f, a'⟩ ⟨t', f', b'⟩ := ha ▸ hb ▸ h

theorem transGen_congr {t t' : Store H} {f f' : Frame} {a a' b b' : List Admin}
    (h : Relation.TransGen (Step P host) ⟨t, f, a⟩ ⟨t', f', b⟩) (ha : a = a') (hb : b = b') :
    Relation.TransGen (Step P host) ⟨t, f, a'⟩ ⟨t', f', b'⟩ := ha ▸ hb ▸ h

theorem transGen_append_right {t t' : Store H} {f f' : Frame} {a b : List Admin}
    (h : Relation.TransGen (Step P host) ⟨t, f, a⟩ ⟨t', f', b⟩) (rest : List Admin) :
    Relation.TransGen (Step P host) ⟨t, f, a ++ rest⟩ ⟨t', f', b ++ rest⟩ := by
  have step : ∀ {c d : Config H}, Step P host c d →
      Step P host ⟨c.store, c.frame, c.code ++ rest⟩ ⟨d.store, d.frame, d.code ++ rest⟩ := by
    intro c d hc
    obtain ⟨_, _, _⟩ := c
    obtain ⟨_, _, _⟩ := d
    exact Step.append_right hc rest
  have key : ∀ {c d : Config H}, Relation.TransGen (Step P host) c d →
      Relation.TransGen (Step P host) ⟨c.store, c.frame, c.code ++ rest⟩
        ⟨d.store, d.frame, d.code ++ rest⟩ := by
    intro c d hcd
    induction hcd with
    | single hs => exact .single (step hs)
    | tail _ hs ih => exact ih.tail (step hs)
  exact key h

theorem exitCut_not_all {x y : List Admin} (h : ExitCut x y) :
    x.all Admin.isVal = false := by
  obtain ⟨us, ws, k, x', y', hk, rfl, rfl⟩ := h
  rcases hk with rfl | ⟨a, rfl⟩ <;> simp [List.all_append, Admin.isVal, Admin.val?, throwing]

/-- A segmented pair whose left side is all values: the right side runs to the
same values (`BaseSim.values` on base pairs). -/
theorem run_vals (hB : BaseFacts P host F BI B rank) :
    ∀ {x y : List Admin}, Segs BI (WithCuts B) x y → x.all Admin.isVal = true →
    ∀ {s t : Store H} {f : Frame} (W : List Val), StoreRel F s t →
    ∃ t', Steps P host ⟨t, f, vals W ++ y⟩ ⟨t', f, vals W ++ x⟩ ∧ StoreRel F s t' := by
  intro x y h
  induction h with
  | nil => intro _ s t f W hst; exact ⟨t, .refl, hst⟩
  | @cons xs ys xr yr hs _ ih =>
    intro hall s t f W hst
    rw [List.all_append, Bool.and_eq_true] at hall
    obtain ⟨hxs, hxr⟩ := hall
    obtain ⟨u, hu⟩ := exists_vals_of_all hxs
    -- the head segment runs to `vals u`
    obtain ⟨t₁, h₁, hst₁⟩ : ∃ t₁, Steps P host ⟨t, f, vals W ++ ys⟩ ⟨t₁, f, vals W ++ xs⟩ ∧
        StoreRel F s t₁ := by
      cases hs with
      | @one a b hab =>
        obtain ⟨v, hv⟩ : ∃ v, a.val? = some v := by
          cases ha : a.val? with
          | none => simp [List.all_cons, Admin.isVal, ha] at hxs
          | some v => exact ⟨v, rfl⟩
        obtain rfl := hab.eq_of_val hv
        exact ⟨t, .refl, hst⟩
      | base hb =>
        rcases hb with hb | hcut
        · subst hu
          exact hB.values hst hb rfl
        · exact absurd (exitCut_not_all hcut) (by simp [hxs])
    subst hu
    obtain ⟨t₂, h₂, hst₂⟩ := ih hxr (f := f) (W ++ u) hst₁
    refine ⟨t₂, ?_, hst₂⟩
    have h₁' := Steps.append_right h₁ yr
    dsimp only at h₁'
    exact Relation.ReflTransGen.trans (b := ⟨t₁, f, vals (W ++ u) ++ yr⟩)
      (steps_congr h₁' (by simp) (by simp)) (steps_congr h₂ rfl (by simp))

/-- **First active segment.** In a segmented pair whose left side is not all
values, find the first segment whose left side is not all values; the right side
runs its prefix to the same values. -/
theorem split_active (hB : BaseFacts P host F BI B rank) :
    ∀ {x y : List Admin}, Segs BI (WithCuts B) x y → x.all Admin.isVal = false →
    ∀ {s t : Store H} {f : Frame} (W : List Val), StoreRel F s t →
    ∃ (V : List Val) (xs ys xr yr : List Admin) (t' : Store H),
      x = vals V ++ xs ++ xr ∧ Seg BI (WithCuts B) xs ys ∧ xs.all Admin.isVal = false ∧
      Segs BI (WithCuts B) xr yr ∧
      Steps P host ⟨t, f, vals W ++ y⟩ ⟨t', f, vals W ++ vals V ++ ys ++ yr⟩ ∧
      StoreRel F s t' := by
  intro x y h
  induction h with
  | nil => intro h; simp at h
  | @cons xs ys xr yr hs hr ih =>
    intro hall s t f W hst
    by_cases hxs : xs.all Admin.isVal = true
    · have hxr : xr.all Admin.isVal = false := by
        simpa [List.all_append, hxs] using hall
      obtain ⟨t₁, h₁, hst₁⟩ := run_vals hB (Segs.single hs) hxs W hst
      obtain ⟨u, rfl⟩ := exists_vals_of_all hxs
      obtain ⟨V, xs', ys', xr', yr', t₂, rfl, hseg, hact, hr', h₂, hst₂⟩ :=
        ih hxr (f := f) (W ++ u) hst₁
      refine ⟨u ++ V, xs', ys', xr', yr', t₂, by simp, hseg, hact, hr', ?_, hst₂⟩
      have h₁' := Steps.append_right h₁ yr
      dsimp only at h₁'
      exact Relation.ReflTransGen.trans (b := ⟨t₁, f, vals (W ++ u) ++ yr⟩)
        (steps_congr h₁' (by simp) (by simp)) (steps_congr h₂ rfl (by simp))
    · refine ⟨[], xs, ys, xr, yr, t, by simp [vals_nil'], hs, by simpa using hxs, hr, ?_, hst⟩
      exact steps_congr .refl rfl (by simp [vals_nil'])

/-- **Exit lift** (inlined here; `Sim/ExitLift.lean` imports this file). If the
left side of a segmented pair is in exit shape `val* k j`, the right side runs to
the same exit kernel after the same values (any values for `trap` and a thrown
exception, which the exit cuts allow to differ), keeping its frame. -/
theorem exit_lift (hB : BaseFacts P host F BI B rank) {x y : List Admin}
    (hxy : Segs BI (WithCuts B) x y) {s t : Store H} {f : Frame} (hst : StoreRel F s t)
    (W : List Val) {us : List Val} {k j : List Admin} (hk : Exit k) (hx : x = vals us ++ k ++ j) :
    ∃ (t' : Store H) (us' : List Val) (j' : List Admin),
      Steps P host ⟨t, f, vals W ++ y⟩ ⟨t', f, vals W ++ vals us' ++ k ++ j'⟩ ∧
      StoreRel F s t' ∧ (us' = us ∨ k = [.trap] ∨ ∃ a, k = throwing a) := by
  obtain ⟨pre, e, he, hke⟩ := hk.eq_vals_append
  have hx' : x = vals (us ++ pre) ++ e :: j := by rw [hx, hke]; simp
  have hna : x.all Admin.isVal = false := by
    rw [hx']; simp [List.all_append, Admin.isVal, he]
  obtain ⟨V, xs, ys, xr, yr, t₁, hxV, hseg, hact, hr, hrun, hst₁⟩ :=
    split_active hB hxy hna W hst
  obtain ⟨hflat, hctx⟩ := hk.head_flat (BI := BI) hke
  cases hseg with
  | @one a b hab =>
    have ha : a.val? = none := by simpa [Admin.isVal] using hact
    have hj : vals V ++ a :: xr = vals (us ++ pre) ++ e :: j := by rw [← hx', hxV]; simp
    obtain ⟨hV, rfl, rfl⟩ := vals_append_cons_inj ha he hj
    obtain rfl := hab.eq_of_flat hflat hctx
    exact ⟨t₁, us, yr, steps_congr hrun rfl (by rw [hV, hke]; simp), hst₁, Or.inl rfl⟩
  | base hb =>
    obtain ⟨u₁, e', xs₁, he', rfl⟩ := exists_head_of_not_all hact
    have hj : vals (V ++ u₁) ++ e' :: (xs₁ ++ xr) = vals (us ++ pre) ++ e :: j := by
      rw [← hx', hxV]; simp
    obtain ⟨hVu, he'e, -⟩ := vals_append_cons_inj he' he hj
    subst e'
    rcases hb with hb | ⟨cu, cw, ck, cx, cy, hck, hcx, rfl⟩
    · have heq : vals (W ++ V) ++ (vals u₁ ++ e :: xs₁) = vals (W ++ us) ++ k ++ xs₁ := by
        rw [hke, show vals (W ++ V) ++ (vals u₁ ++ e :: xs₁) =
          vals W ++ vals (V ++ u₁) ++ e :: xs₁ by simp, hVu]
        simp
      obtain ⟨t₂, j', h₂, hst₂⟩ := hB.exit (f := f) hst₁ hb hk heq
      have h₂' := Steps.append_right h₂ yr
      dsimp only at h₂'
      exact ⟨t₂, us, j' ++ yr, Relation.ReflTransGen.trans hrun
        (steps_congr h₂' (by simp) (by simp)), hst₂, Or.inl rfl⟩
    · obtain ⟨htrap, hthrow⟩ := hk.eq_of_head hke
      rcases hck with rfl | ⟨a', rfl⟩
      · have hc' : vals u₁ ++ e :: xs₁ = vals cu ++ Admin.trap :: cx := by rw [hcx]; simp
        obtain ⟨-, rfl, -⟩ := vals_append_cons_inj he val?_trap hc'
        have hk' := htrap rfl
        refine ⟨t₁, V ++ cw, cy ++ yr, steps_congr hrun rfl (by rw [hk']; simp), hst₁,
          Or.inr (Or.inl hk')⟩
      · have hc' : vals u₁ ++ e :: xs₁ = vals (cu ++ [.ref (.exn a')]) ++
            Admin.plain .throwRef :: cx := by
          rw [hcx]; simp [vals, throwing, Val.toAdmin]
        obtain ⟨hu₁, rfl, -⟩ := vals_append_cons_inj he val?_throwRef hc'
        obtain ⟨a, rfl, rfl⟩ := hthrow rfl
        have hVu' : us ++ [.ref (.exn a)] = (V ++ cu) ++ [.ref (.exn a')] := by
          rw [← hVu, hu₁]; simp
        have ha' : a = a' := by simpa using (List.append_inj' hVu' rfl).2
        subst ha'
        exact ⟨t₁, V ++ cw, cy ++ yr, steps_congr hrun rfl (by simp), hst₁,
          Or.inr (Or.inr ⟨a, rfl⟩)⟩

/-- A partial `trap`/`throw_ref` discard, or any step of an exit-cut pair: the left
stays in exit shape with smaller code; the right stutters and the pair is a cut. -/
theorem cut_case [LawfulCodeRank rank] {s t s' : Store H} {f f' : Frame} {U W : List Val}
    {k X Y x y es' : List Admin} (hk : k = [.trap] ∨ ∃ a, k = throwing a)
    (hst : StoreRel F s t) (hx : x = vals U ++ k ++ X) (hy : y = vals W ++ k ++ Y)
    (h : Step P host ⟨s, f, x⟩ ⟨s', f', es'⟩) :
    RankedMatched rank P host F BI B ⟨s', f', es'⟩ ⟨t, f, y⟩ (rank x) := by
  subst hx hy
  obtain ⟨rfl, rfl, ⟨U', X', rfl⟩, hlt⟩ := Step.exitShape_cut_rank (rank := rank) hk h
  exact ⟨⟨t, _, vals W ++ k ++ Y⟩, Or.inr ⟨rfl, hlt⟩,
    ⟨hst, rfl, AdminsRel.base (Or.inr ⟨U', W, k, X', Y, hk, rfl, rfl⟩)⟩⟩

/-- An unchanged head that is neither a context nor a call: `Step.transport_storeRel`,
lifted through the value prefix and the related suffix. -/
theorem transport_lift {s t s' : Store H} {f f' : Frame} {ws us : List Val} {a : Admin}
    {is' L L' : List Admin} (hst : StoreRel F s t) (hctx : ¬ a.IsCtx) (hcall : ¬ a.IsCallRef)
    (hL : AdminsRel BI (WithCuts B) L L')
    (h : Step P host ⟨s, f, vals us ++ [a]⟩ ⟨s', f', is'⟩) (m : Nat) :
    RankedMatched rank P host F BI B ⟨s', f', vals ws ++ is' ++ L⟩ ⟨t, f, vals (ws ++ us) ++ [a] ++ L'⟩ m := by
  obtain ⟨t', ht', hst'⟩ := Step.transport_storeRel hst hctx hcall h
  refine ⟨⟨t', f', vals ws ++ is' ++ L'⟩, Or.inl (.single ?_), hst', rfl,
    (AdminsRel.refl _).append hL⟩
  have := Step.append_right (Step.vals_left ht' ws) L'
  rwa [show vals ws ++ (vals us ++ [a]) ++ L' = vals (ws ++ us) ++ [a] ++ L' by simp] at this

end Closure

end Silmaril.Wasm.Execution.Core.Sim
