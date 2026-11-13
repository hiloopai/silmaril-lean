module

public import Silmaril.Proofs.Wasm.Game.ULink.CmpPos
public import Silmaril.Proofs.Wasm.Game.ULink.Backward
public import Silmaril.Proofs.Wasm.Game.Untyped.Typing
public import Silmaril.Proofs.Wasm.Game.Untyped.Runs

/-!
# Closed programs: the layout is an invariant

Against an environment `Lenv`, the linked closed system `LC = (Lenv.dlts q₀).comp (L.U.lts P)`
and the composite closed system `CC = (Lenv.dlts q₀).comp (Cmp L P)` are compared during one
export call `f`, with no per-play hypothesis: the stores of the hidden plays have the link's
layout because

* the export call starts in a store with the layout whose stubbed functions exist (`CHyp`);
* host-free steps keep the functions (`slay_tau`);
* every environment answer is to a **well-typed** call (the run invariant `UGood` of
  `Silmaril.Proofs.Wasm.Game.Untyped.Typing` along the product run related by `URel`), so by
  `UEnvOk` its store extends the caller's (`Extend` keeps provider code), and by
  `EnvNoStub` it has no stub-coded host function (`ans_layout`).

`CF`/`CB` pair the forward and backward simulations `FRel`/`BRel` with equal environment states
and this invariant (`Good`) on the linked side. Hence (`cc_responds_of_lc`, `lc_responds_of_cc`,
`div_iff`) the observations of the two closed programs agree.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-! ### Silent runs -/

section Silent

universe u

variable {E F : Sig.{u}} {X : LTS E F}

/-- A silent run is a chain of silent steps. -/
theorem rtg_of_run_nil {a b : X.State} {p : List (Move E F)} (h : X.Run a p b) (hp : p = []) :
    Relation.ReflTransGen X.Silent a b := by
  induction h with
  | nil => exact .refl
  | tau hs _ ih => exact .head hs (ih hp)
  | vis _ _ _ => cases hp

/-- A chain of silent steps is a silent run. -/
theorem run_nil_of_transGen {a b : X.State} (h : Relation.TransGen X.Silent a b) : X.Run a [] b := by
  induction h with
  | single h => exact .tau h (.nil _)
  | tail _ h ih => exact ih.append (.tau h (.nil _))

end Silent

/-! ### Store growth keeps the layout -/

section Layout

variable {L : ULink}

/-- Stubbed functions stay functions as the store grows. -/
theorem stubsIn_extend {s s' : Store Nat} (h : L.StubsIn s) (he : Extend s s') : L.StubsIn s' :=
  fun a k c hs => Nat.lt_of_lt_of_le (h a k c hs) he.funcs.1

/-- **Store growth keeps the layout**, when no stub-coded host function appears. -/
theorem layout_extend {s s' : Store Nat} (hl : L.Layout s) (hin : L.StubsIn s) (he : Extend s s')
    (hns : L.NoStub s') : L.Layout s' := by
  refine ⟨fun a fi k c ha hs => ?_, hns⟩
  have h₀ : s.funcs[a]? = some (s.funcs[a]'(hin a k c hs)) := List.getElem?_eq_getElem _
  have hc₀ : (s.funcs[a]'(hin a k c hs)).code = .wasm c := hl.prov a _ k c h₀ hs
  obtain ⟨fi₁, h₁, hext⟩ := he.funcs.get h₀
  have hfi : fi₁ = fi := Option.some.inj (h₁.symm.trans ha)
  exact hfi ▸ hext.2.2.1 c hc₀

/-- The store layout of a state of the linked module. -/
def SLay (L : ULink) : L.U.State → Prop
  | .idle => True
  | .running _ s _ => L.Layout s
  | .waiting _ s _ _ => L.Layout s

/-- Host-free steps keep the functions. -/
theorem internalP_funcs {P : Profile} {s s' : Store Nat} {t t' : Thread}
    (h : InternalP P (s, t) (s', t')) : s'.funcs = s.funcs := by
  obtain ⟨f', code', -, hstep⟩ := h
  have hf : s'.funcs = (t.config s).store.funcs := (Step.framesLocal hstep).1
  rw [hf, Thread.config_store]

/-- Silent linked steps keep the store layout. -/
theorem slay_tau {P : Profile} {y y' : L.U.State} (hy : SLay L y) (hs : (L.U.lts P).step y none y') :
    SLay L y' := by
  cases hs with
  | tau h => exact Layout.of_funcs hy (internalP_funcs h)

/-- Visible linked steps keep the store layout when the move has it. -/
theorem slay_vis {P : Profile} {y y' : L.U.State} {m : Move UImp L.U.F} (hy : SLay L y)
    (hm : L.MoveLayout m) (hs : (L.U.lts P).step y (some m) y') : SLay L y' := by
  cases hs with
  | call f => exact hm
  | ucall => exact hy
  | uret a => exact hm
  | oret => trivial

/-- A linked answer from a state with the layout is in a store with the layout. -/
theorem ans_store_layout {P : Profile} {y y' : L.U.State} {g : L.U.F.Op} {a : UReply}
    (hy : SLay L y) (hs : (L.U.lts P).step y (some (.inr (.ans g a))) y') : L.Layout a.store := by
  cases hs with
  | oret => exact hy

end Layout

/-! ### The closed systems and the invariant -/

/-- The linked closed system. -/
abbrev LC (L : ULink) (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) : LTS Sig.empty L.U.F :=
  Untyped.Cmp L.U P Lenv q₀

/-- The composite closed system. -/
abbrev CC (L : ULink) (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) : LTS Sig.empty L.U.F :=
  (Lenv.dlts q₀).comp (Cmp L P)

/-- The hypotheses on the export call and the environment. -/
structure CHyp (L : ULink) (Lenv : SEnv UImp) (f : L.U.F.Op) (ps rs : Ty (.list .val)) : Prop where
  call : L.U.CallOk f ps rs
  env : UEnvOk f.store Lenv
  noStub : L.EnvNoStub Lenv
  stubsIn : L.StubsIn f.store
  layout : L.Layout f.store

variable {L : ULink} {P : Profile} {Lenv : SEnv UImp} {q₀ : Lenv.S} {f : L.U.F.Op}
  {ps rs : Ty (.list .val)}

/-- The invariant of the linked closed system during the export call `f`: a related product run
of the call, and the store layout. -/
def Good (L : ULink) (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) (f : L.U.F.Op)
    (z : (LC L P Lenv q₀).State) : Prop :=
  (∃ cq, USteps P Lenv (invoke f.store (L.U.addr f.target) f.args, q₀) cq ∧ Untyped.URel f cq z) ∧
    SLay L z.2

/-- A related state with a pending environment question waits at its callout. -/
theorem urel_waiting {cq : Config Nat × Lenv.S} {qs : Lenv.S} {e : UCall Nat} {y : L.U.State}
    (hc : Untyped.URel (P := P) (q₀ := q₀) f cq ((qs, some e), y)) :
    ∃ (s : Store Nat) (t : Thread) (h : Nat) (args : List Val), e = ⟨h, s, args⟩ ∧
      y = .waiting f s t ⟨h, s, args⟩ ∧ cq.1 = t.config s ∧ CalloutAt s t h args := by
  rcases hc with ⟨s, t, hx, -⟩ | ⟨s, t, h, args, hx, hct, hco⟩
  · have hne : (some e : Option (UCall Nat)) = none := congrArg (fun z => z.1.2) hx
    cases hne
  · have he : e = ⟨h, s, args⟩ := Option.some.inj (congrArg (fun z => z.1.2) hx)
    have hy : y = .waiting f s t ⟨h, s, args⟩ := congrArg Prod.snd hx
    exact ⟨s, t, h, args, he, hy, hct, hco⟩

/-- **Environment answers have the layout.** The call is well typed (the run invariant), so the
answer's store extends the caller's, and it has no stub codes. -/
theorem ans_layout (hc : CHyp L Lenv f ps rs) {qs qs' : Lenv.S} {e : UCall Nat} {y : L.U.State}
    (hg : Good L P Lenv q₀ f ((qs, some e), y)) {a : UReply} (hans : Lenv.Ans qs e a qs') :
    L.Layout a.store := by
  obtain ⟨⟨cq, hrun, hcq⟩, hsl⟩ := hg
  obtain ⟨s, t, h, args, rfl, rfl, hct, hco⟩ := urel_waiting hcq
  have hgood : Untyped.UGood f.store rs.toList cq.1 :=
    Untyped.uGood_uSteps hc.env (Untyped.uGood_invoke hc.call) hrun
  have hstore : cq.1.store = s := by rw [hct, Thread.config_store]
  obtain ⟨E, fa, hd⟩ := hco
  have hd' : decompose? cq.1.store cq.1.code = some (E, fa, h, args) := by
    rw [hstore, hct]
    exact hd
  obtain ⟨ps', rs', hcall⟩ := Untyped.callsHost_of_decompose P hgood.ok hd'
  have hext : Extend f.store s := hstore ▸ hgood.ext
  have hcall' : (⟨h, s, args⟩ : UCall Nat).CallsHost ps' rs' := hstore ▸ hcall
  have hok : a.OkFor s rs' := hc.env qs ⟨h, s, args⟩ a qs' ps' rs' hext hcall' hans
  have hls : L.Layout s := hsl
  exact layout_extend hls (stubsIn_extend hc.stubsIn hext) hok.2.1 (hc.noStub qs _ a qs' hans hls.noStub)

/-- The lower move of a synchronisation with the environment has the layout. -/
theorem env_move_layout (hc : CHyp L Lenv f ps rs) {ê ê' : Lenv.S × Option (UCall Nat)}
    {y : L.U.State} (hg : Good L P Lenv q₀ f (ê, y)) {g : Ev UImp}
    (hk : (Lenv.dlts q₀).step ê (some (.inr g)) ê') : L.MoveLayout (.inl g : Move UImp L.U.F) := by
  cases hk with
  | ask q e => trivial
  | ans hans => exact ans_layout hc hg hans

/-- **Silent linked closed steps keep the invariant.** -/
theorem good_tau (hc : CHyp L Lenv f ps rs) {z z' : (LC L P Lenv q₀).State}
    (hg : Good L P Lenv q₀ f z) (hs : (LC L P Lenv q₀).step z none z') : Good L P Lenv q₀ f z' := by
  obtain ⟨⟨cq, hrun, hcq⟩, hsl⟩ := hg
  obtain ⟨cq', hrun', hcq'⟩ := Untyped.uSteps_of_silent f hcq hs
  refine ⟨⟨cq', hrun.trans hrun', hcq'⟩, ?_⟩
  rcases z with ⟨ê, y⟩
  cases hs with
  | tau₁ hk => exact hsl
  | tau₂ hi => exact slay_tau hsl hi
  | sync g hk hi => exact slay_vis hsl (env_move_layout hc ⟨⟨cq, hrun, hcq⟩, hsl⟩ hk) hi

/-! ### Forward: the composite closed system in the linked one -/

/-- The forward closed relation. -/
def CF (L : ULink) (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) (f : L.U.F.Op)
    (x : (CC L P Lenv q₀).State) (z : (LC L P Lenv q₀).State) : Prop :=
  x.1 = z.1 ∧ FRel L x.2 z.2 ∧ Good L P Lenv q₀ f z

/-- **Silent composite closed steps.** -/
theorem cf_tau (hc : CHyp L Lenv f ps rs) {x x' : (CC L P Lenv q₀).State}
    {z : (LC L P Lenv q₀).State} (hR : CF L P Lenv q₀ f x z) (hs : (CC L P Lenv q₀).step x none x') :
    (∃ z', (LC L P Lenv q₀).step z none z' ∧ CF L P Lenv q₀ f x' z') ∨
      (CF L P Lenv q₀ f x' z ∧ rank x'.2 < rank x.2) := by
  rcases x with ⟨ê, xc⟩
  rcases z with ⟨ê', y⟩
  obtain ⟨he, hF, hg⟩ := hR
  have he' : ê = ê' := he
  subst he'
  cases hs with
  | tau₁ hk =>
    have hz : (LC L P Lenv q₀).step (ê, y) none (_, y) := .tau₁ hk
    exact .inl ⟨_, hz, rfl, hF, good_tau hc hg hz⟩
  | tau₂ hcs =>
    rcases sim_tau hF hcs with ⟨y', hy, hF'⟩ | ⟨hF', hlt⟩
    · have hz : (LC L P Lenv q₀).step (ê, y) none (ê, y') := .tau₂ hy
      exact .inl ⟨_, hz, rfl, hF', good_tau hc hg hz⟩
    · exact .inr ⟨⟨rfl, hF', hg⟩, hlt⟩
  | sync g hk hcs =>
    obtain ⟨y', hy, hF'⟩ := sim_vis hF hcs rfl (env_move_layout hc hg hk)
    have hz : (LC L P Lenv q₀).step (ê, y) none (_, y') := .sync g hk hy
    exact .inl ⟨_, hz, rfl, hF', good_tau hc hg hz⟩

/-- Silent composite closed runs are silent linked closed runs. -/
theorem cf_run_nil (hc : CHyp L Lenv f ps rs) {x x' : (CC L P Lenv q₀).State}
    {p : List (Move Sig.empty L.U.F)} (h : (CC L P Lenv q₀).Run x p x') (hp : p = []) :
    ∀ z, CF L P Lenv q₀ f x z → ∃ z', (LC L P Lenv q₀).Run z [] z' ∧ CF L P Lenv q₀ f x' z' := by
  induction h with
  | nil x => exact fun z hR => ⟨z, .nil _, hR⟩
  | tau hs _ ih =>
    intro z hR
    rcases cf_tau hc hR hs with ⟨z₁, hz, hR₁⟩ | ⟨hR₁, -⟩
    · obtain ⟨z', hr, hR'⟩ := ih hp z₁ hR₁
      exact ⟨z', .tau hz hr, hR'⟩
    · exact ih hp z hR₁
  | vis _ _ _ => cases hp

/-- **Composite closed divergence is linked closed divergence.** -/
theorem cf_diverges (hc : CHyp L Lenv f ps rs) {x : (CC L P Lenv q₀).State}
    {z : (LC L P Lenv q₀).State} (hR : CF L P Lenv q₀ f x z) (hd : (CC L P Lenv q₀).Diverges x) :
    (LC L P Lenv q₀).Diverges z := by
  refine InfiniteTrace.coinduct
    (fun z => ∃ x, CF L P Lenv q₀ f x z ∧ (CC L P Lenv q₀).Diverges x) ?_ ⟨x, hR, hd⟩
  rintro z ⟨x, hR, hd⟩
  induction hn : rank x.2 using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
    rcases cf_tau hc hR hs with ⟨z₁, hz, hR₁⟩ | ⟨hR₁, hlt⟩
    · exact ⟨z₁, hz, x₁, hR₁, hd₁⟩
    · exact ih (rank x₁.2) (hn ▸ hlt) x₁ hR₁ hd₁ rfl

/-! ### Backward: the linked closed system in the composite one -/

/-- The backward closed relation. -/
def CB (L : ULink) (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) (f : L.U.F.Op)
    (z : (LC L P Lenv q₀).State) (x : (CC L P Lenv q₀).State) : Prop :=
  z.1 = x.1 ∧ BRel L z.2 x.2 ∧ Good L P Lenv q₀ f z

/-- Silent composite runs are silent composite closed runs. -/
theorem cc_run_nil' {ê : Lenv.S × Option (UCall Nat)} {a b : (Cmp L P).State}
    {p : List (Move UImp L.U.F)} (h : (Cmp L P).Run a p b) (hp : p = []) :
    (CC L P Lenv q₀).Run (ê, a) [] (ê, b) := by
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => exact .tau (.tau₂ hs) (ih hp)
  | vis _ _ _ => cases hp

/-- Silent composite runs are silent composite closed runs. -/
theorem cc_run_nil {ê : Lenv.S × Option (UCall Nat)} {a b : (Cmp L P).State}
    (h : (Cmp L P).Run a [] b) : (CC L P Lenv q₀).Run (ê, a) [] (ê, b) :=
  cc_run_nil' h rfl

/-- A composite run with one upper move is a composite closed run. -/
theorem cc_run_inr {ê : Lenv.S × Option (UCall Nat)} {a b : (Cmp L P).State} {g : Ev L.U.F}
    (h : (Cmp L P).Run a [.inr g] b) : (CC L P Lenv q₀).Run (ê, a) [.inr g] (ê, b) := by
  obtain ⟨a₁, a₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv h
  exact (cc_run_nil h₁).append (.vis (.right g h₂) (cc_run_nil h₃))

/-- Silent composite progress is silent composite closed progress. -/
theorem cc_transGen {ê : Lenv.S × Option (UCall Nat)} {a b : (Cmp L P).State}
    (h : Relation.TransGen (Cmp L P).Silent a b) :
    Relation.TransGen (CC L P Lenv q₀).Silent (ê, a) (ê, b) := by
  induction h with
  | single h => exact .single (.tau₂ h)
  | tail _ h ih => exact .tail ih (.tau₂ h)

/-- A synchronisation with the environment around a composite lower move is silent progress. -/
theorem cc_sync {ê ê' : Lenv.S × Option (UCall Nat)} {a b : (Cmp L P).State} {g : Ev UImp}
    (hk : (Lenv.dlts q₀).step ê (some (.inr g)) ê') (h : (Cmp L P).Run a [.inl g] b) :
    Relation.TransGen (CC L P Lenv q₀).Silent (ê, a) (ê', b) := by
  obtain ⟨a₁, a₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv h
  have r₁ : (CC L P Lenv q₀).Run (ê, a) [] (ê, a₁) := cc_run_nil h₁
  have r₃ : (CC L P Lenv q₀).Run (ê', a₂) [] (ê', b) := cc_run_nil h₃
  have hs : (CC L P Lenv q₀).Silent (ê, a₁) (ê', a₂) := .sync g hk h₂
  exact Relation.TransGen.trans_right (rtg_of_run_nil r₁ rfl)
    (Relation.TransGen.trans_left (.single hs) (rtg_of_run_nil r₃ rfl))

/-- **Silent linked closed steps.** -/
theorem cb_tau (hc : CHyp L Lenv f ps rs) {z z' : (LC L P Lenv q₀).State}
    {x : (CC L P Lenv q₀).State} (hR : CB L P Lenv q₀ f z x) (hs : (LC L P Lenv q₀).step z none z') :
    ∃ x', Relation.TransGen (CC L P Lenv q₀).Silent x x' ∧ CB L P Lenv q₀ f z' x' := by
  rcases x with ⟨ê, xc⟩
  rcases z with ⟨ê', y⟩
  obtain ⟨he, hB, hg⟩ := hR
  have he' : ê' = ê := he
  subst he'
  have hg' : Good L P Lenv q₀ f z' := good_tau hc hg hs
  cases hs with
  | tau₁ hk => exact ⟨_, .single (.tau₁ hk), rfl, hB, hg'⟩
  | tau₂ hi =>
    obtain ⟨xc', hx, hB'⟩ := bsim_tau hB hi
    exact ⟨(ê', xc'), cc_transGen hx, rfl, hB', hg'⟩
  | sync g hk hi =>
    obtain ⟨xc', hx, hB'⟩ := bsim_vis hB hi (env_move_layout hc hg hk)
    exact ⟨_, cc_sync hk hx, rfl, hB', hg'⟩

/-- Silent linked closed runs are silent composite closed runs. -/
theorem cb_run_nil (hc : CHyp L Lenv f ps rs) {z z' : (LC L P Lenv q₀).State}
    {p : List (Move Sig.empty L.U.F)} (h : (LC L P Lenv q₀).Run z p z') (hp : p = []) :
    ∀ x, CB L P Lenv q₀ f z x → ∃ x', (CC L P Lenv q₀).Run x [] x' ∧ CB L P Lenv q₀ f z' x' := by
  induction h with
  | nil z => exact fun x hR => ⟨x, .nil _, hR⟩
  | tau hs _ ih =>
    intro x hR
    obtain ⟨x₁, hx, hR₁⟩ := cb_tau hc hR hs
    obtain ⟨x', hr, hR'⟩ := ih hp x₁ hR₁
    exact ⟨x', (run_nil_of_transGen hx).append hr, hR'⟩
  | vis _ _ _ => cases hp

/-- **Linked closed divergence is composite closed divergence.** -/
theorem cb_diverges (hc : CHyp L Lenv f ps rs) {z : (LC L P Lenv q₀).State}
    {x : (CC L P Lenv q₀).State} (hR : CB L P Lenv q₀ f z x) (hd : (LC L P Lenv q₀).Diverges z) :
    (CC L P Lenv q₀).Diverges x := by
  refine InfiniteTrace.coinduct
    (fun x => ∃ x₁ z, Relation.ReflTransGen (CC L P Lenv q₀).Silent x x₁ ∧ CB L P Lenv q₀ f z x₁ ∧
      (LC L P Lenv q₀).Diverges z) ?_ ⟨x, z, .refl, hR, hd⟩
  rintro x ⟨x₁, z, hxx, hR, hd⟩
  rcases Relation.ReflTransGen.cases_head hxx with rfl | ⟨x', hx', hrest⟩
  · obtain ⟨z₁, hz, hd₁⟩ := hd.unfold
    obtain ⟨x₂, hx₂, hR₂⟩ := cb_tau hc hR hz
    obtain ⟨x', hx', hrest⟩ := Relation.TransGen.head'_iff.mp hx₂
    exact ⟨x', hx', x₂, z₁, hrest, hR₂, hd₁⟩
  · exact ⟨x', hx', x₁, z, hrest, hR, hd⟩

end Silmaril.Proofs.Wasm.Game.ULink
