module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Main
public import Silmaril.Wasm.Binaryen.Behaviour

@[expose] public section

/-! # Simulation under address maps: observations

Related instantiations have the same module observations (`obs_sim`): the
instantiation run, the export invocations (looked up by name) and their
results are simulated in lockstep.
-/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

/-- Exports of the two module instances, related by name. -/
structure ExportsRel (X : SimCtx) : Prop where
  fwd : ∀ x a, exportFunc? X.MA x = some a → ∃ b, exportFunc? X.MB x = some b ∧ X.F a b
  bwd : ∀ x b, exportFunc? X.MB x = some b → ∃ a, exportFunc? X.MA x = some a

theorem valOk_num {S : Store H} {v : Val} {t : NumType} (h : ValOk S v (.num t)) :
    ∃ n, v = .num n := by
  generalize hT : (.num t : CValType) = T at h
  cases h with
  | num n => exact ⟨n, rfl⟩
  | vec => cases hT
  | ref => cases hT

theorem valOk_num_transfer {S T : Store H} {v : Val} {t : NumType} (h : ValOk S v (.num t)) :
    ValOk T v (.num t) := by
  obtain ⟨n, rfl⟩ := valOk_num h
  generalize hT : (.num t : CValType) = T' at h ⊢
  cases h with
  | num n => exact .num n

theorem forall₂_valOk_num {S T : Store H} {n0 : Nat} :
    ∀ {vs : List Val} {ps : List CValType}, (∀ p ∈ ps, ∃ t, p = .num t) →
    List.Forall₂ (ValOk S) vs ps → (∀ v ∈ vs, valF n0 v) ∧ List.Forall₂ (ValOk T) vs ps
  | [], [], _, .nil => ⟨by simp, .nil⟩
  | v :: vs, p :: ps, hp, .cons h t => by
    obtain ⟨t', rfl⟩ := hp p (by simp)
    obtain ⟨n, rfl⟩ := valOk_num h
    obtain ⟨h1, h2⟩ := forall₂_valOk_num (T := T) (n0 := n0) (fun q hq => hp q (by simp [hq])) t
    refine ⟨?_, .cons (valOk_num_transfer h) h2⟩
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · trivial
    · exact h1 w hw

theorem FuncPair.fwd {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {a b : Nat}
    (hab : X.F a b) {fi : FuncInst H} (h : S.funcs[a]? = some fi) :
    ∃ fi', T.funcs[b]? = some fi' ∧ fi'.type = fi.type := by
  rcases hS.fpair a b hab with ⟨ha, rfl⟩ | ⟨-, -, fA, fB, cA, cB, h1, h2, h3, -⟩
  · exact ⟨fi, hS.func_lo ha h, rfl⟩
  · rw [h] at h1
    cases h1
    exact ⟨fB, h2, h3.symm⟩

theorem FuncPair.bwd {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {a b : Nat}
    (hab : X.F a b) {fi' : FuncInst H} (h : T.funcs[b]? = some fi') :
    ∃ fi, S.funcs[a]? = some fi ∧ fi.type = fi'.type := by
  rcases hS.fpair a b hab with ⟨ha, rfl⟩ | ⟨-, -, fA, fB, cA, cB, h1, h2, h3, -⟩
  · exact ⟨fi', by rw [hS.funcs _ ha]; exact h, rfl⟩
  · rw [h] at h2
    cases h2
    exact ⟨fA, h1, h3⟩

theorem invokeOk_fwd {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {a b : Nat}
    (hab : X.F a b) {vs : List Val} (h : InvokeOk S a vs) :
    InvokeOk T b vs ∧ ∀ v ∈ vs, valF X.n0 v := by
  obtain ⟨fi, ps, rs, hfi, hexp, hvs⟩ := h
  obtain ⟨fi', hfi', hty⟩ := FuncPair.fwd hS hab hfi
  obtain ⟨h1, h2⟩ := forall₂_valOk_num (T := T) (n0 := X.n0) (hS.intp a b hab fi hfi ps rs hexp) hvs
  exact ⟨⟨fi', ps, rs, hfi', hty ▸ hexp, h2⟩, h1⟩

theorem invokeOk_bwd {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {a b : Nat}
    (hab : X.F a b) {vs : List Val} (h : InvokeOk T b vs) : InvokeOk S a vs := by
  obtain ⟨fi', ps, rs, hfi', hexp, hvs⟩ := h
  obtain ⟨fi, hfi, hty⟩ := FuncPair.bwd hS hab hfi'
  have hexp' : Expand fi.type (.func ps rs) := hty ▸ hexp
  obtain ⟨-, h2⟩ := forall₂_valOk_num (T := S) (n0 := X.n0) (hS.intp a b hab fi hfi ps rs hexp') hvs
  exact ⟨fi, ps, rs, hfi, hexp', h2⟩

theorem frameS_empty (X : SimCtx) : FrameS X ({} : Frame) :=
  ⟨⟨fun _ h => by simp at h, fun _ h => by simp at h⟩, fun _ h => by simp at h⟩

theorem invoke_rel {X : SimCtx} {S T : Store H} (hS : StoreRel X S T) {a b : Nat}
    (hab : X.F a b) {vs : List Val} (hvs : ∀ v ∈ vs, valF X.n0 v) :
    ConfRel X .same (invoke S a vs) (invoke T b vs) := by
  have hty : (S.funcs[a]?.map FuncInst.type).getD default =
      (T.funcs[b]?.map FuncInst.type).getD default := by
    cases h : S.funcs[a]? with
    | none =>
      cases h' : T.funcs[b]? with
      | none => rfl
      | some fi' =>
        obtain ⟨fi, hfi, -⟩ := FuncPair.bwd hS hab h'
        rw [h] at hfi
        cases hfi
    | some fi =>
      obtain ⟨fi', hfi', hty⟩ := FuncPair.fwd hS hab h
      rw [hfi']
      simp [hty]
  refine ⟨hS, ⟨rfl, frameS_empty X⟩, ?_⟩
  simp only [invoke]
  rw [hty]
  exact CodeR.append (CodeR.ofVals hvs) (CodeR.pair hab .nil)

/-- Sessions of related stores. -/
theorem session_sim {X : SimCtx} (hX : X.WF) (hE : ExportsRel X) {S T : Store H}
    (hS : StoreRel X S T) {script : List Call} {bs : List (Behaviour Val)}
    (h : Session P closedHost X.MA S script bs) : Session P closedHost X.MB T script bs := by
  induction h generalizing T with
  | nil => exact .nil
  | stop hno =>
    refine .stop fun b hb hinv => ?_
    obtain ⟨a, ha⟩ := hE.bwd _ _ hb
    obtain ⟨b', hb', hab⟩ := hE.fwd _ _ ha
    rw [hb] at hb'
    cases hb'
    exact hno a ha (invokeOk_bwd hS hab hinv)
  | done ha hok run hr tail ih =>
    obtain ⟨b, hb, hab⟩ := hE.fwd _ _ ha
    obtain ⟨hok', hvs⟩ := invokeOk_fwd hS hab hok
    obtain ⟨d', hrun', hrel⟩ := sim_steps hX run (invoke_rel hS hab hvs)
    exact .done hb hok' hrun' (hrel.result hr) (ih hrel.1)
  | diverge ha hok hd =>
    obtain ⟨b, hb, hab⟩ := hE.fwd _ _ ha
    obtain ⟨hok', hvs⟩ := invokeOk_fwd hS hab hok
    exact .diverge hb hok' (sim_diverges hX hd (invoke_rel hS hab hvs))

/-- **Observations of related instantiations are equal.** -/
theorem obs_sim {s : Store H} {xas : List ExternAddr} {MA MB : Module} {script : List Call}
    (hinst : ∀ c, Instantiate P closedHost s MA xas c → ∃ (X : SimCtx) (c' : Config H), X.WF ∧
      ExportsRel X ∧ Instantiate P closedHost s MB xas c' ∧ ConfRel X .ours c c' ∧
      c.frame.module = X.MA ∧ c'.frame.module = X.MB) :
    ∀ bs ∈ moduleObs P closedHost s xas MA script, bs ∈ moduleObs P closedHost s xas MB script := by
  rintro bs ⟨c, hc, hcase⟩
  obtain ⟨X, c', hX, hE, hc', hrel, hmA, hmB⟩ := hinst c hc
  refine ⟨c', hc', ?_⟩
  rcases hcase with ⟨c₁, bs', hst, hcode, hses, rfl⟩ | ⟨c₁, r, hst, hcode, hr, rfl⟩ | ⟨hd, rfl⟩
  · obtain ⟨d, hst', hrel'⟩ := sim_steps hX hst hrel
    refine .inl ⟨d, bs', hst', hrel'.result (r := .values []) hcode, ?_, rfl⟩
    rw [hmB]
    rw [hmA] at hses
    exact session_sim hX hE hrel'.1 hses
  · obtain ⟨d, hst', hrel'⟩ := sim_steps hX hst hrel
    exact .inr (.inl ⟨d, r, hst', hrel'.result hcode, hr, rfl⟩)
  · exact .inr (.inr ⟨sim_diverges hX hd hrel, rfl⟩)

end Silmaril.Wasm.Binaryen.RUMESim
