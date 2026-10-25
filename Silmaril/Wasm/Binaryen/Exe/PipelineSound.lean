module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.Inline
public import Silmaril.Wasm.Binaryen.Exe.DCESound
public import Silmaril.Wasm.Binaryen.Exe.InlineCallee
public import Silmaril.Wasm.Binaryen.Exe.InlineCallCountsSound
public import Silmaril.Wasm.Binaryen.Exe.MergeBlocksAnySound
public import Silmaril.Wasm.Binaryen.Exe.VacuumStage
public import Silmaril.Wasm.Binaryen.Pass.SimplifyGlobalsSound
public import Silmaril.Wasm.Binaryen.Exe.PrecomputeStage
public import Silmaril.Wasm.Binaryen.Exe.CodeFoldingStage
public import Silmaril.Wasm.Binaryen.Exe.CoalesceLocalsStage
public import Silmaril.Wasm.Binaryen.Exe.RemoveUnusedBrsSound
public import Silmaril.Wasm.Binaryen.Exe.PeepholeStage
public import Silmaril.Wasm.Binaryen.Exe.SimplifyLocalsStage
public import Silmaril.Wasm.Binaryen.Exe.DirectizeStage
public import Silmaril.Wasm.Binaryen.Exe.ConstBranchStage
public import Silmaril.Wasm.Binaryen.Exe.ConstSelectStage
public import Silmaril.Wasm.Binaryen.Exe.AddChainStage

@[expose] public section

/-! # Soundness of the `binaryen-lean` pipeline, through the pass API

Kept apart from `Exe/Pipeline.lean` so that the executable does not import
`Inline.lean` (see the note there).

**Design.** Every stage of the executable pipeline is a `Pass` of the pass API
(`PassAPI/Pass.lean`) for one contract `ExeC o H`:

* semantic domain: `ExportEquiv Eq` under the closed host and the deterministic
  profile with grow oracle `o` (`equivDomain`, `PassAPI/Instances.lean`);
* IR: Binaryen modules with denotation `BModule.lower` (`birIR`);
* invariant `ExeInv`: the executable profile check `profileOk` holds and the
  module is valid (`BModule.Ok`).

A stage is `guardedP pass h`: `Pass.ofOption` of "run `pass`, keep the result only if
it passes `profileOk`", where `h : StageOk o H pass` proves that `pass` keeps validity
and is export-equivalent on `ExeInv` inputs. Its run function is the executable
`guarded pass` (`guardedP_run`).

The pipeline is a **product in the pass monoid**,
`pipelineP = inlineP budget * roundP ^ rounds * rumeP` with
`roundP = Pass.pipeline functionPassesP`, and the driver's size-guarded choice is
`Pass.best score [pipelineP 0 rounds, pipelineP inlineBudget rounds]`. Soundness of
the composite is `Pass.sound`: no composition proof beyond the monoid. The bridge to
the executable is two run-function equalities, `pipelineP_run` and `bestNamed_run`.

**Extension point.** `functionPassesP` maps the same `functionStageIds` as the
executable `functionStages`. A new identifier supplies its executable transformation
in `Exe/Pipeline.lean` and a `StageOk` certificate in `FunctionStageId.stageOk` below,
usually proved in a leaf file importing `Exe/StageContract.lean`.
`functionPassesP_run` checks that the two interpretations agree, and every theorem below is
unchanged. See `PassRegistry.lean`.

**Host side conditions.** `inlineSite_sound_noReturn` needs `HostRespectsCode` and
`HostOk` of the host. `closedHost` respects code (`closedHost_respectsCode`), but
`HostOk closedHost` holds only when the host-state type `H` is empty, so the inlining
stage assumes `H → False` (for example `H = Empty`).
-/

namespace Silmaril.Wasm.Binaryen.Exe

open Silmaril.Wasm Silmaril.Wasm.Binaryen Execution.Core Numerics Validation ModuleWf


/-! ## The executable copies are the originals -/

namespace Inl

-- The recursive copies are not definitionally unfolded by `rfl` (their compiled forms
-- differ in auxiliary constants), so they are compared through their equation lemmas.

theorem shiftLocalInstr_eq (base : Nat) (i : Instr) :
    Inl.shiftLocalInstr base i = Binaryen.shiftLocalInstr base i := by
  cases i <;> rfl

theorem labelIdx_eq (d : Nat) : Inl.labelIdx d = Binaryen.labelIdx d := rfl

theorem zeroInstr_eq : Inl.zeroInstr = Binaryen.zeroInstr := by
  funext t
  match t with
  | .num (.int _) => rfl
  | .num (.float _) => rfl
  | .vec _ => rfl
  | .ref _ => rfl

mutual
theorem shiftLocalsE_eq (base : Nat) :
    ∀ e : BExpr, Inl.shiftLocalsE base e = Binaryen.shiftLocalsE base e
  | .op i args => by
    rw [Inl.shiftLocalsE, Binaryen.shiftLocalsE, shiftLocalInstr_eq, shiftLocalsL_eq base args]
  | .block bt b => by rw [Inl.shiftLocalsE, Binaryen.shiftLocalsE, shiftLocalsL_eq base b]
  | .loop bt b => by rw [Inl.shiftLocalsE, Binaryen.shiftLocalsE, shiftLocalsL_eq base b]
  | .if_ bt c t e => by
    rw [Inl.shiftLocalsE, Binaryen.shiftLocalsE, shiftLocalsL_eq base c, shiftLocalsL_eq base t,
      shiftLocalsL_eq base e]
  | .tryTable bt cs b => by rw [Inl.shiftLocalsE, Binaryen.shiftLocalsE, shiftLocalsL_eq base b]
theorem shiftLocalsL_eq (base : Nat) :
    ∀ es : List BExpr, Inl.shiftLocalsL base es = Binaryen.shiftLocalsL base es
  | [] => by rw [Inl.shiftLocalsL, Binaryen.shiftLocalsL]
  | e :: es => by
    rw [Inl.shiftLocalsL, Binaryen.shiftLocalsL, shiftLocalsE_eq base e, shiftLocalsL_eq base es]
end

theorem retToBrE_op {d : Nat} {i : Instr} (hi : i ≠ .return_) (args : List BExpr) :
    Inl.retToBrE d (.op i args) = .op i (Inl.retToBrL d args) := by
  cases i <;> simp_all [Inl.retToBrE]

mutual
theorem retToBrE_eq (d : Nat) : ∀ e : BExpr, Inl.retToBrE d e = Binaryen.retToBrE d e
  | .op i args => by
    by_cases hi : i = .return_
    · subst hi
      rw [Inl.retToBrE, Binaryen.retToBrE, retToBrL_eq d args, labelIdx_eq]
    · rw [retToBrE_op hi, Binaryen.retToBrE_op hi, retToBrL_eq d args]
  | .block bt b => by rw [Inl.retToBrE, Binaryen.retToBrE, retToBrL_eq (d + 1) b]
  | .loop bt b => by rw [Inl.retToBrE, Binaryen.retToBrE, retToBrL_eq (d + 1) b]
  | .if_ bt c t e => by
    rw [Inl.retToBrE, Binaryen.retToBrE, retToBrL_eq d c, retToBrL_eq (d + 1) t,
      retToBrL_eq (d + 1) e]
  | .tryTable bt cs b => by rw [Inl.retToBrE, Binaryen.retToBrE, retToBrL_eq (d + 1) b]
theorem retToBrL_eq (d : Nat) : ∀ es : List BExpr, Inl.retToBrL d es = Binaryen.retToBrL d es
  | [] => by rw [Inl.retToBrL, Binaryen.retToBrL]
  | e :: es => by
    rw [Inl.retToBrL, Binaryen.retToBrL, retToBrE_eq d e, retToBrL_eq d es]
end

theorem siteCode_eq : Inl.siteCode = Binaryen.siteCode := by
  have h1 : Inl.retToBrL = Binaryen.retToBrL := by funext d es; exact retToBrL_eq d es
  have h2 : Inl.shiftLocalsL = Binaryen.shiftLocalsL := by funext b es; exact shiftLocalsL_eq b es
  funext ty base np ls args body
  simp only [Inl.siteCode, Binaryen.siteCode, h1, h2, zeroInstr_eq]

/-- The executable `inlineSite` is `Binaryen.inlineSite`. -/
theorem inlineSite_eq : Inl.inlineSite = Binaryen.inlineSite := by
  funext m g K args f
  simp only [Inl.inlineSite, Binaryen.inlineSite, siteCode_eq]

/-! ## Call-site search -/

theorem map_some {o : Option Site} {F : Site → Site} {s : Site} (h : o.map F = some s) :
    ∃ x, o = some x ∧ F x = s := by
  cases o with
  | none => simp at h
  | some x => exact ⟨x, rfl, Option.some.inj h⟩

theorem callee?_some {i : Instr} {f : FuncIdx} (h : callee? i = some f) : i = .call f := by
  unfold callee? at h
  split at h <;> simp_all

mutual
/-- `siteE` returns a context of the tree around a call it accepts. -/
theorem siteE_spec (p : FuncIdx → Bool) : ∀ (e : BExpr) (s : Site), siteE p e = some s →
    s.1.plug [.op (.call s.2.2) s.2.1] = [e] ∧ p s.2.2 = true
  | .op i args, s, h => by
    rcases hc : callee? i with _ | f
    · simp only [siteE, hc] at h
      obtain ⟨⟨K, a, g⟩, hx, rfl⟩ := map_some h
      obtain ⟨h1, h2⟩ := siteL_spec p args _ hx
      exact ⟨by simp [BCtx.plug, h1], h2⟩
    · rcases hp : p f with _ | _
      · simp only [siteE, hc, hp, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨⟨K, a, g⟩, hx, rfl⟩ := map_some h
        obtain ⟨h1, h2⟩ := siteL_spec p args _ hx
        exact ⟨by simp [BCtx.plug, h1], h2⟩
      · simp only [siteE, hc, hp, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨by simp [BCtx.plug, callee?_some hc], hp⟩
  | .block bt b, s, h => by
    simp only [siteE] at h
    obtain ⟨⟨K, a, g⟩, hx, rfl⟩ := map_some h
    obtain ⟨h1, h2⟩ := siteL_spec p b _ hx
    exact ⟨by simp [BCtx.plug, h1], h2⟩
  | .loop bt b, s, h => by
    simp only [siteE] at h
    obtain ⟨⟨K, a, g⟩, hx, rfl⟩ := map_some h
    obtain ⟨h1, h2⟩ := siteL_spec p b _ hx
    exact ⟨by simp [BCtx.plug, h1], h2⟩
  | .if_ bt c t e, s, h => by
    rcases hc : siteL p c with _ | ⟨K, a, g⟩
    · rcases ht : siteL p t with _ | ⟨K, a, g⟩
      · simp only [siteE, hc, ht] at h
        obtain ⟨⟨K, a, g⟩, hx, rfl⟩ := map_some h
        obtain ⟨h1, h2⟩ := siteL_spec p e _ hx
        exact ⟨by simp [BCtx.plug, h1], h2⟩
      · simp only [siteE, hc, ht, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := siteL_spec p t _ ht
        exact ⟨by simp [BCtx.plug, h1], h2⟩
    · simp only [siteE, hc, Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := siteL_spec p c _ hc
      exact ⟨by simp [BCtx.plug, h1], h2⟩
  | .tryTable .., s, h => by simp [siteE] at h
/-- `siteL` returns a context of the list around a call it accepts. -/
theorem siteL_spec (p : FuncIdx → Bool) : ∀ (es : List BExpr) (s : Site), siteL p es = some s →
    s.1.plug [.op (.call s.2.2) s.2.1] = es ∧ p s.2.2 = true
  | [], s, h => by simp [siteL] at h
  | e :: es, s, h => by
    rcases he : siteE p e with _ | ⟨K, a, g⟩
    · simp only [siteL, he] at h
      obtain ⟨⟨K, a, g⟩, hx, rfl⟩ := map_some h
      obtain ⟨h1, h2⟩ := siteL_spec p es _ hx
      exact ⟨by simp [BCtx.plug, h1], h2⟩
    · simp only [siteL, he, Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := siteE_spec p e _ he
      refine ⟨?_, h2⟩
      simp only [BCtx.plug, List.nil_append]
      rw [h1]
      rfl
end

theorem findIn_spec (p : FuncIdx → Bool) : ∀ (g₀ : Nat) (fs : List BFunc) (g : Nat) (s : Site),
    findIn p g₀ fs = some (g, s) → g₀ ≤ g ∧
      (fs[g - g₀]?).map (·.body) = some (s.1.plug [.op (.call s.2.2) s.2.1]) ∧ p s.2.2 = true
  | _, [], _, _, h => by simp [findIn] at h
  | g₀, fn :: fs, g, s, h => by
    rcases hc : siteL p fn.body with _ | s'
    · simp only [findIn, hc] at h
      obtain ⟨h1, h2, h3⟩ := findIn_spec p (g₀ + 1) fs g s h
      refine ⟨by omega, ?_, h3⟩
      have e : g - g₀ = (g - (g₀ + 1)) + 1 := by omega
      rw [e, List.getElem?_cons_succ]
      exact h2
    · simp only [findIn, hc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := siteL_spec p fn.body _ hc
      refine ⟨Nat.le_refl _, ?_, h2⟩
      simp [h1]

/-- **The found site is a call site of the module.** -/
theorem findSite_spec {p : FuncIdx → Bool} {m : BModule} {g : Nat} {s : Site}
    (h : findSite p m = some (g, s)) :
    m.body? g = some (s.1.plug [.op (.call s.2.2) s.2.1]) ∧ p s.2.2 = true := by
  obtain ⟨-, h2, h3⟩ := findIn_spec p 0 m.funcs g s h
  exact ⟨by simpa [BModule.body?] using h2, h3⟩

end Inl

/-- `HostOk closedHost` for an empty host-state type. With an inhabited `H` it fails:
a store holding a host function `h` has no outcome for it. -/
theorem closedHost_hostOk {H : Type} (hH : H → False) : HostOk (closedHost (H := H)) :=
  fun _ _ h => (hH h).elim

/-! ## Inlining -/

theorem inlineSite_base {m m' : BModule} {g : Nat} {K : BCtx} {args : List BExpr}
    {f : FuncIdx} (h : Binaryen.inlineSite m g K args f = some m') : m'.base = m.base := by
  simp only [Binaryen.inlineSite] at h
  obtain ⟨caller, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨callee, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cft, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ft, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨site, -, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  rfl

theorem inlineStep_spec {H : Type} (hH : H → False) (o : GrowKind → Nat → Nat → Nat → Bool)
    {budget : Nat} {m m' : BModule} (hok : m.Ok) (hty : HTy m)
    (h : Inl.inlineStep budget m = some m') : m'.Ok ∧ HTy m' ∧ EE H o m' m := by
  rw [Inl.inlineStep_eq] at h
  rcases hs : Inl.findSite (Inl.calleeOk budget m) m with _ | ⟨g, K, args, f⟩
  · simp [hs] at h
  · simp only [hs] at h
    obtain ⟨hsite, hc⟩ := Inl.findSite_spec hs
    rw [Inl.inlineSite_eq] at h
    have good := fun fn (hfn : m.defFunc? f.toNat = some fn) => calleeOk_good hc hfn
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨mt, hmt⟩ := hok
      exact ⟨mt, inlineSite_valid_mt hmt hsite (fun fn hfn => (good fn hfn).1)
        (fun fn hfn => (good fn hfn).2) h⟩
    · unfold HTy
      rw [inlineSite_base h]
      exact hty
    · exact inlineSite_sound_of_good hok hsite (fun fn hfn => (good fn hfn).1)
        (fun fn hfn => (good fn hfn).2) h o closedHost closedHost_respectsCode
        (closedHost_hostOk hH)

theorem inlineSmall_spec {H : Type} (hH : H → False) (o : GrowKind → Nat → Nat → Nat → Bool)
    (budget : Nat) : ∀ (fuel : Nat) (m : BModule), m.Ok → HTy m →
      (Inl.inlineSmall budget fuel m).Ok ∧ HTy (Inl.inlineSmall budget fuel m) ∧
        EE H o (Inl.inlineSmall budget fuel m) m
  | 0, m, hok, hty => ⟨hok, hty, exportEquiv_refl _⟩
  | fuel + 1, m, hok, hty => by
    unfold Inl.inlineSmall
    rcases hs : Inl.inlineStep budget m with _ | m'
    · exact ⟨hok, hty, exportEquiv_refl _⟩
    · obtain ⟨a, b, c⟩ := inlineStep_spec hH o hok hty hs
      obtain ⟨a', b', c'⟩ := inlineSmall_spec hH o budget fuel m' a b
      exact ⟨a', b', ExportEquiv.trans_eq c' c⟩


/-! ## The stages (the contract `ExeC`, `StageOk` and `guardedP`: `Exe/StageContract.lean`) -/

section PassAPI

open PassAPI

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-! ## The stages -/

/-- The inlining stage keeps validity and is export-equivalent. -/
theorem inline_stageOk (hH : H → False) (budget : Nat) :
    StageOk o H (inlineSmall budget inlineFuel) := fun m hm => by
  unfold inlineSmall
  split
  · next hn =>
    let r := inlineSmall_spec hH o budget inlineFuel m hm.ok (typesInProfile_sound hn)
    exact ⟨r.1, r.2.2⟩
  · exact ⟨hm.ok, exportEquiv_refl _⟩

/-- RUME keeps validity and is export-equivalent (closed host). -/
theorem rume_stageOk : StageOk o H rume :=
  fun _ hm => ⟨rume_valid hm.ok,
    rume_sound hm.ok (Profile.deterministic o) (H := H)⟩

/-- **The inlining pass.** -/
def inlineP (hH : H → False) (budget : Nat) : Pass (ExeC o H) :=
  guardedP (inlineSmall budget inlineFuel) (inline_stageOk hH budget)

/-- **The RUME pass.** -/
def rumeP : Pass (ExeC o H) := guardedP rume rume_stageOk

/-! ## Dead-code elimination (`Exe/DCESound.lean`) -/

/-- **The checked DCE pass.** -/
def dceP : Pass (ExeC o H) := guardedP Dce.dceChecked dce_stageOk

variable (o H)

/-- Each registered transformation has its own exact-equivalence certificate.
The shared phase list cannot mention a new identifier until this family is total. -/
theorem FunctionStageId.stageOk : ∀ stage : FunctionStageId, StageOk o H stage.transform
  | .dce => dce_stageOk
  | .removeUnusedNames => removeUnusedNames_stageOk
  | .mergeBlocks => mergeBlocks_stageOk
  | .vacuum => vacuum_stageOk
  | .simplifyGlobals => simplifyGlobals_stageOk
  | .directize => directize_stageOk
  | .precompute => precompute_stageOk
  | .constBranch => constBranch_stageOk
  | .constSelect => constSelect_stageOk
  | .addChain => addChain_stageOk
  | .codeFolding => codeFolding_stageOk
  | .coalesceLocals => coalesceLocals_stageOk
  | .removeUnusedBrs => removeUnusedBrs_stageOk
  | .optimizeInstructions => optimizeInstructions_stageOk
  | .simplifyLocals => simplifyLocals_stageOk

/-- A registered executable transformation packaged as its original guarded pass. -/
def FunctionStageId.toPass (stage : FunctionStageId) : Pass (ExeC o H) :=
  guardedP stage.transform (stage.stageOk o H)

@[simp] theorem FunctionStageId.toPass_run (stage : FunctionStageId) :
    (stage.toPass o H).run = stage.run :=
  guardedP_run stage.transform (stage.stageOk o H)

/-- Function-level passes of one round, using the executable registry's order. -/
def functionPassesP : List (Pass (ExeC o H)) :=
  functionStageIds.map (FunctionStageId.toPass o H)

/-- The proof-side and executable function stages agree. -/
theorem functionPassesP_run :
    (functionPassesP o H).map Pass.run = functionStages.map Prod.snd := by
  simp only [functionPassesP, functionStages, List.map_map, Function.comp_def,
    FunctionStageId.toStage, FunctionStageId.toPass_run]

/-- One round of function-level passes. -/
def roundP : Pass (ExeC o H) := Pass.pipeline (functionPassesP o H)

variable {o H}

/-- **The pipeline, as a product in the pass monoid.** -/
def pipelineP (hH : H → False) (budget rounds : Nat) : Pass (ExeC o H) :=
  inlineP hH budget * roundP o H ^ rounds * rumeP

/-- `runStages` is a left fold of the stage functions. -/
theorem runStages_eq_foldl (ss : List Stage) (m : BModule) :
    runStages ss m = (ss.map Prod.snd).foldl (fun y f => f y) m := by
  simp [runStages, List.foldl_map]

theorem runStages_append (ss ts : List Stage) (m : BModule) :
    runStages (ss ++ ts) m = runStages ts (runStages ss m) := by
  simp [runStages, List.foldl_append]

/-- A pipeline whose run functions are those of a list of stages runs the stages. -/
theorem pipeline_run_stages (ps : List (Pass (ExeC o H))) (ss : List Stage)
    (h : ps.map Pass.run = ss.map Prod.snd) (m : BModule) :
    (Pass.pipeline ps).run m = runStages ss m := by
  rw [Pass.pipeline_run, runStages_eq_foldl, ← h, List.foldl_map]

/-- The run function of `rounds` rounds. -/
theorem roundP_pow_run (rounds : Nat) (m : BModule) :
    (roundP o H ^ rounds).run m = runStages (List.replicate rounds functionStages).flatten m := by
  induction rounds generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Pass.mul_run, ih, List.replicate_succ', List.flatten_append,
      List.flatten_singleton, runStages_append]
    exact pipeline_run_stages _ _ (functionPassesP_run o H) _

/-- **The pipeline's run function is the executable one.** -/
theorem pipelineP_run (hH : H → False) (budget rounds : Nat) :
    (pipelineP (o := o) hH budget rounds).run = pipelineWith budget rounds := by
  funext m
  simp only [pipelineP, Pass.mul_run, roundP_pow_run, pipelineWith, pipelineStages,
    List.cons_append]
  simp only [runStages, List.foldl_cons, List.foldl_append, List.foldl_nil, inlineStage,
    rumeStage, inlineP, rumeP, guardedP_run]

/-- **The size-guarded choice, as `Pass.best`.** -/
def bestP (hH : H → False) (score : BModule → Nat) (rounds : Nat) : Pass (ExeC o H) :=
  Pass.best score [pipelineP hH 0 rounds, pipelineP hH inlineBudget rounds]

/-- **The driver's choice is `Pass.best`.** `bestNamed` scores each candidate once and
labels the winner; its module is the run of `bestP`. -/
theorem bestNamed_run (hH : H → False) (score : BModule → Nat) (rounds : Nat) (m : BModule) :
    (bestNamed score rounds m).2 = (bestP (o := o) hH score rounds).run m := by
  simp only [bestNamed, namedCandidates, bestP, Pass.best, Pass.bestRun, List.map_cons,
    List.map_nil, List.foldl_cons, List.foldl_nil, pickScored, pipelineP_run]
  by_cases h1 : score (pipelineWith 0 rounds m) < score m
  · by_cases h2 : score (pipelineWith inlineBudget rounds m) < score (pipelineWith 0 rounds m)
    · simp [h1, h2]
    · simp [h1, h2]
  · by_cases h2 : score (pipelineWith inlineBudget rounds m) < score m
    · simp [h1, h2]
    · simp [h1, h2]

/-! ## Soundness, derived from the pass API -/

/-- **The driver's choice is sound**, for every score: the result satisfies the
invariant and is export-equivalent to the input. An instance of `Pass.sound`. -/
theorem bestNamed_sound (hH : H → False) (score : BModule → Nat) (rounds : Nat)
    {m : BModule} (hm : ExeInv m) :
    EE H o (bestNamed score rounds m).2 m ∧ ExeInv (bestNamed score rounds m).2 := by
  rw [bestNamed_run (o := o) hH]
  exact ⟨(bestP hH score rounds).sound hm, (bestP hH score rounds).inv_run hm⟩

/-- **Pipeline soundness** (the statement of the bespoke `pipeline_sound` of pipeline contract,
now a corollary of `Pass.sound`). -/
theorem pipeline_sound {m : BModule} (hp : m.inProfile = true) (hok : m.Ok)
    (hty : ∀ st ∈ m.base.typeDefinitions, ∀ ft : FuncType, st.body = .func ft →
      ∀ t ∈ ft.params ++ ft.results, profileValType t = true)
    (rounds : Nat) (hH : H → False) :
    ExportEquiv (· = ·) (Profile.deterministic o) (closedHost (H := H))
      (pipeline rounds m).lower m.lower := by
  have hm : ExeInv m := ⟨profileOk_of_inProfile hp (typesInProfile_complete fun st hst ft hft t ht =>
      sigValType_of_profileValType (hty st hst ft hft t ht)), hok⟩
  have := (pipelineP (o := o) hH inlineBudget rounds).sound hm
  rw [pipelineP_run] at this
  exact this

end PassAPI

end Silmaril.Wasm.Binaryen.Exe
