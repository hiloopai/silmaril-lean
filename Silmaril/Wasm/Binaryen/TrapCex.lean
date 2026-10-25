module

public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Binaryen.Effects
public import Silmaril.Wasm.Binaryen.LoopCex
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateIff
public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Removing a dropped trap is not an equivalence

A module whose start function is `drop (i32.div_u 1 0)` traps while it is
instantiated; with the body removed it returns. Under the deterministic profile the
trapping run is the only run (its normal form is reached from every reachable
configuration, `steps_to_nf`), so the trapping module has no returning observation:
`not_refines` refutes `ExportRefines (· = ·)` from the empty module body to the
trapping one, which `Pass/Vacuum.lean` turns into `vacuum_tnh_not_equiv`.

The shapes of the instantiated configurations are computed by kernel evaluation of
the concrete instantiator `instantiate?` (`decide +kernel`); the runs are built by
hand (they do not depend on the grow oracle).
-/

namespace Silmaril.Wasm.Binaryen.TrapCex

open Silmaril.Wasm.Binaryen Execution.Core Numerics Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det

/-- `(func)` as a singleton recursive group. -/
def ftUnit : RecType := ⟨[⟨true, [], .func ⟨[], []⟩⟩]⟩

/-- One function type; the start function is function `0`. -/
def base : Module := { types := [ftUnit], start := some ⟨0⟩ }

/-- The module of layer D: one function of type `0` (its body is replaced). -/
def mod : BModule := ⟨base, [⟨⟨0⟩, [], []⟩]⟩

/-- The lowered module with body `es`. -/
abbrev lowered (es : List BExpr) : Module := (mod.withBody 0 (BCtx.hole.plug es)).lower

/-- The trapping body. -/
abbrev trapBody : List BExpr := [.op .drop [divByZero]]

theorem valid_nil : (validate? (lowered [])).isSome = true := by decide +kernel

theorem valid_trap : (validate? (lowered trapBody)).isSome = true := by decide +kernel

theorem ok_nil : (mod.withBody 0 (BCtx.hole.plug [])).Ok := validate_sound valid_nil

theorem ok_trap : (mod.withBody 0 (BCtx.hole.plug trapBody)).Ok := validate_sound valid_trap

/-- No imports. -/
def noImports (r : Option CModuleType) : Bool :=
  match r with
  | some ⟨[], _⟩ => true
  | _ => false

theorem noImports_nil : noImports (validate? (lowered [])) = true := by decide +kernel

theorem noImports_trap : noImports (validate? (lowered trapBody)) = true := by decide +kernel

theorem hvalid {es : List BExpr} (hv : (validate? (lowered es)).isSome = true)
    (hi : noImports (validate? (lowered es)) = true) {H : Type} :
    ∃ xtE xtI, ModuleOk (lowered es) ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store H)) [] xtI := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp hv
  rw [hmt] at hi
  obtain ⟨xtI, xtE⟩ := mt
  cases xtI with
  | nil => exact ⟨xtE, [], validate?_sound hmt, .nil⟩
  | cons _ _ => simp [noImports] at hi

/-! ## The instantiated configurations -/

/-- The shape of an instantiated configuration: it calls function `0`, whose single
instance has type `[] → []`, no locals and a body accepted by `bodyOk`. -/
def shapeOk {H : Type} (bodyOk : List Instr → Bool) (c : Config H) : Bool :=
  (match c.code with
    | [.plain (.call x)] => x.toNat == 0
    | _ => false) &&
  c.frame.module.funcs == [0] &&
  (match c.store.funcs with
    | [fi] =>
      (match fi.code with
        | .wasm fn => bodyOk fn.body && fn.locals.isEmpty
        | .host _ => false) &&
      (match fi.type.funcType? with
        | some ([], []) => true
        | _ => false)
    | _ => false)

/-- The empty body. -/
def emptyOk (b : List Instr) : Bool := b.isEmpty

/-- `i32.const 1; i32.const 0; i32.div_u; drop`. -/
def trapOk (b : List Instr) : Bool :=
  match b with
  | [.intConst .i32 x, .intConst .i32 y, .intBinOp .i32 (.div .unsigned), .drop] =>
      x == 1 && y == 0
  | _ => false

theorem inst_nil :
    (instantiate? evalConst? ({} : Store Empty) (lowered []) []).map (shapeOk emptyOk) =
      some true := by decide +kernel

theorem inst_trap :
    (instantiate? evalConst? ({} : Store Empty) (lowered trapBody) []).map (shapeOk trapOk) =
      some true := by decide +kernel

/-- Unpacking `shapeOk`. -/
theorem shapeOk_inv {H : Type} {bodyOk : List Instr → Bool} {c : Config H}
    (h : shapeOk bodyOk c = true) :
    ∃ fi fn ps rs, c.code = [.plain (.call ⟨⟨0, by decide⟩⟩)] ∧
      c.frame.module.funcs = [0] ∧ c.store.funcs = [fi] ∧ fi.code = .wasm fn ∧
      bodyOk fn.body = true ∧ fn.locals = [] ∧ Expand fi.type (.func ps rs) ∧ ps.length = 0 ∧
      rs.length = 0 := by
  unfold shapeOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hcode, hfuncs⟩, hstore⟩ := h
  split at hcode
  · next x hx =>
    split at hstore
    · next fi hfi =>
      simp only [Bool.and_eq_true] at hstore
      obtain ⟨hcd, hty⟩ := hstore
      split at hcd
      · next fn hfn =>
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hcd
        split at hty
        · next hft =>
          unfold DefType.funcType? at hft
          split at hft
          · next ps rs hexp =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hft
            refine ⟨fi, fn, ps, rs, ?_, hfuncs, hfi, hfn, hcd.1, hcd.2, Expand.iff.mpr hexp,
              ?_, ?_⟩
            · rw [hx]
              have : x = ⟨⟨0, by decide⟩⟩ := by
                obtain ⟨⟨v, hv⟩⟩ := x
                simp only [Idx.toNat, beq_iff_eq] at hcode
                subst hcode
                rfl
              rw [this]
            · simp [Ty.length, hft.1]
            · simp [Ty.length, hft.2]
          · simp at hft
        · simp at hty
      · simp at hcd
    · simp at hstore
  · simp at hcode

/-! ## Runs -/

section Run

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

/-- Calling the function enters its frame and label. -/
theorem call_run {c : Config H} {fi : FuncInst H} {fn : Func} {ps rs : Ty (.list .val)}
    (hcode : c.code = [.plain (.call ⟨⟨0, by decide⟩⟩)]) (hfuncs : c.frame.module.funcs = [0])
    (hstore : c.store.funcs = [fi]) (hfc : fi.code = .wasm fn) (hexp : Expand fi.type (.func ps rs))
    (hps : ps.length = 0) :
    Steps (Profile.deterministic o) closedHost c
      ⟨c.store, c.frame, [.frame rs.length (Frame.forCall fi.module [] fn.locals)
        [.label rs.length [] (expression fn.body)]]⟩ := by
  obtain ⟨s, f, code⟩ := c
  simp only at hcode hfuncs hstore
  subst hcode
  have h₁ := Step.call (P := Profile.deterministic o) (host := closedHost) (s := s) (f := f)
    (x := ⟨⟨0, by decide⟩⟩) (a := 0) (fi := fi) (by simp [hfuncs, Idx.toNat]) (by simp [hstore])
  have h₂ := Step.callRefFunc (P := Profile.deterministic o) (host := closedHost) (s := s)
    (f := f) (c := .callRefType fi.type) (vs := []) (a := 0) (fi := fi) (code := fn) trivial
    (by simp [hstore]) hexp (by simp [hps]) hfc
  exact h₁.steps.trans (by simpa [vals] using h₂.steps)

/-- The empty body returns. -/
theorem empty_run {s : Store H} {f fi : Frame} :
    Steps (Profile.deterministic o) closedHost ⟨s, f, [.frame 0 fi [.label 0 [] []]]⟩
      ⟨s, f, []⟩ := by
  have h₁ : Steps (Profile.deterministic o) closedHost ⟨s, f, [.frame 0 fi [.label 0 [] []]]⟩
      ⟨s, f, [.frame 0 fi []]⟩ :=
    (Step.ctxtFrame (P := Profile.deterministic o) (host := closedHost) (s := s) (f := f)
      (n := 0) (fi := fi) (fi' := fi)
      (Step.labelVals (P := Profile.deterministic o) (host := closedHost) (s := s) (f := fi)
        (n := 0) (cont := []) (vs := []))).steps
  have h₂ : Steps (Profile.deterministic o) closedHost ⟨s, f, [.frame 0 fi []]⟩ ⟨s, f, []⟩ :=
    (Step.frameVals (P := Profile.deterministic o) (host := closedHost) (s := s) (f := f)
      (fi := fi) (vs := []) (n := 0) rfl).steps
  exact h₁.trans h₂

/-- `1 / 0` traps, through the label and the frame. -/
theorem trap_run {s : Store H} {f fi : Frame} {n : Nat} :
    Steps (Profile.deterministic o) closedHost
      ⟨s, f, [.frame n fi [.label n [] [.plain (.intConst .i32 1), .plain (.intConst .i32 0),
        .plain (.intBinOp .i32 (.div .unsigned)), .plain .drop]]]⟩ ⟨s, f, [.trap]⟩ := by
  have hdiv : intBinOp .i32 (.div .unsigned) 1 0 = .error .divideByZero := by
    simp [intBinOp]
  have hin : Steps (Profile.deterministic o) closedHost
      ⟨s, fi, [.plain (.intConst .i32 1), .plain (.intConst .i32 0),
        .plain (.intBinOp .i32 (.div .unsigned)), .plain .drop]⟩ ⟨s, fi, [.trap]⟩ := by
    have h₁ : Steps (Profile.deterministic o) closedHost
        ⟨s, fi, [.plain (.intConst .i32 1), .plain (.intConst .i32 0),
          .plain (.intBinOp .i32 (.div .unsigned)), .plain .drop]⟩
        ⟨s, fi, [.trap, .plain .drop]⟩ :=
      (Step.ctxtInstrs (P := Profile.deterministic o) (host := closedHost) (s := s)
        (f := fi) (vs := []) (rest := [.plain .drop])
        (Step.numeric (P := Profile.deterministic o) (host := closedHost) (s := s) (f := fi)
          (NumericStep.intBinOpTrap hdiv)) (.inr (by simp))).steps
    have h₂ : Steps (Profile.deterministic o) closedHost ⟨s, fi, [.trap, .plain .drop]⟩
        ⟨s, fi, [.trap]⟩ :=
      (Step.trapInstrs (P := Profile.deterministic o) (host := closedHost) (s := s)
        (f := fi) (vs := []) (rest := [.plain .drop]) (.inr (by simp))).steps
    exact h₁.trans h₂
  have hl := (Steps.label (n := n) (cont := []) hin).trans
    (Step.trapLabel (P := Profile.deterministic o) (host := closedHost) (s := s) (f := fi)
      (n := n) (cont := [])).steps
  exact (Steps.frame (f := f) (n := n) hl).trans
    (Step.trapFrame (P := Profile.deterministic o) (host := closedHost) (s := s) (f := f)
      (fi := fi) (n := n)).steps

end Run

/-! ## Normal forms are reached from every reachable configuration -/

section Confluence

variable {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type}

theorem strip {c₁ c₂ t : Config H} (hrun : Steps (Profile.deterministic o) noHost c₁ t)
    (hnf : ∀ d, ¬ Step (Profile.deterministic o) noHost t d)
    (hs : Step (Profile.deterministic o) noHost c₁ c₂) :
    Steps (Profile.deterministic o) noHost c₂ t := by
  induction hrun using Relation.ReflTransGen.head_induction_on generalizing c₂ with
  | refl => exact (hnf _ hs).elim
  | head hcd hdt ih =>
    obtain ⟨z, h₁, h₂⟩ := DStep.join' (o := o) hs hcd
    cases h₂ with
    | refl =>
      cases h₁ with
      | refl => exact hdt
      | single h => exact .head h hdt
    | single h =>
      have := ih h
      cases h₁ with
      | refl => exact this
      | single h' => exact .head h' this

/-- From every configuration reachable from `c`, the normal form of `c` is reachable. -/
theorem steps_to_nf {c t c' : Config H} (hrun : Steps (Profile.deterministic o) noHost c t)
    (hnf : ∀ d, ¬ Step (Profile.deterministic o) noHost t d)
    (hc' : Steps (Profile.deterministic o) noHost c c') :
    Steps (Profile.deterministic o) noHost c' t := by
  induction hc' with
  | refl => exact hrun
  | tail _ hs ih => exact strip ih hnf hs

end Confluence

/-! ## The refutation -/

theorem not_step_nil {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type} {s : Store H}
    {f : Frame} {d : Config H} : ¬ Step (Profile.deterministic o) noHost ⟨s, f, []⟩ d :=
  fun h => not_step_vals (W := []) h

/-- **The trapping module has no returning observation, the empty one does.** -/
theorem not_refines (o : GrowKind → Nat → Nat → Nat → Bool) :
    ¬ ExportRefines (· = ·) (Profile.deterministic o) (closedHost (H := Empty))
      (lowered []) (lowered trapBody) := by
  intro h
  -- the empty module instantiates and its start function returns
  obtain ⟨cE, hcE⟩ := Option.isSome_iff_exists.mp
    (show (instantiate? evalConst? ({} : Store Empty) (lowered []) []).isSome = true by
      have := inst_nil
      revert this
      cases instantiate? evalConst? ({} : Store Empty) (lowered []) [] <;> simp)
  have hshE : shapeOk emptyOk cE = true := by
    have := inst_nil; rw [hcE] at this; simpa using this
  obtain ⟨fiE, fnE, psE, rsE, hcodeE, hfuncsE, hstoreE, hfcE, hbodyE, -, hexpE, hpsE, hrsE⟩ :=
    shapeOk_inv hshE
  have hinstE : Instantiate (Profile.deterministic o) closedHost ({} : Store Empty) (lowered [])
      [] cE := (instantiate?_iff (hvalid valid_nil noImports_nil)).mp hcE
  have hbodyE' : fnE.body = [] := by simpa [emptyOk] using hbodyE
  have hrunE : Steps (Profile.deterministic o) closedHost cE ⟨cE.store, cE.frame, []⟩ := by
    have := call_run (o := o) hcodeE hfuncsE hstoreE hfcE hexpE hpsE
    rw [hbodyE', hrsE] at this
    have hE := empty_run (o := o) (s := cE.store) (f := cE.frame)
      (fi := Frame.forCall fiE.module [] fnE.locals)
    exact this.trans (by simpa [expression] using hE)
  have hobs : [Behaviour.returns []] ∈ moduleObs (Profile.deterministic o) closedHost
      ({} : Store Empty) [] (lowered []) [] :=
    ⟨cE, hinstE, .inl ⟨_, [], hrunE, rfl, .nil, rfl⟩⟩
  obtain ⟨bs', hbs', hrel⟩ := h.obs {} [] [] LoopCex.storeOk_empty _ hobs
  -- the related observation of the trapping module starts by returning
  have hhead : ∃ rest, bs' = .returns [] :: rest := by
    cases hrel with
    | cons hb _ => exact ⟨_, by rw [← hb]⟩
    | ub hb =>
      have h1 := hb .traps
      have h2 := hb (.returns [])
      rw [← h2] at h1
      simp at h1
  obtain ⟨rest, rfl⟩ := hhead
  -- the trapping module instantiates to a unique configuration, which traps
  obtain ⟨cT, hcT⟩ := Option.isSome_iff_exists.mp
    (show (instantiate? evalConst? ({} : Store Empty) (lowered trapBody) []).isSome = true by
      have := inst_trap
      revert this
      cases instantiate? evalConst? ({} : Store Empty) (lowered trapBody) [] <;> simp)
  have hshT : shapeOk trapOk cT = true := by
    have := inst_trap; rw [hcT] at this; simpa using this
  obtain ⟨fiT, fnT, psT, rsT, hcodeT, hfuncsT, hstoreT, hfcT, hbodyT, -, hexpT, hpsT, -⟩ :=
    shapeOk_inv hshT
  have hbodyT' : fnT.body = [.intConst .i32 1, .intConst .i32 0,
      .intBinOp .i32 (.div .unsigned), .drop] := by
    unfold trapOk at hbodyT
    split at hbodyT
    · next x y =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hbodyT
      obtain ⟨rfl, rfl⟩ := hbodyT
      assumption
    · simp at hbodyT
  have hrunT : Steps (Profile.deterministic o) closedHost cT ⟨cT.store, cT.frame, [.trap]⟩ := by
    have := call_run (o := o) hcodeT hfuncsT hstoreT hfcT hexpT hpsT
    rw [hbodyT'] at this
    have hT := trap_run (o := o) (s := cT.store) (f := cT.frame)
      (fi := Frame.forCall fiT.module [] fnT.locals) (n := rsT.length)
    exact this.trans (by simpa [expression] using hT)
  have hnfT : ∀ d, ¬ Step (Profile.deterministic o) noHost ⟨cT.store, cT.frame, [.trap]⟩ d :=
    fun d hd => not_step_trap hd
  obtain ⟨c, hinst, hcase⟩ := hbs'
  have hc : c = cT := by
    have := instantiate?_evalConst_complete hinst
    rw [hcT] at this
    exact (Option.some.inj this).symm
  subst hc
  rcases hcase with ⟨c', bs'', hrun', hcode', -, -⟩ | ⟨c', r, -, -, hr, hbs⟩ | ⟨-, hbs⟩
  · -- a run reaching an empty code would reach the trap
    have hback := steps_to_nf (o := o) hrunT hnfT hrun'
    obtain ⟨s', f', code'⟩ := c'
    simp only at hcode'
    subst hcode'
    rcases Relation.ReflTransGen.cases_head hback with he | ⟨d, hd, -⟩
    · simp only [Config.mk.injEq] at he
      exact absurd he.2.2 (by simp)
    · exact not_step_nil hd
  · simp only [List.cons.injEq] at hbs
    obtain ⟨hb, -⟩ := hbs
    cases r with
    | values vs =>
      simp only [Result.toBehaviour, Behaviour.returns.injEq] at hb
      exact hr (by rw [hb])
    | throw a => simp [Result.toBehaviour] at hb
    | trap => simp [Result.toBehaviour] at hb
  · simp at hbs

end Silmaril.Wasm.Binaryen.TrapCex
