module

public import Silmaril.Wasm.LimeCompile.TailCex.Defs
public import Silmaril.Proofs.Wasm.LimeCompile.Tail.Ident
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Tail calls under `try_table`: the naive rewrite is wrong

For the valid module `cexM` (`cexM_validates`, silmaril-lean's validator run by `decide`):

* `alloc_cexM`, `alloc_naive`: allocating `cexM` and its naive rewrite `naiveModule cexM` in the
  empty store gives `storeC` and `storeN` (same module instance `miC`); `tailModule cexM = cexM`
  (`tail_cexM`: the correct rewrite leaves the `try_table` alone);
* `src_run`: invoking `f` (address `0`) in `storeC` runs to an uncaught exception, at every
  profile and every host: `return_call` leaves the handler first;
* `naive_run`: invoking `f` in `storeN` runs to `[i32 7]`: `call $g; return` runs `$g` inside
  the handler, `catch_all` catches the exception;
* **`naive_behaviours_ne`**: under silmaril-lean's deterministic single-threaded profile
  `profile o` and the host-free semantics, the two invocations have different behaviour sets:
  `throws 0` is a behaviour of the source and not of the naive rewrite (whose behaviours are
  among `returns [7]` and divergence, by confluence, `behavioursOf_subset_of_steps_nf`).

So the naive rewrite under `try_table` does not preserve behaviours, even of a single invocation
of a valid module; the rewrite of `Tail` excludes `try_table` bodies.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.TailCex

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core.Sim (Step.append_right)
open Silmaril.Wasm.LimeCompile.Tail Silmaril.Proofs.Wasm.LimeCompile.Tail

theorem cexM_validates : ∃ mt, ModuleOk cexM mt := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp (show (validate? cexM).isSome = true by decide)
  exact ⟨mt, validate?_sound hmt⟩

theorem naiveL_bodyF : naiveL bodyF = bodyFN := by
  simp [bodyF, bodyFN, naiveL_cons, naiveL_nil, naiveI]

theorem naiveL_bodyG : naiveL bodyG = bodyG := by
  simp [bodyG, naiveL_cons, naiveL_nil, naiveI]

theorem tailL_bodyF : tailL bodyF = bodyF := by
  simp [bodyF, tailL_cons, tailL_nil, tailI]

theorem tailL_bodyG : tailL bodyG = bodyG := by
  simp [bodyG, tailL_cons, tailL_nil, tailI]

/-- The correct rewrite leaves `cexM` alone (its only tail call is under `try_table`). -/
theorem tail_cexM : tailModule cexM = cexM := by
  simp [tailModule, cexM, tailFunc, tailL_bodyF, tailL_bodyG]

/-- The naive rewrite of `cexM`. -/
theorem naive_cexM : naiveModule cexM = { cexM with funcs := [⟨⟨0⟩, [], bodyFN⟩, ⟨⟨0⟩, [], bodyG⟩] } := by
  simp [naiveModule, cexM, naiveL_bodyF, naiveL_bodyG]

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem alloc_cexM : allocModule? ({} : Store H) cexM [] [] [] [] = some (storeC, miC) := rfl

theorem alloc_naive :
    allocModule? ({} : Store H) (naiveModule cexM) [] [] [] [] = some (storeN, miC) := by
  rw [naive_cexM]
  rfl

/-! ## The runs -/

/-- The frame of `$f` and of `$g` (no parameters, no locals). -/
abbrev F0 : Frame := ⟨[], miC⟩

abbrev csC : List Catch := [.catchAll l0]

abbrev c7 : Admin := .plain (.intConst .i32 7)

/-- Code `X` running as the body of `$f`. -/
abbrev inF (X : List Admin) : List Admin := [.frame 1 F0 [.label 1 [] X]]

theorem expandF : Expand dtF (.func .nil (.cons .i32 .nil)) := Expand.iff.2 rfl

theorem expandE : Expand dtE (.func .nil .nil) := Expand.iff.2 rfl

/-- A step of the body of `$f`, lifted into its frame and label. -/
theorem inF_step {s s' : Store H} {X X' : List Admin}
    (h : Step P host ⟨s, F0, X⟩ ⟨s', F0, X'⟩) :
    Step P host ⟨s, {}, inF X⟩ ⟨s', {}, inF X'⟩ :=
  .ctxtFrame (.ctxtLabel h)

/-- A step inside the block label of `$f`, before `i32.const 7`. -/
theorem inBlk_step {s s' : Store H} {X X' : List Admin}
    (h : Step P host ⟨s, F0, X⟩ ⟨s', F0, X'⟩) :
    Step P host ⟨s, {}, inF [.label 0 [] X, c7]⟩ ⟨s', {}, inF [.label 0 [] X', c7]⟩ :=
  inF_step (Step.append_right (.ctxtLabel h) [c7])

/-- A step inside the `try_table` handler and its label. -/
theorem inTry_step {s s' : Store H} {X X' : List Admin}
    (h : Step P host ⟨s, F0, X⟩ ⟨s', F0, X'⟩) :
    Step P host ⟨s, {}, inF [.label 0 [] [.handler 0 csC [.label 0 [] X]], c7]⟩
      ⟨s', {}, inF [.label 0 [] [.handler 0 csC [.label 0 [] X']], c7]⟩ :=
  inBlk_step (.ctxtHandler (.ctxtLabel h))

/-- Calling `$f` (address `0`) from the top level. -/
theorem enter_f {s : Store H} {b : Expr} (hs : s.funcs[0]? = some ⟨dtF, miC, .wasm ⟨⟨0⟩, [], b⟩⟩) :
    Step P host (invoke s 0 []) ⟨s, {}, inF (expression b)⟩ := by
  have h := Step.callRefFunc (P := P) (host := host) (s := s) (f := {}) (vs := [])
    (c := .callRefType dtF) (code := ⟨⟨0⟩, [], b⟩) trivial hs expandF rfl rfl
  have e : invoke s 0 [] = ⟨s, {}, vals [] ++ [.ref (.func 0), .callRefType dtF]⟩ := by
    simp [invoke, hs]
  rw [e]
  exact h

/-- Entering the block and the `try_table` of `$f`. -/
theorem enter_try {s : Store H} {body : List Instr} :
    Steps P host ⟨s, {}, inF [.plain (.block .empty [.tryTable .empty csC body]), c7]⟩
      ⟨s, {}, inF [.label 0 [] [.handler 0 csC [.label 0 [] (expression body)]], c7]⟩ := by
  have hb := Step.block (P := P) (host := host) (s := s) (f := F0) (vs := [])
    (bt := .empty) (body := [.tryTable .empty csC body]) (t₁ := []) (t₂ := []) rfl rfl
  have ht := Step.tryTable (P := P) (host := host) (s := s) (f := F0) (vs := [])
    (bt := .empty) (cs := csC) (body := body) (t₁ := []) (t₂ := []) rfl rfl
  exact .head (inF_step (Step.append_right hb [c7])) (.single (inBlk_step ht))

/-- The source: `return_call $g` leaves the handler and the frame, `$g` throws outside. -/
theorem src_run :
    Steps P host (invoke storeC 0 [])
      ⟨(storeC : Store H).addExn ⟨0, []⟩, {}, throwing 0⟩ :=
  have h0 := enter_f (P := P) (host := host) (s := storeC) (b := bodyF) rfl
  have h1 := enter_try (P := P) (host := host) (s := storeC) (body := [.returnCall ⟨1⟩])
  have hrc := Step.returnCall (P := P) (host := host) (s := (storeC : Store H)) (f := F0)
    (x := ⟨1⟩) (a := 1) rfl rfl
  have hl₁ := Step.returnCallRefLabel (P := P) (host := host) (s := (storeC : Store H)) (f := F0)
    (k := 0) (cont := []) (vs := [.ref (.func 1)]) (c := .returnCallRefType dtF) (rest := []) trivial
  have hh := Step.returnCallRefHandler (P := P) (host := host) (s := (storeC : Store H)) (f := F0)
    (k := 0) (cs := csC) (vs := [.ref (.func 1)]) (c := .returnCallRefType dtF) (rest := []) trivial
  have hl₂ := Step.returnCallRefLabel (P := P) (host := host) (s := (storeC : Store H)) (f := F0)
    (k := 0) (cont := []) (vs := [.ref (.func 1)]) (c := .returnCallRefType dtF) (rest := []) trivial
  have hl₃ := Step.returnCallRefLabel (P := P) (host := host) (s := (storeC : Store H)) (f := F0)
    (k := 1) (cont := []) (vs := [.ref (.func 1)]) (c := .returnCallRefType dtF) (rest := [c7])
    trivial
  have hfa := Step.returnCallRefFrameAddr (P := P) (host := host) (s := (storeC : Store H))
    (f := {}) (fi := F0) (k := 1) (vs' := []) (vs := []) (a := 1) (c := .returnCallRefType dtF)
    (rest := []) trivial rfl expandF rfl
  have hg := Step.callRefFunc (P := P) (host := host) (s := (storeC : Store H)) (f := {})
    (vs := []) (c := .callRefType dtF) (a := 1) (fi := ⟨dtF, miC, .wasm ⟨⟨0⟩, [], bodyG⟩⟩)
    (code := ⟨⟨0⟩, [], bodyG⟩) trivial rfl expandF rfl rfl
  have ht := Step.throw (P := P) (host := host) (s := (storeC : Store H)) (f := F0) (x := ⟨0⟩)
    (vs := []) (ta := 0) (ti := ⟨dtE⟩) rfl expandE rfl
  have hlab := Step.throwRefLabel (P := P) (host := host) (s := (storeC : Store H).addExn ⟨0, []⟩)
    (f := F0) (n := 1) (cont := []) (a := 0)
  have hfr := Step.throwRefFrame (P := P) (host := host) (s := (storeC : Store H).addExn ⟨0, []⟩)
    (f := {}) (fi := F0) (n := 1) (a := 0)
  .head h0 (h1.trans (.head (inTry_step hrc) (.head (inBlk_step (.ctxtHandler hl₁))
    (.head (inBlk_step hh) (.head (inF_step (Step.append_right hl₂ [c7]))
    (.head (.ctxtFrame hl₃) (.head hfa (.head hg (.head (.ctxtFrame (.ctxtLabel ht))
    (.head (.ctxtFrame hlab) (.single hfr)))))))))))

/-- The naive rewrite: `call $g` runs inside the handler, which catches `$g`'s exception. -/
theorem naive_run :
    Steps P host (invoke storeN 0 [])
      ⟨(storeN : Store H).addExn ⟨0, []⟩, {}, vals [.num ⟨.int .i32, 7⟩]⟩ :=
  have h0 := enter_f (P := P) (host := host) (s := storeN) (b := bodyFN) rfl
  have h1 := enter_try (P := P) (host := host) (s := storeN) (body := [.call ⟨1⟩, .return_])
  have hc := Step.call (P := P) (host := host) (s := (storeN : Store H)) (f := F0)
    (x := ⟨1⟩) (a := 1) rfl rfl
  have hg := Step.callRefFunc (P := P) (host := host) (s := (storeN : Store H)) (f := F0)
    (vs := []) (c := .callRefType dtF) (a := 1) (fi := ⟨dtF, miC, .wasm ⟨⟨0⟩, [], bodyG⟩⟩)
    (code := ⟨⟨0⟩, [], bodyG⟩) trivial rfl expandF rfl rfl
  have ht := Step.throw (P := P) (host := host) (s := (storeN : Store H)) (f := F0) (x := ⟨0⟩)
    (vs := []) (ta := 0) (ti := ⟨dtE⟩) rfl expandE rfl
  have hlab := Step.throwRefLabel (P := P) (host := host) (s := (storeN : Store H).addExn ⟨0, []⟩)
    (f := F0) (n := 1) (cont := []) (a := 0)
  have hfr := Step.throwRefFrame (P := P) (host := host) (s := (storeN : Store H).addExn ⟨0, []⟩)
    (f := F0) (fi := F0) (n := 1) (a := 0)
  have hins := Step.throwRefInstrs (P := P) (host := host)
    (s := (storeN : Store H).addExn ⟨0, []⟩) (f := F0) (vs := []) (a := 0)
    (rest := [.plain .return_]) (Or.inr (List.cons_ne_nil _ _))
  have hlab₂ := Step.throwRefLabel (P := P) (host := host)
    (s := (storeN : Store H).addExn ⟨0, []⟩) (f := F0) (n := 0) (cont := []) (a := 0)
  have hcatch := Step.throwRefHandlerCatchAll (P := P) (host := host)
    (s := (storeN : Store H).addExn ⟨0, []⟩) (f := F0) (n := 0) (l := l0) (cs := []) (a := 0)
  have hbr := Step.brLabelZero (P := P) (host := host) (s := (storeN : Store H).addExn ⟨0, []⟩)
    (f := F0) (n := 0) (cont := []) (vs' := []) (vs := []) (l := l0) (rest := []) rfl rfl
  have hlv := Step.labelVals (P := P) (host := host) (s := (storeN : Store H).addExn ⟨0, []⟩)
    (f := F0) (n := 1) (cont := []) (vs := [.num ⟨.int .i32, 7⟩])
  have hfv := Step.frameVals (P := P) (host := host) (s := (storeN : Store H).addExn ⟨0, []⟩)
    (f := {}) (fi := F0) (n := 1) (vs := [.num ⟨.int .i32, 7⟩]) rfl
  .head h0 (h1.trans (.head (inTry_step (Step.append_right hc [.plain .return_]))
    (.head (inTry_step (Step.append_right hg [.plain .return_]))
    (.head (inTry_step (Step.append_right (.ctxtFrame (.ctxtLabel ht)) [.plain .return_]))
    (.head (inTry_step (Step.append_right (.ctxtFrame hlab) [.plain .return_]))
    (.head (inTry_step (Step.append_right hfr [.plain .return_]))
    (.head (inTry_step hins) (.head (inBlk_step (.ctxtHandler hlab₂))
    (.head (inBlk_step hcatch) (.head (inF_step (Step.append_right hbr [c7]))
    (.head (.ctxtFrame hlv) (.single hfv))))))))))))

/-- **The naive rewrite under `try_table` changes behaviours**: under the deterministic
single-threaded profile and the host-free semantics, invoking `f` in the allocation of `cexM`
can throw, and invoking it in the allocation of `naiveModule cexM` cannot. -/
theorem naive_behaviours_ne (o : SingleThreaded.GrowOracle) :
    Behaviour.throws 0 ∈ behaviours (SingleThreaded.profile o) SingleThreaded.Det.noHost
        (storeC : Store H) 0 [] ∧
      Behaviour.throws 0 ∉ behaviours (SingleThreaded.profile o) SingleThreaded.Det.noHost
        (storeN : Store H) 0 [] := by
  refine ⟨mem_behavioursOf (r := .throw 0) src_run rfl, fun hm => ?_⟩
  have hsub := SingleThreaded.Exec.BehaviourRefinement.behavioursOf_subset_of_steps_nf
    (r := .values [.num ⟨.int .i32, 7⟩]) naive_run
    (fun x => SingleThreaded.Exec.BehaviourRefinement.not_step_of_terminal
      ⟨.values [.num ⟨.int .i32, 7⟩], rfl⟩) rfl hm
  simp at hsub

/-- **The naive rewrite under `try_table` is refuted**: the behaviours of the invocation differ. -/
theorem naive_not_equiv (o : SingleThreaded.GrowOracle) :
    behaviours (SingleThreaded.profile o) SingleThreaded.Det.noHost (storeC : Store H) 0 [] ≠
      behaviours (SingleThreaded.profile o) SingleThreaded.Det.noHost (storeN : Store H) 0 [] :=
  fun h => (naive_behaviours_ne o).2 (h ▸ (naive_behaviours_ne o).1)

/-- info: 'Silmaril.Wasm.LimeCompile.TailCex.naive_not_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms naive_not_equiv

end Silmaril.Wasm.LimeCompile.TailCex
