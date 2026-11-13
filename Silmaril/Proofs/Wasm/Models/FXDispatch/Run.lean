module

public import Silmaril.Wasm.Models.FXDispatch.Defs

/-!
# Runs of the dispatch prologue in Core 3.0

For any profile and host:

* `step_app`, `step_wrap`: a step lifts past code after it and into the labels of `wrap`;
* `enter`: `nest segs Y` enters its blocks, reaching `wrap segs Y`;
* `select`: `global.get g; br_table` with resume index `i` in `g` steps to `br i`;
* `branch`: `br j` inside `wrap segs` leaves `j + 1` labels and continues with segment `j`;
* **`prologue_run`**: the prologue with index `i` reaches `wrap (segs.drop (i + 1)) segᵢ`;
* **`resumeAt_run`**: so does the code written to start at resume point `i`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXDispatch

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FXDispatch
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem lab_toNat {j : Nat} (hj : j < 2 ^ 32) : (lab j).toNat = j := Nat.mod_eq_of_lt hj

theorem labelPred_lab {j : Nat} (hj : j + 1 < 2 ^ 32) : labelPred (lab (j + 1)) = lab j := by
  apply Idx.toNat_injective
  show (lab (j + 1)).toNat - 1 = (lab j).toNat
  rw [lab_toNat hj, lab_toNat (by omega)]
  rfl

/-- A step lifts past code after it. -/
theorem step_app {s s' : Store H} {f f' : Frame} {Y Y' : List Admin} (rest : List Admin)
    (h : Step P host ⟨s, f, Y⟩ ⟨s', f', Y'⟩) :
    Step P host ⟨s, f, Y ++ rest⟩ ⟨s', f', Y' ++ rest⟩ := by
  cases rest with
  | nil => simpa only [List.append_nil] using h
  | cons r rs =>
    have h' : Step P host ⟨s, f, vals [] ++ Y ++ r :: rs⟩ ⟨s', f', vals [] ++ Y' ++ r :: rs⟩ :=
      .ctxtInstrs h (.inr (List.cons_ne_nil r rs))
    simpa only [vals, List.map_nil, List.nil_append] using h'

/-- A step lifts into the labels of `wrap`. -/
theorem step_wrap {s s' : Store H} {f f' : Frame} (segs : List (List Instr)) :
    ∀ {X X' : List Admin}, Step P host ⟨s, f, X⟩ ⟨s', f', X'⟩ →
      Step P host ⟨s, f, wrap segs X⟩ ⟨s', f', wrap segs X'⟩ := by
  induction segs with
  | nil => exact fun h => h
  | cons seg segs ih =>
    intro X X' h
    have hl : Step P host ⟨s, f, [.label 0 [] X]⟩ ⟨s', f', [.label 0 [] X']⟩ := .ctxtLabel h
    exact ih (step_app (expression seg) hl)

/-- Runs on code with a fixed store and frame. -/
abbrev CSteps (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) :=
  Relation.ReflTransGen (fun a b : List Admin => Step P host ⟨s, f, a⟩ ⟨s, f, b⟩)

theorem CSteps.steps {s : Store H} {f : Frame} {X X' : List Admin}
    (h : CSteps P host s f X X') : Steps P host ⟨s, f, X⟩ ⟨s, f, X'⟩ :=
  h.lift (fun X => (⟨s, f, X⟩ : Config H)) (fun _ _ hs => hs)

theorem CSteps.wrap {s : Store H} {f : Frame} (segs : List (List Instr)) {X X' : List Admin}
    (h : CSteps P host s f X X') : CSteps P host s f (wrap segs X) (wrap segs X') :=
  h.lift (fun X => Silmaril.Wasm.Models.FXDispatch.wrap segs X) (fun _ _ hs => step_wrap segs hs)

/-- Entering a block with no parameters. -/
theorem step_block {s : Store H} {f : Frame} (body : List Instr) :
    Step P host ⟨s, f, [.plain (.block .empty body)]⟩ ⟨s, f, [.label 0 [] (expression body)]⟩ := by
  have h : Step P host ⟨s, f, vals [] ++ [.plain (.block .empty body)]⟩
      ⟨s, f, [.label 0 [] (vals [] ++ expression body)]⟩ :=
    .block (t₁ := []) (t₂ := []) rfl rfl
  simpa only [vals, List.map_nil, List.nil_append, List.length_nil] using h

/-- **`nest segs Y` enters its blocks.** -/
theorem enter {s : Store H} {f : Frame} (segs : List (List Instr)) :
    ∀ Y : List Instr, CSteps P host s f (expression (nest segs Y)) (wrap segs (expression Y)) := by
  induction segs with
  | nil => exact fun Y => .refl
  | cons seg segs ih =>
    intro Y
    have hb : Step P host ⟨s, f, .plain (.block .empty Y) :: expression seg⟩
        ⟨s, f, .label 0 [] (expression Y) :: expression seg⟩ :=
      step_app (expression seg) (step_block Y)
    exact (ih (.block .empty Y :: seg)).tail (step_wrap segs hb)

/-- The dispatch table selects label `j`. -/
theorem table_get {n j : Nat} (hj : j < n) : ((List.range n).map lab)[j]? = some (lab j) := by
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some]

/-- **`global.get g; br_table` with resume index `i` in `g` branches to label `i`.** -/
theorem select {s : Store H} {f : Frame} {g : GlobalIdx} {a : Nat} {gi : GlobalInst}
    {i : BitVec 32} (hg : s.global? f g = some (a, gi)) (hv : gi.value = Val.i32 i) {n : Nat}
    (hi : i.toNat < n) :
    CSteps P host s f [.plain (.globalGet g), .plain (table n)] [.plain (.br (lab i.toNat))] := by
  have h1 : Step P host ⟨s, f, [.plain (.globalGet g)]⟩ ⟨s, f, [constI32 i]⟩ := by
    have h := Step.variable (P := P) (host := host) (VariableStep.globalGet hg)
    rw [hv] at h
    exact h
  have h2 : Step P host ⟨s, f, [constI32 i, .plain (table n)]⟩ ⟨s, f, [.plain (.br (lab i.toNat))]⟩ :=
    .brTableLt (table_get hi)
  have h1' : Step P host ⟨s, f, [.plain (.globalGet g), .plain (table n)]⟩
      ⟨s, f, [constI32 i, .plain (table n)]⟩ := step_app [.plain (table n)] h1
  exact .tail (.single h1') h2

/-- The branch to label `0` leaves the innermost label. -/
theorem step_br_zero {s : Store H} {f : Frame} (rest : List Admin) :
    Step P host ⟨s, f, [.label 0 [] (.plain (.br (lab 0)) :: rest)]⟩ ⟨s, f, []⟩ := by
  have h : Step P host ⟨s, f, [.label 0 [] (vals [] ++ vals [] ++ [.plain (.br (lab 0))] ++ rest)]⟩
      ⟨s, f, vals [] ++ expression []⟩ := .brLabelZero rfl rfl
  simpa only [vals, expression, List.map_nil, List.nil_append, List.singleton_append] using h

/-- A branch to label `j + 1` leaves one label. -/
theorem step_br_succ {s : Store H} {f : Frame} {j : Nat} (hj : j + 1 < 2 ^ 32)
    (rest : List Admin) :
    Step P host ⟨s, f, [.label 0 [] (.plain (.br (lab (j + 1))) :: rest)]⟩
      ⟨s, f, [.plain (.br (lab j))]⟩ := by
  have h : Step P host ⟨s, f, [.label 0 [] (vals [] ++ [.plain (.br (lab (j + 1)))] ++ rest)]⟩
      ⟨s, f, vals [] ++ [.plain (.br (labelPred (lab (j + 1))))]⟩ :=
    .brLabelSucc (by rw [lab_toNat hj]; omega)
  simpa only [vals, List.map_nil, List.nil_append, List.singleton_append, labelPred_lab hj]
    using h

/-- **`br j` inside `wrap segs` continues with segment `j`.** -/
theorem branch {s : Store H} {f : Frame} (segs : List (List Instr)) :
    ∀ (j : Nat) (rest : List Admin), j < segs.length → j < 2 ^ 32 →
      ∃ seg, segs[j]? = some seg ∧ CSteps P host s f (wrap segs (.plain (.br (lab j)) :: rest))
        (wrap (segs.drop (j + 1)) (expression seg)) := by
  induction segs with
  | nil => intro j rest hj; exact absurd hj (Nat.not_lt_zero _)
  | cons seg segs ih =>
    intro j rest hj hj32
    cases j with
    | zero =>
      have h : Step P host ⟨s, f, .label 0 [] (.plain (.br (lab 0)) :: rest) :: expression seg⟩
          ⟨s, f, [] ++ expression seg⟩ := step_app (expression seg) (step_br_zero rest)
      exact ⟨seg, rfl, .single (step_wrap segs h)⟩
    | succ j =>
      have h : Step P host
          ⟨s, f, .label 0 [] (.plain (.br (lab (j + 1))) :: rest) :: expression seg⟩
          ⟨s, f, [.plain (.br (lab j))] ++ expression seg⟩ :=
        step_app (expression seg) (step_br_succ hj32 rest)
      obtain ⟨seg', hseg', hrun⟩ := ih j (expression seg) (by simpa using hj) (by omega)
      exact ⟨seg', by simpa using hseg', Relation.ReflTransGen.head (step_wrap segs h) hrun⟩

/-- **The prologue with resume index `i` in global `g` reaches segment `i` in its labels.** -/
theorem prologue_run {s : Store H} {f : Frame} {g : GlobalIdx} {a : Nat} {gi : GlobalInst}
    {i : BitVec 32} (hg : s.global? f g = some (a, gi)) (hv : gi.value = Val.i32 i)
    {segs : List (List Instr)} (hi : i.toNat < segs.length) :
    ∃ seg, segs[i.toNat]? = some seg ∧
      Steps P host ⟨s, f, expression (prologue g segs)⟩
        ⟨s, f, wrap (segs.drop (i.toNat + 1)) (expression seg)⟩ := by
  have h1 : CSteps P host s f (expression (prologue g segs))
      (wrap segs [.plain (.globalGet g), .plain (table segs.length)]) :=
    enter segs [.globalGet g, table segs.length]
  have h2 : CSteps P host s f (wrap segs [.plain (.globalGet g), .plain (table segs.length)])
      (wrap segs [.plain (.br (lab i.toNat))]) := (select hg hv hi).wrap segs
  obtain ⟨seg, hseg, h3⟩ := branch (P := P) (host := host) (s := s) (f := f) segs i.toNat [] hi
    i.isLt
  exact ⟨seg, hseg, CSteps.steps (h1.trans (h2.trans h3))⟩

/-- **The code written to start at resume point `j` reaches the same configuration.** -/
theorem resumeAt_run {s : Store H} {f : Frame} {segs : List (List Instr)} {j : Nat}
    {seg : List Instr} (hseg : segs[j]? = some seg) :
    Steps P host ⟨s, f, expression (resumeAt segs j)⟩
      ⟨s, f, wrap (segs.drop (j + 1)) (expression seg)⟩ := by
  have h : resumeAt segs j = nest (segs.drop (j + 1)) seg := by
    simp only [resumeAt, hseg, Option.getD_some]
  rw [h]
  exact CSteps.steps (enter (segs.drop (j + 1)) seg)

/-- Read a global holding `i32 c`. -/
theorem step_global {s : Store H} {f : Frame} {m : GlobalIdx} {a : Nat} {gi : GlobalInst}
    {c : BitVec 32} (hg : s.global? f m = some (a, gi)) (hv : gi.value = Val.i32 c) :
    Step P host ⟨s, f, [.plain (.globalGet m)]⟩ ⟨s, f, [constI32 c]⟩ := by
  have h := Step.variable (P := P) (host := host) (VariableStep.globalGet hg)
  rw [hv] at h
  exact h

/-- **The check in normal mode is a no-op.** -/
theorem check_normal {s : Store H} {f : Frame} {m : GlobalIdx} {a : Nat} {gi : GlobalInst}
    (hg : s.global? f m = some (a, gi)) (hv : gi.value = Val.i32 0) (save : List Instr)
    (rest : List Admin) : CSteps P host s f (expression (check m save) ++ rest) rest := by
  have h1 : Step P host ⟨s, f, expression (check m save) ++ rest⟩
      ⟨s, f, [constI32 0, .plain (.if_ .empty save [])] ++ rest⟩ :=
    step_app _ (step_app [.plain (.if_ .empty save [])] (step_global hg hv))
  have h2 : Step P host ⟨s, f, [constI32 0, .plain (.if_ .empty save [])] ++ rest⟩
      ⟨s, f, [.plain (.block .empty [])] ++ rest⟩ := step_app rest .ifFalse
  have h3 : Step P host ⟨s, f, [.plain (.block .empty [])] ++ rest⟩
      ⟨s, f, [.label 0 [] (expression [])] ++ rest⟩ := step_app rest (step_block [])
  have h4 : Step P host ⟨s, f, [.label 0 [] (vals [])] ++ rest⟩ ⟨s, f, vals [] ++ rest⟩ :=
    step_app rest .labelVals
  exact .tail (.tail (.tail (.single h1) h2) h3) h4

/-- **The check in any other mode enters the save code.** -/
theorem check_save {s : Store H} {f : Frame} {m : GlobalIdx} {a : Nat} {gi : GlobalInst}
    {c : BitVec 32} (hg : s.global? f m = some (a, gi)) (hv : gi.value = Val.i32 c)
    (hc : c ≠ 0) (save : List Instr) (rest : List Admin) :
    CSteps P host s f (expression (check m save) ++ rest)
      (.label 0 [] (expression save) :: rest) := by
  have h1 : Step P host ⟨s, f, expression (check m save) ++ rest⟩
      ⟨s, f, [constI32 c, .plain (.if_ .empty save [])] ++ rest⟩ :=
    step_app _ (step_app [.plain (.if_ .empty save [])] (step_global hg hv))
  have h2 : Step P host ⟨s, f, [constI32 c, .plain (.if_ .empty save [])] ++ rest⟩
      ⟨s, f, [.plain (.block .empty save)] ++ rest⟩ := step_app rest (.ifTrue hc)
  have h3 : Step P host ⟨s, f, [.plain (.block .empty save)] ++ rest⟩
      ⟨s, f, [.label 0 [] (expression save)] ++ rest⟩ := step_app rest (step_block save)
  exact .tail (.tail (.single h1) h2) h3

end Silmaril.Proofs.Wasm.Models.FXDispatch
