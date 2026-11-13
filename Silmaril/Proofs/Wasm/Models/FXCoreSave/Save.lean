module

public import Silmaril.Proofs.Wasm.Models.FXCoreSave.Run

/-!
# The save code, the check and the mode transitions in Core 3.0

* **`save_run`**: from a frame whose locals `0, …, n-1` hold `q.locals`, the save code builds
  the record struct of `q` with the old buffer head as next pointer, stores it in the buffer
  global and reaches `return`;
* `chk_normal`, **`chk_unwind`**: the check with this save code is a no-op in normal mode and
  saves and returns in any other mode;
* `setMode_run`: `i32.const k; global.set m`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXCoreSave

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FXCoreSave
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem i32_toAdmin (c : BitVec 32) : (Val.i32 c).toAdmin = .plain (.intConst .i32 c) := rfl

/-- **The save code.** -/
theorem save_run {s : Store H} {f : Frame} {x : TypeIdx} {b : GlobalIdx} {n : Nat}
    (hx : RecTy f x n) {ab : Nat} {gb : GlobalInst} (hb : s.global? f b = some (ab, gb))
    (q : CRec) (hL : LocalsAre f q.locals) (hn : q.locals.length = n) (rest : List Admin) :
    ∃ d, Steps P host ⟨s, f, expression (saveCode x b n q.fn q.r) ++ rest⟩
      ⟨saveStore s d q gb.value ab, f, [.plain .return_] ++ rest⟩ := by
  obtain ⟨d, h3⟩ : ∃ d, Step P host ⟨s, f, vals (q.fields gb.value) ++ [.plain (.structNew x)]⟩
      ⟨s.addStruct ⟨d, (q.fields gb.value).map .val⟩, f, [.ref (.struct s.structs.length)]⟩ :=
    step_structNew hx (q.fields gb.value) (by simp [CRec.fields, hn])
  let s₁ : Store H := s.addStruct ⟨d, (q.fields gb.value).map .val⟩
  let tl : List Admin := [.plain (.globalSet b), .plain .return_] ++ rest
  have h1 : Steps P host ⟨s, f, expression (saveCode x b n q.fn q.r) ++ rest⟩
      ⟨s, f, vals (q.locals ++ [.i32 q.fn, .i32 q.r]) ++ [.plain (.globalGet b)] ++
        ([.plain (.structNew x)] ++ tl)⟩ :=
    steps_eq (getLocals_run (s := s) hL []
      ([.plain (.intConst .i32 q.fn), .plain (.intConst .i32 q.r), .plain (.globalGet b),
        .plain (.structNew x)] ++ tl)) (by simp [saveCode, getLocals, expression, vals, tl, hn])
      (by simp [vals, tl, i32_toAdmin])
  have h2 : Step P host
      ⟨s, f, vals (q.locals ++ [.i32 q.fn, .i32 q.r]) ++ [.plain (.globalGet b)] ++
        ([.plain (.structNew x)] ++ tl)⟩
      ⟨s, f, vals [] ++ (vals (q.fields gb.value) ++ [.plain (.structNew x)]) ++ tl⟩ :=
    step_eq (step_ctx (q.locals ++ [.i32 q.fn, .i32 q.r]) ([.plain (.structNew x)] ++ tl)
      (step_globalGet hb)) rfl (by simp [vals, CRec.fields, tl])
  have h3' : Step P host
      ⟨s, f, vals [] ++ (vals (q.fields gb.value) ++ [.plain (.structNew x)]) ++ tl⟩
      ⟨s₁, f, vals [] ++ [(Val.ref (.struct s.structs.length)).toAdmin, .plain (.globalSet b)] ++
        ([.plain .return_] ++ rest)⟩ :=
    step_eq (step_ctx [] tl h3) rfl (by simp [vals, Val.toAdmin, tl, s₁])
  have hb₁ : s₁.global? f b = some (ab, gb) := hb
  have h4 : Step P host
      ⟨s₁, f, vals [] ++ [(Val.ref (.struct s.structs.length)).toAdmin, .plain (.globalSet b)] ++
        ([.plain .return_] ++ rest)⟩
      ⟨saveStore s d q gb.value ab, f, [.plain .return_] ++ rest⟩ :=
    step_eq (step_ctx [] ([.plain .return_] ++ rest)
      (step_globalSet hb₁ (.ref (.struct s.structs.length)))) rfl (by simp [vals, saveStore, s₁])
  exact ⟨d, h1.trans (((Relation.ReflTransGen.single h2).tail h3').tail h4)⟩

/-- Entering a block with no parameters. -/
theorem step_block_empty {s : Store H} {f : Frame} (body : List Instr) :
    Step P host ⟨s, f, [.plain (.block .empty body)]⟩ ⟨s, f, [.label 0 [] (expression body)]⟩ := by
  have h : Step P host ⟨s, f, vals [] ++ [.plain (.block .empty body)]⟩
      ⟨s, f, [.label 0 [] (vals [] ++ expression body)]⟩ :=
    .block (t₁ := []) (t₂ := []) rfl rfl
  simpa only [vals, List.map_nil, List.nil_append, List.length_nil] using h

/-- Read the mode global and branch on it: in normal mode the `if` takes its empty else arm. -/
theorem chk_normal {s : Store H} {f : Frame} {m : GlobalIdx} {am : Nat} {gm : GlobalInst}
    (hm : s.global? f m = some (am, gm)) (hv : gm.value = .i32 0) (x : TypeIdx) (b : GlobalIdx)
    (n : Nat) (fn r : BitVec 32) (rest : List Admin) :
    Steps P host ⟨s, f, expression (chkCode m x b n fn r) ++ rest⟩ ⟨s, f, rest⟩ := by
  have h1 := step_ctx [] ([.plain (.if_ .empty (saveCode x b n fn r) [])] ++ rest)
    (step_globalGet (P := P) (host := host) hm)
  have e1 : vals [] ++ [gm.value.toAdmin] ++ ([.plain (.if_ .empty (saveCode x b n fn r) [])] ++
      rest) = vals [] ++ [constI32 0, .plain (.if_ .empty (saveCode x b n fn r) [])] ++ rest := by
    simp [vals, hv, constI32]
  rw [e1] at h1
  have h2 := step_ctx [] rest
    (Step.ifFalse (P := P) (host := host) (s := s) (f := f) (bt := .empty)
      (b₁ := saveCode x b n fn r) (b₂ := []))
  have h3 := step_ctx [] rest (step_block_empty (P := P) (host := host) (s := s) (f := f) [])
  have h4 := step_ctx [] rest
    (Step.labelVals (P := P) (host := host) (s := s) (f := f) (n := 0) (cont := []) (vs := []))
  have e0 : expression (chkCode m x b n fn r) ++ rest =
      vals [] ++ [.plain (.globalGet m)] ++ ([.plain (.if_ .empty (saveCode x b n fn r) [])] ++
        rest) := by simp [chkCode, expression, vals]
  rw [e0]
  have e4 : vals [] ++ vals [] ++ rest = rest := by simp [vals]
  rw [e4] at h4
  exact (((Relation.ReflTransGen.single h1).tail h2).tail h3).tail h4

/-- The check reads the mode global and enters its `if`. -/
theorem chk_enter {s : Store H} {f : Frame} {m : GlobalIdx} {am : Nat} {gm : GlobalInst}
    (hm : s.global? f m = some (am, gm)) {c : BitVec 32} (hv : gm.value = .i32 c)
    (save : List Instr) (rest : List Admin) :
    Step P host ⟨s, f, expression [.globalGet m, .if_ .empty save []] ++ rest⟩
      ⟨s, f, vals [] ++ [constI32 c, .plain (.if_ .empty save [])] ++ rest⟩ :=
  step_eq (step_ctx [] ([.plain (.if_ .empty save [])] ++ rest) (step_globalGet hm))
    (by simp [vals, expression]) (by simp [vals, hv, constI32])

/-- **The check in unwinding mode** (any non-zero mode): the save code runs and the frame
reaches `return`. -/
theorem chk_unwind {s : Store H} {f : Frame} {m : GlobalIdx} {am : Nat} {gm : GlobalInst}
    (hm : s.global? f m = some (am, gm)) {c : BitVec 32} (hv : gm.value = .i32 c) (hc : c ≠ 0)
    {x : TypeIdx} {b : GlobalIdx} {n : Nat} (hx : RecTy f x n) {ab : Nat} {gb : GlobalInst}
    (hb : s.global? f b = some (ab, gb)) (q : CRec) (hL : LocalsAre f q.locals)
    (hn : q.locals.length = n) (rest : List Admin) :
    ∃ d, Steps P host ⟨s, f, expression (chkCode m x b n q.fn q.r) ++ rest⟩
      ⟨saveStore s d q gb.value ab, f, [.plain .return_] ++ rest⟩ := by
  obtain ⟨d, hs⟩ : ∃ d, Steps P host ⟨s, f, expression (saveCode x b n q.fn q.r) ++ []⟩
      ⟨saveStore s d q gb.value ab, f, [.plain .return_] ++ []⟩ := save_run hx hb q hL hn []
  let save := saveCode x b n q.fn q.r
  have h1 : Step P host ⟨s, f, expression (chkCode m x b n q.fn q.r) ++ rest⟩
      ⟨s, f, vals [] ++ [constI32 c, .plain (.if_ .empty save [])] ++ rest⟩ :=
    chk_enter hm hv save rest
  have h2 : Step P host ⟨s, f, vals [] ++ [constI32 c, .plain (.if_ .empty save [])] ++ rest⟩
      ⟨s, f, vals [] ++ [.plain (.block .empty save)] ++ rest⟩ :=
    step_ctx [] rest (.ifTrue hc)
  have h3 : Step P host ⟨s, f, vals [] ++ [.plain (.block .empty save)] ++ rest⟩
      ⟨s, f, vals [] ++ [.label 0 [] (expression save ++ [])] ++ rest⟩ :=
    step_eq (step_ctx [] rest (step_block_empty save)) rfl (by simp)
  have h4 : Steps P host ⟨s, f, vals [] ++ [.label 0 [] (expression save ++ [])] ++ rest⟩
      ⟨saveStore s d q gb.value ab, f,
        vals [] ++ [.label 0 [] (vals [] ++ [.plain .return_] ++ [])] ++ rest⟩ :=
    steps_eq (steps_ctx [] rest (steps_label 0 [] hs)) rfl (by simp [vals])
  have h5 : Step P host
      ⟨saveStore s d q gb.value ab, f,
        vals [] ++ [.label 0 [] (vals [] ++ [.plain .return_] ++ [])] ++ rest⟩
      ⟨saveStore s d q gb.value ab, f, [.plain .return_] ++ rest⟩ :=
    step_eq (step_ctx [] rest (.returnLabel (vs := []))) rfl (by simp [vals])
  exact ⟨d, ((((Relation.ReflTransGen.single h1).tail h2).tail h3).trans h4).tail h5⟩

/-- **A mode transition.** -/
theorem setMode_run {s : Store H} {f : Frame} {m : GlobalIdx} {am : Nat} {gm : GlobalInst}
    (hm : s.global? f m = some (am, gm)) (k : BitVec 32) (rest : List Admin) :
    Step P host ⟨s, f, expression (setMode m k) ++ rest⟩ ⟨s.setGlobal am (.i32 k), f, rest⟩ := by
  have h := step_ctx (P := P) (host := host) [] rest (step_globalSet hm (.i32 k))
  simpa [setMode, expression, vals, i32_toAdmin] using h

end Silmaril.Proofs.Wasm.Models.FXCoreSave
