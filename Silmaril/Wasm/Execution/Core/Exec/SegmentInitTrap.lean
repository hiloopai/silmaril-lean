module

public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInit

@[expose] public section

/-! # Trap-aware segment initialisation for Core 3.0

`initSegments?` (in `Exec/SegmentInit.lean`) reports out-of-bounds
`table.init`/`memory.init` as `none`. In SpecTec (4.4) this situation traps
(`Step_read/table.init-oob`, `Step_read/memory.init-oob`), and the trap then
absorbs the rest of the segment code (`Step_pure/trap-instrs`).

This file adds `initSegmentsT?`, which distinguishes success (`.ok`), a trap
(`.trap s`, with `s` the store at the trapping instruction) and failure (`.fail`),
and `instantiateInitT?`, which returns the trapped configuration
`⟨s, f, [trap]⟩` in that case.

* `initSegmentsT?_ok_iff`: on success it agrees with `initSegments?`.
* `initSegmentsT?_trap_steps`: a trap result is reachable by `Steps` from the
  segment code.
* `instantiateInitT?_sound` and `instantiateInitT?_of_instantiateInit?`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Outcome of a trap-aware initialisation step. -/
inductive SegResult (H : Type) (α : Type) where
  | ok (a : α)
  | trap (s : Store H)
  | fail

/-- The initial bounds check of `table.init x y` fails (after both lookups succeed). -/
def tableInitOob? (s : Store H) (f : Frame) (x : TableIdx) (y : ElemIdx) (a : AddrType)
    (i : BitVec a.intType.width) (j n : BitVec 32) : Bool :=
  match s.table? f x, s.elem? f y with
  | some (_, ti), some (_, ei) =>
    decide (ti.refs.length < i.toNat + n.toNat ∨ ei.refs.length < j.toNat + n.toNat)
  | _, _ => false

/-- The initial bounds check of `memory.init x y` fails (after both lookups succeed). -/
def memoryInitOob? (s : Store H) (f : Frame) (x : MemIdx) (y : DataIdx) (a : AddrType)
    (i : BitVec a.intType.width) (j n : BitVec 32) : Bool :=
  match s.mem? f x, s.data? f y with
  | some (_, mi), some (_, di) =>
    decide (mi.bytes.size < i.toNat + n.toNat ∨ di.bytes.size < j.toNat + n.toNat)
  | _, _ => false

section
variable (ev : Store H → Frame → Expr → Option (Store H × Val))

/-- The store at which `$runelem_(k, e)` traps, if it does. -/
def elemSegTrap? (s : Store H) (f : Frame) (k : Nat) (e : Elem) : Option (Store H) :=
  match e.mode with
  | .active y off =>
    match ev s f off with
    | some (s₁, v) =>
      match v.addr? with
      | some ⟨a, i⟩ =>
        if tableInitOob? s₁ f y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 e.init.length) then
          some s₁ else none
      | none => none
    | none => none
  | _ => none

/-- The store at which `$rundata_(k, d)` traps, if it does. -/
def dataSegTrap? (s : Store H) (f : Frame) (k : Nat) (d : Data) : Option (Store H) :=
  match d.mode with
  | .active y off =>
    match ev s f off with
    | some (s₁, v) =>
      match v.addr? with
      | some ⟨a, i⟩ =>
        if memoryInitOob? s₁ f y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 d.bytes.size) then
          some s₁ else none
      | none => none
    | none => none
  | _ => none

/-- Trap-aware `$runelem_(k, e)`. -/
def initElemSegT? (s : Store H) (f : Frame) (k : Nat) (e : Elem) : SegResult H (Store H) :=
  match initElemSeg? ev s f k e with
  | some s' => .ok s'
  | none =>
    match elemSegTrap? ev s f k e with
    | some s₁ => .trap s₁
    | none => .fail

/-- Trap-aware `$rundata_(k, d)`. -/
def initDataSegT? (s : Store H) (f : Frame) (k : Nat) (d : Data) : SegResult H (Store H) :=
  match initDataSeg? ev s f k d with
  | some s' => .ok s'
  | none =>
    match dataSegTrap? ev s f k d with
    | some s₁ => .trap s₁
    | none => .fail

def initElemListT? : Store H → Frame → List (Nat × Elem) → SegResult H (Store H)
  | s, _, [] => .ok s
  | s, f, (k, e) :: es =>
    match initElemSegT? ev s f k e with
    | .ok s₁ => initElemListT? s₁ f es
    | .trap s₁ => .trap s₁
    | .fail => .fail

def initDataListT? : Store H → Frame → List (Nat × Data) → SegResult H (Store H)
  | s, _, [] => .ok s
  | s, f, (k, d) :: ds =>
    match initDataSegT? ev s f k d with
    | .ok s₁ => initDataListT? s₁ f ds
    | .trap s₁ => .trap s₁
    | .fail => .fail

/-- Trap-aware element segments, then data segments. -/
def initSegmentsT? (s : Store H) (f : Frame) (m : Module) : SegResult H (Store H × Frame) :=
  match initElemListT? ev s f ((List.range m.elems.length).zip m.elems) with
  | .ok s₁ =>
    match initDataListT? ev s₁ f ((List.range m.data.length).zip m.data) with
    | .ok s₂ => .ok (s₂, f)
    | .trap t => .trap t
    | .fail => .fail
  | .trap t => .trap t
  | .fail => .fail

end

/-! ## Agreement -/

variable {ev : Store H → Frame → Expr → Option (Store H × Val)}

theorem initElemSegT?_ok_iff {s s' : Store H} {f : Frame} {k : Nat} {e : Elem} :
    initElemSegT? ev s f k e = .ok s' ↔ initElemSeg? ev s f k e = some s' := by
  unfold initElemSegT?
  split
  · rename_i h; rw [h]; simp
  · rename_i h; rw [h]; split <;> simp

theorem initDataSegT?_ok_iff {s s' : Store H} {f : Frame} {k : Nat} {d : Data} :
    initDataSegT? ev s f k d = .ok s' ↔ initDataSeg? ev s f k d = some s' := by
  unfold initDataSegT?
  split
  · rename_i h; rw [h]; simp
  · rename_i h; rw [h]; split <;> simp

theorem initElemListT?_ok_iff :
    ∀ {s s' : Store H} {f : Frame} {es : List (Nat × Elem)},
      initElemListT? ev s f es = .ok s' ↔ initElemList? ev s f es = some s'
  | s, s', f, [] => by simp [initElemListT?, initElemList?]
  | s, s', f, (k, e) :: es => by
    simp only [initElemListT?, initElemList?]
    cases h : initElemSeg? ev s f k e with
    | none =>
      cases h' : initElemSegT? ev s f k e with
      | ok s₁ => rw [initElemSegT?_ok_iff, h] at h'; cases h'
      | trap t => simp
      | fail => simp
    | some s₁ =>
      rw [(initElemSegT?_ok_iff).2 h]
      exact initElemListT?_ok_iff

theorem initDataListT?_ok_iff :
    ∀ {s s' : Store H} {f : Frame} {ds : List (Nat × Data)},
      initDataListT? ev s f ds = .ok s' ↔ initDataList? ev s f ds = some s'
  | s, s', f, [] => by simp [initDataListT?, initDataList?]
  | s, s', f, (k, d) :: ds => by
    simp only [initDataListT?, initDataList?]
    cases h : initDataSeg? ev s f k d with
    | none =>
      cases h' : initDataSegT? ev s f k d with
      | ok s₁ => rw [initDataSegT?_ok_iff, h] at h'; cases h'
      | trap t => simp
      | fail => simp
    | some s₁ =>
      rw [(initDataSegT?_ok_iff).2 h]
      exact initDataListT?_ok_iff

theorem initSegmentsT?_ok_iff {s s' : Store H} {f f' : Frame} {m : Module} :
    initSegmentsT? ev s f m = .ok (s', f') ↔ initSegments? ev s f m = some (s', f') := by
  unfold initSegmentsT? initSegments? initElem? initData?
  cases h₁ : initElemList? ev s f ((List.range m.elems.length).zip m.elems) with
  | none =>
    cases h₁' : initElemListT? ev s f ((List.range m.elems.length).zip m.elems) with
    | ok s₁ => rw [initElemListT?_ok_iff, h₁] at h₁'; cases h₁'
    | trap t => simp
    | fail => simp
  | some s₁ =>
    rw [(initElemListT?_ok_iff).2 h₁]
    simp only [Option.map_some]
    cases h₂ : initDataList? ev s₁ f ((List.range m.data.length).zip m.data) with
    | none =>
      cases h₂' : initDataListT? ev s₁ f ((List.range m.data.length).zip m.data) with
      | ok s₂ => rw [initDataListT?_ok_iff, h₂] at h₂'; cases h₂'
      | trap t => simp
      | fail => simp
    | some s₂ =>
      rw [(initDataListT?_ok_iff).2 h₂]
      simp

theorem initSegmentsT?_of_initSegments? {s s' : Store H} {f f' : Frame} {m : Module}
    (h : initSegments? ev s f m = some (s', f')) : initSegmentsT? ev s f m = .ok (s', f') :=
  initSegmentsT?_ok_iff.2 h

/-! ## Trap soundness -/

variable {P : Profile} {host : HostSemantics H}

/-- A trap absorbs any trailing code. -/
theorem Steps.trap_append {s s' : Store H} {f f' : Frame} {is js : List Admin}
    (h : Steps P host ⟨s, f, is⟩ ⟨s', f', [.trap]⟩) :
    Steps P host ⟨s, f, is ++ js⟩ ⟨s', f', [.trap]⟩ := by
  have h1 := Steps.ctxtInstrs (vs := []) (rest := js) h
  simp only [vals, List.map_nil, List.nil_append] at h1
  cases js with
  | nil => simpa using h1
  | cons j js =>
    refine h1.trans (Relation.ReflTransGen.single ?_)
    have := Step.trapInstrs (P := P) (host := host) (s := s') (f := f') (vs := [])
      (rest := j :: js) (Or.inr (by simp))
    simpa [vals] using this

/-- Run a successful prefix, then trap in the remainder. -/
theorem Steps.prefix_trap {s s₁ s' : Store H} {f f₁ f' : Frame} {is js : List Admin}
    (h₁ : Steps P host ⟨s, f, is⟩ ⟨s₁, f₁, []⟩) (h₂ : Steps P host ⟨s₁, f₁, js⟩ ⟨s', f', [.trap]⟩) :
    Steps P host ⟨s, f, is ++ js⟩ ⟨s', f', [.trap]⟩ :=
  (Steps.append_suffix h₁).trans h₂

/-- Evaluate an offset then trap in the remaining (constant-prefixed) code. -/
theorem offset_trap (hev : EvalSound P host ev) {s s₁ s' : Store H} {f : Frame} {off : Expr}
    {v : Val} {rest : List Admin} (he : ev s f off = some (s₁, v))
    (hr : Steps P host ⟨s₁, f, v.toAdmin :: rest⟩ ⟨s', f, [.trap]⟩) :
    Steps P host ⟨s, f, expression off ++ rest⟩ ⟨s', f, [.trap]⟩ := by
  have h1 := Steps.ctxtInstrs (vs := []) (rest := rest) (hev _ _ _ _ _ he)
  simp only [vals, List.map_nil, List.nil_append, List.map_cons, List.singleton_append] at h1
  exact h1.trans hr

theorem elemSegTrap?_steps (hev : EvalSound P host ev) {s s' : Store H} {f : Frame} {k : Nat}
    {e : Elem} (h : elemSegTrap? ev s f k e = some s') :
    Steps P host ⟨s, f, expression (runElem k e)⟩ ⟨s', f, [.trap]⟩ := by
  unfold elemSegTrap? at h
  unfold runElem
  split at h
  · rename_i y off hm
    rw [hm]
    split at h
    · rename_i s₁ v he
      split at h
      · rename_i a i hv
        split at h
        · rename_i hoob
          injection h with h; subst h
          simp only [expression, List.map_append, List.map_cons, List.map_nil]
          refine offset_trap hev he ?_
          rw [Val.toAdmin_of_addr? hv]
          unfold tableInitOob? at hoob
          split at hoob
          · rename_i ta ti ea ei ht hel
            have hb := of_decide_eq_true hoob
            have hs : Step P host ⟨s₁, f, [aconst a i, constI32 0,
                constI32 (BitVec.ofNat 32 e.init.length), .plain (.tableInit y ⟨Fin.ofNat _ k⟩)]⟩
                ⟨s₁, f, [.trap]⟩ := Step.table (.initOob ht hel hb)
            exact Steps.trap_append (js := [.plain (.elemDrop ⟨Fin.ofNat _ k⟩)]) hs.steps
          · cases hoob
        · cases h
      · cases h
    · cases h
  · cases h

theorem dataSegTrap?_steps (hev : EvalSound P host ev) {s s' : Store H} {f : Frame} {k : Nat}
    {d : Data} (h : dataSegTrap? ev s f k d = some s') :
    Steps P host ⟨s, f, expression (runData k d)⟩ ⟨s', f, [.trap]⟩ := by
  unfold dataSegTrap? at h
  unfold runData
  split at h
  · rename_i y off hm
    rw [hm]
    split at h
    · rename_i s₁ v he
      split at h
      · rename_i a i hv
        split at h
        · rename_i hoob
          injection h with h; subst h
          simp only [expression, List.map_append, List.map_cons, List.map_nil]
          refine offset_trap hev he ?_
          rw [Val.toAdmin_of_addr? hv]
          unfold memoryInitOob? at hoob
          split at hoob
          · rename_i ma mi da di hmm hd
            have hb := of_decide_eq_true hoob
            have hs : Step P host ⟨s₁, f, [aconst a i, constI32 0,
                constI32 (BitVec.ofNat 32 d.bytes.size), .plain (.memoryInit y ⟨Fin.ofNat _ k⟩)]⟩
                ⟨s₁, f, [.trap]⟩ := Step.memory (.initOob hmm hd hb)
            exact Steps.trap_append (js := [.plain (.dataDrop ⟨Fin.ofNat _ k⟩)]) hs.steps
          · cases hoob
        · cases h
      · cases h
    · cases h
  · cases h

theorem initElemSegT?_trap_steps (hev : EvalSound P host ev) {s s' : Store H} {f : Frame}
    {k : Nat} {e : Elem} (h : initElemSegT? ev s f k e = .trap s') :
    Steps P host ⟨s, f, expression (runElem k e)⟩ ⟨s', f, [.trap]⟩ := by
  unfold initElemSegT? at h
  split at h
  · cases h
  · split at h
    · rename_i s₁ ht; cases h; exact elemSegTrap?_steps hev ht
    · cases h

theorem initDataSegT?_trap_steps (hev : EvalSound P host ev) {s s' : Store H} {f : Frame}
    {k : Nat} {d : Data} (h : initDataSegT? ev s f k d = .trap s') :
    Steps P host ⟨s, f, expression (runData k d)⟩ ⟨s', f, [.trap]⟩ := by
  unfold initDataSegT? at h
  split at h
  · cases h
  · split at h
    · rename_i s₁ ht; cases h; exact dataSegTrap?_steps hev ht
    · cases h

theorem initElemListT?_trap_steps (hev : EvalSound P host ev) :
    ∀ {s s' : Store H} {f : Frame} {es : List (Nat × Elem)},
      initElemListT? ev s f es = .trap s' →
      Steps P host ⟨s, f, expression (es.flatMap fun (i, e) => runElem i e)⟩ ⟨s', f, [.trap]⟩
  | s, s', f, [], h => by cases h
  | s, s', f, (k, e) :: es, h => by
    simp only [initElemListT?] at h
    simp only [List.flatMap_cons, expression, List.map_append]
    split at h
    · rename_i s₁ h₁
      exact Steps.prefix_trap (initElemSeg?_steps hev (initElemSegT?_ok_iff.1 h₁))
        (initElemListT?_trap_steps hev h)
    · rename_i s₁ h₁
      cases h
      exact Steps.trap_append (initElemSegT?_trap_steps hev h₁)
    · cases h

theorem initDataListT?_trap_steps (hev : EvalSound P host ev) :
    ∀ {s s' : Store H} {f : Frame} {ds : List (Nat × Data)},
      initDataListT? ev s f ds = .trap s' →
      Steps P host ⟨s, f, expression (ds.flatMap fun (i, d) => runData i d)⟩ ⟨s', f, [.trap]⟩
  | s, s', f, [], h => by cases h
  | s, s', f, (k, d) :: ds, h => by
    simp only [initDataListT?] at h
    simp only [List.flatMap_cons, expression, List.map_append]
    split at h
    · rename_i s₁ h₁
      exact Steps.prefix_trap (initDataSeg?_steps hev (initDataSegT?_ok_iff.1 h₁))
        (initDataListT?_trap_steps hev h)
    · rename_i s₁ h₁
      cases h
      exact Steps.trap_append (initDataSegT?_trap_steps hev h₁)
    · cases h

/-- Main theorem: a trapping trap-aware segment initialisation is reproduced by
running the element and data segment code of `$instantiate` to `trap`. -/
theorem initSegmentsT?_trap_steps (hev : EvalSound P host ev) {s s' : Store H} {f : Frame}
    {m : Module} (h : initSegmentsT? ev s f m = .trap s') :
    Steps P host
      ⟨s, f, expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
        expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d)⟩
      ⟨s', f, [.trap]⟩ := by
  unfold initSegmentsT? at h
  split at h
  · rename_i s₁ h₁
    split at h
    · cases h
    · rename_i t h₂
      cases h
      exact Steps.prefix_trap (initElemList?_steps hev (initElemListT?_ok_iff.1 h₁))
        (initDataListT?_trap_steps hev h₂)
    · cases h
  · rename_i t h₁
    cases h
    exact Steps.trap_append (initElemListT?_trap_steps hev h₁)
  · cases h

/-! ## Trap-aware instantiation -/

/-- Concrete instantiation with trapping segment initialisation: on a trap, the
result is the trapped configuration (the start function is not run). -/
def instantiateInitT? (s : Store H) (m : Module) (xas : List ExternAddr) : Option (Config H) :=
  match prepare? evalConst? s m xas with
  | none => none
  | some (c, st) =>
    match initSegmentsT? evalConst? c.store c.frame m with
    | .ok (s', f') => some ((⟨s', f', []⟩ : Config H).withStart st)
    | .trap s' => some ⟨s', c.frame, [.trap]⟩
    | .fail => none

theorem Steps.withStart_trap {c : Config H} {s' : Store H} {f' : Frame} {st : Option FuncIdx}
    (h : Steps P host c ⟨s', f', [.trap]⟩) :
    Steps P host (c.withStart st) ⟨s', f', [.trap]⟩ := by
  rcases c with ⟨s, f, is⟩
  cases st with
  | none => exact h
  | some x => simpa [Config.withStart] using Steps.trap_append (js := [.plain (.call x)]) h

theorem instantiateInitT?_sound {s : Store H} {m : Module} {xas : List ExternAddr}
    {c' : Config H}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateInitT? s m xas = some c') :
    ∃ c₀, Instantiate P host s m xas c₀ ∧ Steps P host c₀ c' := by
  unfold instantiateInitT? at h
  split at h
  · cases h
  · rename_i c st hp
    refine ⟨c.withStart st, (prepare?_sound evalConst?_evalSound hp hvalid).2, ?_⟩
    split at h
    · rename_i s' f' hi
      cases h
      have hs := initSegments?_steps (P := P) (host := host) evalConst?_evalSound
        (initSegmentsT?_ok_iff.1 hi)
      rw [← prepare?_code hp] at hs
      exact Steps.withStart hs
    · rename_i s' hi
      cases h
      have hs := initSegmentsT?_trap_steps (P := P) (host := host) evalConst?_evalSound hi
      rw [← prepare?_code hp] at hs
      exact Steps.withStart_trap hs
    · cases h

theorem instantiateInitT?_of_instantiateInit? {s : Store H} {m : Module}
    {xas : List ExternAddr} {c' : Config H} (h : instantiateInit? s m xas = some c') :
    instantiateInitT? s m xas = some c' := by
  unfold instantiateInit? at h
  unfold instantiateInitT?
  split at h
  · cases h
  · rename_i c st hp
    rw [hp]
    split at h
    · cases h
    · rename_i s' f' hi
      simp only [initSegmentsT?_of_initSegments? hi]
      exact h

end Silmaril.Wasm.Execution.Core
