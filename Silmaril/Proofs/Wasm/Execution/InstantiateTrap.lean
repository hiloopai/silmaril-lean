module

public import Silmaril.Wasm.Execution.InstantiateTrap.Defs
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitTrap
public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
public import Silmaril.Wasm.Execution.MemRep.Inst.Thms

/-!
# Proofs: instantiation that reports a segment trap with the residual store

* `initSegmentsR?_ok_iff`: on success the trap-aware segment initialisation is `initSegments?`
  (any representation);
* `initSegmentsR?_byteArray`: on `ByteArray` stores it is `initSegmentsT?`
  (`Exec/SegmentInitTrap`), whose traps are runs of the segment code to `trap`
  (`initSegmentsT?_trap_steps`);
* `initSegmentsR?_toBytes`, `instantiateT?_toBytes`, `instantiateOnceT?_toBytes`: reading the
  memories through `toBytes` commutes with them (lawful representations);
* `instantiateT?_ok_iff`, `instantiateOnceT?_ok_iff`, `instantiateOnceT?_of_nil`;
* `instantiateT?_trap_sound`, `instantiateT?_ok_sound`: the outcomes are runs of the
  specification's `Instantiate` configuration;
* `instantiateOnceT?_trap_steps`: a trap of single allocation is a run of the residue's
  segment code to `trap`;
* `instantiateCfg?_toBytes`, `instantiateCfg?_eq_none_iff`, `instantiateCfg?_sound`: the
  configuration form of `instantiateT?` is reached from the `Instantiate` configuration.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Execution.InstantiateTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

/-! ## Success -/

section Generic

variable {H R : Type} [MemRep R] {ev : Store H R → Frame → Expr → Option (Store H R × Val)}

omit [MemRep R] in
theorem initElemSegR?_ok_iff {s s' : Store H R} {f : Frame} {k : Nat} {e : Elem} :
    initElemSegR? ev s f k e = .ok s' ↔ initElemSeg? ev s f k e = some s' := by
  unfold initElemSegR?
  split
  · rename_i h; rw [h]; simp
  · rename_i h; rw [h]; split <;> simp

theorem initDataSegR?_ok_iff {s s' : Store H R} {f : Frame} {k : Nat} {d : Data} :
    initDataSegR? ev s f k d = .ok s' ↔ initDataSeg? ev s f k d = some s' := by
  unfold initDataSegR?
  split
  · rename_i h; rw [h]; simp
  · rename_i h; rw [h]; split <;> simp

omit [MemRep R] in
theorem initElemListR?_ok_iff :
    ∀ {s s' : Store H R} {f : Frame} {es : List (Nat × Elem)},
      initElemListR? ev s f es = .ok s' ↔ initElemList? ev s f es = some s'
  | s, s', f, [] => by simp [initElemListR?, initElemList?]
  | s, s', f, (k, e) :: es => by
    simp only [initElemListR?, initElemList?]
    cases h : initElemSeg? ev s f k e with
    | none =>
      cases h' : initElemSegR? ev s f k e with
      | ok s₁ => rw [initElemSegR?_ok_iff, h] at h'; cases h'
      | trap t => simp
      | fail => simp
    | some s₁ =>
      rw [(initElemSegR?_ok_iff).2 h]
      exact initElemListR?_ok_iff

theorem initDataListR?_ok_iff :
    ∀ {s s' : Store H R} {f : Frame} {ds : List (Nat × Data)},
      initDataListR? ev s f ds = .ok s' ↔ initDataList? ev s f ds = some s'
  | s, s', f, [] => by simp [initDataListR?, initDataList?]
  | s, s', f, (k, d) :: ds => by
    simp only [initDataListR?, initDataList?]
    cases h : initDataSeg? ev s f k d with
    | none =>
      cases h' : initDataSegR? ev s f k d with
      | ok s₁ => rw [initDataSegR?_ok_iff, h] at h'; cases h'
      | trap t => simp
      | fail => simp
    | some s₁ =>
      rw [(initDataSegR?_ok_iff).2 h]
      exact initDataListR?_ok_iff

theorem initSegmentsR?_ok_iff {s s' : Store H R} {f f' : Frame} {m : Module} :
    initSegmentsR? ev s f m = .ok (s', f') ↔ initSegments? ev s f m = some (s', f') := by
  unfold initSegmentsR? initSegments? initElem? initData?
  cases h₁ : initElemList? ev s f ((List.range m.elems.length).zip m.elems) with
  | none =>
    cases h₁' : initElemListR? ev s f ((List.range m.elems.length).zip m.elems) with
    | ok s₁ => rw [initElemListR?_ok_iff, h₁] at h₁'; cases h₁'
    | trap t => simp
    | fail => simp
  | some s₁ =>
    rw [(initElemListR?_ok_iff).2 h₁]
    simp only [Option.map_some]
    cases h₂ : initDataList? ev s₁ f ((List.range m.data.length).zip m.data) with
    | none =>
      cases h₂' : initDataListR? ev s₁ f ((List.range m.data.length).zip m.data) with
      | ok s₂ => rw [initDataListR?_ok_iff, h₂] at h₂'; cases h₂'
      | trap t => simp
      | fail => simp
    | some s₂ =>
      rw [(initDataListR?_ok_iff).2 h₂]
      simp

theorem instantiateT?_ok_iff {s s' : Store H R} {m : Module} {xas : List ExternAddr} {f : Frame}
    {st : Option FuncIdx} :
    instantiateT? s m xas = .ok s' f st ↔ prepareDirect? evalConst? s m xas = some (s', f, st) := by
  unfold instantiateT? prepareDirect?
  cases prepare? evalConst? s m xas with
  | none => simp
  | some p =>
    obtain ⟨c, st₀⟩ := p
    simp only
    cases h : initSegments? evalConst? c.store c.frame m with
    | none =>
      cases h' : initSegmentsR? evalConst? c.store c.frame m with
      | ok p => obtain ⟨s₂, f₂⟩ := p; rw [initSegmentsR?_ok_iff, h] at h'; cases h'
      | trap t => simp
      | fail => simp
    | some p =>
      obtain ⟨s₂, f₂⟩ := p
      rw [initSegmentsR?_ok_iff.2 h]
      simp [and_comm, eq_comm]

theorem instantiateOnceT?_ok_iff {s s' : Store H R} {m : Module} {xas : List ExternAddr}
    {f : Frame} {st : Option FuncIdx} :
    instantiateOnceT? s m xas = .ok s' f st ↔ instantiateOnce? s m xas = some (s', f, st) := by
  unfold instantiateOnceT? instantiateOnce?
  cases evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) with
  | none => simp
  | some p =>
    obtain ⟨s₁, f₁, vs⟩ := p
    exact instantiateT?_ok_iff

/-- On a module without globals, single allocation is the specification's (`$evalglobals`
allocates nothing). -/
theorem instantiateOnceT?_of_nil {s : Store H R} {m : Module} {xas : List ExternAddr}
    (h : m.globals = []) : instantiateOnceT? s m xas = instantiateT? s m xas := by
  unfold instantiateOnceT?
  simp [Module.closedGlobalTypes, h, evalGlobals?, globalAddrs, Module.globalResidue_of_nil h,
    instantiateT?]

end Generic

/-! ## Reading the memories through `toBytes` -/

section ToBytes

variable {H R : Type} [MemRep R]

theorem tableInitOobR?_toBytes (s : Store H R) f x y a i j n :
    tableInitOobR? s.toBytes f x y a i j n = tableInitOobR? s f x y a i j n := rfl

theorem memoryInitOobR?_toBytes [LawfulMemRep R] (s : Store H R) f x y a i j n :
    memoryInitOobR? s.toBytes f x y a i j n = memoryInitOobR? s f x y a i j n := by
  unfold memoryInitOobR?
  rw [Silmaril.Wasm.Execution.Core.Store.mem?_toBytes,
    show s.toBytes.data? f y = s.data? f y from rfl]
  rcases s.mem? f x with _ | ⟨ma, mi⟩ <;> rcases s.data? f y with _ | ⟨_, di⟩ <;> try rfl
  simp only [Option.map_some, MemInst.toBytes]
  rw [show MemRep.size (R := ByteArray) (MemRep.toBytes mi.bytes) = MemRep.size mi.bytes from
    (LawfulMemRep.size_eq _).symm]

/-- Read the stores of a segment outcome through `toBytes`. -/
def mapI : InitOutcome (Store H R) (Store H R) → InitOutcome (Store H) (Store H)
  | .ok s => .ok s.toBytes
  | .trap s => .trap s.toBytes
  | .fail => .fail

theorem elemSegTrapR?_toBytes (s : Store H R) f k e :
    elemSegTrapR? evalConst? s.toBytes f k e =
      (elemSegTrapR? evalConst? s f k e).map Store.toBytes := by
  unfold elemSegTrapR?
  split
  · rw [← evalConst?_toBytes]
    rcases evalConst? s f _ with _ | ⟨s₁, v⟩
    · rfl
    · simp only [Option.map_some]
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · simp only [tableInitOobR?_toBytes]
        split <;> simp_all
  · rfl

theorem dataSegTrapR?_toBytes [LawfulMemRep R] (s : Store H R) f k d :
    dataSegTrapR? evalConst? s.toBytes f k d =
      (dataSegTrapR? evalConst? s f k d).map Store.toBytes := by
  unfold dataSegTrapR?
  split
  · rw [← evalConst?_toBytes]
    rcases evalConst? s f _ with _ | ⟨s₁, v⟩
    · rfl
    · simp only [Option.map_some]
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · simp only [memoryInitOobR?_toBytes]
        split <;> simp_all
  · rfl

theorem initElemSegR?_toBytes (s : Store H R) f k e :
    initElemSegR? evalConst? s.toBytes f k e = mapI (initElemSegR? evalConst? s f k e) := by
  unfold initElemSegR?
  rw [initElemSeg?_toBytes, elemSegTrapR?_toBytes]
  rcases initElemSeg? evalConst? s f k e with _ | s'
  · rcases elemSegTrapR? evalConst? s f k e with _ | s₁ <;> rfl
  · rfl

theorem initDataSegR?_toBytes [LawfulMemRep R] (s : Store H R) f k d :
    initDataSegR? evalConst? s.toBytes f k d = mapI (initDataSegR? evalConst? s f k d) := by
  unfold initDataSegR?
  rw [initDataSeg?_toBytes, dataSegTrapR?_toBytes]
  rcases initDataSeg? evalConst? s f k d with _ | s'
  · rcases dataSegTrapR? evalConst? s f k d with _ | s₁ <;> rfl
  · rfl

theorem initElemListR?_toBytes (s : Store H R) f es :
    initElemListR? evalConst? s.toBytes f es = mapI (initElemListR? evalConst? s f es) := by
  induction es generalizing s with
  | nil => rfl
  | cons p es ih =>
    obtain ⟨k, e⟩ := p
    simp only [initElemListR?, initElemSegR?_toBytes]
    rcases initElemSegR? evalConst? s f k e with s₁ | s₁ | _
    · exact ih s₁
    · rfl
    · rfl

theorem initDataListR?_toBytes [LawfulMemRep R] (s : Store H R) f ds :
    initDataListR? evalConst? s.toBytes f ds = mapI (initDataListR? evalConst? s f ds) := by
  induction ds generalizing s with
  | nil => rfl
  | cons p ds ih =>
    obtain ⟨k, d⟩ := p
    simp only [initDataListR?, initDataSegR?_toBytes]
    rcases initDataSegR? evalConst? s f k d with s₁ | s₁ | _
    · exact ih s₁
    · rfl
    · rfl

/-- Read the stores of a segment-initialisation outcome through `toBytes`. -/
def mapIF : InitOutcome (Store H R) (Store H R × Frame) → InitOutcome (Store H) (Store H × Frame)
  | .ok (s, f) => .ok (s.toBytes, f)
  | .trap s => .trap s.toBytes
  | .fail => .fail

theorem initSegmentsR?_toBytes [LawfulMemRep R] (s : Store H R) f m :
    initSegmentsR? evalConst? s.toBytes f m = mapIF (initSegmentsR? evalConst? s f m) := by
  unfold initSegmentsR?
  rw [initElemListR?_toBytes]
  rcases initElemListR? evalConst? s f _ with s₁ | s₁ | _
  · simp only [mapI]
    rw [initDataListR?_toBytes]
    rcases initDataListR? evalConst? s₁ f _ with s₂ | s₂ | _ <;> rfl
  · rfl
  · rfl

theorem instantiateT?_toBytes [LawfulMemRep R] (s : Store H R) m xas :
    instantiateT? s.toBytes m xas = (instantiateT? s m xas).map Store.toBytes := by
  unfold instantiateT?
  rw [← prepare?_toBytes]
  rcases prepare? evalConst? s m xas with _ | ⟨c, st⟩
  · rfl
  · simp only [Option.map_some, Config.toBytes]
    rw [initSegmentsR?_toBytes]
    rcases initSegmentsR? evalConst? c.store c.frame m with ⟨s', f'⟩ | s' | _ <;> rfl

theorem instantiateOnceT?_toBytes [LawfulMemRep R] (s : Store H R) m xas :
    instantiateOnceT? s.toBytes m xas = (instantiateOnceT? s m xas).map Store.toBytes := by
  unfold instantiateOnceT?
  rw [show ModuleInst.initial s.toBytes m xas = ModuleInst.initial s m xas from rfl,
    ← evalGlobals?_toBytes]
  rcases evalGlobals? evalConst? s _ _ _ with _ | ⟨s₁, f₁, vs⟩
  · rfl
  · simp only [Option.map_some]
    rw [show s.toBytes.globals = s.globals from rfl, ← prepare?_toBytes]
    rcases prepare? evalConst? s₁ _ _ with _ | ⟨c, st⟩
    · rfl
    · simp only [Option.map_some, Config.toBytes]
      rw [initSegmentsR?_toBytes]
      rcases initSegmentsR? evalConst? c.store c.frame m.globalResidue with ⟨s', f'⟩ | s' | _ <;>
        rfl

theorem instantiateCfg?_toBytes [LawfulMemRep R] (s : Store H R) m xas :
    instantiateCfg? s.toBytes m xas = (instantiateCfg? s m xas).map fun p => (p.1.toBytes, p.2) := by
  unfold instantiateCfg?
  rw [← prepare?_toBytes]
  rcases prepare? evalConst? s m xas with _ | ⟨c, st⟩
  · rfl
  · simp only [Option.map_some, Config.toBytes]
    rw [initSegmentsR?_toBytes]
    rcases initSegmentsR? evalConst? c.store c.frame m with ⟨s', f'⟩ | s' | _ <;> rfl

theorem instantiateCfg?_eq_none_iff {s : Store H R} {m : Module}
    {xas : List ExternAddr} : instantiateCfg? s m xas = none ↔ instantiateT? s m xas = .fail := by
  unfold instantiateCfg? instantiateT?
  rcases prepare? evalConst? s m xas with _ | ⟨c, st⟩
  · simp
  · simp only []
    rcases initSegmentsR? evalConst? c.store c.frame m with ⟨s', f'⟩ | s' | _ <;> simp

end ToBytes

/-! ## On `ByteArray` stores: the trap-aware initialisation of `Exec/SegmentInitTrap` -/

section ByteArray

variable {H : Type} {ev : Store H → Frame → Expr → Option (Store H × Val)}

/-- A `SegResult` as an `InitOutcome`. -/
def ofSeg {α : Type} : SegResult H α → InitOutcome (Store H) α
  | .ok a => .ok a
  | .trap s => .trap s
  | .fail => .fail

theorem tableInitOobR?_byteArray (s : Store H) f x y a i j n :
    tableInitOobR? s f x y a i j n = tableInitOob? s f x y a i j n := by
  unfold tableInitOobR? tableInitOob?; rfl

theorem memoryInitOobR?_byteArray (s : Store H) f x y a i j n :
    memoryInitOobR? s f x y a i j n = memoryInitOob? s f x y a i j n := by
  unfold memoryInitOobR? memoryInitOob?
  rcases s.mem? f x with _ | ⟨_, mi⟩ <;> rcases s.data? f y with _ | ⟨_, di⟩ <;> rfl

theorem elemSegTrapR?_byteArray (s : Store H) f k e :
    elemSegTrapR? ev s f k e = elemSegTrap? ev s f k e := by
  unfold elemSegTrapR? elemSegTrap?
  cases hm : e.mode with
  | active y off =>
    simp only
    rcases ev s f off with _ | ⟨s₁, v⟩
    · rfl
    · simp only
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · simp only [tableInitOobR?_byteArray]
  | _ => rfl

theorem dataSegTrapR?_byteArray (s : Store H) f k d :
    dataSegTrapR? ev s f k d = dataSegTrap? ev s f k d := by
  unfold dataSegTrapR? dataSegTrap?
  cases hm : d.mode with
  | active y off =>
    simp only
    rcases ev s f off with _ | ⟨s₁, v⟩
    · rfl
    · simp only
      rcases v.addr? with _ | ⟨a, i⟩
      · rfl
      · simp only [memoryInitOobR?_byteArray]
  | _ => rfl

theorem initElemSegR?_byteArray (s : Store H) f k e :
    initElemSegR? ev s f k e = ofSeg (initElemSegT? ev s f k e) := by
  unfold initElemSegR? initElemSegT?
  rw [elemSegTrapR?_byteArray]
  rcases initElemSeg? ev s f k e with _ | s'
  · dsimp only
    rcases elemSegTrap? ev s f k e with _ | s₁ <;> rfl
  · rfl

theorem initDataSegR?_byteArray (s : Store H) f k d :
    initDataSegR? ev s f k d = ofSeg (initDataSegT? ev s f k d) := by
  unfold initDataSegR? initDataSegT?
  rw [dataSegTrapR?_byteArray]
  rcases initDataSeg? ev s f k d with _ | s'
  · dsimp only
    rcases dataSegTrap? ev s f k d with _ | s₁ <;> rfl
  · rfl

theorem initElemListR?_byteArray (s : Store H) f es :
    initElemListR? ev s f es = ofSeg (initElemListT? ev s f es) := by
  induction es generalizing s with
  | nil => rfl
  | cons p es ih =>
    obtain ⟨k, e⟩ := p
    simp only [initElemListR?, initElemListT?, initElemSegR?_byteArray]
    rcases initElemSegT? ev s f k e with s₁ | s₁ | _
    · exact ih s₁
    · rfl
    · rfl

theorem initDataListR?_byteArray (s : Store H) f ds :
    initDataListR? ev s f ds = ofSeg (initDataListT? ev s f ds) := by
  induction ds generalizing s with
  | nil => rfl
  | cons p ds ih =>
    obtain ⟨k, d⟩ := p
    simp only [initDataListR?, initDataListT?, initDataSegR?_byteArray]
    rcases initDataSegT? ev s f k d with s₁ | s₁ | _
    · exact ih s₁
    · rfl
    · rfl

theorem initSegmentsR?_byteArray (s : Store H) f m :
    initSegmentsR? ev s f m = ofSeg (initSegmentsT? ev s f m) := by
  unfold initSegmentsR? initSegmentsT?
  rw [initElemListR?_byteArray]
  rcases initElemListT? ev s f _ with s₁ | s₁ | _
  · simp only [ofSeg]
    rw [initDataListR?_byteArray]
    rcases initDataListT? ev s₁ f _ with s₂ | s₂ | _ <;> rfl
  · rfl
  · rfl

theorem initSegmentsR?_trap {s s' : Store H} {f : Frame} {m : Module}
    (h : initSegmentsR? ev s f m = .trap s') : initSegmentsT? ev s f m = .trap s' := by
  rw [initSegmentsR?_byteArray] at h
  revert h
  rcases initSegmentsT? ev s f m with _ | t | _ <;> simp [ofSeg]

variable {P : Profile} {host : HostSemantics H}

/-- **A trap of `instantiateT?` is a run of the specification's instantiation to `trap`** in
the residual store: `prepare?` gives the configuration of `$instantiate` (`Instantiate`), and its
segment code runs to `⟨s', frame, [trap]⟩`; the start call is never reached. -/
theorem instantiateT?_trap_sound {s s' : Store H} {m : Module} {xas : List ExternAddr}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateT? s m xas = .trap s') :
    ∃ c st, prepare? evalConst? s m xas = some (c, st) ∧
      initSegmentsT? evalConst? c.store c.frame m = .trap s' ∧
      Instantiate P host s m xas (c.withStart st) ∧
      Steps P host (c.withStart st) ⟨s', c.frame, [.trap]⟩ := by
  unfold instantiateT? at h
  split at h
  · cases h
  · rename_i c st hp
    split at h
    · cases h
    · rename_i t hi
      cases h
      have hT := initSegmentsR?_trap hi
      refine ⟨c, st, hp, hT, (prepare?_sound evalConst?_evalSound hp hvalid).2, ?_⟩
      have hs := initSegmentsT?_trap_steps (P := P) (host := host) evalConst?_evalSound hT
      rw [← prepare?_code hp] at hs
      exact Steps.withStart_trap hs
    · cases h

/-- **Success of `instantiateT?` is a run of the specification's instantiation** to the start
code. -/
theorem instantiateT?_ok_sound {s s' : Store H} {m : Module} {xas : List ExternAddr} {f : Frame}
    {st : Option FuncIdx}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateT? s m xas = .ok s' f st) :
    ∃ c, prepare? evalConst? s m xas = some (c, st) ∧ st = m.start ∧
      Instantiate P host s m xas (c.withStart st) ∧
      Steps P host (c.withStart st) ⟨s', f, startCode st⟩ :=
  instantiateDirect?_sound (instantiateT?_ok_iff.1 h) hvalid

theorem instantiateT?_eq_fail_iff {s : Store H} {m : Module} {xas : List ExternAddr} :
    instantiateT? s m xas = .fail ↔ prepare? evalConst? s m xas = none ∨
      ∃ c st, prepare? evalConst? s m xas = some (c, st) ∧
        initSegmentsT? evalConst? c.store c.frame m = .fail := by
  unfold instantiateT?
  rcases prepare? evalConst? s m xas with _ | ⟨c, st⟩
  · simp
  · simp only [initSegmentsR?_byteArray, reduceCtorEq, false_or, Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro h
      refine ⟨c, st, ⟨rfl, rfl⟩, ?_⟩
      revert h
      rcases initSegmentsT? evalConst? c.store c.frame m with ⟨_, _⟩ | _ | _ <;> simp [ofSeg]
    · rintro ⟨c', st', ⟨rfl, rfl⟩, h⟩
      rw [h]; rfl

/-- **A trap of single allocation is a run of the residue's segment code to `trap`**:
`$evalglobals` succeeds, `prepare?` of the global-free residue gives a configuration `c`, the
trap-aware initialisation of `Exec/SegmentInitTrap` traps in the store `s'`, and `c` with the
start call runs to `⟨s', c.frame, [trap]⟩`. -/
theorem instantiateOnceT?_trap_steps {s s' : Store H} {m : Module} {xas : List ExternAddr}
    (h : instantiateOnceT? s m xas = .trap s') :
    ∃ s₁ f₁ vs c st, evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩
        (Module.closedGlobalTypes m) (m.globals.map Global.init) = some (s₁, f₁, vs) ∧
      prepare? evalConst? s₁ m.globalResidue
        (xas ++ globalAddrs s.globals.length m.globals.length) = some (c, st) ∧
      initSegmentsT? evalConst? c.store c.frame m.globalResidue = .trap s' ∧
      Steps P host (c.withStart st) ⟨s', c.frame, [.trap]⟩ := by
  unfold instantiateOnceT? at h
  split at h
  · cases h
  · rename_i s₁ f₁ vs hg
    split at h
    · cases h
    · rename_i c st hp
      split at h
      · cases h
      · rename_i t hi
        cases h
        have hT := initSegmentsR?_trap hi
        refine ⟨s₁, f₁, vs, c, st, hg, hp, hT, ?_⟩
        have hs := initSegmentsT?_trap_steps (P := P) (host := host) evalConst?_evalSound hT
        rw [← prepare?_code hp] at hs
        exact Steps.withStart_trap hs
      · cases h

/-- **`instantiateCfg?` is the specification's instantiation run through its segment code**:
its configuration is reached from the `Instantiate` configuration, whose frame is that of the
module instance it returns. -/
theorem instantiateCfg?_sound {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H}
    {mi : ModuleInst}
    (hvalid : ∃ xtE xtI, ModuleOk m ⟨xtI, xtE⟩ ∧ List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : instantiateCfg? s m xas = some (c, mi)) :
    ∃ c₀, Instantiate P host s m xas c₀ ∧ c₀.frame.module = mi ∧ Steps P host c₀ c := by
  unfold instantiateCfg? at h
  split at h
  · cases h
  · rename_i c₁ st hp
    have hI := (prepare?_sound (P := P) (host := host) evalConst?_evalSound hp hvalid).2
    have hfr : (c₁.withStart st).frame = c₁.frame := by cases st <;> rfl
    split at h
    · rename_i s' f' hi
      cases h
      have hi' := initSegmentsR?_ok_iff.1 hi
      have hd : prepareDirect? evalConst? s m xas = some (s', f', st) := by
        unfold prepareDirect?; simp only [hp, hi']
      obtain ⟨c₂, hp₂, -, -, hS⟩ := prepareDirect?_sound (P := P) (host := host)
        evalConst?_evalSound hd hvalid
      rw [hp] at hp₂
      cases hp₂
      obtain rfl := initSegments?_frame hi'
      exact ⟨_, hI, by rw [hfr], hS⟩
    · rename_i t hi
      cases h
      have hT := initSegmentsR?_trap hi
      have hs := initSegmentsT?_trap_steps (P := P) (host := host) evalConst?_evalSound hT
      rw [← prepare?_code hp] at hs
      exact ⟨_, hI, by rw [hfr], Steps.withStart_trap hs⟩
    · cases h

end ByteArray

end Silmaril.Proofs.Wasm.Execution.InstantiateTrap

end
