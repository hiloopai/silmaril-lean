module

public import Silmaril.Wasm.Execution.Core.Exec.Instantiate
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section

/-! # Computable segment initialisation for Core 3.0

`initElem?`/`initData?`/`initSegments?` apply the effect of the segment programs
`$runelem_`/`$rundata_` (constant offset, `table.init`/`memory.init`,
`elem.drop`/`data.drop`) directly to the store. Offsets are computed by an
evaluator `ev` with `EvalSound`. Out-of-bounds initialisation (which traps) is
reported as `none`; the trap outcome is not modelled.

`initSegments?_steps` proves that a successful run is reproduced by `Steps` on
the segment code of `$instantiate`.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-- Recognise an address-typed integer constant. -/
def Val.addr? : Val → Option (Σ a : AddrType, BitVec a.intType.width)
  | .num ⟨.int .i32, b⟩ => some ⟨.i32, b⟩
  | .num ⟨.int .i64, b⟩ => some ⟨.i64, b⟩
  | _ => none

theorem Val.toAdmin_of_addr? {v : Val} {a : AddrType} {i : BitVec a.intType.width}
    (h : v.addr? = some ⟨a, i⟩) : v.toAdmin = aconst a i := by
  unfold Val.addr? at h
  split at h
  · simp only [Option.some.injEq] at h
    cases h; rfl
  · simp only [Option.some.injEq] at h
    cases h; rfl
  · cases h

theorem bv32_sub_one_lt {n : BitVec 32} (hn : n ≠ 0) : (n - 1).toNat < n.toNat := by
  have : n.toNat ≠ 0 := fun h => hn (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def]; simp; omega)]
  simp; omega

/-- The direct effect of `table.init x y` from `i`, `j`, `n`. -/
def tableInitLoop (s : Store H) (f : Frame) (x : TableIdx) (y : ElemIdx) (a : AddrType)
    (i : BitVec a.intType.width) (j n : BitVec 32) : Option (Store H) :=
  match s.table? f x, s.elem? f y with
  | some (ta, ti), some (_, ei) =>
    if i.toNat + n.toNat ≤ ti.refs.length ∧ j.toNat + n.toNat ≤ ei.refs.length then
      if _hn : n = 0 then some s
      else
        match ei.refs[j.toNat]? with
        | some r =>
          tableInitLoop (s.setTable ta { ti with refs := ti.refs.set i.toNat r }) f x y a
            (i + 1) (j + 1) (n - 1)
        | none => none
    else none
  | _, _ => none
termination_by n.toNat
decreasing_by exact bv32_sub_one_lt _hn

/-- The direct effect of `memory.init x y` from `i`, `j`, `n`. -/
def memoryInitLoop (s : Store H) (f : Frame) (x : MemIdx) (y : DataIdx) (a : AddrType)
    (i : BitVec a.intType.width) (j n : BitVec 32) : Option (Store H) :=
  match s.mem? f x, s.data? f y with
  | some (ma, mi), some (_, di) =>
    if i.toNat + n.toNat ≤ mi.bytes.size ∧ j.toNat + n.toNat ≤ di.bytes.size then
      if _hn : n = 0 then some s
      else
        match di.bytes.data[j.toNat]? with
        | some byte =>
          match Memory.store mi.bytes (effAddr i.toNat memarg0) (count := PackSize.i8.width / 8)
              ((BitVec.ofNat 32 byte.toNat).setWidth _) with
          | some b =>
            memoryInitLoop (s.setMem ma { mi with bytes := b }) f x y a (i + 1) (j + 1) (n - 1)
          | none => none
        | none => none
    else none
  | _, _ => none
termination_by n.toNat
decreasing_by exact bv32_sub_one_lt _hn

section
variable (ev : Store H → Frame → Expr → Option (Store H × Val))

/-- `elem.drop y` applied directly. -/
def elemDrop? (s : Store H) (f : Frame) (y : ElemIdx) : Option (Store H) :=
  (s.elem? f y).map fun (ea, _) => s.setElem ea []

/-- `data.drop y` applied directly. -/
def dataDrop? (s : Store H) (f : Frame) (y : DataIdx) : Option (Store H) :=
  (s.data? f y).map fun (da, _) => s.setData da ByteArray.empty

/-- The effect of `$runelem_(k, e)`. -/
def initElemSeg? (s : Store H) (f : Frame) (k : Nat) (e : Elem) : Option (Store H) :=
  match e.mode with
  | .passive => some s
  | .declarative => elemDrop? s f ⟨Fin.ofNat _ k⟩
  | .active y off =>
    match ev s f off with
    | none => none
    | some (s₁, v) =>
      match v.addr? with
      | none => none
      | some ⟨a, i⟩ =>
        match tableInitLoop s₁ f y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 e.init.length) with
        | none => none
        | some s₂ => elemDrop? s₂ f ⟨Fin.ofNat _ k⟩

/-- The effect of `$rundata_(k, d)`. -/
def initDataSeg? (s : Store H) (f : Frame) (k : Nat) (d : Data) : Option (Store H) :=
  match d.mode with
  | .passive => some s
  | .active y off =>
    match ev s f off with
    | none => none
    | some (s₁, v) =>
      match v.addr? with
      | none => none
      | some ⟨a, i⟩ =>
        match memoryInitLoop s₁ f y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 d.bytes.size) with
        | none => none
        | some s₂ => dataDrop? s₂ f ⟨Fin.ofNat _ k⟩

/-- Run a list of indexed segments. -/
def initElemList? : Store H → Frame → List (Nat × Elem) → Option (Store H)
  | s, _, [] => some s
  | s, f, (k, e) :: es =>
    match initElemSeg? ev s f k e with
    | none => none
    | some s₁ => initElemList? s₁ f es

def initDataList? : Store H → Frame → List (Nat × Data) → Option (Store H)
  | s, _, [] => some s
  | s, f, (k, d) :: ds =>
    match initDataSeg? ev s f k d with
    | none => none
    | some s₁ => initDataList? s₁ f ds

/-- All element segments of `m`. -/
def initElem? (s : Store H) (f : Frame) (m : Module) : Option (Store H × Frame) :=
  (initElemList? ev s f ((List.range m.elems.length).zip m.elems)).map (·, f)

/-- All data segments of `m`. -/
def initData? (s : Store H) (f : Frame) (m : Module) : Option (Store H × Frame) :=
  (initDataList? ev s f ((List.range m.data.length).zip m.data)).map (·, f)

/-- Element segments, then data segments. -/
def initSegments? (s : Store H) (f : Frame) (m : Module) : Option (Store H × Frame) :=
  match initElem? ev s f m with
  | none => none
  | some (s₁, f₁) => initData? ev s₁ f₁ m

end

/-! ## Soundness -/

variable {P : Profile} {host : HostSemantics H}
  {ev : Store H → Frame → Expr → Option (Store H × Val)}

theorem Steps.append_nil {s s' s'' : Store H} {f f' f'' : Frame} {is js : List Admin}
    (h₁ : Steps P host ⟨s, f, is⟩ ⟨s', f', []⟩) (h₂ : Steps P host ⟨s', f', js⟩ ⟨s'', f'', []⟩) :
    Steps P host ⟨s, f, is ++ js⟩ ⟨s'', f'', []⟩ := by
  have := Steps.ctxtInstrs (vs := []) (rest := js) h₁
  simp only [vals, List.map_nil, List.nil_append] at this
  exact this.trans h₂

theorem tableInitLoop_steps {x : TableIdx} {y : ElemIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f : Frame} {i : BitVec a.intType.width} {j : BitVec 32},
      tableInitLoop s f x y a i j n = some s' →
      Steps P host ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩
        ⟨s', f, []⟩ := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s s' f i j hl
  rw [tableInitLoop] at hl
  split at hl
  · rename_i ta ti ea ei ht he
    split at hl
    · rename_i hb
      split at hl
      · rename_i hn
        subst hn; cases hl
        exact (Step.table (.initZero ht he (by simpa using hb))).steps
      · rename_i hn
        split at hl
        · rename_i r hr
          have hs1 : Step P host ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.tableInit x y)]⟩
              ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x),
                aconst a (i + 1), constI32 (j + 1), constI32 (n - 1), .plain (.tableInit x y)]⟩ :=
            Step.table (.initSucc ht he hb hn hr)
          have hnz : n.toNat ≠ 0 := fun h0 => hn (BitVec.eq_of_toNat_eq (by simpa using h0))
          have hs2 : Step P host ⟨s, f, [aconst a i, .ref r, .plain (.tableSet x)]⟩
              ⟨s.setTable ta { ti with refs := ti.refs.set i.toNat r }, f, []⟩ :=
            Step.table (.setVal ht (by omega))
          have hrest := ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl hl
          refine (hs1.steps).trans ?_
          exact Steps.append_nil (is := [aconst a i, .ref r, .plain (.tableSet x)])
            hs2.steps hrest
        · cases hl
    · cases hl
  · cases hl

theorem memoryInitLoop_steps {x : MemIdx} {y : DataIdx} {a : AddrType} :
    ∀ (n : BitVec 32) {s s' : Store H} {f : Frame} {i : BitVec a.intType.width} {j : BitVec 32},
      memoryInitLoop s f x y a i j n = some s' →
      Steps P host ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩
        ⟨s', f, []⟩ := by
  intro n
  induction h : n.toNat using Nat.strong_induction_on generalizing n with
  | _ k ih =>
  intro s s' f i j hl
  rw [memoryInitLoop] at hl
  split at hl
  · rename_i ma mi da di hm hd
    split at hl
    · rename_i hb
      split at hl
      · rename_i hn
        subst hn; cases hl
        exact (Step.memory (.initZero hm hd (by simpa using hb))).steps
      · rename_i hn
        split at hl
        · rename_i byte hbyte
          split at hl
          · rename_i b hst
            have hs1 : Step P host
                ⟨s, f, [aconst a i, constI32 j, constI32 n, .plain (.memoryInit x y)]⟩
                ⟨s, f, [aconst a i, constI32 (BitVec.ofNat 32 byte.toNat), store8 x,
                  aconst a (i + 1), constI32 (j + 1), constI32 (n - 1),
                  .plain (.memoryInit x y)]⟩ :=
              Step.memory (.initSucc hm hd hb hn hbyte)
            have hs2 : Step P host
                ⟨s, f, [aconst a i, constI32 (BitVec.ofNat 32 byte.toNat), store8 x]⟩
                ⟨s.setMem ma { mi with bytes := b }, f, []⟩ :=
              Step.memory (.storePackVal (t := .i32) (sz := .i8) (arg := memarg0) hm hst)
            have hrest := ih _ (h ▸ bv32_sub_one_lt hn) (n - 1) rfl hl
            refine (hs1.steps).trans ?_
            exact Steps.append_nil
              (is := [aconst a i, constI32 (BitVec.ofNat 32 byte.toNat), store8 x])
              hs2.steps hrest
          · cases hl
        · cases hl
    · cases hl
  · cases hl

theorem elemDrop?_steps {s s' : Store H} {f : Frame} {y : ElemIdx}
    (h : elemDrop? s f y = some s') :
    Steps P host ⟨s, f, [.plain (.elemDrop y)]⟩ ⟨s', f, []⟩ := by
  unfold elemDrop? at h
  cases he : s.elem? f y with
  | none => simp [he] at h
  | some p =>
    rcases p with ⟨ea, ei⟩
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst h
    exact (Step.table (.elemDrop he)).steps

theorem dataDrop?_steps {s s' : Store H} {f : Frame} {y : DataIdx}
    (h : dataDrop? s f y = some s') :
    Steps P host ⟨s, f, [.plain (.dataDrop y)]⟩ ⟨s', f, []⟩ := by
  unfold dataDrop? at h
  cases hd : s.data? f y with
  | none => simp [hd] at h
  | some p =>
    rcases p with ⟨da, di⟩
    simp only [hd, Option.map_some, Option.some.injEq] at h
    subst h
    exact (Step.memory (.dataDrop hd)).steps

/-- Evaluate an offset then run the remaining (constant-prefixed) code. -/
theorem offset_steps (hev : EvalSound P host ev) {s s₁ s' : Store H} {f : Frame} {off : Expr}
    {v : Val} {rest : List Admin} (he : ev s f off = some (s₁, v))
    (hr : Steps P host ⟨s₁, f, v.toAdmin :: rest⟩ ⟨s', f, []⟩) :
    Steps P host ⟨s, f, expression off ++ rest⟩ ⟨s', f, []⟩ := by
  have h1 := Steps.ctxtInstrs (vs := []) (rest := rest) (hev _ _ _ _ _ he)
  simp only [vals, List.map_nil, List.nil_append, List.map_cons, List.singleton_append] at h1
  exact h1.trans hr

theorem initElemSeg?_steps (hev : EvalSound P host ev) {s s' : Store H} {f : Frame} {k : Nat}
    {e : Elem} (h : initElemSeg? ev s f k e = some s') :
    Steps P host ⟨s, f, expression (runElem k e)⟩ ⟨s', f, []⟩ := by
  unfold initElemSeg? at h
  unfold runElem
  split at h
  · rename_i hm; rw [hm]; cases h; exact Relation.ReflTransGen.refl
  · rename_i hm; rw [hm]; exact elemDrop?_steps h
  · rename_i y off hm
    rw [hm]
    split at h
    · cases h
    · rename_i s₁ v he
      split at h
      · cases h
      · rename_i a i hv
        split at h
        · cases h
        · rename_i s₂ hl
          simp only [expression, List.map_append, List.map_cons, List.map_nil]
          refine offset_steps hev he ?_
          rw [Val.toAdmin_of_addr? hv]
          have := tableInitLoop_steps (P := P) (host := host) _ hl
          exact Steps.append_nil (is := [aconst a i, constI32 0, constI32 _, .plain (.tableInit y _)])
            this (elemDrop?_steps h)

theorem initDataSeg?_steps (hev : EvalSound P host ev) {s s' : Store H} {f : Frame} {k : Nat}
    {d : Data} (h : initDataSeg? ev s f k d = some s') :
    Steps P host ⟨s, f, expression (runData k d)⟩ ⟨s', f, []⟩ := by
  unfold initDataSeg? at h
  unfold runData
  split at h
  · rename_i hm; rw [hm]; cases h; exact Relation.ReflTransGen.refl
  · rename_i y off hm
    rw [hm]
    split at h
    · cases h
    · rename_i s₁ v he
      split at h
      · cases h
      · rename_i a i hv
        split at h
        · cases h
        · rename_i s₂ hl
          simp only [expression, List.map_append, List.map_cons, List.map_nil]
          refine offset_steps hev he ?_
          rw [Val.toAdmin_of_addr? hv]
          have := memoryInitLoop_steps (P := P) (host := host) _ hl
          exact Steps.append_nil (is := [aconst a i, constI32 0, constI32 _, .plain (.memoryInit y _)])
            this (dataDrop?_steps h)

theorem initElemList?_steps (hev : EvalSound P host ev) :
    ∀ {s s' : Store H} {f : Frame} {es : List (Nat × Elem)},
      initElemList? ev s f es = some s' →
      Steps P host ⟨s, f, expression (es.flatMap fun (i, e) => runElem i e)⟩ ⟨s', f, []⟩
  | s, s', f, [], h => by cases h; exact Relation.ReflTransGen.refl
  | s, s', f, (k, e) :: es, h => by
    simp only [initElemList?] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      simp only [List.flatMap_cons, expression, List.map_append]
      exact Steps.append_nil (initElemSeg?_steps hev h₁) (initElemList?_steps hev h)

theorem initDataList?_steps (hev : EvalSound P host ev) :
    ∀ {s s' : Store H} {f : Frame} {ds : List (Nat × Data)},
      initDataList? ev s f ds = some s' →
      Steps P host ⟨s, f, expression (ds.flatMap fun (i, d) => runData i d)⟩ ⟨s', f, []⟩
  | s, s', f, [], h => by cases h; exact Relation.ReflTransGen.refl
  | s, s', f, (k, d) :: ds, h => by
    simp only [initDataList?] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      simp only [List.flatMap_cons, expression, List.map_append]
      exact Steps.append_nil (initDataSeg?_steps hev h₁) (initDataList?_steps hev h)

theorem initElem?_steps (hev : EvalSound P host ev) {s s' : Store H} {f f' : Frame}
    {m : Module} (h : initElem? ev s f m = some (s', f')) :
    Steps P host
      ⟨s, f, expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e)⟩
      ⟨s', f', []⟩ := by
  unfold initElem? at h
  cases hl : initElemList? ev s f ((List.range m.elems.length).zip m.elems) with
  | none => simp [hl] at h
  | some s₁ =>
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact initElemList?_steps hev hl

theorem initData?_steps (hev : EvalSound P host ev) {s s' : Store H} {f f' : Frame}
    {m : Module} (h : initData? ev s f m = some (s', f')) :
    Steps P host
      ⟨s, f, expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d)⟩
      ⟨s', f', []⟩ := by
  unfold initData? at h
  cases hl : initDataList? ev s f ((List.range m.data.length).zip m.data) with
  | none => simp [hl] at h
  | some s₁ =>
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact initDataList?_steps hev hl

/-- Main theorem: a successful direct segment initialisation is reproduced by
running the element and data segment code of `$instantiate`. -/
theorem initSegments?_steps (hev : EvalSound P host ev) {s s' : Store H} {f f' : Frame}
    {m : Module} (h : initSegments? ev s f m = some (s', f')) :
    Steps P host
      ⟨s, f, expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
        expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d)⟩
      ⟨s', f', []⟩ := by
  unfold initSegments? at h
  split at h
  · cases h
  · rename_i s₁ f₁ h₁
    exact Steps.append_nil (initElem?_steps hev h₁) (initData?_steps hev h)

/-- The frame is unchanged by segment initialisation. -/
theorem initSegments?_frame {s s' : Store H} {f f' : Frame} {m : Module}
    (h : initSegments? ev s f m = some (s', f')) : f' = f := by
  unfold initSegments? initData? initElem? at h
  split at h
  · cases h
  · rename_i s₁ f₁ h₁
    cases h₂ : initDataList? ev s₁ f₁ ((List.range m.data.length).zip m.data) <;>
      simp_all

end Silmaril.Wasm.Execution.Core
