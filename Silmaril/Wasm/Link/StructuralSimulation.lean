module

public import Silmaril.Wasm.Link.ControlInversion
public import Silmaril.Wasm.Link.AdminScope
public import Silmaril.Wasm.Link.ControlSimulation
public import Silmaril.Wasm.Link.SimulationDefs

/-! # Structural control transport

Structural rules retain the related stores and current frames. Runtime values
are shared, while source annotations follow the actual instruction rewrite.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.StructuralSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open AdminRelation Simulation

variable {H : Type} {P : Profile} {host : HostSemantics H}

inductive IsStructural : {source final : Config H} → Step P host source final → Prop where
  | block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : vs.length = t₁.length)  :
      IsStructural (Step.block (s := s) (f := f) (bt := bt) (body := body) (vs := vs) (t₁ := t₁) (t₂ := t₂) (hbt := hbt) (hm := hm))
  | loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : vs.length = t₁.length)  :
      IsStructural (Step.loop (s := s) (f := f) (bt := bt) (body := body) (vs := vs) (t₁ := t₁) (t₂ := t₂) (hbt := hbt) (hm := hm))
  | ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr}
      (hc : c ≠ 0)  :
      IsStructural (Step.ifTrue (s := s) (f := f) (c := c) (bt := bt) (b₁ := b₁) (b₂ := b₂) (hc := hc))
  | ifFalse {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr}  :
      IsStructural (Step.ifFalse (s := s) (f := f) (bt := bt) (b₁ := b₁) (b₂ := b₂))
  | labelVals {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}  :
      IsStructural (Step.labelVals (s := s) (f := f) (n := n) (cont := cont) (vs := vs))
  | brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs' vs : List Val}
      {l : LabelIdx} {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = n)  :
      IsStructural (Step.brLabelZero (s := s) (f := f) (n := n) (cont := cont) (vs' := vs') (vs := vs) (l := l) (rest := rest) (hl := hl) (hn := hn))
  | brLabelSucc {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
      {l : LabelIdx} {rest : List Admin} (hl : 0 < l.toNat)  :
      IsStructural (Step.brLabelSucc (s := s) (f := f) (n := n) (cont := cont) (vs := vs) (l := l) (rest := rest) (hl := hl))
  | brHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
      {l : LabelIdx} {rest : List Admin}  :
      IsStructural (Step.brHandler (s := s) (f := f) (n := n) (cs := cs) (vs := vs) (l := l) (rest := rest))
  | brIfTrue {s : Store H} {f : Frame} {c : BitVec 32} {l : LabelIdx} (hc : c ≠ 0)  :
      IsStructural (Step.brIfTrue (s := s) (f := f) (c := c) (l := l) (hc := hc))
  | brIfFalse {s : Store H} {f : Frame} {l : LabelIdx}  :
      IsStructural (Step.brIfFalse (s := s) (f := f) (l := l))
  | brTableLt {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx}
      (hi : ls[i.toNat]? = some l)  :
      IsStructural (Step.brTableLt (s := s) (f := f) (i := i) (ls := ls) (l' := l') (l := l) (hi := hi))
  | brTableGe {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
      (hi : ls.length ≤ i.toNat)  :
      IsStructural (Step.brTableGe (s := s) (f := f) (i := i) (ls := ls) (l' := l') (hi := hi))
  | brOnNullNull {s : Store H} {f : Frame} {l : LabelIdx}  :
      IsStructural (Step.brOnNullNull (s := s) (f := f) (l := l))
  | brOnNullAddr {s : Store H} {f : Frame} {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null)  :
      IsStructural (Step.brOnNullAddr (s := s) (f := f) (v := v) (l := l) (hv := hv))
  | brOnNonNullNull {s : Store H} {f : Frame} {l : LabelIdx}  :
      IsStructural (Step.brOnNonNullNull (s := s) (f := f) (l := l))
  | brOnNonNullAddr {s : Store H} {f : Frame} {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null)  :
      IsStructural (Step.brOnNonNullAddr (s := s) (f := f) (v := v) (l := l) (hv := hv))
  | brOnCastSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : RefOk s r (f.module.instRef rt₂))  :
      IsStructural (Step.brOnCastSucceed (s := s) (f := f) (r := r) (l := l) (rt₁ := rt₁) (rt₂ := rt₂) (h := h))
  | brOnCastFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt₂))  :
      IsStructural (Step.brOnCastFail (s := s) (f := f) (r := r) (l := l) (rt₁ := rt₁) (rt₂ := rt₂) (h := h))
  | brOnCastFailSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : RefOk s r (f.module.instRef rt₂))  :
      IsStructural (Step.brOnCastFailSucceed (s := s) (f := f) (r := r) (l := l) (rt₁ := rt₁) (rt₂ := rt₂) (h := h))
  | brOnCastFailFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt₂))  :
      IsStructural (Step.brOnCastFailFail (s := s) (f := f) (r := r) (l := l) (rt₁ := rt₁) (rt₂ := rt₂) (h := h))
  | call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)  :
      IsStructural (Step.call (s := s) (f := f) (x := x) (a := a) (fi := fi) (hx := hx) (hf := hf))
  | callRefNull {s : Store H} {f : Frame} {c : Admin} (hc : c.IsCallRef)  :
      IsStructural (Step.callRefNull (s := s) (f := f) (c := c) (hc := hc))
  | callRefFunc {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
      {ps rs : Ty (.list .val)} {code : Func}
      (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : vs.length = ps.length) (hcode : fi.code = .wasm code)  :
      IsStructural (Step.callRefFunc (s := s) (f := f) (c := c) (vs := vs) (a := a) (fi := fi) (ps := ps) (rs := rs) (code := code) (hc := hc) (hf := hf) (he := he) (hn := hn) (hcode := hcode))
  | returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)  :
      IsStructural (Step.returnCall (s := s) (f := f) (x := x) (a := a) (fi := fi) (hx := hx) (hf := hf))
  | returnCallRefLabel {s : Store H} {f : Frame} {k : Nat} {cont : List Instr} {vs : List Val}
      {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef)  :
      IsStructural (Step.returnCallRefLabel (s := s) (f := f) (k := k) (cont := cont) (vs := vs) (c := c) (rest := rest) (hc := hc))
  | returnCallRefHandler {s : Store H} {f : Frame} {k : Nat} {cs : List Catch} {vs : List Val}
      {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef)  :
      IsStructural (Step.returnCallRefHandler (s := s) (f := f) (k := k) (cs := cs) (vs := vs) (c := c) (rest := rest) (hc := hc))
  | returnCallRefFrameNull {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val} {c : Admin}
      {rest : List Admin} (hc : c.IsReturnCallRef)  :
      IsStructural (Step.returnCallRefFrameNull (s := s) (f := f) (fi := fi) (k := k) (vs := vs) (c := c) (rest := rest) (hc := hc))
  | returnCallRefFrameAddr {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
      {c : Admin} {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
      (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
      (hn : vs.length = ps.length)  :
      IsStructural (Step.returnCallRefFrameAddr (s := s) (f := f) (fi := fi) (k := k) (vs' := vs') (vs := vs) (a := a) (c := c) (rest := rest) (fn := fn) (ps := ps) (rs := rs) (hc := hc) (hf := hf) (he := he) (hn := hn))
  | callIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}  :
      IsStructural (Step.callIndirect (s := s) (f := f) (x := x) (y := y))
  | returnCallIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx}  :
      IsStructural (Step.returnCallIndirect (s := s) (f := f) (x := x) (y := y))
  | frameVals {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val} (hn : vs.length = n)  :
      IsStructural (Step.frameVals (s := s) (f := f) (fi := fi) (n := n) (vs := vs) (hn := hn))
  | returnFrame {s : Store H} {f fi : Frame} {n : Nat} {vs' vs : List Val} {rest : List Admin}
      (hn : vs.length = n)  :
      IsStructural (Step.returnFrame (s := s) (f := f) (fi := fi) (n := n) (vs' := vs') (vs := vs) (rest := rest) (hn := hn))
  | returnLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
      {rest : List Admin}  :
      IsStructural (Step.returnLabel (s := s) (f := f) (n := n) (cont := cont) (vs := vs) (rest := rest))
  | returnHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
      {rest : List Admin}  :
      IsStructural (Step.returnHandler (s := s) (f := f) (n := n) (cs := cs) (vs := vs) (rest := rest))
  | trapInstrs {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
      (hne : vs ≠ [] ∨ rest ≠ [])  :
      IsStructural (Step.trapInstrs (s := s) (f := f) (vs := vs) (rest := rest) (hne := hne))
  | trapLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}  :
      IsStructural (Step.trapLabel (s := s) (f := f) (n := n) (cont := cont))
  | trapHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}  :
      IsStructural (Step.trapHandler (s := s) (f := f) (n := n) (cs := cs))
  | trapFrame {s : Store H} {f fi : Frame} {n : Nat}  :
      IsStructural (Step.trapFrame (s := s) (f := f) (fi := fi) (n := n))

private theorem unchanged {mode : Mode} {i : Instr}
    (stable : ∀ r, instruction? r i = some i) : Instruction mode i i := by
  cases mode with
  | same => rfl
  | relocated r => exact stable r

private theorem stable_target {mode : Mode} {i j : Instr}
    (h : Instruction mode i j) (stable : ∀ r, instruction? r i = some i) : j = i := by
  cases mode with
  | same => exact h.symm
  | relocated r => exact (Option.some.inj ((stable r).symm.trans h)).symm

private theorem stable_nonthrow {i : Instr} (stable : ∀ r, instruction? r i = some i) :
    i ≠ .throwRef := by
  intro hi
  have h := stable ⟨0,0,0,[]⟩
  rw [hi] at h
  simp only [instruction?,reduceCtorEq] at h

private theorem values_stable {mode : Mode} {left right : ModuleInst}
    {vs : List Val} {i : Instr} {ys : List Admin}
    (h : Control mode left right (vals vs ++ [.plain i]) ys)
    (nonvalue : (Admin.plain i).val? = none)
    (stable : ∀ r, instruction? r i = some i) : ys = vals vs ++ [.plain i] := by
  obtain ⟨j,rfl,hj⟩ := h.values_instruction nonvalue (stable_nonthrow stable)
  rw [stable_target hj stable]

private theorem plain_stable {mode : Mode} {left right : ModuleInst}
    {i : Instr} {xs ys : List Admin}
    (h : Control mode left right (.plain i :: xs) ys)
    (nonvalue : (Admin.plain i).val? = none)
    (stable : ∀ r, instruction? r i = some i) :
    ∃ rest, ys = .plain i :: rest ∧ Control mode left right xs rest := by
  obtain ⟨j,rest,rfl,hj,hr⟩ := h.plain_cons nonvalue (stable_nonthrow stable)
  rw [stable_target hj stable]
  exact ⟨rest,rfl,hr⟩

private theorem view_same {left right : ModuleInst} (view : View .same left right) :
    left = right := by cases view; rfl

private theorem same_module {left right : Frame} (frames : Frames .same left right) :
    left.module = right.module := view_same frames.view

private theorem empty_instructions (mode : Mode) : Instructions mode [] [] := by
  cases mode <;> rfl

private theorem attached {r : Relocation} {body body' : List Instr}
    (h : body.attach.mapM (fun nested => instruction? r nested.val) = some body') :
    instructions? r body = some body' := by
  rw [List.mapM_subtype (g := instruction? r) (fun _ _ => rfl),List.unattach_attach] at h
  exact h

private theorem plain_singleton {mode : Mode} {left right : ModuleInst}
    {i : Instr} {ys : List Admin} (h : Control mode left right [.plain i] ys)
    (nonvalue : (Admin.plain i).val? = none)
    (nonthrow : i ≠ .throwRef := by intro h; cases h) :
    ∃ j, ys = [.plain j] ∧ Instruction mode i j := by
  obtain ⟨j,rest,rfl,hi,hr⟩ := h.plain_cons nonvalue nonthrow
  rw [hr.nil_left]
  exact ⟨j,rfl,hi⟩

private theorem handler_singleton {mode : Mode} {left right : ModuleInst}
    {n : Nat} {cs : List Catch} {body ys : List Admin}
    (h : Control mode left right [.handler n cs body] ys) :
    mode = .same ∧ left = right ∧ ∃ body', ys = [.handler n cs body'] ∧
      Control .same left left body body' := by
  obtain ⟨hm,he,body',rest,hcode,hbody,hr⟩ := h.handler_cons
  rw [hr.nil_left] at hcode
  exact ⟨hm,he,body',hcode,hbody⟩

private theorem nonempty_right {mode : Mode} {left right : ModuleInst} {xs ys : List Admin}
    (h : Control mode left right xs ys) (hx : xs ≠ []) : ys ≠ [] := by
  intro hy
  have hl := h.length_eq
  rw [hy,List.length_nil,List.length_eq_zero_iff] at hl
  exact hx hl

private theorem callRefType_cons {mode : Mode} {left right : ModuleInst}
    {d : DefType} {xs ys : List Admin} (h : Control mode left right (.callRefType d :: xs) ys) :
    ∃ rest, ys = .callRefType d :: rest ∧ Control mode left right xs rest := by
  generalize ha : Admin.callRefType d = a at h
  cases h
  case callRefType rest => cases ha; exact ⟨_,rfl,rest⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha] at hv
    simp only [Admin.val?,reduceCtorEq] at hv
  all_goals cases ha

private theorem returnCallRefType_cons {mode : Mode} {left right : ModuleInst}
    {d : DefType} {xs ys : List Admin} (h : Control mode left right (.returnCallRefType d :: xs) ys) :
    ∃ rest, ys = .returnCallRefType d :: rest ∧ Control mode left right xs rest := by
  generalize ha : Admin.returnCallRefType d = a at h
  cases h
  case returnCallRefType rest => cases ha; exact ⟨_,rfl,rest⟩
  case val v tail =>
    have hv := Admin.val?_toAdmin v
    rw [← ha] at hv
    simp only [Admin.val?,reduceCtorEq] at hv
  all_goals cases ha

private theorem callRef_cons {mode : Mode} {left right : ModuleInst} {c : Admin}
    {xs ys : List Admin} (h : Control mode left right (c :: xs) ys) (hc : c.IsCallRef) :
    ∃ c' rest, ys = c' :: rest ∧ c'.IsCallRef ∧
      Control mode left right [c] [c'] ∧ Control mode left right xs rest := by
  cases c <;> simp only [Admin.IsCallRef] at hc
  case plain i =>
    cases i <;> simp only at hc
    rename_i x
    obtain ⟨j,rest,hcode,rewrite,hrest⟩ := h.plain_cons (by rfl)
    refine ⟨.plain j,rest,hcode,?_,.plain rewrite .nil,hrest⟩
    cases mode with
    | same => change Instr.callRef x = j at rewrite; rw [← rewrite]; trivial
    | relocated r =>
      simp only [Instruction,instruction?,Option.map_eq_map,Option.map_eq_some_iff] at rewrite
      obtain ⟨y,hy,rfl⟩ := rewrite
      trivial
  case callRefType d =>
    obtain ⟨rest,hcode,hrest⟩ := callRefType_cons h
    exact ⟨.callRefType d,rest,hcode,trivial,.callRefType .nil,hrest⟩

private theorem returnCallRef_cons {mode : Mode} {left right : ModuleInst} {c : Admin}
    {xs ys : List Admin} (h : Control mode left right (c :: xs) ys) (hc : c.IsReturnCallRef) :
    ∃ c' rest, ys = c' :: rest ∧ c'.IsReturnCallRef ∧
      Control mode left right [c] [c'] ∧ Control mode left right xs rest := by
  cases c <;> simp only [Admin.IsReturnCallRef] at hc
  case plain i =>
    cases i <;> simp only at hc
    rename_i x
    obtain ⟨j,rest,hcode,rewrite,hrest⟩ := h.plain_cons (by rfl)
    refine ⟨.plain j,rest,hcode,?_,.plain rewrite .nil,hrest⟩
    cases mode with
    | same => change Instr.returnCallRef x = j at rewrite; rw [← rewrite]; trivial
    | relocated r =>
      simp only [Instruction,instruction?,Option.map_eq_map,Option.map_eq_some_iff] at rewrite
      obtain ⟨y,hy,rfl⟩ := rewrite
      trivial
  case returnCallRefType d =>
    obtain ⟨rest,hcode,hrest⟩ := returnCallRefType_cons h
    exact ⟨.returnCallRefType d,rest,hcode,trivial,.returnCallRefType .nil,hrest⟩

/-- The two cast-branch instructions, selected by whether failure branches. -/
def cast_instr (failure : Bool) (l : LabelIdx) (rt₁ rt₂ : RefType) : Instr :=
  if failure then .brOnCastFail l rt₁ rt₂ else .brOnCast l rt₁ rt₂

/-- Rewriting a scoped cast-branch annotation preserves its instantiated test type. -/
theorem cast_annotation {mode : Mode} {left right : Frame} {failure : Bool}
    {l : LabelIdx} {rt₁ rt₂ : RefType} {j : Instr} (frames : Frames mode left right)
    (rewrite : Instruction mode (cast_instr failure l rt₁ rt₂) j)
    (scope : rt₂.Scoped left.module.types.length) :
    ∃ rt₁' rt₂', j = cast_instr failure l rt₁' rt₂' ∧
      right.module.instRef rt₂' = left.module.instRef rt₂ := by
  cases mode with
  | same => exact ⟨rt₁,rt₂,rewrite.symm,by rw [same_module frames]⟩
  | relocated r =>
    have views : Views.Successful r left.module right.module := by cases frames.view; assumption
    cases failure <;>
      simp [cast_instr,Instruction,instruction?,Option.bind_eq_some_iff] at rewrite
    all_goals obtain ⟨rt₁',h₁,rt₂',h₂,rfl⟩ := rewrite
    all_goals exact ⟨rt₁',rt₂',rfl,ControlViews.closed_ref_type views h₂ scope⟩

private def call_instr (tail : Bool) (x : FuncIdx) : Instr :=
  if tail then .returnCall x else .call x

private theorem call_lookup {mode : Mode} {left right : Frame} {tail : Bool}
    {x : FuncIdx} {address : Nat} {j : Instr} (frames : Frames mode left right)
    (rewrite : Instruction mode (call_instr tail x) j)
    (lookup : left.module.funcs[x.toNat]? = some address) :
    ∃ y, j = call_instr tail y ∧ right.module.funcs[y.toNat]? = some address := by
  cases mode with
  | same => exact ⟨x,rewrite.symm,same_module frames ▸ lookup⟩
  | relocated r =>
    have views : Views.Successful r left.module right.module := by cases frames.view; assumption
    cases tail <;>
      simp [call_instr,Instruction,instruction?] at rewrite
    all_goals obtain ⟨y,hy,rfl⟩ := rewrite
    all_goals exact ⟨y,rfl,views.functions hy lookup⟩

/-- A tail-call annotation leaving related callee frames becomes the same
runtime call tag in any pair of outer caller frames. -/
theorem ret_to_call {innerMode outerMode : Mode} {left right : Frame}
    {outerLeft outerRight : ModuleInst} {c c' : Admin} (frames : Frames innerMode left right)
    (control : Control innerMode left.module right.module [c] [c']) (hc : c.IsReturnCallRef)
    (scope : AdminScope.Admin left.module.types.length c) :
    Control outerMode outerLeft outerRight [c.retToCallIn left.module] [c'.retToCallIn right.module] := by
  cases c <;> simp only [Admin.IsReturnCallRef] at hc
  case plain i =>
    cases i <;> simp only at hc
    rename_i x
    obtain ⟨j,hcode,rewrite⟩ := plain_singleton control (by rfl)
    have hc' : c' = .plain j := (List.cons.inj hcode).1
    subst c'
    have bound : x.toNat < left.module.types.length := by
      simpa only [AdminScope.Admin,CodeScope.Instruction] using scope
    have lookup : left.module.types[x.toNat]? = some left.module.types[x.toNat] :=
      List.getElem?_eq_getElem bound
    cases innerMode with
    | same =>
      change Instr.returnCallRef x = j at rewrite
      subst j
      have lookup' : right.module.types[x.toNat]? = some left.module.types[x.toNat] :=
        same_module frames ▸ lookup
      simp only [Admin.retToCallIn,lookup,lookup']
      exact .callRefType .nil
    | relocated r =>
      simp only [Instruction,instruction?,Option.map_eq_map,Option.map_eq_some_iff] at rewrite
      obtain ⟨y,hy,rfl⟩ := rewrite
      have views : Views.Successful r left.module right.module := by cases frames.view; assumption
      have lookup' := views.types hy lookup
      simp only [Admin.retToCallIn,lookup,lookup']
      exact .callRefType .nil
  case returnCallRefType d =>
    obtain ⟨rest,hcode,hrest⟩ := returnCallRefType_cons control
    have hc' : c' = .returnCallRefType d := (List.cons.inj hcode).1
    subst c'
    exact .callRefType .nil

theorem step {source final target : Config H} {mode : Mode}
    (sourceStep : Step P host source final) (structural : IsStructural sourceStep)
    (matching : Matching mode source target)
    (scope : AdminScope.Admins source.frame.module.types.length source.code)
    (functionScopes : FunctionScopes source.store) :
    ∃ targetFinal, Step P host target targetFinal ∧ Matching mode final targetFinal := by
  rcases target with ⟨st,fr,code⟩
  rcases matching with ⟨stores,frames,control⟩
  cases structural <;> dsimp only at stores frames control scope functionScopes ⊢
  case block s f bt body vs ps rs lookup arity =>
    obtain ⟨j,hcode,rewrite⟩ := control.values_instruction (by rfl)
    have hscope := AdminScope.plain_scope.mp (scope (.plain (.block bt body)) (by simp))
    rw [CodeScope.Instruction] at hscope
    have annotationScope := hscope.1
    cases mode with
    | same =>
      change Instr.block bt body = j at rewrite
      subst j
      refine ⟨⟨st,fr,[.label rs.length [] (vals vs ++ expression body)]⟩,?_,
        ⟨stores,frames,?_⟩⟩
      · rw [hcode]
        exact .block (same_module frames ▸ lookup) arity
      · exact .label rfl ((Control.values _ _ _ vs).append (Control.expression (mode := .same) rfl)) .nil
    | relocated r =>
      change instruction? r (.block bt body) = some j at rewrite
      simp only [instruction?,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,
        Option.some.injEq] at rewrite
      obtain ⟨bt',hb,body',hi,rfl⟩ := rewrite
      have bodyRewrite := attached hi
      have views : Views.Successful r f.module fr.module := by cases frames.view; assumption
      refine ⟨⟨st,fr,[.label rs.length [] (vals vs ++ expression body')]⟩,?_,
        ⟨stores,frames,?_⟩⟩
      · rw [hcode]
        exact .block (ControlViews.block_lookup views hb annotationScope lookup) arity
      · exact .label (empty_instructions _) ((Control.values _ _ _ vs).append
          (Control.expression bodyRewrite)) .nil
  case loop s f bt body vs ps rs lookup arity =>
    obtain ⟨j,hcode,rewrite⟩ := control.values_instruction (by rfl)
    have hscope := AdminScope.plain_scope.mp (scope (.plain (.loop bt body)) (by simp))
    rw [CodeScope.Instruction] at hscope
    have annotationScope := hscope.1
    cases mode with
    | same =>
      change Instr.loop bt body = j at rewrite
      subst j
      refine ⟨⟨st,fr,[.label ps.length [.loop bt body] (vals vs ++ expression body)]⟩,?_,
        ⟨stores,frames,?_⟩⟩
      · rw [hcode]
        exact .loop (same_module frames ▸ lookup) arity
      · exact .label rfl ((Control.values _ _ _ vs).append (Control.expression (mode := .same) rfl)) .nil
    | relocated r =>
      change instruction? r (.loop bt body) = some j at rewrite
      simp only [instruction?,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,
        Option.some.injEq] at rewrite
      obtain ⟨bt',hb,body',hi,rfl⟩ := rewrite
      have bodyRewrite := attached hi
      have views : Views.Successful r f.module fr.module := by cases frames.view; assumption
      refine ⟨⟨st,fr,[.label ps.length [.loop bt' body'] (vals vs ++ expression body')]⟩,?_,
        ⟨stores,frames,?_⟩⟩
      · rw [hcode]
        exact .loop (ControlViews.block_lookup views hb annotationScope lookup) arity
      · have hi' : instruction? r (.loop bt body) = some (.loop bt' body') := by
          simp only [instruction?,hb,hi,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
        have hc : Instructions (.relocated r) [.loop bt body] [.loop bt' body'] := by
          simp only [Instructions,instructions?,List.mapM_cons,hi',List.mapM_nil,
            Option.bind_eq_bind,Option.bind_some,Option.pure_def]
        exact .label hc ((Control.values _ _ _ vs).append (Control.expression bodyRewrite)) .nil
  case ifTrue s f c bt yes no condition =>
    have input : Control mode f.module fr.module (vals [.i32 c] ++ [.plain (.if_ bt yes no)]) code :=
      control
    obtain ⟨j,hcode,rewrite⟩ := input.values_instruction (by rfl)
    cases mode with
    | same =>
      change Instr.if_ bt yes no = j at rewrite
      subst j
      refine ⟨⟨st,fr,[.plain (.block bt yes)]⟩,?_,⟨stores,frames,?_⟩⟩
      · rw [hcode]; exact .ifTrue condition
      · exact .plain rfl .nil
    | relocated r =>
      change instruction? r (.if_ bt yes no) = some j at rewrite
      simp only [instruction?,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,
        Option.some.injEq] at rewrite
      obtain ⟨bt',hb,yes',hy,no',hn,rfl⟩ := rewrite
      refine ⟨⟨st,fr,[.plain (.block bt' yes')]⟩,?_,⟨stores,frames,?_⟩⟩
      · rw [hcode]; exact .ifTrue condition
      · exact .plain (by simp only [Instruction,instruction?,hb,hy,Option.bind_eq_bind,
          Option.bind_some,Option.pure_def]) .nil
  case ifFalse s f bt yes no =>
    have input : Control mode f.module fr.module (vals [.i32 0] ++ [.plain (.if_ bt yes no)]) code :=
      control
    obtain ⟨j,hcode,rewrite⟩ := input.values_instruction (by rfl)
    cases mode with
    | same =>
      change Instr.if_ bt yes no = j at rewrite
      subst j
      refine ⟨⟨st,fr,[.plain (.block bt no)]⟩,?_,⟨stores,frames,?_⟩⟩
      · rw [hcode]; exact .ifFalse
      · exact .plain rfl .nil
    | relocated r =>
      change instruction? r (.if_ bt yes no) = some j at rewrite
      simp only [instruction?,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,
        Option.some.injEq] at rewrite
      obtain ⟨bt',hb,yes',hy,no',hn,rfl⟩ := rewrite
      refine ⟨⟨st,fr,[.plain (.block bt' no')]⟩,?_,⟨stores,frames,?_⟩⟩
      · rw [hcode]; exact .ifFalse
      · exact .plain (by simp only [Instruction,instruction?,hb,hn,Option.bind_eq_bind,
          Option.bind_some,Option.pure_def]) .nil
  case labelVals s f n cont vs =>
    obtain ⟨cont',body',hcode,hcont,hbody⟩ := control.label_singleton
    have hb := hbody.values_left
    refine ⟨⟨st,fr,vals vs⟩,?_,⟨stores,frames,Control.values _ _ _ vs⟩⟩
    rw [hcode,hb]
    exact .labelVals
  case brIfTrue s f c l hc =>
    have input : Control mode f.module fr.module (vals [.i32 c] ++ [.plain (.brIf l)]) code := control
    have hcode := values_stable input (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,[.plain (.br l)]⟩,?_,⟨stores,frames,.plain (unchanged (by intro r; simp only [instruction?])) .nil⟩⟩
    rw [hcode]
    exact .brIfTrue hc
  case brIfFalse s f l =>
    have input : Control mode f.module fr.module (vals [.i32 0] ++ [.plain (.brIf l)]) code := control
    have hcode := values_stable input (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,[]⟩,?_,⟨stores,frames,.nil⟩⟩
    rw [hcode]
    exact .brIfFalse
  case brTableLt s f i ls ld l hi =>
    have input : Control mode f.module fr.module (vals [.i32 i] ++ [.plain (.brTable ls ld)]) code := control
    have hcode := values_stable input (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,[.plain (.br l)]⟩,?_,⟨stores,frames,.plain (unchanged (by intro r; simp only [instruction?])) .nil⟩⟩
    rw [hcode]
    exact .brTableLt hi
  case brTableGe s f i ls ld hi =>
    have input : Control mode f.module fr.module (vals [.i32 i] ++ [.plain (.brTable ls ld)]) code := control
    have hcode := values_stable input (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,[.plain (.br ld)]⟩,?_,⟨stores,frames,.plain (unchanged (by intro r; simp only [instruction?])) .nil⟩⟩
    rw [hcode]
    exact .brTableGe hi
  case brOnNullNull s f l =>
    have input : Control mode f.module fr.module (vals [.ref .null] ++ [.plain (.brOnNull l)]) code := control
    have hcode := values_stable input (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,[.plain (.br l)]⟩,?_,⟨stores,frames,.plain (unchanged (by intro r; simp only [instruction?])) .nil⟩⟩
    rw [hcode]
    exact .brOnNullNull
  case brOnNullAddr s f v l hv =>
    have input : Control mode f.module fr.module (vals [v] ++ [.plain (.brOnNull l)]) code := control
    have hcode := values_stable input (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,[v.toAdmin]⟩,?_,⟨stores,frames,Control.value v⟩⟩
    rw [hcode]
    exact .brOnNullAddr hv
  case brOnNonNullNull s f l =>
    have input : Control mode f.module fr.module (vals [.ref .null] ++ [.plain (.brOnNonNull l)]) code := control
    have hcode := values_stable input (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,[]⟩,?_,⟨stores,frames,.nil⟩⟩
    rw [hcode]
    exact .brOnNonNullNull
  case brOnNonNullAddr s f v l hv =>
    have input : Control mode f.module fr.module (vals [v] ++ [.plain (.brOnNonNull l)]) code := control
    have hcode := values_stable input (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,[v.toAdmin,.plain (.br l)]⟩,?_,⟨stores,frames,.val (.plain (unchanged (by intro r; simp only [instruction?])) .nil)⟩⟩
    rw [hcode]
    exact .brOnNonNullAddr hv
  case brLabelZero s f n cont discard vs l rest zero arity =>
    obtain ⟨cont',body',hcode,hcont,hbody⟩ := control.label_singleton
    simp only [List.append_assoc,List.singleton_append] at hbody
    obtain ⟨middle,rfl,hmiddle⟩ := hbody.values_prefix
    obtain ⟨last,rfl,hlast⟩ := hmiddle.values_prefix
    obtain ⟨rest',hrest,hrel⟩ := plain_stable hlast (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,vals vs ++ expression cont'⟩,?_,
      ⟨stores,frames,(Control.values _ _ _ vs).append (Control.expression hcont)⟩⟩
    rw [hcode,hrest]
    simpa only [List.append_assoc,List.singleton_append] using
      (Step.brLabelZero (P := P) (host := host) (s := st) (f := fr) (cont := cont')
        (vs' := discard) (rest := rest') zero arity)
  case brLabelSucc s f n cont vs l rest positive =>
    obtain ⟨cont',body',hcode,hcont,hbody⟩ := control.label_singleton
    simp only [List.append_assoc,List.singleton_append] at hbody
    obtain ⟨last,rfl,hlast⟩ := hbody.values_prefix
    obtain ⟨rest',hrest,hrel⟩ := plain_stable hlast (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,vals vs ++ [.plain (.br (labelPred l))]⟩,?_,
      ⟨stores,frames,(Control.values _ _ _ vs).append
        (.plain (unchanged (by intro r; simp only [instruction?])) .nil)⟩⟩
    rw [hcode,hrest]
    simpa only [List.append_assoc,List.singleton_append] using
      (Step.brLabelSucc (P := P) (host := host) (s := st) (f := fr) (cont := cont')
        (vs := vs) (rest := rest') positive)
  case brHandler s f n cs vs l rest =>
    obtain ⟨rfl,modules,body',hcode,hbody⟩ := handler_singleton control
    simp only [List.append_assoc,List.singleton_append] at hbody
    obtain ⟨last,rfl,hlast⟩ := hbody.values_prefix
    obtain ⟨rest',hrest,hrel⟩ := plain_stable hlast (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,vals vs ++ [.plain (.br l)]⟩,?_,⟨stores,frames,?_⟩⟩
    · rw [hcode,hrest]
      simpa only [List.append_assoc,List.singleton_append] using
        (Step.brHandler (P := P) (host := host) (s := st) (f := fr) (n := n)
          (cs := cs) (vs := vs) (l := l) (rest := rest'))
    · exact (Control.values _ _ _ vs).append (.plain (unchanged (by intro r; simp only [instruction?])) .nil)
  case frameVals s f inner n vs arity =>
    obtain ⟨innerMode,inner',body',hcode,hframes,hbody⟩ := control.frame_singleton
    have hb := hbody.values_left
    refine ⟨⟨st,fr,vals vs⟩,?_,⟨stores,frames,Control.values _ _ _ vs⟩⟩
    rw [hcode,hb]
    exact .frameVals arity
  case returnFrame s f inner n discard vs rest arity =>
    obtain ⟨innerMode,inner',body',hcode,hframes,hbody⟩ := control.frame_singleton
    simp only [List.append_assoc,List.singleton_append] at hbody
    obtain ⟨middle,rfl,hmiddle⟩ := hbody.values_prefix
    obtain ⟨last,rfl,hlast⟩ := hmiddle.values_prefix
    obtain ⟨rest',hrest,hrel⟩ := plain_stable hlast (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,vals vs⟩,?_,⟨stores,frames,Control.values _ _ _ vs⟩⟩
    rw [hcode,hrest]
    simpa only [List.append_assoc,List.singleton_append] using
      (Step.returnFrame (P := P) (host := host) (s := st) (f := fr) (fi := inner')
        (vs' := discard) (rest := rest') arity)
  case returnLabel s f n cont vs rest =>
    obtain ⟨cont',body',hcode,hcont,hbody⟩ := control.label_singleton
    simp only [List.append_assoc,List.singleton_append] at hbody
    obtain ⟨last,rfl,hlast⟩ := hbody.values_prefix
    obtain ⟨rest',hrest,hrel⟩ := plain_stable hlast (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,vals vs ++ [.plain .return_]⟩,?_,
      ⟨stores,frames,(Control.values _ _ _ vs).append
        (.plain (unchanged (by intro r; simp only [instruction?])) .nil)⟩⟩
    rw [hcode,hrest]
    simpa only [List.append_assoc,List.singleton_append] using
      (Step.returnLabel (P := P) (host := host) (s := st) (f := fr) (n := n)
        (cont := cont') (vs := vs) (rest := rest'))
  case returnHandler s f n cs vs rest =>
    obtain ⟨rfl,modules,body',hcode,hbody⟩ := handler_singleton control
    simp only [List.append_assoc,List.singleton_append] at hbody
    obtain ⟨last,rfl,hlast⟩ := hbody.values_prefix
    obtain ⟨rest',hrest,hrel⟩ := plain_stable hlast (by rfl) (by intro r; simp only [instruction?])
    refine ⟨⟨st,fr,vals vs ++ [.plain .return_]⟩,?_,
      ⟨stores,frames,(Control.values _ _ _ vs).append (.plain (unchanged (by intro r; simp only [instruction?])) .nil)⟩⟩
    rw [hcode,hrest]
    simpa only [List.append_assoc,List.singleton_append] using
      (Step.returnHandler (P := P) (host := host) (s := st) (f := fr) (n := n)
        (cs := cs) (vs := vs) (rest := rest'))
  case trapInstrs s f vs rest nonempty =>
    simp only [List.append_assoc,List.singleton_append] at control
    obtain ⟨last,hcode,hlast⟩ := control.values_prefix
    obtain ⟨rest',hrest,hrel⟩ := hlast.trap_cons
    refine ⟨⟨st,fr,[.trap]⟩,?_,⟨stores,frames,.trap .nil⟩⟩
    rw [hcode,hrest]
    have hn : vs ≠ [] ∨ rest' ≠ [] := nonempty.elim Or.inl (fun hr => Or.inr (nonempty_right hrel hr))
    simpa only [List.append_assoc,List.singleton_append] using
      (Step.trapInstrs (P := P) (host := host) (s := st) (f := fr) hn)
  case trapLabel s f n cont =>
    obtain ⟨cont',body',hcode,hcont,hbody⟩ := control.label_singleton
    refine ⟨⟨st,fr,[.trap]⟩,?_,⟨stores,frames,.trap .nil⟩⟩
    rw [hcode,hbody.trap_singleton]
    exact .trapLabel
  case trapHandler s f n cs =>
    obtain ⟨rfl,modules,body',hcode,hbody⟩ := handler_singleton control
    refine ⟨⟨st,fr,[.trap]⟩,?_,⟨stores,frames,.trap .nil⟩⟩
    rw [hcode,hbody.trap_singleton]
    exact .trapHandler
  case trapFrame s f inner n =>
    obtain ⟨innerMode,inner',body',hcode,hframes,hbody⟩ := control.frame_singleton
    refine ⟨⟨st,fr,[.trap]⟩,?_,⟨stores,frames,.trap .nil⟩⟩
    rw [hcode,hbody.trap_singleton]
    exact .trapFrame
  case brOnCastSucceed s f r l rt₁ rt₂ valid =>
    have input : Control mode f.module fr.module
        (vals [.ref r] ++ [.plain (cast_instr false l rt₁ rt₂)]) code := control
    obtain ⟨j,hcode,rewrite⟩ := input.values_instruction (by simp [cast_instr,Admin.val?])
    have hscope := AdminScope.plain_scope.mp (scope (.plain (cast_instr false l rt₁ rt₂))
      (by simp [cast_instr]))
    simp [cast_instr,CodeScope.Instruction] at hscope
    obtain ⟨rt₁',rt₂',rfl,tag⟩ := cast_annotation frames rewrite hscope.2
    refine ⟨⟨st,fr,[.ref r,.plain (.br l)]⟩,?_,⟨stores,frames,.ref (.plain (unchanged (by intro r; simp only [instruction?])) .nil)⟩⟩
    rw [hcode]
    apply Step.brOnCastSucceed
    rw [tag]
    exact stores.refOk valid
  case brOnCastFail s f r l rt₁ rt₂ valid =>
    have input : Control mode f.module fr.module
        (vals [.ref r] ++ [.plain (cast_instr false l rt₁ rt₂)]) code := control
    obtain ⟨j,hcode,rewrite⟩ := input.values_instruction (by simp [cast_instr,Admin.val?])
    have hscope := AdminScope.plain_scope.mp (scope (.plain (cast_instr false l rt₁ rt₂))
      (by simp [cast_instr]))
    simp [cast_instr,CodeScope.Instruction] at hscope
    obtain ⟨rt₁',rt₂',rfl,tag⟩ := cast_annotation frames rewrite hscope.2
    refine ⟨⟨st,fr,[.ref r]⟩,?_,⟨stores,frames,.ref .nil⟩⟩
    rw [hcode]
    apply Step.brOnCastFail
    rw [tag]
    exact fun h => valid (stores.refOk_reverse h)
  case brOnCastFailSucceed s f r l rt₁ rt₂ valid =>
    have input : Control mode f.module fr.module
        (vals [.ref r] ++ [.plain (cast_instr true l rt₁ rt₂)]) code := control
    obtain ⟨j,hcode,rewrite⟩ := input.values_instruction (by simp [cast_instr,Admin.val?])
    have hscope := AdminScope.plain_scope.mp (scope (.plain (cast_instr true l rt₁ rt₂))
      (by simp [cast_instr]))
    simp [cast_instr,CodeScope.Instruction] at hscope
    obtain ⟨rt₁',rt₂',rfl,tag⟩ := cast_annotation frames rewrite hscope.2
    refine ⟨⟨st,fr,[.ref r]⟩,?_,⟨stores,frames,.ref .nil⟩⟩
    rw [hcode]
    apply Step.brOnCastFailSucceed
    rw [tag]
    exact stores.refOk valid
  case brOnCastFailFail s f r l rt₁ rt₂ valid =>
    have input : Control mode f.module fr.module
        (vals [.ref r] ++ [.plain (cast_instr true l rt₁ rt₂)]) code := control
    obtain ⟨j,hcode,rewrite⟩ := input.values_instruction (by simp [cast_instr,Admin.val?])
    have hscope := AdminScope.plain_scope.mp (scope (.plain (cast_instr true l rt₁ rt₂))
      (by simp [cast_instr]))
    simp [cast_instr,CodeScope.Instruction] at hscope
    obtain ⟨rt₁',rt₂',rfl,tag⟩ := cast_annotation frames rewrite hscope.2
    refine ⟨⟨st,fr,[.ref r,.plain (.br l)]⟩,?_,⟨stores,frames,.ref (.plain (unchanged (by intro r; simp only [instruction?])) .nil)⟩⟩
    rw [hcode]
    apply Step.brOnCastFailFail
    rw [tag]
    exact fun h => valid (stores.refOk_reverse h)
  case call s f x a fi lookup definition =>
    have input : Control mode f.module fr.module [.plain (call_instr false x)] code := control
    obtain ⟨j,hcode,rewrite⟩ := plain_singleton input (by simp [call_instr,Admin.val?])
    obtain ⟨y,rfl,lookup'⟩ := call_lookup frames rewrite lookup
    obtain ⟨fi',definition',paired⟩ := stores.function_lookup definition
    refine ⟨⟨st,fr,[.ref (.func a),.callRefType fi.type]⟩,?_,⟨stores,frames,.ref (.callRefType .nil)⟩⟩
    rw [hcode]
    have hstep := Step.call (P := P) (host := host) (f := fr) lookup' definition'
    rw [← paired.type_eq] at hstep
    exact hstep
  case returnCall s f x a fi lookup definition =>
    have input : Control mode f.module fr.module [.plain (call_instr true x)] code := control
    obtain ⟨j,hcode,rewrite⟩ := plain_singleton input (by simp [call_instr,Admin.val?])
    obtain ⟨y,rfl,lookup'⟩ := call_lookup frames rewrite lookup
    obtain ⟨fi',definition',paired⟩ := stores.function_lookup definition
    refine ⟨⟨st,fr,[.ref (.func a),.returnCallRefType fi.type]⟩,?_,⟨stores,frames,.ref (.returnCallRefType .nil)⟩⟩
    rw [hcode]
    have hstep := Step.returnCall (P := P) (host := host) (f := fr) lookup' definition'
    rw [← paired.type_eq] at hstep
    exact hstep
  case callIndirect s f x y =>
    obtain ⟨j,hcode,rewrite⟩ := plain_singleton control (by rfl)
    cases mode with
    | same =>
      change Instr.callIndirect x y = j at rewrite
      subst j
      refine ⟨⟨st,fr,[.plain (.tableGet x),.plain (.refCast ⟨true,.typeIdx y⟩),.plain (.callRef y)]⟩,?_,⟨stores,frames,.plain rfl (.plain rfl (.plain rfl .nil))⟩⟩
      rw [hcode]
      exact .callIndirect
    | relocated r => simp only [Instruction,instruction?,reduceCtorEq] at rewrite
  case returnCallIndirect s f x y =>
    obtain ⟨j,hcode,rewrite⟩ := plain_singleton control (by rfl)
    cases mode with
    | same =>
      change Instr.returnCallIndirect x y = j at rewrite
      subst j
      refine ⟨⟨st,fr,[.plain (.tableGet x),.plain (.refCast ⟨true,.typeIdx y⟩),.plain (.returnCallRef y)]⟩,?_,⟨stores,frames,.plain rfl (.plain rfl (.plain rfl .nil))⟩⟩
      rw [hcode]
      exact .returnCallIndirect
    | relocated r => simp only [Instruction,instruction?,reduceCtorEq] at rewrite
  case callRefNull s f c hc =>
    obtain ⟨last,hcode,hlast⟩ := control.ref_cons
    obtain ⟨c',rest',hrest,hc',hannotation,hempty⟩ := callRef_cons hlast hc
    rw [hempty.nil_left] at hrest
    refine ⟨⟨st,fr,[.trap]⟩,?_,⟨stores,frames,.trap .nil⟩⟩
    rw [hcode,hrest]
    exact .callRefNull hc'
  case callRefFunc s f c vs a fi ps rs fn hc lookup signature arity wasm =>
    obtain ⟨last,hcode,hlast⟩ := control.values_prefix
    obtain ⟨annotation,hannotationCode,hannotation⟩ := hlast.ref_cons
    obtain ⟨c',rest',hrest,hc',hpair,hempty⟩ := callRef_cons hannotation hc
    rw [hempty.nil_left] at hrest
    obtain ⟨fi',lookup',paired⟩ := stores.function_lookup lookup
    obtain ⟨fn',calleeMode,hwasm,hframes,hbody⟩ := function_entry paired wasm vs
    refine ⟨⟨st,fr,[.frame rs.length (Frame.forCall fi'.module vs fn'.locals)
      [.label rs.length [] (expression fn'.body)]]⟩,?_,
      ⟨stores,frames,.frame hframes (.label (empty_instructions _) hbody .nil) .nil⟩⟩
    rw [hcode,hannotationCode,hrest]
    exact .callRefFunc hc' lookup' (paired.type_eq ▸ signature) arity hwasm
  case returnCallRefLabel s f k cont vs c rest hc =>
    obtain ⟨cont',body',hcode,hcont,hbody⟩ := control.label_singleton
    simp only [List.append_assoc,List.singleton_append] at hbody
    obtain ⟨last,rfl,hlast⟩ := hbody.values_prefix
    obtain ⟨c',rest',hrest,hc',hannotation,hrel⟩ := returnCallRef_cons hlast hc
    refine ⟨⟨st,fr,vals vs ++ [c']⟩,?_,
      ⟨stores,frames,(Control.values _ _ _ vs).append hannotation⟩⟩
    rw [hcode,hrest]
    simpa only [List.append_assoc,List.singleton_append] using
      (Step.returnCallRefLabel (P := P) (host := host) (s := st) (f := fr) (k := k)
        (cont := cont') (vs := vs) (rest := rest') hc')
  case returnCallRefHandler s f k cs vs c rest hc =>
    obtain ⟨rfl,modules,body',hcode,hbody⟩ := handler_singleton control
    simp only [List.append_assoc,List.singleton_append] at hbody
    obtain ⟨last,rfl,hlast⟩ := hbody.values_prefix
    obtain ⟨c',rest',hrest,hc',hannotation,hrel⟩ := returnCallRef_cons hlast hc
    refine ⟨⟨st,fr,vals vs ++ [c']⟩,?_,⟨stores,frames,?_⟩⟩
    · rw [hcode,hrest]
      simpa only [List.append_assoc,List.singleton_append] using
        (Step.returnCallRefHandler (P := P) (host := host) (s := st) (f := fr) (k := k)
          (cs := cs) (vs := vs) (rest := rest') hc')
    · simpa only [← modules] using (Control.values _ _ _ vs).append hannotation
  case returnCallRefFrameNull s f inner k vs c rest hc =>
    obtain ⟨innerMode,inner',body',hcode,hframes,hbody⟩ := control.frame_singleton
    simp only [List.append_assoc] at hbody
    obtain ⟨last,rfl,hlast⟩ := hbody.values_prefix
    obtain ⟨annotation,hannotationCode,hannotation⟩ := hlast.ref_cons
    obtain ⟨c',rest',hrest,hc',hpair,hrel⟩ := returnCallRef_cons hannotation hc
    refine ⟨⟨st,fr,[.trap]⟩,?_,⟨stores,frames,.trap .nil⟩⟩
    rw [hcode,hannotationCode,hrest]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      (Step.returnCallRefFrameNull (P := P) (host := host) (s := st) (f := fr) (fi := inner')
        (k := k) (vs := vs) (rest := rest') hc')
  case returnCallRefFrameAddr s f inner k discard vs a c rest fi ps rs hc lookup signature arity =>
    have bodyScope := AdminScope.frame_scope.mp (scope _ (List.mem_singleton_self _))
    have annotationScope : AdminScope.Admin inner.module.types.length c := bodyScope c (by simp)
    obtain ⟨innerMode,inner',body',hcode,hframes,hbody⟩ := control.frame_singleton
    simp only [List.append_assoc] at hbody
    obtain ⟨middle,rfl,hmiddle⟩ := hbody.values_prefix
    obtain ⟨last,rfl,hlast⟩ := hmiddle.values_prefix
    obtain ⟨annotation,hannotationCode,hannotation⟩ := hlast.ref_cons
    obtain ⟨c',rest',hrest,hc',hpair,hrel⟩ := returnCallRef_cons hannotation hc
    obtain ⟨fi',lookup',paired⟩ := stores.function_lookup lookup
    refine ⟨⟨st,fr,vals vs ++ [.ref (.func a),c'.retToCallIn inner'.module]⟩,?_,
      ⟨stores,frames,(Control.values _ _ _ vs).append
        (.ref (ret_to_call hframes hpair hc annotationScope))⟩⟩
    rw [hcode,hannotationCode,hrest]
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      (Step.returnCallRefFrameAddr (P := P) (host := host) (s := st) (f := fr) (fi := inner')
        (k := k) (vs' := discard) (rest := rest') hc' lookup' (paired.type_eq ▸ signature) arity)


end Silmaril.Wasm.Link.GC.StructuralSimulation
