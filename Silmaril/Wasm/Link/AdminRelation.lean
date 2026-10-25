module

public import Silmaril.Wasm.Link.StoreRelation

/-! # Administrative control under static linking

Unchanged ambient code and relocated module code use separate modes. Each
administrative call frame selects its own mode, so an unchanged caller can
enter a linked function and return to its original module. Values, branch
indices, result arities and local cells agree exactly.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.AdminRelation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-- Ambient code is unchanged; linked code uses the linker's partial rewrite. -/
inductive Mode where
  | same
  | relocated (r : Relocation)

def Instruction : Mode → Instr → Instr → Prop
  | .same, source, target => source = target
  | .relocated r, source, target => instruction? r source = some target

def Instructions : Mode → List Instr → List Instr → Prop
  | .same, source, target => source = target
  | .relocated r, source, target => instructions? r source = some target

inductive View : Mode → ModuleInst → ModuleInst → Prop where
  | same (m : ModuleInst) : View .same m m
  | relocated {r : Relocation} {source target : ModuleInst}
      (views : Views.Successful r source target) : View (.relocated r) source target

structure Frames (mode : Mode) (source target : Frame) : Prop where
  view : View mode source.module target.module
  locals : source.locals = target.locals

theorem Frames.same (f : Frame) : Frames .same f f := ⟨.same _, rfl⟩

theorem Frames.setLocal {mode : Mode} {source target : Frame}
    (h : Frames mode source target) (x : LocalIdx) (v : Val) :
    Frames mode (source.setLocal x v) (target.setLocal x v) := by
  exact ⟨h.view, by simp only [Frame.setLocal, h.locals]⟩

/-- A single relation on instruction lists, including recursively nested
labels and frames. Handlers only occur in unchanged ambient code: the current
linker rejects exception instructions. -/
inductive Control : Mode → ModuleInst → ModuleInst → List Admin → List Admin → Prop where
  | nil {mode source target} : Control mode source target [] []
  | plain {mode source target i j xs ys} (rewrite : Instruction mode i j)
      (rest : Control mode source target xs ys) :
      Control mode source target (.plain i :: xs) (.plain j :: ys)
  | val {mode source target xs ys} {v : Val} (rest : Control mode source target xs ys) :
      Control mode source target (v.toAdmin :: xs) (v.toAdmin :: ys)
  | ref {mode source target r xs ys} (rest : Control mode source target xs ys) :
      Control mode source target (.ref r :: xs) (.ref r :: ys)
  | callRefType {mode source target d xs ys} (rest : Control mode source target xs ys) :
      Control mode source target (.callRefType d :: xs) (.callRefType d :: ys)
  | returnCallRefType {mode source target d xs ys} (rest : Control mode source target xs ys) :
      Control mode source target (.returnCallRefType d :: xs) (.returnCallRefType d :: ys)
  /-- An exception from an unchanged callee can bubble into a relocated caller.
  This administrative instruction is emitted at runtime; source linking still
  rejects exception instructions. -/
  | throwRef {mode source target xs ys} (rest : Control mode source target xs ys) :
      Control mode source target (.plain .throwRef :: xs) (.plain .throwRef :: ys)
  | label {mode source target n cont cont' body body' xs ys}
      (continuation : Instructions mode cont cont')
      (inner : Control mode source target body body')
      (rest : Control mode source target xs ys) :
      Control mode source target (.label n cont body :: xs) (.label n cont' body' :: ys)
  | handler {source n catches body body' xs ys}
      (inner : Control .same source source body body')
      (rest : Control .same source source xs ys) :
      Control .same source source (.handler n catches body :: xs) (.handler n catches body' :: ys)
  | frame {mode source target innerMode n f f' body body' xs ys}
      (frames : Frames innerMode f f')
      (inner : Control innerMode f.module f'.module body body')
      (rest : Control mode source target xs ys) :
      Control mode source target (.frame n f body :: xs) (.frame n f' body' :: ys)
  | trap {mode source target xs ys} (rest : Control mode source target xs ys) :
      Control mode source target (.trap :: xs) (.trap :: ys)

theorem Control.length_eq {mode source target xs ys}
    (h : Control mode source target xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

theorem Control.append {mode source target xs ys xs' ys'}
    (h : Control mode source target xs ys) (h' : Control mode source target xs' ys') :
    Control mode source target (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => exact h'
  | plain hr _ ih => exact .plain hr (ih h')
  | val _ ih => exact .val (ih h')
  | ref _ ih => exact .ref (ih h')
  | callRefType _ ih => exact .callRefType (ih h')
  | returnCallRefType _ ih => exact .returnCallRefType (ih h')
  | throwRef _ ih => exact .throwRef (ih h')
  | label hc hb _ _ ih => exact .label hc hb (ih h')
  | handler hb _ _ ih => exact .handler hb (ih h')
  | frame hf hb _ _ ih => exact .frame hf hb (ih h')
  | trap _ ih => exact .trap (ih h')

theorem Control.split {mode source target xs ys zs}
    (h : Control mode source target (xs ++ ys) zs) :
    ∃ xs' ys', zs = xs' ++ ys' ∧ Control mode source target xs xs' ∧
      Control mode source target ys ys' := by
  induction xs generalizing zs with
  | nil => exact ⟨[], zs, rfl, .nil, h⟩
  | cons a xs ih =>
    cases h with
    | plain hr rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .plain hr hx, hy⟩
    | val rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .val hx, hy⟩
    | ref rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .ref hx, hy⟩
    | callRefType rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .callRefType hx, hy⟩
    | returnCallRefType rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .returnCallRefType hx, hy⟩
    | throwRef rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .throwRef hx, hy⟩
    | label hc hb rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .label hc hb hx, hy⟩
    | handler hb rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .handler hb hx, hy⟩
    | frame hf hb rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .frame hf hb hx, hy⟩
    | trap rest =>
      obtain ⟨xs', ys', rfl, hx, hy⟩ := ih rest
      exact ⟨_ :: xs', ys', rfl, .trap hx, hy⟩

theorem Control.value {mode source target} (v : Val) :
    Control mode source target [v.toAdmin] [v.toAdmin] := .val .nil

theorem Control.values (mode : Mode) (source target : ModuleInst) (vs : List Val) :
    Control mode source target (vals vs) (vals vs) := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih => exact (Control.value v).append ih

theorem Instruction.value_result {mode : Mode} {i j : Instr} {v : Val}
    (rewrite : Instruction mode i j) (value : (Admin.plain i).val? = some v) :
    Admin.plain j = v.toAdmin := by
  cases mode with
  | same =>
    change i = j at rewrite
    subst j
    exact Admin.eq_of_val? value
  | relocated r =>
    change instruction? r i = some j at rewrite
    cases i <;> simp only [Admin.val?, reduceCtorEq] at value
    all_goals simp only [instruction?, Option.some.injEq, reduceCtorEq] at rewrite
    all_goals subst j; cases value; rfl

theorem Control.head_value {mode source target a b xs ys v}
    (h : Control mode source target (a :: xs) (b :: ys)) (value : a.val? = some v) :
    b = v.toAdmin := by
  cases h with
  | plain hr _ => exact Instruction.value_result hr value
  | val _ => exact Admin.eq_of_val? value
  | ref _ => exact Admin.eq_of_val? value
  | callRefType _ => simp [Admin.val?] at value
  | returnCallRefType _ => simp [Admin.val?] at value
  | throwRef _ => simp [Admin.val?] at value
  | label _ _ _ => simp [Admin.val?] at value
  | handler _ _ => simp [Admin.val?] at value
  | frame _ _ _ => simp [Admin.val?] at value
  | trap _ => simp [Admin.val?] at value

theorem Control.tail {mode source target a b xs ys}
    (h : Control mode source target (a :: xs) (b :: ys)) :
    Control mode source target xs ys := by cases h <;> assumption

/-- Runtime operands retain their exact values under either code mode. -/
theorem Control.values_left {mode source target vs ys}
    (h : Control mode source target (vals vs) ys) : ys = vals vs := by
  induction vs generalizing ys with
  | nil => cases h; rfl
  | cons v vs ih =>
    cases ys with
    | nil => have := h.length_eq; simp only [vals_length, List.length_cons, List.length_nil] at this; omega
    | cons a ys =>
      rw [h.head_value (Admin.val?_toAdmin v), ih h.tail]
      rfl

theorem Control.expression {mode source target xs ys}
    (h : Instructions mode xs ys) :
    Control mode source target (expression xs) (expression ys) := by
  cases mode with
  | same =>
    change xs = ys at h
    subst ys
    induction xs with
    | nil => exact .nil
    | cons i xs ih => exact .plain rfl ih
  | relocated r =>
    change instructions? r xs = some ys at h
    have hr := List.mapM_some_forall₂ (R := fun a b => instruction? r a = some b)
      (fun h => h) h
    generalize hx : xs = left at hr ⊢
    generalize hy : ys = right at hr ⊢
    clear h hx hy
    induction hr with
    | nil => exact .nil
    | cons h _ ih => exact .plain h ih

/-- All ambient syntax is available in the unchanged mode, including
instructions outside the static linker's GC fragment. -/
theorem Control.same (m : ModuleInst) (xs : List Admin) : Control .same m m xs xs := by
  cases xs with
  | nil => exact .nil
  | cons a xs =>
    have rest := Control.same m xs
    cases a with
    | plain i => exact .plain rfl rest
    | ref r => exact .ref rest
    | callRefType d => exact .callRefType rest
    | returnCallRefType d => exact .returnCallRefType rest
    | label n cont body => exact .label rfl (Control.same m body) rest
    | handler n catches body => exact .handler (Control.same m body) rest
    | frame n f body => exact .frame (Frames.same f) (Control.same f.module body) rest
    | trap => exact .trap rest
termination_by sizeOf xs
decreasing_by all_goals simp_wf; all_goals omega

/-- A corresponding stored wasm definition supplies the next call frame's
mode, matching locals and the actual rewritten expression. -/
theorem function_entry {H : Type} {source target : FuncInst H} {code : Func}
    (functions : StoreRelation.Function source target) (wasm : source.code = .wasm code)
    (args : List Val) :
    ∃ targetCode mode, target.code = .wasm targetCode ∧
      Frames mode (Frame.forCall source.module args code.locals)
        (Frame.forCall target.module args targetCode.locals) ∧
      Control mode source.module target.module (expression code.body) (expression targetCode.body) := by
  cases functions with
  | same fi => exact ⟨code, .same, wasm, Frames.same _, Control.same _ _⟩
  | @relocated tag left right sourceCode targetCode r views rewrite =>
    cases wasm
    exact ⟨targetCode, .relocated r, rfl, ⟨.relocated views, rewrite.forCall_locals _ _ args⟩,
      Control.expression rewrite.body⟩

inductive Configs {H : Type} (source target : Config H) : Prop where
  | mk {mode : Mode} (stores : StoreRelation.Related source.store target.store)
      (frames : Frames mode source.frame target.frame)
      (code : Control mode source.frame.module target.frame.module source.code target.code) :
      Configs source target

/-- Calls enter paired actual bodies, even when the caller's own code is
unchanged. No execution equivalence is assumed of the stored definitions. -/
theorem callRefFunc {H : Type} {P : Profile} {host : HostSemantics H}
    {sourceStore targetStore : Store H} {sourceCaller targetCaller : Frame}
    {mode : Mode} {address : Nat} {sourceFunction : FuncInst H} {code : Func}
    {args : List Val} {params results : Ty (.list .val)}
    (stores : StoreRelation.Related sourceStore targetStore)
    (callers : Frames mode sourceCaller targetCaller)
    (lookup : sourceStore.funcs[address]? = some sourceFunction)
    (wasm : sourceFunction.code = .wasm code)
    (signature : Expand sourceFunction.type (.func params results))
    (arity : args.length = params.length) :
    ∃ targetFinal,
      Step P host
        ⟨targetStore, targetCaller,
          vals args ++ [.ref (.func address), .callRefType sourceFunction.type]⟩ targetFinal ∧
      Configs
        ⟨sourceStore, sourceCaller,
          [.frame results.length (Frame.forCall sourceFunction.module args code.locals)
            [.label results.length [] (expression code.body)]]⟩ targetFinal := by
  obtain ⟨targetFunction, targetLookup, functions⟩ := stores.function_lookup lookup
  obtain ⟨targetCode, calleeMode, targetWasm, frames, body⟩ := function_entry functions wasm args
  refine ⟨⟨targetStore, targetCaller,
    [.frame results.length (Frame.forCall targetFunction.module args targetCode.locals)
      [.label results.length [] (expression targetCode.body)]]⟩, ?_, ?_⟩
  · exact .callRefFunc trivial targetLookup (functions.type_eq ▸ signature) arity targetWasm
  · exact .mk stores callers (.frame frames (.label (by cases calleeMode <;> rfl) body .nil) .nil)

end Silmaril.Wasm.Link.GC.AdminRelation
