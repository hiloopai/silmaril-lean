module

public import Silmaril.Wasm.Link.ControlInversion
public import Silmaril.Wasm.Link.AmbientSimulation
public import Silmaril.Proofs.Wasm.Game.Machine.Soft

/-!
# Static linking: inverting the code relation from the linked side

silmaril-lean's `AdminRelation.Control` inversions (`Silmaril/Wasm/Link/ControlInversion.lean`)
start from the source (shared world) code. The backward simulation of the linker needs the
converse: the source code is determined, up to `Control`, by the shape of the linked code.

* `Control.split_right`, `Control.cons_right`: splitting along the target;
* `Control.single_*_right`: the source of a value, `TRAP`, `THROW_REF`, plain instruction,
  label, handler or frame (`instruction?` never produces a constant from a non-constant);
* `Control.values_right`, `Control.result_right`, `Control.throwing_right`;
* `instruction?_choice`: a relocated instruction of a numeric, vector, table or memory family
  is a numeric instruction, unchanged by relocation (vector, table and memory instructions
  are rejected by the linker);
* `table_back`, `memory_back`: table and memory steps of the linked store are steps of the
  shared store (the stores agree on everything but function code), mirroring
  `AmbientSimulation.table_same`/`memory_same`.

New (no source file); the reverse lookups mirror silmaril-lean's forward ones at the pinned
revision.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Linking

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation Silmaril.Wasm.SingleThreaded.Det
  Silmaril.Proofs.Wasm.Game.Choice

variable {H : Type}

/-! ### Splitting along the target -/

theorem Control.split_right {mode : Mode} {m m' : ModuleInst} {xs A B : List Admin}
    (h : Control mode m m' xs (A ++ B)) :
    ∃ A₀ B₀, xs = A₀ ++ B₀ ∧ Control mode m m' A₀ A ∧ Control mode m m' B₀ B := by
  have hlen : xs.length = A.length + B.length := by simpa using h.length_eq
  have hx : xs = xs.take A.length ++ xs.drop A.length := (List.take_append_drop _ _).symm
  rw [hx] at h
  obtain ⟨A', B', heq, hA, hB⟩ := h.split
  have hlA : A.length = A'.length := by
    have := hA.length_eq
    simp only [List.length_take] at this
    omega
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hlA
  exact ⟨_, _, hx, hA, hB⟩

theorem Control.cons_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin} {y : Admin}
    {ys : List Admin} (h : Control mode m m' xs (y :: ys)) :
    ∃ x xs', xs = x :: xs' ∧ Control mode m m' [x] [y] ∧ Control mode m m' xs' ys := by
  obtain ⟨A₀, B₀, rfl, hA, hB⟩ := Control.split_right (A := [y]) (B := ys) h
  have hl : A₀.length = 1 := by simpa using hA.length_eq
  match A₀, hl with
  | [x], _ => exact ⟨x, B₀, rfl, hA, hB⟩

/-! ### Single instructions -/

theorem instruction?_select {r : Relocation} {o : Option (List ValType)} {j : Instr}
    (h : instruction? r (.select o) = some j) : ∃ o', j = .select o' := by
  cases o with
  | none => simp only [instruction?, Option.some.injEq] at h; exact ⟨none, h.symm⟩
  | some ts =>
    simp only [instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ts', -, rfl⟩ := h
    exact ⟨_, rfl⟩

/-- `instruction?` produces a constant only from that constant. -/
theorem instruction?_val {r : Relocation} {i j : Instr} (h : instruction? r i = some j)
    {v : Val} (hv : (Admin.plain j).val? = some v) : i = j := by
  cases j <;> simp only [Admin.val?, reduceCtorEq] at hv <;>
    (cases i <;> first
      | (obtain ⟨_, h'⟩ := instruction?_select h; cases h')
      | simp_all [instruction?, Option.bind_eq_some_iff])

set_option linter.unusedTactic false in
/-- A relocated instruction of a choice family is numeric and unchanged. -/
theorem instruction?_choice {r : Relocation} {i j : Instr} (h : instruction? r i = some j)
    (hk : ChoiceFam (famOf (.plain j))) : i = j ∧ famOf (.plain j) = .numeric := by
  cases i <;> first
    | (obtain ⟨_, h'⟩ := instruction?_select h; subst h'; exact absurd hk id)
    | (simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, reduceCtorEq] at h ; all_goals
       first
       | (subst h; simp [famOf, ChoiceFam] at hk ⊢)
       | (obtain ⟨_, _, rfl⟩ := h; exact hk.elim)
       | (obtain ⟨_, _, _, _, rfl⟩ := h; exact hk.elim)
       | (obtain ⟨_, _, _, _, _, _, rfl⟩ := h; exact hk.elim))

theorem Instruction.val_right {mode : Mode} {i j : Instr} (h : Instruction mode i j) {v : Val}
    (hv : (Admin.plain j).val? = some v) : i = j := by
  cases mode with
  | same => exact h
  | relocated r => exact instruction?_val h hv

theorem Instruction.choice_right {mode : Mode} {i j : Instr} (h : Instruction mode i j)
    (hk : ChoiceFam (famOf (.plain j))) :
    i = j ∧ (mode = .same ∨ famOf (.plain j) = .numeric) := by
  cases mode with
  | same => exact ⟨h, .inl rfl⟩
  | relocated r =>
    obtain ⟨rfl, hn⟩ := instruction?_choice h hk
    exact ⟨rfl, .inr hn⟩

/-- `throw_ref` is not relocated (the linker rejects exception instructions). -/
theorem Instruction.throwRef_right {mode : Mode} {i : Instr} (h : Instruction mode i .throwRef) :
    i = .throwRef := by
  cases mode with
  | same => exact h
  | relocated r =>
    change instruction? r i = some .throwRef at h
    cases i <;> first
      | (obtain ⟨_, h'⟩ := instruction?_select h; cases h')
      | simp_all [instruction?, Option.bind_eq_some_iff]

/-! ### One instruction of the code relation -/

/-- The code relation on one administrative instruction. -/
inductive One : Mode → ModuleInst → ModuleInst → Admin → Admin → Prop where
  | plain {mode m m' i j} (rewrite : Instruction mode i j) : One mode m m' (.plain i) (.plain j)
  | val {mode m m' a} (hv : a.val? ≠ none) : One mode m m' a a
  | callRefType {mode m m' d} : One mode m m' (.callRefType d) (.callRefType d)
  | returnCallRefType {mode m m' d} : One mode m m' (.returnCallRefType d) (.returnCallRefType d)
  | throwRef {mode m m'} : One mode m m' (.plain .throwRef) (.plain .throwRef)
  | label {mode m m' n cont cont' body body'} (continuation : Instructions mode cont cont')
      (inner : Control mode m m' body body') :
      One mode m m' (.label n cont body) (.label n cont' body')
  | handler {m n catches body body'} (inner : Control .same m m body body') :
      One .same m m (.handler n catches body) (.handler n catches body')
  | frame {mode m m' innerMode n f f' body body'} (frames : Frames innerMode f f')
      (inner : Control innerMode f.module f'.module body body') :
      One mode m m' (.frame n f body) (.frame n f' body')
  | trap {mode m m'} : One mode m m' .trap .trap

theorem Control.cons_inv {mode : Mode} {m m' : ModuleInst} {x y : Admin} {xs ys : List Admin}
    (h : Control mode m m' (x :: xs) (y :: ys)) : One mode m m' x y ∧ Control mode m m' xs ys := by
  generalize hX : x :: xs = X at h
  generalize hY : y :: ys = Y at h
  cases h <;> simp only [List.cons.injEq, reduceCtorEq] at hX hY <;>
    obtain ⟨rfl, rfl⟩ := hX <;> obtain ⟨rfl, rfl⟩ := hY
  case plain hr hrest => exact ⟨.plain hr, hrest⟩
  case val v hrest => exact ⟨.val (by simp), hrest⟩
  case ref r hrest => exact ⟨.val (by simp [Admin.val?]), hrest⟩
  case callRefType hrest => exact ⟨.callRefType, hrest⟩
  case returnCallRefType hrest => exact ⟨.returnCallRefType, hrest⟩
  case throwRef hrest => exact ⟨.throwRef, hrest⟩
  case label hc hb hrest => exact ⟨.label hc hb, hrest⟩
  case handler hb hrest => exact ⟨.handler hb, hrest⟩
  case frame hf hb hrest => exact ⟨.frame hf hb, hrest⟩
  case trap hrest => exact ⟨.trap, hrest⟩

theorem One.val_right {mode : Mode} {m m' : ModuleInst} {x y : Admin} {v : Val}
    (h : One mode m m' x y) (hv : y.val? = some v) : x = y := by
  cases h with
  | plain hr => rw [Instruction.val_right hr hv]
  | val _ => rfl
  | _ => simp [Admin.val?] at hv

theorem One.trap_right {mode : Mode} {m m' : ModuleInst} {x : Admin}
    (h : One mode m m' x .trap) : x = .trap := by
  cases h <;> rfl

theorem One.throwRef_right {mode : Mode} {m m' : ModuleInst} {x : Admin}
    (h : One mode m m' x (.plain .throwRef)) : x = .plain .throwRef := by
  cases h with
  | plain hr => rw [Instruction.throwRef_right hr]
  | val _ => rfl
  | throwRef => rfl

theorem One.choice_right {mode : Mode} {m m' : ModuleInst} {x : Admin} {j : Instr}
    (h : One mode m m' x (.plain j)) (hk : ChoiceFam (famOf (.plain j))) :
    x = .plain j ∧ (mode = .same ∨ famOf (.plain j) = .numeric) := by
  cases h with
  | plain hr =>
    obtain ⟨rfl, h'⟩ := Instruction.choice_right hr hk
    exact ⟨rfl, h'⟩
  | val hv =>
    exfalso
    cases j <;> simp only [Admin.val?, ne_eq, not_true_eq_false, reduceCtorEq] at hv <;>
      exact hk.elim
  | throwRef => exact hk.elim

theorem One.label_right {mode : Mode} {m m' : ModuleInst} {x : Admin} {n : Nat}
    {cont' : List Instr} {body' : List Admin} (h : One mode m m' x (.label n cont' body')) :
    ∃ cont body, x = .label n cont body ∧ Instructions mode cont cont' ∧
      Control mode m m' body body' := by
  cases h with
  | val hv => simp [Admin.val?] at hv
  | label hc hb => exact ⟨_, _, rfl, hc, hb⟩

theorem One.handler_right {mode : Mode} {m m' : ModuleInst} {x : Admin} {n : Nat}
    {cs : List Catch} {body' : List Admin} (h : One mode m m' x (.handler n cs body')) :
    mode = .same ∧ m = m' ∧ ∃ body, x = .handler n cs body ∧ Control .same m m body body' := by
  cases h with
  | val hv => simp [Admin.val?] at hv
  | handler hb => exact ⟨rfl, rfl, _, rfl, hb⟩

theorem One.frame_right {mode : Mode} {m m' : ModuleInst} {x : Admin} {n : Nat}
    {f' : Frame} {body' : List Admin} (h : One mode m m' x (.frame n f' body')) :
    ∃ innerMode f body, x = .frame n f body ∧ Frames innerMode f f' ∧
      Control innerMode f.module f'.module body body' := by
  cases h with
  | val hv => simp [Admin.val?] at hv
  | frame hf hb => exact ⟨_, _, _, rfl, hf, hb⟩

/-! ### Lists -/

theorem Control.nil_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin}
    (h : Control mode m m' xs []) : xs = [] :=
  List.eq_nil_of_length_eq_zero (by simpa using h.length_eq)

theorem Control.single_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin} {y : Admin}
    (h : Control mode m m' xs [y]) : ∃ x, xs = [x] ∧ One mode m m' x y := by
  obtain ⟨x, xs', rfl, hx, hr⟩ := Control.cons_right h
  rw [Control.nil_right hr]
  exact ⟨x, rfl, (Control.cons_inv hx).1⟩

theorem Control.values_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin} {vs : List Val}
    (h : Control mode m m' xs (vals vs)) : xs = vals vs := by
  induction vs generalizing xs with
  | nil => exact Control.nil_right h
  | cons v vs ih =>
    obtain ⟨x, xs', rfl, hx, hr⟩ := Control.cons_right h
    obtain ⟨y, hy, hone⟩ := Control.single_right hx
    cases hy
    rw [hone.val_right (Admin.val?_toAdmin v), ih hr]
    rfl

theorem Control.trap_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin}
    (h : Control mode m m' xs [.trap]) : xs = [.trap] := by
  obtain ⟨x, rfl, hx⟩ := Control.single_right h
  rw [hx.trap_right]

theorem Control.throwing_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin} {a : Nat}
    (h : Control mode m m' xs (throwing a)) : xs = throwing a := by
  obtain ⟨x, xs', rfl, hx, hr⟩ := Control.cons_right h
  obtain ⟨y, hy, hone⟩ := Control.single_right hx
  cases hy
  obtain ⟨z, rfl, hz⟩ := Control.single_right hr
  rw [hone.val_right (v := .ref (.exn a)) rfl, hz.throwRef_right]

theorem Control.result_right {mode : Mode} {m m' : ModuleInst} {xs : List Admin} {r : Result}
    (h : Control mode m m' xs r.toAdmin) : xs = r.toAdmin := by
  cases r with
  | values vs => exact Control.values_right h
  | trap => exact Control.trap_right h
  | throw a => exact Control.throwing_right h

/-! ### Tables and memories, backwards -/

section ambient

variable {P : Profile}

private theorem table_lookup' {s s' : Store H} (stores : StoreRelation.Related s s') {f : Frame}
    {x : TableIdx} {a : Nat} {ti : TableInst} (h : s'.table? f x = some (a, ti)) :
    s.table? f x = some (a, ti) := by
  simpa only [Store.table?, stores.tables] using h

private theorem elem_lookup' {s s' : Store H} (stores : StoreRelation.Related s s') {f : Frame}
    {x : ElemIdx} {a : Nat} {ei : ElemInst} (h : s'.elem? f x = some (a, ei)) :
    s.elem? f x = some (a, ei) := by
  simpa only [Store.elem?, stores.elems] using h

private theorem mem_lookup' {s s' : Store H} (stores : StoreRelation.Related s s') {f : Frame}
    {x : MemIdx} {a : Nat} {mi : MemInst} (h : s'.mem? f x = some (a, mi)) :
    s.mem? f x = some (a, mi) := by
  simpa only [Store.mem?, stores.mems] using h

private theorem data_lookup' {s s' : Store H} (stores : StoreRelation.Related s s') {f : Frame}
    {x : DataIdx} {a : Nat} {di : DataInst} (h : s'.data? f x = some (a, di)) :
    s.data? f x = some (a, di) := by
  simpa only [Store.data?, stores.datas] using h

/-- A table step of the linked store is a table step of the shared store (the converse of
`AmbientSimulation.table_same`). -/
theorem table_back {s s' s'' : Store H} {f f'' : Frame} {code out : List Admin}
    (stores : StoreRelation.Related s s') (h : TableStep P ⟨s', f, code⟩ ⟨s'', f'', out⟩) :
    ∃ s₂, TableStep P ⟨s, f, code⟩ ⟨s₂, f'', out⟩ ∧ StoreRelation.Related s₂ s'' := by
  cases h with
  | getOob ht h => exact ⟨s, .getOob (table_lookup' stores ht) h, stores⟩
  | getVal ht h => exact ⟨s, .getVal (table_lookup' stores ht) h, stores⟩
  | setOob ht h => exact ⟨s, .setOob (table_lookup' stores ht) h, stores⟩
  | setVal ht h => exact ⟨_, .setVal (table_lookup' stores ht) h, stores.setTable _ _⟩
  | size ht => exact ⟨s, .size (table_lookup' stores ht), stores⟩
  | growSucceed ht hg hp =>
    exact ⟨_, .growSucceed (table_lookup' stores ht) hg hp, stores.setTable _ _⟩
  | growFail ht hp => exact ⟨s, .growFail (table_lookup' stores ht) hp, stores⟩
  | fillOob ht h => exact ⟨s, .fillOob (table_lookup' stores ht) h, stores⟩
  | fillZero ht h => exact ⟨s, .fillZero (table_lookup' stores ht) h, stores⟩
  | fillSucc ht h hn => exact ⟨s, .fillSucc (table_lookup' stores ht) h hn, stores⟩
  | copyOob h₁ h₂ h =>
    exact ⟨s, .copyOob (table_lookup' stores h₁) (table_lookup' stores h₂) h, stores⟩
  | copyZero h₁ h₂ h =>
    exact ⟨s, .copyZero (table_lookup' stores h₁) (table_lookup' stores h₂) h, stores⟩
  | copyLe h₁ h₂ h hn hle =>
    exact ⟨s, .copyLe (table_lookup' stores h₁) (table_lookup' stores h₂) h hn hle, stores⟩
  | copyGt h₁ h₂ h hn hgt =>
    exact ⟨s, .copyGt (table_lookup' stores h₁) (table_lookup' stores h₂) h hn hgt, stores⟩
  | initOob ht he h =>
    exact ⟨s, .initOob (table_lookup' stores ht) (elem_lookup' stores he) h, stores⟩
  | initZero ht he h =>
    exact ⟨s, .initZero (table_lookup' stores ht) (elem_lookup' stores he) h, stores⟩
  | initSucc ht he h hn hr =>
    exact ⟨s, .initSucc (table_lookup' stores ht) (elem_lookup' stores he) h hn hr, stores⟩
  | elemDrop he => exact ⟨_, .elemDrop (elem_lookup' stores he), stores.setElem _ []⟩

/-- A memory step of the linked store is a memory step of the shared store (the converse of
`AmbientSimulation.memory_same`). -/
theorem memory_back {s s' s'' : Store H} {f f'' : Frame} {code out : List Admin}
    (stores : StoreRelation.Related s s') (h : MemoryStep P ⟨s', f, code⟩ ⟨s'', f'', out⟩) :
    ∃ s₂, MemoryStep P ⟨s, f, code⟩ ⟨s₂, f'', out⟩ ∧ StoreRelation.Related s₂ s'' := by
  cases h with
  | loadIntOob hm h => exact ⟨s, .loadIntOob (mem_lookup' stores hm) h, stores⟩
  | loadIntVal hm hl => exact ⟨s, .loadIntVal (mem_lookup' stores hm) hl, stores⟩
  | loadPackOob hm h => exact ⟨s, .loadPackOob (mem_lookup' stores hm) h, stores⟩
  | loadPackVal hm hl => exact ⟨s, .loadPackVal (mem_lookup' stores hm) hl, stores⟩
  | loadFloatOob hm h => exact ⟨s, .loadFloatOob (mem_lookup' stores hm) h, stores⟩
  | loadFloatVal hm hl => exact ⟨s, .loadFloatVal (mem_lookup' stores hm) hl, stores⟩
  | vecLoadOob hm h => exact ⟨s, .vecLoadOob (mem_lookup' stores hm) h, stores⟩
  | vecLoadVal hm hl => exact ⟨s, .vecLoadVal (mem_lookup' stores hm) hl, stores⟩
  | vecLoadLaneOob hm h => exact ⟨s, .vecLoadLaneOob (mem_lookup' stores hm) h, stores⟩
  | vecLoadLaneVal hm hl => exact ⟨s, .vecLoadLaneVal (mem_lookup' stores hm) hl, stores⟩
  | storeIntOob hm h => exact ⟨s, .storeIntOob (mem_lookup' stores hm) h, stores⟩
  | storeIntVal hm hs => exact ⟨_, .storeIntVal (mem_lookup' stores hm) hs, stores.setMem _ _⟩
  | storePackOob hm h => exact ⟨s, .storePackOob (mem_lookup' stores hm) h, stores⟩
  | storePackVal hm hs => exact ⟨_, .storePackVal (mem_lookup' stores hm) hs, stores.setMem _ _⟩
  | storeFloatOob hm h => exact ⟨s, .storeFloatOob (mem_lookup' stores hm) h, stores⟩
  | storeFloatVal hm hs =>
    exact ⟨_, .storeFloatVal (mem_lookup' stores hm) hs, stores.setMem _ _⟩
  | vecStoreOob hm h => exact ⟨s, .vecStoreOob (mem_lookup' stores hm) h, stores⟩
  | vecStoreVal hm hs => exact ⟨_, .vecStoreVal (mem_lookup' stores hm) hs, stores.setMem _ _⟩
  | vecStoreLaneOob hm h => exact ⟨s, .vecStoreLaneOob (mem_lookup' stores hm) h, stores⟩
  | vecStoreLaneVal hm hs =>
    exact ⟨_, .vecStoreLaneVal (mem_lookup' stores hm) hs, stores.setMem _ _⟩
  | size hm => exact ⟨s, .size (mem_lookup' stores hm), stores⟩
  | growSucceed hm hg hp =>
    exact ⟨_, .growSucceed (mem_lookup' stores hm) hg hp, stores.setMem _ _⟩
  | growFail hm hp => exact ⟨s, .growFail (mem_lookup' stores hm) hp, stores⟩
  | fillOob hm h => exact ⟨s, .fillOob (mem_lookup' stores hm) h, stores⟩
  | fillZero hm h => exact ⟨s, .fillZero (mem_lookup' stores hm) h, stores⟩
  | fillSucc hm h hn => exact ⟨s, .fillSucc (mem_lookup' stores hm) h hn, stores⟩
  | copyOob h₁ h₂ h =>
    exact ⟨s, .copyOob (mem_lookup' stores h₁) (mem_lookup' stores h₂) h, stores⟩
  | copyZero h₁ h₂ h =>
    exact ⟨s, .copyZero (mem_lookup' stores h₁) (mem_lookup' stores h₂) h, stores⟩
  | copyLe h₁ h₂ h hn hle =>
    exact ⟨s, .copyLe (mem_lookup' stores h₁) (mem_lookup' stores h₂) h hn hle, stores⟩
  | copyGt h₁ h₂ h hn hgt =>
    exact ⟨s, .copyGt (mem_lookup' stores h₁) (mem_lookup' stores h₂) h hn hgt, stores⟩
  | initOob hm hd h =>
    exact ⟨s, .initOob (mem_lookup' stores hm) (data_lookup' stores hd) h, stores⟩
  | initZero hm hd h =>
    exact ⟨s, .initZero (mem_lookup' stores hm) (data_lookup' stores hd) h, stores⟩
  | initSucc hm hd h hn hb =>
    exact ⟨s, .initSucc (mem_lookup' stores hm) (data_lookup' stores hd) h hn hb, stores⟩
  | dataDrop hd => exact ⟨_, .dataDrop (data_lookup' stores hd), stores.setData _ _⟩

end ambient

/-- Frames related in the unchanged mode are equal. -/
theorem Frames.same_eq {f f' : Frame} (h : Frames .same f f') : f = f' := by
  have hm : f.module = f'.module := by
    have hv := h.view
    generalize f.module = a at hv
    generalize f'.module = b at hv
    cases hv
    rfl
  rcases f with ⟨l, m⟩
  rcases f' with ⟨l', m'⟩
  have hl : l = l' := h.locals
  simp only at hm
  rw [hl, hm]

end Silmaril.Proofs.Wasm.Game.Linking
