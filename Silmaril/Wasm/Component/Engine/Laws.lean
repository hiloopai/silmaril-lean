module

public import Silmaril.Wasm.Component.Engine.Interface
public import Silmaril.Foundations.InfiniteTrace

/-!
# Laws and executable extension of a core engine

This file states what the component runtime relies on from a `CoreEngine` (its laws, and an optional
executable layer):

* `CoreEngine.Extends s s'`: store extension. Existing function types, memory and table address
  types, and the callout status of every thread persist; memories only grow. It is the engine-level
  analogue of `Execution.Runtime.StoreExtends`. It is reflexive and transitive.
* `CoreEngine.Lawful E`: parked threads (returned, callout, stuck) take no internal step;
  `Internal`, `prepare?`, `allocHost` and `memWrite?` extend the store; `allocHost` allocates a
  fresh address typed `ofFlatType ft`, leaves every other function type unchanged, and its
  invocation with matching arity is immediately a callout; `asFunc? (ofFunc a) = some a`;
  `ExternSub` is reflexive and transitive;
  `memWrite?` preserves memory sizes and address types and satisfies read-after-write and frame
  laws; `memRead?`/`memWrite?` succeed exactly in bounds; `flatType? (ofFlatType ft) = some ft`.
  A running thread may step but is not required to progress.
* `CoreEngine.ResumeLawful E`: resuming a callout thread yields a running or returned thread. This
  is kept OUT of `Lawful` (see below).
* `CoreEngine.Steps`/`CoreEngine.Diverges`: reflexive-transitive closure and infinite traces of
  `Internal` (reusing `Silmaril.InfiniteTrace`, as V1 and Lime1 do). Finite stuckness is not
  divergence.
* `CoreEngine.Exec E`: an executable, sound stepper `step?`, the derived fuel loop `runCore`,
  and completeness side structures `ExecComplete` (progress) and `ExecDeterministic`
  (`step?` computes every internal step; expected for the Mock engine only).

Why `ResumeLawful` is separate: for Lime1, resuming plugs the host result into the evaluation
context; with an ill-typed result (or ill-typed surrounding code) the resumed thread can be `stuck`,
and V1/Lime1 have no progress theorem. The law is therefore only available for engines that satisfy
it unconditionally (e.g. a Mock engine).

No import-typing law is imposed on `prepare?`: Lime1's `prepare?` does not check imports
(`ImportsMatch` is a separate side condition of `Lime1.Execution.Instantiation`), so the
component instantiator must establish import matching itself.

The file ends with a private toy engine (store = list of host functions, no memories, no
internal steps) showing that `CoreEngine`, `Lawful`, `ResumeLawful`, `Exec`, and
`ExecDeterministic` are all instantiable.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine

namespace CoreEngine

variable (E : CoreEngine)

/-- Store extension: everything the component runtime has observed about a store persists.
Function types, memory and table address types, and the callout status of every thread (in
particular of threads parked inside wasm frames, which the scheduler resumes later at an
extended store) are kept; memory sizes may only grow. -/
structure Extends {H : Type} (s s' : E.Store H) : Prop where
  funcType : ∀ a ft, E.funcType? s a = some ft → E.funcType? s' a = some ft
  memAddrType : ∀ m t, E.memAddrType? s m = some t → E.memAddrType? s' m = some t
  memSize : ∀ m n, E.memSize? s m = some n → ∃ n', E.memSize? s' m = some n' ∧ n ≤ n'
  tableAddrType : ∀ t at_, E.tableAddrType? s t = some at_ → E.tableAddrType? s' t = some at_
  callout : ∀ (t : E.Thread H) h (args : List FlatValue),
    E.status s t = .callout h args → E.status s' t = .callout h args

variable {E}

theorem Extends.refl {H : Type} (s : E.Store H) : E.Extends s s :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ n h => ⟨n, h, Nat.le_refl n⟩, fun _ _ h => h,
    fun _ _ _ h => h⟩

theorem Extends.trans {H : Type} {s₁ s₂ s₃ : E.Store H} (h₁ : E.Extends s₁ s₂)
    (h₂ : E.Extends s₂ s₃) : E.Extends s₁ s₃ where
  funcType a ft h := h₂.funcType a ft (h₁.funcType a ft h)
  memAddrType m t h := h₂.memAddrType m t (h₁.memAddrType m t h)
  memSize m n h := by
    obtain ⟨n₂, e₂, le₂⟩ := h₁.memSize m n h
    obtain ⟨n₃, e₃, le₃⟩ := h₂.memSize m n₂ e₂
    exact ⟨n₃, e₃, Nat.le_trans le₂ le₃⟩
  tableAddrType t at_ h := h₂.tableAddrType t at_ (h₁.tableAddrType t at_ h)
  callout t h args e := h₂.callout t h args (h₁.callout t h args e)

/-- Finite host-free runs. -/
abbrev Steps (E : CoreEngine) {H : Type} : E.Config H → E.Config H → Prop :=
  Relation.ReflTransGen (@CoreEngine.Internal E H)

/-- An infinite host-free trace; finite stuckness is not divergence. -/
def Diverges (E : CoreEngine) {H : Type} (c : E.Config H) : Prop :=
  InfiniteTrace (@CoreEngine.Internal E H) c

/-- The laws the component runtime relies on. Assumed engines (Core 3.0)
state them as hypotheses; concrete engines prove them. -/
class Lawful (E : CoreEngine) : Prop where
  flatType?_ofFlatType : ∀ ft, E.flatType? (E.ofFlatType ft) = some ft
  /-- A returned thread takes no internal step. -/
  returned_no_step : ∀ {H : Type} {s : E.Store H} {t r c'},
    E.status s t = .returned r → ¬ E.Internal (s, t) c'
  /-- A thread parked on a callout takes no internal step. -/
  callout_no_step : ∀ {H : Type} {s : E.Store H} {t h args c'},
    E.status s t = .callout h args → ¬ E.Internal (s, t) c'
  /-- A stuck thread takes no internal step. -/
  stuck_no_step : ∀ {H : Type} {s : E.Store H} {t c'},
    E.status s t = .stuck → ¬ E.Internal (s, t) c'
  /-- `ExternSub` is a preorder. -/
  externSub_refl : ∀ τ, E.ExternSub τ τ
  externSub_trans : ∀ {τ₁ τ₂ τ₃}, E.ExternSub τ₁ τ₂ → E.ExternSub τ₂ τ₃ → E.ExternSub τ₁ τ₃
  asFunc?_ofFunc : ∀ a, E.asFunc? (E.ofFunc a) = some a
  internal_extends : ∀ {H : Type} {s s' : E.Store H} {t t'},
    E.Internal (s, t) (s', t') → E.Extends s s'
  /-- Core instantiation (allocation and segment initialization) extends the store. -/
  prepare_extends : ∀ {H : Type} {s s' : E.Store H} {m imps i st},
    E.prepare? s m imps = some (s', i, st) → E.Extends s s'
  allocHost_extends : ∀ {H : Type} {s s' : E.Store H} {ft h a},
    E.allocHost s ft h = (s', a) → E.Extends s s'
  /-- The allocated address was not in use. -/
  allocHost_fresh : ∀ {H : Type} {s s' : E.Store H} {ft h a},
    E.allocHost s ft h = (s', a) → E.funcType? s a = none
  /-- Frame law: `allocHost` changes no other function type. -/
  allocHost_frame : ∀ {H : Type} {s s' : E.Store H} {ft h a b},
    E.allocHost s ft h = (s', a) → b ≠ a → E.funcType? s' b = E.funcType? s b
  allocHost_funcType : ∀ {H : Type} {s s' : E.Store H} {ft h a},
    E.allocHost s ft h = (s', a) → E.funcType? s' a = some (E.ofFlatType ft)
  /-- Invoking an allocated host function with matching arity is immediately a callout. -/
  allocHost_callout : ∀ {H : Type} {s s' : E.Store H} {ft h a} {args : List FlatValue},
    E.allocHost s ft h = (s', a) → args.length = ft.params.length →
      E.status s' (E.invoke a args) = .callout h args
  memWrite_extends : ∀ {H : Type} {s s' : E.Store H} {m st bs},
    E.memWrite? s m st bs = some s' → E.Extends s s'
  memWrite_memSize : ∀ {H : Type} {s s' : E.Store H} {m st bs},
    E.memWrite? s m st bs = some s' → ∀ m', E.memSize? s' m' = E.memSize? s m'
  memWrite_memAddrType : ∀ {H : Type} {s s' : E.Store H} {m st bs},
    E.memWrite? s m st bs = some s' → ∀ m', E.memAddrType? s' m' = E.memAddrType? s m'
  /-- Read after write. -/
  memWrite_read : ∀ {H : Type} {s s' : E.Store H} {m st bs},
    E.memWrite? s m st bs = some s' → E.memRead? s' m st bs.size = some bs
  /-- Frame law: reads of another memory or a disjoint range are unchanged. -/
  memWrite_read_other : ∀ {H : Type} {s s' : E.Store H} {m st bs m' st' len},
    E.memWrite? s m st bs = some s' → (m' ≠ m ∨ st' + len ≤ st ∨ st + bs.size ≤ st') →
      E.memRead? s' m' st' len = E.memRead? s m' st' len
  memRead_isSome_iff : ∀ {H : Type} {s : E.Store H} {m st len},
    (E.memRead? s m st len).isSome ↔ ∃ n, E.memSize? s m = some n ∧ st + len ≤ n
  memRead_size : ∀ {H : Type} {s : E.Store H} {m st len bs},
    E.memRead? s m st len = some bs → bs.size = len
  memWrite_isSome_iff : ∀ {H : Type} {s : E.Store H} {m st bs},
    (E.memWrite? s m st bs).isSome ↔ ∃ n, E.memSize? s m = some n ∧ st + bs.size ≤ n
  memAddrType_isSome_iff : ∀ {H : Type} {s : E.Store H} {m},
    (E.memAddrType? s m).isSome ↔ (E.memSize? s m).isSome

/-- Resumption progress: resuming a callout thread in an extended store yields a running or
returned thread. Not part of `Lawful`; see the module docstring. -/
class ResumeLawful (E : CoreEngine) : Prop where
  resume_unparked : ∀ {H : Type} {s s' : E.Store H} {t h args r},
    E.status s t = .callout h args → E.Extends s s' →
      E.status s' (E.resume s' t r) = .running ∨
        ∃ r', E.status s' (E.resume s' t r) = .returned r'

section Lawful

variable [L : E.Lawful]

/-- Only running threads step. -/
theorem status_running_of_internal {H : Type} {s : E.Store H} {t c'}
    (h : E.Internal (s, t) c') : E.status s t = .running := by
  cases e : E.status s t with
  | running => rfl
  | returned r => exact absurd h (L.returned_no_step e)
  | callout h' args => exact absurd h (L.callout_no_step e)
  | stuck => exact absurd h (L.stuck_no_step e)

theorem internal_extends' {H : Type} {c c' : E.Config H} (h : E.Internal c c') :
    E.Extends c.1 c'.1 := by
  obtain ⟨s, t⟩ := c
  obtain ⟨s', t'⟩ := c'
  exact L.internal_extends h

theorem steps_extends {H : Type} {c c' : E.Config H} (h : E.Steps c c') :
    E.Extends c.1 c'.1 := by
  induction h with
  | refl => exact Extends.refl _
  | tail _ step ih => exact ih.trans (internal_extends' step)

/-- A thread that is not running has only the trivial run. -/
theorem steps_parked {H : Type} {s : E.Store H} {t c'} (hs : E.status s t ≠ .running)
    (h : E.Steps (s, t) c') : c' = (s, t) := by
  rcases Relation.ReflTransGen.cases_head h with e | ⟨c, step, _⟩
  · exact e.symm
  · exact absurd (status_running_of_internal step) hs

/-- A diverging configuration is running. -/
theorem Diverges.running {H : Type} {s : E.Store H} {t} (h : E.Diverges (s, t)) :
    E.status s t = .running := by
  obtain ⟨_, step, _⟩ := h.unfold
  exact status_running_of_internal step

/-- An allocated host function stays a callout target in every later extension. -/
theorem allocHost_callout_of_extends {H : Type} {s s' s'' : E.Store H} {ft h a}
    {args : List FlatValue} (ha : E.allocHost s ft h = (s', a)) (hx : E.Extends s' s'')
    (hl : args.length = ft.params.length) : E.status s'' (E.invoke a args) = .callout h args :=
  hx.callout _ h args (L.allocHost_callout ha hl)

/-- An allocated host function keeps its flat type in every later extension. -/
theorem allocHost_flatType_of_extends {H : Type} {s s' s'' : E.Store H} {ft h a}
    (ha : E.allocHost s ft h = (s', a)) (hx : E.Extends s' s'') :
    (E.funcType? s'' a).bind E.flatType? = some ft := by
  rw [hx.funcType a _ (L.allocHost_funcType ha)]
  exact L.flatType?_ofFlatType ft

end Lawful

/-- An executable host-free stepper, sound for `Internal`. It returns `none` on parked or stuck
configurations (for lawful engines this follows from soundness, `step?_parked`). -/
structure Exec (E : CoreEngine) where
  step? : {H : Type} → E.Config H → Option (E.Config H)
  step?_sound : ∀ {H : Type} {c c' : E.Config H}, step? c = some c' → E.Internal c c'

/-- Completeness of an executable stepper: whenever an internal step exists, `step?` finds one
(not necessarily the same, as internal steps may be nondeterministic). -/
structure ExecComplete {E : CoreEngine} (X : E.Exec) : Prop where
  progress : ∀ {H : Type} {c c' : E.Config H}, E.Internal c c' → (X.step? c).isSome

/-- Full determinism of an executable stepper: every internal step is the one `step?`
computes. Expected for the Mock engine only. -/
structure ExecDeterministic {E : CoreEngine} (X : E.Exec) : Prop extends ExecComplete X where
  deterministic : ∀ {H : Type} {c c' : E.Config H}, E.Internal c c' → X.step? c = some c'

/-- `deterministic` alone gives `ExecDeterministic`. -/
theorem ExecDeterministic.of_deterministic {X : E.Exec}
    (d : ∀ {H : Type} {c c' : E.Config H}, E.Internal c c' → X.step? c = some c') :
    ExecDeterministic X where
  progress h := by rw [d h]; rfl
  deterministic := d

namespace Exec

variable (X : E.Exec)

/-- The fuel loop: step while `step?` succeeds and fuel remains. The flag is `true` iff the
final configuration has no executable step (`returned`, `callout` or `stuck` for lawful
engines); `false` means fuel ran out, which is not divergence. Both directions are proved
(`runCore_stopped`, `runCore_exhausted`). -/
def runCore {H : Type} : Nat → E.Config H → E.Config H × Bool
  | 0, c => (c, (X.step? c).isNone)
  | n + 1, c =>
    match X.step? c with
    | none => (c, true)
    | some c' => runCore n c'

theorem runCore_steps {H : Type} (n : Nat) (c : E.Config H) : E.Steps c (X.runCore n c).1 := by
  induction n generalizing c with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [runCore]
    split
    · exact Relation.ReflTransGen.refl
    · rename_i c' e
      exact Relation.ReflTransGen.head (X.step?_sound e) (ih c')

theorem runCore_stopped {H : Type} (n : Nat) (c : E.Config H)
    (h : (X.runCore n c).2 = true) : X.step? (X.runCore n c).1 = none := by
  induction n generalizing c with
  | zero => simpa [runCore] using h
  | succ n ih =>
    cases e : X.step? c with
    | none => simp [runCore, e]
    | some c' => simpa [runCore, e] using ih c' (by simpa [runCore, e] using h)

theorem runCore_exhausted {H : Type} (n : Nat) (c : E.Config H)
    (h : (X.runCore n c).2 = false) : (X.step? (X.runCore n c).1).isSome := by
  induction n generalizing c with
  | zero => simpa [runCore] using h
  | succ n ih =>
    cases e : X.step? c with
    | none => simp [runCore, e] at h
    | some c' => simpa [runCore, e] using ih c' (by simpa [runCore, e] using h)

/-- With a complete stepper, a stopped run ends in a configuration with no internal step. -/
theorem runCore_final {X : E.Exec} (hc : ExecComplete X) {H : Type} (n : Nat)
    (c : E.Config H) (h : (X.runCore n c).2 = true) :
    ∀ c', ¬ E.Internal (X.runCore n c).1 c' := by
  intro c' step
  have := hc.progress step
  rw [X.runCore_stopped n c h] at this
  exact Bool.false_ne_true this

/-- For lawful engines, `step?` is `none` on threads that are not running. -/
theorem step?_parked [L : E.Lawful] {H : Type} {s : E.Store H} {t}
    (hs : E.status s t ≠ .running) : X.step? (s, t) = none := by
  cases e : X.step? (s, t) with
  | none => rfl
  | some c' => exact absurd (status_running_of_internal (X.step?_sound e)) hs

end Exec

end CoreEngine

/-! ## A toy engine (instantiability check) -/

namespace Toy

private abbrev Store (H : Type) := List (V1.FuncType × H)
private abbrev Thread (_ : Type) := (Nat × List FlatValue) ⊕ CallResult

private def status {H : Type} (s : Store H) : Thread H → Status H
  | .inl (a, args) =>
    match s[a]? with
    | some (_, h) => .callout h args
    | none => .stuck
  | .inr r => .returned r

private abbrev toy : CoreEngine where
  Module := Unit
  Valid _ := True
  FuncType := V1.FuncType
  ExternType := CoreExternType
  ExternSub := CoreExternType.Sub
  ofFlatType := id
  flatType? := some
  importTypes _ := []
  exportTypes _ := []
  Store := Store
  empty _ := []
  FuncAddr := Nat
  MemAddr := Nat
  TableAddr := Nat
  GlobalAddr := Nat
  ExternVal := Nat
  asFunc? := some
  asMemory? _ := none
  asTable? _ := none
  asGlobal? _ := none
  ofFunc := id
  Inst := Unit
  exports _ := []
  externType? s a := (s[a]?).map fun p => .func p.1
  prepare? s _ _ := some (s, (), none)
  allocHost s ft h := (s ++ [(ft, h)], s.length)
  funcType? s a := (s[a]?).map (·.1)
  memAddrType? _ _ := none
  memSize? _ _ := none
  memRead? _ _ _ _ := none
  memWrite? _ _ _ _ := none
  tableAddrType? _ _ := none
  tableFunc? _ _ _ := none
  Thread := Thread
  invoke a args := .inl (a, args)
  status := status
  Internal _ _ := False
  resume _ _ r := .inr r

private theorem getElem?_append_of_some {α : Type} {l : List α} {a : Nat} {x : α}
    (l' : List α) (h : l[a]? = some x) : (l ++ l')[a]? = some x := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

private theorem append_extends {H : Type} (s : Store H) (l : List (V1.FuncType × H)) :
    toy.Extends s (s ++ l) where
  funcType a ft h := by
    change ((s ++ l)[a]?).map (·.1) = some ft
    change (s[a]?).map (·.1) = some ft at h
    cases e : s[a]? with
    | none => simp [e] at h
    | some x => rw [getElem?_append_of_some l e]; simpa [e] using h
  memAddrType _ _ h := nomatch h
  memSize _ _ h := nomatch h
  tableAddrType _ _ h := nomatch h
  callout t h args e := by
    change status (s ++ l) t = .callout h args
    change status s t = .callout h args at e
    rcases t with ⟨a, args'⟩ | r
    · cases hs : s[a]? with
      | none => simp [status, hs] at e
      | some x => simpa [status, hs, getElem?_append_of_some l hs] using e
    · simp [status] at e

private instance : toy.Lawful where
  flatType?_ofFlatType _ := rfl
  returned_no_step _ h := h
  callout_no_step _ h := h
  stuck_no_step _ h := h
  externSub_refl := CoreExternType.Sub.refl
  externSub_trans := CoreExternType.Sub.trans
  asFunc?_ofFunc _ := rfl
  internal_extends h := nomatch h
  prepare_extends h := by
    cases h
    exact CoreEngine.Extends.refl _
  allocHost_extends h := by
    cases h
    exact append_extends _ _
  allocHost_fresh := by
    intro _ s _ _ _ _ e
    cases e
    change (s[s.length]?).map (·.1) = none
    simp
  allocHost_frame := by
    intro _ s s' ft h a b e hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e.symm
    change ((s ++ [(ft, h)])[b]?).map (·.1) = (s[b]?).map (·.1)
    rw [List.getElem?_append]
    split
    · rfl
    · rename_i hlt
      have hb' : @Ne Nat b s.length := hb
      have : b - s.length ≠ 0 :=
        Nat.sub_ne_zero_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hb'))
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hlt), this]
  allocHost_funcType := by
    intro _ s _ ft h _ e
    cases e
    change ((s ++ [(ft, h)])[s.length]?).map (·.1) = some ft
    simp
  allocHost_callout := by
    intro _ s _ ft h _ args e _
    cases e
    change status (s ++ [(ft, h)]) (.inl (s.length, args)) = _
    simp [status]
  memWrite_extends h := nomatch h
  memWrite_memSize h := nomatch h
  memWrite_memAddrType h := nomatch h
  memWrite_read h := nomatch h
  memWrite_read_other h := nomatch h
  memRead_isSome_iff := by
    intros
    change (none : Option ByteArray).isSome = true ↔ ∃ n, (none : Option Nat) = some n ∧ _
    simp
  memRead_size h := nomatch h
  memWrite_isSome_iff := by
    intros
    change (none : Option (Store _)).isSome = true ↔ ∃ n, (none : Option Nat) = some n ∧ _
    simp
  memAddrType_isSome_iff := Iff.rfl

private instance : toy.ResumeLawful where
  resume_unparked _ _ := Or.inr ⟨_, rfl⟩

private noncomputable def toyExec : toy.Exec where
  step? _ := none
  step?_sound h := nomatch h

private theorem toyExec_deterministic : CoreEngine.ExecDeterministic toyExec :=
  .of_deterministic fun h => nomatch h

/-- A host function allocated in the empty store is a callout target. -/
example : toy.status (toy.allocHost (toy.empty Nat) ⟨[], []⟩ 7).1
    (toy.invoke (toy.allocHost (toy.empty Nat) ⟨[], []⟩ 7).2 []) = .callout 7 [] := rfl

/-- Resuming it returns; the fuel loop stops immediately. -/
example : toyExec.runCore 3 ((toy.empty Nat), toy.resume (toy.empty Nat)
    (toy.invoke (0 : Nat) []) (.values [])) =
      ((([], Sum.inr (CallResult.values [])) : toy.Config Nat), true) :=
  rfl

end Toy

end Silmaril.Wasm.Component.Engine
