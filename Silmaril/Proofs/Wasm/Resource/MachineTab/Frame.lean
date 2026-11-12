module

public import Silmaril.Wasm.Resource.MachineTab.Defs
public import Silmaril.Wasm.Resource.Table.Thms
public import Silmaril.Proofs.Wasm.Resource.CompTable.Basic
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# Handle tables along whole machine runs: the frame argument

* `TabMove.refl`, `TabMove.trans`, `TabMove.of_insts` (an update that leaves the instance
  arena unchanged is a table move), `tabMove_modify_frame` (an instance update that keeps the
  handle table), `tabMove_addHandle`, `tabMove_removeHandle` (the table operations of
  `Canon.handlesAdd`/`handlesRemove`, successful or not), `tabMove_allocInst`;
* `tabFrom_of_move`: a table move preserves every `TabFrom j s₀`, the bridge to the `P.Inv`
  lemmas of the reference programs;
* `TabProg.cont`, `TabProg.modify`: the continuations of a table-moving program are
  table-moving, and its `modify` updates are table moves;
* the host-frame programs `invokeProg`, `tickProg`, `cancelProg`, `runProg`;
* **`step_tab`**: every machine step from a table-moving configuration, with a table-moving
  dispatcher (and a table-moving program if the step is `HostEvent.run p`), reaches a
  table-moving configuration through a table move; **`steps_tab`**: the same for runs.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {σ : Type} {α : Type} {j : InstId}

/-! ## Silmaril.Wasm.Component.Runtime.Table moves -/

theorem TabMove.refl (s : CStore E) : TabMove j s s := ⟨[], .nil _⟩

theorem TabMove.trans {s₁ s₂ s₃ : CStore E} (h₁ : TabMove j s₁ s₂) (h₂ : TabMove j s₂ s₃) :
    TabMove j s₁ s₃ := by
  obtain ⟨e₁, h₁⟩ := h₁
  obtain ⟨e₂, h₂⟩ := h₂
  exact ⟨e₁ ++ e₂, steps_append h₁ h₂⟩

theorem vtab_of_insts {s s' : CStore E} (h : s'.insts = s.insts) : vtab s' j = vtab s j := by
  simp [vtab, handles?, CStore.inst?, ArenaField.get?, ArenaField.insts, h]

theorem TabMove.of_insts {s s' : CStore E} (h : s'.insts = s.insts) : TabMove j s s' :=
  ⟨[], vtab_of_insts h ▸ .nil _⟩

theorem vtab_modify_self (s : CStore E) (i : InstId) (f : InstState → InstState) :
    vtab (ArenaField.insts.modify s i f) i =
      ((s.inst? i).map fun st => (f st).handles).getD Table.empty := by
  rw [vtab, handles?_modify_self]

theorem vtab_modify_ne (s : CStore E) {i : InstId} (f : InstState → InstState) (h : j ≠ i) :
    vtab (ArenaField.insts.modify s i f) j = vtab s j := by
  rw [vtab, vtab, handles?_modify_ne _ _ h]

/-- An instance update that moves the instance's table by a successful history. -/
theorem tabMove_modify (s : CStore E) (i : InstId) {f : InstState → InstState}
    (hf : ∀ st, ∃ evs, Table.Steps st.handles evs (f st).handles) :
    TabMove j s (ArenaField.insts.modify s i f) := by
  by_cases hj : j = i
  · subst hj
    cases hs : s.inst? j with
    | none =>
      have e : vtab (ArenaField.insts.modify s j f) j = vtab s j := by
        rw [vtab_modify_self, hs]; simp [vtab, handles?, hs]
      exact ⟨[], e ▸ .nil _⟩
    | some st =>
      obtain ⟨evs, h⟩ := hf st
      have e₁ : vtab (ArenaField.insts.modify s j f) j = (f st).handles := by
        rw [vtab_modify_self, hs]; rfl
      have e₀ : vtab s j = st.handles := by simp [vtab, handles?, hs]
      exact ⟨evs, e₀ ▸ e₁ ▸ h⟩
  · exact ⟨[], (vtab_modify_ne s f hj).symm ▸ .nil _⟩

/-- An instance update that keeps every handle table is a table move. -/
theorem tabMove_modify_frame (s : CStore E) (i : InstId) {g : InstState → InstState}
    (hg : ∀ st, (g st).handles = st.handles) : TabMove j s (ArenaField.insts.modify s i g) :=
  tabMove_modify s i fun st => ⟨[], (hg st).symm ▸ .nil _⟩

theorem steps_addHandle (e : HandleEntry) (st : InstState) :
    ∃ evs, Table.Steps st.handles evs (InstState.addHandle e st).handles := by
  cases ha : st.addHandle? e with
  | none =>
    have hn : InstState.addHandle e st = st := by simp [InstState.addHandle, ha]
    exact ⟨[], by rw [hn]; exact .nil _⟩
  | some p =>
    obtain ⟨hadd, hst⟩ := addHandle?_tab ha
    exact ⟨[.added p.1 e], hst ▸ steps_single (by simp [Table.Event.op, Table.step?, hadd])⟩

theorem steps_removeHandle (k : ℕ) (st : InstState) :
    ∃ evs, Table.Steps st.handles evs (InstState.removeHandle k st).handles := by
  cases ha : st.removeHandle? k with
  | none =>
    have hn : InstState.removeHandle k st = st := by simp [InstState.removeHandle, ha]
    exact ⟨[], by rw [hn]; exact .nil _⟩
  | some p =>
    obtain ⟨hrem, hst⟩ := removeHandle?_tab ha
    exact ⟨[.removed k p.1], hst ▸ steps_single (by simp [Table.Event.op, Table.step?, hrem])⟩

theorem tabMove_addHandle (s : CStore E) (i : InstId) (e : HandleEntry) :
    TabMove j s (ArenaField.insts.modify s i (InstState.addHandle e)) :=
  tabMove_modify s i (steps_addHandle e)

theorem tabMove_removeHandle (s : CStore E) (i : InstId) (k : ℕ) :
    TabMove j s (ArenaField.insts.modify s i (InstState.removeHandle k)) :=
  tabMove_modify s i (steps_removeHandle k)

/-- Allocating an instance with an empty handle table is a table move. -/
theorem tabMove_allocInst (s : CStore E) {x : InstState} (hx : x.handles = Table.empty) :
    TabMove j s (ArenaOps.allocSt ArenaField.insts x s) := by
  refine ⟨[], ?_⟩
  have ha := ArenaField.get?_alloc (E := E) ArenaField.insts s x j
  have e : vtab (ArenaOps.allocSt ArenaField.insts x s) j = vtab s j := by
    by_cases h : (ArenaField.insts (E := E)).idx j = ArenaField.insts.size s
    · have hn : ArenaField.insts.get? s j = none := by
        have := ArenaField.get?_isSome_iff ArenaField.insts s j
        cases hg : ArenaField.insts.get? s j <;> simp_all
      simp only [h, ↓reduceIte] at ha
      simp [vtab, handles?, CStore.inst?, ArenaOps.allocSt, ha, hn, hx]
    · simp only [h, ↓reduceIte] at ha
      simp [vtab, handles?, CStore.inst?, ArenaOps.allocSt, ha]
  exact e ▸ .nil _

/-- A table move preserves every `TabFrom j s₀`. -/
theorem tabFrom_of_move {s₀ : CStore E} {g : CStore E → CStore E} (hg : ∀ s, TabMove j s (g s)) :
    ∀ s, TabFrom j s₀ s → TabFrom j s₀ (g s) :=
  fun s hs => TabMove.trans hs (hg s)

/-- An update that leaves the instance arena unchanged preserves every `TabFrom j s₀`. -/
theorem tabFrom_of_insts {s₀ : CStore E} {g : CStore E → CStore E}
    (hg : ∀ s, (g s).insts = s.insts) : ∀ s, TabFrom j s₀ s → TabFrom j s₀ (g s) :=
  tabFrom_of_move fun s => TabMove.of_insts (hg s)

/-! ## Silmaril.Wasm.Component.Runtime.Table-moving programs -/

theorem TabProg.cont {o : (Eff E σ).Op} {k : (Eff E σ).Resp o → P E σ α}
    (h : TabProg j (.op (S := Eff E σ) o k)) (r : (Eff E σ).Resp o) : TabProg j (k r) :=
  fun s₀ => (Prog.every_op_iff.1 (h s₀)).2 r

theorem TabProg.modify {f : CStore E → CStore E} {k : Unit → P E σ α}
    (h : TabProg j (.op (S := Eff E σ) (.modify f) k)) (s : CStore E) : TabMove j s (f s) :=
  (Prog.every_op_iff.1 (h s)).1 s (TabMove.refl s)

theorem TabProg.bind {p : P E σ α} {β : Type} {f : α → P E σ β} (hp : TabProg j p)
    (hf : ∀ a, TabProg j (f a)) : TabProg j (p >>= f) :=
  fun s₀ => P.Inv.bind (hp s₀) fun a => hf a s₀

theorem tabProg_invokeProg (c : CallId) (f : FuncId) (args : List Silmaril.Wasm.Component.Value.Val) :
    TabProg j (StepDefs.invokeProg (E := E) (σ := σ) c f args) := fun _ =>
  P.Inv.bind (P.Inv.allocObj _ _ (tabFrom_of_insts fun _ => rfl)) fun _ =>
    P.Inv.bind (P.Inv.modifyStore (tabFrom_of_insts fun _ => rfl)) fun _ =>
      P.Inv.bind (P.Inv.callRet _) fun _ =>
        P.Inv.bind (P.Inv.modifyStore (tabFrom_of_insts fun _ => rfl)) fun _ => P.Inv.pure _

theorem tabProg_tickProg (hr : HostReady σ) : TabProg j (StepDefs.tickProg (E := E) hr) := by
  intro s₀
  unfold StepDefs.tickProg
  refine P.Inv.bind (P.Inv.modifyStore (tabFrom_of_insts fun _ => rfl)) fun _ => ?_
  refine P.Inv.bind P.Inv.getStore fun s => P.Inv.bind P.Inv.hostGet fun h => ?_
  have hl : P.Inv (TabFrom j s₀) (modifyStore StepDefs.leaveHostSt >>= fun _ =>
      (pure Ret.unit : P E σ (Ret E))) :=
    P.Inv.bind (P.Inv.modifyStore (tabFrom_of_insts fun _ => rfl)) fun _ => P.Inv.pure _
  dsimp only
  split
  · exact hl
  · exact P.Inv.bind (P.Inv.pickTick _ _) fun t =>
      P.Inv.bind (Thread.resume_inv t (tabFrom_of_insts fun _ => rfl)) fun _ => hl

theorem tabProg_cancelProg (r : CancelRef) : TabProg j (StepDefs.cancelProg (E := E) (σ := σ) r) :=
  fun _ => P.Inv.bind (P.Inv.modifyStore (tabFrom_of_insts fun _ => rfl)) fun _ =>
    P.Inv.bind (P.Inv.callRet _) fun _ =>
      P.Inv.bind (P.Inv.modifyStore (tabFrom_of_insts fun _ => rfl)) fun _ => P.Inv.pure _

theorem tabProg_runProg {p : P E σ (Ret E)} (hp : TabProg j p) : TabProg j (StepDefs.runProg p) :=
  fun s₀ => P.Inv.bind (hp s₀) fun _ => P.Inv.pure _

end Silmaril.Wasm.Resource
