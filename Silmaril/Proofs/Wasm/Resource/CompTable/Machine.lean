module

public import Silmaril.Proofs.Wasm.Resource.CompTable.Basic
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# The resource built-ins on the reference machine: proofs

The store-only runs `SRun` of `Silmaril.Proofs.Wasm.Resource.CompTable.Basic` are machine runs, and
every machine run of a store-only program is one of them.

* `storeProg_resourceNewCore`, `storeProg_resourceRepCore`, `storeProg_resourceDropCore`,
  `storeProg_resScript`: the cores of the resource built-ins issue only `get`, `modify` and
  `trap`.
* `step_get_inv`, `step_modify_inv`, `step_trap_inv`: the only machine step of a configuration
  whose focus program issues `get`, `modify` or `trap` is the corresponding rule; `steps_dead`:
  a trapped configuration (empty control chain, store locked down) takes no step.
* `SRun.steps`: a store-only run is a run of `tau` steps of the machine, in any context.
* **`steps_storeProg`**: every machine run from a configuration whose focus is `p >>= f`, with
  `p` store-only, either stops inside `p` (at a residual `q` whose completions are completions
  of `p`), or trapped (the machine is then dead), or completed `p` through a store-only run
  `SRun p s a s₁` and continued with `f a`.
* **`machine_resScript`**, **`machine_resScript_accepts`**: the instance of `steps_storeProg`
  for scripts of resource built-in cores: every machine run that completes the script makes
  the handle table of every instance follow a successful table history whose handle events are
  the calls' events, accepted by `handleProto ℕ r` (both orientations) from an empty table.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {α β : Type}

/-! ## The cores are store-only programs -/

theorem storeProg_pure (a : α) : StoreProg (Pure.pure a : P E σ α) := Prog.Every.pure a

theorem storeProg_bind {p : P E σ α} {f : α → P E σ β} (hp : StoreProg p)
    (hf : ∀ a, StoreProg (f a)) : StoreProg (p >>= f) := Prog.Every.bind hp hf

theorem storeProg_getStore : StoreProg (getStore : P E σ (CStore E)) :=
  Prog.Every.lift (S := Eff E σ) trivial

theorem storeProg_modifyStore (f : CStore E → CStore E) : StoreProg (modifyStore f : P E σ Unit) :=
  Prog.Every.lift (S := Eff E σ) trivial

theorem storeProg_trap (r : TrapReason) : StoreProg (trap r : P E σ α) :=
  Prog.Every.op (S := Eff E σ) trivial fun e => nomatch e

theorem storeProg_internal (msg : String) : StoreProg (internal msg : P E σ α) := storeProg_trap _

theorem storeProg_trapIf (c : Bool) (r : TrapReason) : StoreProg (trapIf c r : P E σ Unit) := by
  cases c
  · exact storeProg_pure _
  · exact storeProg_trap _

theorem storeProg_getObj {Id : Type} (F : ArenaField E Id α) (i : Id) :
    StoreProg (getObj F i : P E σ α) := by
  refine storeProg_bind storeProg_getStore fun s => ?_
  cases F.get? s i
  · exact storeProg_internal _
  · exact storeProg_pure _

theorem storeProg_allocObj {Id : Type} (F : ArenaField E Id α) (x : α) :
    StoreProg (allocObj F x : P E σ Id) :=
  storeProg_bind storeProg_getStore fun _ =>
    storeProg_bind (storeProg_modifyStore _) fun _ => storeProg_pure _

theorem storeProg_handlesAdd (inst : InstId) (e : HandleEntry) :
    StoreProg (handlesAdd inst e : P E σ ℕ) := by
  refine storeProg_bind (storeProg_getObj _ _) fun st => ?_
  cases st.addHandle? e with
  | none => exact storeProg_trap _
  | some p => exact storeProg_bind (storeProg_modifyStore _) fun _ => storeProg_pure _

theorem storeProg_handlesGet (inst : InstId) (i : ℕ) :
    StoreProg (handlesGet inst i : P E σ HandleEntry) := by
  refine storeProg_bind (storeProg_getObj _ _) fun st => ?_
  cases st.handles.get? i
  · exact storeProg_trap _
  · exact storeProg_pure _

theorem storeProg_handlesRemove (inst : InstId) (i : ℕ) :
    StoreProg (handlesRemove inst i : P E σ HandleEntry) := by
  refine storeProg_bind (storeProg_getObj _ _) fun st => ?_
  cases st.removeHandle? i with
  | none => exact storeProg_trap _
  | some p => exact storeProg_bind (storeProg_modifyStore _) fun _ => storeProg_pure _

theorem storeProg_expectResource (e : HandleEntry) :
    StoreProg (expectResource e : P E σ HandleObjId) := by
  cases e
  · exact storeProg_pure _
  all_goals exact storeProg_trap _

theorem storeProg_resourceNewCore (lim : Silmaril.Wasm.Component.Limits) (inst : InstId) (rt : RtId) (rep : ℕ) :
    StoreProg (resourceNewCore lim inst rt rep : P E σ ℕ) :=
  storeProg_bind (storeProg_allocObj _ _) fun _ => storeProg_handlesAdd _ _

theorem storeProg_resourceRepCore (lim : Silmaril.Wasm.Component.Limits) (inst : InstId) (rt : RtId) (i : ℕ) :
    StoreProg (resourceRepCore lim inst rt i : P E σ ℕ) :=
  storeProg_bind (storeProg_handlesGet _ _) fun _ =>
    storeProg_bind (storeProg_expectResource _) fun _ =>
      storeProg_bind (storeProg_getObj _ _) fun _ =>
        storeProg_bind (storeProg_trapIf _ _) fun _ => storeProg_pure _

theorem storeProg_dropHandleTail (rt : RtId) (rh : ResourceHandle) :
    StoreProg (dropHandleTail rt rh : P E σ (Option (DtorRequest E))) := by
  unfold dropHandleTail
  cases rh.own
  · cases rh.scope with
    | none => exact storeProg_internal _
    | some t => exact storeProg_bind (storeProg_modifyStore _) fun _ => storeProg_pure _
  · exact storeProg_bind (storeProg_getObj _ _) fun _ => storeProg_pure _

theorem storeProg_resourceDropCore (lim : Silmaril.Wasm.Component.Limits) (inst : InstId) (rt : RtId) (i : ℕ) :
    StoreProg (resourceDropCore lim inst rt i : P E σ (Option (DtorRequest E))) :=
  storeProg_bind (storeProg_handlesRemove _ _) fun _ =>
    storeProg_bind (storeProg_expectResource _) fun _ =>
      storeProg_bind (storeProg_getObj _ _) fun _ =>
        storeProg_bind (storeProg_trapIf _ _) fun _ =>
          storeProg_bind (storeProg_trapIf _ _) fun _ => storeProg_dropHandleTail _ _

theorem storeProg_resCall (lim : Silmaril.Wasm.Component.Limits) (c : ResCall) : StoreProg (c.prog lim : P E σ ℕ) := by
  cases c with
  | new => exact storeProg_resourceNewCore lim ..
  | rep => exact storeProg_resourceRepCore lim ..
  | drop => exact storeProg_bind (storeProg_resourceDropCore lim ..) fun _ => storeProg_pure _

theorem storeProg_resScript (lim : Silmaril.Wasm.Component.Limits) (cs : List ResCall) :
    StoreProg (resScript lim cs : P E σ (List ℕ)) :=
  Prog.Every.mapM fun c _ => storeProg_resCall lim c

/-! ## Store-only programs on the machine -/

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

theorem SRun.get {k : CStore E → P E σ α} {s s' : CStore E} {a : α} (h : SRun (k s) s a s') :
    SRun (.op (S := Eff E σ) .get k) s a s' :=
  Prog.Eval.op (S := Eff E σ) (o := Op.get) s ⟨rfl, rfl⟩ h

theorem SRun.modify {f : CStore E → CStore E} {k : Unit → P E σ α} {s s' : CStore E} {a : α}
    (h : SRun (k ()) (f s) a s') : SRun (.op (S := Eff E σ) (.modify f) k) s a s' :=
  Prog.Eval.op (S := Eff E σ) (o := Op.modify f) () rfl h

theorem fault_inv_prog {m : Config E σ} {msg : String} {th : Option ThreadId}
    {q : P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog q, segs⟩ :: rest)
    (hb : ∀ sw k, q ≠ .op (S := Eff E σ) (.block sw) k)
    (ht : ∀ t k, q ≠ .op (S := Eff E σ) (.resumeThread t) k) (hp : ∀ r, q ≠ .pure r)
    (h : Fault m msg) : False := by
  cases h with
  | blockNoThread hc' => rw [hc] at hc'; cases hc'; exact hb _ _ rfl
  | switchMissing hc' => rw [hc] at hc'; cases hc'; exact hb _ _ rfl
  | resumeMissing hc' => rw [hc] at hc'; cases hc'; exact ht _ _ rfl
  | calloutBadRet hc' => rw [hc] at hc'; cases hc'; exact hp _ rfl

/-- Close a step case whose control-chain hypothesis contradicts `hc`. -/
local macro "ctl_absurd" hc:ident : tactic => `(tactic| first
    | (rename_i hc'; rw [$hc:ident] at hc'; cases hc' <;> fail)
    | (rename_i hc' _; rw [$hc:ident] at hc'; cases hc' <;> fail)
    | (rename_i hc' _ _; rw [$hc:ident] at hc'; cases hc' <;> fail))


theorem step_get_inv {m m' : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {k : CStore E → P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) .get k), segs⟩ :: rest)
    (h : Step prof hr dispatch m l m') :
    l = .tau ∧ m' = { m with ctl := ⟨th, .prog (k m.store), segs⟩ :: rest } := by
  cases h with
  | get hc' => rw [hc] at hc'; cases hc'; exact ⟨rfl, rfl⟩
  | fault hf => exact (fault_inv_prog hc (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ h => by cases h) hf).elim
  | hostInvoke hr' _ => rw [hr'.1] at hc; cases hc
  | hostTick hr' => rw [hr'.1] at hc; cases hc
  | hostCancel hr' _ _ => rw [hr'.1] at hc; cases hc
  | hostRun hr' => rw [hr'.1] at hc; cases hc
  | _ => ctl_absurd hc

theorem step_modify_inv {m m' : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {f : CStore E → CStore E} {k : Unit → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.modify f) k), segs⟩ :: rest)
    (h : Step prof hr dispatch m l m') :
    l = .tau ∧ m' = { m with store := f m.store, ctl := ⟨th, .prog (k ()), segs⟩ :: rest } := by
  cases h with
  | modify hc' => rw [hc] at hc'; cases hc'; exact ⟨rfl, rfl⟩
  | fault hf => exact (fault_inv_prog hc (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ h => by cases h) hf).elim
  | hostInvoke hr' _ => rw [hr'.1] at hc; cases hc
  | hostTick hr' => rw [hr'.1] at hc; cases hc
  | hostCancel hr' _ _ => rw [hr'.1] at hc; cases hc
  | hostRun hr' => rw [hr'.1] at hc; cases hc
  | _ => ctl_absurd hc

theorem step_trap_inv {m m' : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {r : TrapReason} {k : Empty → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.trap r) k), segs⟩ :: rest)
    (h : Step prof hr dispatch m l m') : m' = trapCfg m := by
  cases h with
  | trap hc' => rfl
  | fault hf => rfl
  | coreTrap => rfl
  | hostInvoke hr' _ => rw [hr'.1] at hc; cases hc
  | hostTick hr' => rw [hr'.1] at hc; cases hc
  | hostCancel hr' _ _ => rw [hr'.1] at hc; cases hc
  | hostRun hr' => rw [hr'.1] at hc; cases hc
  | _ => ctl_absurd hc

/-- A trapped configuration takes no step. -/
theorem steps_dead {m m' : Config E σ} {tr : List (Label E σ)} (hc : m.ctl = [])
    (hl : m.store.lockdown = true) (h : Steps prof hr dispatch m tr m') : m' = m := by
  cases h with
  | refl => rfl
  | cons s _ =>
    obtain ⟨ev, rfl⟩ := Step.host_of_ctl_nil hc s
    have := (Step.host_ready s).2.1
    rw [hl] at this
    cases this

theorem steps_storeProg {p : P E σ α} (hp : StoreProg p) {f : α → P E σ (Ret E)}
    {th : Option ThreadId} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr m') :
    (∃ q s₁, (∀ a s₂, SRun q s₁ a s₂ → SRun p m.store a s₂) ∧
        m' = { m with store := s₁, ctl := ⟨th, .prog (q >>= f), segs⟩ :: rest }) ∨
      (m'.ctl = [] ∧ m'.store.lockdown = true) ∨
      ∃ a s₁ tr₁ tr₂, SRun p m.store a s₁ ∧ tr = tr₁ ++ tr₂ ∧
        Steps prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr₁
          { m with store := s₁, ctl := ⟨th, .prog (f a), segs⟩ :: rest } ∧
        Steps prof hr dispatch { m with store := s₁, ctl := ⟨th, .prog (f a), segs⟩ :: rest } tr₂
          m' := by
  induction p generalizing m tr with
  | pure a => exact .inr (.inr ⟨a, m.store, [], tr, Prog.Eval.pure _ _, rfl, .refl _, h⟩)
  | op o k ih =>
    obtain ⟨ho, hk⟩ := Prog.every_op_iff.1 hp
    cases h with
    | refl => exact .inl ⟨_, m.store, fun _ _ h => h, rfl⟩
    | cons s h' =>
      cases o with
      | get =>
        obtain ⟨rfl, rfl⟩ := step_get_inv rfl s
        rcases ih m.store (hk _) h' with ⟨q, s₁, hq, rfl⟩ | hd | ⟨a, s₁, tr₁, tr₂, ha, rfl, h₁, h₂⟩
        · exact .inl ⟨q, s₁, fun a s₂ h => SRun.get (hq a s₂ h), rfl⟩
        · exact .inr (.inl hd)
        · exact .inr (.inr ⟨a, s₁, .tau :: tr₁, tr₂, SRun.get ha, rfl, .cons s h₁, h₂⟩)
      | modify g =>
        obtain ⟨rfl, rfl⟩ := step_modify_inv rfl s
        rcases ih () (m := { m with store := g m.store }) (hk _) h' with
          ⟨q, s₁, hq, rfl⟩ | hd | ⟨a, s₁, tr₁, tr₂, ha, rfl, h₁, h₂⟩
        · exact .inl ⟨q, s₁, fun a s₂ h => SRun.modify (hq a s₂ h), rfl⟩
        · exact .inr (.inl hd)
        · exact .inr (.inr ⟨a, s₁, .tau :: tr₁, tr₂, SRun.modify ha, rfl, .cons s h₁, h₂⟩)
      | trap r =>
        have hm := step_trap_inv rfl s
        subst hm
        rw [steps_dead rfl rfl h']
        exact .inr (.inl ⟨rfl, rfl⟩)
      | _ => exact ho.elim

theorem SRun.steps {p : P E σ α} {s s' : CStore E} {a : α} (h : SRun p s a s')
    (f : α → P E σ (Ret E)) (th : Option ThreadId) (segs : List (Seg E σ))
    (rest : List (Activation E σ)) (m : Config E σ) :
    ∃ tr, (∀ l ∈ tr, l = .tau) ∧
      Steps prof hr dispatch { m with store := s, ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m with store := s', ctl := ⟨th, .prog (f a), segs⟩ :: rest } := by
  induction h with
  | pure => exact ⟨[], fun _ h => (nomatch h), .refl _⟩
  | @op o k s r s₁ a s₂ hH _ ih =>
    obtain ⟨tr, htr, hs⟩ := ih
    cases o with
    | get =>
      obtain ⟨rfl, rfl⟩ := hH
      exact ⟨.tau :: tr, by simpa using htr, .cons (Step.get rfl) hs⟩
    | modify g =>
      cases hH
      exact ⟨.tau :: tr, by simpa using htr, .cons (Step.modify rfl) hs⟩
    | _ => exact hH.elim


/-! ## Scripts of resource built-ins on the machine -/

/-- **Machine runs of the resource built-ins are table histories.** Every machine run from a
configuration running a script `cs` of resource built-in cores (then `f`) stops inside the
script, traps (and the machine is dead), or completes the script with results `ns` in store
`s₁` and continues with `f ns`; in the last case the handle table of every instance `j` went
from its value in the initial store to its value in `s₁` through a successful table history
whose handle events are the events of the calls on `j`. -/
theorem machine_resScript {lim : Silmaril.Wasm.Component.Limits} {cs : List ResCall} {f : List ℕ → P E σ (Ret E)}
    {th : Option ThreadId} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch
      { m with ctl := ⟨th, .prog (resScript lim cs >>= f), segs⟩ :: rest } tr m') :
    (∃ q s₁, (∀ a s₂, SRun q s₁ a s₂ → SRun (resScript (σ := σ) lim cs) m.store a s₂) ∧
        m' = { m with store := s₁, ctl := ⟨th, .prog (q >>= f), segs⟩ :: rest }) ∨
      (m'.ctl = [] ∧ m'.store.lockdown = true) ∨
      ∃ ns s₁ tr₁ tr₂, tr = tr₁ ++ tr₂ ∧
        Steps prof hr dispatch { m with ctl := ⟨th, .prog (resScript lim cs >>= f), segs⟩ :: rest }
          tr₁ { m with store := s₁, ctl := ⟨th, .prog (f ns), segs⟩ :: rest } ∧
        Steps prof hr dispatch { m with store := s₁, ctl := ⟨th, .prog (f ns), segs⟩ :: rest } tr₂
          m' ∧
        ∀ j, ∃ evs, TabSteps m.store s₁ j evs ∧ evs.map tableEv = instEvs j cs ns := by
  rcases steps_storeProg (storeProg_resScript lim cs) h with hA | hB | ⟨ns, s₁, tr₁, tr₂, hs, e, h₁, h₂⟩
  · exact .inl hA
  · exact .inr (.inl hB)
  · exact .inr (.inr ⟨ns, s₁, tr₁, tr₂, e, h₁, h₂, resScript_tab hs⟩)

/-- **The reference machine enforces the handle protocol on its resource built-ins**: every
machine run from a configuration running a script of resource built-in cores stops inside the
script, traps, or completes it with results `ns`; in the last case the handle events of the
calls on an instance whose table was empty are accepted by `handleProto ℕ r`, in both
orientations (`resource.new` returns a fresh index; `resource.rep`/`resource.drop` touch only
live indices). -/
theorem machine_resScript_accepts {lim : Silmaril.Wasm.Component.Limits} {cs : List ResCall}
    {f : List ℕ → P E σ (Ret E)} {th : Option ThreadId} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch
      { m with ctl := ⟨th, .prog (resScript lim cs >>= f), segs⟩ :: rest } tr m')
    {j : InstId} (hj : handles? m.store j = some Silmaril.Wasm.Component.Runtime.Table.empty) :
    (∃ q s₁, (∀ a s₂, SRun q s₁ a s₂ → SRun (resScript (σ := σ) lim cs) m.store a s₂) ∧
        m' = { m with store := s₁, ctl := ⟨th, .prog (q >>= f), segs⟩ :: rest }) ∨
      (m'.ctl = [] ∧ m'.store.lockdown = true) ∨
      ∃ ns s₁ tr₁ tr₂, tr = tr₁ ++ tr₂ ∧
        Steps prof hr dispatch { m with ctl := ⟨th, .prog (resScript lim cs >>= f), segs⟩ :: rest }
          tr₁ { m with store := s₁, ctl := ⟨th, .prog (f ns), segs⟩ :: rest } ∧
        Steps prof hr dispatch { m with store := s₁, ctl := ⟨th, .prog (f ns), segs⟩ :: rest } tr₂
          m' ∧
        ∀ r, (handleProto ℕ r).Accepts (instEvs j cs ns) := by
  rcases machine_resScript h with hA | hB | ⟨ns, s₁, tr₁, tr₂, e, h₁, h₂, hT⟩
  · exact .inl hA
  · exact .inr (.inl hB)
  · refine .inr (.inr ⟨ns, s₁, tr₁, tr₂, e, h₁, h₂, fun r => ?_⟩)
    obtain ⟨evs, hT', hE⟩ := hT j
    obtain ⟨t', -, hs⟩ := hT' _ hj
    rw [← hE]
    exact table_steps_accepts hs r

end Silmaril.Wasm.Resource
