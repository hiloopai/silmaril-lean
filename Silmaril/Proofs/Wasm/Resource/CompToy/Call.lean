module

public import Silmaril.Wasm.Resource.CompToy.Defs
public import Silmaril.Wasm.Component.Reference.Calls.Thms
public import Silmaril.Proofs.Wasm.Resource.CompToy.Init

/-!
# The toy resource component: the deterministic parts of an export call

Over every profile `P`, from the configuration between calls:

* `toyCfgX P c ι G`: `toyCfg P c ι G` with every component-store field but the core store
  explicit (`toyCfg_eq`, kernel evaluation), so that the machine's store accesses reduce;
* `toy_invoke_inv`: the host's invocation of call `k` leads to `toyInvoked`; `toy_tick`: a tick
  returns to the configuration between calls;
* **`toy_callAt`**: the synchronous `canon lift` call of a function value `j` (core address
  `addr`, type `ft`) of the toy, as a live deterministic run from the invocation to the core
  activation on the lowered arguments, given the run of the lowering (which may add handles); and
  from the core activation's return, given the run of the lifting, a live deterministic run to
  the next configuration between calls `toyCfgX P c' (removeThread 1 ι₅) (nextG …)`.

The proofs follow `MultiPath.call_at_k` (`Silmaril.Proofs.Wasm.Component.Reference`), over the
toy's store (resource type, handles) instead of `readyStore`. New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs

variable (P : Silmaril.Wasm.Numerics.Profile)

/-! ## The configuration between calls -/

/-- The type of `make`. -/
def ftMake : WIT.FuncType Empty RtId := { params := [], result := some (.own ⟨0⟩), async_ := false }
/-- The type of `get`. -/
def ftGet : WIT.FuncType Empty RtId :=
  { params := [("h", .borrow ⟨0⟩)], result := some (.prim .u32), async_ := false }
/-- The type of `drop`. -/
def ftDrop : WIT.FuncType Empty RtId :=
  { params := [("h", .own ⟨0⟩)], result := none, async_ := false }

/-- The toy's function values. -/
def toyFuncs : List (CFuncInst (core3P P)) :=
  [.lifted (show (core3P P).FuncAddr from (2 : ℕ)) ftMake {} ⟨0⟩,
    .lifted (show (core3P P).FuncAddr from (3 : ℕ)) ftGet {} ⟨0⟩,
    .lifted (show (core3P P).FuncAddr from (4 : ℕ)) ftDrop {} ⟨0⟩]

/-- The store between calls, with every field but the core store explicit. -/
noncomputable def toyStoreX (c : ℕ) (ι : InstState) (G : ToyGarb P) : CStore (core3P P) where
  core := setCtr P (toyInst P).store.core c
  insts := [ι]
  resourceTypes := [{ impl := some ⟨0⟩ }]
  funcs := toyFuncs P
  tasks := G.tasks
  threads := G.threads
  resHandles := G.handles
  callers := G.callers

/-- The configuration between calls, with every field but the core store explicit. -/
noncomputable def toyCfgX (c : ℕ) (ι : InstState) (G : ToyGarb P) :
    Machine.Config (core3P P) Unit where
  store := toyStoreX P c ι G
  host := ()
  conts := G.conts
  pending := G.pending
  results := G.results
  cancels := G.cancels

theorem toyCfg_eq (c : ℕ) (ι : InstState) (G : ToyGarb P) : toyCfg P c ι G = toyCfgX P c ι G := by
  kernel_rfl

theorem toyCfgX_lockdown (c : ℕ) (ι : InstState) (G : ToyGarb P) :
    (toyCfgX P c ι G).store.lockdown = false := rfl

/-! ## The stores of a call -/

/-- The configuration after the host invoked `f` on `args` as call `k`. -/
noncomputable def toyInvoked (c : ℕ) (ι : InstState) (G : ToyGarb P) (k : ℕ) (f : FuncId)
    (args : List Silmaril.Wasm.Component.Reference.Val) : Machine.Config (core3P P) Unit :=
  { toyCfgX P c ι G with
    pending := G.pending ++ [(⟨k⟩, f, args)]
    ctl := [.ofProg none (StepDefs.invokeProg ⟨k⟩ f args)] }

/-- The task of a call of the lift of type `ft`. -/
def tTask₀ (ft : WIT.FuncType Empty RtId) (Gc : List (Caller (core3P P))) :
    Runtime.Task (core3P P) :=
  { ft := ft, opts := {}, inst := ⟨0⟩, caller := ⟨Gc.length⟩ }

/-- The task once its implicit thread `t` is registered. -/
def tTask₁ (ft : WIT.FuncType Empty RtId) (Gc : List (Caller (core3P P))) (t : ThreadId) :
    Runtime.Task (core3P P) :=
  ({ tTask₀ P ft Gc with implicitThread := some t } : Runtime.Task (core3P P)).addThread t

/-- The store when the thread of call `k` starts running. -/
noncomputable def tStore₁ (ft : WIT.FuncType Empty RtId) (c : ℕ) (ι : InstState) (G : ToyGarb P)
    (k : ℕ) (args : List Silmaril.Wasm.Component.Reference.Val) : CStore (core3P P) :=
  { toyStoreX P c ι G with
    tasks := G.tasks ++ [tTask₀ P ft G.callers]
    threads := G.threads ++ [thread₁ G.tasks]
    callers := G.callers ++ [.host ⟨k⟩ args 0]
    nestingDepth := 1 }

/-- The store once the thread entered its task. -/
noncomputable def tStore₂ (ft : WIT.FuncType Empty RtId) (c : ℕ) (ι ι' : InstState) (G : ToyGarb P)
    (k : ℕ) (args : List Silmaril.Wasm.Component.Reference.Val) : CStore (core3P P) :=
  { tStore₁ P ft c ι G k args with
    tasks := G.tasks ++ [tTask₁ P ft G.callers ⟨G.threads.length⟩]
    insts := [ι']
    threads := G.threads ++ [(thread₁ G.tasks).withIndex 1] }

/-- The store when the core activation starts. -/
noncomputable def tStore₃ (ft : WIT.FuncType Empty RtId) (c : ℕ) (ι ι' : InstState) (G : ToyGarb P)
    (k : ℕ) (args : List Silmaril.Wasm.Component.Reference.Val) : CStore (core3P P) :=
  { tStore₂ P ft c ι ι' G k args with
    tasks := G.tasks ++ [(tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started] }

/-- The store after the lowering of the arguments (instance `ι₄`, handle objects `H₄`). -/
noncomputable def tStore₄ (ft : WIT.FuncType Empty RtId) (c : ℕ) (ι ι' : InstState) (G : ToyGarb P)
    (k : ℕ) (args : List Silmaril.Wasm.Component.Reference.Val) (ι₄ : InstState) (H₄ : List ResourceHandle) : CStore (core3P P) :=
  { tStore₃ P ft c ι ι' G k args with insts := [ι₄], resHandles := H₄ }

/-- The task of a call once finished. -/
noncomputable def tTask₂ (ft : WIT.FuncType Empty RtId) (Gc : List (Caller (core3P P)))
    (t : ThreadId) :
    Runtime.Task (core3P P) :=
  { ((tTask₁ P ft Gc t).withState .started).withState .resolved with
    threads := (((tTask₁ P ft Gc t).withState .started).withState .resolved).threads.erase t }

/-- The leftovers after call `k` of function `j` (lift of type `ft` at `addr`) on `args` with
results `rs`, the handle objects being `H`. -/
noncomputable def nextG (G : ToyGarb P) (ft : WIT.FuncType Empty RtId) (k j addr : ℕ)
    (args rs : List Silmaril.Wasm.Component.Reference.Val)
    (H : List ResourceHandle) : ToyGarb P where
  tasks := G.tasks ++ [tTask₂ P ft G.callers ⟨G.threads.length⟩]
  threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }]
  callers := G.callers ++ [.host ⟨k⟩ args 0]
  handles := H
  conts := Config.setSlot (Config.setSlot G.conts G.threads.length
    (some (threadAct (D P) ⟨G.threads.length⟩
      (.liftImplicit ⟨G.tasks.length⟩ (show (core3P P).FuncAddr from addr)))))
    G.threads.length none
  pending := G.pending ++ [(⟨k⟩, ⟨j⟩, args)]
  results := G.results ++ [(⟨k⟩, some rs)]
  cancels := (⟨k⟩, .task ⟨G.tasks.length⟩) :: G.cancels.filter (·.1 != ⟨k⟩)

variable {P}

/-! ## Host events between calls -/

theorem toy_tick (prof : ProfileKind) (c : ℕ) (ι : InstState) (G : ToyGarb P)
    (m₁ : Machine.Config (E3 P) Unit)
    (hs : Step prof (refHost P).hr (D P) (toyCfgX P c ι G) (.host .tick) m₁) :
    ∃ trT, LRun prof (refHost P).hr (D P) m₁ trT (toyCfgX P c ι G) := by
  cases hs
  apply Exists.intro
  repeat mstep
  exact .refl _

theorem toy_invoke_inv {prof : ProfileKind} {c : ℕ} {ι : InstState} {G : ToyGarb P} {k : ℕ}
    {f : FuncId} {args : List Silmaril.Wasm.Component.Reference.Val} {m : Machine.Config (E3 P) Unit}
    (h : Step prof (refHost P).hr (D P) (toyCfgX P c ι G) (.host (invokeTop ⟨k⟩ f args)) m) :
    m = toyInvoked P c ι G k f args ∧ ∀ x ∈ G.pending, x.1 ≠ ⟨k⟩ := by
  cases h with
  | hostInvoke _ hfresh => exact ⟨rfl, hfresh⟩

/-- A call id that is not pending has no resolution in leftovers that are `Ok`. -/
theorem ToyGarb.Ok.find?_none {G : ToyGarb P} (hG : G.Ok) {k : ℕ}
    (hk : ∀ x ∈ G.pending, x.1 ≠ ⟨k⟩) : G.results.find? (·.1 == (⟨k⟩ : CallId)) = none := by
  rw [List.find?_eq_none]
  intro x hx e
  obtain ⟨y, hy, hxy⟩ := hG.1 x hx
  have hx' : x.1 = ⟨k⟩ := by simpa using e
  exact hk y hy (hxy.trans hx')

/-- The next configuration between calls answers call `k` with `rs`. -/
theorem result?_nextG {G : ToyGarb P} (hG : G.Ok) {k : ℕ} (hk : ∀ x ∈ G.pending, x.1 ≠ ⟨k⟩)
    (c : ℕ) (ι : InstState) (ft : WIT.FuncType Empty RtId) (j addr : ℕ) (args rs : List Silmaril.Wasm.Component.Reference.Val)
    (H : List ResourceHandle) :
    (toyCfgX P c ι (nextG P G ft k j addr args rs H)).result? ⟨k⟩ = some (some rs) := by
  unfold Machine.Config.result?
  show ((G.results ++ [((⟨k⟩ : CallId), some rs)]).find? (fun p => p.1 == (⟨k⟩ : CallId))).map
    Prod.snd = _
  rw [List.find?_append, hG.find?_none hk]
  simp

/-- The leftovers after a call are `Ok`. -/
theorem nextG_ok {G : ToyGarb P} (hG : G.Ok) (ft : WIT.FuncType Empty RtId) (k j addr : ℕ)
    (args rs : List Silmaril.Wasm.Component.Reference.Val) (H : List ResourceHandle) : (nextG P G ft k j addr args rs H).Ok := by
  have hnew : ((⟨k⟩ : CallId), (⟨j⟩ : FuncId), args) ∈ G.pending ++ [(⟨k⟩, ⟨j⟩, args)] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have hold : ∀ y ∈ G.pending, y ∈ G.pending ++ [(⟨k⟩, ⟨j⟩, args)] :=
    fun y hy => List.mem_append_left _ hy
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, e⟩ := hG.1 x hx
      exact ⟨y, hold y hy, e⟩
    · exact ⟨_, hnew, by rw [List.mem_singleton.mp hx]⟩
  · rcases List.mem_cons.mp hx with hx | hx
    · exact ⟨_, hnew, by rw [hx]⟩
    · obtain ⟨y, hy, e⟩ := hG.2 x (List.mem_filter.mp hx).1
      exact ⟨y, hold y hy, e⟩

/-- The thread table of the toy's instance during a call whose implicit thread is `t`: slot
`1` holds `t`; slot `2` stays free when the table between calls had two freed slots. -/
def callT (tb : Silmaril.Wasm.Component.Runtime.Table ThreadId) (t : ThreadId) : Silmaril.Wasm.Component.Runtime.Table ThreadId :=
  if tb = ⟨#[none, none, none], [1, 2]⟩ then ⟨#[none, some t, none], [2]⟩ else ⟨#[none, some t], []⟩

/-- The instance during a call whose implicit thread is `t`. -/
def callIn (ι : InstState) (t : ThreadId) : InstState := { ι with threads := callT ι.threads t }

/-- From a table between calls, the implicit thread of a call goes to slot `1`. -/
theorem addThread?_free {ι : InstState} (h : ThreadsFree ι.threads) (t : ThreadId) :
    ι.addThread? t = some (1, callIn ι t) := by
  rcases h with h | h | h <;>
    simp [InstState.addThread?, Table.add?, callIn, callT, h, Table.maxLength]

theorem removeThread?_call (ι : InstState) (t : ThreadId) :
    (callIn ι t).removeThread? 1 = some (t, InstState.removeThread 1 (callIn ι t)) := by
  unfold callIn callT
  split <;> rfl

theorem removeThread?_callH (ι : InstState) (t : ThreadId) (T : Silmaril.Wasm.Component.Runtime.Table HandleEntry) :
    ({ callIn ι t with handles := T } : InstState).removeThread? 1 =
      some (t, InstState.removeThread 1 { callIn ι t with handles := T }) := by
  unfold callIn callT
  split <;> rfl

/-- The instance after a call: its thread table is again one between calls. -/
theorem removeThread_call {ι : InstState} (h : ThreadsFree ι.threads) (t : ThreadId) :
    ∃ tb, InstState.removeThread 1 (callIn ι t) = { ι with threads := tb } ∧ ThreadsFree tb := by
  rcases h with h | h | h
  · exact ⟨_, by simp [InstState.removeThread, InstState.removeThread?, Table.remove?, Table.get?,
      callIn, callT, h], .inr (.inl rfl)⟩
  · exact ⟨_, by simp [InstState.removeThread, InstState.removeThread?, Table.remove?, Table.get?,
      callIn, callT, h], .inr (.inl rfl)⟩
  · exact ⟨_, by simp [InstState.removeThread, InstState.removeThread?, Table.remove?, Table.get?,
      callIn, callT, h], .inr (.inr rfl)⟩

/-- **`toyR` holds at the next configuration between calls.** -/
theorem toyR_next {c : ℕ} {ι : InstState} {G : ToyGarb P} (hc : c < 2 ^ 32)
    (hι : ι = { handles := ι.handles, threads := ι.threads }) (hth : ThreadsFree ι.threads)
    (hTB : TabB ι.handles) (hG : G.Ok)
    (t : ThreadId) (ft : WIT.FuncType Empty RtId) (k j addr : ℕ) (args rs : List Silmaril.Wasm.Component.Reference.Val)
    (H : List ResourceHandle) :
    toyR P toyEs (toyCfgX P c (InstState.removeThread 1 (callIn ι t))
      (nextG P G ft k j addr args rs H)) := by
  rw [← toyCfg_eq]
  obtain ⟨tb, e, htb⟩ := removeThread_call hth t
  rw [e]
  refine ⟨rfl, c, _, _, rfl, hc, ?_, htb, hTB, nextG_ok hG ft k j addr args rs H⟩
  rw [hι]

/-! ## Outcomes of a call -/

/-- **After a run to the next configuration between calls** where call `k` is resolved with
`rs`, the only resolved outcome of call `k` is `rs`, at that configuration. -/
theorem resolved_of_lrun {prof : ProfileKind} {mS mE m' : Machine.Config (E3 P) Unit}
    {c : ℕ} {ι : InstState} {G : ToyGarb P} {k : ℕ} {rs : List Silmaril.Wasm.Component.Reference.Val} {r : Option (List Silmaril.Wasm.Component.Reference.Val)}
    {trR tr : List (Label (E3 P) Unit)} (hR : LRun prof (refHost P).hr (D P) mS trR mE)
    (hE : mE = toyCfgX P c ι G) (hres : mE.result? ⟨k⟩ = some (some rs))
    (hs : Steps prof (refHost P).hr (D P) mS tr m')
    (hev : ∀ ev, Label.host ev ∈ tr → CallHostEvent ⟨k⟩ ev)
    (ho : (CallOutcome.resolved r).Holds (refHost P).hr ⟨k⟩ m') : m' = mE ∧ r = some rs := by
  rcases hR.inv hs with hl | ⟨tr₄, e, r'⟩
  · exact absurd ho (hl.not_holds _ _)
  have hev' : ∀ ev, Label.host ev ∈ tr₄ → CallHostEvent ⟨k⟩ ev :=
    fun ev hm => hev ev (e ▸ List.mem_append_right _ hm)
  subst hE
  have hq := quiet (c := ⟨k⟩) rfl (by rw [hres]; simp) (toy_tick prof c ι G) _ tr₄ m' le_rfl r'
    hev'
  rcases hq with rfl | hl
  · exact ⟨rfl, Option.some.inj (ho.2.2.symm.trans hres)⟩
  · exact absurd ho (hl.not_holds _ _)

/-- After a live run to a configuration whose only step is a trap, call `k` has no resolved
outcome. -/
theorem not_resolved_of_trap {prof : ProfileKind} {M mT m' : Machine.Config (E3 P) Unit}
    {trT tr : List (Label (E3 P) Unit)} {rT : TrapReason} {k : ℕ} {r : Option (List Silmaril.Wasm.Component.Reference.Val)}
    (hrun : LRun prof (refHost P).hr (D P) M trT mT) (hlive : Live mT)
    (hu : UniqueStep prof (refHost P).hr (D P) mT (.trap rT) (trapCfg mT))
    (hs : Steps prof (refHost P).hr (D P) M tr m') :
    ¬ (CallOutcome.resolved r).Holds (refHost P).hr ⟨k⟩ m' := by
  intro ho
  rcases hrun.inv hs with hl | ⟨tr₄, -, r'⟩
  · exact hl.not_holds _ _ ho
  cases r' with
  | refl => exact hlive.not_holds _ _ ho
  | cons s r'' =>
    obtain ⟨rfl, rfl⟩ := hu.2 _ _ s
    rw [steps_of_locked rfl rfl r''] at ho
    exact absurd ho.2.1 (by simp [trapCfg, lockdownSt])

/-! ## The call -/

theorem runs_ite_loop {th : Option ThreadId} {m : Machine.Config (E3 P) Unit}
    {Gt : List (Runtime.Task (E3 P))} {y : Runtime.Task (E3 P)}
    (ht : m.store.tasks = Gt ++ [y]) (hst : y.state = .resolved) {b : Bool} (hb : b = false) :
    RunsQ (D P) th (if !b then callUnit (.loop (.syncLiftLoop ⟨Gt.length⟩)) else pure () :
      Canon.P (E3 P) Unit Unit) m [.tau, .tau, .tau] () m := by
  subst hb
  exact runs_callUnit_loop ht hst

/-- **The deterministic parts of an export call** of the toy (function value `j`, the lift of
`ft` at core address `addr`), given the run of the lowering of `args` to `xs`. -/
theorem toy_callAt (prof : ProfileKind) (ft : WIT.FuncType Empty RtId) (j addr : ℕ)
    (args : List Silmaril.Wasm.Component.Reference.Val) (xs : List FlatValue) (c : ℕ) (ι ι' ι₄ : InstState) (G : ToyGarb P) (k : ℕ)
    (H₄ : List ResourceHandle) (trL : List (Label (E3 P) Unit))
    (hf : (toyFuncs P)[j]? = some (.lifted (show (core3P P).FuncAddr from addr) ft {} ⟨0⟩))
    (hasync : ft.async_ = false)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hlow : ∀ m : Machine.Config (E3 P) Unit, m.store = tStore₃ P ft c ι ι' G k args →
      RunsQ (D P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
        ABI.maxFlatParams args (paramTypes ft) none) m trL xs
        { m with store := tStore₄ P ft c ι ι' G k args ι₄ H₄ }) :
    ∃ M₀ th K segs rest tr₁, LRun prof (refHost P).hr (D P) (toyInvoked P c ι G k ⟨j⟩ args) tr₁ M₀ ∧
      th = some ⟨G.threads.length⟩ ∧ M₀.ctl =
        ⟨th, .core (Silmaril.Wasm.SingleThreaded.Thread.invokeFlat addr xs) K, segs⟩ :: rest ∧
      M₀.store = tStore₄ P ft c ι ι' G k args ι₄ H₄ ∧
      (∀ ys, ∃ (β : Type) (f : List Silmaril.Wasm.Component.Reference.Val × FlatCursor → Canon.P (E3 P) Unit β)
        (g : β → Canon.P (E3 P) Unit (Ret (E3 P))), K ys = (liftFlatValues Limits.spec Quirks.none
          ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
          ABI.maxFlatResults (.ofList ys) (resultTypes ft) >>= f) >>= g) ∧
      ∀ (cs' : (core3P P).Store (CanonHost (core3P P))) (ιc ι₅ : InstState)
        (Hc H₅ : List ResourceHandle) (ys : List FlatValue) (ws : List Silmaril.Wasm.Component.Reference.Val) (cur : FlatCursor)
        (trF : List (Label (E3 P) Unit)) (c' : ℕ),
        (∀ m : Machine.Config (E3 P) Unit,
          m.store = { tStore₄ P ft c ι ι' G k args ιc Hc with core := cs' } →
          RunsQ (D P) (some ⟨G.threads.length⟩) (liftFlatValues Limits.spec Quirks.none
            ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
            ABI.maxFlatResults (.ofList ys) (resultTypes ft)) m trF (ws, cur)
            { m with store := { tStore₄ P ft c ι ι' G k args ι₅ H₅ with core := cs' } }) →
        cs' = setCtr P (toyInst P).store.core c' →
        ι₅.removeThread? 1 = some (⟨G.threads.length⟩, InstState.removeThread 1 ι₅) →
        ∃ tr, LRun prof (refHost P).hr (D P)
          { M₀ with store := { tStore₄ P ft c ι ι' G k args ιc Hc with core := cs' },
                    ctl := ⟨th, .prog (K ys), segs⟩ :: rest } tr
          (toyCfgX P c' (InstState.removeThread 1 ι₅) (nextG P G ft k j addr args ws H₅)) := by
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply Exists.intro; apply Exists.intro; apply Exists.intro
  apply And.intro
  unfold toyInvoked
  apply RunsQ.chunk rfl (runs_allocObj ArenaField.callers (.host ⟨k⟩ args 0) _ rfl) rfl
  apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
  apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
  have hget : ∀ s : CStore (E3 P), s.funcs = toyFuncs P →
      ArenaField.funcs.get? s (⟨j⟩ : FuncId) =
        some (.lifted (show (core3P P).FuncAddr from addr) ft {} ⟨0⟩) := by
    intro s e
    simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
    exact hf
  apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
  apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
  apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
  apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
  apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) rfl
  apply LRun.prog rfl (fun _ _ e => by cases e) rfl
    (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
  have e₁ : ∀ S : CStore (E3 P), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
      threadStatusSt ⟨G.threads.length⟩ .running S =
        { S with threads := G.threads ++ [thread₁ G.tasks] } :=
    fun S h => threadStatus_last h _
  apply LRun.store_congr (S' := tStore₁ P ft c ι G k args) ((e₁ _ rfl).trans rfl)
  have hS₁ : (tStore₁ P ft c ι G k args).insts = [ι] := rfl
  apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
    (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
    (runs_enter (Gt := G.tasks) (y := tTask₀ P ft G.callers) rfl hasync rfl hS₁ hadd) rfl
  have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
      (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (tStore₁ P ft c ι G k args)) = tStore₂ P ft c ι ι' G k args :=
    enter_eq rfl rfl rfl hadd rfl
  apply LRun.store_congr (S' := tStore₂ P ft c ι ι' G k args) (by exact e₂)
  have hS₂ : (tStore₂ P ft c ι ι' G k args).tasks =
      G.tasks ++ [tTask₁ P ft G.callers ⟨G.threads.length⟩] := rfl
  apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last (Gt := G.tasks) hS₂))
    rfl
  apply RunsQ.chunk rfl (runs_start (Gt := G.tasks) (Gc := G.callers) hS₂ rfl rfl) rfl
  apply RunsQ.chunk rfl (hlow _ (setTaskState_last (Gt := G.tasks) rfl _)) rfl
  mstep
  exact .refl _
  refine ⟨rfl, rfl, rfl, fun ys => ⟨_, _, _, rfl⟩, ?_⟩
  intro cs' ιc ι₅ Hc H₅ ys ws cur trF c' hlift hcs hrem
  apply Exists.intro
  have hS : ∀ ιx Hx, ({ tStore₄ P ft c ι ι' G k args ιx Hx with core := cs' }).tasks =
      G.tasks ++ [(tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started] := fun _ _ => rfl
  apply RunsQ.chunk2 rfl (hlift _ rfl) rfl
  apply RunsQ.chunk2 rfl
    (runs_return (Gt := G.tasks) (Gc := G.callers) _ (hS ι₅ H₅) rfl rfl rfl rfl) rfl
  apply LRun.store_congr (S' := { tStore₄ P ft c ι ι' G k args ι₅ H₅ with
      core := cs'
      tasks := G.tasks ++ [((tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started).withState
        .resolved] })
    (by refine setTaskState_last (Gt := G.tasks) ?_ _; rfl)
  apply RunsQ.chunk rfl
    (runs_exit (Gt := G.tasks) (Gth := G.threads)
      (y := ((tTask₁ P ft G.callers ⟨G.threads.length⟩).withState .started).withState .resolved)
      (z := (thread₁ G.tasks).withIndex 1) (ι := ι₅) rfl rfl rfl hasync rfl rfl rfl rfl hrem) rfl
  apply LRun.store_congr (S' := { tStore₄ P ft c ι ι' G k args ι₅ H₅ with
      core := cs'
      tasks := G.tasks ++ [tTask₂ P ft G.callers ⟨G.threads.length⟩]
      insts := [InstState.removeThread 1 ι₅] }) (unregisterThreadSt_eq _ _ rfl rfl rfl)
  mstep
  apply LRun.store_congr (S' := { tStore₄ P ft c ι ι' G k args ι₅ H₅ with
      core := cs'
      tasks := G.tasks ++ [tTask₂ P ft G.callers ⟨G.threads.length⟩]
      insts := [InstState.removeThread 1 ι₅]
      threads := G.threads ++ [{ (thread₁ G.tasks).withIndex 1 with status := .exited }] })
    (threadStatus_last (z := (thread₁ G.tasks).withIndex 1) rfl _)
  apply RunsQ.chunk rfl (runs_ite_loop (Gt := G.tasks) rfl rfl hasync) rfl
  mstep
  mstep
  mstep
  rw [hostFinish_cancel _ G.pending ⟨k⟩ ⟨j⟩ args _ rfl]
  subst hcs
  exact .refl _


theorem trapsQ_lrun_at {prof : ProfileKind} {α : Type} {th : Option ThreadId}
    {p : Canon.P (E3 P) Unit α} {f : α → Canon.P (E3 P) Unit (Ret (E3 P))}
    {segs : List (Seg (E3 P) Unit)} {rest : List (Activation (E3 P) Unit)}
    {M mT : Machine.Config (E3 P) Unit} {tr : List (Label (E3 P) Unit)}
    (hc : M.ctl = ⟨th, .prog (p >>= f), segs⟩ :: rest) (hT : TrapsQ (D P) th p M tr mT)
    (hl : M.store.lockdown = false) :
    ∃ M' r, LRun prof (refHost P).hr (D P) M tr M' ∧ Live M' ∧
      UniqueStep prof (refHost P).hr (D P) M' (.trap r) (trapCfg M') := by
  obtain ⟨q, segs', r, h₁, h₂, h₃⟩ := hT.lrun (prof := prof) (hr := (refHost P).hr) hl f segs rest
  have e : ({ M with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } : Machine.Config (E3 P) Unit) =
      M := by
    rw [← hc]
  rw [e] at h₁
  exact ⟨_, r, h₁, h₂, h₃⟩

/-- **An export call of the toy whose lowering traps** is a live deterministic run to a
configuration whose only step is a trap. -/
theorem toy_callAt_trap (prof : ProfileKind) (ft : WIT.FuncType Empty RtId) (j addr : ℕ)
    (args : List Silmaril.Wasm.Component.Reference.Val) (c : ℕ) (ι ι' : InstState) (G : ToyGarb P) (k : ℕ)
    (hf : (toyFuncs P)[j]? = some (.lifted (show (core3P P).FuncAddr from addr) ft {} ⟨0⟩))
    (hasync : ft.async_ = false)
    (hadd : ι.addThread? ⟨G.threads.length⟩ = some (1, ι'))
    (hT : ∀ m : Machine.Config (E3 P) Unit, m.store = tStore₃ P ft c ι ι' G k args →
      ∃ trT mT, TrapsQ (D P) (some ⟨G.threads.length⟩) (lowerFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
        ABI.maxFlatParams args (paramTypes ft) none) m trT mT) :
    ∃ tr mT r, LRun prof (refHost P).hr (D P) (toyInvoked P c ι G k ⟨j⟩ args) tr mT ∧ Live mT ∧
      UniqueStep prof (refHost P).hr (D P) mT (.trap r) (trapCfg mT) := by
  have hpre : ∃ (X : Machine.Config (E3 P) Unit)
      (f : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))) (segs : List (Seg (E3 P) Unit))
      (rest : List (Activation (E3 P) Unit))
      (tr : List (Label (E3 P) Unit)),
      LRun prof (refHost P).hr (D P) (toyInvoked P c ι G k ⟨j⟩ args) tr X ∧
      X.ctl = ⟨some ⟨G.threads.length⟩, .prog (lowerFlatValues Limits.spec Quirks.none
        ({ opts := {}, inst := ⟨0⟩, scope := .task ⟨G.tasks.length⟩ } : LiftLowerContext (E3 P))
        ABI.maxFlatParams args (paramTypes ft) none >>= f), segs⟩ :: rest ∧
      X.store = tStore₃ P ft c ι ι' G k args := by
    apply Exists.intro; apply Exists.intro; apply Exists.intro
    apply Exists.intro; apply Exists.intro
    apply And.intro
    unfold toyInvoked
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.callers (.host ⟨k⟩ args 0) _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.modify (f := enterHostSt) rfl (.pure _ _)) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl (.call rfl)
    have hget : ∀ s : CStore (E3 P), s.funcs = toyFuncs P →
        ArenaField.funcs.get? s (⟨j⟩ : FuncId) =
          some (.lifted (show (core3P P).FuncAddr from addr) ft {} ⟨0⟩) := by
      intro s e
      simp only [ArenaField.get?, ArenaField.funcs, e, Arena.get?_eq_getElem?]
      exact hf
    apply RunsQ.chunk rfl (runs_getObj ArenaField.funcs _ _ (hget _ rfl)) rfl
    apply RunsQ.chunk rfl (runs_allocObj ArenaField.tasks _ _ rfl) rfl
    apply RunsQ.chunk rfl (RunsQ.newThread rfl rfl (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (RunsQ.get (.pure _ _)) rfl
    apply RunsQ.chunk2 rfl (runs_ite_false (by exact threadIs_last rfl) _ _) rfl
    apply LRun.prog rfl (fun _ _ e => by cases e) rfl
      (.resumeThread rfl (by exact Config.cont?_setCont_self _ _ _))
    have e₁ : ∀ S : CStore (E3 P), S.threads = G.threads ++ [{ task := ⟨G.tasks.length⟩ }] →
        threadStatusSt ⟨G.threads.length⟩ .running S =
          { S with threads := G.threads ++ [thread₁ G.tasks] } :=
      fun S h => threadStatus_last h _
    apply LRun.store_congr (S' := tStore₁ P ft c ι G k args) ((e₁ _ rfl).trans rfl)
    have hS₁ : (tStore₁ P ft c ι G k args).insts = [ι] := rfl
    apply RunsQ.chunk (th := some ⟨G.threads.length⟩)
      (p := Task.enterImplicitThread Quirks.none ⟨G.tasks.length⟩) (a := true) rfl
      (runs_enter (Gt := G.tasks) (y := tTask₀ P ft G.callers) rfl hasync rfl hS₁ hadd) rfl
    have e₂ : CStore.registerThreadSt ⟨G.tasks.length⟩ ⟨G.threads.length⟩
        (CStore.setImplicitThread ⟨G.tasks.length⟩ ⟨G.threads.length⟩
          (tStore₁ P ft c ι G k args)) = tStore₂ P ft c ι ι' G k args :=
      enter_eq rfl rfl rfl hadd rfl
    apply LRun.store_congr (S' := tStore₂ P ft c ι ι' G k args) (by exact e₂)
    have hS₂ : (tStore₂ P ft c ι ι' G k args).tasks =
        G.tasks ++ [tTask₁ P ft G.callers ⟨G.threads.length⟩] := rfl
    apply RunsQ.chunk rfl (runs_getObj ArenaField.tasks _ _ (tasks_get_last (Gt := G.tasks) hS₂))
      rfl
    apply RunsQ.chunk rfl (runs_start (Gt := G.tasks) (Gc := G.callers) hS₂ rfl rfl) rfl
    exact .refl _
    refine ⟨rfl, setTaskState_last (Gt := G.tasks) rfl _⟩
  obtain ⟨X, f, segs, rest, tr, hrun, hc, hs⟩ := hpre
  obtain ⟨trT, mT, hT'⟩ := hT X hs
  obtain ⟨M', r, hrun', hlive, hu⟩ := trapsQ_lrun_at (prof := prof) hc hT' (by rw [hs]; rfl)
  exact ⟨_, M', r, hrun.trans hrun', hlive, hu⟩

end Silmaril.Wasm.Resource.CompToy
