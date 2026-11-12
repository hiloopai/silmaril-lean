module

public import Silmaril.Proofs.Wasm.Resource.CompToy.DropLower

/-!
# The toy resource component: the callouts of `drop`

* `builtin_lrunL`: `builtin_lrun` for a callout whose program switches threads (a live run
  instead of a big-step run), here the destructor call of `resource.drop`;
* `traps_dropCallout`: the callout to `resource.drop` of an index that is not live traps;
* **`drop_calloutsAns`**: the callouts of `drop`'s core phase are run by the machine as
  `Hdrop w` allows. From the call's frame (`dF0`, entry `i` an own handle of the toy's resource),
  the first `resource.drop(i)` removes it and runs REF's no-op destructor (`lrun_dropCallout`),
  ending in the frame `dF1` with one more task, thread and caller record and the thread table
  `⟨#[none, some t, none], [2]⟩`; from `dF1`, `resource.drop(i)` traps.

New proofs.
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Resource.CompToy

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Component
open Silmaril.Wasm.Component.Reference Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Component.Machine.StepDefs

variable {P : Silmaril.Wasm.Numerics.Profile} {prof : ProfileKind}

/-- **A built-in callout run to flat results** by a live run of the callout program (which may
switch threads), ending with the same core store: a live run to the resumed activation. -/
theorem builtin_lrunL {B : Machine.Config (E3 P) Unit} {th : Option ThreadId}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} {x : CoreSt (E3 P)} {h : CanonHost (E3 P)}
    {ys flat : List FlatValue} {tr : List (Label (E3 P) Unit)} {S' : CStore (E3 P)}
    {C : List (Option (Activation (E3 P) Unit))}
    (hl : B.store.lockdown = false) (hs : (E3 P).status x.1 x.2 = .callout h ys)
    (hS' : S'.lockdown = false) (hcore : S'.core = x.1)
    (hrun : LRun prof (refHost P).hr (D P) (calloutCfg B th K segs rest x h ys) tr
      { calloutCfg B th K segs rest x h ys with
        store := S'
        conts := C
        ctl := ⟨th, .prog (pure (.flat flat)), .core x.2 K :: segs⟩ :: rest }) :
    LRun prof (refHost P).hr (D P) (coreCfg B th K segs rest x) (.tau :: (tr ++ [.tau]))
      (coreCfg { B with store := S', conts := C } th K segs rest
        (x.1, (E3 P).resume x.1 x.2 (.values flat))) := by
  let M := coreCfg B th K segs rest x
  let M₁ := calloutCfg B th K segs rest x h ys
  have s₁ : UniqueStep prof (refHost P).hr (D P) M .tau M₁ :=
    .of_core rfl (callout_status_ne hs) (.coreCallout rfl hs)
  have s₂ : UniqueStep prof (refHost P).hr (D P)
      { M₁ with
        store := S'
        conts := C
        ctl := ⟨th, .prog (Prog.pure (.flat flat)), .core x.2 K :: segs⟩ :: rest }
      .tau
      { M₁ with
        store := S'
        conts := C
        ctl := ⟨th, .core ((E3 P).resume S'.core x.2 (.values flat)) K, segs⟩ :: rest } :=
    .of_prog rfl (fun _ _ e => by cases e) (Step.popCore rfl)
  have e : ({ M₁ with
      store := S'
      conts := C
      ctl := ⟨th, .core ((E3 P).resume S'.core x.2 (.values flat)) K, segs⟩ :: rest } :
        Machine.Config (E3 P) Unit) =
      coreCfg { B with store := S', conts := C } th K segs rest
        (x.1, (E3 P).resume x.1 x.2 (.values flat)) := by
    rw [hcore]
    cases S'
    dsimp only at hcore
    subst hcore
    rfl
  exact .cons ⟨List.cons_ne_nil _ _, hl⟩ s₁ (hrun.trans (.cons ⟨List.cons_ne_nil _ _, hS'⟩
    (e ▸ s₂) (.refl _)))

/-- **The callout to `resource.drop` of an index that is not live** traps. -/
theorem traps_dropCallout {th : ThreadId} {m : Machine.Config (E3 P) Unit} {thr : Runtime.Thread}
    {tk : Runtime.Task (E3 P)} {ι : InstState} {a : FlatValue}
    (hthr : ArenaField.threads.get? m.store th = some thr)
    (htk : ArenaField.tasks.get? m.store thr.task = some tk) (hinst : tk.inst = ⟨0⟩)
    (hi : m.store.insts = [ι]) (hleave : ι.mayLeave = true)
    (hrem : ι.removeHandle? (flatNat a) = none) :
    ∃ tr mT, TrapsQ (D P) (some th) (D P (.hostCallout (dropH P) [a])) m tr mT := by
  have hentry := calloutEntry_builtin (b := .resourceDrop ⟨0⟩) hthr htk hinst
  obtain ⟨tr₁, h₁⟩ := runs_resourceEnter hthr htk hinst hi hleave
  have hgi : ArenaField.insts.get? m.store ⟨0⟩ = some ι := insts_get₀ hi
  have hT : TrapsQ (D P) (some th) (handlesRemove ⟨0⟩ (flatNat a)) m ([.tau] ++ []) m := by
    unfold handlesRemove
    refine TrapsQ.bind (runs_getObj ArenaField.insts _ m hgi) ?_
    rw [hrem]
    exact TrapsQ.trap _ (isTrap_trap _)
  have hb : TrapsQ (D P) (some th) (Builtins.resourceDrop Silmaril.Wasm.Component.Limits.spec Quirks.none
      (destructorCall Silmaril.Wasm.Component.Limits.spec Quirks.none) ⟨0⟩ (flatNat a)) m (tr₁ ++ ([.tau] ++ [])) m := by
    unfold Builtins.resourceDrop resourceDropCore
    exact TrapsQ.bind h₁ (TrapsQ.left (TrapsQ.left hT))
  refine ⟨_, m, TrapsQ.bind (RunsQ.currentThread (RunsQ.pure _ _))
    (TrapsQ.bind (tr₂ := tr₁ ++ ([.tau] ++ [])) (RunsQ.get (RunsQ.pure _ _)) ?_)⟩
  show TrapsQ _ _ (match calloutEntry m.store (some th) (dropH P) with
    | some r => trap r | none => _) _ _ _
  rw [hentry]
  exact TrapsQ.left hb

/-- A callout that the host relation of `drop` answers is to `resource.drop` on `w`. -/
theorem hdrop_inv {w : BitVec 32} {h : CanonHost (E3 P)}
    {s : (E3 P).Store (CanonHost (E3 P))} {args : List Silmaril.Wasm.Execution.Core.Val}
    {o : Silmaril.Wasm.Execution.Host.Outcome (Silmaril.Wasm.Execution.Core.Store (CanonHost (E3 P)))
      Silmaril.Wasm.Execution.Core.Result}
    (ho : Hdrop P w h s args o) : h = dropH P ∧ args = [.i32 w] := by
  obtain ⟨S, hS, hpre, -⟩ := ho
  have hh : h = dropH P := by
    by_contra hne
    have h1 : toyBind P h ≠ 1 := by
      unfold toyBind
      split_ifs <;> simp_all
    simp [Γdrop, h1] at hS
  subst hh
  rw [toyBind_drop] at hS
  obtain rfl : dropSpec P w = S := Option.some.inj hS
  exact ⟨rfl, hpre⟩

/-! ## Thread tables during a drop -/

/-- The thread table of the instance after the destructor thread of a drop is freed. -/
def dropT (t : ThreadId) : Silmaril.Wasm.Component.Runtime.Table ThreadId := ⟨#[none, some t, none], [2]⟩

theorem callT_add (tb : Silmaril.Wasm.Component.Runtime.Table ThreadId) (t t' : ThreadId) :
    (callT tb t).add? t' = some (2, ⟨#[none, some t, some t'], []⟩) := by
  unfold callT
  split <;> rfl

theorem addThread?_drop (ι : InstState) (t t' : ThreadId) (T : Silmaril.Wasm.Component.Runtime.Table HandleEntry) :
    ({ callIn ι t with handles := T } : InstState).addThread? t' =
      some (2, { callIn ι t with handles := T, threads := ⟨#[none, some t, some t'], []⟩ }) := by
  simp only [InstState.addThread?, callIn, callT_add]
  rfl

theorem removeThread?_drop (ι : InstState) (t t' : ThreadId) (T : Silmaril.Wasm.Component.Runtime.Table HandleEntry) :
    ({ callIn ι t with handles := T, threads := ⟨#[none, some t, some t'], []⟩ } :
      InstState).removeThread? 2 =
      some (t', { callIn ι t with handles := T, threads := dropT t }) := rfl

theorem removeThread?_dropT (ι : InstState) (t : ThreadId) (T : Silmaril.Wasm.Component.Runtime.Table HandleEntry) :
    ({ callIn ι t with handles := T, threads := dropT t } : InstState).removeThread? 1 =
      some (t, InstState.removeThread 1 { callIn ι t with handles := T, threads := dropT t }) :=
  rfl

theorem removeThread_dropT (ι : InstState) (t : ThreadId) (T : Silmaril.Wasm.Component.Runtime.Table HandleEntry) :
    InstState.removeThread 1 { callIn ι t with handles := T, threads := dropT t } =
      { ι with handles := T, threads := ⟨#[none, none, none], [1, 2]⟩ } := rfl

/-! ## The frames of `drop`'s core phase -/

/-- The frame of `drop`'s core phase before the drop: the call's configuration `M₀` with the
store `S₀` (core store `cs`). -/
abbrev dF0 (M₀ : Machine.Config (E3 P) Unit) (S₀ : CStore (E3 P))
    (cs : (E3 P).Store (CanonHost (E3 P))) : Machine.Config (E3 P) Unit :=
  { M₀ with store := { S₀ with core := cs } }

/-- The frame after the destructor call of a drop of a handle of representation `rep`: one more
task `dtk`, thread `dthr` and caller record, the instance `ι₅`, continuation slots `C`. -/
abbrev dF1 (M₀ : Machine.Config (E3 P) Unit) (S₀ : CStore (E3 P)) (rep : ℕ) (ι₅ : InstState)
    (cs : (E3 P).Store (CanonHost (E3 P))) (dtk : Runtime.Task (E3 P)) (dthr : Runtime.Thread)
    (C : List (Option (Activation (E3 P) Unit))) : Machine.Config (E3 P) Unit :=
  { M₀ with store := dStore { S₀ with core := cs } rep ι₅ dtk dthr, conts := C }

/-- The invariant of `drop`'s core phase: before the drop, or after it. -/
def DInv (M₀ : Machine.Config (E3 P) Unit) (S₀ : CStore (E3 P)) (rep : ℕ) (ι₅ : InstState)
    (B : Machine.Config (E3 P) Unit) : Prop :=
  ∃ cs, B = dF0 M₀ S₀ cs ∨ ∃ dtk dthr C, B = dF1 M₀ S₀ rep ι₅ cs dtk dthr C

/-- The store of a call of `drop` once `own n` is lowered to entry `i` of the table `T₄`. -/
abbrev dS₀ (c : ℕ) (ι : InstState) (G : ToyGarb P) (k n : ℕ) (T₄ : Silmaril.Wasm.Component.Runtime.Table HandleEntry) :
    CStore (E3 P) :=
  tStore₄ P ftDrop c ι (callI ι G) G k [.own n] { callI ι G with handles := T₄ }
    (G.handles ++ [{ rt := ⟨0⟩, rep := n, own := true }])

/-- **The callouts of `drop`'s core phase** are run by the machine as the host relation of
`drop` allows: from the call's frame, `resource.drop(i)` removes the own handle at `i` and runs
the no-op destructor; after that, `resource.drop(i)` traps. -/
theorem drop_calloutsAns {M₀ : Machine.Config (E3 P) Unit} {c : ℕ} {ι : InstState}
    {G : ToyGarb P} {k n i : ℕ} {T₄ T₅ : Silmaril.Wasm.Component.Runtime.Table HandleEntry}
    {K : List FlatValue → Canon.P (E3 P) Unit (Ret (E3 P))} {segs : List (Seg (E3 P) Unit)}
    {rest : List (Activation (E3 P) Unit)} (hi32 : i < 2 ^ 32)
    (hrm : T₄.remove? i = some (.resource ⟨G.handles.length⟩, T₅)) (hT₅ : T₅.get? i = none)
    (hleave : ι.mayLeave = true) :
    CalloutsAns (prof := prof) (Hdrop P (BitVec.ofNat 32 i))
      (DInv M₀ (dS₀ c ι G k n T₄) n
        { callIn ι ⟨G.threads.length⟩ with handles := T₅, threads := dropT ⟨G.threads.length⟩ })
      (some ⟨G.threads.length⟩) K segs rest := by
  rintro B x E a h args ys o hB hd hst ho
  obtain ⟨rfl, rfl⟩ := hdrop_inv ho
  have hys : ys = [.int .i32 (BitVec.ofNat 32 i)] := by
    have hm := callout_args hd hst
    have e : ([.i32 (BitVec.ofNat 32 i)] : List Silmaril.Wasm.Execution.Core.Val).mapM
        Silmaril.Wasm.SingleThreaded.toFlat? = some [.int .i32 (BitVec.ofNat 32 i)] := rfl
    exact (Option.some.inj (hm.symm.trans e))
  subst hys
  have hflat : flatNat (.int .i32 (BitVec.ofNat 32 i)) = i := flatNat_i32 hi32
  rcases hB with ⟨cs, rfl | ⟨dtk, dthr, C, rfl⟩⟩
  · left
    have hrem : ({ callI ι G with handles := T₄ } : InstState).removeHandle?
        (flatNat (.int .i32 (BitVec.ofNat 32 i))) =
        some (.resource ⟨G.handles.length⟩, { callI ι G with handles := T₅ }) := by
      rw [hflat]
      simp [InstState.removeHandle?, hrm]
    have hthr := tStore₄_thread (c := c) (ι := ι) (G := G) (k := k) ftDrop
      { callI ι G with handles := T₄ } (G.handles ++ [{ rt := ⟨0⟩, rep := n, own := true }]) [.own n]
    have htk := tStore₄_task (c := c) (ι := ι) (G := G) (k := k) ftDrop
      { callI ι G with handles := T₄ } (G.handles ++ [{ rt := ⟨0⟩, rep := n, own := true }]) [.own n]
    obtain ⟨dtk, dthr, C, tr, hrun⟩ := lrun_dropCallout (prof := prof)
      (M := calloutCfg (dF0 M₀ (dS₀ c ι G k n T₄) cs) (some ⟨G.threads.length⟩) K segs rest x
        (dropH P) [.int .i32 (BitVec.ofNat 32 i)])
      (h := { rt := ⟨0⟩, rep := n, own := true }) rfl rfl
      (by exact hthr) (by exact htk) rfl
      rfl hleave hrem hleave
      (by
        show (G.handles ++ [_])[G.handles.length]? = _
        simp)
      rfl rfl rfl rfl (addThread?_drop ι _ _ T₅) (removeThread?_drop ι _ _ T₅)
    exact ⟨dF1 M₀ (dS₀ c ι G k n T₄) n
        { callIn ι ⟨G.threads.length⟩ with handles := T₅, threads := dropT ⟨G.threads.length⟩ }
        x.1 dtk dthr C, [], tr ++ [.tau], ⟨x.1, .inr ⟨dtk, dthr, C, rfl⟩⟩,
      ⟨dropSpec P (BitVec.ofNat 32 i), by rw [toyBind_drop]; rfl, rfl, rfl, rfl⟩,
      builtin_lrunL rfl hst rfl rfl hrun⟩
  · right
    have hrem : ({ callIn ι ⟨G.threads.length⟩ with
        handles := T₅
        threads := dropT ⟨G.threads.length⟩ } : InstState).removeHandle?
        (flatNat (.int .i32 (BitVec.ofNat 32 i))) = none := by
      rw [hflat]
      simp [InstState.removeHandle?, Silmaril.Wasm.Component.Runtime.Table.remove?, hT₅]
    obtain ⟨trT, mT, hT⟩ := traps_dropCallout (P := P)
      (m := calloutCfg (dF1 M₀ (dS₀ c ι G k n T₄) n
        { callIn ι ⟨G.threads.length⟩ with handles := T₅, threads := dropT ⟨G.threads.length⟩ }
        cs dtk dthr C) (some ⟨G.threads.length⟩) K segs rest x (dropH P)
        [.int .i32 (BitVec.ofNat 32 i)])
      (thr := (thread₁ G.tasks).withIndex 1)
      (tk := (tTask₁ P ftDrop G.callers ⟨G.threads.length⟩).withState .started)
      (by
        show (G.threads ++ [_] ++ [dthr])[G.threads.length]? = _
        exact getElem?_mid)
      (by
        show (G.tasks ++ [_] ++ [dtk])[G.tasks.length]? = _
        exact getElem?_mid)
      rfl rfl hleave hrem
    exact builtin_traps rfl hst hT

end Silmaril.Wasm.Resource.CompToy
