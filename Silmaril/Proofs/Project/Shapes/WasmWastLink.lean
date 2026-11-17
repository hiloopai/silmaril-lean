module

public import Silmaril.Project.Shapes.WasmWastLink.Defs
public import Silmaril.Proofs.Project.Shapes.WasmWast
public import Silmaril.Wasm.Game.InstantiateTyped.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.Verify.Kernel.Thms
public import Silmaril.Wasm.Execution.MemRep.Inst.Thms

/-!
# Proofs: linked WAST scripts from one kernel evaluation

* `scriptG_toBytes`: the checker on `KMem` stores (`scriptLK`) agrees with the checker on
  `ByteArray` stores (`instantiateOnce?_toBytes`, `runI_toBytes`);
* `runG_sound`, `instG_sound`, `actG_sound`, `unlinkableG_sound`: a stopped run of a typed
  configuration is a host-free normal form and stays typed; instantiation keeps the store typed
  (`Game.instantiateOnce?_configOk`);
* `nf_unique`, `nf_always`: uniqueness and termination for the host-free normal forms of any
  configuration (from `Silmaril.Proofs.Project.Shapes.WasmWast`, same topic);
* `actNF_unique`, `instNF_unique`, `cmdRun_unique`, `scriptAt_unique`: at `profile o` a script
  prefix reaches at most one context (`nf_unique`);
* `scriptHolds_of_kernel`: `scriptLK … = true` gives `ScriptHolds`;
* `reaches_always`: one run of an action to a result excludes infinite runs (`nf_always`);
* `print_nf`: a function whose body is empty returns no values and leaves the store unchanged.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.WasmWastLink

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Project.Shapes.WasmWastLink
open Silmaril.Project.Shapes.WasmWast (Expect exportFunc? invokeOkB importStoreKM)
open Silmaril.Wasm.Execution (KMem MemRep LawfulMemRep)

/-! ## From `KMem` stores to `ByteArray` stores -/

section ToBytes

variable {R : Type} [MemRep R] [LawfulMemRep R]

theorem runG_toBytes (o : GrowOracle) (fuel : Nat) (c : Config Nat R) :
    (runG o fuel c).map Config.toBytes = runG o fuel c.toBytes := by
  unfold runG
  rw [Silmaril.Wasm.Verify.Kernel.runK_eq, Silmaril.Wasm.Verify.Kernel.runK_eq]
  change (if (Exec.runI o fuel c).2 = true then some (Exec.runI o fuel c).1 else none).map _ =
    (if (Exec.runI o fuel c.toBytes).2 = true then some (Exec.runI o fuel c.toBytes).1 else none)
  rw [← Exec.runI_toBytes o fuel c]
  generalize Exec.runI o fuel c = p
  rcases p with ⟨c', b⟩
  cases b <;> rfl

omit [LawfulMemRep R] in
theorem externAddrType?_toBytes (s : Store Nat R) (xa : ExternAddr) :
    externAddrType? s.toBytes xa = externAddrType? s xa := by
  cases xa <;> simp [externAddrType?, Store.toBytes]
  rename_i a
  cases s.mems[a]? <;> rfl

omit [LawfulMemRep R] in
theorem externAddrsOk?_toBytes (s : Store Nat R) :
    ∀ (xas : List ExternAddr) (xts : List CExternType),
      externAddrsOk? s.toBytes xas xts = externAddrsOk? s xas xts
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | xa :: xas, xt :: xts => by
    simp only [externAddrsOk?, externAddrOk?, externAddrType?_toBytes, externAddrsOk?_toBytes s xas]

theorem runG_mk_toBytes (o : GrowOracle) (fuel : Nat) (s : Store Nat R) (f : Frame)
    (code : List Admin) :
    runG o fuel ⟨s.toBytes, f, code⟩ = (runG o fuel ⟨s, f, code⟩).map Config.toBytes :=
  (runG_toBytes o fuel ⟨s, f, code⟩).symm

theorem runG_invoke_toBytes (o : GrowOracle) (fuel : Nat) (s : Store Nat R) (a : Nat)
    (args : List Val) :
    runG o fuel (invoke s.toBytes a args) = (runG o fuel (invoke s a args)).map Config.toBytes :=
  (runG_toBytes o fuel (invoke s a args)).symm

theorem instG_toBytes (o : GrowOracle) (fuel : Nat) (ctx : CtxR R) (m : Module) :
    (instG o fuel ctx m).map (fun p => (p.1.toBytes, p.2)) = instG o fuel ctx.toBytes m := by
  simp only [instG, CtxR.toBytes]
  cases validate? m with
  | none => rfl
  | some mt =>
    simp only
    cases resolve? ctx.regs m.imports with
    | none => rfl
    | some xas =>
      simp only [externAddrsOk?_toBytes]
      cases externAddrsOk? ctx.store xas mt.imports with
      | false => rfl
      | true =>
        simp only [ite_true, ← instantiateOnce?_toBytes]
        cases instantiateOnce? ctx.store m xas with
        | none => rfl
        | some p =>
          obtain ⟨s, f, st⟩ := p
          simp only [Option.map_some, runG_mk_toBytes]
          cases runG o fuel ⟨s, f, startCode st⟩ <;> rfl

omit [LawfulMemRep R] in
theorem inst?_toBytes (ctx : CtxR R) (t : Target) : ctx.toBytes.inst? t = ctx.inst? t := by
  cases t <;> rfl

theorem actG_toBytes (o : GrowOracle) (fuel : Nat) (ctx : CtxR R) (act : Action) :
    (actG o fuel ctx act).map (fun p => (p.1, p.2.toBytes)) = actG o fuel ctx.toBytes act := by
  cases act with
  | invoke t name args =>
    simp only [actG]
    rw [inst?_toBytes]
    cases ctx.inst? t with
    | none => rfl
    | some mi =>
      simp only
      cases exportFunc? mi name with
      | none => rfl
      | some a =>
        simp only
        rw [show invokeOkB ctx.toBytes.store a args = invokeOkB ctx.store a args from rfl]
        cases invokeOkB ctx.store a args with
        | false => rfl
        | true =>
          simp only [ite_true]
          rw [show ctx.toBytes.store = ctx.store.toBytes from rfl, runG_invoke_toBytes]
          cases runG o fuel (invoke ctx.store a args) with
          | none => rfl
          | some c =>
            simp only [Option.map_some, Option.bind_some]
            change _ = (c.outcome?).map fun r => (r, c.store.toBytes)
            cases c.outcome? <;> rfl
  | get t name =>
    simp only [actG]
    rw [inst?_toBytes]
    cases ctx.inst? t with
    | none => rfl
    | some mi =>
      simp only
      cases exportAddr? mi name with
      | none => rfl
      | some xa =>
        cases xa with
        | global a =>
          simp only
          change _ = ctx.store.globals[a]?.map fun gi =>
            (Result.values [gi.value], ctx.store.toBytes)
          cases ctx.store.globals[a]? <;> rfl
        | _ => rfl

omit [LawfulMemRep R] in
theorem unlinkableG_toBytes (ctx : CtxR R) (m : Module) :
    unlinkableG ctx.toBytes m = unlinkableG ctx m := by
  simp only [unlinkableG, CtxR.toBytes]
  cases validate? m with
  | none => rfl
  | some mt =>
    simp only
    cases resolve? ctx.regs m.imports with
    | none => rfl
    | some xas => simp only [externAddrsOk?_toBytes]

theorem cmdsG_toBytes (o : GrowOracle) (fuel : Nat) :
    ∀ (ctx : CtxR R) (cmds : List Cmd), cmdsG o fuel ctx cmds = cmdsG o fuel ctx.toBytes cmds
  | _, [] => rfl
  | ctx, .module name m :: cmds => by
    simp only [cmdsG]
    rw [← instG_toBytes]
    cases instG o fuel ctx m with
    | none => rfl
    | some p =>
      obtain ⟨c, mi⟩ := p
      simp only [Option.map_some]
      rw [cmdsG_toBytes o fuel _ cmds]
      rfl
  | ctx, .register as t :: cmds => by
    simp only [cmdsG]
    change _ = match ctx.inst? t with
      | some mi => cmdsG o fuel { ctx.toBytes with regs := (as, mi) :: ctx.regs } cmds
      | none => false
    cases ctx.inst? t with
    | none => rfl
    | some mi => exact cmdsG_toBytes o fuel _ cmds
  | ctx, .action act e :: cmds => by
    simp only [cmdsG]
    rw [← actG_toBytes]
    cases actG o fuel ctx act with
    | none => rfl
    | some p =>
      obtain ⟨r, s⟩ := p
      simp only [Option.map_some]
      rw [cmdsG_toBytes o fuel _ cmds]
      rfl
  | ctx, .unlinkable m claim :: cmds => by
    simp only [cmdsG]
    rw [unlinkableG_toBytes, cmdsG_toBytes o fuel ctx cmds]
  | ctx, .uninstantiable m claim :: cmds => by
    simp only [cmdsG]
    rw [← instG_toBytes]
    cases instG o fuel ctx m with
    | none => rfl
    | some p =>
      obtain ⟨c, mi⟩ := p
      simp only [Option.map_some]
      change _ = match c.outcome? with
        | some r => (!claim || decide (r = Result.trap)) &&
            cmdsG o fuel { ctx.toBytes with store := c.store.toBytes } cmds
        | none => false
      cases c.outcome? with
      | none => rfl
      | some r =>
        simp only
        rw [cmdsG_toBytes o fuel _ cmds]
        rfl

theorem scriptG_toBytes (o : GrowOracle) (fuel : Nat) (s₀ : Store Nat R) (cmds : List Cmd) :
    scriptG o fuel s₀ cmds = scriptG o fuel s₀.toBytes cmds := by
  simp only [scriptG]
  cases validate? Spectest.module with
  | none => rfl
  | some mt =>
    simp only [← instantiateOnce?_toBytes]
    cases instantiateOnce? s₀ Spectest.module [] with
    | none => rfl
    | some p =>
      obtain ⟨s, f, st⟩ := p
      cases st with
      | none =>
        simp only [Option.map_some]
        rw [cmdsG_toBytes o fuel _ cmds]
        rfl
      | some _ => rfl

end ToBytes

/-! ## Normal forms of any configuration

The two facts of `Silmaril.Proofs.Project.Shapes.WasmWast` (same topic) for the host-free normal
forms of any configuration, not only of an invocation: uniqueness (`Det.DStep.join'`) and
termination (`nsteps_normal_not_infinite`, `Det.DStep.shrink`). -/

section NF

open Silmaril.Proofs.Project.Shapes.WasmWast (nsteps_normal_not_infinite nsteps_of_steps
  nsteps_to_rtg dstep_shrink)

theorem nf_unique {o : GrowOracle} {c₀ c c' : Config Nat} (h : Steps (profile o) Det.noHost c₀ c)
    (hn : ∀ x, ¬ Step (profile o) Det.noHost c x) (h' : Steps (profile o) Det.noHost c₀ c')
    (hn' : ∀ x, ¬ Step (profile o) Det.noHost c' x) : c = c' :=
  nf_unique_of_join (R := Det.DStep o) (fun ha hb => Det.DStep.join' ha hb) h h' hn hn'

theorem nf_always {o : GrowOracle} {c₀ c : Config Nat} (h : Steps (profile o) Det.noHost c₀ c)
    (hn : ∀ x, ¬ Step (profile o) Det.noHost c x) :
    ¬ Diverges (profile o) Det.noHost c₀ ∧
      ∀ c', Steps (profile o) Det.noHost c₀ c' → Steps (profile o) Det.noHost c' c := by
  obtain ⟨k, hk⟩ := NSteps.of_rtg (R := Det.DStep o) h
  refine ⟨nsteps_normal_not_infinite (R := Det.DStep o) (fun c : Config Nat => sizeOf c.code)
    (fun ha hb => Det.DStep.join' ha hb) (fun ha hb => dstep_shrink ha hb) hn k _ hk,
    fun c' hc' => ?_⟩
  obtain ⟨m, hm⟩ := nsteps_of_steps (R := Det.DStep o) (fun ha hb => Det.DStep.join' ha hb)
    hn hk hc'
  exact nsteps_to_rtg hm

end NF

/-! ## Soundness on `ByteArray` stores -/

theorem runG_sound {o : GrowOracle} {fuel : Nat} {c c' : Config Nat} {ts : List CValType}
    (hc : ConfigOk c ts) (h : runG o fuel c = some c') : NF o c c' ∧ ConfigOk c' ts := by
  unfold runG at h
  rw [Silmaril.Wasm.Verify.Kernel.runK_eq] at h
  change (if (Exec.runI o fuel c).2 = true then some (Exec.runI o fuel c).1 else none) = _ at h
  split at h
  · rename_i hst
    cases h
    exact ⟨⟨Exec.runI_steps_typed fuel hc, Exec.runI_stopped_no_step_typed hc hst⟩,
      Exec.runI_typed fuel hc⟩
  · cases h

theorem instG_sound {o : GrowOracle} {fuel : Nat} {ctx : CtxR ByteArray} {m : Module} {c : Config Nat}
    {mi : ModuleInst} (hs : StoreOk ctx.store) (h : instG o fuel ctx m = some (c, mi)) :
    InstNF o ctx m c.outcome? c.store mi ∧ StoreOk c.store := by
  unfold instG at h
  split at h
  · cases h
  · rename_i mt hv
    split at h
    · cases h
    · rename_i xas hr
      split at h
      · rename_i hx
        split at h
        · rename_i s f st hi
          have hm := validate?_sound hv
          have hx' := externAddrsOk?_sound hx
          have hc := Game.instantiateOnce?_configOk hs hm hx' hi
          cases hrun : runG o fuel ⟨s, f, startCode st⟩ with
          | none => rw [hrun] at h; cases h
          | some c' =>
            rw [hrun] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hnf, hok⟩ := runG_sound hc hrun
            exact ⟨.mk hm hr hx' hi hnf, ConfigOk.storeOk hok⟩
        · cases h
      · cases h

theorem actG_sound {o : GrowOracle} {fuel : Nat} {ctx : CtxR ByteArray} {act : Action} {r : Result}
    {s : Store Nat} (hs : StoreOk ctx.store) (h : actG o fuel ctx act = some (r, s)) :
    ActNF o ctx act (some r) s ∧ StoreOk s := by
  cases act with
  | invoke t name args =>
    simp only [actG] at h
    split at h
    · rename_i mi hm
      split at h
      · rename_i a ha
        split at h
        · rename_i hok
          have hi := Silmaril.Proofs.Project.Shapes.WasmWast.invokeOk_of_invokeOkB hok
          obtain ⟨_, _, rs, _, _, hc⟩ := invoke_ok hs hi
          cases hrun : runG o fuel (invoke ctx.store a args) with
          | none => rw [hrun] at h; cases h
          | some c =>
            rw [hrun] at h
            simp only [Option.bind_some] at h
            obtain ⟨hnf, hok'⟩ := runG_sound hc hrun
            cases hr : c.outcome? with
            | none => rw [hr] at h; cases h
            | some r' =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have := ActNF.invoke (o := o) (args := args) hm ha hnf
              rw [hr] at this
              exact ⟨this, ConfigOk.storeOk hok'⟩
        · cases h
      · cases h
    · cases h
  | get t name =>
    simp only [actG] at h
    split at h
    · rename_i mi hm
      split at h
      · rename_i a ha
        cases hg : ctx.store.globals[a]? with
        | none => rw [hg] at h; cases h
        | some gi =>
          rw [hg] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨.get hm ha hg, hs⟩
      · cases h
    · cases h

theorem unlinkableG_sound {ctx : CtxR ByteArray} {m : Module} (hs : StoreOk ctx.store)
    (h : unlinkableG ctx m = true) :
    (∃ mt, ModuleOk m mt) ∧ ∀ mt xas, ModuleOk m mt → resolve? ctx.regs m.imports = some xas →
      ¬ List.Forall₂ (ExternAddrOk ctx.store) xas mt.imports := by
  unfold unlinkableG at h
  split at h
  · rename_i mt₀ hv
    have hm₀ := validate?_sound hv
    refine ⟨⟨mt₀, hm₀⟩, fun mt xas hm hr hx => ?_⟩
    obtain rfl := ModuleOk.unique hm hm₀
    rw [hr] at h
    simp only [Bool.not_eq_true'] at h
    rw [externAddrsOk?_complete hs hx] at h
    cases h
  · cases h

/-! ## Uniqueness -/

theorem actNF_unique {o : GrowOracle} {ctx : CtxR ByteArray} {act : Action} {ro ro' : Option Result}
    {s s' : Store Nat} (h : ActNF o ctx act ro s) (h' : ActNF o ctx act ro' s') :
    ro = ro' ∧ s = s' := by
  cases h with
  | invoke hm ha hc =>
    cases h' with
    | invoke hm' ha' hc' =>
      rw [hm] at hm'
      cases hm'
      rw [ha] at ha'
      cases ha'
      obtain rfl := nf_unique hc.1 hc.2 hc'.1 hc'.2
      exact ⟨rfl, rfl⟩
  | get hm ha hg =>
    cases h' with
    | get hm' ha' hg' =>
      rw [hm] at hm'
      cases hm'
      rw [ha] at ha'
      cases ha'
      rw [hg] at hg'
      cases hg'
      exact ⟨rfl, rfl⟩

theorem instNF_unique {o : GrowOracle} {ctx : CtxR ByteArray} {m : Module} {ro ro' : Option Result}
    {s s' : Store Nat} {mi mi' : ModuleInst} (h : InstNF o ctx m ro s mi)
    (h' : InstNF o ctx m ro' s' mi') : ro = ro' ∧ s = s' ∧ mi = mi' := by
  cases h with
  | mk hm hr hx hi hc =>
    cases h' with
    | mk hm' hr' hx' hi' hc' =>
      rw [hr] at hr'
      cases hr'
      rw [hi] at hi'
      simp only [Option.some.injEq, Prod.mk.injEq] at hi'
      obtain ⟨rfl, rfl, rfl⟩ := hi'
      obtain rfl := nf_unique hc.1 hc.2 hc'.1 hc'.2
      exact ⟨rfl, rfl, rfl⟩

theorem cmdRun_unique {o : GrowOracle} {ctx ctx₁ ctx₂ : CtxR ByteArray} {cmd : Cmd}
    (h₁ : CmdRun o ctx cmd ctx₁) (h₂ : CmdRun o ctx cmd ctx₂) : ctx₁ = ctx₂ := by
  cases h₁ with
  | module h =>
    cases h₂ with
    | module h' =>
      obtain ⟨-, rfl, rfl⟩ := instNF_unique h h'
      rfl
  | register h =>
    cases h₂ with
    | register h' =>
      rw [h] at h'
      cases h'
      rfl
  | action h =>
    cases h₂ with
    | action h' =>
      obtain ⟨-, rfl⟩ := actNF_unique h h'
      rfl
  | unlinkable => cases h₂; rfl
  | uninstantiable h =>
    cases h₂ with
    | uninstantiable h' =>
      obtain ⟨-, rfl, -⟩ := instNF_unique h h'
      rfl

theorem run_unique {o : GrowOracle} {ctx ctx₁ ctx₂ : CtxR ByteArray} {cmds : List Cmd}
    (h₁ : Run o ctx cmds ctx₁) (h₂ : Run o ctx cmds ctx₂) : ctx₁ = ctx₂ := by
  induction h₁ with
  | nil => cases h₂; rfl
  | cons h _ ih =>
    cases h₂ with
    | cons h' t' =>
      obtain rfl := cmdRun_unique h h'
      exact ih t'

theorem run_append {o : GrowOracle} {ctx ctx₁ ctx₂ : CtxR ByteArray} {l₁ l₂ : List Cmd}
    (h₁ : Run o ctx l₁ ctx₁) (h₂ : Run o ctx₁ l₂ ctx₂) : Run o ctx (l₁ ++ l₂) ctx₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem init_unique {ctx ctx' : CtxR ByteArray} (h : Init ctx) (h' : Init ctx') : ctx = ctx' := by
  obtain ⟨s, f, hi, rfl⟩ := h
  obtain ⟨s', f', hi', rfl⟩ := h'
  rw [hi] at hi'
  simp only [Option.some.injEq, Prod.mk.injEq] at hi'
  obtain ⟨rfl, rfl, -⟩ := hi'
  rfl

theorem scriptAt_unique {o : GrowOracle} {pre : List Cmd} {ctx ctx' : CtxR ByteArray}
    (h : ScriptAt o pre ctx) (h' : ScriptAt o pre ctx') : ctx = ctx' := by
  obtain ⟨c₀, hI, hr⟩ := h
  obtain ⟨c₀', hI', hr'⟩ := h'
  obtain rfl := init_unique hI hI'
  exact run_unique hr hr'

/-! ## Scripts -/

theorem scriptAt_snoc {o : GrowOracle} {done : List Cmd} {ctx ctx' : CtxR ByteArray} {cmd : Cmd}
    (hS : ScriptAt o done ctx) (h : CmdRun o ctx cmd ctx') : ScriptAt o (done ++ [cmd]) ctx' := by
  obtain ⟨c₀, hI, hr⟩ := hS
  exact ⟨c₀, hI, run_append hr (.cons h (.nil _))⟩

theorem holds_action {o : GrowOracle} {done : List Cmd} {ctx : CtxR ByteArray} {act : Action} {r : Result}
    {s : Store Nat} (hS : ScriptAt o done ctx) (h : ActNF o ctx act (some r) s) :
    Reaches o done act r ∧ Only o done act r := by
  refine ⟨⟨ctx, s, hS, h⟩, fun ctx' ro s' hS' h' => ?_⟩
  obtain rfl := scriptAt_unique hS hS'
  exact (actNF_unique h h').1.symm

theorem cmdsG_holds {o : GrowOracle} {fuel : Nat} :
    ∀ {cmds : List Cmd} {done : List Cmd} {ctx : CtxR ByteArray}, StoreOk ctx.store →
      ScriptAt o done ctx → cmdsG o fuel ctx cmds = true →
      ∀ k (cmd : Cmd), cmds[k]? = some cmd → cmd.Holds o (done ++ pre cmds k)
  | [], _, _, _, _, _, k, _, hk => by simp at hk
  | cmd :: cmds, done, ctx, hs, hS, h, k, cmd', hk => by
    -- the next context, its typing, and the claim of `cmd` itself
    have step : ∃ ctx', StoreOk ctx'.store ∧ CmdRun o ctx cmd ctx' ∧
        cmdsG o fuel ctx' cmds = true ∧ cmd.Holds o done := by
      cases cmd with
      | module name m =>
        simp only [cmdsG] at h
        split at h
        · rename_i c mi hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨hv, h⟩ := h
          obtain ⟨hI, hs'⟩ := instG_sound hs hc
          rw [hv] at hI
          exact ⟨_, hs', .module hI, h, trivial⟩
        · cases h
      | register as t =>
        simp only [cmdsG] at h
        split at h
        · rename_i mi hm
          exact ⟨{ ctx with regs := (as, mi) :: ctx.regs }, hs, .register hm, h, trivial⟩
        · cases h
      | action act e =>
        simp only [cmdsG] at h
        split at h
        · rename_i r s ha
          simp only [Bool.and_eq_true] at h
          obtain ⟨he, h⟩ := h
          obtain ⟨hA, hs'⟩ := actG_sound hs ha
          refine ⟨_, hs', .action hA, h, ?_⟩
          rcases e with _ | e
          · trivial
          · simp only [decide_eq_true_eq] at he
            subst he
            have := holds_action hS hA
            cases e <;> exact this
        · cases h
      | unlinkable m claim =>
        simp only [cmdsG, Bool.and_eq_true] at h
        obtain ⟨hu, h⟩ := h
        refine ⟨_, hs, .unlinkable, h, ?_⟩
        cases claim with
        | false => trivial
        | true =>
          simp only [Bool.not_true, Bool.false_or] at hu
          exact ⟨⟨ctx, hS⟩, fun ctx' hS' => by
            obtain rfl := scriptAt_unique hS hS'
            exact unlinkableG_sound hs hu⟩
      | uninstantiable m claim =>
        simp only [cmdsG] at h
        split at h
        · rename_i c mi hc
          obtain ⟨hI, hs'⟩ := instG_sound hs hc
          split at h
          · rename_i r hr
            simp only [Bool.and_eq_true] at h
            obtain ⟨ht, h⟩ := h
            rw [hr] at hI
            refine ⟨_, hs', .uninstantiable hI, h, ?_⟩
            cases claim with
            | false => trivial
            | true =>
              simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at ht
              subst ht
              refine ⟨⟨ctx, _, _, hS, hI⟩, fun ctx' ro s' mi' hS' h' => ?_⟩
              obtain rfl := scriptAt_unique hS hS'
              exact (instNF_unique hI h').1.symm
          · cases h
        · cases h
    obtain ⟨ctx', hs', hrun, h', hholds⟩ := step
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simpa [pre] using hholds
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have := cmdsG_holds hs' (scriptAt_snoc hS hrun) h' k cmd' hk
      simpa [pre, List.take_succ_cons, List.append_assoc] using this

/-- **One kernel evaluation proves every claim of a linked script.** -/
theorem scriptHolds_of_kernel {o : GrowOracle} {fuel : Nat} {cmds : List Cmd}
    (h : scriptLK o fuel cmds = true) : ScriptHolds o cmds := by
  unfold scriptLK at h
  rw [scriptG_toBytes] at h
  unfold scriptG at h
  split at h
  · rename_i mt hv
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨himp, h⟩ := h
    split at h
    · rename_i s f hi
      have hi' : instantiateOnce? (Game.importStore []) Spectest.module [] = some (s, f, none) :=
        hi
      have hc := Game.instantiateOnce?_configOk Game.importStore_nil_ok (validate?_sound hv)
        (by rw [himp]; exact .nil) hi'
      have hS : ScriptAt o [] { store := s, regs := [("spectest", f.module)] } :=
        ⟨_, ⟨s, f, hi', rfl⟩, .nil _⟩
      intro k cmd hk
      simpa using cmdsG_holds (ConfigOk.storeOk hc) hS h k cmd hk
    · cases h
  · cases h

/-! ## Termination -/

theorem reaches_always {o : GrowOracle} {pre : List Cmd} {act : Action} {r : Result}
    (h : Reaches o pre act r) : Always o pre act r := by
  obtain ⟨ctx, s, hS, hA⟩ := h
  intro ctx' hS' t name args mi a hact hm ha
  obtain rfl := scriptAt_unique hS hS'
  subst hact
  generalize hro : (some r : Option Result) = ro at hA
  cases hA with
  | invoke hm' ha' hc =>
    rw [hm] at hm'
    cases hm'
    rw [ha] at ha'
    cases ha'
    obtain ⟨hdiv, hext⟩ := nf_always hc.1 hc.2
    exact ⟨hdiv, fun c' hc' => ⟨_, hext c' hc', hc, rfl⟩⟩

/-! ## Functions with an empty body -/

/-- **A function whose body is empty returns no values and leaves the store unchanged**: invoked
with arguments of its parameter count, it reaches the empty code in the same store, a host-free
normal form. -/
theorem emptyBody_nf {o : GrowOracle} {s : Store Nat} {a : Nat} {fi : FuncInst Nat}
    {x : TypeIdx} {args : List Val} {ps : List CValType} (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm ⟨x, [], []⟩) (ht : fi.type.funcType? = some (ps, []))
    (hn : args.length = ps.length) : NF o (invoke s a args) ⟨s, {}, []⟩ := by
  unfold DefType.funcType? at ht
  split at ht
  · rename_i P Rs hex
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨hP, hR⟩ := ht
    have hlen : Rs.length = 0 := by simp [Ty.length, hR]
    have he : Expand fi.type (.func P Rs) := Expand.iff.mpr hex
    have hinv : invoke s a args =
        ⟨s, {}, vals args ++ [.ref (.func a), .callRefType fi.type]⟩ := by
      simp [invoke, hf]
    have h₁ : Step (profile o) Det.noHost (invoke s a args)
        ⟨s, {}, [.frame Rs.length (Frame.forCall fi.module args [])
          [.label Rs.length [] (expression [])]]⟩ := by
      rw [hinv]
      exact Step.callRefFunc (code := ⟨x, [], []⟩) trivial hf he (by rw [hn, ← hP]; rfl) hcode
    have h₂ : Step (profile o) Det.noHost
        ⟨s, {}, [.frame Rs.length (Frame.forCall fi.module args [])
          [.label Rs.length [] (expression [])]]⟩
        ⟨s, {}, [.frame Rs.length (Frame.forCall fi.module args []) (vals [])]⟩ :=
      Step.ctxtFrame (Step.labelVals (vs := []))
    have h₃ : Step (profile o) Det.noHost
        ⟨s, {}, [.frame Rs.length (Frame.forCall fi.module args []) (vals [])]⟩
        ⟨s, {}, vals []⟩ :=
      Step.frameVals (by rw [hlen]; rfl)
    exact ⟨.tail (.tail (.single h₁) h₂) h₃, fun c hc => Det.not_step_vals (W := []) hc⟩
  · cases ht

theorem mem_exportFuncAddrs {mi : ModuleInst} {name : String} {a : Nat}
    (h : exportFunc? mi name = some a) : a ∈ Game.exportFuncAddrs mi := by
  unfold exportFunc? at h
  split at h
  · rename_i n a' hx
    cases h
    unfold Game.exportFuncAddrs
    exact List.mem_filterMap.mpr ⟨_, List.mem_of_find?_eq_some hx, rfl⟩
  · cases h

theorem argsOk_length : ∀ {vs : List Val} {ps : List CValType},
    Silmaril.Project.Shapes.WasmWast.argsOk vs ps = true → vs.length = ps.length
  | [], [], _ => rfl
  | .num _ :: vs, _ :: ps, h => by
    simp only [Silmaril.Project.Shapes.WasmWast.argsOk, Bool.and_eq_true] at h
    simp [argsOk_length h.2]
  | [], _ :: _, h => by simp [Silmaril.Project.Shapes.WasmWast.argsOk] at h
  | _ :: _, [], h => by cases ‹Val› <;> simp [Silmaril.Project.Shapes.WasmWast.argsOk] at h
  | .vec _ :: _, _ :: _, h => by simp [Silmaril.Project.Shapes.WasmWast.argsOk] at h
  | .ref _ :: _, _ :: _, h => by simp [Silmaril.Project.Shapes.WasmWast.argsOk] at h

/-- **The print functions of the `spectest` instance return no values and leave the store
unchanged**, in every store that holds them at their address. -/
theorem print_nf (hk : Spectest.printsEmptyB = true) {o : GrowOracle} {ctx₀ : CtxR ByteArray}
    (h₀ : Init ctx₀) {mi : ModuleInst} (hmi : lookup ctx₀.regs "spectest" = some mi)
    {name : String} {a : Nat} (ha : exportFunc? mi name = some a) {fi : FuncInst Nat}
    (hf : ctx₀.store.funcs[a]? = some fi) {s : Store Nat} (hs : s.funcs[a]? = some fi)
    {args : List Val} (hargs : invokeOkB s a args = true) :
    NF o (invoke s a args) ⟨s, {}, []⟩ := by
  obtain ⟨s₀, f, hi, rfl⟩ := h₀
  simp only [lookup, List.find?, beq_self_eq_true, Option.map_some, Option.some.injEq] at hmi
  subst hmi
  unfold Spectest.printsEmptyB at hk
  split at hk
  · rename_i sK fK hK
    have hb := instantiateOnce?_toBytes importStoreKM Spectest.module []
    rw [hK] at hb
    have hb' : instantiateOnce? (Game.importStore []) Spectest.module [] =
        some (sK.toBytes, fK, none) := hb.symm
    rw [hi] at hb'
    simp only [Option.some.injEq, Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl, -⟩ := hb'
    simp only [Bool.and_eq_true] at hk
    have hall : Spectest.printsEmpty sK.toBytes f.module = true := hk.1
    unfold Spectest.printsEmpty at hall
    have ha' := List.all_eq_true.mp hall a (mem_exportFuncAddrs ha)
    simp only at hf
    rw [hf] at ha'
    simp only [Bool.and_eq_true] at ha'
    obtain ⟨hc, ht⟩ := ha'
    split at hc
    · rename_i g hg
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
      obtain ⟨hl, hbd⟩ := hc
      split at ht
      · rename_i ps rs hft
        simp only [List.isEmpty_iff] at ht
        subst ht
        unfold invokeOkB at hargs
        rw [hs] at hargs
        simp only [hft] at hargs
        obtain ⟨x, l, b⟩ := g
        change l = [] at hl
        change b = [] at hbd
        subst hl hbd
        exact emptyBody_nf hs hg hft (argsOk_length hargs)
      · cases ht
    · cases hc
  · cases hk

/-! ## Unlinkable modules -/

theorem unlinkable_not_instantiate {o : GrowOracle} {pre : List Cmd} {m : Module}
    (h : Unlinkable o pre m) {ctx : CtxR ByteArray} (hS : ScriptAt o pre ctx) {xas : List ExternAddr}
    (hr : resolve? ctx.regs m.imports = some xas) {P : Silmaril.Wasm.Numerics.Profile}
    {host : HostSemantics Nat} {c : Config Nat} : ¬ Instantiate P host ctx.store m xas c := by
  intro hI
  obtain ⟨xtE, xtI, hm, hx⟩ := hI.valid
  exact (h.2 ctx hS).2 ⟨xtI, xtE⟩ xas hm hr hx

end Silmaril.Proofs.Project.Shapes.WasmWastLink

end
