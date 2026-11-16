module

public import Silmaril.Project.Shapes.WasmWast.Defs
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.SingleThreaded.Exec.StatusComplete
public import Silmaril.Wasm.SingleThreaded.Determinism.Join
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.Verify.Kernel.Thms
public import Silmaril.Wasm.Execution.MemRep.Inst.Thms
import Silmaril.Wasm.Binary.Core.DecodeSound
import Silmaril.Wasm.Validation.Check.ValidateFinal

/-!
# Proofs: WAST script commands from one kernel evaluation

* `storeOk_of_inst`: the store of an instantiated module (valid, no imports, scalar function
  exports) is well typed, through `Silmaril.Wasm.Game.IsInstance.ok`;
* `invokeOk_of_invokeOkB`: typed arguments give the premise `InvokeOk` of `$invoke`;
* `actK_sound`: a stopped run of `runInvokeK` at a result is a host-free normal form, and its
  store is well typed (`runInvoke?_steps_noHost`, `runInvoke?_stopped`, `runInvoke?_sound`);
* `invokeNF_unique`: host-free normal forms of an invocation are unique (`DStep.join'`,
  `nf_unique_of_join`), hence `scriptAt_unique`: a script reaches at most one state;
* `scriptHolds_of_kernel`: `scriptK … = true` gives `ScriptHolds`;
* `scriptK_of_scriptKM`: `scriptKM … = true` (the checker on `KMem` stores) gives
  `scriptK … = true`, by `instantiateOnce?_toBytes` and `runI_toBytes`;
* `reaches_always`: at `profile o` one run of a command to a result rules out infinite runs of
  it and extends every finite run to that result (`Det.DStep.join'`, `Det.DStep.shrink`).
* `validatorRejects_not_valid`: a validator rejection of the module the decoder reads excludes
  every valid module the bytes encode (`decode?_sound`, `Binary.Core.functional`,
  `validate?_complete`).
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.WasmWast

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Project.Shapes.WasmWast

/-! ## Instances -/

theorem forall₂_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp at h; subst h; exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        have h' : b :: bs = l' := by simpa [ha, hl] using h
        subst h'
        exact .cons ha (forall₂_of_mapM hl)

/-- The store of an instantiated module with no imports and scalar function exports is well
typed. -/
theorem storeOk_of_inst {m : Module} {mt : CModuleType} {s : Store Nat} {f : Frame}
    (hv : validate? m = some mt) (himp : mt.imports = [])
    (hi : instantiateOnce? (Game.importStore []) m [] = some (s, f, none))
    (hx : exportsScalar s f.module = true) : StoreOk s := by
  unfold exportsScalar at hx
  obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.mp hx
  have hI : Game.IsInstance m mt ⟨[], ts, Game.exportFuncAddrs f.module, s⟩ := by
    refine ⟨hv, by simp [himp], by simp [himp, CExternType.funcs], ⟨f, ?_, rfl⟩, ?_⟩
    · rw [himp]
      exact hi
    · refine (forall₂_of_mapM hts).imp fun a ft h => ?_
      cases hf : s.funcs[a]? with
      | none => simp [hf] at h
      | some fi => exact ⟨fi, rfl, by simpa [hf] using h⟩
  exact hI.ok.storeOk

/-! ## Invocations -/

theorem valOk_of_argsOk {s : Store Nat} :
    ∀ {vs : List Val} {ps : List CValType}, argsOk vs ps = true → List.Forall₂ (ValOk s) vs ps
  | [], [], _ => .nil
  | .num n :: vs, p :: ps, h => by
    simp only [argsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact .cons (.num n) (valOk_of_argsOk h)
  | [], _ :: _, h => by simp [argsOk] at h
  | _ :: _, [], h => by cases ‹Val› <;> simp [argsOk] at h
  | .vec _ :: _, _ :: _, h => by simp [argsOk] at h
  | .ref _ :: _, _ :: _, h => by simp [argsOk] at h

theorem invokeOk_of_invokeOkB {s : Store Nat} {a : Nat} {args : List Val}
    (h : invokeOkB s a args = true) : InvokeOk s a args := by
  unfold invokeOkB at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i ps rs hft
      unfold DefType.funcType? at hft
      split at hft
      · rename_i P R hex
        simp only [Option.some.injEq, Prod.mk.injEq] at hft
        obtain ⟨rfl, rfl⟩ := hft
        exact ⟨fi, P, R, hfi, Expand.iff.mpr hex, valOk_of_argsOk h⟩
      · cases hft
    · cases h
  · cases h

/-- A stopped kernel run at a result is a host-free normal form with a well-typed store. -/
theorem actK_sound {o : GrowOracle} {fuel : Nat} {mi : ModuleInst} {s : Store Nat}
    {act : Action} {c : Config Nat} (hs : StoreOk s) (h : actK o fuel mi s act = some c) :
    ∃ a, exportFunc? mi act.name = some a ∧ InvokeNF o s a act.args c ∧
      (∃ r, c.outcome? = some r) ∧ StoreOk c.store := by
  unfold actK at h
  split at h
  · rename_i a ha
    split at h
    · rename_i hok
      have hi := invokeOk_of_invokeOkB hok
      split at h
      · rename_i c' r hrun
        cases h
        rw [Silmaril.Wasm.Verify.Kernel.runInvokeK_eq] at hrun
        obtain ⟨-, hr⟩ := Exec.InvokeRun.runInvoke?_eq_some hrun
        have hst := Exec.InvokeRun.runInvoke?_steps_noHost hs hi hrun
        have hnf := (Exec.InvokeRun.runInvoke?_stopped hs hi hrun).2
        obtain ⟨-, ⟨_, _, _, _, _, hok'⟩, -⟩ := Exec.InvokeRun.runInvoke?_sound hs hi hrun
        exact ⟨a, ha, ⟨hst, hnf⟩, ⟨r, hr.symm⟩, ConfigOk.storeOk hok'⟩
      · cases h
    · cases h
  · cases h

/-- Host-free normal forms of an invocation under `profile o` are unique. -/
theorem invokeNF_unique {o : GrowOracle} {s : Store Nat} {a : Nat} {args : List Val}
    {c c' : Config Nat} (h : InvokeNF o s a args c) (h' : InvokeNF o s a args c') : c = c' :=
  nf_unique_of_join (R := Det.DStep o) (fun ha hb => Det.DStep.join' ha hb) h.1 h'.1 h.2 h'.2

/-! ## Scripts -/

theorem instance_unique {m : Module} {s s' : Store Nat} {mi mi' : ModuleInst}
    (h : Instance m s mi) (h' : Instance m s' mi') : s = s' ∧ mi = mi' := by
  obtain ⟨-, f, hf, rfl⟩ := h
  obtain ⟨-, f', hf', rfl⟩ := h'
  rw [hf] at hf'
  simp only [Option.some.injEq, Prod.mk.injEq] at hf'
  obtain ⟨rfl, rfl, -⟩ := hf'
  exact ⟨rfl, rfl⟩

theorem run_unique {o : GrowOracle} {mi : ModuleInst} {s s₁ s₂ : Store Nat} {acts : List Action}
    (h₁ : Run o mi s acts s₁) (h₂ : Run o mi s acts s₂) : s₁ = s₂ := by
  induction h₁ with
  | nil => cases h₂; rfl
  | cons ha hc _ _ ih =>
    cases h₂ with
    | cons ha' hc' _ h' =>
      rw [ha] at ha'
      cases ha'
      cases invokeNF_unique hc hc'
      exact ih h'

theorem run_append {o : GrowOracle} {mi : ModuleInst} {s s₁ s₂ : Store Nat}
    {l₁ l₂ : List Action} (h₁ : Run o mi s l₁ s₁) (h₂ : Run o mi s₁ l₂ s₂) :
    Run o mi s (l₁ ++ l₂) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons ha hc hr _ ih => exact .cons ha hc hr (ih h₂)

/-- A script reaches at most one state. -/
theorem scriptAt_unique {o : GrowOracle} {m : Module} {pre : List Action}
    {mi mi' : ModuleInst} {s s' : Store Nat} (h : ScriptAt o m pre mi s)
    (h' : ScriptAt o m pre mi' s') : mi = mi' ∧ s = s' := by
  obtain ⟨s₀, hI, hr⟩ := h
  obtain ⟨s₀', hI', hr'⟩ := h'
  obtain ⟨rfl, rfl⟩ := instance_unique hI hI'
  exact ⟨rfl, run_unique hr hr'⟩

/-- The claim of one command, at the unique state of the script before it. -/
theorem holds_of_run {o : GrowOracle} {m : Module} {pre : List Action} {mi : ModuleInst}
    {s : Store Nat} {act : Action} {a : Nat} {c : Config Nat} {r : Result}
    (hS : ScriptAt o m pre mi s) (ha : exportFunc? mi act.name = some a)
    (hc : InvokeNF o s a act.args c) (hr : c.outcome? = some r) :
    Reaches o m pre act r ∧ Only o m pre act r := by
  refine ⟨⟨mi, s, a, c, hS, ha, hc, hr⟩, fun mi' s' a' c' hS' ha' hc' => ?_⟩
  obtain ⟨rfl, rfl⟩ := scriptAt_unique hS hS'
  rw [ha] at ha'
  cases ha'
  rw [← invokeNF_unique hc hc']
  exact hr

theorem cmdsK_holds {o : GrowOracle} {fuel : Nat} {m : Module} {mi : ModuleInst} :
    ∀ {cmds : List Cmd} {done : List Action} {s : Store Nat}, StoreOk s →
      ScriptAt o m done mi s → cmdsK o fuel mi s cmds = true →
      ∀ k (cmd : Cmd), cmds[k]? = some cmd → cmd.Holds o m (done ++ pre cmds k)
  | [], _, _, _, _, _, k, _, hk => by simp at hk
  | cmd :: cmds, done, s, hs, hS, h, k, cmd', hk => by
    unfold cmdsK at h
    split at h
    · rename_i c hc
      obtain ⟨a, ha, hnf, ⟨r, hr⟩, hs'⟩ := actK_sound hs hc
      simp only [Bool.and_eq_true] at h
      obtain ⟨he, h⟩ := h
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [pre, List.take_zero, List.map_nil, List.append_nil]
        rcases cmd with ⟨act, _ | e⟩
        · trivial
        · simp only [decide_eq_true_eq] at he
          have := holds_of_run hS ha hnf he
          cases e <;> exact this
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨s₀, hI, hrun⟩ := hS
        have hS' : ScriptAt o m (done ++ [cmd.act]) mi c.store :=
          ⟨s₀, hI, run_append hrun (.cons ha hnf hr (.nil _))⟩
        have := cmdsK_holds hs' hS' h k cmd' hk
        simpa [pre, List.take_succ_cons, List.append_assoc] using this
    · cases h

/-- **One kernel evaluation proves every command of a script.** -/
theorem scriptHolds_of_kernel {o : GrowOracle} {fuel : Nat} {m : Module} {cmds : List Cmd}
    (h : scriptK o fuel m cmds = true) : ScriptHolds o m cmds := by
  unfold scriptK at h
  split at h
  · rename_i mt hv
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨himp, h⟩ := h
    split at h
    · rename_i s f hi
      simp only [Bool.and_eq_true] at h
      obtain ⟨hx, h⟩ := h
      have hs := storeOk_of_inst hv himp hi hx
      have hS : ScriptAt o m [] f.module s :=
        ⟨s, ⟨⟨mt.exports, by rw [← himp]; exact validate?_sound hv⟩, f, hi, rfl⟩, .nil _⟩
      intro k cmd hk
      simpa using cmdsK_holds hs hS h k cmd hk
    · cases h
  · cases h

/-! ## From `KMem` stores to `ByteArray` stores -/

section KM

open Silmaril.Wasm.Execution (KMem MemRep LawfulMemRep)

theorem importStoreKM_toBytes : importStoreKM.toBytes = Game.importStore [] := rfl

theorem exportsScalar_toBytes {R : Type} [MemRep R] (s : Store Nat R) (mi : ModuleInst) :
    exportsScalar s.toBytes mi = exportsScalar s mi := rfl

theorem invokeOkB_toBytes {R : Type} [MemRep R] (s : Store Nat R) (a : Nat) (args : List Val) :
    invokeOkB s.toBytes a args = invokeOkB s a args := rfl

/-- `runInvokeK` on `s.toBytes` is `runInvokeKR` on `s`, read through `toBytes`. -/
theorem runInvokeK_toBytes {R : Type} [MemRep R] [LawfulMemRep R] (o : GrowOracle) (n : Nat)
    (s : Store Nat R) (a : Nat) (vs : List Val) :
    Silmaril.Wasm.Verify.Kernel.runInvokeK o n s.toBytes a vs =
      (runInvokeKR o n s a vs).map fun p => (p.1.toBytes, p.2.1, p.2.2) := by
  rw [Silmaril.Wasm.Verify.Kernel.runInvokeK_eq]
  have h := Exec.runI_toBytes o n (invoke s a vs)
  have hi : (invoke s a vs).toBytes = invoke s.toBytes a vs := rfl
  rw [hi] at h
  have hk : Silmaril.Wasm.Verify.Kernel.runK (Exec.interpHead (H := Nat) (R := R) o) n
      (invoke s a vs) = Exec.runI o n (invoke s a vs) := by
    rw [Silmaril.Wasm.Verify.Kernel.runK_eq]; rfl
  simp only [Exec.runInvoke?, runInvokeKR, hk, ← h, Option.map_some]
  rfl

theorem actK_of_actKM {o : GrowOracle} {fuel : Nat} {mi : ModuleInst} {s : Store Nat KMem}
    {act : Action} {c : Config Nat KMem} (h : actKM o fuel mi s act = some c) :
    actK o fuel mi s.toBytes act = some c.toBytes := by
  unfold actKM at h
  unfold actK
  split at h
  · simp only [invokeOkB_toBytes]
    split at h
    · rename_i hok
      simp only [hok, ↓reduceIte, runInvokeK_toBytes]
      split at h
      · rename_i c' r hrun
        cases h
        rw [hrun]
        rfl
      · cases h
    · cases h
  · cases h

theorem cmdsK_of_cmdsKM {o : GrowOracle} {fuel : Nat} {mi : ModuleInst} :
    ∀ {cmds : List Cmd} {s : Store Nat KMem}, cmdsKM o fuel mi s cmds = true →
      cmdsK o fuel mi s.toBytes cmds = true
  | [], _, _ => rfl
  | cmd :: cmds, s, h => by
    unfold cmdsKM at h
    unfold cmdsK
    split at h
    · rename_i c hc
      rw [actK_of_actKM hc]
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, cmdsK_of_cmdsKM h.2⟩
    · cases h

/-- **The `KMem` checker implies the `ByteArray` checker.** -/
theorem scriptK_of_scriptKM {o : GrowOracle} {fuel : Nat} {m : Module} {cmds : List Cmd}
    (h : scriptKM o fuel m cmds = true) : scriptK o fuel m cmds = true := by
  unfold scriptKM at h
  unfold scriptK
  split at h
  · simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    split at h2
    · rename_i s f hi
      have hb := instantiateOnce?_toBytes importStoreKM m []
      rw [hi, importStoreKM_toBytes] at hb
      rw [← hb]
      simp only [Option.map_some, Bool.and_eq_true] at h2 ⊢
      exact ⟨by rw [exportsScalar_toBytes]; exact h2.1, cmdsK_of_cmdsKM h2.2⟩
    · cases h2
  · cases h

end KM

/-! ## Termination

Core reduction at `profile o` is not a function (a trap bubbles out at several context depths),
but two different successors of a configuration are joinable in at most one step each
(`Det.DStep.join'`), and both have strictly smaller code (`Det.DStep.shrink`). Then a
configuration with a run to a normal form has no infinite run (`nsteps_normal_not_infinite`,
the abstract argument of `Silmaril.Proofs.Wasm.Game.nsteps_normal_not_infinite`, restated here
because it lives in another topic's proof modules), and every finite run extends to that normal
form (`nsteps_of_steps`). -/

/-- If peaks of `R` are joinable in at most one step on each side and the two sides of a
non-trivial peak are strictly smaller than its top under `μ`, then a configuration with a
counted path to a normal form has no infinite trace. Lexicographic induction on (path length,
`μ`). -/
theorem nsteps_normal_not_infinite {α : Type _} {R : α → α → Prop} (μ : α → Nat)
    (hj : ∀ {x a b : α}, R x a → R x b → Det.Join R a b)
    (hs : ∀ {x a b : α}, R x a → R x b → a = b ∨ μ a < μ x)
    {y : α} (hy : ∀ z, ¬ R y z) :
    ∀ (k : Nat) (x : α), NSteps R k x y → ¬ InfiniteTrace R x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  suffices h : ∀ (n : Nat) (x : α), μ x = n → NSteps R k x y → ¬ InfiniteTrace R x from
    fun x => h _ x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro x hn hpath hinf
  obtain ⟨x₁, hx₁, hinf₁⟩ := hinf.unfold
  obtain ⟨m, hm, hpath₁⟩ := NSteps.of_step_join hj hy hpath hx₁
  cases hpath with
  | refl => exact hy _ hx₁
  | @head _ a _ k' hxa hrest =>
    rcases hs hx₁ hxa with heq | hlt
    · exact ihk k' (Nat.lt_succ_self k') _ (heq ▸ hrest) hinf₁
    · rcases Nat.lt_or_ge m (k' + 1) with hlt' | hge
      · exact ihk m hlt' x₁ hpath₁ hinf₁
      · have hmk : m = k' + 1 := le_antisymm hm hge
        exact ihn (μ x₁) (by omega) x₁ rfl (hmk ▸ hpath₁) hinf₁

/-- Under the `Join` diamond, every configuration reachable from one with a counted path to a
normal form still has a counted path to it. -/
theorem nsteps_of_steps {α : Type _} {R : α → α → Prop}
    (hj : ∀ {x a b : α}, R x a → R x b → Det.Join R a b) {y : α} (hy : ∀ z, ¬ R y z)
    {k : Nat} {x x' : α} (hk : NSteps R k x y) (h : Relation.ReflTransGen R x x') :
    ∃ m, NSteps R m x' y := by
  induction h with
  | refl => exact ⟨k, hk⟩
  | tail _ hs ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨m', -, hm'⟩ := NSteps.of_step_join hj hy hm hs
    exact ⟨m', hm'⟩

theorem nsteps_to_rtg {α : Type _} {R : α → α → Prop} {k : Nat} {x y : α}
    (h : NSteps R k x y) : Relation.ReflTransGen R x y := by
  induction h with
  | refl => exact .refl
  | head hxy _ ih => exact .head hxy ih

theorem dstep_shrink {o : GrowOracle} {x a b : Config Nat} (ha : Det.DStep o x a)
    (hb : Det.DStep o x b) : a = b ∨ sizeOf a.code < sizeOf x.code := by
  rcases x with ⟨s, f, code⟩
  rcases Det.DStep.shrink _ s f code a b rfl ha hb with h | ⟨-, -, hl, -⟩
  · exact .inl h
  · exact .inr hl

/-- A host-free normal form of an invocation excludes infinite runs of it, and every finite run
of it extends to that normal form. -/
theorem invokeNF_always {o : GrowOracle} {s : Store Nat} {a : Nat} {args : List Val}
    {c : Config Nat} (h : InvokeNF o s a args c) :
    ¬ Diverges (profile o) Det.noHost (invoke s a args) ∧
      ∀ c', Steps (profile o) Det.noHost (invoke s a args) c' →
        Steps (profile o) Det.noHost c' c := by
  obtain ⟨k, hk⟩ := NSteps.of_rtg (R := Det.DStep o) h.1
  refine ⟨nsteps_normal_not_infinite (R := Det.DStep o) (fun c : Config Nat => sizeOf c.code)
    (fun ha hb => Det.DStep.join' ha hb) (fun ha hb => dstep_shrink ha hb) h.2 k _ hk,
    fun c' hc' => ?_⟩
  obtain ⟨m, hm⟩ := nsteps_of_steps (R := Det.DStep o) (fun ha hb => Det.DStep.join' ha hb)
    h.2 hk hc'
  exact nsteps_to_rtg hm

/-- **At `profile o`, one run to a normal form decides every run.** -/
theorem reaches_always {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {r : Result} (h : Reaches o m pre act r) : Always o m pre act r := by
  obtain ⟨mi, s, a, c, hS, ha, hc, hr⟩ := h
  intro mi' s' a' hS' ha'
  obtain ⟨rfl, rfl⟩ := scriptAt_unique hS hS'
  rw [ha] at ha'
  cases ha'
  obtain ⟨hdiv, hext⟩ := invokeNF_always hc
  exact ⟨hdiv, fun c' hc' => ⟨c, hext c' hc', hc, hr⟩⟩

/-! ## Rejections -/

theorem validatorRejects_not_valid {b : ByteArray} (h : ValidatorRejects b) {m : Module}
    (hm : Binary.Core.Encodes b.data.toList m) : ¬ ModuleValid m := by
  obtain ⟨m', hd, hv⟩ := h
  rintro ⟨mt, hok⟩
  obtain rfl := Binary.Core.functional (Binary.Core.decode?_sound hd) hm
  rw [validate?_complete hok] at hv
  cases hv

end Silmaril.Proofs.Project.Shapes.WasmWast

end
