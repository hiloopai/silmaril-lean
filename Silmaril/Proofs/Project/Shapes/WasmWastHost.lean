module

public import Silmaril.Project.Shapes.WasmWastHost.Defs
public import Silmaril.Proofs.Project.Shapes.WasmWastLink
public import Silmaril.Wasm.Abstract.HostDet.Thms
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Store.Defs
public import Silmaril.Wasm.Execution.MemRep.Sim.Thms

/-!
# Proofs: linked WAST scripts against the typed `spectest` host

* `lookup?_toBytes`, `resolve?_toBytes`, `runHG_toBytes`, …, `scriptG_toBytes`: the checker on
  `KMem` stores agrees with the checker on `ByteArray` stores.
* `storeOk_allocGlobal`, `lookup?_ok`, `resolve?_ok`: resolution keeps the store typed (fresh host
  functions by `allocHost_storeOk`, fresh immutable numeric globals here).
* `hostDet`, `hostTyped`: the host has at most one outcome per call, and its answers are typed
  (the guard `printsTyped`).
* `runHG_sound`: a stopped logged run of a typed configuration is a normal form under
  `Spectest.host`, reached by an `LStep` run, and stays typed: between host calls,
  `WasmWastLink.runG_sound`; at a callout the host answers are plugged in with
  `Ctx.fill_callout_typed`.
* `actNF_unique`, `instNF_unique`, `cmdRun_unique`, `scriptAt_unique`: at `profile o` a script
  prefix reaches at most one context, its log included (`LSteps.nf_unique_of_hostDet`).
* `scriptHolds_of_kernel`, `reaches_always`, `print_nf`, `unlinkable_not_instantiate`.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.Shapes.WasmWastHost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Abstract Silmaril.Project.Shapes.WasmWastHost
open Silmaril.Project.Shapes.WasmWast (Expect exportFunc? invokeOkB importStoreKM)
open Silmaril.Project.Shapes.WasmWastLink (Names lookup Target bindName exportAddr? Action Cmd
  runG)
open Silmaril.Proofs.Project.Shapes.WasmWastLink (runG_toBytes runG_sound)
open Silmaril.Wasm.Execution (KMem MemRep LawfulMemRep)

/-! ## From `KMem` stores to `ByteArray` stores -/

section ToBytes

variable {R : Type} [MemRep R] [LawfulMemRep R]

omit [LawfulMemRep R] in
theorem lookup?_toBytes (sh : ModuleInst) (s : Store Nat R) (name : String) :
    (Spectest.lookup? sh s name).map (fun p => (p.1.toBytes, p.2)) =
      Spectest.lookup? sh s.toBytes name := by
  unfold Spectest.lookup?
  cases Spectest.entry? name with
  | none => rfl
  | some e =>
    cases e with
    | print k ps => rfl
    | global t b => rfl
    | shared => cases exportAddr? sh name <;> rfl

omit [LawfulMemRep R] in
theorem resolve?_toBytes (regs : Regs) :
    ∀ (s : Store Nat R) (imps : List Import),
      (resolve? regs s imps).map (fun p => (p.1.toBytes, p.2)) = resolve? regs s.toBytes imps
  | s, [] => rfl
  | s, i :: is => by
    simp only [resolve?]
    cases lookupReg regs i.moduleName with
    | none => rfl
    | some r =>
      cases r with
      | inst mi =>
        simp only
        cases exportAddr? mi i.name with
        | none => rfl
        | some xa =>
          simp only
          rw [← resolve?_toBytes regs s is]
          cases resolve? regs s is <;> rfl
      | spectest sh =>
        simp only
        rw [← lookup?_toBytes]
        cases Spectest.lookup? sh s i.name with
        | none => rfl
        | some p =>
          obtain ⟨s₁, xa⟩ := p
          simp only [Option.map_some]
          rw [← resolve?_toBytes regs s₁ is]
          cases resolve? regs s₁ is <;> rfl

theorem runHG_toBytes (o : GrowOracle) (fuel : Nat) :
    ∀ (n : Nat) (c : Config Nat R) (l : HostLog Nat),
      (runHG o fuel n (c, l)).map (fun p => (p.1.toBytes, p.2)) = runHG o fuel n (c.toBytes, l)
  | 0, _, _ => rfl
  | n + 1, c, l => by
    simp only [runHG]
    rw [← runG_toBytes]
    cases runG o fuel c with
    | none => rfl
    | some c' =>
      simp only [Option.map_some]
      rw [show c'.toBytes.store = c'.store.toBytes from rfl,
        show c'.toBytes.code = c'.code from rfl, Exec.decompose?_toBytes]
      cases decompose? c'.store c'.code with
      | none => rfl
      | some d =>
        obtain ⟨E, a, k, args⟩ := d
        simp only
        rw [show Spectest.answers c'.store.toBytes k = Spectest.answers c'.store k from rfl]
        cases Spectest.answers c'.store k with
        | false => rfl
        | true =>
          simp only [ite_true]
          exact runHG_toBytes o fuel n _ _

theorem instG_toBytes (o : GrowOracle) (fuel : Nat) (ctx : CtxR R) (m : Module) :
    (instG o fuel ctx m).map (fun p => ((p.1.1.toBytes, p.1.2), p.2)) =
      instG o fuel ctx.toBytes m := by
  simp only [instG, CtxR.toBytes]
  cases validate? m with
  | none => rfl
  | some mt =>
    simp only
    rw [← resolve?_toBytes]
    cases resolve? ctx.regs ctx.store m.imports with
    | none => rfl
    | some p =>
      obtain ⟨s₀, xas⟩ := p
      simp only [Option.map_some, externAddrsOk?_toBytes]
      cases externAddrsOk? s₀ xas mt.imports with
      | false => rfl
      | true =>
        simp only [ite_true, ← instantiateOnce?_toBytes]
        cases instantiateOnce? s₀ m xas with
        | none => rfl
        | some p =>
          obtain ⟨s, f, st⟩ := p
          simp only [Option.map_some]
          rw [show (⟨s.toBytes, f, startCode st⟩ : Config Nat) =
            Config.toBytes ⟨s, f, startCode st⟩ from rfl, ← runHG_toBytes]
          cases runHG o fuel fuel (⟨s, f, startCode st⟩, ctx.log) <;> rfl

omit [LawfulMemRep R] in
theorem inst?_toBytes (ctx : CtxR R) (t : Target) : ctx.toBytes.inst? t = ctx.inst? t := by
  cases t <;> rfl

theorem actG_toBytes (o : GrowOracle) (fuel : Nat) (ctx : CtxR R) (act : Action) :
    (actG o fuel ctx act).map (fun p => (p.1, p.2.1.toBytes, p.2.2)) =
      actG o fuel ctx.toBytes act := by
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
          rw [show (invoke ctx.toBytes.store a args, ctx.toBytes.log) =
            ((invoke ctx.store a args).toBytes, ctx.log) from rfl, ← runHG_toBytes]
          cases runHG o fuel fuel (invoke ctx.store a args, ctx.log) with
          | none => rfl
          | some p =>
            obtain ⟨c, l⟩ := p
            simp only [Option.map_some, Option.bind_some]
            change _ = (c.outcome?).map fun r => (r, c.store.toBytes, l)
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
            (Result.values [gi.value], ctx.store.toBytes, ctx.log)
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
    rw [← resolve?_toBytes]
    cases resolve? ctx.regs ctx.store m.imports with
    | none => rfl
    | some p =>
      obtain ⟨s₀, xas⟩ := p
      simp only [Option.map_some, externAddrsOk?_toBytes]

theorem cmdsG_toBytes (o : GrowOracle) (fuel : Nat) :
    ∀ (ctx : CtxR R) (cmds : List Cmd), cmdsG o fuel ctx cmds = cmdsG o fuel ctx.toBytes cmds
  | _, [] => rfl
  | ctx, .module name m :: cmds => by
    simp only [cmdsG]
    rw [← instG_toBytes]
    cases instG o fuel ctx m with
    | none => rfl
    | some p =>
      obtain ⟨⟨c, l⟩, mi⟩ := p
      simp only [Option.map_some]
      rw [cmdsG_toBytes o fuel _ cmds]
      rfl
  | ctx, .register as t :: cmds => by
    simp only [cmdsG]
    change _ = match ctx.inst? t with
      | some mi => cmdsG o fuel { ctx.toBytes with regs := (as, .inst mi) :: ctx.regs } cmds
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
      obtain ⟨r, s, l⟩ := p
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
      obtain ⟨⟨c, l⟩, mi⟩ := p
      simp only [Option.map_some]
      change _ = match c.outcome? with
        | some r => (!claim || decide (r = Result.trap)) &&
            cmdsG o fuel { ctx.toBytes with store := c.store.toBytes, log := l } cmds
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
  cases validate? Spectest.shared with
  | none => rfl
  | some mt =>
    simp only [← instantiateOnce?_toBytes]
    cases instantiateOnce? s₀ Spectest.shared [] with
    | none => rfl
    | some p =>
      obtain ⟨s, f, st⟩ := p
      cases st with
      | none =>
        simp only [Option.map_some]
        rw [cmdsG_toBytes o fuel _ cmds]
        rfl
      | some _ => rfl

theorem runCmdsG_toBytes (o : GrowOracle) (fuel : Nat) :
    ∀ (ctx : CtxR R) (cmds : List Cmd),
      (runCmdsG o fuel ctx cmds).map CtxR.toBytes = runCmdsG o fuel ctx.toBytes cmds
  | _, [] => rfl
  | ctx, .module name m :: cmds => by
    simp only [runCmdsG]
    rw [← instG_toBytes]
    cases instG o fuel ctx m with
    | none => rfl
    | some p =>
      obtain ⟨⟨c, l⟩, mi⟩ := p
      simp only [Option.map_some]
      change _ = if c.outcome? = some (.values []) then runCmdsG o fuel
          { ctx.toBytes with
            store := c.store.toBytes, log := l, cur := some mi, named := bindName name mi ctx.named }
          cmds else none
      split
      · exact runCmdsG_toBytes o fuel _ cmds
      · rfl
  | ctx, .register as t :: cmds => by
    simp only [runCmdsG]
    change _ = match ctx.inst? t with
      | some mi => runCmdsG o fuel { ctx.toBytes with regs := (as, .inst mi) :: ctx.regs } cmds
      | none => none
    cases ctx.inst? t with
    | none => rfl
    | some mi => exact runCmdsG_toBytes o fuel _ cmds
  | ctx, .action act e :: cmds => by
    simp only [runCmdsG]
    rw [← actG_toBytes]
    cases actG o fuel ctx act with
    | none => rfl
    | some p =>
      obtain ⟨r, s, l⟩ := p
      simp only [Option.map_some]
      exact runCmdsG_toBytes o fuel _ cmds
  | ctx, .unlinkable m claim :: cmds => by
    simp only [runCmdsG]
    exact runCmdsG_toBytes o fuel ctx cmds
  | ctx, .uninstantiable m claim :: cmds => by
    simp only [runCmdsG]
    rw [← instG_toBytes]
    cases instG o fuel ctx m with
    | none => rfl
    | some p =>
      obtain ⟨⟨c, l⟩, mi⟩ := p
      simp only [Option.map_some]
      change _ = if c.outcome?.isSome = true then
          runCmdsG o fuel { ctx.toBytes with store := c.store.toBytes, log := l } cmds else none
      split
      · exact runCmdsG_toBytes o fuel _ cmds
      · rfl

theorem logG_toBytes (o : GrowOracle) (fuel : Nat) (s₀ : Store Nat R) (cmds : List Cmd) :
    logG o fuel s₀ cmds = logG o fuel s₀.toBytes cmds := by
  simp only [logG]
  cases validate? Spectest.shared with
  | none => rfl
  | some mt =>
    simp only
    split
    · simp only [← instantiateOnce?_toBytes]
      cases instantiateOnce? s₀ Spectest.shared [] with
      | none => rfl
      | some p =>
        obtain ⟨s, f, st⟩ := p
        cases st with
        | none =>
          simp only [Option.map_some]
          rw [show ({ store := s.toBytes, regs := [("spectest", .spectest f.module)] } : CtxR ByteArray)
            = CtxR.toBytes { store := s, regs := [("spectest", .spectest f.module)] } from rfl,
            ← runCmdsG_toBytes]
          cases runCmdsG o fuel { store := s, regs := [("spectest", .spectest f.module)] } cmds <;>
            rfl
        | some _ => rfl
    · rfl

end ToBytes

/-! ## Typing of resolution -/

/-- Appending an immutable numeric global keeps the store typed and extends it. -/
theorem storeOk_allocGlobal {s : Store Nat} {t : NumType} {b : BitVec t.width} (hs : StoreOk s) :
    StoreOk (allocGlobal s ⟨.const, .num t⟩ (.num ⟨t, b⟩)).1 ∧
      Extend s (allocGlobal s ⟨.const, .num t⟩ (.num ⟨t, b⟩)).1 := by
  simp only [allocGlobal]
  have he : Extend s { s with globals := s.globals ++ [⟨⟨.const, .num t⟩, .num ⟨t, b⟩⟩] } :=
    { Extend.refl hs with
      globals := ExtendsList.of_prefix (List.prefix_append _ _) fun _ _ => ⟨rfl, .inr rfl⟩ }
  have htr : ∀ {x y : FieldVal},
      ImmutReachable { s with globals := s.globals ++ [⟨⟨.const, .num t⟩, .num ⟨t, b⟩⟩] } x y →
      ImmutReachable s x y :=
    fun hr => TM.immutReachable_transfer (s := s)
      (s' := { s with globals := s.globals ++ [⟨⟨.const, .num t⟩, .num ⟨t, b⟩⟩] }) rfl rfl rfl hr
  refine ⟨{ tags := hs.tags, globals := ?_, mems := hs.mems, tables := ?_, funcs := ?_,
             elems := ?_, structs := ?_, arrays := ?_, exns := ?_, acyclicStructs := ?_,
             acyclicArrays := ?_, acyclicExns := ?_, structsClosed := hs.structsClosed,
             arraysClosed := hs.arraysClosed }, he⟩
  · intro gi h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨h₁, h₂⟩ := hs.globals gi h
      exact ⟨h₁, TM.valOk_extend he h₂⟩
    · rw [List.mem_singleton] at h
      subst h
      exact ⟨TyOk.num t, ValOk.num ⟨t, b⟩⟩
  · intro ti h
    exact TM.tableInstOk_extend he (hs.tables ti h)
  · intro fi h
    cases hs.funcs fi h with
    | wasm hdt hm hcode hf hsub => exact .wasm hdt (TM.moduleInstOk_extend hs he hm) hcode hf hsub
    | host hdt he' hcode => exact .host hdt he' hcode
  · intro ei h
    exact TM.elemInstOk_extend he ⟨rfl, .inl rfl⟩ (hs.elems ei h)
  · intro si h
    obtain ⟨fs, hx, hf⟩ := hs.structs si h
    exact ⟨fs, hx, hf.imp fun _ _ h => TM.fieldValOk_extend he h⟩
  · intro ai h
    obtain ⟨ft, hx, hf⟩ := hs.arrays ai h
    exact ⟨ft, hx, fun fv hfv => TM.fieldValOk_extend he (hf fv hfv)⟩
  · intro e h
    obtain ⟨ti, ts, ht, hx, hf⟩ := hs.exns e h
    exact ⟨ti, ts, ht, hx, hf.imp fun _ _ h => TM.valOk_extend he h⟩
  · intro a ha hr
    exact hs.acyclicStructs a ha (htr hr)
  · intro a ha hr
    exact hs.acyclicArrays a ha (htr hr)
  · intro a ha hr
    exact hs.acyclicExns a ha (htr hr)

theorem lookup?_ok {sh : ModuleInst} {s s' : Store Nat} {name : String} {xa : ExternAddr}
    (hs : StoreOk s) (h : Spectest.lookup? sh s name = some (s', xa)) : StoreOk s' := by
  unfold Spectest.lookup? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (Silmaril.Wasm.Component.Engine.Core3.Typed.allocHost_storeOk hs rfl).1
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact (storeOk_allocGlobal hs).1
  · cases hx : exportAddr? sh name with
    | none => rw [hx] at h; cases h
    | some _ =>
      rw [hx] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hs
  · cases h

theorem resolve?_ok {regs : Regs} :
    ∀ {s s' : Store Nat} {imps : List Import} {xas : List ExternAddr}, StoreOk s →
      resolve? regs s imps = some (s', xas) → StoreOk s'
  | s, s', [], xas, hs, h => by
    simp only [resolve?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hs
  | s, s', i :: is, xas, hs, h => by
    simp only [resolve?] at h
    split at h
    · split at h
      · cases hr : resolve? regs s is with
        | none => rw [hr] at h; cases h
        | some p =>
          obtain ⟨s₂, xs⟩ := p
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact resolve?_ok hs hr
      · cases h
    · split at h
      · rename_i s₁ xa hl
        cases hr : resolve? regs s₁ is with
        | none => rw [hr] at h; cases h
        | some p =>
          obtain ⟨s₂, xs⟩ := p
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact resolve?_ok (lookup?_ok hs hl) hr
      · cases h
    · cases h

/-! ## The host -/

/-- **The `spectest` host has at most one outcome per call.** -/
theorem hostDet : HostDet Spectest.host := by
  intro k s vs o₁ o₂ h₁ h₂
  rw [h₁.2, h₂.2]

theorem rs_nil_of_printsTyped {s : Store Nat} {k : Nat} (hp : Spectest.printsTyped s k = true)
    {fi : FuncInst Nat} (hfi : fi ∈ s.funcs) (hc : fi.code = .host k)
    {ps rs : Ty (.list .val)} (he : Expand fi.type (.func ps rs)) : rs.toList = [] := by
  have := List.all_eq_true.mp hp fi hfi
  rw [hc] at this
  simp only [bne_self_eq_false, Bool.false_or] at this
  unfold DefType.funcType? at this
  rw [Expand.iff.mp he] at this
  simpa using this

/-- **The answers of the `spectest` host are typed**: the store is unchanged, and the empty
result has the result type of every host function with that code (`printsTyped`). -/
theorem hostTyped : HostTyped Spectest.host := by
  intro s fi k vs ps rs hs hfi hc he _ out hout
  obtain ⟨hans, rfl⟩ := hout
  simp only [Spectest.answers, Bool.and_eq_true] at hans
  refine ⟨hs, Extend.refl hs, ?_⟩
  show List.Forall₂ (ValOk s) [] rs.toList
  rw [rs_nil_of_printsTyped hans.2 hfi hc he]
  exact .nil

/-! ## Soundness of the logged runs -/

variable {o : GrowOracle}

theorem steps_free_lsteps {c c' : Config Nat}
    (h : Steps (profile o) (fun _ _ _ _ => False) c c') (l : HostLog Nat) :
    LSteps (profile o) Spectest.host (c, l) (c', l) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (.free h)

/-- At a configuration with no host-free step, a host step is an answer of the host at the
callout. -/
theorem no_step_of {c : Config Nat} (hnf : ∀ x, ¬ Step (profile o) (fun _ _ _ _ => False) c x)
    (hno : ∀ E a k args, decompose? c.store c.code = some (E, a, k, args) →
      Spectest.answers c.store k = false) :
    ∀ x, ¬ Step (profile o) Spectest.host c x := by
  intro x hx
  rcases Step.split_host hx with hf | ⟨E, a, k, args, hd, ⟨s', r, hr, -⟩ | ⟨hv, -⟩⟩
  · exact hnf _ hf
  · have h1 := hr.1
    rw [hno E a k args hd] at h1
    cases h1
  · cases hv.2

theorem runHG_sound {fuel : Nat} :
    ∀ (n : Nat) {c c' : Config Nat} {l l' : HostLog Nat} {ts : List CValType},
      ConfigOk c ts → runHG o fuel n (c, l) = some (c', l') →
        NF o (c, l) (c', l') ∧ ConfigOk c' ts
  | 0, _, _, _, _, _, _, h => by cases h
  | n + 1, c, c', l, l', ts, hc, h => by
    simp only [runHG] at h
    cases hrun : runG o fuel c with
    | none => rw [hrun] at h; cases h
    | some c₁ =>
      rw [hrun] at h
      simp only at h
      obtain ⟨⟨hst, hnf⟩, hok⟩ := runG_sound hc hrun
      have hst' := steps_free_lsteps (o := o) hst l
      cases hd : decompose? c₁.store c₁.code with
      | none =>
        rw [hd] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨⟨hst', no_step_of hnf fun E a k args hd' => ?_⟩, hok⟩
        rw [hd] at hd'
        cases hd'
      | some d =>
        obtain ⟨E, a, k, args⟩ := d
        rw [hd] at h
        simp only at h
        cases hans : Spectest.answers c₁.store k with
        | false =>
          rw [hans] at h
          simp only [Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨⟨hst', no_step_of hnf fun E' a' k' args' hd' => ?_⟩, hok⟩
          rw [hd] at hd'
          simp only [Option.some.injEq, Prod.mk.injEq] at hd'
          obtain ⟨-, -, rfl, -⟩ := hd'
          exact hans
        | true =>
          rw [hans] at h
          simp only [ite_true] at h
          have hstep : LStep (profile o) Spectest.host (c₁, l)
              (⟨c₁.store, c₁.frame, E.fill []⟩, l ++ [(k, args)]) :=
            LStep.call (r := .values []) hd ⟨hans, rfl⟩
          obtain ⟨fi, yy, ps, rs, hf, hcode, hyy, he, hn, hfill⟩ := decompose?_sound hd
          have hs₁ : StoreOk c₁.store := ConfigOk.storeOk hok
          simp only [Spectest.answers, Bool.and_eq_true] at hans
          have hrs := rs_nil_of_printsTyped hans.2 (List.mem_of_getElem? hf) hcode he
          have hok₁ : ConfigOk ⟨c₁.store, c₁.frame, E.fill (vals [])⟩ ts := by
            rcases c₁ with ⟨s₁, f₁, code₁⟩
            simp only at hfill hok
            subst hfill
            exact Ctx.fill_callout_typed hok hf he hyy hn hs₁ (Extend.refl hs₁)
              (by rw [hrs]; exact .nil)
          obtain ⟨⟨hrest, hnf'⟩, hok'⟩ := runHG_sound n hok₁ h
          exact ⟨⟨(hst'.tail hstep).trans hrest, hnf'⟩, hok'⟩

theorem instG_sound {fuel : Nat} {ctx : CtxR ByteArray} {m : Module} {c : Config Nat}
    {l : HostLog Nat} {mi : ModuleInst} (hs : StoreOk ctx.store)
    (h : instG o fuel ctx m = some ((c, l), mi)) :
    InstNF o ctx m c.outcome? c.store l mi ∧ StoreOk c.store := by
  unfold instG at h
  split at h
  · cases h
  · rename_i mt hv
    split at h
    · cases h
    · rename_i s₀ xas hr
      split at h
      · rename_i hx
        split at h
        · rename_i s f st hi
          have hm := validate?_sound hv
          have hs₀ := resolve?_ok hs hr
          have hx' := externAddrsOk?_sound hx
          have hc := Game.instantiateOnce?_configOk hs₀ hm hx' hi
          cases hrun : runHG o fuel fuel (⟨s, f, startCode st⟩, ctx.log) with
          | none => rw [hrun] at h; cases h
          | some p =>
            obtain ⟨c', l'⟩ := p
            rw [hrun] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
            obtain ⟨hnf, hok⟩ := runHG_sound fuel hc hrun
            exact ⟨.mk hm hr hx' hi hnf, ConfigOk.storeOk hok⟩
        · cases h
      · cases h

theorem actG_sound {fuel : Nat} {ctx : CtxR ByteArray} {act : Action} {r : Result}
    {s : Store Nat} {l : HostLog Nat} (hs : StoreOk ctx.store)
    (h : actG o fuel ctx act = some (r, s, l)) : ActNF o ctx act (some r) s l ∧ StoreOk s := by
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
          cases hrun : runHG o fuel fuel (invoke ctx.store a args, ctx.log) with
          | none => rw [hrun] at h; cases h
          | some p =>
            obtain ⟨c, l'⟩ := p
            rw [hrun] at h
            simp only [Option.bind_some] at h
            obtain ⟨hnf, hok'⟩ := runHG_sound fuel hc hrun
            cases hr : c.outcome? with
            | none => rw [hr] at h; cases h
            | some r' =>
              rw [hr] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
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
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨.get hm ha hg, hs⟩
      · cases h
    · cases h

theorem unlinkableG_sound {ctx : CtxR ByteArray} {m : Module} (hs : StoreOk ctx.store)
    (h : unlinkableG ctx m = true) :
    (∃ mt, ModuleOk m mt) ∧ ∀ mt s₀ xas, ModuleOk m mt →
      resolve? ctx.regs ctx.store m.imports = some (s₀, xas) →
      ¬ List.Forall₂ (ExternAddrOk s₀) xas mt.imports := by
  unfold unlinkableG at h
  split at h
  · rename_i mt₀ hv
    have hm₀ := validate?_sound hv
    refine ⟨⟨mt₀, hm₀⟩, fun mt s₀ xas hm hr hx => ?_⟩
    obtain rfl := ModuleOk.unique hm hm₀
    rw [hr] at h
    simp only [Bool.not_eq_true'] at h
    rw [externAddrsOk?_complete (resolve?_ok hs hr) hx] at h
    cases h
  · cases h

/-! ## Uniqueness -/

theorem nf_unique {x : Config Nat × HostLog Nat} {c c' : Config Nat} {l l' : HostLog Nat}
    (h : NF o x (c, l)) (h' : NF o x (c', l')) : c = c' ∧ l = l' :=
  LSteps.nf_unique_of_hostDet hostDet h.1 h.2 h'.1 h'.2

theorem actNF_unique {ctx : CtxR ByteArray} {act : Action} {ro ro' : Option Result}
    {s s' : Store Nat} {l l' : HostLog Nat} (h : ActNF o ctx act ro s l)
    (h' : ActNF o ctx act ro' s' l') : ro = ro' ∧ s = s' ∧ l = l' := by
  cases h with
  | invoke hm ha hc =>
    cases h' with
    | invoke hm' ha' hc' =>
      rw [hm] at hm'
      cases hm'
      rw [ha] at ha'
      cases ha'
      obtain ⟨rfl, rfl⟩ := nf_unique hc hc'
      exact ⟨rfl, rfl, rfl⟩
  | get hm ha hg =>
    cases h' with
    | get hm' ha' hg' =>
      rw [hm] at hm'
      cases hm'
      rw [ha] at ha'
      cases ha'
      rw [hg] at hg'
      cases hg'
      exact ⟨rfl, rfl, rfl⟩

theorem instNF_unique {ctx : CtxR ByteArray} {m : Module} {ro ro' : Option Result}
    {s s' : Store Nat} {l l' : HostLog Nat} {mi mi' : ModuleInst} (h : InstNF o ctx m ro s l mi)
    (h' : InstNF o ctx m ro' s' l' mi') : ro = ro' ∧ s = s' ∧ l = l' ∧ mi = mi' := by
  cases h with
  | mk hm hr hx hi hc =>
    cases h' with
    | mk hm' hr' hx' hi' hc' =>
      rw [hr] at hr'
      simp only [Option.some.injEq, Prod.mk.injEq] at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      rw [hi] at hi'
      simp only [Option.some.injEq, Prod.mk.injEq] at hi'
      obtain ⟨rfl, rfl, rfl⟩ := hi'
      obtain ⟨rfl, rfl⟩ := nf_unique hc hc'
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem cmdRun_unique {ctx ctx₁ ctx₂ : CtxR ByteArray} {cmd : Cmd}
    (h₁ : CmdRun o ctx cmd ctx₁) (h₂ : CmdRun o ctx cmd ctx₂) : ctx₁ = ctx₂ := by
  cases h₁ with
  | module h =>
    cases h₂ with
    | module h' =>
      obtain ⟨-, rfl, rfl, rfl⟩ := instNF_unique h h'
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
      obtain ⟨-, rfl, rfl⟩ := actNF_unique h h'
      rfl
  | unlinkable => cases h₂; rfl
  | uninstantiable h =>
    cases h₂ with
    | uninstantiable h' =>
      obtain ⟨-, rfl, rfl, -⟩ := instNF_unique h h'
      rfl

theorem run_unique {ctx ctx₁ ctx₂ : CtxR ByteArray} {cmds : List Cmd}
    (h₁ : Run o ctx cmds ctx₁) (h₂ : Run o ctx cmds ctx₂) : ctx₁ = ctx₂ := by
  induction h₁ with
  | nil => cases h₂; rfl
  | cons h _ ih =>
    cases h₂ with
    | cons h' t' =>
      obtain rfl := cmdRun_unique h h'
      exact ih t'

theorem run_append {ctx ctx₁ ctx₂ : CtxR ByteArray} {l₁ l₂ : List Cmd}
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

theorem scriptAt_unique {pre : List Cmd} {ctx ctx' : CtxR ByteArray}
    (h : ScriptAt o pre ctx) (h' : ScriptAt o pre ctx') : ctx = ctx' := by
  obtain ⟨c₀, hI, hr⟩ := h
  obtain ⟨c₀', hI', hr'⟩ := h'
  obtain rfl := init_unique hI hI'
  exact run_unique hr hr'

/-! ## Scripts -/

theorem scriptAt_snoc {done : List Cmd} {ctx ctx' : CtxR ByteArray} {cmd : Cmd}
    (hS : ScriptAt o done ctx) (h : CmdRun o ctx cmd ctx') : ScriptAt o (done ++ [cmd]) ctx' := by
  obtain ⟨c₀, hI, hr⟩ := hS
  exact ⟨c₀, hI, run_append hr (.cons h (.nil _))⟩

theorem holds_action {done : List Cmd} {ctx : CtxR ByteArray} {act : Action} {r : Result}
    {s : Store Nat} {l : HostLog Nat} (hS : ScriptAt o done ctx) (h : ActNF o ctx act (some r) s l) :
    Reaches o done act r ∧ Only o done act r := by
  refine ⟨⟨ctx, s, l, hS, h⟩, fun ctx' ro s' l' hS' h' => ?_⟩
  obtain rfl := scriptAt_unique hS hS'
  exact (actNF_unique h h').1.symm

theorem cmdsG_holds {fuel : Nat} :
    ∀ {cmds : List Cmd} {done : List Cmd} {ctx : CtxR ByteArray}, StoreOk ctx.store →
      ScriptAt o done ctx → cmdsG o fuel ctx cmds = true →
      ∀ k (cmd : Cmd), cmds[k]? = some cmd → CmdHolds o (done ++ pre cmds k) cmd
  | [], _, _, _, _, _, k, _, hk => by simp at hk
  | cmd :: cmds, done, ctx, hs, hS, h, k, cmd', hk => by
    have step : ∃ ctx', StoreOk ctx'.store ∧ CmdRun o ctx cmd ctx' ∧
        cmdsG o fuel ctx' cmds = true ∧ CmdHolds o done cmd := by
      cases cmd with
      | module name m =>
        simp only [cmdsG] at h
        split at h
        · rename_i c l mi hc
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
          exact ⟨{ ctx with regs := (as, .inst mi) :: ctx.regs }, hs, .register hm, h, trivial⟩
        · cases h
      | action act e =>
        simp only [cmdsG] at h
        split at h
        · rename_i r s l ha
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
        · rename_i c l mi hc
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
              refine ⟨⟨ctx, _, _, _, hS, hI⟩, fun ctx' ro s' l' mi' hS' h' => ?_⟩
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

/-- **One kernel evaluation proves every claim of a linked script against the host.** -/
theorem scriptHolds_of_kernel {fuel : Nat} {cmds : List Cmd} (h : scriptHK o fuel cmds = true) :
    ScriptHolds o cmds := by
  unfold scriptHK at h
  rw [scriptG_toBytes] at h
  unfold scriptG at h
  split at h
  · rename_i mt hv
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨himp, h⟩ := h
    split at h
    · rename_i s f hi
      have hi' : instantiateOnce? (Game.importStore []) Spectest.shared [] = some (s, f, none) :=
        hi
      have hc := Game.instantiateOnce?_configOk Game.importStore_nil_ok (validate?_sound hv)
        (by rw [himp]; exact .nil) hi'
      have hS : ScriptAt o [] { store := s, regs := [("spectest", .spectest f.module)] } :=
        ⟨_, ⟨s, f, hi', rfl⟩, .nil _⟩
      intro k cmd hk
      simpa using cmdsG_holds (ConfigOk.storeOk hc) hS h k cmd hk
    · cases h
  · cases h

/-! ## The log of a script -/

theorem runCmdsG_run {fuel : Nat} :
    ∀ {cmds : List Cmd} {ctx ctx' : CtxR ByteArray}, StoreOk ctx.store →
      runCmdsG o fuel ctx cmds = some ctx' → Run o ctx cmds ctx'
  | [], ctx, ctx', _, h => by
    simp only [runCmdsG, Option.some.injEq] at h
    subst h
    exact .nil _
  | .module name m :: cmds, ctx, ctx', hs, h => by
    simp only [runCmdsG] at h
    split at h
    · rename_i c l mi hc
      split at h
      · rename_i hv
        obtain ⟨hI, hs'⟩ := instG_sound hs hc
        rw [hv] at hI
        exact .cons (.module hI) (runCmdsG_run hs' h)
      · cases h
    · cases h
  | .register as t :: cmds, ctx, ctx', hs, h => by
    simp only [runCmdsG] at h
    split at h
    · rename_i mi hm
      exact .cons (.register hm) (runCmdsG_run hs h)
    · cases h
  | .action act e :: cmds, ctx, ctx', hs, h => by
    simp only [runCmdsG] at h
    split at h
    · rename_i r s l ha
      obtain ⟨hA, hs'⟩ := actG_sound hs ha
      exact .cons (.action (e := e) hA) (runCmdsG_run hs' h)
    · cases h
  | .unlinkable m claim :: cmds, ctx, ctx', hs, h => by
    simp only [runCmdsG] at h
    exact .cons .unlinkable (runCmdsG_run hs h)
  | .uninstantiable m claim :: cmds, ctx, ctx', hs, h => by
    simp only [runCmdsG] at h
    split at h
    · rename_i c l mi hc
      split at h
      · rename_i hr
        obtain ⟨hI, hs'⟩ := instG_sound hs hc
        obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp hr
        rw [hr'] at hI
        exact .cons (.uninstantiable (claim := claim) hI) (runCmdsG_run hs' h)
      · cases h
    · cases h

/-- **The log of a script, from one kernel evaluation.** -/
theorem logIs_of_kernel {fuel : Nat} {cmds : List Cmd} {l : HostLog Nat}
    (h : logHK o fuel cmds = some l) : LogIs o cmds l := by
  unfold logHK at h
  rw [logG_toBytes] at h
  unfold logG at h
  split at h
  · rename_i mt hv
    split at h
    · rename_i himp
      simp only [List.isEmpty_iff] at himp
      split at h
      · rename_i s f hi
        have hi' : instantiateOnce? (Game.importStore []) Spectest.shared [] = some (s, f, none) :=
          hi
        have hc := Game.instantiateOnce?_configOk Game.importStore_nil_ok (validate?_sound hv)
          (by rw [himp]; exact .nil) hi'
        cases hr : runCmdsG o fuel { store := s, regs := [("spectest", .spectest f.module)] } cmds
          with
        | none => rw [hr] at h; cases h
        | some ctx' =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          have hS : ScriptAt o cmds ctx' :=
            ⟨_, ⟨s, f, hi', rfl⟩, runCmdsG_run (ConfigOk.storeOk hc) hr⟩
          exact ⟨⟨ctx', hS⟩, fun ctx'' hS' => by rw [← scriptAt_unique hS hS', h]⟩
      · cases h
    · cases h
  · cases h

/-! ## Termination -/

theorem reaches_always {pre : List Cmd} {act : Action} {r : Result}
    (h : Reaches o pre act r) : Always o pre act r := by
  obtain ⟨ctx, s, l, hS, hA⟩ := h
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
    obtain ⟨hdiv, hext⟩ := Steps.always_of_hostDet hostDet (LSteps.toSteps hc.1) hc.2
    exact ⟨hdiv, fun c' hc' => ⟨_, _, hext c' hc', hc, rfl⟩⟩

/-! ## Print calls -/

/-- **A call of a print function returns no values, leaves the store unchanged and logs the
call**: invoking the host function at `a` (code `k`, answered by the host in `s`) with arguments
of its parameter count takes one logged step to the empty code in the same store, a normal
form. -/
theorem print_nf {s : Store Nat} {a k : Nat} {fi : FuncInst Nat} {ps rs : List CValType}
    {args : List Val} (l : HostLog Nat) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host k)
    (ht : fi.type.funcType? = some (ps, rs)) (hn : args.length = ps.length)
    (hk : Spectest.answers s k = true) :
    NF o (invoke s a args, l) (⟨s, {}, []⟩, l ++ [(k, args)]) := by
  have hinv : invoke s a args =
      ⟨s, {}, vals (args ++ [.ref (.func a)]) ++ [.callRefType fi.type]⟩ := by
    simp [invoke, hf, vals, Val.toAdmin]
  have har : hostArity? s a = some (k, args.length) := by
    simp [hostArity?, hf, hcode, ht, hn]
  have hd : decompose? (invoke s a args).store (invoke s a args).code =
      some (.top [] [], a, k, args) := by
    rw [hinv]
    simpa using decompose?_top (pre := args) (c := .callRefType fi.type) (rest := []) rfl har
      le_rfl
  have hstep := LStep.call (P := profile o) (host := Spectest.host) (l := l) (r := .values []) hd
    ⟨hk, rfl⟩
  have he : (invoke s a args).frame = {} := by rw [hinv]
  have hs : (invoke s a args).store = s := by rw [hinv]
  rw [he, hs] at hstep
  refine ⟨.single hstep, fun c hc => Step.not_quiet hc ?_⟩
  exact quiet_vals []

/-! ## Unlinkable modules -/

theorem unlinkable_not_instantiate {pre : List Cmd} {m : Module}
    (h : Unlinkable o pre m) {ctx : CtxR ByteArray} (hS : ScriptAt o pre ctx) {s₀ : Store Nat}
    {xas : List ExternAddr} (hr : resolve? ctx.regs ctx.store m.imports = some (s₀, xas))
    {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics Nat} {c : Config Nat} :
    ¬ Instantiate P host s₀ m xas c := by
  intro hI
  obtain ⟨xtE, xtI, hm, hx⟩ := hI.valid
  exact (h.2 ctx hS).2 ⟨xtI, xtE⟩ s₀ xas hm hr hx

end Silmaril.Proofs.Project.Shapes.WasmWastHost

end
