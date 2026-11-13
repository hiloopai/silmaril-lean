module

public import Silmaril.Raw.Wasm.Versions.V2.Soundness.Progress
public import Silmaril.Raw.Wasm.Versions.V2.Execution.Properties

/-!
# Type soundness of WebAssembly 2.0

The headline statements, in the shape of
`Silmaril/Wasm/Execution/Core/Soundness.lean` and
`.../Core/Soundness/Headline.lean`:

* `Step.preservation` (`Soundness/Preservation.lean`) — a typed configuration
  steps to a typed configuration of the same result type, over an extended
  store;
* `Config.progress` (`Soundness/Progress.lean`) — a typed configuration is
  terminal (a value stack or `TRAP`) or can step;
* `Steps.safe` — the usual corollary: typed configurations never get stuck, and
  the store only ever grows (`Extend c.store c'.store`);
* `invoke_ok` / `invoke_safe` — `$invoke` (`9-module:196`) on well-typed
  arguments yields a typed configuration, which never gets stuck and only
  extends the store;
* `Instantiate.ok` / `Instantiate.safe` — `$instantiate` (`9-module:167`) of a
  valid module against typed imports yields a typed configuration (of empty
  result type) over an extended store, which never gets stuck;
* `Module.safe` — the spec-shaped statement starting from `ModuleOk` and typed
  imports.

The `Extend` conjunct of the last four is the W3C 2.0 appendix *Corollary
(Soundness)* clause "`|- S <= S'`" (`document/core/appendix/properties.rst` at
`wg-2.0`), transitively closed from `Step.preservation`; it is what makes an
embedder's view of an import — a table or memory handle, an immutable global, an
allocated function address — stable across a run.

**Deviation (no SpecTec source).** The pinned SpecTec wasm-2.0 sources
(WebAssembly/spec `608711107b7f1edb13efd57b7d79b49477462d36`, see
`specs/wasm/core-2.0.json`) contain **no `7-soundness` file**: 2.0 states no
soundness theorem and has no store typing at all. Every judgment these
statements rest on is reconstructed in `Soundness/Store.lean`,
`Soundness/Defs.lean` and `Soundness/Config.lean` from the W3C WebAssembly 2.0
appendix *Soundness*, cross-checked against the Core 3.0 SpecTec files.

**Host functions** are constrained by `HostOk` (`Soundness/Defs.lean`): on a
well-typed store with well-typed arguments the host *has* an outcome (progress)
and *every* returned outcome is a well-typed, store-extending result
(preservation). SpecTec 2.0 has no host functions; this is deviation 3 of
`Execution/Step.lean`, and with `H = Empty` the whole contract is vacuous.

## Instantiation

`Instantiate.ok` needs a development of its own, which the long section
*Instantiation* below carries out — the 2.0 analogue of
`Silmaril/Wasm/Execution/Core/Soundness/{Instantiation,InstantiationAlloc,
ConstEval}.lean`, several times shorter because a 2.0 constant expression is a
*single* instruction (`Execution/Properties.lean`'s `exprOkConst_singleton`):

* `evalExpr_constInstr?_det` — `Eval_expr` on a constant expression is
  deterministic, so the values `$instantiate` feeds to `$allocmodule` are exactly
  the denotations `constInstr?` computes. This is where `Step` is inverted on a
  one-instruction configuration;
* `ExprOkConst.weaken` — a constant expression stays valid when the context
  grows, which is what lets the element and data *offsets*, checked in `C'`, be
  typed in the module context `C`;
* `exprOkConst_valOk` — an initializer has the type the context gives it, in the
  **allocated** store `s'` (the forward reference of `9-module:177-181`: a
  `ref.func` initializer names a function address that `$allocmodule` has not
  allocated yet);
* `Instantiate.alloc_ok` — `Store_ok` for the store `$allocmodule`
  (`9-module:107-147`) returns, `Moduleinst_ok` for the new instance against
  the module context, and `Extend` from the store it started in;
* `initCode_ok` — the `$runelem`/`$rundata`/`$start` program (`9-module:188-189`)
  is typed `eps -> eps` in that context.

Nothing in this file is `sorry`ed.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.V2.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Memory (pageSize Bytes)

variable {H : Type}

/-! ## Type safety -/

/-- **Type safety.** Every configuration reachable from a well-typed one is
well typed at the same result type, **over an extended store**, and is terminal
or can step.

This is the W3C 2.0 appendix *Corollary (Soundness)*
(`document/core/appendix/properties.rst` at `wg-2.0`): a valid configuration
`S;T` "takes a finite number of steps to reach a terminal configuration `S';T'`
… that is valid with the same result type … and where `S'` is an extension of
`S` (i.e. `|- S <= S'`)". The `Extend` conjunct is the transitive closure of the
one in `Step.preservation`, and is stated here for *every* reachable `c'`, not
only the terminal ones — strictly stronger than the corollary as written. It is
what makes an embedder's view of an import stable: a table or memory only grows,
an immutable global keeps its value, and an allocated function address stays
allocated at the same type. -/
theorem Steps.safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts) (h : Steps P host c c') :
    ConfigOk c' ts ∧ Extend c.store c'.store ∧
      (c'.Terminal ∨ ∃ c'', Step P host c' c'') := by
  have hok : ConfigOk c' ts ∧ Extend c.store c'.store := by
    induction h with
    | refl => exact ⟨hc, Extend.refl _⟩
    | tail _ hstep ih =>
      obtain ⟨hok, hext⟩ := ih
      obtain ⟨hok', hext'⟩ := Step.preservation hhost hok hstep
      exact ⟨hok', hext.trans hext'⟩
  exact ⟨hok.1, hok.2, Config.progress hhost hok.1⟩

/-! ## Invocation (`9-module:196-199`) -/

/-- A value whose `Val.type` is `t` and whose function addresses are allocated
is typed by `Val_ok` at `t`. This is the store-dependent half of the
"assert: the value `val_i` is of type `t_i`" of the W3C `$invoke` text, which
`InvokeOk` spells out (`Execution/Instantiation.lean`). -/
theorem valOk_of_type_eq {s : Store H} {v : Val} {t : ValType} (ht : v.type = t)
    (ha : ∀ b : FuncAddr, v = .ref (.funcAddr b) → (s.funcInst? b).isSome) : ValOk s v t := by
  subst ht
  rcases v with ⟨nt, b⟩ | b | (rt | a | a)
  · exact .num _
  · exact .vec _
  · exact .ref (.null rt)
  · obtain ⟨fi, hfi⟩ := Option.isSome_iff_exists.mp (ha a rfl)
    exact .ref (.funcAddr hfi)
  · exact .ref (.hostAddr a)

/-- The pointwise form of `valOk_of_type_eq`: the argument list of `$invoke`. -/
theorem forall₂_valOk {s : Store H} : ∀ {vs : List Val} {ts : List ValType},
    List.Forall₂ (fun (v : Val) (t : ValType) => v.type = t) vs ts →
    (∀ v ∈ vs, ∀ b : FuncAddr, v = .ref (.funcAddr b) → (s.funcInst? b).isSome) →
    List.Forall₂ (ValOk s) vs ts := by
  intro vs ts ht
  induction ht with
  | nil => intro _; exact .nil
  | @cons v t vs' ts' h _ ih =>
    intro ha
    exact .cons (valOk_of_type_eq h (fun b hb => ha v (by simp) b hb))
      (ih (fun w hw b hb => ha w (List.mem_cons_of_mem v hw) b hb))

/-- The empty module instance realizes the empty context. -/
theorem moduleInstOk_empty (s : Store H) :
    ModuleInstOk s ({} : ModuleInst) ({} : Context) :=
  .mk (refs := []) (by simp) .nil .nil .nil .nil .nil (by simp) (by simp) (by simp)
    (by simp) (by simp)

/-- The empty frame `f = { MODULE {} }` of `$invoke` (`9-module:197`) realizes
the empty context. -/
theorem frameOk_empty (s : Store H) : FrameOk s ({} : Frame) ({} : Context) :=
  ⟨{}, [], moduleInstOk_empty s, .nil, rfl⟩

/-- **`$invoke` is well typed.** Invoking an allocated function with arguments
of its parameter types yields a configuration typed at its result type
(`9-module:196-199`). -/
theorem invoke_ok {s : Store H} {a : FuncAddr} {vs : List Val} (hs : StoreOk s)
    (h : InvokeOk s a vs) :
    ∃ fi : FuncInst H, s.funcInst? a = some fi ∧
      ConfigOk (invoke s a vs) (liftResult fi.type.results) := by
  obtain ⟨fi, hfi, -, htypes, halloc⟩ := h
  refine ⟨fi, hfi, ({} : Context), ⟨hs, frameOk_empty s⟩, ?_⟩
  have hvs : List.Forall₂ (ValOk s) vs fi.type.params := forall₂_valOk htypes halloc
  have hvals : AdminsOk s ({} : Context) (vals vs) ⟨[], liftResult fi.type.params⟩ :=
    AdminsOk.of_vals hvs
  have hcall : AdminsOk s ({} : Context) [.callAddr a]
      ⟨liftResult fi.type.params, liftResult fi.type.results⟩ := .single (.callAddr hfi)
  exact hvals.append hcall

/-- **Type safety of invocation.** Every configuration reachable from a
well-typed `$invoke` is typed at the function's result type, runs over a store
extending `s`, and never gets stuck. -/
theorem invoke_safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {a : FuncAddr} {vs : List Val} {c' : Config H} (hs : StoreOk s)
    (h : InvokeOk s a vs) (hsteps : Steps P host (invoke s a vs) c') :
    ∃ fi : FuncInst H, s.funcInst? a = some fi ∧
      ConfigOk c' (liftResult fi.type.results) ∧ Extend s c'.store ∧
      (c'.Terminal ∨ ∃ c'', Step P host c' c'') := by
  obtain ⟨fi, hfi, hc⟩ := invoke_ok hs h
  exact ⟨fi, hfi, Steps.safe hhost hc hsteps⟩

/-! ## Instantiation: the allocation and initialization lemmas

Everything `Instantiate.ok` needs; see the module docstring for the map. The
section is `local`-scoped so that the `simp` set it uses for the closed forms of
`allocMany` does not leak. -/

section Instantiation

variable {P : Profile} {host : HostSemantics H}

/-! ### `Eval_expr` on a constant expression is deterministic

A 2.0 constant expression is a single instruction of one of five forms
(`exprOkConst_singleton`), and `Step` on a one-instruction configuration is
`Step/pure` or `Step/read` — `Step/ctxt-instrs` cannot apply, because its inner
premise would step the empty code. So the value `$instantiate`'s `Eval_expr`
premise produces is exactly the denotation `constInstr?` computes. -/

/-- A singleton is an append of a singleton only trivially. -/
theorem eq_of_singleton_append {α : Type} {l : List α} {a b : α}
    (h : [a] = l ++ [b]) : a = b := by
  have hlen := congrArg List.length h
  simp only [List.length_cons, List.length_nil, List.length_append] at hlen
  have hl : l = [] := List.length_eq_zero_iff.mp (by omega)
  subst hl
  simpa using h

/-- A value stack is a normal form of `Steps`. -/
theorem steps_vals_inv {s : Store H} {f : Frame} {vs : List Val} {c : Config H}
    (h : Steps P host ⟨s, f, vals vs⟩ c) : c = ⟨s, f, vals vs⟩ := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c', hstep, -⟩
  · rfl
  · exact absurd hstep Step.not_vals

/-- `REF.FUNC x` alone is no `Step_pure` redex. -/
theorem pureStep_refFunc {x : FuncIdx} {is' : List Admin}
    (h : PureStep P [.plain (.refFunc x)] is') : False := by
  generalize hL : [Admin.plain (Instr.refFunc x)] = L at h
  cases h with
  | trapVals hne =>
    have hmem : Admin.trap ∈ [Admin.plain (Instr.refFunc x)] := by rw [hL]; simp
    simp at hmem
  | _ => exact absurd hL (by simp [Val.toAdmin])

/-- `GLOBAL.GET x` alone is no `Step_pure` redex. -/
theorem pureStep_globalGet {x : GlobalIdx} {is' : List Admin}
    (h : PureStep P [.plain (.globalGet x)] is') : False := by
  generalize hL : [Admin.plain (Instr.globalGet x)] = L at h
  cases h with
  | trapVals hne =>
    have hmem : Admin.trap ∈ [Admin.plain (Instr.globalGet x)] := by rw [hL]; simp
    simp at hmem
  | _ => exact absurd hL (by simp [Val.toAdmin])

/-- Inversion of `Step` on `(REF.FUNC x)`: only `Step_read/ref.func` applies. -/
theorem step_refFunc_inv {s : Store H} {f : Frame} {x : FuncIdx} {c : Config H}
    (h : Step P host (⟨s, f, [.plain (.refFunc x)]⟩ : Config H) c) :
    ∃ a, f.module.funcAddr? x = some a ∧ c = ⟨s, f, [.refFuncAddr a]⟩ := by
  generalize hL : [Admin.plain (Instr.refFunc x)] = L at h
  cases h with
  | pure hp => exact absurd (hL ▸ hp) (fun hh => pureStep_refFunc hh)
  | read hr =>
    cases hr with
    | refFunc ha =>
      simp only [List.cons.injEq, Admin.plain.injEq, Instr.refFunc.injEq, and_true] at hL
      obtain ⟨rfl, -⟩ := hL
      exact ⟨_, ha, rfl⟩
    | @block bt body vs ft hbt hk => exact absurd (eq_of_singleton_append hL) (by simp)
    | @loop bt body vs ft hbt hk => exact absurd (eq_of_singleton_append hL) (by simp)
    | @callAddr a vs fi fn hf hcode hk => exact absurd (eq_of_singleton_append hL) (by simp)
    | _ => exact absurd hL (by simp [Val.toAdmin])
  | @ctxtInstrs sa sb fa fb vs is is' rest hstep hne =>
    exfalso
    have hisne : is ≠ [] := by
      rintro rfl
      exact Step.not_vals (vs := []) hstep
    have hlen := congrArg List.length hL
    simp only [List.length_cons, List.length_nil, List.length_append, vals_length] at hlen
    have h1 : 0 < is.length := List.length_pos_iff.mpr hisne
    rcases hne with hh | hh
    · exact hh (List.length_eq_zero_iff.mp (by omega))
    · exact hh (List.length_eq_zero_iff.mp (by omega))
  | @callAddrHost sa sb fa a vs fi hh r hf hcode hk hhost =>
    exact absurd (eq_of_singleton_append hL) (by simp)
  | @callAddrHostDiv sa fa a vs fi hh hf hcode hk hhost =>
    exact absurd (eq_of_singleton_append hL) (by simp)
  | _ => exact absurd hL (by simp [Val.toAdmin])


/-- Inversion of `Step` on `(GLOBAL.GET x)`: only `Step_read/global.get`
applies. -/
theorem step_globalGet_inv {s : Store H} {f : Frame} {x : GlobalIdx} {c : Config H}
    (h : Step P host (⟨s, f, [.plain (.globalGet x)]⟩ : Config H) c) :
    ∃ gi, (⟨s, f⟩ : State H).global? x = some gi ∧ c = ⟨s, f, [gi.value.toAdmin]⟩ := by
  generalize hL : [Admin.plain (Instr.globalGet x)] = L at h
  cases h with
  | pure hp => exact absurd (hL ▸ hp) (fun hh => pureStep_globalGet hh)
  | read hr =>
    cases hr with
    | globalGet hg =>
      simp only [List.cons.injEq, Admin.plain.injEq, Instr.globalGet.injEq, and_true] at hL
      obtain ⟨rfl, -⟩ := hL
      exact ⟨_, hg, rfl⟩
    | @block bt body vs ft hbt hk => exact absurd (eq_of_singleton_append hL) (by simp)
    | @loop bt body vs ft hbt hk => exact absurd (eq_of_singleton_append hL) (by simp)
    | @callAddr a vs fi fn hf hcode hk => exact absurd (eq_of_singleton_append hL) (by simp)
    | _ => exact absurd hL (by simp [Val.toAdmin])
  | @ctxtInstrs sa sb fa fb vs is is' rest hstep hne =>
    exfalso
    have hisne : is ≠ [] := by
      rintro rfl
      exact Step.not_vals (vs := []) hstep
    have hlen := congrArg List.length hL
    simp only [List.length_cons, List.length_nil, List.length_append, vals_length] at hlen
    have h1 : 0 < is.length := List.length_pos_iff.mpr hisne
    rcases hne with hh | hh
    · exact hh (List.length_eq_zero_iff.mp (by omega))
    · exact hh (List.length_eq_zero_iff.mp (by omega))
  | @callAddrHost sa sb fa a vs fi hh r hf hcode hk hhost =>
    exact absurd (eq_of_singleton_append hL) (by simp)
  | @callAddrHostDiv sa fa a vs fi hh hf hcode hk hhost =>
    exact absurd (eq_of_singleton_append hL) (by simp)
  | _ => exact absurd hL (by simp [Val.toAdmin])

/-- A plain non-value instruction is not a one-element value stack. -/
theorem plain_ne_vals_singleton {i : Instr} {v : Val} (hnv : (Admin.plain i).val? = none)
    (h : [Admin.plain i] = vals [v]) : False := by
  simp only [vals, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
  have hv := Admin.val?_toAdmin v
  rw [← h, hnv] at hv
  simp at hv

/-- A constant expression evaluates to exactly its denotation. -/
theorem evalExpr_constInstr?_det {s s' : Store H} {f f' : Frame} {i : Instr} {v v₀ : Val}
    (hden : constInstr? s f.module i = some v₀)
    (h : EvalExpr P host s f [i] s' f' [v]) : v = v₀ ∧ s' = s ∧ f' = f := by
  have hval : ∀ (w : Val) (sa : Store H) (fa : Frame),
      Steps P host (⟨sa, fa, vals [w]⟩ : Config H) ⟨s', f', vals [v]⟩ →
      v = w ∧ s' = sa ∧ f' = fa := by
    intro w sa fa hh
    have he := steps_vals_inv hh
    simp only [Config.mk.injEq] at he
    have hvv : [v] = [w] := vals_injective he.2.2
    exact ⟨by simpa using hvv, he.1, he.2.1⟩
  have hcode : expression [i] = [Admin.plain i] := rfl
  rw [EvalExpr, hcode] at h
  cases i with
  | intConst t c =>
    simp only [constInstr?, Option.some.injEq] at hden
    subst hden
    exact hval _ s f h
  | floatConst t c =>
    simp only [constInstr?, Option.some.injEq] at hden
    subst hden
    exact hval _ s f h
  | vecConst c =>
    simp only [constInstr?, Option.some.injEq] at hden
    subst hden
    exact hval _ s f h
  | refNull rt =>
    simp only [constInstr?, Option.some.injEq] at hden
    subst hden
    exact hval _ s f h
  | refFunc x =>
    simp only [constInstr?, Option.map_eq_some_iff] at hden
    obtain ⟨a, ha, rfl⟩ := hden
    rcases Relation.ReflTransGen.cases_head h with he | ⟨c₁, hstep, hrest⟩
    · exfalso
      simp only [Config.mk.injEq] at he
      exact plain_ne_vals_singleton (by simp [Admin.val?]) he.2.2
    · obtain ⟨a', ha', rfl⟩ := step_refFunc_inv hstep
      rw [ha] at ha'
      injection ha' with haa
      subst haa
      exact hval _ s f hrest
  | globalGet x =>
    simp only [constInstr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hden
    obtain ⟨a, ha, gi, hgi, rfl⟩ := hden
    rcases Relation.ReflTransGen.cases_head h with he | ⟨c₁, hstep, hrest⟩
    · exfalso
      simp only [Config.mk.injEq] at he
      exact plain_ne_vals_singleton (by simp [Admin.val?]) he.2.2
    · obtain ⟨gi', hgi', rfl⟩ := step_globalGet_inv hstep
      rw [show (⟨s, f⟩ : State H).global? x = some gi by simp [State.global?, ha, hgi]] at hgi'
      injection hgi' with hgg
      subst hgg
      exact hval _ s f hrest
  | _ => simp [constInstr?] at hden

/-! ### Closed forms of `allocMany` -/

/-- The component an `$alloc*s` sequence writes is the old one with one entry
appended per argument. -/
theorem allocMany_fst_map {α β : Type} {alloc : Store H → α → Store H × Addr}
    (F : Store H → List β) (g : α → β)
    (hF : ∀ (s : Store H) (x : α), F (alloc s x).1 = F s ++ [g x]) :
    ∀ (s : Store H) (xs : List α), F (allocMany alloc s xs).1 = F s ++ xs.map g := by
  intro s xs
  induction xs generalizing s with
  | nil => simp [allocMany]
  | cons x xs ih =>
    show F (allocMany alloc (alloc s x).1 xs).1 = _
    rw [ih, hF]
    simp

theorem allocFuncs_fst_funcs (s : Store H) (mi : ModuleInst)
    (fs : List (FuncType × Func)) :
    (allocFuncs s mi fs).1.funcs = s.funcs ++ fs.map (fun p => ⟨p.1, mi, .wasm p.2⟩) :=
  allocMany_fst_map (fun s => s.funcs) _ (fun _ _ => rfl) s fs

theorem allocGlobals_fst_globals (s : Store H) (gs : List (GlobalType × Val)) :
    (allocGlobals s gs).1.globals = s.globals ++ gs.map (fun p => ⟨p.1, p.2⟩) :=
  allocMany_fst_map (fun s => s.globals) _ (fun _ _ => rfl) s gs

theorem allocTables_fst_tables (s : Store H) (ts : List TableType) :
    (allocTables s ts).1.tables =
      s.tables ++ ts.map (fun tt => ⟨tt, List.replicate tt.limits.min.val (.null tt.element)⟩) :=
  allocMany_fst_map (fun s => s.tables) _ (fun _ _ => rfl) s ts

theorem allocMems_fst_mems (s : Store H) (ts : List MemoryType) :
    (allocMems s ts).1.mems =
      s.mems ++ ts.map (fun mt => ⟨mt, ⟨Array.replicate (mt.limits.min.val * pageSize) 0⟩⟩) :=
  allocMany_fst_map (fun s => s.mems) _ (fun _ _ => rfl) s ts

theorem allocElems_fst_elems (s : Store H) (es : List (ElemType × List Ref)) :
    (allocElems s es).1.elems = s.elems ++ es.map (fun p => ⟨p.1, p.2⟩) :=
  allocMany_fst_map (fun s => s.elems) _ (fun _ _ => rfl) s es

theorem allocDatas_fst_datas (s : Store H) (bs : List Bytes) :
    (allocDatas s bs).1.datas = s.datas ++ bs.map DataInst.mk :=
  allocMany_fst_map (fun s => s.datas) _ (fun _ _ => rfl) s bs

/-! ### The components an allocator leaves alone, in the other direction -/

theorem allocGlobals_fst_funcs (s : Store H) (gs : List (GlobalType × Val)) :
    (allocGlobals s gs).1.funcs = s.funcs :=
  allocMany_fst (fun s => s.funcs) (fun _ _ => rfl) s gs

theorem allocTables_fst_funcs (s : Store H) (ts : List TableType) :
    (allocTables s ts).1.funcs = s.funcs :=
  allocMany_fst (fun s => s.funcs) (fun _ _ => rfl) s ts

theorem allocTables_fst_globals (s : Store H) (ts : List TableType) :
    (allocTables s ts).1.globals = s.globals :=
  allocMany_fst (fun s => s.globals) (fun _ _ => rfl) s ts

theorem allocMems_fst_funcs (s : Store H) (ts : List MemoryType) :
    (allocMems s ts).1.funcs = s.funcs :=
  allocMany_fst (fun s => s.funcs) (fun _ _ => rfl) s ts

theorem allocMems_fst_globals (s : Store H) (ts : List MemoryType) :
    (allocMems s ts).1.globals = s.globals :=
  allocMany_fst (fun s => s.globals) (fun _ _ => rfl) s ts

theorem allocMems_fst_tables (s : Store H) (ts : List MemoryType) :
    (allocMems s ts).1.tables = s.tables :=
  allocMany_fst (fun s => s.tables) (fun _ _ => rfl) s ts

theorem allocElems_fst_funcs (s : Store H) (es : List (ElemType × List Ref)) :
    (allocElems s es).1.funcs = s.funcs :=
  allocMany_fst (fun s => s.funcs) (fun _ _ => rfl) s es

theorem allocElems_fst_globals (s : Store H) (es : List (ElemType × List Ref)) :
    (allocElems s es).1.globals = s.globals :=
  allocMany_fst (fun s => s.globals) (fun _ _ => rfl) s es

theorem allocElems_fst_tables (s : Store H) (es : List (ElemType × List Ref)) :
    (allocElems s es).1.tables = s.tables :=
  allocMany_fst (fun s => s.tables) (fun _ _ => rfl) s es

theorem allocElems_fst_mems (s : Store H) (es : List (ElemType × List Ref)) :
    (allocElems s es).1.mems = s.mems :=
  allocMany_fst (fun s => s.mems) (fun _ _ => rfl) s es

theorem allocDatas_fst_funcs (s : Store H) (bs : List Bytes) :
    (allocDatas s bs).1.funcs = s.funcs :=
  allocMany_fst (fun s => s.funcs) (fun _ _ => rfl) s bs

theorem allocDatas_fst_globals (s : Store H) (bs : List Bytes) :
    (allocDatas s bs).1.globals = s.globals :=
  allocMany_fst (fun s => s.globals) (fun _ _ => rfl) s bs

theorem allocDatas_fst_tables (s : Store H) (bs : List Bytes) :
    (allocDatas s bs).1.tables = s.tables :=
  allocMany_fst (fun s => s.tables) (fun _ _ => rfl) s bs

theorem allocDatas_fst_mems (s : Store H) (bs : List Bytes) :
    (allocDatas s bs).1.mems = s.mems :=
  allocMany_fst (fun s => s.mems) (fun _ _ => rfl) s bs

theorem allocDatas_fst_elems (s : Store H) (bs : List Bytes) :
    (allocDatas s bs).1.elems = s.elems :=
  allocMany_fst (fun s => s.elems) (fun _ _ => rfl) s bs

attribute [local simp] allocFuncs_fst_funcs allocGlobals_fst_globals allocTables_fst_tables
  allocMems_fst_mems allocElems_fst_elems allocDatas_fst_datas allocGlobals_fst_funcs
  allocTables_fst_funcs allocTables_fst_globals allocMems_fst_funcs allocMems_fst_globals
  allocMems_fst_tables allocElems_fst_funcs allocElems_fst_globals allocElems_fst_tables
  allocElems_fst_mems allocDatas_fst_funcs allocDatas_fst_globals allocDatas_fst_tables
  allocDatas_fst_mems allocDatas_fst_elems allocFuncs_fst_globals allocFuncs_fst_tables
  allocFuncs_fst_mems allocFuncs_fst_elems allocFuncs_fst_datas allocGlobals_fst_tables
  allocGlobals_fst_mems allocGlobals_fst_elems allocGlobals_fst_datas allocTables_fst_mems
  allocTables_fst_elems allocTables_fst_datas allocMems_fst_elems allocMems_fst_datas
  allocElems_fst_datas

/-- The six components of the store `$allocmodule` returns. -/
theorem allocModule?_store {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vs rss = some (s', mi)) :
    ∃ fts : List FuncType,
      (m.funcs.mapM fun fn => m.types[fn.type.toNat]?) = some fts ∧
      s'.funcs = s.funcs ++ (fts.zip m.funcs).map (fun p => ⟨p.1, mi, .wasm p.2⟩) ∧
      s'.globals = s.globals ++
        ((m.globals.map Global.type).zip vs).map (fun p => ⟨p.1, p.2⟩) ∧
      s'.tables = s.tables ++ m.tables.map
        (fun tt => ⟨tt, List.replicate tt.limits.min.val (.null tt.element)⟩) ∧
      s'.mems = s.mems ++ m.memories.map
        (fun mt => ⟨mt, ⟨Array.replicate (mt.limits.min.val * pageSize) 0⟩⟩) ∧
      s'.elems = s.elems ++ ((m.elems.map Elem.type).zip rss).map (fun p => ⟨p.1, p.2⟩) ∧
      s'.datas = s.datas ++ (m.data.map Data.bytes).map DataInst.mk := by
  obtain ⟨fts, s₁, s₂, s₃, s₄, s₅, hfts, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -, -, -⟩ :=
    allocModule?_spec h
  exact ⟨fts, hfts, by simp, by simp, by simp, by simp, by simp, by simp⟩


/-! ### Store extension by appending -/

/-- Appending to a store component extends it. -/
theorem ExtendsList.of_append {α : Type} {R : α → α → Prop} (l t : List α)
    (hR : ∀ x, R x x) : ExtendsList R l (l ++ t) :=
  ⟨by simp, fun i x hx => ⟨x, by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]; exact hx, hR x⟩⟩

/-- A store that appends to every component extends the old one. -/
theorem Extend.of_appends {s s' : Store H} {fs : List (FuncInst H)} {gs : List GlobalInst}
    {ts : List TableInst} {ms : List MemInst} {es : List ElemInst} {ds : List DataInst}
    (hf : s'.funcs = s.funcs ++ fs) (hg : s'.globals = s.globals ++ gs)
    (ht : s'.tables = s.tables ++ ts) (hm : s'.mems = s.mems ++ ms)
    (he : s'.elems = s.elems ++ es) (hd : s'.datas = s.datas ++ ds) : Extend s s' where
  funcs := hf ▸ ExtendsList.of_append _ _ extendFunc_refl
  globals := hg ▸ ExtendsList.of_append _ _ extendGlobal_refl
  tables := ht ▸ ExtendsList.of_append _ _ extendTable_refl
  mems := hm ▸ ExtendsList.of_append _ _ extendMem_refl
  elems := he ▸ ExtendsList.of_append _ _ extendElem_refl
  datas := hd ▸ ExtendsList.of_append _ _ extendData_refl

/-- `Store_ok` for a store that extends a well-typed one by *allocation*: every
instance is either an old one or a new one that is already known to be well
typed. Unlike `StoreOk.mk_of_extend` this allows new function instances. -/
theorem StoreOk.mk_of_alloc {s s' : Store H} (hs : StoreOk s) (he : Extend s s')
    (hf : ∀ fi ∈ s'.funcs, fi ∈ s.funcs ∨ FuncInstOk s' fi)
    (hg : ∀ gi ∈ s'.globals, gi ∈ s.globals ∨ GlobalInstOk s' gi)
    (ht : ∀ ti ∈ s'.tables, ti ∈ s.tables ∨ TableInstOk s' ti)
    (hm : ∀ mi ∈ s'.mems, mi ∈ s.mems ∨ MemInstOk mi)
    (hel : ∀ ei ∈ s'.elems, ei ∈ s.elems ∨ ElemInstOk s' ei) : StoreOk s' where
  funcs fi hfi := (hf fi hfi).elim (fun h => (hs.funcs fi h).extend hs he) id
  globals gi hgi := (hg gi hgi).elim (fun h => (hs.globals gi h).extend he) id
  tables ti hti := (ht ti hti).elim (fun h => (hs.tables ti h).extend he) id
  mems mi hmi := (hm mi hmi).elim (fun h => hs.mems mi h) id
  elems ei hei :=
    (hel ei hei).elim (fun h => ElemInstOk.extend he (extendElem_refl ei) (hs.elems ei h)) id
  datas _ _ := trivial

/-! ### Import matching, split by kind -/

theorem ExternAddrOk.forall₂_funcs {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List ExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a ft => ExternAddrOk s (.func a) (.func ft))
        (ExternAddr.funcs xas) (ExternType.funcs xts) := by
  intro xas xts h
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    rcases hx.kind_eq with ⟨a, ft, rfl, rfl⟩ | ⟨a, gt, rfl, rfl⟩ | ⟨a, tt, rfl, rfl⟩ |
      ⟨a, mt, rfl, rfl⟩
    · exact .cons hx ih
    · exact ih
    · exact ih
    · exact ih

theorem ExternAddrOk.forall₂_globals {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List ExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a gt => ExternAddrOk s (.global a) (.global gt))
        (ExternAddr.globals xas) (ExternType.globals xts) := by
  intro xas xts h
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    rcases hx.kind_eq with ⟨a, ft, rfl, rfl⟩ | ⟨a, gt, rfl, rfl⟩ | ⟨a, tt, rfl, rfl⟩ |
      ⟨a, mt, rfl, rfl⟩
    · exact ih
    · exact .cons hx ih
    · exact ih
    · exact ih

theorem ExternAddrOk.forall₂_tables {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List ExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a tt => ExternAddrOk s (.table a) (.table tt))
        (ExternAddr.tables xas) (ExternType.tables xts) := by
  intro xas xts h
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    rcases hx.kind_eq with ⟨a, ft, rfl, rfl⟩ | ⟨a, gt, rfl, rfl⟩ | ⟨a, tt, rfl, rfl⟩ |
      ⟨a, mt, rfl, rfl⟩
    · exact ih
    · exact ih
    · exact .cons hx ih
    · exact ih

theorem ExternAddrOk.forall₂_mems {s : Store H} :
    ∀ {xas : List ExternAddr} {xts : List ExternType}, List.Forall₂ (ExternAddrOk s) xas xts →
      List.Forall₂ (fun a mt => ExternAddrOk s (.mem a) (.memory mt))
        (ExternAddr.mems xas) (ExternType.mems xts) := by
  intro xas xts h
  induction h with
  | nil => exact .nil
  | cons hx _ ih =>
    rcases hx.kind_eq with ⟨a, ft, rfl, rfl⟩ | ⟨a, gt, rfl, rfl⟩ | ⟨a, tt, rfl, rfl⟩ |
      ⟨a, mt, rfl, rfl⟩
    · exact ih
    · exact ih
    · exact ih
    · exact .cons hx ih

/-! ### Constant expressions weaken along a context prefix -/

/-- A lookup that succeeds in a list still succeeds, with the same value, in any
extension of it. -/
theorem getElem?_of_prefix {α : Type} {l l' : List α} {t : List α} (hl : l' = l ++ t)
    {i : Nat} {x : α} (hx : l[i]? = some x) : l'[i]? = some x := by
  subst hl
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hx).1]
  exact hx

/-- A 2.0 constant expression stays valid when the context grows: the five
`Instr_const` forms read only `C.FUNCS`, `C.GLOBALS` and `C.REFS`, and growing
`C.GLOBALS` at the end preserves every lookup. -/
theorem ExprOkConst.weaken {C₁ C₂ : Context} {e : Expr} {t : ValType}
    (hfuncs : C₁.funcs = C₂.funcs) (hrefs : C₁.refs = C₂.refs)
    {gs : List GlobalType} (hglobals : C₂.globals = C₁.globals ++ gs)
    (h : ExprOkConst C₁ e t) : ExprOkConst C₂ e t := by
  obtain ⟨i, rfl, hc, hit⟩ := exprOkConst_singleton h
  have hok : InstrOk C₂ i ⟨[], [.val t]⟩ := by
    cases hc with
    | intConst t' c => cases hit; exact .intConst
    | floatConst t' c => cases hit; exact .floatConst
    | vecConst c => cases hit; exact .vecConst
    | refNull rt => cases hit; exact .refNull
    | refFunc x =>
      cases hit with
      | refFunc hx hr => exact .refFunc (hfuncs ▸ hx) (hrefs ▸ hr)
    | globalGet hx hmut =>
      cases hit with
      | globalGet hx' => exact .globalGet (getElem?_of_prefix hglobals hx')
  refine ⟨.instr hok, ?_⟩
  intro j hj
  simp only [List.mem_singleton] at hj
  subst hj
  cases hc with
  | intConst t' c => exact .intConst _ _
  | floatConst t' c => exact .floatConst _ _
  | vecConst c => exact .vecConst _
  | refNull rt => exact .refNull _
  | refFunc x => exact .refFunc _
  | globalGet hx hmut => exact .globalGet (getElem?_of_prefix hglobals hx) hmut


/-! ### Free function indices of a constant expression -/

/-- Every element of the left list of a `Forall₂` is related to one on the
right. -/
theorem forall₂_exists_left {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) : ∃ b, R a b := by
  induction h with
  | nil => exact absurd ha (by simp)
  | cons hx _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨_, hx⟩
    · exact ih ha'

/-- Every function index free in a constant expression is in range. -/
theorem ExprOkConst.freeFuncs_lt {C : Context} {e : Expr} {t : ValType}
    (h : ExprOkConst C e t) {x : FuncIdx} (hx : x ∈ Expr.freeFuncs e) :
    x.toNat < C.funcs.length := by
  obtain ⟨i, rfl, hc, hit⟩ := exprOkConst_singleton h
  simp only [Expr.freeFuncs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
  cases hc with
  | intConst t' c => simp [Instr.freeFuncs] at hx
  | floatConst t' c => simp [Instr.freeFuncs] at hx
  | vecConst c => simp [Instr.freeFuncs] at hx
  | refNull rt => simp [Instr.freeFuncs] at hx
  | globalGet hg hmut => simp [Instr.freeFuncs] at hx
  | refFunc y =>
    simp only [Instr.freeFuncs, List.mem_singleton] at hx
    subst hx
    obtain ⟨⟨ft, hft⟩, -, -⟩ := InstrOk.refFunc_inv hit
    exact (List.getElem?_eq_some_iff.mp hft).1

/-- Every index of `$funcidx_nonfuncs` — the `REFS` of the module context — is a
valid function index. -/
theorem funcIdxNonFuncs_lt {m : Module} {C C' : Context} {gts : List GlobalType}
    {rts : List RefType} {xts : List ExternType}
    (hfc : C'.funcs = C.funcs)
    (hglobals : List.Forall₂ (GlobalOk C') m.globals gts)
    (helems : List.Forall₂ (ElemOk C') m.elems rts)
    (hexports : List.Forall₂ (ExportOk C) m.exports xts) :
    ∀ x ∈ funcIdxNonFuncs m, x.toNat < C.funcs.length := by
  intro x hx
  simp only [funcIdxNonFuncs, List.mem_append, List.mem_flatMap] at hx
  rcases hx with ⟨⟨g, hg, hxg⟩ | ⟨e, he, hxe⟩⟩ | ⟨ex, hex, hxx⟩
  · obtain ⟨gt, -, -, hinit⟩ := forall₂_exists_left hglobals hg
    exact hfc ▸ ExprOkConst.freeFuncs_lt hinit hxg
  · obtain ⟨rt, -, hinit, hmode⟩ := forall₂_exists_left helems he
    rcases hxe with ⟨ex, hex, hx1⟩ | hx2
    · exact hfc ▸ ExprOkConst.freeFuncs_lt (hinit ex hex) hx1
    · rcases hm : e.mode with ⟨y, off⟩ | _ | _
      · have hmode' : ElemModeOk C' (.active y off) rt := hm ▸ hmode
        simp only [hm] at hx2
        cases hmode' with
        | active hxt hrt hoff => exact hfc ▸ ExprOkConst.freeFuncs_lt hoff hx2
      · simp only [hm] at hx2; exact absurd hx2 (by simp)
      · simp only [hm] at hx2; exact absurd hx2 (by simp)
  · obtain ⟨xt, hok⟩ := forall₂_exists_left hexports hex
    have hok' : ExternIdxOk C ex.index xt := hok
    rcases hidx : ex.index with y | y | y | y
    · rw [hidx] at hok'
      simp only [hidx, List.mem_singleton] at hxx
      subst hxx
      cases hok' with
      | func hy => exact (List.getElem?_eq_some_iff.mp hy).1
    all_goals (exfalso; simp [hidx] at hxx)

/-! ### Initializer values -/

/-- **An initializer has the type the context gives it, in the allocated store.**
The hypotheses are the agreement between the module context `C` and the initial
module instance `f.MODULE` that `$instantiate` establishes: `C.FUNCS` is no
longer than the (predicted) function index space, every global of `C` is an
allocated global of `s` of the declared type, and every function address of the
instance is allocated in the *final* store `s'`. -/
theorem exprOkConst_valOk {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {C : Context} {f : Frame} {e : Expr} {t : ValType} {v : Val}
    (hs : StoreOk s) (hext : Extend s s')
    (hfl : C.funcs.length ≤ f.module.funcs.length)
    (hgl : ∀ (x : GlobalIdx) (gt : GlobalType), C.globals[x.toNat]? = some gt →
      ∃ a gi, f.module.globalAddr? x = some a ∧ s.globalInst? a = some gi ∧ gi.type = gt)
    (hfa : ∀ (x : FuncIdx) (a : FuncAddr), f.module.funcAddr? x = some a →
      (s'.funcInst? a).isSome)
    (h : ExprOkConst C e t)
    (hev : EvalExpr P host s f e s f [v]) : ValOk s' v t := by
  obtain ⟨i, rfl, hc, hit⟩ := exprOkConst_singleton h
  cases hc with
  | intConst t' c =>
    cases hit
    obtain ⟨rfl, -, -⟩ := evalExpr_constInstr?_det (v₀ := .num ⟨.int t', c⟩) rfl hev
    exact .num _
  | floatConst t' c =>
    cases hit
    obtain ⟨rfl, -, -⟩ := evalExpr_constInstr?_det (v₀ := .num ⟨.float t', c⟩) rfl hev
    exact .num _
  | vecConst c =>
    cases hit
    obtain ⟨rfl, -, -⟩ := evalExpr_constInstr?_det (v₀ := .vec c) rfl hev
    exact .vec _
  | refNull rt =>
    cases hit
    obtain ⟨rfl, -, -⟩ := evalExpr_constInstr?_det (v₀ := .ref (.null rt)) rfl hev
    exact .ref (.null rt)
  | refFunc x =>
    cases hit with
    | refFunc hx hr =>
      have hxlt : x.toNat < f.module.funcs.length :=
        Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hx).1 hfl
      have ha : f.module.funcAddr? x = some f.module.funcs[x.toNat] :=
        List.getElem?_eq_getElem hxlt
      obtain ⟨fi, hfi⟩ := Option.isSome_iff_exists.mp (hfa x _ ha)
      obtain ⟨rfl, -, -⟩ := evalExpr_constInstr?_det
        (v₀ := .ref (.funcAddr f.module.funcs[x.toNat])) (by simp [constInstr?, ha]) hev
      exact .ref (.funcAddr hfi)
  | globalGet hx hmut =>
    cases hit with
    | globalGet hx' =>
      rename_i x gt _
      obtain ⟨a, gi, ha, hgi, rfl⟩ := hgl x _ hx'
      obtain ⟨rfl, -, -⟩ := evalExpr_constInstr?_det (v₀ := gi.value)
        (by simp [constInstr?, ha, hgi]) hev
      exact ValOk.extend hext (hs.globals gi (List.mem_of_getElem? hgi)).2


/-! ### `List.Forall₂` plumbing for the allocation proof -/

/-- A pointwise equality of lists is an equality of lists. -/
theorem forall₂_eq_right {α : Type} : ∀ {l l' : List α},
    List.Forall₂ (fun a b => b = a) l l' → l' = l
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    cases h with
    | cons hx hs => rw [hx, forall₂_eq_right hs]

/-- `List.mapM` over `Option` is determined by its pointwise graph. -/
theorem mapM_eq_of_forall₂ {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' l'' : List β}, l.mapM g = some l' →
      List.Forall₂ (fun a b => g a = some b) l l'' → l' = l''
  | [], l', l'', h, h2 => by
    cases h2
    simpa using h
  | a :: l, l', l'', h, h2 => by
    cases h2 with
    | cons hx hs =>
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨b, hb, bs, hbs, rfl⟩ := h
      rw [hx] at hb
      obtain rfl := Option.some.inj hb
      rw [mapM_eq_of_forall₂ hbs hs]

/-- A pointwise relation against a consecutive range of addresses. -/
theorem forall₂_rangeMap {β : Type} (c n : Nat) {l : List β} {R : Nat → β → Prop}
    (hlen : l.length = n) (h : ∀ (i : Nat) (hi : i < l.length), R (c + i) l[i]) :
    List.Forall₂ R ((List.range n).map (c + ·)) l := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hlen], ?_⟩
  intro i h₁ h₂
  simpa using h i h₂

/-- Indexing past the end of the left operand of an append. -/
theorem getElem?_append_right_add {α : Type} (l t : List α) (i : Nat) :
    (l ++ t)[l.length + i]? = t[i]? := by
  rw [List.getElem?_append_right (by omega)]
  simp


/-- A pointwise `b = g a` is `l' = l.map g`. -/
theorem forall₂_eq_map {α β : Type} {g : α → β} : ∀ {l : List α} {l' : List β},
    List.Forall₂ (fun a b => b = g a) l l' → l' = l.map g
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    cases h with
    | cons hx hs => rw [hx, forall₂_eq_map hs]; rfl

/-- `$instexport` returns an export instance with the export's own name whose
address is one of the four index spaces it was given. -/
theorem instExport?_spec {fas : List FuncAddr} {gas : List GlobalAddr} {tas : List TableAddr}
    {mas : List MemAddr} {e : Export} {xi : ExportInst}
    (h : instExport? fas gas tas mas e = some xi) :
    xi.name = e.name ∧ xi.addr ∈ fas.map ExternAddr.func ++ gas.map ExternAddr.global ++
      tas.map ExternAddr.table ++ mas.map ExternAddr.mem := by
  simp only [instExport?, Option.map_eq_some_iff] at h
  obtain ⟨xa, hxa, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  rcases hidx : e.index with y | y | y | y <;> rw [hidx] at hxa <;>
    simp only [Option.map_eq_some_iff] at hxa <;> obtain ⟨a, ha, rfl⟩ := hxa <;>
    simp only [List.mem_append, List.mem_map]
  · exact .inl (.inl (.inl ⟨a, List.mem_of_getElem? ha, rfl⟩))
  · exact .inl (.inl (.inr ⟨a, List.mem_of_getElem? ha, rfl⟩))
  · exact .inl (.inr ⟨a, List.mem_of_getElem? ha, rfl⟩)
  · exact .inr ⟨a, List.mem_of_getElem? ha, rfl⟩

/-- A successful `List.mapM` over `Option` is a pointwise graph. -/
theorem forall₂_of_mapM {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' →
      List.Forall₂ (fun a b => g a = some b) l l'
  | [], l', h => by simp at h; subst h; exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (forall₂_of_mapM hbs)



/-- Combine two pointwise relations over a common index list. -/
theorem forall₂_zip {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {T : γ → β → Prop}
    (hT : ∀ a b c, R a b → S a c → T c b) :
    ∀ {l : List α} {lb : List β} {lc : List γ},
      List.Forall₂ R l lb → List.Forall₂ S l lc → List.Forall₂ T lc lb
  | [], _, _, h1, h2 => by cases h1; cases h2; exact .nil
  | _ :: _, _, _, h1, h2 => by
    cases h1 with
    | cons hx hs =>
      cases h2 with
      | cons hy ht => exact .cons (hT _ _ _ hx hy) (forall₂_zip hT hs ht)

/-- Every element of the right list of a `Forall₂` is related to one on the
left. -/
theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {b : β} (hb : b ∈ l') : ∃ a, a ∈ l ∧ R a b := by
  induction h with
  | nil => exact absurd hb (by simp)
  | cons hx _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨_, by simp, hx⟩
    · obtain ⟨a, ha, hR⟩ := ih hb'
      exact ⟨a, by simp [ha], hR⟩


/-- `Forall₂` holds at every common index. -/
theorem forall₂_getElem {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {i : Nat} (hi : i < l.length) (hi' : i < l'.length) :
    R l[i] l'[i] := by
  rw [List.forall₂_iff_get] at h
  simpa using h.2 i hi hi'

/-- A pointwise equality of images is an equality of images. -/
theorem forall₂_map_eq {α β γ : Type} {g : α → γ} {g' : β → γ} {l : List α} {l' : List β}
    (h : List.Forall₂ (fun a b => g' b = g a) l l') : l'.map g' = l.map g := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp [hx, ih]

/-- The export instances `$allocmodule` builds. -/
theorem allocModule?_exports {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vs rss = some (s', mi)) :
    m.exports.mapM (instExport? mi.funcs mi.globals mi.tables mi.mems) = some mi.exports := by
  simp only [allocModule?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq, exists_const] at h
  obtain ⟨fts, -, -, -, xi, hxi, -, hmi⟩ := h
  subst hmi
  exact hxi

/-! ### The allocated store and module instance -/

/-- **The store `$allocmodule` returns is valid, extends `s`, and the new module
instance realizes the module context.** The premises are those of `Module_ok`
(`6-typing:682`) together with the import matching and the two `Eval_expr`
premises of `$instantiate` (`9-module:183-185`). -/
theorem Instantiate.alloc_ok {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {m : Module} {xas : List ExternAddr} {mi : ModuleInst}
    {ixt xt : List ExternType} {ft' ft : List FuncType} {gt : List GlobalType}
    {tt : List TableType} {mt : List MemoryType} {rt : List RefType}
    {C C' : Context} {valsG : List Val} {refsE : List (List Ref)}
    (hs : StoreOk s)
    (htypes : List.Forall₂ TypeOk m.types ft')
    (hglobals : List.Forall₂ (GlobalOk C') m.globals gt)
    (htables : List.Forall₂ TableOk m.tables tt)
    (hmems : List.Forall₂ MemOk m.memories mt)
    (helems : List.Forall₂ (ElemOk C') m.elems rt)
    (hfuncs : List.Forall₂ (FuncOk C) m.funcs ft)
    (hexports : List.Forall₂ (ExportOk C) m.exports xt)
    (hnames : (m.exports.map Export.name).Nodup)
    (hC : C = { types := ft', funcs := ExternType.funcs ixt ++ ft,
                globals := ExternType.globals ixt ++ gt,
                tables := ExternType.tables ixt ++ tt,
                mems := ExternType.mems ixt ++ mt, elems := rt,
                datas := m.data.map fun _ => (), refs := funcIdxNonFuncs m })
    (hC' : C' = { types := ft', funcs := ExternType.funcs ixt ++ ft,
                  globals := ExternType.globals ixt,
                  tables := ExternType.tables ixt ++ tt,
                  mems := ExternType.mems ixt ++ mt, refs := funcIdxNonFuncs m })
    (hxas : List.Forall₂ (ExternAddrOk s) xas ixt)
    (hg : List.Forall₂ (fun (g : Global) (v : Val) =>
        EvalExpr P host s (Frame.initial s m xas) (Global.init g)
          s (Frame.initial s m xas) [v]) m.globals valsG)
    (he : List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
        List.Forall₂ (fun (ex : Expr) (r : Ref) =>
          EvalExpr P host s (Frame.initial s m xas) ex
            s (Frame.initial s m xas) [Val.ref r]) e.init rs) m.elems refsE)
    (ha : allocModule? s m xas valsG refsE = some (s', mi)) :
    StoreOk s' ∧ ModuleInstOk s' mi C ∧ Extend s s' := by
  -- the identifications forced by the `Module_ok` premises
  have hft' : ft' = m.types := by
    simpa using forall₂_eq_map (g := id) (htypes.imp fun _ _ h => h.1)
  have hgt : gt = m.globals.map Global.type := forall₂_eq_map (hglobals.imp fun _ _ h => h.1)
  have htt : tt = m.tables := by
    simpa using forall₂_eq_map (g := id) (htables.imp fun _ _ h => h.1)
  have hmt : mt = m.memories := by
    simpa using forall₂_eq_map (g := id) (hmems.imp fun _ _ h => h.1)
  have hrt : rt = m.elems.map Elem.type := forall₂_eq_map (helems.imp fun _ _ h => h.1)
  -- the shape of the allocated store and module instance
  obtain ⟨fts, hfts, eF, eG, eT, eM, eE, eD⟩ := allocModule?_store ha
  obtain ⟨miT, miF, miG, miTb, miM, miE, miD⟩ := allocModule?_moduleInst ha
  have hCt : C.types = m.types := by rw [hC]; exact hft'
  have hfteq : fts = ft := by
    refine mapM_eq_of_forall₂ hfts (hfuncs.imp fun fn d h => ?_)
    cases h with
    | mk hx _ => rw [← hCt]; exact hx
  rw [hfteq] at eF
  -- lengths
  have hlenF : ft.length = m.funcs.length := hfuncs.length_eq.symm
  have hlenG : valsG.length = m.globals.length := hg.length_eq.symm
  have hlenG' : gt.length = m.globals.length := hglobals.length_eq.symm
  have hlenT : tt.length = m.tables.length := htables.length_eq.symm
  have hlenM : mt.length = m.memories.length := hmems.length_eq.symm
  have hlenE : refsE.length = m.elems.length := he.length_eq.symm
  have hlenE' : rt.length = m.elems.length := helems.length_eq.symm
  have hlenXF : (ExternAddr.funcs xas).length = (ExternType.funcs ixt).length :=
    (ExternAddrOk.forall₂_funcs hxas).length_eq
  have hlenXG : (ExternAddr.globals xas).length = (ExternType.globals ixt).length :=
    (ExternAddrOk.forall₂_globals hxas).length_eq
  have hlenXT : (ExternAddr.tables xas).length = (ExternType.tables ixt).length :=
    (ExternAddrOk.forall₂_tables hxas).length_eq
  have hlenXM : (ExternAddr.mems xas).length = (ExternType.mems ixt).length :=
    (ExternAddrOk.forall₂_mems hxas).length_eq
  -- store extension
  have hext : Extend s s' := Extend.of_appends eF eG eT eM eE eD
  -- the new function instances
  have hnewF : ∀ (i : Nat) (d : FuncType) (fn : Func), ft[i]? = some d → m.funcs[i]? = some fn →
      s'.funcInst? (s.funcs.length + i) = some ⟨d, mi, .wasm fn⟩ := by
    intro i d fn hd hfn
    show s'.funcs[s.funcs.length + i]? = _
    rw [eF, getElem?_append_right_add, List.getElem?_map,
      show (ft.zip m.funcs)[i]? = some (d, fn) from List.getElem?_zip_eq_some.mpr ⟨hd, hfn⟩]
    rfl
  -- every function address of the initial instance is allocated in the new store
  have hinitF : (ModuleInst.initial s m xas).funcs = mi.funcs := by
    rw [miF]; rfl
  have hfuncAddrAlloc : ∀ (x : FuncIdx) (a : FuncAddr),
      (ModuleInst.initial s m xas).funcAddr? x = some a → (s'.funcInst? a).isSome := by
    intro x a hx
    have hmem : a ∈ mi.funcs := hinitF ▸ List.mem_of_getElem? hx
    rw [miF, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · obtain ⟨ftx, hok⟩ := forall₂_exists_left (ExternAddrOk.forall₂_funcs hxas) hmem
      obtain ⟨fi, hfi, -⟩ := hok.func_inv
      rw [hext.funcInst? hfi]
      exact rfl
    · simp only [List.mem_map, List.mem_range] at hmem
      obtain ⟨i, hi, rfl⟩ := hmem
      have hd : i < ft.length := by omega
      rw [hnewF i ft[i] m.funcs[i] (List.getElem?_eq_getElem hd)
        (List.getElem?_eq_getElem hi)]
      exact rfl
  -- the imported globals agree with the initial instance
  have hinitG : (ModuleInst.initial s m xas).globals = ExternAddr.globals xas := rfl
  have hglobalInit : ∀ (x : GlobalIdx) (gtx : GlobalType), C'.globals[x.toNat]? = some gtx →
      ∃ a gi, (ModuleInst.initial s m xas).globalAddr? x = some a ∧
        s.globalInst? a = some gi ∧ gi.type = gtx := by
    intro x gtx hx
    rw [hC'] at hx
    obtain ⟨a, ha, hok⟩ := forall₂_getElem? (ExternAddrOk.forall₂_globals hxas) _ _ hx
    obtain ⟨gi, hgi, hty⟩ := hok.global_inv
    exact ⟨a, gi, ha, hgi, hty⟩
  have hCfl : C'.funcs.length ≤ (ModuleInst.initial s m xas).funcs.length := by
    rw [hC', hinitF, miF]
    simp [hlenXF, hlenF]
  -- the values the global initializers produce are typed
  have hGok : List.Forall₂ (fun (v : Val) (g : GlobalType) => ValOk s' v g.value) valsG gt := by
    refine forall₂_zip ?_ hglobals hg
    intro g gtx v hgok hev
    exact exprOkConst_valOk hs hext hCfl hglobalInit hfuncAddrAlloc hgok.2.2 hev
  -- the references the element initializers produce are typed
  have hEok : List.Forall₂ (fun (rs : List Ref) (r : RefType) => ∀ x ∈ rs, RefOk s' x r)
      refsE rt := by
    refine forall₂_zip ?_ helems he
    intro e rtx rs hok hev x hx
    obtain ⟨ex, hex, hevx⟩ := forall₂_exists_right hev hx
    have := exprOkConst_valOk hs hext hCfl hglobalInit hfuncAddrAlloc (hok.2.1 ex hex) hevx
    cases this with
    | ref hr => exact hr
  -- the new global, table, memory, element and data instances
  have hnewG : ∀ (i : Nat) (g : GlobalType) (v : Val), gt[i]? = some g → valsG[i]? = some v →
      s'.globalInst? (s.globals.length + i) = some ⟨g, v⟩ := by
    intro i g v hg' hv
    show s'.globals[s.globals.length + i]? = _
    rw [eG, getElem?_append_right_add, List.getElem?_map,
      show ((m.globals.map Global.type).zip valsG)[i]? = some (g, v) from
        List.getElem?_zip_eq_some.mpr ⟨by rw [← hgt]; exact hg', hv⟩]
    rfl
  have hnewT : ∀ (i : Nat) (ttx : TableType), tt[i]? = some ttx →
      s'.tableInst? (s.tables.length + i) =
        some ⟨ttx, List.replicate ttx.limits.min.val (.null ttx.element)⟩ := by
    intro i ttx hx
    show s'.tables[s.tables.length + i]? = _
    rw [eT, getElem?_append_right_add, List.getElem?_map,
      show m.tables[i]? = some ttx from by rw [← htt]; exact hx]
    rfl
  have hnewM : ∀ (i : Nat) (mtx : MemoryType), mt[i]? = some mtx →
      s'.memInst? (s.mems.length + i) =
        some ⟨mtx, ⟨Array.replicate (mtx.limits.min.val * pageSize) 0⟩⟩ := by
    intro i mtx hx
    show s'.mems[s.mems.length + i]? = _
    rw [eM, getElem?_append_right_add, List.getElem?_map,
      show m.memories[i]? = some mtx from by rw [← hmt]; exact hx]
    rfl
  have hnewE : ∀ (i : Nat) (rtx : RefType) (rs : List Ref), rt[i]? = some rtx →
      refsE[i]? = some rs → s'.elemInst? (s.elems.length + i) = some ⟨rtx, rs⟩ := by
    intro i rtx rs hx hrs
    show s'.elems[s.elems.length + i]? = _
    rw [eE, getElem?_append_right_add, List.getElem?_map,
      show ((m.elems.map Elem.type).zip refsE)[i]? = some (rtx, rs) from
        List.getElem?_zip_eq_some.mpr ⟨by rw [← hrt]; exact hx, hrs⟩]
    rfl
  have hnewD : ∀ (i : Nat), i < m.data.length → (s'.dataInst? (s.datas.length + i)).isSome := by
    intro i hi
    show (s'.datas[s.datas.length + i]?).isSome
    rw [eD, getElem?_append_right_add, List.getElem?_map,
      List.getElem?_eq_getElem (by simpa using hi)]
    rfl
  -- every address of the module instance is typed in the new store
  have halloF : List.Forall₂ (fun a ftx => ExternAddrOk s' (.func a) (.func ftx))
      mi.funcs (ExternType.funcs ixt ++ ft) := by
    rw [miF]
    refine List.rel_append
      ((ExternAddrOk.forall₂_funcs hxas).imp fun _ _ h => h.extend hs hext) ?_
    refine forall₂_rangeMap _ _ hlenF (fun i hi => ?_)
    exact ExternAddrOk.func (hnewF i ft[i] m.funcs[i] (List.getElem?_eq_getElem hi)
      (List.getElem?_eq_getElem (by omega)))
  have halloG : List.Forall₂ (fun a gtx => ExternAddrOk s' (.global a) (.global gtx))
      mi.globals (ExternType.globals ixt ++ gt) := by
    rw [miG]
    refine List.rel_append
      ((ExternAddrOk.forall₂_globals hxas).imp fun _ _ h => h.extend hs hext) ?_
    refine forall₂_rangeMap _ _ hlenG' (fun i hi => ?_)
    exact ExternAddrOk.global (hnewG i gt[i] valsG[i] (List.getElem?_eq_getElem hi)
      (List.getElem?_eq_getElem (by omega)))
  have halloT : List.Forall₂ (fun a ttx => ExternAddrOk s' (.table a) (.table ttx))
      mi.tables (ExternType.tables ixt ++ tt) := by
    rw [miTb]
    refine List.rel_append
      ((ExternAddrOk.forall₂_tables hxas).imp fun _ _ h => h.extend hs hext) ?_
    refine forall₂_rangeMap _ _ hlenT (fun i hi => ?_)
    exact ExternAddrOk.table (hnewT i tt[i] (List.getElem?_eq_getElem hi))
  have halloM : List.Forall₂ (fun a mtx => ExternAddrOk s' (.mem a) (.memory mtx))
      mi.mems (ExternType.mems ixt ++ mt) := by
    rw [miM]
    refine List.rel_append
      ((ExternAddrOk.forall₂_mems hxas).imp fun _ _ h => h.extend hs hext) ?_
    refine forall₂_rangeMap _ _ hlenM (fun i hi => ?_)
    exact ExternAddrOk.mem (hnewM i mt[i] (List.getElem?_eq_getElem hi))
  -- the module instance realizes the module context
  have hMI : ModuleInstOk s' mi C := by
    have hctx : C =
        { types := mi.types, funcs := ExternType.funcs ixt ++ ft,
          globals := ExternType.globals ixt ++ gt, tables := ExternType.tables ixt ++ tt,
          mems := ExternType.mems ixt ++ mt, elems := rt,
          datas := mi.datas.map (fun _ => ()), refs := funcIdxNonFuncs m } := by
      rw [hC, miT, hft', miD]
      simp [Function.comp_def, List.map_const', List.length_range]
    rw [hctx]
    refine ModuleInstOk.mk ?_ halloF halloG halloT halloM ?_ ?_ ?_ ?_ ?_ ?_
    · intro ftx hftx
      rw [miT] at hftx
      obtain ⟨d, -, hok⟩ := forall₂_exists_left htypes hftx
      exact hok
    · rw [miE]
      refine forall₂_rangeMap _ _ hlenE' (fun i hi => ?_)
      refine ⟨⟨rt[i], refsE[i]⟩, hnewE i rt[i] refsE[i] (List.getElem?_eq_getElem hi)
        (List.getElem?_eq_getElem (by omega)), ?_, rfl⟩
      exact forall₂_getElem hEok (by omega) hi
    · intro a hamem
      rw [miD] at hamem
      simp only [List.mem_map, List.mem_range] at hamem
      obtain ⟨i, hi, rfl⟩ := hamem
      exact Option.isSome_iff_exists.mp (hnewD i hi)
    · intro xi hxi
      obtain ⟨e, -, hinst⟩ :=
        forall₂_exists_right (forall₂_of_mapM (allocModule?_exports ha)) hxi
      obtain ⟨-, hmem⟩ := instExport?_spec hinst
      simp only [List.mem_append, List.mem_map] at hmem
      rcases hmem with ((⟨a, hamem, heq⟩ | ⟨a, hamem, heq⟩) | ⟨a, hamem, heq⟩) |
        ⟨a, hamem, heq⟩
      · obtain ⟨ftx, hok⟩ := forall₂_exists_left halloF hamem
        exact ⟨_, heq ▸ hok⟩
      · obtain ⟨gtx, hok⟩ := forall₂_exists_left halloG hamem
        exact ⟨_, heq ▸ hok⟩
      · obtain ⟨ttx, hok⟩ := forall₂_exists_left halloT hamem
        exact ⟨_, heq ▸ hok⟩
      · obtain ⟨mtx, hok⟩ := forall₂_exists_left halloM hamem
        exact ⟨_, heq ▸ hok⟩
    · rw [forall₂_map_eq ((forall₂_of_mapM (allocModule?_exports ha)).imp
        fun e xi h => (instExport?_spec h).1)]
      exact hnames
    · intro xi hxi
      obtain ⟨e, -, hinst⟩ :=
        forall₂_exists_right (forall₂_of_mapM (allocModule?_exports ha)) hxi
      exact (instExport?_spec hinst).2
    · intro x hx
      have hlt := funcIdxNonFuncs_lt (hfc := by rw [hC, hC']) hglobals helems hexports x hx
      rw [hC] at hlt
      simp only [List.length_append] at hlt
      rw [miF]
      simp only [List.length_append, List.length_map, List.length_range]
      omega
  refine ⟨?_, hMI, hext⟩
  refine StoreOk.mk_of_alloc hs hext ?_ ?_ ?_ ?_ ?_
  · intro fi hfi
    rw [eF, List.mem_append] at hfi
    rcases hfi with hfi | hfi
    · exact .inl hfi
    · refine .inr ?_
      simp only [List.mem_map] at hfi
      obtain ⟨⟨pa, pb⟩, hp, rfl⟩ := hfi
      obtain ⟨i, hpi⟩ := List.mem_iff_getElem?.mp hp
      obtain ⟨hd, hfn⟩ := List.getElem?_zip_eq_some.mp hpi
      have hi : i < m.funcs.length := (List.getElem?_eq_some_iff.mp hfn).1
      have hi' : i < ft.length := by omega
      obtain rfl : pa = ft[i] := Option.some.inj (hd.symm.trans
        (List.getElem?_eq_getElem hi'))
      obtain rfl : pb = m.funcs[i] := Option.some.inj (hfn.symm.trans
        (List.getElem?_eq_getElem hi))
      have hok := forall₂_getElem hfuncs hi hi'
      refine .wasm ?_ hMI rfl hok
      cases hok with
      | mk hx _ =>
        obtain ⟨d, hdok⟩ := forall₂_exists_left htypes
          (List.mem_of_getElem? (hCt ▸ hx))
        exact hdok.2
  · intro gi hgi
    rw [eG, List.mem_append] at hgi
    rcases hgi with hgi | hgi
    · exact .inl hgi
    · refine .inr ?_
      simp only [List.mem_map] at hgi
      obtain ⟨⟨pa, pb⟩, hp, rfl⟩ := hgi
      obtain ⟨i, hpi⟩ := List.mem_iff_getElem?.mp hp
      obtain ⟨hd, hv⟩ := List.getElem?_zip_eq_some.mp hpi
      rw [← hgt] at hd
      have hi : i < gt.length := (List.getElem?_eq_some_iff.mp hd).1
      have hi' : i < valsG.length := (List.getElem?_eq_some_iff.mp hv).1
      obtain rfl : pa = gt[i] := Option.some.inj (hd.symm.trans
        (List.getElem?_eq_getElem hi))
      obtain rfl : pb = valsG[i] := Option.some.inj (hv.symm.trans
        (List.getElem?_eq_getElem hi'))
      exact ⟨(forall₂_getElem hglobals (by omega) hi).2.1, forall₂_getElem hGok hi' hi⟩
  · intro ti hti
    rw [eT, List.mem_append] at hti
    rcases hti with hti | hti
    · exact .inl hti
    · refine .inr ?_
      simp only [List.mem_map] at hti
      obtain ⟨ttx, htx, rfl⟩ := hti
      obtain ⟨ttj, hok⟩ := forall₂_exists_left htables htx
      refine ⟨hok.2, by simp, ?_⟩
      intro r hr
      obtain rfl := List.eq_of_mem_replicate hr
      exact .null _
  · intro mx hmx
    rw [eM, List.mem_append] at hmx
    rcases hmx with hmx | hmx
    · exact .inl hmx
    · refine .inr ?_
      simp only [List.mem_map] at hmx
      obtain ⟨mtx, hmtx, rfl⟩ := hmx
      obtain ⟨mtj, hok⟩ := forall₂_exists_left hmems hmtx
      exact ⟨hok.2, by simp [ByteArray.size]⟩
  · intro ei hei
    rw [eE, List.mem_append] at hei
    rcases hei with hei | hei
    · exact .inl hei
    · refine .inr ?_
      simp only [List.mem_map] at hei
      obtain ⟨⟨pa, pb⟩, hp, rfl⟩ := hei
      obtain ⟨i, hpi⟩ := List.mem_iff_getElem?.mp hp
      obtain ⟨hd, hrs⟩ := List.getElem?_zip_eq_some.mp hpi
      rw [← hrt] at hd
      have hi : i < rt.length := (List.getElem?_eq_some_iff.mp hd).1
      have hi' : i < refsE.length := (List.getElem?_eq_some_iff.mp hrs).1
      obtain rfl : pa = rt[i] := Option.some.inj (hd.symm.trans
        (List.getElem?_eq_getElem hi))
      obtain rfl : pb = refsE[i] := Option.some.inj (hrs.symm.trans
        (List.getElem?_eq_getElem hi'))
      exact forall₂_getElem hEok hi' hi


/-! ### The program `$instantiate` runs -/

/-- A `flatMap` of `eps -> eps` programs is an `eps -> eps` program. -/
theorem InstrsOk.flatMap_nil {α : Type} {C : Context} {l : List α} {g : α → List Instr}
    (h : ∀ a ∈ l, InstrsOk C (g a) ⟨[], []⟩) : InstrsOk C (l.flatMap g) ⟨[], []⟩ := by
  induction l with
  | nil => exact .empty
  | cons a l ih =>
    rw [List.flatMap_cons]
    exact .seq (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- An element of `(range n).zip l` is an index-value pair of `l`. -/
theorem mem_zip_range {α : Type} {n : Nat} {l : List α} {p : Nat × α}
    (h : p ∈ (List.range n).zip l) : p.1 < n ∧ l[p.1]? = some p.2 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.mp hi
  have hi1 : i < n := by simpa using (List.getElem?_eq_some_iff.mp h1).1
  have hp1 : p.1 = i := by simpa using ((List.getElem?_eq_some_iff.mp h1).2).symm
  rw [hp1]
  exact ⟨hi1, h2⟩

/-- `$runelem`/`$rundata` pass the segment index as a `u32`; in range it is the
index back again. -/
theorem idx_ofNat_toNat {kind : IndexKind} {i : Nat} (h : i < 2 ^ 32) :
    (⟨Fin.ofNat _ i⟩ : Idx kind).toNat = i := by
  simp only [Idx.toNat, Fin.ofNat]
  omega

/-- The tail `(CONST I32 0) (CONST I32 n) instr instr'` of `$runelem`/`$rundata`. -/
theorem InstrsOk.segTail {C : Context} {ii jj : Instr} (c₁ c₂ : BitVec 32)
    (hi : InstrOk C ii ⟨[.val .i32, .val .i32, .val .i32], []⟩)
    (hj : InstrOk C jj ⟨[], []⟩) :
    InstrsOk C [Instr.intConst .i32 c₁, Instr.intConst .i32 c₂, ii, jj]
      ⟨[.val .i32], []⟩ := by
  have h1 : InstrsOk C [Instr.intConst .i32 c₁] ⟨[.val .i32], [.val .i32, .val .i32]⟩ := by
    simpa [ValType.i32] using InstrsOk.frame (ts := [CValType.val .i32])
      (InstrsOk.instr (InstrOk.intConst (t := .i32) (c := c₁)))
  have h2 : InstrsOk C [Instr.intConst .i32 c₂]
      ⟨[.val .i32, .val .i32], [.val .i32, .val .i32, .val .i32]⟩ := by
    simpa [ValType.i32] using InstrsOk.frame (ts := [CValType.val .i32, CValType.val .i32])
      (InstrsOk.instr (InstrOk.intConst (t := .i32) (c := c₂)))
  have h3 : InstrsOk C [ii, jj] ⟨[.val .i32, .val .i32, .val .i32], []⟩ :=
    .seq (.instr hi) (.instr hj)
  simpa using InstrsOk.seq h1 (InstrsOk.seq h2 h3)

/-- A whole `$runelem`/`$rundata` segment program. -/
theorem InstrsOk.segment {C : Context} {off : Expr} {ii jj : Instr} (c₁ c₂ : BitVec 32)
    (hoff : InstrsOk C off ⟨[], [.val .i32]⟩)
    (hi : InstrOk C ii ⟨[.val .i32, .val .i32, .val .i32], []⟩)
    (hj : InstrOk C jj ⟨[], []⟩) :
    InstrsOk C (off ++ [Instr.intConst .i32 c₁, Instr.intConst .i32 c₂, ii, jj]) ⟨[], []⟩ :=
  .seq hoff (InstrsOk.segTail c₁ c₂ hi hj)

/-- `$runelem(elem, i)` (`9-module:154-159`) is typed in the module context. -/
theorem runElem_ok {C C' : Context} {e : Elem} {rtx : RefType} {i : Nat}
    (hi : i < 2 ^ 32) (hCe : C.elems[i]? = some rtx)
    (hft : C'.funcs = C.funcs) (hrf : C'.refs = C.refs)
    {gs : List GlobalType} (hgl : C.globals = C'.globals ++ gs)
    (hCt : C'.tables = C.tables)
    (hok : ElemOk C' e rtx) : InstrsOk C (runElem i e) ⟨[], []⟩ := by
  have hxe : (⟨Fin.ofNat _ i⟩ : ElemIdx).toNat = i := idx_ofNat_toNat hi
  have hdrop : InstrOk C (.elemDrop ⟨Fin.ofNat _ i⟩) ⟨[], []⟩ :=
    .elemDrop (by rw [hxe]; exact hCe)
  simp only [runElem]
  cases hm : e.mode with
  | passive => exact .empty
  | declare => exact .instr hdrop
  | active x off =>
    have hmode : ElemModeOk C' (.active x off) rtx := hm ▸ hok.2.2
    cases hmode with
    | active hx hrt hoff =>
      refine InstrsOk.segment _ _ (ExprOkConst.weaken hft hrf hgl hoff).typed ?_ hdrop
      exact .tableInit (by rw [← hCt]; exact hx) (by rw [hxe]; exact hCe) hrt

/-- `$rundata(data, i)` (`9-module:161-165`) is typed in the module context. -/
theorem runData_ok {C C' : Context} {d : Data} {i : Nat}
    (hi : i < 2 ^ 32) (hCd : C.datas[i]? = some ())
    (hft : C'.funcs = C.funcs) (hrf : C'.refs = C.refs)
    {gs : List GlobalType} (hgl : C.globals = C'.globals ++ gs)
    (hCm : C'.mems = C.mems)
    (hok : DataOk C' d) : InstrsOk C (runData i d) ⟨[], []⟩ := by
  have hxd : (⟨Fin.ofNat _ i⟩ : DataIdx).toNat = i := idx_ofNat_toNat hi
  have hdrop : InstrOk C (.dataDrop ⟨Fin.ofNat _ i⟩) ⟨[], []⟩ :=
    .dataDrop (by rw [hxd]; exact hCd)
  simp only [runData]
  cases hm : d.mode with
  | passive => exact .empty
  | active x off =>
    have hmode : DataModeOk C' (.active x off) := hm ▸ hok
    cases hmode with
    | active hx hmem hoff =>
      refine InstrsOk.segment _ _ (ExprOkConst.weaken hft hrf hgl hoff).typed ?_ hdrop
      exact .memoryInit (by rw [← hCm]; exact hmem) (by rw [hxd]; exact hCd)


/-- A pointwise relation transports an index resolution on the left to one on
the right. -/
theorem forall₂_getElem?_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ (i : Nat) (a : α), l₁[i]? = some a →
      ∃ b, l₂[i]? = some b ∧ R a b := by
  induction h with
  | nil => intro i a hi; simp at hi
  | cons hx hs ih =>
    intro i a hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨_, rfl, hx⟩
    | succ n =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨b, hb, hR⟩ := ih n a hi
      exact ⟨b, by simpa using hb, hR⟩

/-- **The program `$instantiate` runs is typed in the module context**
(`9-module:188-189`). -/
theorem initCode_ok {C C' : Context} {m : Module} {gts : List GlobalType} {rts : List RefType}
    (hCe : C.elems = rts) (hCd : C.datas = m.data.map fun _ => ())
    (hft : C'.funcs = C.funcs) (hrf : C'.refs = C.refs)
    (hgl : C.globals = C'.globals ++ gts) (hCt : C'.tables = C.tables) (hCm : C'.mems = C.mems)
    (helems : List.Forall₂ (ElemOk C') m.elems rts)
    (hdatas : ∀ d ∈ m.data, DataOk C' d)
    (hstart : ∀ x, m.start = some x → StartOk C x)
    (hbE : m.elems.length ≤ 2 ^ 32) (hbD : m.data.length ≤ 2 ^ 32) :
    InstrsOk C (runElems m ++ runDatas m ++
      (match m.start with | some x => [Instr.call x] | none => [])) ⟨[], []⟩ := by
  refine .seq (t₂ := []) (.seq (t₂ := []) ?_ ?_) ?_
  · refine InstrsOk.flatMap_nil ?_
    rintro ⟨i, e⟩ hie
    obtain ⟨hi, hget⟩ := mem_zip_range hie
    obtain ⟨rtx, hrtx, hok⟩ := forall₂_getElem?_left helems i e hget
    exact runElem_ok (by omega) (by rw [hCe]; exact hrtx) hft hrf hgl hCt hok
  · refine InstrsOk.flatMap_nil ?_
    rintro ⟨i, d⟩ hid
    obtain ⟨hi, hget⟩ := mem_zip_range hid
    refine runData_ok (by omega) ?_ hft hrf hgl hCm (hdatas d (List.mem_of_getElem? hget))
    rw [hCd, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  · cases hst : m.start with
    | none => exact .empty
    | some x =>
      have hx := hstart x hst
      exact .instr (InstrOk.call hx)


end Instantiation

/-! ## Instantiation (`9-module:167-189`) -/

/-- **`$instantiate` is well typed.** Instantiating a valid module against
typed external addresses in a valid store yields a configuration of empty
result type: the `$runelem`/`$rundata`/`$start` program (`9-module:188-189`)
runs in a frame whose module instance realizes the module-level context.

The host contract plays no part: `$instantiate` neither calls a host function
nor inspects one, so `hhost` is unused here and is kept only to line the
statement up with `Instantiate.safe` and `Module.safe`. -/
theorem Instantiate.ok {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {m : Module} {xas : List ExternAddr} {c : Config H} (hs : StoreOk s)
    (h : Instantiate P host s m xas c) : ConfigOk c [] ∧ Extend s c.store := by
  have _ := hhost
  obtain ⟨ixt, xtE, hm, hxas⟩ := h.valid
  obtain ⟨hbE, hbD, -, -⟩ := h.bounded
  obtain ⟨valsG, refsE, s', mi, hg, he, ha, rfl⟩ := h.run
  cases hm with
  | mk htypes himports hglobals htables hmems helems hdatas hfuncs hstart hexports hmemsle
      hnames hC hC' =>
    rename_i ft' ft gt tt mt rt C C'
    obtain ⟨hs', hMI, hext⟩ := Instantiate.alloc_ok (P := P) (host := host) hs htypes hglobals
      htables hmems helems hfuncs hexports hnames hC hC' hxas hg he ha
    refine ⟨⟨C, ⟨hs', ⟨C, [], hMI, .nil, by simp⟩⟩, ?_⟩, hext⟩
    refine AdminsOk.of_instrsOk (initCode_ok (gts := gt) ?_ ?_ ?_ ?_ ?_ ?_ ?_ helems hdatas
      hstart hbE hbD)
    · rw [hC]
    · rw [hC]
    · rw [hC, hC']
    · rw [hC, hC']
    · rw [hC, hC']
    · rw [hC, hC']
    · rw [hC, hC']

/-- **Type safety of instantiation.** Every configuration reachable from an
instantiation in a valid store is typed (at the empty result type), runs over a
store extending the embedder's original `s` — not merely the post-allocation
store — and is terminal or can step. -/
theorem Instantiate.safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {m : Module} {xas : List ExternAddr} {c c' : Config H} (hs : StoreOk s)
    (h : Instantiate P host s m xas c) (hsteps : Steps P host c c') :
    ConfigOk c' [] ∧ Extend s c'.store ∧ (c'.Terminal ∨ ∃ c'', Step P host c' c'') := by
  obtain ⟨hc, hext⟩ := Instantiate.ok hhost hs h
  obtain ⟨hok, hext', hprog⟩ := Steps.safe hhost hc hsteps
  exact ⟨hok, hext.trans hext', hprog⟩

/-- **Soundness, spec shape.** A valid 2.0 module `m : xtI -> xtE`
(`Module_ok`, `6-typing:682`), instantiated in a valid store against external
addresses of the import types `xtI`, never reaches a stuck configuration, and
only ever extends the store. -/
theorem Module.safe {P : Profile} {host : HostSemantics H} (hhost : HostOk host)
    {s : Store H} {m : Module} {xtI xtE : List ExternType} {xas : List ExternAddr}
    {c c' : Config H} (hs : StoreOk s) (hm : ModuleOk m xtI xtE)
    (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    (h : Instantiate P host s m xas c) (hsteps : Steps P host c c') :
    ConfigOk c' [] ∧ Extend s c'.store ∧ (c'.Terminal ∨ ∃ c'', Step P host c' c'') :=
  Instantiate.safe hhost hs { h with valid := ⟨xtI, xtE, hm, hxas⟩ } hsteps

end Silmaril.Wasm.V2.Execution
