module

public import Silmaril.Raw.Wasm.Versions.V2.ToCore.Execution
public import Silmaril.Raw.Wasm.Versions.V2.Execution.Properties
public import Silmaril.Wasm.V2.ToCore.Validation
public import Silmaril.Wasm.Execution.Core.Instantiation

@[expose] public section

/-! # Wasm 2.0 instantiation is simulated by Core 3.0 instantiation (milestones)

The instantiation half of the `2.0 ⊆ 3.0` subset theorem, the analogue of
`Silmaril/Wasm/Lime1/ToCore/Instantiation.lean`: Wasm 2.0's `$instantiate`
(`9-module:167-189`, transcribed as
`Silmaril.Wasm.V2.Execution.Instantiate`) is Core 3.0's `$instantiate`
(`Silmaril.Wasm.Execution.Core.Instantiate`) on the image of the module, the
store and the external addresses, and the two configurations the two
`$instantiate`s produce are related by the `Sim` of `V2/ToCore/Runtime.lean`.

Line references `9-module:NN` point into
`specification/wasm-2.0/9-module.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (hash-pinned in
`specs/wasm/core-2.0.json`).

## What is *much* simpler than in `Lime1`

Lime1's instantiation is a *function* (`prepare?`) that allocates, resolves and
applies every segment **atomically**, outside the machine; the Core 3.0 segment
programs then have to be run step by step and matched against it, which is what
`Lime1/ToCore/Instantiation.lean` spends its `elemLoop_core`/`dataLoop_core`
inductions on.

Wasm 2.0 is written exactly like Core 3.0: `$instantiate` *returns a
configuration* whose code is `instr_E* instr_D* (CALL x)?`
(`9-module:168`, `:188-189`), and the segments are initialised by the ordinary
reduction rules for `TABLE.INIT`/`MEMORY.INIT`, which are lock-step with Core
3.0's (see the module docstring of `V2/ToCore/Execution.lean`). So there are no
loop inductions here at all: `instantiate_sim` relates the two configurations
`$instantiate` returns, and everything after that is `Steps.toCore`.

## Side conditions (`InstantiationBounds`)

**`noGlobals` is still needed, and the brief's reason for dropping it is wrong.**
The 2.0 `$instantiate` does **not** evaluate global initialisers the way Core
3.0's `$evalglobals` does. `9-module:177-185` reads

```
  -- if moduleinst_init = { TYPES functype*, FUNCS …, GLOBALS $globals(externaddr*) }
  -- if f_init = { MODULE moduleinst_init }
  -- if z = s; f_init
  -- (Eval_expr : z; expr_G ~>* z; val)*
```

— every `expr_G` is evaluated in the **same, fixed** state `z`, under a module
instance whose `GLOBALS` are only the *imported* ones, and **nothing is
allocated**: the 2.0 store grows by the module's globals exactly once, in
`$allocmodule`. Core 3.0's `$evalglobals`
(`Silmaril.Wasm.Execution.Core.EvalGlobals`) instead *allocates* each global
into the store as it evaluates it, so that a later initialiser can read an
earlier one (3.0's constant expressions may do that); `$allocmodule` then
allocates the module's globals a **second** time, on top. Consequently, for a
module with `n > 0` defined globals,

* the Core store after instantiation has `n` unreachable auxiliary global
  instances sitting between the imported globals and the module's own ones, so
  `Store.toCore s' = some (ToCore.Store.erase Sa)` is false; and
* the module instance's global addresses differ by exactly `n`, so
  `ToCore.ModuleInstSim` is false.

This is the identical defect `Lime1.Execution.InstantiationBounds.noGlobals`
records, for the identical reason, and lifting it needs the same thing: a
simulation up to a renaming of global addresses. It is **not** a SpecTec erratum
— both specifications are internally consistent, and 3.0's extra allocation is
forced by extended-const initialisers, which 2.0 does not have (`Instr_const`,
`6-typing:543-557`, admits `GLOBAL.GET x` only for an *imported immutable*
global). It is a limitation of the statement, recorded here and reported.

**`storeWF` is needed** because `Sim` contains `ConfigWF`, which contains
`StoreWF` (`V2/ToCore/Runtime.lean`): the Core machine's `Step_read/call`
resolves the callee's type out of the store where the 2.0 machine does not, and
Core 3.0's 32-bit bulk-operation counters need memories to fit the 32-bit
address space and tables to have fewer than `2^32` entries.

**Lime1's five other fields are *not* needed.**

* `tables` (every table of the initial store has fewer than `2^32` entries) is
  already the third conjunct of 2.0's `StoreWF`, so `storeWF` subsumes it; the
  tables `$alloctable` adds have `|REFS| = i` with `i : u32`, so they satisfy it
  too.
* `data`, `elemSize`, `elemCount` and `dataCount` are already *premises of 2.0's
  own `Instantiate`*: `Silmaril.Wasm.V2.Execution.Instantiate.bounded` records
  exactly the four bounds that `$runelem`/`$rundata` (`9-module:154-165`)
  silently assume, because they emit the segment index as a `u32` `elemidx`/
  `dataidx` and the segment length as `CONST I32 n`. They are therefore
  available for free and are transported to Core 3.0's identical `bounded`
  field.

## Initialiser evaluation does **not** go through `Steps.toCore`

`moduleinst_init` (`9-module:177-181`) lists the *predicted* function addresses
`|s.FUNCS| + i_F`, which are not allocated in `s` yet — that is precisely what
lets a global initialiser or an element initialiser mention `REF.FUNC x` for a
function the module itself defines. But `Sim` contains `ConfigWF`, which
contains `ModWF s f.MODULE` ("every function address of the frame's module is
allocated"), so **`Sim` does not hold of the initialiser configurations** of any
module with a defined function, and `evalExprss_elems` cannot be derived from
`Steps.toCore`.

Its proof is instead the 2.0 analogue of `Lime1.Execution.constFold_core`
(`constInstr_core`/`constExpr_core` below): a direct induction over the five
forms a 2.0 constant expression can take (`Instr_const`, `6-typing:543-557`) —
`t.CONST`, `V128.CONST`, `REF.NULL`, `REF.FUNC x` and `GLOBAL.GET x` for an
imported immutable global. None of the five reads a function *instance* out of
the store (Core 3.0's `Step_read/ref.func` reads `f.MODULE.FUNCS[x]`, not
`s.FUNCS[a]`), so the unallocated predicted addresses are harmless.

Running the argument in this direction needs the 2.0 machine to be
*deterministic on constant expressions*: `$instantiate` only says that
`expr_E ~>* ref` for *some* `ref`, and the Core machine has to produce that same
`ref`. `evalExpr_const_eq` is that determinism, and it rests on
`Silmaril.Wasm.V2.Execution.Step.not_vals` (`val*` is a normal form) together
with the inversion of the two constant instructions that take a step at all,
`REF.FUNC` and `GLOBAL.GET`.

## Statement changes

Three statements below are not the ones the skeleton carried. Each change is
forced; see the individual docstrings for the counterexamples.

* `allocModule_core` gained `hwf : StoreWF s`, `hmemok` and `hximp`. Its
  conclusion `StoreWF s'` is **false** without them: `$allocmodule` only *adds*
  instances, so a malformed `s` stays malformed; a fresh memory of `n` pages has
  `n * 64Ki` bytes, which exceeds the 32-bit address space unless `Memtype_ok`
  (`6-typing:42`) bounds `n` by `2^16`; and the fresh function instances record
  a module instance whose function index space begins with the *imported*
  addresses, which have to be allocated.
* `evalExprss_elems` gained `hconst` and lost `hosts`, `bounds` and `hFl`.
  Without `hconst` it is **false**: its `he` premise only says that each
  initialiser *reduces to* a reference, not that it is an `Instr_const`, and the
  Core machine cannot follow an arbitrary 2.0 run under `moduleinst_init` —
  whose function addresses are deliberately not allocated. `hconst` is what
  `Elem_ok` (`6-typing:612`) gives for every valid module, and
  `elemInit_const_isSome` derives it from `Instantiate.valid`.
* `instantiate_sim` lost `hosts`: host functions play no part in it. That is a
  strengthening.

## Definedness, not a bound

`V2.Module.toCore` and `V2.Execution.Store.toCore` are `Option`-valued, for the
single reason documented in `ToCore/Instructions.lean` (2.0's `CVTOP` is
untyped). The milestones therefore take `Module.toCore m = some cm` and
`Store.toCore s = some S` as ordinary hypotheses, in the style of
`V2.Validation.ModuleOk.toCore`, rather than as `InstantiationBounds` fields:
they are definedness of the embedding, not conditions on the *module*.

## The memory index of `$rundata`

`V2.Execution.runData` ignores the data segment's memory index and emits 2.0's
`MEMORY.INIT i`, whose image is Core 3.0's `MEMORY.INIT 0 i`; Core 3.0's
`runData` emits `MEMORY.INIT y i` for the segment's own `y`. `runData_toCore`
below therefore carries the hypothesis `y = memIdx0`, which
`V2.Execution.DataOk.active_zero` supplies for every valid module — the same
deviation already documented in `V2/Execution/Instantiation.lean`.
-/

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.V2.Validation (Context ModuleOk ModuleValid DataOk)

variable {H : Type}

/-! ## Side conditions -/

/-- Side conditions under which Core 3.0 instantiation simulates Wasm 2.0
instantiation. There are only two; see the module documentation for why each is
needed and why Lime1's other five fields are not. -/
structure InstantiationBounds (s : Store H) (m : Module) : Prop where
  /-- `Sim` contains `ConfigWF`, which contains `StoreWF`: every function
  instance's module names allocated functions (Core 3.0's `Step_read/call`
  reads the store, 2.0's does not), every memory fits the 32-bit address space
  and every table has fewer than `2^32` entries (Core 3.0's bulk operations
  count modulo `2^32`). -/
  storeWF : StoreWF s
  /-- 2.0 evaluates every global initialiser in the *fixed* state `z = s; f_init`
  and allocates the module's globals once, in `$allocmodule`; Core 3.0's
  `$evalglobals` allocates a temporary global instance per initialiser *and*
  `$allocmodule` allocates them again. With `n > 0` defined globals the Core
  store therefore has `n` extra global instances and every global address of the
  module instance is shifted by `n`, so neither the store agreement nor
  `ModuleInstSim` can hold. Identical to
  `Lime1.Execution.InstantiationBounds.noGlobals`; see the module docstring. -/
  noGlobals : m.globals = []

/-! ## The Core 3.0 side of the two segment programs

`Silmaril.Wasm.Execution.Core.Instantiate` writes the code of the configuration
it returns inline; these three definitions name its three pieces so that the
statements below can talk about them. -/

/-- Core 3.0's `$concat_(instr, $runelem_(i, elem*[i])^(i<n_E))`. -/
def coreRunElems (m : Wasm.Module) : List Wasm.Instr :=
  ((List.range m.elems.length).zip m.elems).flatMap fun (i, e) =>
    Silmaril.Wasm.Execution.Core.runElem i e

/-- Core 3.0's `$concat_(instr, $rundata_(j, data*[j])^(j<n_D))`. -/
def coreRunDatas (m : Wasm.Module) : List Wasm.Instr :=
  ((List.range m.data.length).zip m.data).flatMap fun (i, d) =>
    Silmaril.Wasm.Execution.Core.runData i d

/-- The Core 3.0 start code of a module, `(CALL x)?`. -/
def coreStartCode (m : Wasm.Module) : List ToCore.CAdmin :=
  match m.start with
  | some x => [.plain (.call x)]
  | none => []

/-- The Wasm 2.0 start code of a module, `(CALL x)?` (`9-module:168,173`). -/
def startInstrs (m : Module) : List Instr :=
  match m.start with
  | some x => [Instr.call x]
  | none => []

/-- The code of the configuration Core 3.0's `$instantiate` returns. -/
def coreInstantiateCode (m : Wasm.Module) : List ToCore.CAdmin :=
  Silmaril.Wasm.Execution.Core.expression (coreRunElems m) ++
    Silmaril.Wasm.Execution.Core.expression (coreRunDatas m) ++ coreStartCode m

/-! ## Core steps never change the frame's module

Copied from `Silmaril.Wasm.Lime1.Execution.coreStep_frame_module`; the statement
is about the Core 3.0 machine only, so the two proofs are literally the same. -/

theorem coreStep_frame_module {P : Profile} {tgt : ToCore.CHostSemantics H}
    {c c' : ToCore.CConfig H} (h : Silmaril.Wasm.Execution.Core.Step P tgt c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | «variable» h => cases h <;> rfl
  | table h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | _ => rfl

theorem coreSteps_frame_module {P : Profile} {tgt : ToCore.CHostSemantics H}
    {c c' : ToCore.CConfig H} (h : Silmaril.Wasm.Execution.Core.Steps P tgt c c') :
    c'.frame.module = c.frame.module := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [coreStep_frame_module hs, ih]

/-! ## The projections on `externaddr*` commute with the embedding

`$funcs`/`$globals`/`$tables`/`$mems` (`9-module:5-27`) are `filterMap`s in 2.0
and structural recursions in Core 3.0, but they pick out the same addresses. -/

theorem externAddr_funcs_toCore : (xas : List ExternAddr) →
    Silmaril.Wasm.Execution.Core.ExternAddr.funcs (xas.map ExternAddr.toCore) =
      ExternAddr.funcs xas
  | [] => rfl
  | x :: xs => by
    cases x <;>
      simp [ExternAddr.toCore, ExternAddr.funcs,
        Silmaril.Wasm.Execution.Core.ExternAddr.funcs, externAddr_funcs_toCore xs]

theorem externAddr_globals_toCore : (xas : List ExternAddr) →
    Silmaril.Wasm.Execution.Core.ExternAddr.globals (xas.map ExternAddr.toCore) =
      ExternAddr.globals xas
  | [] => rfl
  | x :: xs => by
    cases x <;>
      simp [ExternAddr.toCore, ExternAddr.globals,
        Silmaril.Wasm.Execution.Core.ExternAddr.globals, externAddr_globals_toCore xs]

theorem externAddr_tables_toCore : (xas : List ExternAddr) →
    Silmaril.Wasm.Execution.Core.ExternAddr.tables (xas.map ExternAddr.toCore) =
      ExternAddr.tables xas
  | [] => rfl
  | x :: xs => by
    cases x <;>
      simp [ExternAddr.toCore, ExternAddr.tables,
        Silmaril.Wasm.Execution.Core.ExternAddr.tables, externAddr_tables_toCore xs]

theorem externAddr_mems_toCore : (xas : List ExternAddr) →
    Silmaril.Wasm.Execution.Core.ExternAddr.mems (xas.map ExternAddr.toCore) =
      ExternAddr.mems xas
  | [] => rfl
  | x :: xs => by
    cases x <;>
      simp [ExternAddr.toCore, ExternAddr.mems,
        Silmaril.Wasm.Execution.Core.ExternAddr.mems, externAddr_mems_toCore xs]

theorem externAddr_tags_toCore : (xas : List ExternAddr) →
    Silmaril.Wasm.Execution.Core.ExternAddr.tags (xas.map ExternAddr.toCore) = []
  | [] => rfl
  | x :: xs => by
    cases x <;>
      simp [ExternAddr.toCore, Silmaril.Wasm.Execution.Core.ExternAddr.tags,
        externAddr_tags_toCore xs]

/-! ## Import matching -/

/-- `Externtype_sub` (`6-typing:120-134`) transports to Core 3.0's `ExternSub`.
2.0 has no subtyping between concrete types, so the function and global cases
are equalities and only the limits of tables and memories move. -/
theorem limitsSub_toCore {a b : Limits} (h : Limits.Sub a b) :
    Silmaril.Wasm.Validation.LimitsSub a.toCore b.toCore := by
  cases h with
  | max hmin hmax =>
    refine Silmaril.Wasm.Validation.LimitsSub.max (by simpa [widen32] using hmin) ?_
    intro m hm
    simp only [Option.map_eq_some_iff] at hm
    obtain ⟨m', hm', rfl⟩ := hm
    simpa [widen32] using hmax m' (by simpa using hm')
  | eps hmin =>
    exact Silmaril.Wasm.Validation.LimitsSub.eps (by simpa [Limits.toCore, widen32] using hmin)

theorem externSub_toCore {Δ : Silmaril.Wasm.Validation.TypeCtx} {a b : ExternType}
    (h : ExternType.Sub a b) :
    Silmaril.Wasm.Validation.ExternSub Δ a.toCore b.toCore := by
  cases h with
  | @func x y h =>
    have : x = y := h
    subst this
    exact .func (Silmaril.Wasm.Validation.Sub.refl Δ (k := .«def») trivial _)
  | @global x y h =>
    have : x = y := h
    subst this
    rcases x with ⟨mu, v⟩
    cases mu <;>
      [ exact .global (.const (Silmaril.Wasm.Validation.Sub.refl Δ (k := .val) trivial _));
        exact .global (.var (Silmaril.Wasm.Validation.Sub.refl Δ (k := .val) trivial _)
          (Silmaril.Wasm.Validation.Sub.refl Δ (k := .val) trivial _)) ]
  | @table x y h =>
    obtain ⟨hl, he⟩ := h
    refine .table (.mk (limitsSub_toCore hl) ?_ ?_) <;>
      rw [he] <;> exact Silmaril.Wasm.Validation.Sub.refl Δ (k := .ref) trivial _
  | memory h => exact .mem (.mk (limitsSub_toCore h))

/-- The 2.0 import-matching judgement `ExternAddrOk`
(`V2/Execution/Instantiation.lean`) is Core 3.0's `Externaddr_ok` on the image.
This is the 2.0 analogue of `Lime1.Execution.externAddrOk_import`, and it is
simpler: 2.0 *has* a store typing-free `ExternAddrOk` of its own, with the same
five constructors as Core 3.0's, so the proof is constructor by constructor
rather than a re-derivation from `ImportsMatch`. -/
theorem externAddrOk_toCore {s : Store H} {S : ToCore.CStore H}
    (hS : Store.toCore s = some (ToCore.Store.erase S)) {xa : ExternAddr} {xt : ExternType}
    (h : ExternAddrOk s xa xt) :
    Silmaril.Wasm.Execution.Core.ExternAddrOk S xa.toCore xt.toCore := by
  have hparts := hS
  simp only [Store.toCore, Option.map_eq_some_iff] at hparts
  obtain ⟨fs, -, hSe⟩ := hparts
  have hglob : S.globals = s.globals.map GlobalInst.toCore := by
    have := congrArg (fun (t : ToCore.CStore H) => t.globals) hSe
    simpa [ToCore.Store.erase] using this.symm
  have htab : S.tables = s.tables.map TableInst.toCore := by
    have := congrArg (fun (t : ToCore.CStore H) => t.tables) hSe
    simpa [ToCore.Store.erase] using this.symm
  have hmem : S.mems = s.mems.map MemInst.toCore := by
    have := congrArg (fun (t : ToCore.CStore H) => t.mems) hSe
    simpa [ToCore.Store.erase] using this.symm
  induction h with
  | @func a fi hf =>
    have hty := Store.toCore_funcs_type hS a
    have hcfi : ∃ cfi : ToCore.CFuncInst H, S.funcs[a]? = some cfi ∧
        cfi.type = fi.type.toDefType := by
      rw [Store.funcInst?] at hf
      have hE : (ToCore.Store.erase S).funcs[a]? =
          (S.funcs[a]?).map (fun fi => { fi with module := ToCore.ModuleInst.erase fi.module }) := by
        simp [ToCore.Store.erase]
      rw [hE, hf] at hty
      cases hc : S.funcs[a]? with
      | none => rw [hc] at hty; simp at hty
      | some cfi =>
        rw [hc] at hty
        simp only [Option.map_some, Option.some.injEq] at hty
        exact ⟨cfi, rfl, hty⟩
    obtain ⟨cfi, hcfi, hcty⟩ := hcfi
    have := Silmaril.Wasm.Execution.Core.ExternAddrOk.func hcfi
    rw [hcty] at this
    exact this
  | @global a gi hg =>
    rw [Store.globalInst?] at hg
    have : S.globals[a]? = some gi.toCore := by rw [hglob, List.getElem?_map, hg]; rfl
    exact Silmaril.Wasm.Execution.Core.ExternAddrOk.global this
  | @table a ti ht =>
    rw [Store.tableInst?] at ht
    have : S.tables[a]? = some ti.toCore := by rw [htab, List.getElem?_map, ht]; rfl
    exact Silmaril.Wasm.Execution.Core.ExternAddrOk.table this
  | @mem a mi hm =>
    rw [Store.memInst?] at hm
    have : S.mems[a]? = some mi.toCore := by rw [hmem, List.getElem?_map, hm]; rfl
    exact Silmaril.Wasm.Execution.Core.ExternAddrOk.mem this
  | sub _ hok hsub ih =>
    exact Silmaril.Wasm.Execution.Core.ExternAddrOk.sub ih
      (Silmaril.Wasm.V2.Validation.externTypeOk_toCore _ hok) (externSub_toCore hsub)

/-- The `valid` field of Core 3.0's `$instantiate`: module validity and import
matching transport. The import types are, on the nose, the pointwise images of
the 2.0 ones (`V2.Validation.ModuleOk.toCore`). -/
theorem instantiate_valid {s : Store H} {S : ToCore.CStore H} {m : Module} {cm : Wasm.Module}
    {xas : List ExternAddr} {ixt xt : List ExternType}
    (hS : Store.toCore s = some (ToCore.Store.erase S)) (hcm : Module.toCore m = some cm)
    (hok : ModuleOk m ixt xt) (himp : List.Forall₂ (ExternAddrOk s) xas ixt) :
    ∃ xtE xtI, Silmaril.Wasm.Validation.ModuleOk cm ⟨xtI, xtE⟩ ∧
      List.Forall₂ (Silmaril.Wasm.Execution.Core.ExternAddrOk S)
        (xas.map ExternAddr.toCore) xtI := by
  refine ⟨xt.map ExternType.toCore, ixt.map ExternType.toCore, ModuleOk.toCore hcm hok, ?_⟩
  clear hok hcm
  induction himp with
  | nil => exact .nil
  | cons hh _ ih => exact .cons (externAddrOk_toCore hS hh) ih

/-! ## The segment programs agree

`$runelem`/`$rundata` (`9-module:154-165`) and Core 3.0's `$runelem_`/`$rundata_`
emit the same instruction sequence, modulo the memory index of `MEMORY.INIT`
(see the module docstring). -/

/-- `Expr.toCore` is multiplicative on concatenation. -/
theorem expr_toCore_append {is₁ is₂ : Expr} {cs₁ cs₂ : Wasm.Expr}
    (h₁ : Expr.toCore is₁ = some cs₁) (h₂ : Expr.toCore is₂ = some cs₂) :
    Expr.toCore (is₁ ++ is₂) = some (cs₁ ++ cs₂) := by
  induction is₁ generalizing cs₁ with
  | nil =>
    simp only [Expr.toCore, Option.some.injEq] at h₁
    subst h₁; simpa using h₂
  | cons i is ih =>
    simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁
    obtain ⟨c, hc, cs, hcs, rfl⟩ := h₁
    simp [Expr.toCore, hc, ih hcs]

/-- `List.mapM` over `Option` preserves the length. -/
theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], _, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
                   subst h; rfl
  | a :: l, _, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, -, bs, hbs, rfl⟩ := h
    simp [mapM_length hbs]

/-- `$runelem(elem, i)` maps to `$runelem_(i, elem)` (`9-module:154-159`). -/
theorem runElem_toCore {e : Elem} {ce : Wasm.Elem} (h : Elem.toCore e = some ce) (i : Nat) :
    Expr.toCore (runElem i e) = some (Silmaril.Wasm.Execution.Core.runElem i ce) := by
  obtain ⟨type, init, mode⟩ := e
  simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨is, his, md, hmd, rfl⟩ := h
  have hlen : is.length = init.length := mapM_length his
  cases mode with
  | passive =>
    simp only [ElemMode.toCore, Option.some.injEq] at hmd
    subst hmd
    simp [runElem, Silmaril.Wasm.Execution.Core.runElem, Expr.toCore]
  | declare =>
    simp only [ElemMode.toCore, Option.some.injEq] at hmd
    subst hmd
    simp [runElem, Silmaril.Wasm.Execution.Core.runElem, Expr.toCore, Instr.toCore]
  | active x off =>
    simp only [ElemMode.toCore, Option.map_eq_some_iff] at hmd
    obtain ⟨coff, hcoff, rfl⟩ := hmd
    simp only [runElem, Silmaril.Wasm.Execution.Core.runElem, hlen]
    refine expr_toCore_append hcoff ?_
    simp [Expr.toCore, Instr.toCore]

/-- `$rundata(data, i)` maps to `$rundata_(i, data)` (`9-module:161-165`). The
hypothesis `hx` is the memory index deviation of `V2/Execution/Instantiation.lean`:
2.0's `MEMORY.INIT i` is Core 3.0's `MEMORY.INIT 0 i`, and a valid module's active
data segments all name memory `0` (`DataOk.active_zero`). -/
theorem runData_toCore {d : Data} {cd : Wasm.Data} (h : Data.toCore d = some cd)
    (hx : ∀ (x : MemIdx) (off : Expr), d.mode = .active x off → x = memIdx0) (i : Nat) :
    Expr.toCore (runData i d) = some (Silmaril.Wasm.Execution.Core.runData i cd) := by
  obtain ⟨bytes, mode⟩ := d
  simp only [Data.toCore, Option.map_eq_some_iff] at h
  obtain ⟨md, hmd, rfl⟩ := h
  cases mode with
  | passive =>
    simp only [DataMode.toCore, Option.some.injEq] at hmd
    subst hmd
    simp [runData, Silmaril.Wasm.Execution.Core.runData, Expr.toCore]
  | active x off =>
    simp only [DataMode.toCore, Option.map_eq_some_iff] at hmd
    obtain ⟨coff, hcoff, rfl⟩ := hmd
    have hx0 : x = memIdx0 := hx x off rfl
    subst hx0
    simp only [runData, Silmaril.Wasm.Execution.Core.runData]
    refine expr_toCore_append hcoff ?_
    simp [Expr.toCore, Instr.toCore, memIdx0]

/-- The shape both `$concat_` premises of `$instantiate` have
(`9-module:188-189`): a segment-indexed `flatMap` over a list whose elements
convert pointwise. -/
theorem expr_toCore_flatMap_zip {α β : Type} {R : α → β → Prop}
    {g : Nat → α → List Instr} {cg : Nat → β → List Wasm.Instr}
    (hg : ∀ (i : Nat) (a : α) (b : β), R a b → Expr.toCore (g i a) = some (cg i b)) :
    ∀ (ns : List Nat) {l : List α} {cl : List β}, List.Forall₂ R l cl →
      Expr.toCore ((ns.zip l).flatMap fun p => g p.1 p.2) =
        some ((ns.zip cl).flatMap fun p => cg p.1 p.2)
  | [], _, _, _ => rfl
  | n :: ns, _, _, h => by
    cases h with
    | nil => rfl
    | cons hab hrest =>
      simp only [List.zip_cons_cons, List.flatMap_cons]
      exact expr_toCore_append (hg n _ _ hab) (expr_toCore_flatMap_zip hg ns hrest)

/-- The shape of the image of a module: everything but the four `mapM`ed
sections is a pointwise `map`. -/
theorem module_toCore_shape {m : Module} {cm : Wasm.Module}
    (hcm : Module.toCore m = some cm) :
    cm.types = m.types.map FuncType.toCoreRec ∧
      cm.imports = m.imports.map Import.toCore ∧ cm.tags = [] ∧
      cm.memories = m.memories.map MemoryType.toCore ∧
      cm.tables = m.tables.map TableType.toCoreTable ∧
      cm.start = m.start ∧ cm.exports = m.exports.map Export.toCore ∧
      m.globals.mapM Global.toCore = some cm.globals ∧
      m.funcs.mapM Func.toCore = some cm.funcs := by
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcm
  obtain ⟨gs, hgs, fs, hfs, es, -, ds, -, rfl⟩ := hcm
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hgs, hfs⟩

/-- `$alloctypes` (`Silmaril.Wasm.Execution.Core.allocTypes`) on the image of a
2.0 type section is the pointwise `FuncType.toDefType`: each 2.0 `functype`
becomes one singleton final recursive group, so nothing is rolled or
substituted. -/
theorem allocTypes_toCore (ts : List FuncType) :
    Silmaril.Wasm.Execution.Core.allocTypes (ts.map FuncType.toCoreRec) =
      ts.map FuncType.toDefType :=
  Silmaril.Wasm.Execution.Core.allocTypes_eq (Silmaril.Wasm.V2.Validation.typesOk_map ts {})

/-- The image of a store has as many function instances as the store. -/
theorem store_toCore_funcs_length {s : Store H} {S : ToCore.CStore H}
    (hS : Store.toCore s = some (ToCore.Store.erase S)) : S.funcs.length = s.funcs.length := by
  simp only [Store.toCore, Option.map_eq_some_iff] at hS
  obtain ⟨fs, hfs, hSe⟩ := hS
  have h := congrArg (fun (t : ToCore.CStore H) => t.funcs.length) hSe
  simp only [ToCore.Store.erase, List.length_map] at h
  rw [← h, mapM_length hfs]

/-- The image of a store has the pointwise image of its globals. -/
theorem store_toCore_globals {s : Store H} {S : ToCore.CStore H}
    (hS : Store.toCore s = some (ToCore.Store.erase S)) :
    S.globals = s.globals.map GlobalInst.toCore := by
  simp only [Store.toCore, Option.map_eq_some_iff] at hS
  obtain ⟨fs, -, hSe⟩ := hS
  have := congrArg (fun (t : ToCore.CStore H) => t.globals) hSe
  simpa [ToCore.Store.erase] using this.symm

/-- The element and data sections of the image, as `mapM`s. -/
theorem module_toCore_sections {m : Module} {cm : Wasm.Module}
    (hcm : Module.toCore m = some cm) :
    m.elems.mapM Elem.toCore = some cm.elems ∧ m.data.mapM Data.toCore = some cm.data := by
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcm
  obtain ⟨gs, -, fs, -, es, hes, ds, hds, rfl⟩ := hcm
  exact ⟨hes, hds⟩

/-- The concatenated element-segment programs agree. -/
theorem runElems_toCore {m : Module} {cm : Wasm.Module} (hcm : Module.toCore m = some cm) :
    Expr.toCore (runElems m) = some (coreRunElems cm) := by
  have hes := (module_toCore_sections hcm).1
  have hlen : cm.elems.length = m.elems.length := mapM_length hes
  simp only [runElems, coreRunElems, hlen]
  exact expr_toCore_flatMap_zip (R := fun e ce => Elem.toCore e = some ce)
    (fun i _ _ hab => runElem_toCore hab i) _
    (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hes)

/-- The concatenated data-segment programs agree, for a module all of whose
active data segments name memory `0`. -/
theorem runDatas_toCore {m : Module} {cm : Wasm.Module} (hcm : Module.toCore m = some cm)
    (hx : ∀ d ∈ m.data, ∀ (x : MemIdx) (off : Expr), d.mode = .active x off → x = memIdx0) :
    Expr.toCore (runDatas m) = some (coreRunDatas cm) := by
  have hds := (module_toCore_sections hcm).2
  have hlen : cm.data.length = m.data.length := mapM_length hds
  simp only [runDatas, coreRunDatas, hlen]
  refine expr_toCore_flatMap_zip
    (R := fun (d : Data) (cd : Wasm.Data) => Data.toCore d = some cd ∧
      ∀ (x : MemIdx) (off : Expr), d.mode = .active x off → x = memIdx0)
    (fun i _ _ hab => runData_toCore hab.1 hab.2 i) _ ?_
  exact Silmaril.Wasm.V2.Validation.forall₂_imp_mem
    (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hds) (fun a ha _ hR => ⟨hR, hx a ha⟩)

/-- The start code agrees. -/
theorem startInstrs_toCore {m : Module} {cm : Wasm.Module} (hcm : Module.toCore m = some cm) :
    Expr.toCore (startInstrs m) =
      some (match cm.start with | some x => [Wasm.Instr.call x] | none => []) := by
  have hstart : cm.start = m.start := by
    simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcm
    obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := hcm
    rfl
  rw [hstart]
  cases hs : m.start with
  | none => simp [startInstrs, hs, Expr.toCore]
  | some x => simp [startInstrs, hs, Expr.toCore, Instr.toCore]

/-! ## Allocation -/

/-- The provisional module instance `moduleinst_init` (`9-module:177-181`) is the
image of Core 3.0's. -/
theorem moduleInst_initial_toCore {s : Store H} {S : ToCore.CStore H} {m : Module}
    {cm : Wasm.Module} (hS : Store.toCore s = some (ToCore.Store.erase S))
    (hcm : Module.toCore m = some cm) (xas : List ExternAddr) :
    ToCore.ModuleInstSim (ModuleInst.initial s m xas)
      (Silmaril.Wasm.Execution.Core.ModuleInst.initial S cm (xas.map ExternAddr.toCore)) := by
  obtain ⟨htypes, -, -, -, -, -, -, -, hfuncs⟩ := module_toCore_shape hcm
  have hfl : S.funcs.length = s.funcs.length := store_toCore_funcs_length hS
  have hfn : cm.funcs.length = m.funcs.length := mapM_length hfuncs
  show ToCore.ModuleInst.erase _ = ModuleInst.toCore _
  simp [ToCore.ModuleInst.erase, Silmaril.Wasm.Execution.Core.ModuleInst.initial,
    ModuleInst.initial, ModuleInst.toCore, htypes, allocTypes_toCore, hfl, hfn,
    externAddr_funcs_toCore, externAddr_globals_toCore]

/-! ### Allocation sequences, in closed form

Both `$alloc*s` are the same fold; `allocMany_closed`/`coreAllocMany_closed` give
the store it produces as a single append, which is what makes the two sides
comparable componentwise. The 2.0 and Core 3.0 allocators run their components
in *different orders* (2.0 allocates functions first, Core 3.0 last), but each
allocator touches only its own component, so the resulting stores agree. -/

/-- `(List.range (n+1)).map (L + ·)`, peeled at the left. -/
theorem range_map_succ (L n : Nat) :
    (List.range (n + 1)).map (L + ·) = L :: (List.range n).map ((L + 1) + ·) := by
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp only [Function.comp_apply]
  omega

/-- The closed form of 2.0's `$alloc*s` (`9-module:41-95`). -/
theorem allocMany_closed {α β : Type} (get : Store H → List β) (set : Store H → List β → Store H)
    (g : α → β) (alloc : Store H → α → Store H × Addr)
    (halloc : ∀ s x, alloc s x = (set s (get s ++ [g x]), (get s).length))
    (hgs : ∀ s l, get (set s l) = l) (hss : ∀ s l l', set (set s l) l' = set s l')
    (hsg : ∀ s, set s (get s) = s) :
    ∀ (xs : List α) (s : Store H), allocMany alloc s xs =
      (set s (get s ++ xs.map g), (List.range xs.length).map ((get s).length + ·))
  | [], s => by simp [allocMany, hsg]
  | x :: xs, s => by
    have ih := allocMany_closed get set g alloc halloc hgs hss hsg xs (set s (get s ++ [g x]))
    simp only [allocMany, halloc, ih, hgs, hss, List.length_append, List.map_cons,
      List.length_cons, range_map_succ, List.append_assoc, List.singleton_append,
      List.length_nil, Nat.zero_add]

/-- The closed form of Core 3.0's `$alloc*s`. -/
theorem coreAllocMany_closed {α β : Type} (get : ToCore.CStore H → List β)
    (set : ToCore.CStore H → List β → ToCore.CStore H) (g : α → β)
    (alloc : ToCore.CStore H → α → ToCore.CStore H × Nat)
    (halloc : ∀ s x, alloc s x = (set s (get s ++ [g x]), (get s).length))
    (hgs : ∀ s l, get (set s l) = l) (hss : ∀ s l l', set (set s l) l' = set s l')
    (hsg : ∀ s, set s (get s) = s) :
    ∀ (xs : List α) (s : ToCore.CStore H),
      Silmaril.Wasm.Execution.Core.allocMany alloc s xs =
      (set s (get s ++ xs.map g), (List.range xs.length).map ((get s).length + ·))
  | [], s => by simp [Silmaril.Wasm.Execution.Core.allocMany, hsg]
  | x :: xs, s => by
    have ih := coreAllocMany_closed get set g alloc halloc hgs hss hsg xs (set s (get s ++ [g x]))
    simp only [Silmaril.Wasm.Execution.Core.allocMany, halloc, ih, hgs, hss, List.length_append,
      List.map_cons, List.length_cons, range_map_succ, List.append_assoc, List.singleton_append,
      List.length_nil, Nat.zero_add]

section AllocClosed

variable (s : Store H)

theorem allocFuncs_closed (mi : ModuleInst) (fs : List (FuncType × Func)) :
    allocFuncs s mi fs =
      ({ s with funcs := s.funcs ++ fs.map fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H) },
        (List.range fs.length).map (s.funcs.length + ·)) :=
  allocMany_closed (·.funcs) (fun s l => { s with funcs := l }) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) fs s

theorem allocGlobals_closed (gs : List (GlobalType × Val)) :
    allocGlobals s gs =
      ({ s with globals := s.globals ++ gs.map fun p => (⟨p.1, p.2⟩ : GlobalInst) },
        (List.range gs.length).map (s.globals.length + ·)) :=
  allocMany_closed (·.globals) (fun s l => { s with globals := l }) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) gs s

theorem allocTables_closed (ts : List TableType) :
    allocTables s ts =
      ({ s with tables := s.tables ++ ts.map fun t =>
          (⟨t, List.replicate t.limits.min.val (.null t.element)⟩ : TableInst) },
        (List.range ts.length).map (s.tables.length + ·)) :=
  allocMany_closed (·.tables) (fun s l => { s with tables := l }) _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ts s

theorem allocMems_closed (ts : List MemoryType) :
    allocMems s ts =
      ({ s with mems := s.mems ++ ts.map fun t =>
          (⟨t, ⟨Array.replicate (t.limits.min.val *
            Silmaril.Wasm.Execution.Memory.pageSize) 0⟩⟩ : MemInst) },
        (List.range ts.length).map (s.mems.length + ·)) :=
  allocMany_closed (·.mems) (fun s l => { s with mems := l })
    (fun t => (⟨t, ⟨Array.replicate (t.limits.min.val *
      Silmaril.Wasm.Execution.Memory.pageSize) 0⟩⟩ : MemInst))
    allocMem (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ts s

theorem allocElems_closed (es : List (ElemType × List Ref)) :
    allocElems s es =
      ({ s with elems := s.elems ++ es.map fun p => (⟨p.1, p.2⟩ : ElemInst) },
        (List.range es.length).map (s.elems.length + ·)) :=
  allocMany_closed (·.elems) (fun s l => { s with elems := l })
    (fun p : ElemType × List Ref => (⟨p.1, p.2⟩ : ElemInst))
    (fun (s : Store H) (p : ElemType × List Ref) => allocElem s p.1 p.2)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) es s

theorem allocDatas_closed (bs : List Silmaril.Wasm.Execution.Memory.Bytes) :
    allocDatas s bs =
      ({ s with datas := s.datas ++ bs.map fun b => (⟨b⟩ : DataInst) },
        (List.range bs.length).map (s.datas.length + ·)) :=
  allocMany_closed (·.datas) (fun s l => { s with datas := l })
    (fun b => (⟨b⟩ : DataInst)) allocData
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) bs s

end AllocClosed

section CoreAllocClosed

variable (S : ToCore.CStore H)

theorem coreAllocMems_closed (ms : List Wasm.MemoryType) :
    Silmaril.Wasm.Execution.Core.allocMany Silmaril.Wasm.Execution.Core.allocMem S ms =
      ({ S with mems := S.mems ++ ms.map fun mt =>
          (⟨mt, ByteArray.mk (Array.replicate (mt.limits.min.val *
            Silmaril.Wasm.Execution.Memory.pageSize) 0)⟩ :
            Silmaril.Wasm.Execution.Core.MemInst) },
        (List.range ms.length).map (S.mems.length + ·)) :=
  coreAllocMany_closed (·.mems) (fun s l => { s with mems := l })
    (fun mt => (⟨mt, ByteArray.mk (Array.replicate (mt.limits.min.val *
      Silmaril.Wasm.Execution.Memory.pageSize) 0)⟩ :
      Silmaril.Wasm.Execution.Core.MemInst))
    Silmaril.Wasm.Execution.Core.allocMem
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ms S

theorem coreAllocTables_closed
    (ps : List (Silmaril.Wasm.Validation.CTableType × Silmaril.Wasm.Execution.Core.Ref)) :
    Silmaril.Wasm.Execution.Core.allocMany
        (fun s p => Silmaril.Wasm.Execution.Core.allocTable s p.1 p.2) S ps =
      ({ S with tables := S.tables ++ ps.map fun p =>
          (⟨p.1, List.replicate p.1.limits.min.val p.2⟩ :
            Silmaril.Wasm.Execution.Core.TableInst) },
        (List.range ps.length).map (S.tables.length + ·)) :=
  coreAllocMany_closed (·.tables) (fun s l => { s with tables := l })
    (fun p => (⟨p.1, List.replicate p.1.limits.min.val p.2⟩ :
      Silmaril.Wasm.Execution.Core.TableInst))
    (fun s p => Silmaril.Wasm.Execution.Core.allocTable s p.1 p.2)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ps S

theorem coreAllocDatas_closed (bs : List ByteArray) :
    Silmaril.Wasm.Execution.Core.allocMany Silmaril.Wasm.Execution.Core.allocData S bs =
      ({ S with datas := S.datas ++ bs.map fun b =>
          (⟨b⟩ : Silmaril.Wasm.Execution.Core.DataInst) },
        (List.range bs.length).map (S.datas.length + ·)) :=
  coreAllocMany_closed (·.datas) (fun s l => { s with datas := l })
    (fun b => (⟨b⟩ : Silmaril.Wasm.Execution.Core.DataInst))
    Silmaril.Wasm.Execution.Core.allocData
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) bs S

theorem coreAllocElems_closed
    (ps : List (Silmaril.Wasm.Validation.CRefType × List Silmaril.Wasm.Execution.Core.Ref)) :
    Silmaril.Wasm.Execution.Core.allocMany
        (fun s p => Silmaril.Wasm.Execution.Core.allocElem s p.1 p.2) S ps =
      ({ S with elems := S.elems ++ ps.map fun p =>
          (⟨p.1, p.2⟩ : Silmaril.Wasm.Execution.Core.ElemInst) },
        (List.range ps.length).map (S.elems.length + ·)) :=
  coreAllocMany_closed (·.elems) (fun s l => { s with elems := l })
    (fun p => (⟨p.1, p.2⟩ : Silmaril.Wasm.Execution.Core.ElemInst))
    (fun s p => Silmaril.Wasm.Execution.Core.allocElem s p.1 p.2)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ps S

theorem coreAllocFuncs_closed (miC : ToCore.CModuleInst)
    (ps : List (Silmaril.Wasm.Validation.DefType × Wasm.Func)) :
    Silmaril.Wasm.Execution.Core.allocMany
        (fun s p => Silmaril.Wasm.Execution.Core.allocFunc s p.1
          (Silmaril.Wasm.Execution.Core.FuncCode.wasm p.2) miC) S ps =
      ({ S with funcs := S.funcs ++ ps.map fun p =>
          (⟨p.1, miC, Silmaril.Wasm.Execution.Core.FuncCode.wasm p.2⟩ : ToCore.CFuncInst H) },
        (List.range ps.length).map (S.funcs.length + ·)) :=
  coreAllocMany_closed (·.funcs) (fun s l => { s with funcs := l })
    (fun p => (⟨p.1, miC, Silmaril.Wasm.Execution.Core.FuncCode.wasm p.2⟩ : ToCore.CFuncInst H))
    (fun s p => Silmaril.Wasm.Execution.Core.allocFunc s p.1
      (Silmaril.Wasm.Execution.Core.FuncCode.wasm p.2) miC)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ps S

theorem coreAllocMany_nil {α : Type}
    (alloc : ToCore.CStore H → α → ToCore.CStore H × Nat) :
    Silmaril.Wasm.Execution.Core.allocMany alloc S [] = (S, []) := rfl

end CoreAllocClosed

/-! ### The store `$allocmodule` returns, componentwise -/

/-- Every component of the store `$allocmodule` (`9-module:107-147`) returns, in
closed form. -/
theorem allocModule?_tc_store {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vs rss = some (s', mi)) :
    ∃ fts : List FuncType, (m.funcs.mapM fun fn => m.types[fn.type.toNat]?) = some fts ∧
      vs.length = m.globals.length ∧ rss.length = m.elems.length ∧
      s'.funcs = s.funcs ++ (fts.zip m.funcs).map (fun p => ⟨p.1, mi, .wasm p.2⟩) ∧
      s'.globals = s.globals ++ ((m.globals.map Global.type).zip vs).map
        (fun p => (⟨p.1, p.2⟩ : GlobalInst)) ∧
      s'.tables = s.tables ++ m.tables.map
        (fun t => (⟨t, List.replicate t.limits.min.val (.null t.element)⟩ : TableInst)) ∧
      s'.mems = s.mems ++ m.memories.map (fun t => (⟨t, ⟨Array.replicate
        (t.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize) 0⟩⟩ : MemInst)) ∧
      s'.elems = s.elems ++ ((m.elems.map Elem.type).zip rss).map
        (fun p => (⟨p.1, p.2⟩ : ElemInst)) ∧
      s'.datas = s.datas ++ (m.data.map Data.bytes).map (fun b => (⟨b⟩ : DataInst)) := by
  simp only [allocModule?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq, exists_const] at h
  obtain ⟨fts, hfts, hv, hr, xi, -, hstore, hmi⟩ := h
  subst hmi
  refine ⟨fts, hfts, hv, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [← hstore] <;>
    simp [allocFuncs_closed, allocGlobals_closed, allocTables_closed, allocMems_closed,
      allocElems_closed, allocDatas_closed]

/-- `$allocmodule` preserves store well-formedness.

The three hypotheses are forced: `hwf` because the instances already in `s` are
still there; `hmemok` (`Memtype_ok`, `6-typing:42`) because a fresh memory has
`min` pages and `StoreWF` bounds a memory by the 32-bit address space; and
`hximp` because the fresh function instances record a module instance whose
function index space starts with the *imported* addresses. -/
theorem allocModule_storeWF {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (hwf : StoreWF s) (hmemok : ∀ mt ∈ m.memories, mt.limits.min.val ≤ 2 ^ 16)
    (hximp : ∀ a ∈ ExternAddr.funcs xas, a < s.funcs.length)
    (h : allocModule? s m xas vs rss = some (s', mi)) : StoreWF s' := by
  obtain ⟨fts, hfts, -, -, hfuncs, -, htables, hmems, -, -⟩ := allocModule?_tc_store h
  obtain ⟨hmi_types, hmi_funcs, -, -, -, -, -⟩ := allocModule?_moduleInst h
  have hftslen : fts.length = m.funcs.length := mapM_length hfts
  have hlen : s'.funcs.length = s.funcs.length + m.funcs.length := by
    rw [hfuncs]
    simp [hftslen]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i fi hfi
    have hmem : fi ∈ s'.funcs := by
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hfi
      exact List.getElem_mem hlt
    rw [hfuncs, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · obtain ⟨j, hj⟩ := List.getElem_of_mem hmem
      refine fun a ha => Nat.lt_of_lt_of_le (hwf.1 j fi ?_ a ha) (by omega)
      rw [List.getElem?_eq_getElem hj.1, hj.2]
    · obtain ⟨p, -, hp⟩ := List.mem_map.mp hmem
      intro a ha
      rw [← hp] at ha
      simp only at ha
      rw [hmi_funcs, List.mem_append] at ha
      rcases ha with ha | ha
      · exact Nat.lt_of_lt_of_le (hximp a ha) (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
        rw [List.mem_range] at hk
        rw [hlen]
        exact Nat.add_lt_add_left hk _
  · intro i mem hmem
    have hm : mem ∈ s'.mems := by
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hmem
      exact List.getElem_mem hlt
    rw [hmems, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨j, hj⟩ := List.getElem_of_mem hm
      exact hwf.2.1 j mem (by rw [List.getElem?_eq_getElem hj.1, hj.2])
    · obtain ⟨mt, hmt, rfl⟩ := List.mem_map.mp hm
      have := hmemok mt hmt
      simp only [ByteArray.size, Array.size_replicate]
      calc mt.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize
          ≤ 2 ^ 16 * Silmaril.Wasm.Execution.Memory.pageSize :=
            Nat.mul_le_mul_right _ this
        _ = 2 ^ 32 := by simp [Silmaril.Wasm.Execution.Memory.pageSize]
  · intro i mem hmem
    have hm : mem ∈ s'.mems := by
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hmem
      exact List.getElem_mem hlt
    rw [hmems, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨j, hj⟩ := List.getElem_of_mem hm
      exact hwf.2.2.1 j mem (by rw [List.getElem?_eq_getElem hj.1, hj.2])
    · obtain ⟨mt, -, rfl⟩ := List.mem_map.mp hm
      simp only [ByteArray.size, Array.size_replicate]
      exact Nat.mul_mod_left _ _
  · intro i ti hti
    have ht : ti ∈ s'.tables := by
      obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hti
      exact List.getElem_mem hlt
    rw [htables, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨j, hj⟩ := List.getElem_of_mem ht
      exact hwf.2.2.2 j ti (by rw [List.getElem?_eq_getElem hj.1, hj.2])
    · obtain ⟨tt, -, rfl⟩ := List.mem_map.mp ht
      simp

/-! ### Auxiliary `Option`/`List` lemmas -/

/-- `List.mapM` over `Option` is multiplicative on concatenation. -/
theorem mapM_append_option {α β : Type} {f : α → Option β} :
    ∀ {l₁ l₂ : List α} {b₁ b₂ : List β}, l₁.mapM f = some b₁ → l₂.mapM f = some b₂ →
      (l₁ ++ l₂).mapM f = some (b₁ ++ b₂)
  | [], _, _, _, h₁, h₂ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h₁
    subst h₁; simpa using h₂
  | a :: l, _, _, _, h₁, h₂ => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h₁
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h₁
    simp [hb, mapM_append_option hbs h₂]

/-- A `List.mapM` that factors through a `List.map` on both sides. -/
theorem mapM_map_option {α β γ δ : Type} {f : α → β} {g : β → Option γ} {h : α → Option δ}
    {k : δ → γ} (hfg : ∀ a, g (f a) = (h a).map k) :
    ∀ {l : List α} {d : List δ}, l.mapM h = some d → (l.map f).mapM g = some (d.map k)
  | [], _, hd => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hd
    subst hd; rfl
  | a :: l, _, hd => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hd
    obtain ⟨b, hb, bs, hbs, rfl⟩ := hd
    simp [hfg a, hb, mapM_map_option hfg hbs]

/-- Zipping a mapped list with a constant list of the same length. -/
theorem zip_map_replicate {α β γ : Type} (g : α → β) (c : γ) : ∀ l : List α,
    (l.map g).zip (List.replicate l.length c) = l.map fun x => (g x, c)
  | [] => rfl
  | x :: xs => by simp [List.replicate_succ, zip_map_replicate g c xs]

/-- The six components of the image of a store. -/
theorem store_toCore_parts {s : Store H} {S : ToCore.CStore H}
    (hS : Store.toCore s = some (ToCore.Store.erase S)) :
    S.globals = s.globals.map GlobalInst.toCore ∧ S.mems = s.mems.map MemInst.toCore ∧
      S.tables = s.tables.map TableInst.toCore ∧ S.datas = s.datas.map DataInst.toCore ∧
      S.elems = s.elems.map ElemInst.toCore ∧
      s.funcs.mapM FuncInst.toCore =
        some (S.funcs.map fun fi => { fi with module := ToCore.ModuleInst.erase fi.module }) := by
  simp only [Store.toCore, Option.map_eq_some_iff] at hS
  obtain ⟨fs, hfs, hSe⟩ := hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg (fun (t : ToCore.CStore H) => t.globals) hSe
    simpa [ToCore.Store.erase] using this.symm
  · have := congrArg (fun (t : ToCore.CStore H) => t.mems) hSe
    simpa [ToCore.Store.erase] using this.symm
  · have := congrArg (fun (t : ToCore.CStore H) => t.tables) hSe
    simpa [ToCore.Store.erase] using this.symm
  · have := congrArg (fun (t : ToCore.CStore H) => t.datas) hSe
    simpa [ToCore.Store.erase] using this.symm
  · have := congrArg (fun (t : ToCore.CStore H) => t.elems) hSe
    simpa [ToCore.Store.erase] using this.symm
  · have := congrArg (fun (t : ToCore.CStore H) => t.funcs) hSe
    rw [hfs]
    simpa [ToCore.Store.erase] using congrArg some this

/-! ### Componentwise agreement of the two allocations -/

/-- The type of a function is unchanged by the embedding. -/
theorem func_toCore_type {f : Func} {cf : Wasm.Func} (hf : Func.toCore f = some cf) :
    cf.type = f.type := by
  simp only [Func.toCore, Option.map_eq_some_iff] at hf
  obtain ⟨b, -, rfl⟩ := hf
  rfl

/-- The bytes of a data segment are unchanged by the embedding. -/
theorem data_toCore_bytes {d : Data} {cd : Wasm.Data} (hd : Data.toCore d = some cd) :
    cd.bytes = d.bytes := by
  simp only [Data.toCore, Option.map_eq_some_iff] at hd
  obtain ⟨md, -, rfl⟩ := hd
  rfl

/-- The reference type and the initialisers of an element segment, under the
embedding. -/
theorem elem_toCore_parts {e : Elem} {ce : Wasm.Elem} (he : Elem.toCore e = some ce) :
    ce.type = e.type.toCore ∧ e.init.mapM Expr.toCore = some ce.init := by
  simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
  obtain ⟨is, his, md, -, rfl⟩ := he
  exact ⟨rfl, his⟩

/-- `$allocmodule`'s `$allocfunc` needs the function types out of
`$alloctypes(type*)`; they are the images of the 2.0 ones. -/
theorem funcTypes_toCore {ts : List FuncType} {fs : List Func} {cfs : List Wasm.Func}
    (hfs : List.Forall₂ (fun f cf => Func.toCore f = some cf) fs cfs) :
    ∀ {fts : List FuncType}, fs.mapM (fun fn => ts[fn.type.toNat]?) = some fts →
      cfs.mapM (fun fn => (ts.map FuncType.toDefType)[fn.type.toNat]?) =
        some (fts.map FuncType.toDefType) := by
  induction hfs with
  | nil =>
    intro fts hft
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hft
    subst hft
    rfl
  | @cons f cf fs cfs hf _ ih =>
    intro fts hft
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hft
    obtain ⟨ft, hft1, fts', hfts, rfl⟩ := hft
    have hhead : (ts.map FuncType.toDefType)[cf.type.toNat]? = some ft.toDefType := by
      rw [List.getElem?_map, func_toCore_type hf, hft1]
      rfl
    simp only [List.mapM_cons, hhead, ih hfts, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, List.map_cons]

/-- `$instexport` (`9-module:100-104`) is Core 3.0's `$allocexport` on the image. -/
theorem instExport_toCore (mi₀ : ModuleInst) (miE : ToCore.CModuleInst)
    (hf : miE.funcs = mi₀.funcs) (hgl : miE.globals = mi₀.globals)
    (ht : miE.tables = mi₀.tables) (hm : miE.mems = mi₀.mems) (e : Export) :
    Silmaril.Wasm.Execution.Core.allocExport? miE e.toCore =
      (instExport? mi₀.funcs mi₀.globals mi₀.tables mi₀.mems e).map ExportInst.toCore := by
  rcases e with ⟨nm, idx⟩
  cases idx <;>
    simp [Silmaril.Wasm.Execution.Core.allocExport?, instExport?, Export.toCore,
      ExternIdx.toCore, hf, hgl, ht, hm, ExportInst.toCore, ExternAddr.toCore,
      Option.map_map, Function.comp_def]

/-- The export section of `$allocmodule`, on the image. -/
theorem allocExports_toCore (mi₀ : ModuleInst) (miE : ToCore.CModuleInst)
    (hf : miE.funcs = mi₀.funcs) (hgl : miE.globals = mi₀.globals)
    (ht : miE.tables = mi₀.tables) (hm : miE.mems = mi₀.mems)
    (exs : List Export) (xi : List ExportInst)
    (hxi : exs.mapM (instExport? mi₀.funcs mi₀.globals mi₀.tables mi₀.mems) = some xi) :
    (exs.map Export.toCore).mapM (Silmaril.Wasm.Execution.Core.allocExport? miE) =
      some (xi.map ExportInst.toCore) :=
  mapM_map_option (instExport_toCore mi₀ miE hf hgl ht hm) hxi

/-- `$allocmodule` returns the export instances it was asked for. -/
theorem allocModule?_tc_exports {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas vs rss = some (s', mi)) :
    m.exports.mapM (instExport? mi.funcs mi.globals mi.tables mi.mems) = some mi.exports := by
  simp only [allocModule?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.guard_eq_some', Option.some.injEq, Prod.mk.injEq, exists_const] at h
  obtain ⟨fts, -, -, -, xi, hxi, -, hmi⟩ := h
  subst hmi
  exact hxi

/-- Fresh 2.0 memories and fresh Core 3.0 memories agree. -/
theorem mems_new_toCore (ms : List MemoryType) :
    (ms.map fun t => (⟨t, ⟨Array.replicate (t.limits.min.val *
        Silmaril.Wasm.Execution.Memory.pageSize) 0⟩⟩ : MemInst)).map MemInst.toCore =
      (ms.map MemoryType.toCore).map fun mt =>
        (⟨mt, ByteArray.mk (Array.replicate (mt.limits.min.val *
          Silmaril.Wasm.Execution.Memory.pageSize) 0)⟩ :
          Silmaril.Wasm.Execution.Core.MemInst) := by
  simp [List.map_map, Function.comp_def, MemInst.toCore, MemoryType.toCore, Limits.toCore,
    widen32]

/-- Fresh 2.0 tables and fresh Core 3.0 tables agree: `$alloctable` fills a 2.0
table with `(REF.NULL rt)^i` (`9-module:58`), and `TableType.toCoreTable` gives
the Core table the initialiser `[REF.NULL rt]`. -/
theorem tables_new_toCore (dts : List Silmaril.Wasm.Validation.DefType) (ts : List TableType) :
    (ts.map fun t =>
        (⟨t, List.replicate t.limits.min.val (.null t.element)⟩ : TableInst)).map
      TableInst.toCore =
      (((ts.map TableType.toCoreTable).map fun t =>
          (⟨t.type.address, t.type.limits,
            (Silmaril.Wasm.Validation.liftRef t.type.element).substAll
              (dts.map Silmaril.Wasm.Validation.Ty.dt)⟩ :
            Silmaril.Wasm.Validation.CTableType)).zip
        (List.replicate ts.length Silmaril.Wasm.Execution.Core.Ref.null)).map fun p =>
        (⟨p.1, List.replicate p.1.limits.min.val p.2⟩ :
          Silmaril.Wasm.Execution.Core.TableInst) := by
  rw [List.map_map, List.map_map, zip_map_replicate, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  have hclosed : (Silmaril.Wasm.Validation.liftRef (TableType.toCoreTable t).type.element).substAll
      (dts.map Silmaril.Wasm.Validation.Ty.dt) = t.element.toC := by
    rw [show (TableType.toCoreTable t).type.element = t.element.toCore from rfl]
    exact Silmaril.Wasm.Validation.Ty.substAll_closed (by cases t.element <;> rfl) _
  simp only [Function.comp_apply, TableInst.toCore, ToCore.tableToC, hclosed,
    List.map_replicate, Ref.toCore]
  rfl

/-- Fresh 2.0 element instances and fresh Core 3.0 element instances agree. -/
theorem elems_new_toCore {es : List Elem} {ces : List Wasm.Elem}
    (hes : List.Forall₂ (fun e ce => Elem.toCore e = some ce) es ces)
    (dts : List Silmaril.Wasm.Validation.DefType) (rss : List (List Ref)) :
    (((es.map Elem.type).zip rss).map fun p => (⟨p.1, p.2⟩ : ElemInst)).map ElemInst.toCore =
      (((ces.map fun e => (Silmaril.Wasm.Validation.liftRef e.type).substAll
            (dts.map Silmaril.Wasm.Validation.Ty.dt)).zip
          (rss.map (List.map Ref.toCore))).map fun p =>
        (⟨p.1, p.2⟩ : Silmaril.Wasm.Execution.Core.ElemInst)) := by
  induction hes generalizing rss with
  | nil => simp
  | @cons e ce es ces he _ ih =>
    cases rss with
    | nil => simp
    | cons rs rss =>
      have hty : (Silmaril.Wasm.Validation.liftRef ce.type).substAll
          (dts.map Silmaril.Wasm.Validation.Ty.dt) = e.type.toC := by
        rw [(elem_toCore_parts he).1]
        exact Silmaril.Wasm.Validation.Ty.substAll_closed (by cases e.type <;> rfl) _
      simp only [List.map_cons, List.zip_cons_cons, ih rss, hty, ElemInst.toCore]

/-- A `List.Forall₂` whose two sides map to a common codomain. -/
theorem forall₂_mapEq_toCore {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → g b = f a) : ∀ {l : List α} {l' : List β},
      List.Forall₂ R l l' → l'.map g = l.map f
  | _, _, .nil => rfl
  | _, _, .cons hab hrest => by simp [hfg _ _ hab, forall₂_mapEq_toCore hfg hrest]

/-- Fresh 2.0 function instances and fresh Core 3.0 function instances agree
after erasure. -/
theorem funcs_new_toCore (mi : ModuleInst) {fs : List Func} {cfs : List Wasm.Func}
    (hfs : List.Forall₂ (fun f cf => Func.toCore f = some cf) fs cfs) :
    ∀ fts : List FuncType,
      ((fts.zip fs).map fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst H)).mapM FuncInst.toCore =
        some (((fts.map FuncType.toDefType).zip cfs).map fun p =>
          (⟨p.1, mi.toCore, Silmaril.Wasm.Execution.Core.FuncCode.wasm p.2⟩ :
            ToCore.CFuncInst H)) := by
  induction hfs with
  | nil => intro fts; simp
  | @cons f cf fs cfs hf _ ih =>
    intro fts
    cases fts with
    | nil => simp
    | cons ft fts =>
      simp only [List.zip_cons_cons, List.map_cons, List.mapM_cons, ih fts, FuncInst.toCore, hf,
        Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- **Milestone.** The two allocations agree after erasure: `$allocmodule`
(`9-module:107-147`) composed with the runtime embedding is Core 3.0's
`$allocmodule` on the image of its arguments.

The Core 3.0 initialiser lists are determined: the globals are `[]` (the
`noGlobals` side condition, `hg`), the table initialisers are all
`REF.NULL_ADDR` — 2.0's `$alloctable` fills a fresh table with `(REF.NULL rt)^i`
(`9-module:58`) and `V2.TableType.toCoreTable` therefore gives every Core table
the initialiser `[REF.NULL rt]` — and the element initialisers are the pointwise
images of the 2.0 ones.

**Statement change.** `hwf`, `hmemok` and `hximp` are new, and all three are
forced by the conclusion `StoreWF s'`; see the module docstring. They are the
weakest form of what the call site has: `hwf` is
`InstantiationBounds.storeWF`, `hmemok` is `Memtype_ok` (`6-typing:42`) for the
defined memories, and `hximp` is "the imported function addresses are
allocated", which import matching supplies (`externAddrOk_kinds`). -/
theorem allocModule_core {s s' : Store H} {S : ToCore.CStore H} {m : Module} {cm : Wasm.Module}
    {xas : List ExternAddr} {rss : List (List Ref)} {mi : ModuleInst}
    (hg : m.globals = []) (hwf : StoreWF s)
    (hmemok : ∀ mt ∈ m.memories, mt.limits.min.val ≤ 2 ^ 16)
    (hximp : ∀ a ∈ ExternAddr.funcs xas, a < s.funcs.length)
    (hS : Store.toCore s = some (ToCore.Store.erase S))
    (hcm : Module.toCore m = some cm) (h : allocModule? s m xas [] rss = some (s', mi)) :
    ∃ (Sa : ToCore.CStore H) (miC : ToCore.CModuleInst),
      Silmaril.Wasm.Execution.Core.allocModule? S cm (xas.map ExternAddr.toCore) []
          (List.replicate m.tables.length Silmaril.Wasm.Execution.Core.Ref.null)
          (rss.map (List.map Ref.toCore)) = some (Sa, miC) ∧
      ToCore.ModuleInstSim mi miC ∧
      Store.toCore s' = some (ToCore.Store.erase Sa) ∧
      StoreWF s' := by
  obtain ⟨hSg, hSm, hSt, hSd, hSe, hSf⟩ := store_toCore_parts hS
  have hSfl : S.funcs.length = s.funcs.length := store_toCore_funcs_length hS
  have hSml : S.mems.length = s.mems.length := by rw [hSm, List.length_map]
  have hStl : S.tables.length = s.tables.length := by rw [hSt, List.length_map]
  have hSdl : S.datas.length = s.datas.length := by rw [hSd, List.length_map]
  have hSel : S.elems.length = s.elems.length := by rw [hSe, List.length_map]
  simp only [Module.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hcm
  obtain ⟨gs, hgs, cfs, hcfs, ces, hces, cds, hcds, rfl⟩ := hcm
  rw [hg] at hgs
  simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hgs
  subst hgs
  obtain ⟨fts, hfts, -, hrlen, hfuncs', hglobals', htables', hmems', helems', hdatas'⟩ :=
    allocModule?_tc_store h
  obtain ⟨hmiT, hmiF, hmiG, hmiTa, hmiM, hmiE, hmiD⟩ := allocModule?_moduleInst h
  rw [hg] at hmiG hglobals'
  simp only [List.length_nil, List.range_zero, List.map_nil, List.append_nil,
    List.zip_nil_left] at hmiG hglobals'
  have hftslen : fts.length = m.funcs.length := mapM_length hfts
  have hcfslen : cfs.length = m.funcs.length := mapM_length hcfs
  have hceslen : ces.length = m.elems.length := mapM_length hces
  have hcdslen : cds.length = m.data.length := mapM_length hcds
  have hrsslen : (rss.map (List.map Ref.toCore)).length = m.elems.length := by
    rw [List.length_map, hrlen]
  have hfuncTypes := funcTypes_toCore (ts := m.types)
    (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hcfs) hfts
  simp only [Silmaril.Wasm.Execution.Core.allocModule?, allocTypes_toCore, hfuncTypes,
    List.mapM_nil, List.map_nil, List.zip_nil_right, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, coreAllocMany_nil, coreAllocMems_closed,
    coreAllocTables_closed, coreAllocDatas_closed, coreAllocElems_closed,
    coreAllocFuncs_closed, externAddr_tags_toCore, externAddr_funcs_toCore,
    externAddr_globals_toCore, externAddr_tables_toCore, externAddr_mems_toCore,
    List.append_nil, List.nil_append, List.length_map, List.length_zip, List.length_replicate,
    Nat.min_self, hcfslen, hcdslen, hceslen, hrsslen, hSfl, hSml, hStl, hSdl, hSel]
  rw [← hmiF, ← hmiG, ← hmiTa, ← hmiM, ← hmiD, ← hmiE]
  rw [allocExports_toCore mi
    { globals := mi.globals, mems := mi.mems, tables := mi.tables, funcs := mi.funcs }
    rfl rfl rfl rfl m.exports mi.exports (allocModule?_tc_exports h)]
  simp only [Option.bind_some]
  have hsimEq : ToCore.ModuleInst.erase
      { types := m.types.map FuncType.toDefType, globals := mi.globals, mems := mi.mems,
        tables := mi.tables, funcs := mi.funcs, datas := mi.datas, elems := mi.elems,
        exports := mi.exports.map ExportInst.toCore } = mi.toCore := by
    simp [ToCore.ModuleInst.erase, ModuleInst.toCore, hmiT]
  refine ⟨_, _, rfl, hsimEq, ?_, allocModule_storeWF hwf hmemok hximp h⟩
  have hnew := funcs_new_toCore (H := H) mi
    (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hcfs) fts
  have hbytes : cds.map Wasm.Data.bytes = m.data.map Data.bytes :=
    forall₂_mapEq_toCore (fun _ _ hab => data_toCore_bytes hab)
      (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hcds)
  rw [Store.toCore, hfuncs', mapM_append_option hSf hnew]
  simp only [Option.map_some, Option.some.injEq, ToCore.Store.erase, hglobals', htables',
    hmems', helems', hdatas', List.map_append, hSg, hSm, hSt, hSd, hSe, hbytes,
    mems_new_toCore]
  simp only [List.map_map, Function.comp_def, DataInst.toCore,
    Silmaril.Wasm.Execution.Core.Store.mk.injEq, true_and, and_true, List.append_cancel_left_eq,
    List.map_inj_left]
  refine ⟨?_, ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using
      tables_new_toCore (m.types.map FuncType.toDefType) m.tables
  · exact fun _ _ => by rw [hsimEq]
  · simpa [List.map_map, Function.comp_def] using
      elems_new_toCore (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hces)
        (m.types.map FuncType.toDefType) rss

/-! ## Values are normal forms, and constant expressions are deterministic

`Silmaril.Wasm.V2.Execution.Step.not_vals` already says that a configuration
whose code is `val*` does not step. These lemmas turn that into the determinism
`instantiate_sim` needs: a 2.0 constant expression (`Instr_const`,
`6-typing:543-557`) is a single instruction with at most one reduct, so the
`Eval_expr` premises of `$instantiate` (`9-module:184-185`) pin down the values
and references the module is allocated with. -/

/-- A reduction sequence out of `val*` is the empty one. -/
theorem steps_vals_eq {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {vs : List Val} {c : Config H} (h : Steps P host ⟨s, f, vals vs⟩ c) :
    c = ⟨s, f, vals vs⟩ := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) Step.not_vals

/-- `vals` is injective. -/
theorem vals_inj : {vs ws : List Val} → vals vs = vals ws → vs = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [vals] at h
  | _ :: _, [], h => by simp [vals] at h
  | v :: vs, w :: ws, h => by
    simp only [vals, List.map_cons, List.cons.injEq] at h
    have hvw : v = w := by have := congrArg Admin.val? h.1; simpa using this
    rw [hvw, vals_inj (vs := vs) (ws := ws) (by simpa [vals] using h.2)]

/-- A code sequence that is not `val*` and has a unique reduct reaches `val*`
only through that reduct. -/
theorem steps_vals_of_unique {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {code : List Admin} {v : Val} {ws : List Val}
    (hcode : code.all Admin.isVal = false)
    (hinv : ∀ c : Config H, Step P host ⟨s, f, code⟩ c → c = ⟨s, f, vals [v]⟩)
    (h : Steps P host ⟨s, f, code⟩ ⟨s', f', vals ws⟩) : s' = s ∧ f' = f ∧ ws = [v] := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hstep, hrest⟩
  · exfalso
    have hcc : code = vals ws := congrArg Config.code heq
    rw [hcc, all_isVal_vals] at hcode
    exact Bool.noConfusion hcode
  · have hc := hinv c hstep
    subst hc
    have h₂ := steps_vals_eq hrest
    exact ⟨congrArg Config.store h₂, congrArg Config.frame h₂,
      vals_inj (congrArg Config.code h₂)⟩

/-- A one-element code sequence that starts with `val*` and continues with a
non-empty list: the `val*` is empty and the list is the singleton. -/
theorem vals_append_cons_eq_singleton {vs : List Val} {b a : Admin} {l : List Admin} :
    vals vs ++ b :: l = [a] ↔ (vs = [] ∧ b = a ∧ l = []) := by
  constructor
  · intro h
    cases vs with
    | nil => simpa [vals] using h
    | cons v vs => simp [vals] at h
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The evaluation-context decomposition of a one-element code sequence whose
single instruction is not a value: the hole is empty. -/
theorem vals_append_append_eq_singleton {vs : List Val} {is rest : List Admin} {a : Admin}
    (h : vals vs ++ is ++ rest = [a]) (ha : a.isVal = false) (hne : vs ≠ [] ∨ rest ≠ []) :
    is = [] := by
  cases vs with
  | cons v vs =>
    exfalso
    simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at h
    rw [← h.1] at ha
    simp at ha
  | nil =>
    simp only [vals, List.map_nil, List.nil_append] at h
    rcases hne with hne | hne
    · exact absurd rfl hne
    · cases is with
      | nil => rfl
      | cons y ys =>
        exfalso
        simp only [List.cons_append, List.cons.injEq] at h
        exact hne (List.append_eq_nil_iff.mp h.2).2

/-- No `Step_pure` rule applies to a single plain `REF.FUNC`/`GLOBAL.GET`:
every `Step_pure` left-hand side of length one is a `LABEL_`, a `FRAME_`, or
one of `UNREACHABLE`, `NOP`. -/
theorem pureStep_ne_singleton {P : Profile} {is is' : List Admin} {i : Instr}
    (h : PureStep P is is') (hi : is = [.plain i])
    (h₂ : i ≠ .unreachable) (h₃ : i ≠ .nop) : False := by
  cases h <;> simp_all [vals_append_cons_eq_singleton]

/-- `REF.FUNC x` has exactly one `Step_read` reduct (`8-reduction:212`). -/
theorem readStep_refFunc_inv {s : Store H} {f : Frame} {is is' : List Admin} {x : FuncIdx}
    (h : ReadStep s f is is') (hi : is = [.plain (.refFunc x)]) :
    ∃ a : FuncAddr, f.module.funcAddr? x = some a ∧ is' = [Admin.refFuncAddr a] := by
  cases h <;> simp_all [vals_append_cons_eq_singleton]

/-- `GLOBAL.GET x` has exactly one `Step_read` reduct (`8-reduction:389`). -/
theorem readStep_globalGet_inv {s : Store H} {f : Frame} {is is' : List Admin} {x : GlobalIdx}
    (h : ReadStep s f is is') (hi : is = [.plain (.globalGet x)]) :
    ∃ gi : GlobalInst, (⟨s, f⟩ : State H).global? x = some gi ∧ is' = [gi.value.toAdmin] := by
  cases h <;> simp_all [vals_append_cons_eq_singleton]

/-- The only `Step` out of a single plain instruction that is neither a value
nor one of the two state-writing `DROP`s is a `Step_pure` or a `Step_read`. -/
theorem step_singleton_plain_inv {P : Profile} {host : HostSemantics H} {s : Store H}
    {f : Frame} {code : List Admin} {i : Instr} {c : Config H}
    (h : Step P host ⟨s, f, code⟩ c) (hc : code = [.plain i])
    (hv : (Admin.plain i).isVal = false)
    (he : ∀ x, Instr.elemDrop x ≠ i) (hd : ∀ x, Instr.dataDrop x ≠ i) :
    (∃ is', PureStep P [.plain i] is' ∧ c = ⟨s, f, is'⟩) ∨
      (∃ is', ReadStep s f [.plain i] is' ∧ c = ⟨s, f, is'⟩) := by
  cases h with
  | pure hp => subst hc; exact .inl ⟨_, hp, rfl⟩
  | read hr => subst hc; exact .inr ⟨_, hr, rfl⟩
  | ctxtInstrs hs hne =>
    exfalso
    have hnil := vals_append_append_eq_singleton hc hv hne
    subst hnil
    have := hs.not_allVals
    simp at this
  | _ => simp_all [vals_append_cons_eq_singleton]

/-- `REF.FUNC x` has exactly one reduct. -/
theorem step_refFunc_inv_tc {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {x : FuncIdx} {a : FuncAddr} {c : Config H} (hx : f.module.funcAddr? x = some a)
    (h : Step P host ⟨s, f, [.plain (.refFunc x)]⟩ c) :
    c = ⟨s, f, vals [Val.ref (.funcAddr a)]⟩ := by
  rcases step_singleton_plain_inv h rfl (by simp [Admin.isVal, Admin.val?])
      (by simp) (by simp) with ⟨is', hp, rfl⟩ | ⟨is', hr, rfl⟩
  · exact absurd (pureStep_ne_singleton hp rfl (by simp) (by simp)) not_false
  · obtain ⟨a', ha', rfl⟩ := readStep_refFunc_inv hr rfl
    rw [hx] at ha'
    cases ha'
    rfl

/-- `GLOBAL.GET x` has exactly one reduct. -/
theorem step_globalGet_inv_tc {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {x : GlobalIdx} {gi : GlobalInst} {c : Config H}
    (hx : (⟨s, f⟩ : State H).global? x = some gi)
    (h : Step P host ⟨s, f, [.plain (.globalGet x)]⟩ c) :
    c = ⟨s, f, vals [gi.value]⟩ := by
  rcases step_singleton_plain_inv h rfl (by simp [Admin.isVal, Admin.val?])
      (by simp) (by simp) with ⟨is', hp, rfl⟩ | ⟨is', hr, rfl⟩
  · exact absurd (pureStep_ne_singleton hp rfl (by simp) (by simp)) not_false
  · obtain ⟨gi', hgi', rfl⟩ := readStep_globalGet_inv hr rfl
    rw [hx] at hgi'
    cases hgi'
    rfl

/-- **The denotation of a 2.0 constant expression is the only value it reaches.**
`Instr_const` (`6-typing:543-557`) has five forms; three are already values and
the other two take exactly one `Step_read`. -/
theorem evalExpr_const_eq {P : Profile} {host : HostSemantics H} {s s' : Store H}
    {f f' : Frame} {e : Expr} {v : Val} {ws : List Val}
    (hv : constExpr? s f.module e = some v) (h : EvalExpr P host s f e s' f' ws) :
    s' = s ∧ f' = f ∧ ws = [v] := by
  match e with
  | [] => simp [constExpr?] at hv
  | _ :: _ :: _ => simp [constExpr?] at hv
  | [i] =>
    simp only [constExpr?] at hv
    have hstep : ∀ w : Val, (Admin.plain i) = w.toAdmin →
        Steps P host ⟨s, f, vals [w]⟩ ⟨s', f', vals ws⟩ := by
      intro w hw
      show Steps P host ⟨s, f, [w.toAdmin]⟩ _
      rw [← hw]
      exact h
    have hval : ∀ w : Val, (Admin.plain i) = w.toAdmin → v = w →
        s' = s ∧ f' = f ∧ ws = [v] := by
      intro w hw hvw
      have h₂ := steps_vals_eq (hstep w hw)
      refine ⟨congrArg Config.store h₂, congrArg Config.frame h₂, ?_⟩
      rw [hvw]
      exact vals_inj (congrArg Config.code h₂)
    have hplain : Steps P host ⟨s, f, [Admin.plain i]⟩ ⟨s', f', vals ws⟩ := h
    cases i with
    | intConst t c =>
      simp only [constInstr?, Option.some.injEq] at hv
      exact hval (Val.num ⟨.int t, c⟩) rfl hv.symm
    | floatConst t c =>
      simp only [constInstr?, Option.some.injEq] at hv
      exact hval (Val.num ⟨.float t, c⟩) rfl hv.symm
    | vecConst c =>
      simp only [constInstr?, Option.some.injEq] at hv
      exact hval (Val.vec c) rfl hv.symm
    | refNull rt =>
      simp only [constInstr?, Option.some.injEq] at hv
      exact hval (Val.ref (.null rt)) rfl hv.symm
    | refFunc x =>
      simp only [constInstr?, Option.map_eq_some_iff] at hv
      obtain ⟨a, ha, rfl⟩ := hv
      exact steps_vals_of_unique (by simp [Admin.isVal, Admin.val?])
        (fun _ hs => step_refFunc_inv_tc ha hs) hplain
    | globalGet x =>
      simp only [constInstr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
      obtain ⟨a, ha, gi, hgi, rfl⟩ := hv
      refine steps_vals_of_unique (by simp [Admin.isVal, Admin.val?])
        (fun _ hs => step_globalGet_inv_tc ?_ hs) hplain
      simp [State.global?, ha, hgi]
    | _ => simp [constInstr?] at hv

/-! ## Constant expressions on the Core side

The 2.0 analogue of `Lime1.Execution.constFold_core`: the image of a constant
expression evaluates, in Core 3.0, to the image of the value it denotes, in the
*same* state. None of the five forms of `Instr_const` reads a function
*instance* out of the store — Core 3.0's `Step_read/ref.func` reads
`f.MODULE.FUNCS[x]` — so the predicted, as yet unallocated, function addresses
of `moduleinst_init` (`9-module:179`) are harmless. -/

/-- The image of a 2.0 constant instruction evaluates to the image of its
denotation. -/
theorem constInstr_core {P : Profile} {tgt : ToCore.CHostSemantics H} {s : Store H}
    {S : ToCore.CStore H} {F : ToCore.CFrame} {mi : ModuleInst}
    (hg : S.globals = s.globals.map GlobalInst.toCore)
    (hF : ToCore.ModuleInstSim mi F.module)
    {i : Instr} {ci : Wasm.Instr} (hi : Instr.toCore i = some ci)
    {v : Val} (hv : constInstr? s mi i = some v) :
    Silmaril.Wasm.Execution.Core.EvalExpr P tgt S F [ci] S F [v.toCore] := by
  have hfuncs : F.module.funcs = mi.funcs := by
    have := congrArg (fun m : ToCore.CModuleInst => m.funcs) hF
    simpa [ToCore.ModuleInst.erase, ModuleInst.toCore] using this
  have hglob : F.module.globals = mi.globals := by
    have := congrArg (fun m : ToCore.CModuleInst => m.globals) hF
    simpa [ToCore.ModuleInst.erase, ModuleInst.toCore] using this
  cases i with
  | intConst t c =>
    simp only [constInstr?, Option.some.injEq] at hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hv; subst hi
    exact Relation.ReflTransGen.refl
  | floatConst t c =>
    simp only [constInstr?, Option.some.injEq] at hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hv; subst hi
    exact Relation.ReflTransGen.refl
  | vecConst c =>
    simp only [constInstr?, Option.some.injEq] at hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hv; subst hi
    exact Relation.ReflTransGen.refl
  | refNull rt =>
    simp only [constInstr?, Option.some.injEq] at hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hv; subst hi
    exact Relation.ReflTransGen.single
      (Silmaril.Wasm.Execution.Core.Step.reference
        (Silmaril.Wasm.Execution.Core.RefStep.refNull _))
  | refFunc x =>
    simp only [constInstr?, Option.map_eq_some_iff] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hi
    refine Relation.ReflTransGen.single
      (Silmaril.Wasm.Execution.Core.Step.reference
        (Silmaril.Wasm.Execution.Core.RefStep.refFunc ?_))
    rw [hfuncs]
    exact ha
  | globalGet x =>
    simp only [constInstr?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
    obtain ⟨a, ha, gi, hgi, rfl⟩ := hv
    simp only [Instr.toCore, Option.some.injEq] at hi
    subst hi
    refine Relation.ReflTransGen.single
      (Silmaril.Wasm.Execution.Core.Step.variable
        (Silmaril.Wasm.Execution.Core.VariableStep.globalGet
          (a := a) (g := gi.toCore) ?_))
    simp only [Silmaril.Wasm.Execution.Core.Store.global?, hglob, hg]
    rw [ModuleInst.globalAddr?] at ha
    rw [Store.globalInst?] at hgi
    simp [ha, List.getElem?_map, hgi]
  | _ => simp [constInstr?] at hv

/-- The image of a 2.0 constant *expression* evaluates to the image of its
denotation. -/
theorem constExpr_core {P : Profile} {tgt : ToCore.CHostSemantics H} {s : Store H}
    {S : ToCore.CStore H} {F : ToCore.CFrame} {mi : ModuleInst}
    (hg : S.globals = s.globals.map GlobalInst.toCore)
    (hF : ToCore.ModuleInstSim mi F.module)
    {e : Expr} {ce : Wasm.Expr} (hce : Expr.toCore e = some ce)
    {v : Val} (hv : constExpr? s mi e = some v) :
    Silmaril.Wasm.Execution.Core.EvalExpr P tgt S F ce S F [v.toCore] := by
  match e with
  | [] => simp [constExpr?] at hv
  | _ :: _ :: _ => simp [constExpr?] at hv
  | [i] =>
    simp only [Expr.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hce
    obtain ⟨c, hc, cs, hcs, rfl⟩ := hce
    simp only [Option.some.injEq] at hcs
    subst hcs
    exact constInstr_core hg hF hc hv

/-! ## Initialiser evaluation on the Core side -/

/-- Core 3.0's `$evalexprs` on the table initialisers of the image of a 2.0
module: every 2.0 table is implicitly initialised with nulls
(`V2.TableType.toCoreTable`), so each Core initialiser is `[REF.NULL ht]` and
takes exactly one `Step_read/ref.null` to produce `REF.NULL_ADDR`, leaving the
state alone. -/
theorem evalExprs_tables {P : Profile} {tgt : ToCore.CHostSemantics H} {m : Module}
    {cm : Wasm.Module} (hcm : Module.toCore m = some cm) (S : ToCore.CStore H)
    (F : ToCore.CFrame) :
    Silmaril.Wasm.Execution.Core.EvalExprs P tgt S F
      (cm.tables.map Silmaril.Wasm.Table.init) S F
      (List.replicate m.tables.length Silmaril.Wasm.Execution.Core.Ref.null) := by
  obtain ⟨-, -, -, -, htables, -, -, -, -⟩ := module_toCore_shape hcm
  rw [htables, List.map_map]
  induction m.tables with
  | nil => exact .nil
  | cons t ts ih =>
    refine .cons ?_ ih
    show Silmaril.Wasm.Execution.Core.Steps P tgt _ _
    refine Relation.ReflTransGen.single ?_
    exact Silmaril.Wasm.Execution.Core.Step.reference
      (Silmaril.Wasm.Execution.Core.RefStep.refNull _)

/-- `$evalexprs` on the images of a list of 2.0 constant expressions. -/
theorem evalExprs_core {P : Profile} {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    {s : Store H} {S : ToCore.CStore H} {F : ToCore.CFrame} {f : Frame}
    (hg : S.globals = s.globals.map GlobalInst.toCore)
    (hF : ToCore.ModuleInstSim f.module F.module) {exs : List Expr} :
    ∀ {cexs : List Wasm.Expr} {rs : List Ref}, exs.mapM Expr.toCore = some cexs →
      (∀ ex ∈ exs, (constExpr? s f.module ex).isSome) →
      List.Forall₂ (fun (ex : Expr) (r : Ref) =>
        EvalExpr P src s f ex s f [Val.ref r]) exs rs →
      Silmaril.Wasm.Execution.Core.EvalExprs P tgt S F cexs S F (rs.map Ref.toCore) := by
  induction exs with
  | nil =>
    intro cexs rs hc _ hrs
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hc
    subst hc
    cases hrs
    exact .nil
  | cons ex exs ih =>
    intro cexs rs hc hconst hrs
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hc
    obtain ⟨cex, hcex, cexs', hcexs, rfl⟩ := hc
    cases hrs with
    | cons hr hrs =>
      refine .cons ?_ (ih hcexs (fun e' he' => hconst e' (by simp [he'])) hrs)
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hconst ex (by simp))
      obtain ⟨-, -, hw⟩ := evalExpr_const_eq hv hr
      have hvr : v = Val.ref _ := (List.cons.injEq .. ▸ hw).1.symm
      rw [hvr] at hv
      exact constExpr_core hg hF hcex hv

/-- `$evalexprss` on the images of the element initialisers of a 2.0 module. -/
theorem evalExprss_core {P : Profile} {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    {s : Store H} {S : ToCore.CStore H} {F : ToCore.CFrame} {f : Frame}
    (hg : S.globals = s.globals.map GlobalInst.toCore)
    (hF : ToCore.ModuleInstSim f.module F.module) {es : List Elem} :
    ∀ {ces : List Wasm.Elem} {rss : List (List Ref)}, es.mapM Elem.toCore = some ces →
      (∀ e ∈ es, ∀ ex ∈ e.init, (constExpr? s f.module ex).isSome) →
      List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
        List.Forall₂ (fun (ex : Expr) (r : Ref) =>
          EvalExpr P src s f ex s f [Val.ref r]) e.init rs) es rss →
      Silmaril.Wasm.Execution.Core.EvalExprss P tgt S F (ces.map Silmaril.Wasm.Elem.init) S F
        (rss.map (List.map Ref.toCore)) := by
  induction es with
  | nil =>
    intro ces rss hc _ hrs
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hc
    subst hc
    cases hrs
    exact .nil
  | cons e es ih =>
    intro ces rss hc hconst hrs
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hc
    obtain ⟨ce, hce, ces', hces, rfl⟩ := hc
    cases hrs with
    | cons hr hrs =>
      simp only [List.map_cons]
      refine .cons ?_ (ih hces (fun e' he' => hconst e' (by simp [he'])) hrs)
      simp only [Elem.toCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hce
      obtain ⟨is, his, md, -, rfl⟩ := hce
      exact evalExprs_core hg hF his (hconst e (by simp)) hr

/-- Core 3.0's `$evalexprss` on the element initialisers: every 2.0 initialiser
run `(Eval_expr : z; expr_E ~>* z; ref)` has a Core counterpart, in the **same**
Core state.

**This one cannot go through `Steps.toCore`.** `Steps.toCore` needs `Sim`, `Sim`
contains `ConfigWF`, and `ConfigWF` contains
`ModWF s (Frame.initial s m xas).module` — which is **false** as soon as the
module defines a function. `moduleinst_init` (`9-module:179`) deliberately lists
the *predicted* addresses `|s.FUNCS| + i_F`, none of which is allocated in `s`
yet; that is exactly what lets an element initialiser say `REF.FUNC x` for a
function this module defines. So the proof is the 2.0 analogue of
`Lime1.Execution.constFold_core`: a direct induction over the five forms
`Instr_const` (`6-typing:543-557`) admits — `t.CONST`, `V128.CONST`,
`REF.NULL`, `REF.FUNC` and `GLOBAL.GET` of an imported immutable global — none
of which reads a function instance out of the store (`constExpr_core`).

**Statement change (see the module docstring).** `hconst` is new, and `hosts`,
`bounds` and `hFl` are gone. Without `hconst` the theorem is *false*: `he` alone
does not say that the initialisers are `Instr_const`, and the Core machine
cannot follow an arbitrary 2.0 run under `moduleinst_init`, whose function
addresses are not allocated. `hconst` is exactly what `Elem_ok`
(`6-typing:612`) gives for a valid module, and `elemInit_const_isSome` derives
it from `Instantiate.valid`.

`instantiate_sim` goes through `evalExprss_core` rather than through this
milestone, because Core 3.0's `$instantiate` threads the store on to
`$allocmodule` and so needs the sharper `S' = S` that `evalExprss_core`
states. -/
theorem evalExprss_elems {P : Profile} {src : HostSemantics H}
    {tgt : ToCore.CHostSemantics H}
    {s : Store H} {S : ToCore.CStore H} {F : ToCore.CFrame} {m : Module} {cm : Wasm.Module}
    {xas : List ExternAddr} {rss : List (List Ref)}
    (hS : Store.toCore s = some (ToCore.Store.erase S))
    (hcm : Module.toCore m = some cm)
    (hF : ToCore.ModuleInstSim (ModuleInst.initial s m xas) F.module)
    (hconst : ∀ e ∈ m.elems, ∀ ex ∈ e.init,
      (constExpr? s (ModuleInst.initial s m xas) ex).isSome)
    (he : List.Forall₂ (fun (e : Elem) (rs : List Ref) =>
        List.Forall₂ (fun (ex : Expr) (r : Ref) =>
          EvalExpr P src s (Frame.initial s m xas) ex
            s (Frame.initial s m xas) [Val.ref r]) e.init rs) m.elems rss) :
    ∃ (S' : ToCore.CStore H) (F' : ToCore.CFrame),
      Silmaril.Wasm.Execution.Core.EvalExprss P tgt S F (cm.elems.map Silmaril.Wasm.Elem.init)
        S' F' (rss.map (List.map Ref.toCore)) ∧
      Store.toCore s = some (ToCore.Store.erase S') ∧ F'.module = F.module := by
  refine ⟨S, F, ?_, hS, rfl⟩
  exact evalExprss_core (f := Frame.initial s m xas) (store_toCore_globals hS) hF
    (module_toCore_sections hcm).1 hconst he

/-! ## Side conditions of `$instantiate`, from module validity -/

/-- An external address that matches an external type is allocated. -/
theorem ExternAddrOk.allocated {s : Store H} {xa : ExternAddr} {xt : ExternType}
    (h : ExternAddrOk s xa xt) :
    (∀ a : FuncAddr, xa = .func a → a < s.funcs.length) ∧
      (∀ a : GlobalAddr, xa = .global a → (s.globalInst? a).isSome) := by
  induction h with
  | @func a fi hf =>
    refine ⟨fun b hb => ?_, by simp⟩
    simp only [ExternAddr.func.injEq] at hb
    subst hb
    rw [Store.funcInst?] at hf
    exact (List.getElem?_eq_some_iff.mp hf).1
  | @global a gi hgi =>
    refine ⟨by simp, fun b hb => ?_⟩
    simp only [ExternAddr.global.injEq] at hb
    subst hb
    simp [hgi]
  | table h => exact ⟨by simp, by simp⟩
  | mem h => exact ⟨by simp, by simp⟩
  | sub _ _ _ ih => exact ih

/-- Import matching fixes the shape of the imported index spaces and says that
every imported function and global address is allocated. -/
theorem externAddrOk_kinds {s : Store H} {xas : List ExternAddr} {ixt : List ExternType}
    (h : List.Forall₂ (ExternAddrOk s) xas ixt) :
    (ExternAddr.funcs xas).length = (ExternType.funcs ixt).length ∧
      (ExternAddr.globals xas).length = (ExternType.globals ixt).length ∧
      (∀ a ∈ ExternAddr.funcs xas, a < s.funcs.length) ∧
      (∀ a ∈ ExternAddr.globals xas, (s.globalInst? a).isSome) := by
  induction h with
  | nil =>
    simp [ExternAddr.funcs, ExternAddr.globals, ExternType.funcs, ExternType.globals]
  | @cons xa xt xas ixt hh _ ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    obtain ⟨hfa, hga⟩ := ExternAddrOk.allocated hh
    rcases ExternAddrOk.kind_eq hh with ⟨a, ft, rfl, rfl⟩ | ⟨a, gt, rfl, rfl⟩ |
      ⟨a, tt, rfl, rfl⟩ | ⟨a, mt, rfl, rfl⟩ <;>
      simp_all [ExternAddr.funcs, ExternAddr.globals, ExternType.funcs,
        ExternType.globals] <;>
      exact ⟨h3, h4⟩

/-- A valid module's memories satisfy `Memtype_ok` (`6-typing:42`), hence their
initial size fits the 32-bit address space. -/
theorem ModuleOk.memories_min_le {m : Module} {ixt xt : List ExternType}
    (hok : ModuleOk m ixt xt) : ∀ mt ∈ m.memories, mt.limits.min.val ≤ 2 ^ 16 := by
  obtain ⟨-, -, -, -, hmems, -, -, -, -, -, -, -, -, -⟩ := hok
  intro mt hmt
  obtain ⟨mt', -, hok'⟩ := Silmaril.Wasm.V2.Validation.forall₂_exists_of_mem hmems hmt
  exact hok'.2.1

/-- A valid module's active data segments all name memory `0`
(`Datamode_ok/active`, `6-typing:632`). -/
theorem ModuleOk.data_active_zero {m : Module} {ixt xt : List ExternType}
    (hok : ModuleOk m ixt xt) :
    ∀ d ∈ m.data, ∀ (x : MemIdx) (off : Expr), d.mode = .active x off → x = memIdx0 := by
  obtain ⟨-, -, -, -, -, -, hdatas, -, -, -, -, -, -, -⟩ := hok
  exact fun d hd x off hmode => DataOk.active_zero (hdatas d hd) hmode

/-- **Every element initialiser of a valid module is a constant expression whose
denotation is defined in the initial state** (`Elem_ok`, `6-typing:612`, with
`Expr_ok_const`, `6-typing:564`). This is the side condition `evalExprss_elems`
needs; it is the 2.0 analogue of the `resolveElem?` premises Lime1 carries. -/
theorem elemInit_const_isSome (P : Profile) (host : HostSemantics H) {s : Store H} {m : Module}
    {xas : List ExternAddr} {ixt xt : List ExternType} (hok : ModuleOk m ixt xt)
    (himp : List.Forall₂ (ExternAddrOk s) xas ixt) :
    ∀ e ∈ m.elems, ∀ ex ∈ e.init,
      (constExpr? s (ModuleInst.initial s m xas) ex).isSome := by
  obtain ⟨hlf, hlg, -, hga⟩ := externAddrOk_kinds himp
  obtain ⟨-, -, -, -, -, helems, -, hfuncs, -, -, -, -, -, rfl⟩ := hok
  intro e he ex hex
  obtain ⟨rt, -, hEok⟩ := Silmaril.Wasm.V2.Validation.forall₂_exists_of_mem helems he
  obtain ⟨-, hinit, -⟩ := hEok
  have hden := Silmaril.Wasm.V2.Execution.exprOkConst_evalExpr (P := P) (host := host)
    (f := Frame.initial s m xas) (hinit ex hex)
    (by
      intro x hx
      have hl := List.Forall₂.length_eq hfuncs
      have hlt : x.toNat < (ModuleInst.initial s m xas).funcs.length := by
        simp only [ModuleInst.initial, List.length_append, List.length_map, List.length_range]
        simp only [List.length_append] at hx
        omega
      simp [Frame.initial, ModuleInst.funcAddr?, List.getElem?_eq_getElem hlt])
    (by
      intro x hx
      have hlt : x.toNat < (ExternAddr.globals xas).length := by rw [hlg]; exact hx
      exact ⟨(ExternAddr.globals xas)[x.toNat],
        by simp [Frame.initial, ModuleInst.globalAddr?, ModuleInst.initial,
          List.getElem?_eq_getElem hlt],
        hga _ (List.getElem_mem hlt)⟩)
  obtain ⟨v, hv, -⟩ := hden
  have hv' : constExpr? s (ModuleInst.initial s m xas) ex = some v := hv
  simp [hv']

/-- `$allocmodule` leaves the module instance's function addresses allocated. -/
theorem allocModule_modWF {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {vs : List Val} {rss : List (List Ref)} {mi : ModuleInst}
    (hximp : ∀ a ∈ ExternAddr.funcs xas, a < s.funcs.length)
    (h : allocModule? s m xas vs rss = some (s', mi)) : ModWF s' mi := by
  obtain ⟨fts, hfts, -, -, hfuncs, -, -, -, -, -⟩ := allocModule?_tc_store h
  obtain ⟨-, hmiF, -, -, -, -, -⟩ := allocModule?_moduleInst h
  have hftslen : fts.length = m.funcs.length := mapM_length hfts
  have hlen : s'.funcs.length = s.funcs.length + m.funcs.length := by
    rw [hfuncs]; simp [hftslen]
  intro a ha
  rw [hmiF, List.mem_append] at ha
  rcases ha with ha | ha
  · exact Nat.lt_of_lt_of_le (hximp a ha) (by omega)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hk
    rw [hlen]
    exact Nat.add_lt_add_left hk _

/-- Every element of the codomain of a `List.Forall₂` is related to one of its
domain. -/
theorem forall₂_exists_of_mem_right {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {b : β} (hb : b ∈ l') : ∃ a ∈ l, R a b := by
  induction h with
  | nil => exact absurd hb (by simp)
  | cons hr _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨a, ha, hr'⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr'⟩

/-- Source code is well formed: `Admin.WF` is vacuous on `instr`. -/
theorem listWF_expression (s : Store H) : ∀ es : Expr, Admin.listWF s (expression es)
  | [] => trivial
  | _ :: es => ⟨trivial, listWF_expression s es⟩

/-! ## The two `$instantiate`s -/

/-- **Milestone (the core of this unit).** The configuration Wasm 2.0's
`$instantiate` returns and the configuration Core 3.0's `$instantiate` returns
are related by `Sim`.

Unlike `Lime1`, nothing has to be *run* to get here: both specifications return
the configuration `instr_E* instr_D* (CALL x)?` and leave the segment
initialisation to the machine. The work is in `allocModule_core` (the two
allocations agree) and in `evalExprss_core` (the element initialisers evaluate
to the same references on both sides).

**Statement change.** `hosts` is gone: no host function runs during
instantiation proper. That is a strengthening. -/
theorem instantiate_sim {P : Profile} {src : HostSemantics H}
    {tgt : ToCore.CHostSemantics H}
    {s : Store H} {S : ToCore.CStore H} {m : Module} {cm : Wasm.Module}
    {xas : List ExternAddr} {c : Config H}
    (bounds : InstantiationBounds s m) (hS : Store.toCore s = some S)
    (hcm : Module.toCore m = some cm) (h : Instantiate P src s m xas c) :
    ∃ C : ToCore.CConfig H,
      Silmaril.Wasm.Execution.Core.Instantiate P tgt S cm (xas.map ExternAddr.toCore) C ∧
      Sim c C ∧ C.frame.locals = [] ∧ C.code = coreInstantiateCode cm ∧
      ToCore.ModuleInstSim c.frame.module C.frame.module := by
  have hSe : Store.toCore s = some (ToCore.Store.erase S) := by
    rw [Store.erase_toCore hS]; exact hS
  obtain ⟨hvalid, hbounded, hrun⟩ := h
  obtain ⟨ixt, xt, hok, himp⟩ := hvalid
  obtain ⟨valsG, refsE, s', mi, hgl, hel, halloc, hc⟩ := hrun
  have hvg : valsG = [] := by
    rw [bounds.noGlobals] at hgl
    cases hgl
    rfl
  subst hvg
  subst hc
  obtain ⟨hlenf, hleng, hxfuncs, -⟩ := externAddrOk_kinds himp
  obtain ⟨Sa, miC, hallocC, hsim, hstore', hwf'⟩ :=
    allocModule_core bounds.noGlobals bounds.storeWF (ModuleOk.memories_min_le hok) hxfuncs
      hSe hcm halloc
  -- the image of the sections
  have hcglobals : cm.globals = [] := by
    obtain ⟨-, -, -, -, -, -, -, hgm, -⟩ := module_toCore_shape hcm
    rw [bounds.noGlobals] at hgm
    simpa using hgm.symm
  have helemsM := (module_toCore_sections hcm).1
  have hdatasM := (module_toCore_sections hcm).2
  have hcelen : cm.elems.length = m.elems.length := mapM_length helemsM
  have hcdlen : cm.data.length = m.data.length := mapM_length hdatasM
  -- the Core initialiser runs
  have hFsim := moduleInst_initial_toCore (S := S) hSe hcm xas
  have hEE := evalExprss_core (P := P) (src := src) (tgt := tgt)
    (F := (⟨[], Silmaril.Wasm.Execution.Core.ModuleInst.initial S cm
      (xas.map ExternAddr.toCore)⟩ : ToCore.CFrame))
    (f := Frame.initial s m xas) (store_toCore_globals hSe) hFsim helemsM
    (elemInit_const_isSome P src hok himp) hel
  refine ⟨⟨Sa, { module := miC }, coreInstantiateCode cm⟩,
    ⟨instantiate_valid hSe hcm hok himp, ⟨?_, ?_, ?_, ?_⟩,
      ⟨S, S, S, Sa, _, _, _, [], _, _, miC, ?_, evalExprs_tables hcm S _, hEE, hallocC, rfl⟩⟩,
    ⟨?_, hwf', allocModule_modWF hxfuncs halloc, listWF_expression s' _⟩, rfl, rfl, hsim⟩
  · rw [hcelen]; exact hbounded.1
  · rw [hcdlen]; exact hbounded.2.1
  · intro cd hcd
    obtain ⟨d, hd, hdc⟩ := forall₂_exists_of_mem_right
      (Silmaril.Wasm.V2.Validation.forall₂_of_mapM hdatasM) hcd
    rw [data_toCore_bytes hdc]
    exact hbounded.2.2.1 d hd
  · intro ce hce
    obtain ⟨e, he, hec⟩ := forall₂_exists_of_mem_right
      (Silmaril.Wasm.V2.Validation.forall₂_of_mapM helemsM) hce
    rw [mapM_length (elem_toCore_parts hec).2]
    exact hbounded.2.2.2 e he
  · rw [hcglobals]
    exact .nil
  · -- the two configurations are related
    have hstart : Expr.toCore (startInstrs m) =
        some (match cm.start with | some x => [Wasm.Instr.call x] | none => []) :=
      startInstrs_toCore hcm
    have hbig : Expr.toCore (runElems m ++ runDatas m ++ startInstrs m) =
        some (coreRunElems cm ++ coreRunDatas cm ++
          (match cm.start with | some x => [Wasm.Instr.call x] | none => [])) :=
      expr_toCore_append
        (expr_toCore_append (runElems_toCore hcm)
          (runDatas_toCore hcm (ModuleOk.data_active_zero hok))) hstart
    have hnorm : ToCore.Admin.normList miC (coreInstantiateCode cm) =
        (coreRunElems cm ++ coreRunDatas cm ++
          (match cm.start with | some x => [Wasm.Instr.call x] | none => [])).map
            (ToCore.normPlain miC) := by
      simp only [coreInstantiateCode, Silmaril.Wasm.Execution.Core.expression,
        ToCore.Admin.normList_eq_map, List.map_append, List.map_map, Function.comp_def,
        ToCore.Admin.norm_plain, coreStartCode]
      cases cm.start <;> simp [ToCore.Admin.norm_plain]
    have hpn : (coreRunElems cm ++ coreRunDatas cm ++
        (match cm.start with | some x => [Wasm.Instr.call x] | none => [])).map
          ToCore.plainOrNull =
        ToCore.Admin.normList miC (coreInstantiateCode cm) := by
      rw [hnorm]
      exact List.map_congr_left fun ci hci =>
        (ToCore.normPlain_eq_plainOrNull miC fun x => Expr.toCore_ne_callRef hbig ci hci x).symm
    have hsimEq : ToCore.ModuleInst.erase miC = ModuleInst.toCore mi := hsim
    have hfr : Frame.toCore { module := mi } = ToCore.Frame.erase { module := miC } := by
      simp [Frame.toCore, ToCore.Frame.erase, hsimEq]
    show Config.toCore _ = some (ToCore.Config.norm _)
    simp only [Config.toCore, ToCore.Config.norm, hstore', Option.bind_some]
    show (Admin.listToCore s' (expression (runElems m ++ runDatas m ++ startInstrs m))).map _
      = some _
    rw [expression_toCore, hbig]
    simp only [Option.map_some, Option.some.injEq]
    rw [hfr, hpn]

/-- **Milestone.** Core instantiation followed by the segment programs reaches
the start code.

In 2.0, as in Core 3.0, the segment programs are *part of the configuration*
`$instantiate` returns, so this is `instantiate_sim` followed by `Steps.toCore`:
whenever the 2.0 machine has run the element and data segments and is about to
call the start function, the Core machine has reached a configuration that
simulates it and whose code is exactly the Core start code.

This is the 2.0 analogue of `Lime1.Execution.prepare_core`; the Lime1 version has
to *prove* that the Core segment programs compute Lime1's atomic `prepare?`,
which is the bulk of that file. Here there is nothing to prove about the
segments at all. -/
theorem prepare_core {P : Profile} {src : HostSemantics H}
    {tgt : ToCore.CHostSemantics H} (hosts : HostCompatible src tgt)
    {s s₁ : Store H} {S : ToCore.CStore H} {m : Module} {cm : Wasm.Module}
    {xas : List ExternAddr} {c : Config H}
    (bounds : InstantiationBounds s m) (hS : Store.toCore s = some S)
    (hcm : Module.toCore m = some cm) (h : Instantiate P src s m xas c)
    (hseg : Steps P src c ⟨s₁, c.frame, expression (startInstrs m)⟩) :
    ∃ (C C₁ : ToCore.CConfig H),
      Silmaril.Wasm.Execution.Core.Instantiate P tgt S cm (xas.map ExternAddr.toCore) C ∧
      Silmaril.Wasm.Execution.Core.Steps P tgt C C₁ ∧
      Sim (⟨s₁, c.frame, expression (startInstrs m)⟩ : Config H) C₁ ∧
      C₁.code = coreStartCode cm ∧ C₁.frame = C.frame ∧
      ToCore.ModuleInstSim c.frame.module C.frame.module := by
  obtain ⟨C, hinst, hsim, -, -, hmod⟩ := instantiate_sim bounds hS hcm h
  obtain ⟨C₁, hsteps, hsim₁⟩ := Steps.toCore hosts hseg hsim
  refine ⟨C, C₁, hinst, hsteps, hsim₁, ?_, ?_, hmod⟩
  · -- the Core code is literally the Core start code
    obtain ⟨cs₁, cf₁, cl₁⟩ := C₁
    have hc := ToCoreSim.sim_code hsim₁
    rw [expression_toCore, startInstrs_toCore hcm] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    cases hstart : cm.start with
    | none =>
      rw [hstart] at hc
      simp only [List.map_nil] at hc
      simp only [coreStartCode, hstart]
      exact List.map_eq_nil_iff.mp hc.symm
    | some x =>
      rw [hstart] at hc
      simp only [List.map_cons, List.map_nil, ToCore.plainOrNull] at hc
      simp only [coreStartCode, hstart]
      refine ToCore.map_norm_eq_of_rigid ?_ hc.symm
      intro y hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact ⟨by simp, by simp⟩
  · -- the Core frame is untouched: the module by `coreSteps_frame_module`, the
    -- locals because both ends of the run have the same 2.0 frame
    obtain ⟨cs₁, cf₁, cl₁⟩ := C₁
    obtain ⟨cs, cf, cl⟩ := C
    have h₀ := ToCoreSim.sim_frame hsim
    have h₁ := ToCoreSim.sim_frame hsim₁
    have hl : cf₁.locals = cf.locals := by
      have := congrArg (fun (f : ToCore.CFrame) => f.locals) (h₀.symm.trans h₁)
      simpa [ToCore.Frame.erase] using this.symm
    have hm : cf₁.module = cf.module := coreSteps_frame_module hsteps
    rcases cf with ⟨l, md⟩
    rcases cf₁ with ⟨l₁, md₁⟩
    simp only at hl hm
    rw [hl, hm]

/-- **Milestone.** A Wasm 2.0 instantiation that terminates — segment programs
and start function — is simulated by Core 3.0 instantiation followed by Core
execution. The 2.0 analogue of `Lime1.Execution.Instantiation.toCore`. -/
theorem Instantiate.toCore {P : Profile} {src : HostSemantics H}
    {tgt : ToCore.CHostSemantics H} (hosts : HostCompatible src tgt)
    {s : Store H} {S : ToCore.CStore H} {m : Module} {cm : Wasm.Module}
    {xas : List ExternAddr} {c b : Config H} {r : Result}
    (bounds : InstantiationBounds s m) (hS : Store.toCore s = some S)
    (hcm : Module.toCore m = some cm) (h : Instantiate P src s m xas c)
    (hrun : Steps P src c b) (hres : b.code = r.toAdmin) :
    ∃ (C C' : ToCore.CConfig H),
      Silmaril.Wasm.Execution.Core.Instantiate P tgt S cm (xas.map ExternAddr.toCore) C ∧
      Silmaril.Wasm.Execution.Core.Steps P tgt C C' ∧
      C'.code = r.toCore.toAdmin ∧
      Store.toCore b.store = some (ToCore.Store.erase C'.store) ∧
      ToCore.ModuleInstSim c.frame.module C.frame.module ∧
      C'.frame.module = C.frame.module := by
  obtain ⟨C, hinst, hsim, -, -, hmod⟩ := instantiate_sim bounds hS hcm h
  obtain ⟨C₁, hsteps₁, hsim₁⟩ := Steps.toCore hosts hrun hsim
  obtain ⟨C', hsteps', hstore', hframe', hcode'⟩ := Sim.result (P := P) (tgt := tgt) hsim₁ hres
  refine ⟨C, C', hinst, hsteps₁.trans hsteps', hcode', ?_, hmod, ?_⟩
  · rw [hstore']
    obtain ⟨cs, cf, cl⟩ := C₁
    obtain ⟨bs, bf, bl⟩ := b
    exact ToCoreSim.sim_store hsim₁
  · rw [hframe', coreSteps_frame_module hsteps₁]

/-- **Milestone.** A Wasm 2.0 instantiation whose start function diverges
diverges in Core 3.0. The 2.0 analogue of
`Lime1.Execution.InstantiationDiverges.toCore`. -/
theorem InstantiateDiverges.toCore {P : Profile} {src : HostSemantics H}
    {tgt : ToCore.CHostSemantics H} (hosts : HostCompatible src tgt)
    {s : Store H} {S : ToCore.CStore H} {m : Module} {cm : Wasm.Module}
    {xas : List ExternAddr}
    (bounds : InstantiationBounds s m) (hS : Store.toCore s = some S)
    (hcm : Module.toCore m = some cm) (h : InstantiateDiverges P src s m xas) :
    ∃ C : ToCore.CConfig H,
      Silmaril.Wasm.Execution.Core.Instantiate P tgt S cm (xas.map ExternAddr.toCore) C ∧
      Silmaril.Wasm.Execution.Core.Diverges P tgt C := by
  obtain ⟨c, hc, hdiv⟩ := h
  obtain ⟨C, hinst, hsim, -, -, -⟩ := instantiate_sim bounds hS hcm hc
  exact ⟨C, hinst, Diverges.toCore hosts hdiv hsim⟩

end Silmaril.Wasm.V2.Execution
