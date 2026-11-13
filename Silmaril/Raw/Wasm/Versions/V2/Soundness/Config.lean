module

public import Silmaril.Raw.Wasm.Versions.V2.Soundness.Defs

/-!
# WebAssembly 2.0: typing of configurations

`Frame_ok`, `Instr_ok2` (here `AdminOk`), `Instrs_ok2` (here `AdminsOk`),
`State_ok`, `Config_ok`, and the structural lemmas that preservation and
progress need.

## Where this comes from

**Deviation (no SpecTec source).** As recorded at length in
`Silmaril/Wasm/V2/Soundness/Store.lean`, the pinned SpecTec wasm-2.0 sources
(WebAssembly/spec `608711107b7f1edb13efd57b7d79b49477462d36`, see
`specs/wasm/core-2.0.json`) contain **no `7-soundness` file**: 2.0 has no
machine-checked typing of administrative instructions at all. Every judgment in
this module is reconstructed from the W3C WebAssembly 2.0 text, appendix
*Soundness*, section "Configuration Validity"
(`document/core/appendix/properties.rst`), cross-checked against the Core 3.0
SpecTec file `specification/wasm-3.0/7.1-soundness.configurations.spectec`,
which this development already transcribes in
`Silmaril/Wasm/Execution/Core/Typing/Config.lean`. Line references of the form
`7.1-soundness:NN` point into that 3.0 file.

Everything 3.0-specific is dropped. In particular **2.0 has no
local-initialization tracking**: a 2.0 `instrtype` is a plain
`resulttype -> resulttype` (`6-typing:142`), with no `->_(x*)` component, so
`Instrs_ok2/seq`'s `$with_locals` premise and the whole `Localval_ok` judgment
disappear. Every 2.0 local is defaultable, so `Frame_ok`'s locals are plain
values (`4-runtime:112`) typed by `ValOk`, not `Option`s typed by
`Localval_ok`. There are likewise no `CALL_REF`/`RETURN_CALL_REF` runtime
annotations, no `HANDLER_`, and no `Instrtype_ok`/`Resulttype_ok` side
conditions (`InstrType.Ok` is definitionally `True` in 2.0, and 2.0 value types
carry no type indices that could dangle), so `AdminsOk/sub`, `AdminsOk/frame`
and `AdminOk/trap` have no well-formedness premise and every structural lemma
below is unconditional.

The administrative forms are exactly the four of `4-runtime:128-135` beyond
`instr`: `REF.FUNC_ADDR`, `REF.HOST_ADDR`, `CALL_ADDR`, `LABEL_`, `FRAME_` and
`TRAP`. `Instr_ok2/ref` (`7.1-soundness:28`) is split into `refFuncAddr` and
`refHostAddr`, because in 2.0 `REF.NULL` is a *source* instruction and the only
administrative references are the two addresses.

## Deviations

**Deviation (`Instrs_ok2/seq` is incomplete).** `Instrs_ok2/seq`
(`7.1-soundness:57`) has a *single* instruction on the left
(`instr_1 instr_2*`) and there is no `Instrs_ok2/instr` rule, while
`Instrs_ok2/frame` applies only to whole suffixes. That system is incomplete:
an instruction can never consume a value produced *before* the preceding
instruction — `(i32.const 1) (i32.const 2) drop drop` has no derivation, since
the tail `drop drop` would have to be typed with the second `drop` seeing an
empty stack. This is the same defect the Core 3.0 layer documents.
`AdminsOk` therefore carries exactly the five rules of the *source* judgment
`Instrs_ok` (`6-typing:156-177`), which `Validation.InstrsOk` transcribes:
`nil` (`/empty`), `single` (`/instr`), `seq` with arbitrary sequences on both
sides, `sub` and `frame`. The one-instruction form is the derived lemma
`AdminsOk.cons`. `AdminsOk.of_instrsOk` is what lines the two up.

**Deviation (`Instr_ok2/frame` and `RETURN`).** `Instr_ok2/frame`
(`7.1-soundness:37`) requires `C'.RETURN = t^n` for the context `C'` produced
by `Frame_ok`. But `Frame_ok` (`7.1-soundness:350`) builds `C'` from
`Moduleinst_ok`, whose realized context has `RETURN` empty
(`ModuleInstOk.return_none`), and then only appends locals. So the premise is
unsatisfiable and *no* frame would be typable. We type the body under
`{ C' with return_ := some ts }`, which is the evident intent and what the W3C
prose says ("the frame is valid with arity n ... under the context C with
return type [t^n]"). Core 3.0 takes the same reading.

**Deviation (host functions in `CALL_ADDR`).** `AdminOk.callAddr` requires only
that the address names an allocated function instance, whatever its
`FuncCode`. SpecTec 2.0 has no host functions (deviation 3 of
`Execution/Step.lean`); the behaviour of a host function is constrained by
`HostOk` (`Soundness/Defs.lean`), not by this judgment. This is exactly how
Core 3.0 types `$invoke`.

**Statement change (store extension needs `StoreOk`).** `FrameOk.extend`,
`AdminOk.extend` and `AdminsOk.extend` take a `StoreOk s` hypothesis, because
`FrameOk` contains `ModuleInstOk`, whose table and memory types are recovered
after growth only through `ExternAddrOk.sub`, whose `ExternType.Ok` premise
comes from `StoreOk`. See `ModuleInstOk.extend` in `Soundness/Store.lean`.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.V2.Validation

variable {H : Type}

/-! ## Frames (`Frame_ok`, `7.1-soundness:350`) -/

/-- `Frame_ok: s |- frame : C ++ {LOCALS t*}` (`7.1-soundness:350`).

The module instance realizes the module-level context `C₀`, and the frame's
locals are typed by `lts`. Wasm 2.0 has no local-initialization tracking and
every local is defaultable (`4-runtime:112` holds `val*`, not `(val?)*`), so
`Localval_ok` collapses to `ValOk` and `lts` is a plain `List ValType`. -/
def FrameOk (s : Store H) (f : Frame) (C : Context) : Prop :=
  ∃ (C₀ : Context) (lts : List ValType), ModuleInstOk s f.module C₀ ∧
    List.Forall₂ (ValOk s) f.locals lts ∧ C = { C₀ with locals := C₀.locals ++ lts }

theorem FrameOk.labels_nil {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    C.labels = [] := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := h
  exact hm.labels_nil

theorem FrameOk.return_none {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    C.return_ = none := by
  obtain ⟨C₀, lts, hm, -, rfl⟩ := h
  exact hm.return_none

/-- The frame's locals and the context's locals have the same length, and
`C.locals` is exactly the list of their types. -/
theorem FrameOk.locals_forall₂ {s : Store H} {f : Frame} {C : Context} (h : FrameOk s f C) :
    List.Forall₂ (ValOk s) f.locals C.locals := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := h
  simpa [hm.locals_nil] using hl

/-! ## Administrative instruction typing (`Instr_ok2`/`Instrs_ok2`) -/

mutual

/-- `Instr_ok2: s; C |- instr : instrtype` (`7.1-soundness:3`), the 2.0
instance: the source rules via `plain`, plus the six administrative forms of
`4-runtime:128-135`. -/
inductive AdminOk (s : Store H) : Context → Admin → InstrType → Prop where
  /-- `Instr_ok2/plain` (`7.1-soundness:10`). -/
  | plain {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it) :
      AdminOk s C (.plain i) it
  /-- `Instr_ok2/ref` (`7.1-soundness:28`) at `Ref_ok/func`: an allocated
  function address is a `FUNCREF`. -/
  | refFuncAddr {C : Context} {a : FuncAddr} {fi : FuncInst H}
      (h : s.funcInst? a = some fi) :
      AdminOk s C (.refFuncAddr a) ⟨[], [.val (.ref .funcref)]⟩
  /-- `Instr_ok2/ref` (`7.1-soundness:28`) at `Ref_ok/host`: a host address is
  an `EXTERNREF`, with no premise. -/
  | refHostAddr {C : Context} (a : HostAddr) :
      AdminOk s C (.refHostAddr a) ⟨[], [.val (.ref .externref)]⟩
  /-- `CALL_ADDR a` (`4-runtime:132`): the 2.0 counterpart of
  `Instr_ok2/call_ref`. The address names an allocated function instance and
  the instruction has that instance's type. -/
  | callAddr {C : Context} {a : FuncAddr} {fi : FuncInst H}
      (h : s.funcInst? a = some fi) :
      AdminOk s C (.callAddr a) (InstrType.lift fi.type.params fi.type.results)
  /-- `Instr_ok2/label` (`7.1-soundness:32`): the continuation is typed with
  the label's arity `n` as its parameters, and the body under `{LABELS (t')^n}
  ++ C`, which is `Context.withLabel`. -/
  | label {C : Context} {n : Nat} {cont : List Instr} {body : List Admin}
      {t' ts : CResultType}
      (hn : t'.length = n)
      (hc : AdminsOk s C (expression cont) ⟨t', ts⟩)
      (hb : AdminsOk s (C.withLabel t') body ⟨[], ts⟩) :
      AdminOk s C (.label n cont body) ⟨[], ts⟩
  /-- `Instr_ok2/frame` (`7.1-soundness:37`): the body is typed in a *fresh*
  context realized by the frame, with `RETURN` set to the frame's arity (see
  the module docstring for the `RETURN` deviation). The outer context `C` is
  irrelevant: a frame is closed. -/
  | frame {C C' : Context} {n : Nat} {fr : Frame} {body : List Admin} {ts : CResultType}
      (hf : FrameOk s fr C') (hn : ts.length = n)
      (hb : AdminsOk s { C' with return_ := some ts } body ⟨[], ts⟩) :
      AdminOk s C (.frame n fr body) ⟨[], ts⟩
  /-- `Instr_ok2/trap` (`7.1-soundness:49`): stack polymorphic in both
  directions. `Instrtype_ok` is vacuous in 2.0, so there is no premise. -/
  | trap {C : Context} {it : InstrType} : AdminOk s C .trap it

/-- `Instrs_ok2: s; C |- instr* : instrtype` (`7.1-soundness:5`), with the five
rules of the *source* judgment `Instrs_ok` (`6-typing:156-177`); see the module
docstring for why `Instrs_ok2/seq` is not used as written. -/
inductive AdminsOk (s : Store H) : Context → List Admin → InstrType → Prop where
  /-- `Instrs_ok/empty` (`6-typing:156`) = `Instrs_ok2/empty`. -/
  | nil {C : Context} : AdminsOk s C [] ⟨[], []⟩
  /-- `Instrs_ok/instr` (`6-typing:159`). -/
  | single {C : Context} {a : Admin} {it : InstrType} (h : AdminOk s C a it) :
      AdminsOk s C [a] it
  /-- `Instrs_ok/seq` (`6-typing:163`), arbitrary sequences on both sides. -/
  | seq {C : Context} {as₁ as₂ : List Admin} {t₁ t₂ t₃ : CResultType}
      (h₁ : AdminsOk s C as₁ ⟨t₁, t₂⟩) (h₂ : AdminsOk s C as₂ ⟨t₂, t₃⟩) :
      AdminsOk s C (as₁ ++ as₂) ⟨t₁, t₃⟩
  /-- `Instrs_ok/sub` (`6-typing:168`) = `Instrs_ok2/sub`; `Instrtype_ok` is
  vacuous in 2.0. -/
  | sub {C : Context} {as : List Admin} {it it' : InstrType}
      (h : AdminsOk s C as it) (hs : InstrType.Sub it it') : AdminsOk s C as it'
  /-- `Instrs_ok/frame` (`6-typing:175`) = `Instrs_ok2/frame`; `Resulttype_ok`
  is vacuous in 2.0. -/
  | frame {C : Context} {as : List Admin} {ts t₁ t₂ : CResultType}
      (h : AdminsOk s C as ⟨t₁, t₂⟩) : AdminsOk s C as ⟨ts ++ t₁, ts ++ t₂⟩

end

/-- `Expr_ok2: s; C |- expr : resulttype` (`7.1-soundness:76`). -/
def AdminExprOk (s : Store H) (C : Context) (as : List Admin) (ts : CResultType) : Prop :=
  AdminsOk s C as ⟨[], ts⟩

/-! ## States and configurations -/

/-- `State_ok: |- state : context` (`7.1-soundness:355`). -/
def StateOk (s : Store H) (f : Frame) (C : Context) : Prop := StoreOk s ∧ FrameOk s f C

/-- `Config_ok: |- config : resulttype` (`7.1-soundness:360`). -/
def ConfigOk (c : Config H) (ts : List CValType) : Prop :=
  ∃ C, StateOk c.store c.frame C ∧ AdminsOk c.store C c.code ⟨[], ts⟩

/-- A configuration whose code is a `result` (`4-runtime:46`): a value stack or
`TRAP`. Progress says a well-typed configuration is terminal or steps. -/
def Config.Terminal (c : Config H) : Prop := ∃ r : Result, c.code = r.toAdmin

/-! ## Derived forms and the source embedding -/

/-- `Instrs_ok/seq` under its usual name. -/
theorem AdminsOk.append {s : Store H} {C : Context} {as₁ as₂ : List Admin}
    {t₁ t₂ t₃ : CResultType} (h₁ : AdminsOk s C as₁ ⟨t₁, t₂⟩)
    (h₂ : AdminsOk s C as₂ ⟨t₂, t₃⟩) : AdminsOk s C (as₁ ++ as₂) ⟨t₁, t₃⟩ := .seq h₁ h₂

/-- The one-instruction-then-rest form, i.e. `Instrs_ok2/seq` as SpecTec writes
it (`7.1-soundness:57`), derived from `single` and `seq`. -/
theorem AdminsOk.cons {s : Store H} {C : Context} {a : Admin} {as : List Admin}
    {t₁ t₂ t₃ : CResultType} (ha : AdminOk s C a ⟨t₁, t₂⟩)
    (hs : AdminsOk s C as ⟨t₂, t₃⟩) : AdminsOk s C (a :: as) ⟨t₁, t₃⟩ :=
  .seq (.single ha) hs

/-- `Instrs_ok/sub` under the name `InstrsOk.mono` uses. -/
theorem AdminsOk.mono {s : Store H} {C : Context} {as : List Admin} {it it' : InstrType}
    (h : AdminsOk s C as it) (hs : InstrType.Sub it it') : AdminsOk s C as it' := .sub h hs

/-- `Instrs_ok/frame` on a packaged `InstrType`. -/
theorem AdminsOk.frame' {s : Store H} {C : Context} {as : List Admin} {ts : CResultType}
    {it : InstrType} (h : AdminsOk s C as it) :
    AdminsOk s C as ⟨ts ++ it.params, ts ++ it.results⟩ := by
  obtain ⟨t₁, t₂⟩ := it
  exact .frame h

/-- The empty sequence at any coercion type `t* -> t*`. -/
theorem AdminsOk.id {s : Store H} {C : Context} (ts : CResultType) :
    AdminsOk s C [] ⟨ts, ts⟩ := by
  simpa using (AdminsOk.frame (s := s) (C := C) (ts := ts) AdminsOk.nil)

/-- Source code types the same as administrative code (`Instr_ok2/plain`,
lifted to sequences). -/
theorem AdminsOk.of_instrsOk {s : Store H} {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) : AdminsOk s C (expression is) it := by
  induction h using InstrsOk.rec (motive_1 := fun _ _ _ _ => True) with
  | empty => exact .nil
  | instr h => exact .single (.plain h)
  | seq _ _ ih₁ ih₂ => simpa [expression] using AdminsOk.seq ih₁ ih₂
  | sub _ hs ih => exact .sub ih hs
  | frame _ ih => exact .frame ih
  | _ => trivial

/-! ## Values as administrative instructions -/

/-- A typed value is a typed administrative instruction (`Instr_ok2/plain` for
`CONST`/`VCONST`/`REF.NULL`, `Instr_ok2/ref` for the two addresses). -/
theorem AdminOk.toAdmin_ok {s : Store H} {C : Context} {v : Val} {t : ValType}
    (h : ValOk s v t) : AdminOk s C v.toAdmin ⟨[], [.val t]⟩ := by
  cases h with
  | num w =>
    rcases w with ⟨t, b⟩
    cases t with
    | int t => exact .plain .intConst
    | float t => exact .plain .floatConst
  | vec b => exact .plain .vecConst
  | ref h =>
    cases h with
    | null t => exact .plain .refNull
    | funcAddr h => exact .refFuncAddr h
    | hostAddr a => exact .refHostAddr a

/-- Inversion for a value instruction: it consumes nothing and pushes exactly
its own (unique) type. -/
theorem AdminOk.toAdmin_inv {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminOk s C v.toAdmin it) :
    it.params = [] ∧ ∃ t : ValType, ValOk s v t ∧ it.results = [.val t] := by
  rcases v with ⟨t, b⟩ | b | r
  · cases t with
    | int t => cases h with | plain h => cases h; exact ⟨rfl, _, .num ⟨.int t, b⟩, rfl⟩
    | float t => cases h with | plain h => cases h; exact ⟨rfl, _, .num ⟨.float t, b⟩, rfl⟩
  · cases h with | plain h => cases h; exact ⟨rfl, _, .vec b, rfl⟩
  · cases r with
    | null t => cases h with | plain h => cases h; exact ⟨rfl, _, .ref (.null t), rfl⟩
    | funcAddr a => cases h with | refFuncAddr h => exact ⟨rfl, _, .ref (.funcAddr h), rfl⟩
    | hostAddr a => cases h with | refHostAddr a => exact ⟨rfl, _, .ref (.hostAddr a), rfl⟩

/-- A typed value stack pushes its types. -/
theorem AdminsOk.of_vals {s : Store H} {C : Context} {vs : List Val} {ts : ResultType}
    (h : List.Forall₂ (ValOk s) vs ts) : AdminsOk s C (vals vs) ⟨[], liftResult ts⟩ := by
  induction h with
  | nil => exact .nil
  | @cons v t vs ts hv _ ih =>
    have h2 : AdminsOk s C (vals vs) ⟨[.val t] ++ [], [.val t] ++ liftResult ts⟩ := .frame ih
    simpa using AdminsOk.cons (AdminOk.toAdmin_ok (C := C) hv) h2


/-- Inversion of `AdminOk` at a plain instruction. 2.0 has no administrative
retyping of any source instruction (Core 3.0 needs a `throw_ref` deviation
there), so this is exact. -/
theorem AdminOk.plain_inv {s : Store H} {C : Context} {i : Instr} {it : InstrType}
    (h : AdminOk s C (.plain i) it) : InstrOk C i it := by
  cases h with | plain h => exact h

/-- `TRAP` alone has every instruction type (`Instr_ok2/trap`). -/
theorem AdminsOk.trap_it {s : Store H} {C : Context} (it : InstrType) :
    AdminsOk s C [.trap] it := .single .trap

/-! ## A non-mutual eliminator for `AdminsOk`

Every structural lemma below is an induction on an `AdminsOk` derivation in
which the `AdminOk` premises are used as black boxes, so the `AdminOk` motive
is `True`. -/

theorem AdminsOk.rec' {s : Store H} {motive : Context → List Admin → InstrType → Prop}
    (nil : ∀ {C : Context}, motive C [] ⟨[], []⟩)
    (single : ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → motive C [a] it)
    (seq : ∀ {C : Context} {as₁ as₂ : List Admin} {t₁ t₂ t₃ : CResultType},
      AdminsOk s C as₁ ⟨t₁, t₂⟩ → AdminsOk s C as₂ ⟨t₂, t₃⟩ →
      motive C as₁ ⟨t₁, t₂⟩ → motive C as₂ ⟨t₂, t₃⟩ → motive C (as₁ ++ as₂) ⟨t₁, t₃⟩)
    (sub : ∀ {C : Context} {as : List Admin} {it it' : InstrType},
      AdminsOk s C as it → InstrType.Sub it it' → motive C as it → motive C as it')
    (frame : ∀ {C : Context} {as : List Admin} {ts t₁ t₂ : CResultType},
      AdminsOk s C as ⟨t₁, t₂⟩ → motive C as ⟨t₁, t₂⟩ → motive C as ⟨ts ++ t₁, ts ++ t₂⟩)
    {C : Context} {L : List Admin} {it : InstrType} (h : AdminsOk s C L it) : motive C L it := by
  refine AdminsOk.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun C L it _ => motive C L it) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals try (intros; trivial)
  · exact nil
  · intro C a it ha _; exact single ha
  · intro C as₁ as₂ t₁ t₂ t₃ h₁ h₂ ih₁ ih₂; exact seq h₁ h₂ ih₁ ih₂
  · intro C as it it' h hs ih; exact sub h hs ih
  · intro C as ts t₁ t₂ h ih; exact frame h ih

/-! ## Typings of the empty sequence -/

/-- The empty administrative sequence has exactly the coercion types, as
`InstrsOk.nil_iff` says for the source judgment. -/
theorem AdminsOk.nil_inv {s : Store H} {C : Context} {t₁ t₂ : CResultType}
    (h : AdminsOk s C [] ⟨t₁, t₂⟩) : CResultType.Sub t₁ t₂ := by
  have key : ∀ {C : Context} {L : List Admin} {it : InstrType}, AdminsOk s C L it →
      L = [] → CResultType.Sub it.params it.results := by
    intro C L it h
    refine AdminsOk.rec' (motive := fun _ L it => L = [] → CResultType.Sub it.params it.results)
      ?_ ?_ ?_ ?_ ?_ h
    · intro _ _; exact CResultType.sub_nil_nil
    · intro C a it _ e; exact absurd e (by simp)
    · intro C as₁ as₂ t₁ t₂ t₃ _ _ ih₁ ih₂ e
      obtain ⟨e₁, e₂⟩ := List.append_eq_nil_iff.mp e
      exact CResultType.sub_trans (ih₁ e₁) (ih₂ e₂)
    · intro C as it it' _ hs ih e
      exact CResultType.sub_trans hs.1 (CResultType.sub_trans (ih e) hs.2)
    · intro C as ts t₁ t₂ _ ih e
      exact CResultType.sub_append (CResultType.sub_refl ts) (ih e)
  exact key h rfl

/-! ## Splitting a typed sequence

Unlike the Core 3.0 analogues these need no well-formedness hypothesis at all:
2.0 has no `Resulttype_ok` and no `Instrtype_ok`, so there is nothing to carry. -/

theorem AdminsOk.split_aux {s : Store H} {C : Context} {as : List Admin} {it : InstrType}
    (h : AdminsOk s C as it) : ∀ as₁ as₂, as = as₁ ++ as₂ →
      ∃ tm, AdminsOk s C as₁ ⟨it.params, tm⟩ ∧ AdminsOk s C as₂ ⟨tm, it.results⟩ := by
  refine AdminsOk.rec' (motive := fun C as it => ∀ as₁ as₂, as = as₁ ++ as₂ →
    ∃ tm, AdminsOk s C as₁ ⟨it.params, tm⟩ ∧ AdminsOk s C as₂ ⟨tm, it.results⟩)
    ?_ ?_ ?_ ?_ ?_ h
  · intro C as₁ as₂ e
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp e.symm
    exact ⟨[], .nil, .nil⟩
  · intro C a it ha as₁ as₂ e
    rcases List.append_eq_singleton_iff.mp e.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨it.params, AdminsOk.id _, .single ha⟩
    · exact ⟨it.results, .single ha, AdminsOk.id _⟩
  · intro C l₁ l₂ t₁ t₂ t₃ h₁ h₂ ih₁ ih₂ as₁ as₂ e
    rcases List.append_eq_append_iff.mp e with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · obtain ⟨tm, ha, hb⟩ := ih₂ a' as₂ rfl
      exact ⟨tm, .seq h₁ ha, hb⟩
    · obtain ⟨tm, ha, hb⟩ := ih₁ as₁ c' rfl
      exact ⟨tm, ha, .seq hb h₂⟩
  · intro C as it it' _ hs ih as₁ as₂ e
    obtain ⟨tm, ha, hb⟩ := ih as₁ as₂ e
    exact ⟨tm, .sub ha ⟨hs.1, CResultType.sub_refl tm⟩, .sub hb ⟨CResultType.sub_refl tm, hs.2⟩⟩
  · intro C as F t₁ t₂ _ ih as₁ as₂ e
    obtain ⟨tm, ha, hb⟩ := ih as₁ as₂ e
    exact ⟨F ++ tm, .frame ha, .frame hb⟩

/-- **Splitting.** A typed administrative sequence splits at every position,
with a middle type. -/
theorem AdminsOk.append_inv {s : Store H} {C : Context} {as₁ as₂ : List Admin}
    {t₁ t₃ : CResultType} (h : AdminsOk s C (as₁ ++ as₂) ⟨t₁, t₃⟩) :
    ∃ t₂, AdminsOk s C as₁ ⟨t₁, t₂⟩ ∧ AdminsOk s C as₂ ⟨t₂, t₃⟩ :=
  h.split_aux as₁ as₂ rfl

/-- Inversion for a one-element sequence: up to `Instrs_ok/frame` and
`Instrs_ok/sub`, the sequence has the instruction's own type. -/
theorem AdminsOk.single_inv {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    (h : AdminsOk s C [a] it) :
    ∃ (ts : CResultType) (it₀ : InstrType), AdminOk s C a it₀ ∧
      InstrType.Sub ⟨ts ++ it₀.params, ts ++ it₀.results⟩ it := by
  have key : ∀ {C : Context} {L : List Admin} {it : InstrType}, AdminsOk s C L it →
      ∀ b, L = [b] → ∃ (ts : CResultType) (it₀ : InstrType), AdminOk s C b it₀ ∧
        InstrType.Sub ⟨ts ++ it₀.params, ts ++ it₀.results⟩ it := by
    intro C L it h
    refine AdminsOk.rec' (motive := fun C L it => ∀ b, L = [b] →
      ∃ (ts : CResultType) (it₀ : InstrType), AdminOk s C b it₀ ∧
        InstrType.Sub ⟨ts ++ it₀.params, ts ++ it₀.results⟩ it) ?_ ?_ ?_ ?_ ?_ h
    · intro C b e; exact absurd e.symm (by simp)
    · intro C a it ha b e
      obtain rfl : a = b := by simpa using e
      exact ⟨[], it, ha, by simpa using InstrType.sub_refl it⟩
    · intro C l₁ l₂ t₁ t₂ t₃ h₁ h₂ ih₁ ih₂ b e
      rcases List.append_eq_singleton_iff.mp e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨ts, it₀, ha, hsub⟩ := ih₂ b rfl
        exact ⟨ts, it₀, ha, ⟨CResultType.sub_trans (AdminsOk.nil_inv h₁) hsub.1, hsub.2⟩⟩
      · obtain ⟨ts, it₀, ha, hsub⟩ := ih₁ b rfl
        exact ⟨ts, it₀, ha, ⟨hsub.1, CResultType.sub_trans hsub.2 (AdminsOk.nil_inv h₂)⟩⟩
    · intro C as it it' _ hs ih b e
      obtain ⟨ts, it₀, ha, hsub⟩ := ih b e
      exact ⟨ts, it₀, ha, InstrType.sub_trans hsub hs⟩
    · intro C as F t₁ t₂ _ ih b e
      obtain ⟨ts, it₀, ha, hsub⟩ := ih b e
      refine ⟨F ++ ts, it₀, ha, ?_⟩
      refine ⟨?_, ?_⟩ <;>
        simp only [List.append_assoc] <;>
        exact CResultType.sub_append (CResultType.sub_refl F) (by first | exact hsub.1 | exact hsub.2)
  exact key h a rfl

/-! ## Typings of value sequences -/

theorem AdminsOk.vals_aux {s : Store H} {C : Context} {as : List Admin} {it : InstrType}
    (h : AdminsOk s C as it) : ∀ vs, as = vals vs →
      ∃ ts : ResultType, List.Forall₂ (ValOk s) vs ts ∧
        CResultType.Sub (it.params ++ liftResult ts) it.results := by
  refine AdminsOk.rec' (motive := fun _ as it => ∀ vs, as = vals vs →
    ∃ ts : ResultType, List.Forall₂ (ValOk s) vs ts ∧
      CResultType.Sub (it.params ++ liftResult ts) it.results) ?_ ?_ ?_ ?_ ?_ h
  · intro C vs e
    obtain rfl : vs = [] := by simpa [vals] using e.symm
    exact ⟨[], .nil, by simp⟩
  · intro C a it ha vs e
    obtain ⟨v, rfl, rfl⟩ := List.map_eq_singleton_iff.mp (show vals vs = [a] from e.symm)
    obtain ⟨hp, t, hvt, hr⟩ := AdminOk.toAdmin_inv ha
    refine ⟨[t], .cons hvt .nil, ?_⟩
    rw [hp, hr]
    simpa using CResultType.sub_refl [CValType.val t]
  · intro C l₁ l₂ t₁ t₂ t₃ _ _ ih₁ ih₂ vs e
    obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp (show vals vs = l₁ ++ l₂ from e.symm)
    obtain ⟨ts₁, hv₁, r₁⟩ := ih₁ vs₁ e₁.symm
    obtain ⟨ts₂, hv₂, r₂⟩ := ih₂ vs₂ e₂.symm
    refine ⟨ts₁ ++ ts₂, List.rel_append hv₁ hv₂, ?_⟩
    have : CResultType.Sub ((t₁ ++ liftResult ts₁) ++ liftResult ts₂) (t₂ ++ liftResult ts₂) :=
      CResultType.sub_append r₁ (CResultType.sub_refl _)
    simpa [List.append_assoc] using CResultType.sub_trans this r₂
  · intro C as it it' _ hs ih vs e
    obtain ⟨ts, hv, r⟩ := ih vs e
    refine ⟨ts, hv, ?_⟩
    have h1 : CResultType.Sub (it'.params ++ liftResult ts) (it.params ++ liftResult ts) :=
      CResultType.sub_append hs.1 (CResultType.sub_refl _)
    exact CResultType.sub_trans h1 (CResultType.sub_trans r hs.2)
  · intro C as F t₁ t₂ _ ih vs e
    obtain ⟨ts, hv, r⟩ := ih vs e
    refine ⟨ts, hv, ?_⟩
    simpa [List.append_assoc] using
      CResultType.sub_append (CResultType.sub_refl F) r

/-- Inversion for a value sequence: it pushes (a supertype of) its own value
types. 2.0 values never have type `BOT`, so the types are syntactic. -/
theorem AdminsOk.vals_inv {s : Store H} {C : Context} {vs : List Val} {t₁ t₂ : CResultType}
    (h : AdminsOk s C (vals vs) ⟨t₁, t₂⟩) :
    ∃ ts : ResultType, List.Forall₂ (ValOk s) vs ts ∧
      CResultType.Sub (t₁ ++ liftResult ts) t₂ :=
  h.vals_aux vs rfl

/-! ## Store extension -/

/-- `Frame_ok` is preserved by store extension. (Statement change: needs
`StoreOk s`, because `ModuleInstOk.extend` does.) -/
theorem FrameOk.extend {s s' : Store H} {f : Frame} {C : Context} (hs : StoreOk s)
    (he : Extend s s') (h : FrameOk s f C) : FrameOk s' f C := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := h
  exact ⟨C₀, lts, hm.extend hs he, hl.imp fun _ _ h => h.extend he, rfl⟩

mutual

theorem AdminOk.extend_aux {s s' : Store H} (hS : StoreOk s) (he : Extend s s') :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → AdminOk s' C a it
  | _, _, _, .plain h => .plain h
  | _, _, _, .refFuncAddr h => .refFuncAddr (he.funcInst? h)
  | _, _, _, .refHostAddr a => .refHostAddr a
  | _, _, _, .callAddr h => .callAddr (he.funcInst? h)
  | _, _, _, .label hn hc hb =>
    .label hn (AdminsOk.extend_aux hS he hc) (AdminsOk.extend_aux hS he hb)
  | _, _, _, .frame hf hn hb =>
    .frame (hf.extend hS he) hn (AdminsOk.extend_aux hS he hb)
  | _, _, _, .trap => .trap

theorem AdminsOk.extend_aux {s s' : Store H} (hS : StoreOk s) (he : Extend s s') :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → AdminsOk s' C as it
  | _, _, _, .nil => .nil
  | _, _, _, .single h => .single (AdminOk.extend_aux hS he h)
  | _, _, _, .seq h₁ h₂ => .seq (AdminsOk.extend_aux hS he h₁) (AdminsOk.extend_aux hS he h₂)
  | _, _, _, .sub h hs => .sub (AdminsOk.extend_aux hS he h) hs
  | _, _, _, .frame h => .frame (AdminsOk.extend_aux hS he h)

end

/-- Typing of a single administrative instruction is preserved by store
extension. -/
theorem AdminOk.extend {s s' : Store H} {C : Context} {a : Admin} {it : InstrType}
    (hs : StoreOk s) (he : Extend s s') (h : AdminOk s C a it) : AdminOk s' C a it :=
  AdminOk.extend_aux hs he h

/-- Typing of administrative code is preserved by store extension. -/
theorem AdminsOk.extend {s s' : Store H} {C : Context} {as : List Admin} {it : InstrType}
    (hs : StoreOk s) (he : Extend s s') (h : AdminsOk s C as it) : AdminsOk s' C as it :=
  AdminsOk.extend_aux hs he h

/-! ## Pure-redex decomposition

The progress analogue of `Silmaril/Wasm/Execution/Core/Soundness/PureRedex.lean`:
administrative code is either a value stack or splits as `val* a instr*` with
`a` not a value, and the typing splits with it. -/

/-- Syntactic decomposition: code is all values, or has a leftmost non-value. -/
theorem decompose (as : List Admin) :
    (∃ vs, as = vals vs) ∨ ∃ vs a rest, as = vals vs ++ a :: rest ∧ a.val? = none := by
  induction as with
  | nil => exact .inl ⟨[], rfl⟩
  | cons a as ih =>
    cases ha : a.val? with
    | none => exact .inr ⟨[], a, as, rfl, ha⟩
    | some v =>
      obtain rfl := Admin.toAdmin_of_val? ha
      rcases ih with ⟨vs, rfl⟩ | ⟨vs, b, rest, rfl, hb⟩
      · exact .inl ⟨v :: vs, rfl⟩
      · exact .inr ⟨v :: vs, b, rest, rfl, hb⟩

/-- **Pure-redex decomposition.** Well-typed administrative code that is not a
value stack splits as `vals vs ++ redex :: rest`, with the values typed, the
redex typed on its own, and the rest typed from the redex's results. This is
what progress inducts on. -/
theorem AdminsOk.redex_decompose {s : Store H} {C : Context} {as : List Admin}
    {t₁ t₂ : CResultType} (h : AdminsOk s C as ⟨t₁, t₂⟩) (hv : ∀ vs, as ≠ vals vs) :
    ∃ (vs : List Val) (a : Admin) (rest : List Admin) (ts : ResultType) (tm tm' : CResultType),
      as = vals vs ++ a :: rest ∧ a.val? = none ∧
      List.Forall₂ (ValOk s) vs ts ∧ CResultType.Sub (t₁ ++ liftResult ts) tm ∧
      AdminsOk s C (vals vs) ⟨t₁, tm⟩ ∧ AdminsOk s C [a] ⟨tm, tm'⟩ ∧
      AdminsOk s C rest ⟨tm', t₂⟩ := by
  rcases decompose as with ⟨vs, rfl⟩ | ⟨vs, a, rest, rfl, hval⟩
  · exact absurd rfl (hv vs)
  · obtain ⟨tm, h₁, h₂⟩ := AdminsOk.append_inv h
    obtain ⟨ts, hvs, hsub⟩ := AdminsOk.vals_inv h₁
    obtain ⟨tm', ha, hr⟩ := AdminsOk.append_inv (as₁ := [a]) (as₂ := rest) h₂
    exact ⟨vs, a, rest, ts, tm, tm', rfl, hval, hvs, hsub, h₁, ha, hr⟩

end Silmaril.Wasm.V2.Execution
