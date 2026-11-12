module

public import Silmaril.Proofs.Wasm.Game.Machine.Soft

/-!
# Determinism up to profile choices: control heads

`Head.det_ctl_soft`: two control head steps at the same instruction, under an arbitrary
profile, consume the same arguments and have equal results, or (under a context rule) both
results are `Soft`.

Source: silmaril-lean's `Det.Head.det_ctl`
(`Silmaril/Wasm/SingleThreaded/Determinism/HeadCtl.lean`, pinned revision) with the profile
generalised and the joinability relation `SoftPair`; the context cases are
`ctxt_label_soft`, `ctxt_handler_soft`, `ctxt_frame_soft`. The generic closers (`hd_close`,
`ctl_single`, `ctl_step`, `ctl_body`, `ctl_same`, `ctl_vals`, `ctl_catch`, `ctl_block`) are
silmaril-lean's tactic macros, used unchanged. The eleven per-rule case arms of `det_ctl`,
which silmaril-lean writes inline with in-place rewriting (`rw … at`, `simp at`, `subst`), are
restated here as lemmas `Head.ctlArm_*` with explicit statements and proofs in stated-fact
form; each arm of `Head.det_ctl_soft` is a single application of one of them.

**Elaboration time.** `det_ctl` tries every generic closer on every pair of rules (`fam_excl`
after each case split, then `hd_close`, then `ctl_single` … `ctl_catch` in turn); the failed
attempts were nearly all of this module's 325 s. Here each pair goes only to the closer that
closes it: `fam_close` runs the family exclusion on the goals of the family rules only, with
their own shape lemma; `all_goals_except` runs `hd_close` on every pair but the listed ones
(which `hd_close` cannot close), and `on_goals` sends the remaining pairs, listed by the first of
silmaril's closers that applies to them, to that closer (`ctl_body` takes the rest). The lists
were read off a run of `det_ctl`'s order of closers on this statement; a pair in the wrong list
fails the build. The script (`det_ctl_soft_tac`) is run once per shape of the instruction `e`
(`Head.det_ctl_soft_plain`, `_label`, `_handler`, `_frame`, …), so the eight proofs are
elaborated in parallel; the largest, `_handler`, takes about 12 s of the module's 15 s.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Choice

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

/-- Run `tac` on every goal whose case tag is not one of `tags`; the goals with those tags stay
open, in their order. (`case` selects goals by tag; this is its complement.) -/
syntax (name := allGoalsExcept) "all_goals_except " "[" ident,* "] " tactic : tactic

open Lean Elab Tactic in
@[tactic allGoalsExcept] meta def evalAllGoalsExcept : Tactic := fun stx => do
  let skip := stx[2].getSepArgs.map (·.getId)
  let mut rest : Array MVarId := #[]
  for g in ← getGoals do
    if ← g.isAssigned then continue
    if skip.contains (← g.getTag) then
      rest := rest.push g
    else
      setGoals [g]
      evalTactic stx[4]
      rest := rest ++ (← getGoals).toArray
  setGoals rest.toList

/-- `fam_excl` on the goals of the family rules of `Head` only (the goals whose case tag ends in
`parametric`, `numeric`, …, `aggregate`), with the shape lemma of that family: a family rule at a
control instruction is impossible. The other goals are left as they are. (`fam_excl` itself
tries the eight shape lemmas in turn on every goal, which is most of the cost of the case
splits below.) -/
syntax (name := famClose) "fam_close" : tactic

open Lean Elab Tactic in
@[tactic famClose] meta def evalFamClose : Tactic := fun _ => do
  let shapes : List (String × Name) :=
    [("parametric", `ParametricStep.shape), ("numeric", `NumericStep.shape),
     ("vector", `VectorStep.shape), ("variable", `VariableStep.shape),
     ("table", `TableStep.shape), ("memory", `MemoryStep.shape),
     ("reference", `RefStep.shape), ("aggregate", `AggregateStep.shape)]
  let mut rest : Array MVarId := #[]
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let last := match (← g.getTag) with
      | .str _ s => s
      | _ => ""
    match shapes.lookup last with
    | some shape =>
      setGoals [g]
      evalTactic (← `(tactic|
        (exfalso; exact $(mkIdent `hc) (famOf_of_shape ($(mkIdent shape) ‹_›)).2 (by decide))))
      rest := rest ++ (← getGoals).toArray
    | none => rest := rest.push g
  setGoals rest.toList

variable {H : Type}

variable {P : Profile} {s : Store H} {f : Frame} {c : Config H} {p : List Val}

/-- Equal results with no extra arguments are joinable. -/
theorem Head.ctlArm_close {c₁ c₂ : Config H} (hp : p = []) (hc : c₁ = c₂) :
    p = [] ∧ Join (SoftPair P c) c₁ c₂ :=
  ⟨hp, hc ▸ Join.rfl'⟩

/-- No extra arguments when both rules take none. -/
theorem Head.ctlArm_nil (hp : [] = p ++ []) : p = [] := by
  simpa using hp.symm

/-- `throw` against `throw`: the tag lookup and its expansion agree. -/
theorem Head.ctlArm_throw {x : TagIdx} {ta₁ ta₂ : Nat} {ti₁ ti₂ : TagInst} {ts₁ ts₂ : Ty TKind.val.list}
    {args : List Val} (ht₁ : s.tag? f x = some (ta₁, ti₁)) (ht₂ : s.tag? f x = some (ta₂, ti₂))
    (he₁ : Expand ti₁.type (ts₁.func Ty.nil)) (he₂ : Expand ti₂.type (ts₂.func Ty.nil))
    (hn₁ : (p ++ args).length = ts₁.length) (hn₂ : args.length = ts₂.length) :
    p = [] ∧ Join (SoftPair P c)
      ⟨s.addExn { tag := ta₁, fields := p ++ args }, f,
        [.ref (.exn s.exns.length), .plain .throwRef]⟩
      ⟨s.addExn { tag := ta₂, fields := args }, f, [.ref (.exn s.exns.length), .plain .throwRef]⟩ := by
  have hti : (ta₁, ti₁) = (ta₂, ti₂) := Option.some.inj (ht₁.symm.trans ht₂)
  have hta : ta₁ = ta₂ := congrArg Prod.fst hti
  have hti' : ti₁ = ti₂ := congrArg Prod.snd hti
  have he₂' : Expand ti₁.type (ts₂.func Ty.nil) := hti' ▸ he₂
  have hts : ts₁ = ts₂ := by simpa using Expand.det he₁ he₂'
  have hlen : p.length + args.length = args.length := by
    rw [← List.length_append, hn₁, hts, hn₂]
  have hp0 : p = [] := List.eq_nil_of_length_eq_zero (by omega)
  exact Head.ctlArm_close hp0 (by rw [hp0, hta, List.nil_append])

/-- `call` (or `return_call`) twice: the function address and instance agree; `k` is the admin instruction built from the function type. -/
theorem Head.ctlArm_call {x : FuncIdx} {a₁ a₂ : Nat} {fi₁ fi₂ : FuncInst H} (k : DefType → Admin)
    (hp : [] = p ++ []) (hx₁ : f.module.funcs[Idx.toNat x]? = some a₁)
    (hx₂ : f.module.funcs[Idx.toNat x]? = some a₂) (hf₁ : s.funcs[a₁]? = some fi₁)
    (hf₂ : s.funcs[a₂]? = some fi₂) :
    p = [] ∧ Join (SoftPair P c) ⟨s, f, [.ref (.func a₁), k fi₁.type]⟩
      ⟨s, f, [.ref (.func a₂), k fi₂.type]⟩ := by
  have ha : a₁ = a₂ := Option.some.inj (hx₁.symm.trans hx₂)
  have hf₂' : s.funcs[a₁]? = some fi₂ := ha ▸ hf₂
  have hfi : fi₁ = fi₂ := Option.some.inj (hf₁.symm.trans hf₂')
  exact Head.ctlArm_close (Head.ctlArm_nil hp) (by rw [ha, hfi])

/-- Two `catch`/`catch_ref` handler steps: the exception lookup agrees; `k` builds the result code. -/
theorem Head.ctlArm_catch {a : Nat} {e₁ e₂ : ExnInst} (k : ExnInst → List Admin) (hp : [] = p ++ [])
    (he₁ : s.exns[a]? = some e₁) (he₂ : s.exns[a]? = some e₂) :
    p = [] ∧ Join (SoftPair P c) ⟨s, f, k e₁⟩ ⟨s, f, k e₂⟩ := by
  have he : e₁ = e₂ := Option.some.inj (he₁.symm.trans he₂)
  exact Head.ctlArm_close (Head.ctlArm_nil hp) (by rw [he])

/-- `br_table` in range twice: the index, hence the label, agrees. -/
theorem Head.ctlArm_brTableLt {ls : List LabelIdx} {i₁ i₂ : BitVec 32} {l₁ l₂ : LabelIdx}
    (hp : [Val.num { type := .int .i32, bits := i₁ }] = p ++ [Val.num { type := .int .i32, bits := i₂ }])
    (hi₁ : ls[i₁.toNat]? = some l₁) (hi₂ : ls[i₂.toNat]? = some l₂) :
    p = [] ∧ Join (SoftPair P c) ⟨s, f, [.plain (.br l₁)]⟩ ⟨s, f, [.plain (.br l₂)]⟩ := by
  have hsplit : p = [] ∧ Val.num { type := .int .i32, bits := i₁ } =
      Val.num { type := .int .i32, bits := i₂ } := singleton_hp hp
  have hi : i₁ = i₂ := eq_of_heq (NumVal.mk.inj (Val.num.inj hsplit.2)).2
  have hi₂' : ls[i₁.toNat]? = some l₂ := hi ▸ hi₂
  have hl : l₁ = l₂ := Option.some.inj (hi₁.symm.trans hi₂')
  exact Head.ctlArm_close hsplit.1 (by rw [hl])

/-- `br 0` out of a label twice: the returned values agree. -/
theorem Head.ctlArm_brLabelZero {cont : List Instr} {vs'₁ vs₁ vs'₂ vs₂ : List Val} {l₁ l₂ : LabelIdx}
    {r₁ r₂ : List Admin} (hp : [] = p ++ []) (hn : vs₂.length = vs₁.length)
    (hb : vals vs'₁ ++ vals vs₁ ++ [.plain (.br l₁)] ++ r₁ =
      vals vs'₂ ++ vals vs₂ ++ [.plain (.br l₂)] ++ r₂) :
    p = [] ∧ Join (SoftPair P c) ⟨s, f, vals vs₁ ++ expression cont⟩
      ⟨s, f, vals vs₂ ++ expression cont⟩ := by
  have hb' : vals (vs'₁ ++ vs₁) ++ Admin.plain (.br l₁) :: r₁ =
      vals (vs'₂ ++ vs₂) ++ Admin.plain (.br l₂) :: r₂ := by simpa using hb
  have h1 : vs'₁ ++ vs₁ = vs'₂ ++ vs₂ := (vals_append_cons_inj hb' rfl rfl).1
  have hvs : vs₁ = vs₂ := (List.append_inj' h1 hn.symm).2
  exact Head.ctlArm_close (Head.ctlArm_nil hp) (by rw [hvs])

/-- `return` out of a frame twice: the returned values agree. -/
theorem Head.ctlArm_returnFrame {vs'₁ vs₁ vs'₂ vs₂ : List Val} {r₁ r₂ : List Admin} (hp : [] = p ++ [])
    (hn : vs₂.length = vs₁.length)
    (hb : vals vs'₁ ++ vals vs₁ ++ [.plain .return_] ++ r₁ =
      vals vs'₂ ++ vals vs₂ ++ [.plain .return_] ++ r₂) :
    p = [] ∧ Join (SoftPair P c) ⟨s, f, vals vs₁⟩ ⟨s, f, vals vs₂⟩ := by
  have hvs : vs₁ = vs₂ := br_body_inj rfl hb hn.symm
  exact Head.ctlArm_close (Head.ctlArm_nil hp) (by rw [hvs])

/-- Decomposing a frame body at a reference followed by a non-value instruction. -/
theorem Head.ctlArm_rcrInj {A₁ A₂ B₁ B₂ : List Val} {x y : Val} {d₁ d₂ : Admin} {r₁ r₂ : List Admin}
    (hd₁ : d₁.val? = none) (hd₂ : d₂.val? = none)
    (hb : vals A₁ ++ vals A₂ ++ [x.toAdmin, d₁] ++ r₁ = vals B₁ ++ vals B₂ ++ [y.toAdmin, d₂] ++ r₂) :
    A₁ ++ A₂ = B₁ ++ B₂ ∧ x = y ∧ d₁ = d₂ := by
  have hb' : vals (A₁ ++ A₂) ++ [x.toAdmin, d₁] ++ r₁ = vals (B₁ ++ B₂) ++ [y.toAdmin, d₂] ++ r₂ := by
    simpa only [vals_append] using hb
  have h : A₁ ++ A₂ = B₁ ++ B₂ ∧ x = y ∧ d₁ = d₂ ∧ r₁ = r₂ := frame_body_inj hd₁ hd₂ hb'
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- Two tail calls of function addresses out of a frame (instructions `d₁`, `d₂`): the results agree. -/
theorem Head.ctlArm_rcrAddr {m : ModuleInst} {vs'₁ vs₁ vs'₂ vs₂ : List Val} {a₁ a₂ : Nat}
    {fn₁ fn₂ : FuncInst H} {ps₁ rs₁ ps₂ rs₂ : Ty TKind.val.list} {d₁ d₂ : Admin}
    {r₁ r₂ : List Admin} (hp : [] = p ++ []) (hd₁ : d₁.val? = none) (hd₂ : d₂.val? = none)
    (hf₁ : s.funcs[a₁]? = some fn₁) (hf₂ : s.funcs[a₂]? = some fn₂)
    (he₁ : Expand fn₁.type (ps₁.func rs₁)) (he₂ : Expand fn₂.type (ps₂.func rs₂))
    (hn₁ : vs₁.length = ps₁.length) (hn₂ : vs₂.length = ps₂.length)
    (hb : vals vs'₁ ++ vals vs₁ ++ [.ref (.func a₁), d₁] ++ r₁ =
      vals vs'₂ ++ vals vs₂ ++ [.ref (.func a₂), d₂] ++ r₂) :
    p = [] ∧ Join (SoftPair P c) ⟨s, f, vals vs₁ ++ [.ref (.func a₁), d₁.retToCallIn m]⟩
      ⟨s, f, vals vs₂ ++ [.ref (.func a₂), d₂.retToCallIn m]⟩ := by
  have h : vs'₁ ++ vs₁ = vs'₂ ++ vs₂ ∧ Val.ref (.func a₁) = Val.ref (.func a₂) ∧ d₁ = d₂ :=
    Head.ctlArm_rcrInj hd₁ hd₂ hb
  have ha : a₁ = a₂ := by simpa using h.2.1
  have hf₂' : s.funcs[a₁]? = some fn₂ := ha ▸ hf₂
  have hfn : fn₁ = fn₂ := Option.some.inj (hf₁.symm.trans hf₂')
  have he₂' : Expand fn₁.type (ps₂.func rs₂) := hfn ▸ he₂
  have hps : ps₁ = ps₂ ∧ rs₁ = rs₂ := by simpa using Expand.det he₁ he₂'
  have hlen : vs₁.length = vs₂.length := by rw [hn₁, hn₂, hps.1]
  have hvs : vs₁ = vs₂ := (List.append_inj' h.1 hlen).2
  exact Head.ctlArm_close (Head.ctlArm_nil hp) (by rw [hvs, ha, h.2.2])

/-- A frame body cannot tail-call both a function address and `null` at the same position. -/
theorem Head.ctlArm_rcrAddrNull {A₁ A₂ B : List Val} {a : Nat} {d₁ d₂ : Admin} {r₁ r₂ : List Admin}
    (hd₁ : d₁.val? = none) (hd₂ : d₂.val? = none)
    (hb : vals A₁ ++ vals A₂ ++ [.ref (.func a), d₁] ++ r₁ = vals B ++ [.ref .null, d₂] ++ r₂) :
    False := by
  have hb' : vals A₁ ++ vals A₂ ++ [.ref (.func a), d₁] ++ r₁ =
      vals [] ++ vals B ++ [.ref .null, d₂] ++ r₂ := by simpa using hb
  have hx : Val.ref (.func a) = Val.ref .null :=
    (Head.ctlArm_rcrInj (x := .ref (.func a)) (y := .ref .null) hd₁ hd₂ hb').2.1
  exact absurd hx (by simp)

/-- `call_ref` cannot see both `null` and a function address on top of the stack. -/
theorem Head.ctlArm_callRefNull {vs : List Val} {a : Nat}
    (hp : [Val.ref .null] = p ++ (vs ++ [Val.ref (.func a)])) : False := by
  have hp' : [Val.ref .null] = p ++ vs ++ [Val.ref (.func a)] := by rw [hp, List.append_assoc]
  have hx : Val.ref .null = Val.ref (.func a) := (singleton_hp hp').2
  exact absurd hx (by simp)

/-- Two `call_ref`s of function addresses: the arguments, function and code agree. -/
theorem Head.ctlArm_callRefFunc {vs₁ vs₂ : List Val} {a₁ a₂ : Nat} {fi₁ fi₂ : FuncInst H}
    {ps₁ rs₁ ps₂ rs₂ : Ty TKind.val.list} {code₁ code₂ : Func}
    (ha : p ++ (vs₂ ++ [Val.ref (.func a₂)]) = vs₁ ++ [Val.ref (.func a₁)])
    (hf₁ : s.funcs[a₁]? = some fi₁) (hf₂ : s.funcs[a₂]? = some fi₂)
    (he₁ : Expand fi₁.type (ps₁.func rs₁)) (he₂ : Expand fi₂.type (ps₂.func rs₂))
    (hn₁ : vs₁.length = ps₁.length) (hn₂ : vs₂.length = ps₂.length)
    (hcode₁ : fi₁.code = .wasm code₁) (hcode₂ : fi₂.code = .wasm code₂) :
    p = [] ∧ Join (SoftPair P c)
      ⟨s, f, [.frame rs₁.length (Frame.forCall fi₁.module vs₁ code₁.locals)
        [.label rs₁.length [] (expression code₁.body)]]⟩
      ⟨s, f, [.frame rs₂.length (Frame.forCall fi₂.module vs₂ code₂.locals)
        [.label rs₂.length [] (expression code₂.body)]]⟩ := by
  have ha' : p ++ vs₂ ++ [Val.ref (.func a₂)] = vs₁ ++ [Val.ref (.func a₁)] := by
    rw [List.append_assoc]; exact ha
  have hsplit : p ++ vs₂ = vs₁ ∧ Val.ref (.func a₂) = Val.ref (.func a₁) :=
    append_singleton_inj.mp ha'
  have haeq : a₂ = a₁ := by simpa using hsplit.2
  have hf₂' : s.funcs[a₁]? = some fi₂ := haeq ▸ hf₂
  have hfi : fi₁ = fi₂ := Option.some.inj (hf₁.symm.trans hf₂')
  have he₂' : Expand fi₁.type (ps₂.func rs₂) := hfi ▸ he₂
  have hps : ps₁ = ps₂ ∧ rs₁ = rs₂ := by simpa using Expand.det he₁ he₂'
  have hcode₂' : fi₁.code = .wasm code₂ := hfi ▸ hcode₂
  have hcode : code₁ = code₂ := FuncCode.wasm.inj (hcode₁.symm.trans hcode₂')
  have hlen : p.length + vs₂.length = vs₂.length := by
    rw [← List.length_append, hsplit.1, hn₁, hn₂, hps.1]
  have hp0 : p = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hvs : vs₁ = vs₂ := by rw [← hsplit.1, hp0, List.nil_append]
  exact Head.ctlArm_close hp0 (by rw [hvs, hfi, hps.2, hcode])

/-- Run `tac` on every goal whose case tag matches one of `tags` as `case` matches it (equal,
or the listed tag is a suffix or a prefix of the goal's: `callRefNull.callRefFunc` also selects
`callRefNull.callRefFunc.inl`); each of those goals must be closed by it. A tag with no goal is
skipped, so one script serves every shape of instruction below (`case` fails on it instead). -/
syntax (name := onGoals) "on_goals " "[" ident,* "] " tactic : tactic

open Lean Elab Tactic in
@[tactic onGoals] meta def evalOnGoals : Tactic := fun stx => do
  let tags := stx[2].getSepArgs.map (·.getId)
  let mut rest : Array MVarId := #[]
  for g in ← getGoals do
    if ← g.isAssigned then continue
    let tag ← g.getTag
    if tags.any (fun t => t == tag || t.isSuffixOf tag || t.isPrefixOf tag) then
      setGoals [g]
      evalTactic stx[4]
      unless (← getUnsolvedGoals).isEmpty do
        throwError "on_goals: the tactic did not close the goal tagged {tag}"
    else
      rest := rest.push g
  setGoals rest.toList

/-- The statement of `Head.det_ctl_soft` at one instruction `e`. -/
def DetCtlSoft (P : Profile) (s : Store H) (f : Frame) (e : Admin) : Prop :=
  ∀ {args₁ args₂ p : List Val} {c₁ c₂ : Config H}, famOf e = .control →
    (∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e → Step P noHost ⟨s, f, body⟩ c₁ → Step P noHost ⟨s, f, body⟩ c₂ →
      SoftJoin P ⟨s, f, body⟩ c₁ c₂) →
    Head P s f args₁ e c₁ → Head P s f args₂ e c₂ → args₁ = p ++ args₂ →
    p = [] ∧ Join (SoftPair P ⟨s, f, vals args₂ ++ [e]⟩) c₁ c₂

set_option hygiene false in
/-- The proof of `DetCtlSoft` at one shape of instruction: silmaril-lean's `Det.Head.det_ctl` for
an arbitrary profile, with the joinability relation `SoftPair`, each pair of rules sent to the
closer that closes it (see the module documentation). Unhygienic: the arms refer to the
hypotheses by name (`hp`, `hc`, and `hvn` of `vn_all`). -/
macro "det_ctl_soft_tac" : tactic => `(tactic| (
  intro args₁ args₂ p c₁ c₂ hk ih h₁ h₂ hp
  have hc {k : Fam} (h : _ = k) (hk' : k ≠ .control) : False := hk' (h.symm.trans hk)
  cases h₁
  fam_close
  all_goals cases h₂
  fam_close
  -- `hd_close` closes every pair of rules but those listed, which the per-rule closers below
  -- close (it fails on them only after trying all its alternatives, so they are skipped)
  all_goals_except [ctxtLabel.ctxtLabel, ctxtLabel.brLabelZero, ctxtLabel.brLabelSucc,
      ctxtLabel.returnCallRefLabel, ctxtLabel.returnLabel, ctxtHandler.ctxtHandler,
      ctxtHandler.brHandler, ctxtHandler.returnCallRefHandler, ctxtHandler.returnHandler,
      ctxtFrame.ctxtFrame, ctxtFrame.returnCallRefFrameNull, ctxtFrame.returnCallRefFrameAddr,
      ctxtFrame.returnFrame, block.block, loop.loop, ifTrue.ifTrue, ifTrue.ifFalse, ifFalse.ifTrue,
      labelVals.labelVals, brLabelZero.ctxtLabel, brLabelZero.brLabelZero, brLabelZero.brLabelSucc,
      brLabelZero.returnCallRefLabel, brLabelSucc.ctxtLabel, brLabelSucc.brLabelZero,
      brLabelSucc.brLabelSucc, brLabelSucc.returnCallRefLabel, brHandler.ctxtHandler,
      brHandler.brHandler, brHandler.returnCallRefHandler, brIfTrue.brIfTrue, brIfTrue.brIfFalse,
      brIfFalse.brIfTrue, brTableLt.brTableLt, brTableLt.brTableGe, brTableGe.brTableLt,
      brTableGe.brTableGe, brOnNullNull.brOnNullAddr, brOnNullAddr.brOnNullNull,
      brOnNullAddr.brOnNullAddr, brOnNonNullNull.brOnNonNullAddr, brOnNonNullAddr.brOnNonNullNull,
      brOnNonNullAddr.brOnNonNullAddr, brOnCastSucceed.brOnCastSucceed,
      brOnCastSucceed.brOnCastFail, brOnCastFail.brOnCastSucceed, brOnCastFail.brOnCastFail,
      brOnCastFailSucceed.brOnCastFailSucceed, brOnCastFailSucceed.brOnCastFailFail,
      brOnCastFailFail.brOnCastFailSucceed, brOnCastFailFail.brOnCastFailFail, call.call,
      callRefNull.callRefFunc, callRefFunc.callRefFunc, returnCall.returnCall,
      returnCallRefLabel.ctxtLabel, returnCallRefLabel.brLabelZero, returnCallRefLabel.brLabelSucc,
      returnCallRefLabel.returnCallRefLabel, returnCallRefLabel.returnLabel,
      returnCallRefLabel.throwRefLabel, returnCallRefLabel.trapLabel,
      returnCallRefHandler.ctxtHandler, returnCallRefHandler.brHandler,
      returnCallRefHandler.returnCallRefHandler, returnCallRefHandler.returnHandler,
      returnCallRefHandler.throwRefHandlerEmpty, returnCallRefHandler.throwRefHandlerCatch,
      returnCallRefHandler.throwRefHandlerCatchRef, returnCallRefHandler.throwRefHandlerCatchAll,
      returnCallRefHandler.throwRefHandlerCatchAllRef, returnCallRefHandler.throwRefHandlerNext,
      returnCallRefHandler.trapHandler, returnCallRefFrameNull.ctxtFrame,
      returnCallRefFrameNull.returnCallRefFrameAddr, returnCallRefFrameNull.returnFrame,
      returnCallRefFrameNull.throwRefFrame, returnCallRefFrameAddr.ctxtFrame,
      returnCallRefFrameAddr.returnCallRefFrameNull, returnCallRefFrameAddr.returnCallRefFrameAddr,
      returnCallRefFrameAddr.returnFrame, returnCallRefFrameAddr.throwRefFrame,
      frameVals.frameVals, returnFrame.ctxtFrame, returnFrame.returnCallRefFrameNull,
      returnFrame.returnCallRefFrameAddr, returnFrame.returnFrame, returnLabel.ctxtLabel,
      returnLabel.returnCallRefLabel, returnLabel.returnLabel, returnHandler.ctxtHandler,
      returnHandler.returnCallRefHandler, returnHandler.returnHandler, throw.throw,
      throwRefLabel.returnCallRefLabel, throwRefFrame.returnCallRefFrameNull,
      throwRefFrame.returnCallRefFrameAddr, throwRefHandlerEmpty.returnCallRefHandler,
      throwRefHandlerCatch.returnCallRefHandler, throwRefHandlerCatch.throwRefHandlerCatch,
      throwRefHandlerCatch.throwRefHandlerNext, throwRefHandlerCatchRef.returnCallRefHandler,
      throwRefHandlerCatchRef.throwRefHandlerCatchRef, throwRefHandlerCatchRef.throwRefHandlerNext,
      throwRefHandlerCatchAll.returnCallRefHandler, throwRefHandlerCatchAll.throwRefHandlerNext,
      throwRefHandlerCatchAllRef.returnCallRefHandler,
      throwRefHandlerCatchAllRef.throwRefHandlerNext, throwRefHandlerNext.returnCallRefHandler,
      throwRefHandlerNext.throwRefHandlerCatch, throwRefHandlerNext.throwRefHandlerCatchRef,
      throwRefHandlerNext.throwRefHandlerCatchAll, throwRefHandlerNext.throwRefHandlerCatchAllRef,
      tryTable.tryTable, handlerVals.handlerVals, trapLabel.returnCallRefLabel,
      trapHandler.returnCallRefHandler] hd_close
  on_goals [ctxtLabel.ctxtLabel] exact ctxt_label_soft ih ‹_› ‹_› hp
  on_goals [ctxtHandler.ctxtHandler] exact ctxt_handler_soft ih ‹_› ‹_› hp
  on_goals [ctxtFrame.ctxtFrame] exact ctxt_frame_soft ih ‹_› ‹_› hp
  all_goals (clear ih hc hk; vn_all; subst_vars)
  all_goals (repeat' rcr_step)
  -- `det_ctl` tries silmaril-lean's closers in turn on every goal (`ctl_single`, `ctl_step`,
  -- `ctl_body`, `ctl_same`, `ctl_vals`, `ctl_catch`); here each pair goes to the first closer that
  -- applies to it, and the pairs left after the per-rule arms below go to `ctl_body`
  on_goals [ifTrue.ifTrue, ifTrue.ifFalse, ifFalse.ifTrue, brIfTrue.brIfTrue, brIfTrue.brIfFalse,
      brIfFalse.brIfTrue, brTableLt.brTableGe, brTableGe.brTableLt, brTableGe.brTableGe,
      brOnNullNull.brOnNullAddr, brOnNullAddr.brOnNullNull, brOnNullAddr.brOnNullAddr,
      brOnNonNullNull.brOnNonNullAddr, brOnNonNullAddr.brOnNonNullNull,
      brOnNonNullAddr.brOnNonNullAddr, brOnCastSucceed.brOnCastSucceed,
      brOnCastSucceed.brOnCastFail, brOnCastFail.brOnCastSucceed, brOnCastFail.brOnCastFail,
      brOnCastFailSucceed.brOnCastFailSucceed, brOnCastFailSucceed.brOnCastFailFail,
      brOnCastFailFail.brOnCastFailSucceed, brOnCastFailFail.brOnCastFailFail] ctl_single
  on_goals [ctxtLabel.brLabelZero, ctxtLabel.brLabelSucc, ctxtLabel.returnCallRefLabel.inl,
      ctxtLabel.returnCallRefLabel.inr, ctxtLabel.returnLabel, ctxtHandler.brHandler,
      ctxtHandler.returnCallRefHandler.inl, ctxtHandler.returnCallRefHandler.inr,
      ctxtHandler.returnHandler, ctxtFrame.returnCallRefFrameNull.inl,
      ctxtFrame.returnCallRefFrameNull.inr, ctxtFrame.returnCallRefFrameAddr.inl,
      ctxtFrame.returnCallRefFrameAddr.inr, ctxtFrame.returnFrame, brLabelZero.ctxtLabel,
      brLabelSucc.ctxtLabel, brHandler.ctxtHandler, returnCallRefLabel.ctxtLabel.inl,
      returnCallRefLabel.ctxtLabel.inr, returnCallRefHandler.ctxtHandler.inl,
      returnCallRefHandler.ctxtHandler.inr, returnCallRefFrameNull.ctxtFrame.inl,
      returnCallRefFrameNull.ctxtFrame.inr, returnCallRefFrameAddr.ctxtFrame.inl,
      returnCallRefFrameAddr.ctxtFrame.inr, returnFrame.ctxtFrame, returnLabel.ctxtLabel,
      returnHandler.ctxtHandler] ctl_step
  on_goals [brLabelZero.brLabelSucc, brLabelSucc.brLabelZero, brLabelSucc.brLabelSucc,
      brHandler.brHandler, returnCallRefLabel.returnCallRefLabel.inl.inl,
      returnCallRefLabel.returnCallRefLabel.inr.inr,
      returnCallRefHandler.returnCallRefHandler.inl.inl,
      returnCallRefHandler.returnCallRefHandler.inr.inr, returnLabel.returnLabel,
      returnHandler.returnHandler] ctl_same
  on_goals [labelVals.labelVals, frameVals.frameVals, handlerVals.handlerVals] ctl_vals
  on_goals [throwRefHandlerCatch.throwRefHandlerNext, throwRefHandlerCatchRef.throwRefHandlerNext,
      throwRefHandlerCatchAll.throwRefHandlerNext, throwRefHandlerCatchAllRef.throwRefHandlerNext,
      throwRefHandlerNext.throwRefHandlerCatch, throwRefHandlerNext.throwRefHandlerCatchRef,
      throwRefHandlerNext.throwRefHandlerCatchAll,
      throwRefHandlerNext.throwRefHandlerCatchAllRef] ctl_catch
  on_goals [block.block, loop.loop, tryTable.tryTable] ctl_block
  on_goals [throw.throw]
    (rename_i _ _ _ he₁ ht₁ _ _ _ he₂ hn₂ ht₂ hn₁
     exact Head.ctlArm_throw ht₁ ht₂ he₁ he₂ hn₁ hn₂)
  on_goals [call.call]
    (rename_i _ _ hf₁ hx₁ _ _ hf₂ hx₂
     exact Head.ctlArm_call Admin.callRefType hp hx₁ hx₂ hf₁ hf₂)
  on_goals [returnCall.returnCall]
    (rename_i _ _ hf₁ hx₁ _ _ hf₂ hx₂
     exact Head.ctlArm_call Admin.returnCallRefType hp hx₁ hx₂ hf₁ hf₂)
  on_goals [throwRefHandlerCatch.throwRefHandlerCatch, throwRefHandlerCatchRef.throwRefHandlerCatchRef]
    (rename_i _ he₁ _ _ _ he₂
     exact Head.ctlArm_catch (fun e => vals e.fields ++ _) hp he₁ he₂)
  on_goals [brTableLt.brTableLt]
    (rename_i _ _ _ _ hi₁ _ _ hi₂
     exact Head.ctlArm_brTableLt hp hi₁ hi₂)
  on_goals [brLabelZero.brLabelZero] (rename_i hn hb; exact Head.ctlArm_brLabelZero hp hn hb)
  on_goals [returnFrame.returnFrame] (rename_i hn hb; exact Head.ctlArm_returnFrame hp hn hb)
  on_goals [returnCallRefFrameAddr.returnCallRefFrameAddr.inl.inl,
      returnCallRefFrameAddr.returnCallRefFrameAddr.inr.inr]
    (rename_i _ _ _ _ _ _ _ hf₁ he₁ hn₁ _ _ _ _ _ _ _ hf₂ he₂ hn₂ _ hvn₁ _ hb
     exact Head.ctlArm_rcrAddr hp hvn₁ hvn hf₁ hf₂ he₁ he₂ hn₁ hn₂ hb)
  on_goals [returnCallRefFrameAddr.returnCallRefFrameNull.inl.inl,
      returnCallRefFrameAddr.returnCallRefFrameNull.inr.inr]
    (rename_i _ hvn₁ _ hb; exact (Head.ctlArm_rcrAddrNull hvn₁ hvn hb).elim)
  on_goals [returnCallRefFrameNull.returnCallRefFrameAddr.inl.inl,
      returnCallRefFrameNull.returnCallRefFrameAddr.inr.inr]
    (rename_i _ hvn₁ _ hb; exact (Head.ctlArm_rcrAddrNull hvn hvn₁ hb.symm).elim)
  on_goals [callRefNull.callRefFunc]
    exact (Head.ctlArm_callRefNull hp).elim
  on_goals [callRefFunc.callRefFunc]
    exact Head.ctlArm_callRefFunc ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
  all_goals ctl_body))

/-! One lemma per shape of the instruction `e`, so that Lean elaborates them in parallel (the
case split on the second rule only meets rules of the same shape). -/

theorem Head.det_ctl_soft_plain (i : Instr) : DetCtlSoft P s f (.plain i) := by
  det_ctl_soft_tac

theorem Head.det_ctl_soft_ref (r : Ref) : DetCtlSoft P s f (.ref r) := by
  det_ctl_soft_tac

theorem Head.det_ctl_soft_callRefType (d : DefType) : DetCtlSoft P s f (.callRefType d) := by
  det_ctl_soft_tac

theorem Head.det_ctl_soft_returnCallRefType (d : DefType) :
    DetCtlSoft P s f (.returnCallRefType d) := by
  det_ctl_soft_tac

theorem Head.det_ctl_soft_label (n : Nat) (cont : List Instr) (body : List Admin) :
    DetCtlSoft P s f (.label n cont body) := by
  det_ctl_soft_tac

theorem Head.det_ctl_soft_handler (n : Nat) (cs : List Catch) (body : List Admin) :
    DetCtlSoft P s f (.handler n cs body) := by
  det_ctl_soft_tac

theorem Head.det_ctl_soft_frame (n : Nat) (fi : Frame) (body : List Admin) :
    DetCtlSoft P s f (.frame n fi body) := by
  det_ctl_soft_tac

theorem Head.det_ctl_soft_trap : DetCtlSoft P s f .trap := by
  det_ctl_soft_tac

/-- Two control head steps at the same instruction consume the same arguments, and their
results are equal or both `Soft` (the latter only under a context rule). The proof is
silmaril-lean's `Det.Head.det_ctl` for an arbitrary profile, with the joinability relation
`SoftPair`, split on the shape of `e` (`Head.det_ctl_soft_plain`, …). -/
theorem Head.det_ctl_soft {P : Profile} {s : Store H} {f : Frame}
    {args₁ args₂ p : List Val} {e : Admin} {c₁ c₂ : Config H} (hk : famOf e = .control)
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e → Step P noHost ⟨s, f, body⟩ c₁ → Step P noHost ⟨s, f, body⟩ c₂ →
      SoftJoin P ⟨s, f, body⟩ c₁ c₂)
    (h₁ : Head P s f args₁ e c₁) (h₂ : Head P s f args₂ e c₂) (hp : args₁ = p ++ args₂) :
    p = [] ∧ Join (SoftPair P ⟨s, f, vals args₂ ++ [e]⟩) c₁ c₂ := by
  have key : DetCtlSoft P s f e := by
    cases e with
    | plain i => exact Head.det_ctl_soft_plain i
    | ref r => exact Head.det_ctl_soft_ref r
    | callRefType d => exact Head.det_ctl_soft_callRefType d
    | returnCallRefType d => exact Head.det_ctl_soft_returnCallRefType d
    | label n cont body => exact Head.det_ctl_soft_label n cont body
    | handler n cs body => exact Head.det_ctl_soft_handler n cs body
    | frame n fi body => exact Head.det_ctl_soft_frame n fi body
    | trap => exact Head.det_ctl_soft_trap
  exact key hk ih h₁ h₂ hp

end Silmaril.Proofs.Wasm.Game.Choice
