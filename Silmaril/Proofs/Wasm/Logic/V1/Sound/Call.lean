module

public import Silmaril.Wasm.Logic.V1.Judgement.Defs

/-!
# Soundness of the function-call proof rules

Figure 11 of Watt et al. The `[call]` rule simply reads off an assumed
specification; all the work is in `valid_funcRule`, which discharges the
`[function]` rule: the arguments move from the operand stack into the leading
local variables, the declared locals are zeroed, and the body is verified with
the labels field and the return field both set to the function's postcondition,
because `(br 0)` at the top of a body and `return` anywhere both terminate it.

`ModuleSpecs` is the paper's `[module]` rule, following the strategy of Oheimb
and Nipkow for mutual recursion: every body is verified assuming every
specification, and the assumptions are then discharged by recursion on the
derivation height.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.V1

open Silmaril.Wasm hiding BlockType ConvertOp Data Elem Export Expr ExternIdx ExternType Func FuncType Global GlobalType Import Instr IntUnOp Limits MemArg MemoryType Module PackSize ResultType TableType ValType
open Silmaril.Wasm.V1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.V1.Execution

variable {H : Type*} {host : HostSemantics H} {n : Nat} {F : List FuncDef}
variable {L : List Assert} {R : Option Assert} {P Q : Assert}

/-! ## The frame's module instance is invariant -/

/-- A non-control instruction never changes the frame's module instance. -/
private theorem plain_module {s s' : Store H} {f f' : Frame} {args rets : List Value}
    {i : Silmaril.Wasm.V1.Instr} (step : Plain s f args i s' f' rets) : f'.module = f.module := by
  cases step <;> rfl

/-- Execution never changes the frame's module instance: a `frame` instruction
restores the caller's frame, and nothing else touches `Frame.module`. -/
private theorem bigStepN_module {m : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {es : List Admin} {o : Outcome H} (run : BigStepN host m s f vs es o) :
    o.frame.module = f.module := by
  induction run
  all_goals
    first
      | rfl
      | assumption
      | (rename_i ih₁ ih₂; exact ih₂.trans ih₁)
      | (rename_i step _ ih; exact ih.trans (plain_module step))

/-- `bigStepN_module` with the final outcome spelled out. -/
private theorem bigStepN_module' {m : Nat} {s s' : Store H} {f f' : Frame} {vs : List Value}
    {es : List Admin} {r : BigResult} (run : BigStepN host m s f vs es ⟨s', f', r⟩) :
    f'.module = f.module :=
  bigStepN_module run

/-! ## Moving between the caller's and the callee's abstract store -/

/-- `ρ` with its local variables read off a list of values. -/
private def withLocals (ρ : Sto) (ls : List Value) : Sto := fun x =>
  match x with
  | .loc j => (ls[j]?).getD (ρ (.loc j))
  | _ => ρ x

/-- `ρ` with its local variables taken from `ρ₁`. -/
private def swapLocals (ρ ρ₁ : Sto) : Sto := fun x =>
  match x with
  | .loc j => ρ₁ (.loc j)
  | _ => ρ x

private theorem withLocals_eq (ρ : Sto) (ls : List Value) {x : Var} (hx : x ∉ localVars) :
    withLocals ρ ls x = ρ x := by
  cases x with
  | log j => rfl
  | loc j => exact absurd (show Var.loc j ∈ localVars from ⟨j, rfl⟩) hx
  | glob j => rfl

private theorem swapLocals_eq (ρ ρ₁ : Sto) {x : Var} (hx : x ∉ localVars) :
    swapLocals ρ ρ₁ x = ρ x := by
  cases x with
  | log j => rfl
  | loc j => exact absurd (show Var.loc j ∈ localVars from ⟨j, rfl⟩) hx
  | glob j => rfl

private theorem not_mem_localVars_of_not_program {x : Var} (hx : ¬ x.IsProgram) :
    x ∉ localVars := by
  cases x with
  | log j => rintro ⟨k, hk⟩; exact Var.noConfusion hk
  | loc j => exact absurd trivial hx
  | glob j => exact absurd trivial hx

private theorem withLocals_glob (ρ : Sto) (ls : List Value) (j : Nat) :
    withLocals ρ ls (.glob j) = ρ (.glob j) := rfl

private theorem swapLocals_glob (ρ ρ₁ : Sto) (j : Nat) :
    swapLocals ρ ρ₁ (.glob j) = ρ (.glob j) := rfl

private theorem swapLocals_loc (ρ ρ₁ : Sto) (j : Nat) :
    swapLocals ρ ρ₁ (.loc j) = ρ₁ (.loc j) := rfl

private theorem reifiesLocals_withLocals (ρ : Sto) (ls : List Value) :
    ReifiesLocals ls (withLocals ρ ls) := by
  intro i v hv
  show (ls[i]?).getD _ = v
  rw [hv]
  rfl

private theorem reifiesLocals_swapLocals {ρ ρ₁ : Sto} {ls : List Value}
    (h : ReifiesLocals ls ρ₁) : ReifiesLocals ls (swapLocals ρ ρ₁) := fun i v hv => h i v hv

/-! ## The function-call rules -/

/-- The `[call]` rule. -/
theorem valid_call {A : FuncSpecs} (i : FuncIdx) (specs : ValidSpecs host n F A)
    (assumed : A i P Q) (bound : i.toNat < F.length) :
    Valid host n F L R P [.call i] Q := by
  have _ := bound
  have hv : Valid host n F [] none P [.call i] Q := specs i P Q assumed
  intro s f ρ vs vf h hf o pre disj reify run
  obtain ⟨h', ρ', disj', reify', agree, sat⟩ := hv s f ρ vs vf h hf o pre disj reify run
  refine ⟨h', ρ', disj', reify', agree, ?_⟩
  revert sat
  cases o.result with
  | normal ws => exact fun hh => hh
  | br l ws =>
    intro sat
    simp only [Satisfies] at sat
    obtain ⟨P', -, -, hp, -, -⟩ := sat
    simp at hp
  | ret ws =>
    intro sat
    simp only [Satisfies] at sat
    obtain ⟨R', -, -, hr, -, -⟩ := sat
    simp at hr
  | trap => intro sat; exact sat.elim

/-! ## Transporting reification along a change of module instance or store -/

private theorem reifiesFuncs_cast {s : Store H} {md md' : ModuleInst} (hm : md = md')
    (r : ReifiesFuncs F s md) : ReifiesFuncs F s md' := hm ▸ r

private theorem reifiesMem_cast {s : Store H} {md md' : ModuleInst} {hp : AHeap} (hm : md = md')
    (r : ReifiesMem s md hp) : ReifiesMem s md' hp := hm ▸ r

private theorem reifiesGlobals_cast {s : Store H} {md md' : ModuleInst} {ρ ρ' : Sto}
    (hm : md = md') (hg : ∀ j, ρ' (.glob j) = ρ (.glob j)) (r : ReifiesGlobals s md ρ) :
    ReifiesGlobals s md' ρ' :=
  ⟨hm ▸ r.nodup, fun j b g hb hg' =>
    (hg j).trans ((hm ▸ r : ReifiesGlobals s md' ρ).agree j b g hb hg')⟩

/-! ## Little list lemmas -/

/-- Generalise the operand stack of an execution, so that `cases` is not asked
to solve an equation between two appends. -/
private theorem stack_gen {m : Nat} {s : Store H} {f : Frame} {vs : List Value}
    {es : List Admin} {o : Outcome H} (run : BigStepN host m s f vs es o) :
    ∃ v₀, v₀ = vs ∧ BigStepN host m s f v₀ es o := ⟨vs, rfl, run⟩

/-- A branch or return discards an arbitrary prefix of the operand stack, but
the arity checked at the label or frame it lands on and the fixed stack length
of the assertion pin the transferred values down: two suffixes of the same list
with the same length are equal. -/
private theorem eq_of_append_eq {α : Type*} {a b c d : List α} (hab : a ++ b = c ++ d)
    (hlen : b.length = d.length) : b = d := (List.append_inj' hab hlen).2

/-! ## The `[function]` rule -/

/-- A body that fell off the end. -/
private theorem body_exit_normal {ρ : Sto} {h : AHeap} {ws : List Value}
    (sat : Satisfies [Q] (some Q) Q ρ [] h (.normal ws)) : Q ρ ws h := by
  obtain ⟨ws', hws, hq⟩ := sat
  have hws' : ws' = ws := by simpa using hws.symm
  exact hws' ▸ hq

/-- A body that branched to its own label, which hands back `m` values. -/
private theorem body_exit_br {m : Nat} {ρ : Sto} {h : AHeap} {l : LabelIdx}
    {extra ws : List Value} (post : Assert.StackLen Q m) (target : l.toNat = 0)
    (arity : ws.length = m) (sat : Satisfies [Q] (some Q) Q ρ [] h (.br l (extra ++ ws))) :
    Q ρ ws h := by
  obtain ⟨P', pre₀, ws', hp, hws, hq⟩ := sat
  obtain rfl : Q = P' := by
    simpa only [target, List.getElem?_cons_zero, Option.some.injEq] using hp
  obtain rfl : ws = ws' := eq_of_append_eq hws (arity.trans (post _ _ _ hq).symm)
  exact hq

/-- A body cannot branch past its own label. -/
private theorem body_exit_brSucc {ρ : Sto} {h : AHeap} {l : LabelIdx} {ws : List Value}
    (outer : l.toNat ≠ 0) (sat : Satisfies [Q] (some Q) Q ρ [] h (.br l ws)) : False := by
  obtain ⟨P', -, -, hp, -, -⟩ := sat
  obtain ⟨c, hc⟩ : ∃ c, l.toNat = c + 1 := ⟨l.toNat - 1, by omega⟩
  have hp' : ([Q] : List Assert)[c + 1]? = some P' := hc ▸ hp
  exact absurd hp' (by simp)

/-- A body that returned: the return value is on top of an arbitrary prefix. -/
private theorem body_exit_ret {ρ : Sto} {h : AHeap} {ws : List Value}
    (sat : Satisfies [Q] (some Q) Q ρ [] h (.ret ws)) :
    ∃ pre ws', ws = pre ++ ws' ∧ Q ρ ws' h := by
  obtain ⟨R', pre₁, ws', hr, hws, hq⟩ := sat
  obtain rfl : Q = R' := Option.some.inj hr
  exact ⟨pre₁, ws', hws, hq⟩

/-- The body of a function, wrapped in the label that `invoke` pushes around it:
whichever way the body ends — falling off the end, branching to label `0`, or
returning — the function's postcondition holds of the values the label hands
back. Falling off the end or branching to label `0` hands those values back on
their own, the label's arity having discarded everything below them; a return
escapes the label untouched, so it hands them back under an arbitrary prefix,
which the arity check at `BigStepN.frameRet` discards in turn. -/
private theorem funcBody_sound {k m : Nat} {s : Store H} {fr : Frame} {ρ₀ : Sto}
    {h hf : AHeap} {P₀ : Assert} {e : Silmaril.Wasm.V1.Expr} {ol : Outcome H}
    (post : Assert.StackLen Q m)
    (valid : ∀ j, j < k → Valid host j F [Q] (some Q) P₀ e Q)
    (pre : P₀ ρ₀ [] h) (disj : AHeap.Disj h hf) (reify : Reifies F s fr ρ₀ (h ∪ hf))
    (run : BigStepN host k s fr [] [.label m [] (expression e)] ol) :
    ∃ h' ρ' ws, AHeap.Disj h' hf ∧ Reifies F ol.store ol.frame ρ' (h' ∪ hf) ∧
      ol.frame.module = fr.module ∧ (∀ x, ¬ x.IsProgram → ρ' x = ρ₀ x) ∧ Q ρ' ws h' ∧
      (ol.result = .normal ws ∨ ∃ pre, ol.result = .ret (pre ++ ws)) := by
  obtain ⟨v₀, hv₀, run'⟩ := stack_gen run
  cases run' with
  | labelNormal inner rest =>
    obtain ⟨h', ρ', disj', reify', agree', sat⟩ :=
      valid _ (Nat.lt_succ_self _) s fr ρ₀ [] [] h hf _ pre disj reify inner
    obtain rfl : ol = ⟨_, _, .normal (v₀ ++ _)⟩ := rest.nil_inv
    exact ⟨h', ρ', _, disj', reify', bigStepN_module' inner, Sto.not_isProgram_of_agree agree',
      body_exit_normal sat, Or.inl (by simp [hv₀])⟩
  | labelBrZero inner target arity rest =>
    obtain ⟨h', ρ', disj', reify', agree', sat⟩ :=
      valid _ (Nat.lt_succ_self _) s fr ρ₀ [] [] h hf _ pre disj reify inner
    obtain rfl : ol = ⟨_, _, .normal (v₀ ++ _)⟩ := rest.nil_inv
    exact ⟨h', ρ', _, disj', reify', bigStepN_module' inner, Sto.not_isProgram_of_agree agree',
      body_exit_br post target arity sat, Or.inl (by simp [hv₀])⟩
  | labelBrSucc inner outer =>
    obtain ⟨_, _, _, _, _, sat⟩ :=
      valid _ (Nat.lt_succ_self _) s fr ρ₀ [] [] h hf _ pre disj reify inner
    exact (body_exit_brSucc outer sat).elim
  | labelRet inner =>
    obtain ⟨h', ρ', disj', reify', agree', sat⟩ :=
      valid _ (Nat.lt_succ_self _) s fr ρ₀ [] [] h hf _ pre disj reify inner
    obtain ⟨pre₁, ws', hws, hq⟩ := body_exit_ret sat
    exact ⟨h', ρ', ws', disj', reify', bigStepN_module' inner, Sto.not_isProgram_of_agree agree',
      hq, Or.inr ⟨pre₁, by simp [hv₀, hws]⟩⟩
  | labelTrap inner =>
    obtain ⟨_, _, _, _, _, sat⟩ :=
      valid _ (Nat.lt_succ_self _) s fr ρ₀ [] [] h hf _ pre disj reify inner
    exact (sat : False).elim

/-- After the call, the caller's local variables are back; everything else is the
callee's, and the callee did not touch the caller's logical variables. -/
private theorem agree_call {i : FuncIdx} {ρ ρ' : Sto} {ls : List Value}
    (agree' : ∀ x, ¬ x.IsProgram → ρ' x = withLocals ρ ls x) :
    ∀ x, x ∉ Expr.modified [Silmaril.Wasm.V1.Instr.call i] → swapLocals ρ' ρ x = ρ x := by
  intro x hx
  cases x with
  | loc j => exact swapLocals_loc ρ' ρ j
  | glob j =>
    exact absurd (show Var.glob j ∈ Instr.modified (Silmaril.Wasm.V1.Instr.call i) from ⟨j, rfl⟩)
      (by simpa using hx)
  | log j =>
    have hlog : (Var.log j) ∉ localVars := by rintro ⟨k, hk⟩; exact Var.noConfusion hk
    rw [show swapLocals ρ' ρ (Var.log j) = ρ' (Var.log j) from rfl,
      agree' (Var.log j) (fun h => h), withLocals_eq ρ _ hlog]

/-- The caller's view of a call that returned `ws`: the abstract store swaps the
callee's local variables back for the caller's. -/
private theorem funcRule_finish {i : FuncIdx} {s' : Store H} {f fr' : Frame} {ρ ρ' : Sto}
    {h' hf : AHeap} {vf ws ls : List Value} (locals : ReifiesLocals f.locals ρ)
    (reify' : Reifies F s' fr' ρ' (h' ∪ hf)) (hmod : fr'.module = f.module)
    (agree' : ∀ x, ¬ x.IsProgram → ρ' x = withLocals ρ ls x)
    (postLocals : Assert.Indep localVars Q) (hq : Q ρ' ws h') (disj' : AHeap.Disj h' hf) :
    ∃ h'' ρ'', AHeap.Disj h'' hf ∧ Reifies F s' f ρ'' (h'' ∪ hf) ∧
      (∀ x, x ∉ Expr.modified [Silmaril.Wasm.V1.Instr.call i] → ρ'' x = ρ x) ∧
      Satisfies [] none Q ρ'' vf h'' (.normal (vf ++ ws)) :=
  ⟨h', swapLocals ρ' ρ, disj',
    ⟨reifiesFuncs_cast hmod reify'.funcs, reifiesLocals_swapLocals locals,
      reifiesGlobals_cast hmod (fun j => swapLocals_glob ρ' ρ j) reify'.globals,
      reifiesMem_cast hmod reify'.mem⟩, agree_call agree',
    ⟨_, rfl, (postLocals ρ' _ _ h' (fun _ hx => (swapLocals_eq ρ' ρ hx).symm)).mp hq⟩⟩

/-- The callee's frame, entered: the arguments are the leading locals and the
declared locals are zero. -/
private theorem enter_sound {s : Store H} {f : Frame} {ρ : Sto} {vs : List Value} {h hf : AHeap}
    {d : FuncDef} (pre : Assert.StackLen P d.type.params.length)
    (preLocals : Assert.Indep localVars P) (hP : P ρ vs h) (reify : Reifies F s f ρ (h ∪ hf)) :
    enterFunc d P (withLocals ρ (vs ++ d.locals.map Value.zero)) [] h ∧
      Reifies F s ⟨vs ++ d.locals.map Value.zero, f.module⟩
        (withLocals ρ (vs ++ d.locals.map Value.zero)) (h ∪ hf) :=
  ⟨⟨rfl, vs, pre ρ vs h hP,
      (preLocals ρ _ vs h (fun _ hx => (withLocals_eq ρ _ hx).symm)).mp hP,
      reifiesLocals_withLocals _ _⟩,
    ⟨reify.funcs, reifiesLocals_withLocals _ _,
      reifiesGlobals_cast rfl (fun j => withLocals_glob ρ _ j) reify.globals, reify.mem⟩⟩

/-- The frame of a call of a verified function, seen from the caller. -/
private theorem frame_sound {k : Nat} {s : Store H} {f : Frame} {ρ : Sto} {vs vf : List Value}
    {h hf : AHeap} {d : FuncDef} {i : FuncIdx} {o : Outcome H}
    (pre : Assert.StackLen P d.type.params.length)
    (post : Assert.StackLen Q d.type.results.length)
    (preLocals : Assert.Indep localVars P) (postLocals : Assert.Indep localVars Q)
    (body : ∀ j < k, Valid host j F [Q] (some Q) (enterFunc d P) d.body Q)
    (hP : P ρ vs h) (disj : AHeap.Disj h hf) (reify : Reifies F s f ρ (h ∪ hf))
    (run : BigStepN host k s f vf [.frame d.type.results.length
      ⟨vs ++ d.locals.map Value.zero, f.module⟩
      [.label d.type.results.length [] (expression d.body)]] o) :
    ∃ h' ρ', AHeap.Disj h' hf ∧ Reifies F o.store o.frame ρ' (h' ∪ hf) ∧
      (∀ x, x ∉ Expr.modified [Silmaril.Wasm.V1.Instr.call i] → ρ' x = ρ x) ∧
      Satisfies [] none Q ρ' vf h' o.result := by
  obtain ⟨hpre₀, hreify₀⟩ := enter_sound pre preLocals hP reify
  cases run with
  | frameTrap inner =>
    obtain ⟨_, _, _, _, _, _, _, _, hres⟩ :=
      funcBody_sound post (fun j hj => body j (by omega)) hpre₀ disj hreify₀ inner
    exact absurd hres (by simp)
  | frameNormal inner arity rest =>
    obtain ⟨h', ρ', ws', disj', reify', hmod, agree', hq, hres⟩ :=
      funcBody_sound post (fun j hj => body j (by omega)) hpre₀ disj hreify₀ inner
    obtain rfl : _ = ws' := by simpa using hres
    obtain rfl : o = ⟨_, f, .normal (vf ++ _)⟩ := rest.nil_inv
    exact funcRule_finish reify.locals reify' hmod agree' postLocals hq disj'
  | frameRet inner arity rest =>
    obtain ⟨h', ρ', ws', disj', reify', hmod, agree', hq, hres⟩ :=
      funcBody_sound post (fun j hj => body j (by omega)) hpre₀ disj hreify₀ inner
    obtain ⟨pre₂, hres'⟩ : ∃ pre, _ = pre ++ ws' := by simpa using hres
    obtain rfl : _ = ws' := eq_of_append_eq hres' (arity.trans (post _ _ _ hq).symm)
    obtain rfl : o = ⟨_, f, .normal (vf ++ _)⟩ := rest.nil_inv
    exact funcRule_finish reify.locals reify' hmod agree' postLocals hq disj'

/-- The `invoke` a call of a verified function reduces to. -/
private theorem invoke_sound {k : Nat} {s : Store H} {f : Frame} {ρ : Sto}
    {vs vf v₀ : List Value} {h hf : AHeap} {d : FuncDef} {i : FuncIdx} {o : Outcome H}
    {a : FuncAddr} {fn : Silmaril.Wasm.V1.Func}
    (pre : Assert.StackLen P d.type.params.length)
    (post : Assert.StackLen Q d.type.results.length)
    (preLocals : Assert.Indep localVars P) (postLocals : Assert.Indep localVars Q)
    (body : ∀ j < k + 1, Valid host j F [Q] (some Q) (enterFunc d P) d.body Q)
    (hP : P ρ vs h) (disj : AHeap.Disj h hf) (reify : Reifies F s f ρ (h ∪ hf))
    (hfs : s.funcs[a.value]? = some (FuncInst.wasm d.type f.module fn))
    (hfnlocals : fn.locals = d.locals) (hfnbody : fn.body = d.body) (hv₀ : v₀ = vf ++ vs)
    (rest : BigStepN host k s f v₀ [.invoke a] o) :
    ∃ h' ρ', AHeap.Disj h' hf ∧ Reifies F o.store o.frame ρ' (h' ∪ hf) ∧
      (∀ x, x ∉ Expr.modified [Silmaril.Wasm.V1.Instr.call i] → ρ' x = ρ x) ∧
      Satisfies [] none Q ρ' vf h' o.result := by
  obtain ⟨v₁, hv₁, rest'⟩ := stack_gen rest
  cases rest' with
  | invokeHost foundh arityh behavior rest₂ => exact absurd (hfs.symm.trans foundh) (by simp)
  | invokeWasm foundf arityf resultArityf rest₂ =>
    obtain ⟨rfl, rfl, rfl⟩ : d.type = _ ∧ f.module = _ ∧ fn = _ := by
      have heq := Option.some.inj (hfs.symm.trans foundf)
      injection heq with h₁ h₂ h₃
      exact ⟨h₁, h₂, h₃⟩
    obtain ⟨rfl, rfl⟩ : vf = _ ∧ vs = _ := by
      have happ := List.append_inj' (hv₁.trans hv₀) (arityf.trans (pre ρ vs h hP).symm)
      exact ⟨happ.1.symm, happ.2.symm⟩
    exact frame_sound pre post preLocals postLocals (fun j hj => body j (by omega)) hP disj
      reify (hfnbody ▸ hfnlocals ▸ rest₂)

/-- The `[function]` rule, discharged against an execution of `call i`: if the
body of the `i`-th function satisfies its specification at every smaller
derivation height, then so does a call to it. The source's `{A : FuncSpecs}`
argument, unused, is dropped; `results` is unused here as well (the machine
checks it). -/
theorem valid_funcRule (i : FuncIdx) (d : FuncDef)
    (found : F[i.toNat]? = some d)
    (pre : Assert.StackLen P d.type.params.length)
    (post : Assert.StackLen Q d.type.results.length)
    (_results : d.type.results.length ≤ 1)
    (preLocals : Assert.Indep localVars P) (postLocals : Assert.Indep localVars Q)
    (body : ∀ k < n, Valid host k F [Q] (some Q) (enterFunc d P) d.body Q) :
    Valid host n F [] none P [.call i] Q := by
  intro s f ρ vs vf h hf o hP disj reify run
  obtain ⟨a, fn, hfa, hfs, hfnlocals, hfnbody⟩ := reify.funcs.2 i.toNat d found
  have run₀ : BigStepN host n s f (vf ++ vs) [.source (.call i)] o := run
  obtain ⟨v₀, hv₀, run'⟩ := stack_gen run₀
  cases run' with
  | plain step rest => cases step
  | plainTrap step => cases step
  | call found' rest =>
    obtain rfl : a = _ := Option.some.inj (hfa.symm.trans found')
    exact invoke_sound pre post preLocals postLocals body hP disj reify hfs hfnlocals hfnbody
      hv₀ rest

end Silmaril.Wasm.Logic.V1
