module

public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Execution.Core.Sim.Store
public import Silmaril.Wasm.Execution.Core.Sim.SetFuncs

@[expose] public section

/-! # Evaluation contexts of Core 3.0 reduction

The generic facts about `Step` that every same-language simulation needs, stated
once (all proved):

* **Context lifting** (`Step.append_right`, `Step.vals_left`, and their `Steps`
  forms): a step of a sequence is a step of the sequence with a value prefix and
  any suffix. These are `Step/ctxt-instrs` with the side condition discharged.
* **Exits** (`Exit`, `ExitShape`): the five instruction kernels that the
  bubbling rules of labels, handlers and frames inspect — `br l`, `return`,
  `return_call_ref`, `trap`, and `REF.EXN_ADDR a; THROW_REF`. A body in exit
  shape is `val* exit rest`, and every bubbling rule discards `rest`: that is
  why dead code after an exit is unobservable.
* **Head decomposition** (`Step.split_head`): a step of `val* a rest`, with `a`
  the first non-value, is a step of the redex `val* a` in context, or a
  `trap`/`throw_ref` discarding part of its context.
* **Store transport** (`Step.transport_storeRel`): a step whose redex does not
  call through a function reference is matched on any store with the same
  function types (`StoreRel F`), with the same resulting code. The proof replaces
  the function instances (`Store.setFuncs`, `Sim/SetFuncs.lean`): every family
  step is matched in bulk on `s.setFuncs g` when `g` has the types of `s.funcs`.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Context lifting -/

/-- A step of `es` is a step of `es ++ rest`. -/
theorem Step.append_right {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    (h : Step P host ⟨s, f, es⟩ ⟨s', f', es'⟩) (rest : List Admin) :
    Step P host ⟨s, f, es ++ rest⟩ ⟨s', f', es' ++ rest⟩ := by
  rcases rest with _ | ⟨a, rest⟩
  · simpa using h
  · simpa [vals] using
      Step.ctxtInstrs (vs := []) (rest := a :: rest) h (Or.inr (List.cons_ne_nil _ _))

/-- A step of `es` is a step of `val* es`. -/
theorem Step.vals_left {s s' : Store H} {f f' : Frame} {es es' : List Admin}
    (h : Step P host ⟨s, f, es⟩ ⟨s', f', es'⟩) (vs : List Val) :
    Step P host ⟨s, f, vals vs ++ es⟩ ⟨s', f', vals vs ++ es'⟩ := by
  rcases vs with _ | ⟨v, vs⟩
  · simpa [vals] using h
  · simpa using Step.ctxtInstrs (vs := v :: vs) (rest := []) h (Or.inl (List.cons_ne_nil _ _))

/-- Runs lift through `++ rest`. -/
theorem Steps.append_right {c c' : Config H} (h : Steps P host c c') (rest : List Admin) :
    Steps P host ⟨c.store, c.frame, c.code ++ rest⟩ ⟨c'.store, c'.frame, c'.code ++ rest⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    have lift : ∀ {a b : Config H}, Step P host a b →
        Step P host ⟨a.store, a.frame, a.code ++ rest⟩ ⟨b.store, b.frame, b.code ++ rest⟩ := by
      intro a b hab
      obtain ⟨_, _, _⟩ := a
      obtain ⟨_, _, _⟩ := b
      exact Step.append_right hab rest
    exact ih.tail (lift hab)

/-- Runs lift through a value prefix. -/
theorem Steps.vals_left {c c' : Config H} (h : Steps P host c c') (vs : List Val) :
    Steps P host ⟨c.store, c.frame, vals vs ++ c.code⟩ ⟨c'.store, c'.frame, vals vs ++ c'.code⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih =>
    have lift : ∀ {a b : Config H}, Step P host a b →
        Step P host ⟨a.store, a.frame, vals vs ++ a.code⟩ ⟨b.store, b.frame, vals vs ++ b.code⟩ := by
      intro a b hab
      obtain ⟨_, _, _⟩ := a
      obtain ⟨_, _, _⟩ := b
      exact Step.vals_left hab vs
    exact ih.tail (lift hab)

/-! ## Exits -/

/-- The exit kernels inspected by the bubbling rules of labels, handlers and
frames (`br-label-*`, `br-handler`, `return-*`, `return_call_ref-*`,
`throw_ref-*`, `trap-*`). -/
inductive Exit : List Admin → Prop where
  | br (l : LabelIdx) : Exit [.plain (.br l)]
  | return_ : Exit [.plain .return_]
  | returnCallRef {c : Admin} : c.IsReturnCallRef → Exit [c]
  | trap : Exit [.trap]
  | throw (a : Nat) : Exit (throwing a)

/-- A sequence in exit shape: values, an exit kernel, then anything. -/
def ExitShape (es : List Admin) : Prop :=
  ∃ (vs : List Val) (k rest : List Admin), Exit k ∧ es = vals vs ++ k ++ rest

/-- Values do not step. -/
theorem Step.not_vals {s : Store H} {f : Frame} {vs : List Val} {c' : Config H} :
    ¬ Step P host ⟨s, f, vals vs⟩ c' :=
  Core.Step.not_vals

/-! ## Redex shapes -/

/-- `l` is `val* b` with `b` not a value. -/
def lastRedex : List Admin → Bool
  | [] => false
  | [b] => b.val?.isNone
  | b :: c :: l => b.val?.isSome && lastRedex (c :: l)

theorem vals_nil' : vals ([] : List Val) = [] := rfl

theorem vals_cons' (v : Val) (vs : List Val) : vals (v :: vs) = v.toAdmin :: vals vs := rfl

theorem lastRedex_vals_append (vs : List Val) {l : List Admin} (hl : l ≠ []) :
    lastRedex (vals vs ++ l) = lastRedex l := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨c, l', hc⟩ : ∃ c l', vals vs ++ l = c :: l' := by
      cases h : vals vs ++ l with
      | nil => exact absurd (List.append_eq_nil_iff.mp h).2 hl
      | cons c l' => exact ⟨c, l', rfl⟩
    rw [vals_cons', List.cons_append, hc]
    simp only [lastRedex, Admin.val?_toAdmin, Option.isSome_some, Bool.true_and]
    rw [← hc, ih]

theorem eq_of_lastRedex : ∀ {l : List Admin}, lastRedex l = true →
    ∃ (us : List Val) (b : Admin), b.val? = none ∧ l = vals us ++ [b]
  | [], h => by simp [lastRedex] at h
  | [b], h => ⟨[], b, by simpa [lastRedex] using h, rfl⟩
  | b :: c :: l, h => by
    simp only [lastRedex, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨⟨v, hv⟩, h⟩ := h
    obtain ⟨us, b', hb', he⟩ := eq_of_lastRedex h
    refine ⟨v :: us, b', hb', ?_⟩
    rw [he, Admin.eq_of_val? hv, vals_cons', List.cons_append]

/-- The first non-value of a sequence is determined. -/
theorem vals_append_cons_inj {a b : Admin} {es fs : List Admin} (ha : a.val? = none)
    (hb : b.val? = none) : ∀ {vs ws : List Val}, vals vs ++ a :: es = vals ws ++ b :: fs →
    vs = ws ∧ a = b ∧ es = fs
  | [], [], h => by
    rw [vals_nil', List.nil_append, List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h⟩
  | [], w :: ws, h => by
    rw [vals_nil', List.nil_append, vals_cons', List.cons_append, List.cons.injEq] at h
    rw [h.1, Admin.val?_toAdmin] at ha
    cases ha
  | v :: vs, [], h => by
    rw [vals_nil', List.nil_append, vals_cons', List.cons_append, List.cons.injEq] at h
    rw [← h.1, Admin.val?_toAdmin] at hb
    cases hb
  | v :: vs, w :: ws, h => by
    rw [vals_cons', vals_cons', List.cons_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := vals_append_cons_inj ha hb h₂
    have hv := congrArg Admin.val? h₁
    rw [Admin.val?_toAdmin, Admin.val?_toAdmin, Option.some.injEq] at hv
    exact ⟨by rw [hv], rfl, rfl⟩

/-- A sequence that is not all values has a first non-value. -/
theorem exists_head_of_not_all : ∀ {l : List Admin}, l.all Admin.isVal = false →
    ∃ (vs : List Val) (b : Admin) (r : List Admin), b.val? = none ∧ l = vals vs ++ b :: r
  | [], h => by simp at h
  | b :: l, h => by
    cases hb : b.val? with
    | none => exact ⟨[], b, l, hb, rfl⟩
    | some v =>
      have hl : l.all Admin.isVal = false := by
        simpa [List.all_cons, Admin.isVal, hb] using h
      obtain ⟨vs, b', r, hb', rfl⟩ := exists_head_of_not_all hl
      exact ⟨v :: vs, b', r, hb', by rw [Admin.eq_of_val? hb, vals_cons', List.cons_append]⟩

/-- A sequence of values is `vals` of its values. -/
theorem exists_vals_of_all : ∀ {l : List Admin}, l.all Admin.isVal = true →
    ∃ vs : List Val, l = vals vs
  | [], _ => ⟨[], rfl⟩
  | b :: l, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hb, hl⟩ := h
    obtain ⟨vs, rfl⟩ := exists_vals_of_all hl
    cases hv : b.val? with
    | none => simp [Admin.isVal, hv] at hb
    | some v => exact ⟨v :: vs, by rw [Admin.eq_of_val? hv, vals_cons']⟩

/-- An exit kernel is values followed by one non-value. -/
theorem Exit.eq_vals_append {k : List Admin} (hk : Exit k) :
    ∃ (pre : List Val) (e : Admin), e.val? = none ∧ k = vals pre ++ [e] := by
  cases hk with
  | br l => exact ⟨[], .plain (.br l), rfl, rfl⟩
  | return_ => exact ⟨[], .plain .return_, rfl, rfl⟩
  | @returnCallRef c hc => exact ⟨[], c, Admin.val?_of_isReturnCallRef hc, rfl⟩
  | trap => exact ⟨[], .trap, rfl, rfl⟩
  | throw a => exact ⟨[.ref (.exn a)], .plain .throwRef, rfl, rfl⟩

theorem val?_trap : Admin.trap.val? = none := rfl

theorem val?_throwRef : (Admin.plain .throwRef).val? = none := rfl

theorem ParametricStep.lastRedex_eq {is is' : List Admin} (h : ParametricStep is is') :
    lastRedex is = true := by
  cases h <;> simp [Sim.lastRedex, constI32] <;> simp [Admin.val?]

theorem NumericStep.lastRedex_eq {is is' : List Admin} (h : NumericStep P is is') :
    lastRedex is = true := by
  cases h <;> simp [Sim.lastRedex] <;> simp [Admin.val?]

theorem VectorStep.lastRedex_eq {is is' : List Admin} (h : VectorStep P is is') :
    lastRedex is = true := by
  cases h <;> simp [Sim.lastRedex, constI32] <;> simp [Admin.val?]

theorem VariableStep.lastRedex_eq {c c' : Config H} (h : VariableStep c c') :
    lastRedex c.code = true := by
  cases h <;> simp [Sim.lastRedex] <;> simp [Admin.val?]

theorem TableStep.lastRedex_eq {c c' : Config H} (h : TableStep P c c') :
    lastRedex c.code = true := by
  cases h <;> simp [Sim.lastRedex, constI32] <;> simp [Admin.val?]

theorem MemoryStep.lastRedex_eq {c c' : Config H} (h : MemoryStep P c c') :
    lastRedex c.code = true := by
  cases h <;> simp [Sim.lastRedex, constI32] <;> simp [Admin.val?]

theorem RefStep.lastRedex_eq {c c' : Config H} (h : RefStep c c') :
    lastRedex c.code = true := by
  cases h <;> simp [Sim.lastRedex, constI32] <;> simp [Admin.val?]

theorem AggregateStep.lastRedex_eq {c c' : Config H} (h : AggregateStep c c') :
    lastRedex c.code = true := by
  cases h <;> simp [Sim.lastRedex, lastRedex_vals_append, constI32] <;> simp [Admin.val?]

/-- A step whose code is a redex `val* b` is a step of the redex at the head of
any decomposition `val* a es`. -/
theorem split_head_of_lastRedex {c c' : Config H} (h : Step P host c c')
    (hr : lastRedex c.code = true) {vs : List Val} {a : Admin} {es : List Admin}
    (ha : a.val? = none) (hc : c.code = vals vs ++ a :: es) :
    ∃ (ws us : List Val) (is' : List Admin), vs = ws ++ us ∧
      Step P host ⟨c.store, c.frame, vals us ++ [a]⟩ ⟨c'.store, c'.frame, is'⟩ ∧
      c'.code = vals ws ++ is' ++ es := by
  obtain ⟨us, b, hb, hc'⟩ := eq_of_lastRedex hr
  obtain ⟨h1, h2, h3⟩ := vals_append_cons_inj hb ha (hc'.symm.trans hc)
  refine ⟨[], vs, c'.code, by simp, ?_, by rw [← h3]; simp [vals_nil']⟩
  rw [← h1, ← h2, ← hc']
  exact h

/-- The conclusion of `Step.split_head`. -/
def SplitHead (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (s' : Store H)
    (f' : Frame) (vs : List Val) (a : Admin) (es es' : List Admin) : Prop :=
  (∃ (ws us : List Val) (is' : List Admin), vs = ws ++ us ∧
        Step P host ⟨s, f, vals us ++ [a]⟩ ⟨s', f', is'⟩ ∧ es' = vals ws ++ is' ++ es) ∨
    (a = .trap ∧ s' = s ∧ f' = f ∧ ∃ (ws us : List Val) (r r' : List Admin),
        vs = ws ++ us ∧ es = r ++ r' ∧ (us ≠ [] ∨ r ≠ []) ∧ es' = vals ws ++ [.trap] ++ r') ∨
    (a = .plain .throwRef ∧ s' = s ∧ f' = f ∧ ∃ (ws us : List Val) (x : Nat) (r r' : List Admin),
        vs = ws ++ us ++ [.ref (.exn x)] ∧ es = r ++ r' ∧ (us ≠ [] ∨ r ≠ []) ∧
        es' = vals ws ++ throwing x ++ r')

set_option linter.unusedSimpArgs false in
theorem Step.split_head_aux {c c' : Config H} (h : Step P host c c') :
    Step P host c c' → ∀ (vs : List Val) (a : Admin) (es : List Admin), a.val? = none →
      c.code = vals vs ++ a :: es →
      SplitHead P host c.store c.frame c'.store c'.frame vs a es c'.code := by
  induction h with
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs hne ih =>
    intro _ vs a es ha hc
    have hna : is.all Admin.isVal = false := hs.not_all_isVal
    obtain ⟨vs₁, b, es₁, hb, rfl⟩ := exists_head_of_not_all hna
    dsimp only at hc
    have hc' : vals (vs₀ ++ vs₁) ++ b :: (es₁ ++ rest) = vals vs ++ a :: es := by
      rw [← hc]; simp
    obtain ⟨h1, h2, h3⟩ := vals_append_cons_inj hb ha hc'
    subst h1 h3
    subst h2
    have := ih hs _ _ _ hb rfl
    unfold SplitHead at this ⊢
    dsimp only at this ⊢
    rcases this with ⟨ws, us, is'', rfl, hst, he⟩ |
        ⟨rfl, rfl, rfl, ws, us, r, r', rfl, rfl, hne', he⟩ |
        ⟨rfl, rfl, rfl, ws, us, x, r, r', rfl, rfl, hne', he⟩
    · left
      refine ⟨vs₀ ++ ws, us, is'', by simp, hst, ?_⟩
      rw [he]; simp
    · right; left
      refine ⟨rfl, rfl, rfl, vs₀ ++ ws, us, r, r' ++ rest, by simp, by simp, hne', ?_⟩
      rw [he]; simp
    · right; right
      refine ⟨rfl, rfl, rfl, vs₀ ++ ws, us, x, r, r' ++ rest, by simp, by simp, hne', ?_⟩
      rw [he]; simp
  | @trapInstrs s f vs₀ rest hne =>
    intro _ vs a es ha hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals vs ++ a :: es := by
      rw [← hc]; simp
    obtain ⟨rfl, rfl, rfl⟩ := vals_append_cons_inj val?_trap ha hc'
    unfold SplitHead
    dsimp only
    right; left
    exact ⟨rfl, rfl, rfl, [], _, _, [], by simp, by simp, hne, by simp [vals_nil']⟩
  | @throwRefInstrs s f vs₀ x rest hne =>
    intro _ vs a es ha hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals vs ++ a :: es := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    obtain ⟨rfl, rfl, rfl⟩ := vals_append_cons_inj val?_throwRef ha hc'
    unfold SplitHead
    dsimp only
    right; right
    exact ⟨rfl, rfl, rfl, [], _, x, _, [], by simp, by simp, hne, by simp [vals_nil']⟩
  | _ =>
    intro h0 vs a es ha hc
    unfold SplitHead
    left
    refine split_head_of_lastRedex h0 ?_ ha hc
    first
      | exact ParametricStep.lastRedex_eq ‹_›
      | exact NumericStep.lastRedex_eq ‹_›
      | exact VectorStep.lastRedex_eq ‹_›
      | exact VariableStep.lastRedex_eq ‹_›
      | exact TableStep.lastRedex_eq ‹_›
      | exact MemoryStep.lastRedex_eq ‹_›
      | exact RefStep.lastRedex_eq ‹_›
      | exact AggregateStep.lastRedex_eq ‹_›
      | (simp [Sim.lastRedex, lastRedex_vals_append, constI32]; simp [Admin.val?]; done)
      | (simp [Sim.lastRedex, lastRedex_vals_append, Admin.val?_of_isCallRef (by assumption)]
         simp [Admin.val?])

/-! ## Head decomposition -/

/-- **Head decomposition.** Let `a` be the first non-value of `val* a es`. A step
of this sequence is either a step of the redex `val* a` (using a suffix `us` of
the values) with `es` untouched, or `a` is `trap` (resp. the `THROW_REF` of an
exception reference) and the step discards some values before it and some prefix
of `es` (`trap-instrs`, `throw_ref-instrs`, possibly under `ctxt-instrs`). -/
theorem Step.split_head {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin}
    {es es' : List Admin} (ha : a.val? = none)
    (h : Step P host ⟨s, f, vals vs ++ a :: es⟩ ⟨s', f', es'⟩) :
    (∃ (ws us : List Val) (is' : List Admin), vs = ws ++ us ∧
        Step P host ⟨s, f, vals us ++ [a]⟩ ⟨s', f', is'⟩ ∧ es' = vals ws ++ is' ++ es) ∨
    (a = .trap ∧ s' = s ∧ f' = f ∧ ∃ (ws us : List Val) (r r' : List Admin),
        vs = ws ++ us ∧ es = r ++ r' ∧ (us ≠ [] ∨ r ≠ []) ∧ es' = vals ws ++ [.trap] ++ r') ∨
    (a = .plain .throwRef ∧ s' = s ∧ f' = f ∧ ∃ (ws us : List Val) (x : Nat) (r r' : List Admin),
        vs = ws ++ us ++ [.ref (.exn x)] ∧ es = r ++ r' ∧ (us ≠ [] ∨ r ≠ []) ∧
        es' = vals ws ++ throwing x ++ r') :=
  Step.split_head_aux h h vs a es ha rfl

/-! ## Store transport -/

/-- The administrative instructions with a body: `LABEL`, `HANDLER`, `FRAME`. -/
def _root_.Silmaril.Wasm.Execution.Core.Admin.IsCtx : Admin → Prop
  | .label .. | .handler .. | .frame .. => True
  | _ => False

/-- A head redex that is neither a context nor a call through a function reference
steps on any store with the same function types, leaving function instances
unchanged. -/
theorem Step.setFuncs_aux {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (a : Admin), ¬ a.IsCtx → ¬ a.IsCallRef → a.val? = none →
      c.code = vals us ++ [a] → ∀ g : List (FuncInst H),
      g.map FuncInst.type = c.store.funcs.map FuncInst.type →
      Step P host ⟨c.store.setFuncs g, c.frame, c.code⟩ ⟨c'.store.setFuncs g, c'.frame, c'.code⟩ ∧
        c'.store.funcs = c.store.funcs := by
  induction h with
  | parametric hp => intro _ _ _ _ _ _ g _; exact ⟨.parametric hp, rfl⟩
  | numeric hp => intro _ _ _ _ _ _ g _; exact ⟨.numeric hp, rfl⟩
  | vector hp => intro _ _ _ _ _ _ g _; exact ⟨.vector hp, rfl⟩
  | «variable» hp => intro _ _ _ _ _ _ g _; exact ⟨.variable (hp.setFuncs g), hp.funcs_eq⟩
  | table hp => intro _ _ _ _ _ _ g _; exact ⟨.table (hp.setFuncs g), hp.funcs_eq⟩
  | memory hp => intro _ _ _ _ _ _ g _; exact ⟨.memory (hp.setFuncs g), hp.funcs_eq⟩
  | reference hp => intro _ _ _ _ _ _ g hg; exact ⟨.reference (hp.setFuncs hg), hp.funcs_eq⟩
  | aggregate hp => intro _ _ _ _ _ _ g _; exact ⟨.aggregate (hp.setFuncs g), hp.funcs_eq⟩
  | @ctxtInstrs _ _ _ _ vs₀ is _ rest hs hne ih =>
    intro us a hctx hcall ha hc g hg
    have hna : is.all Admin.isVal = false := hs.not_all_isVal
    obtain ⟨vs₁, b, es₁, hb, rfl⟩ := exists_head_of_not_all hna
    dsimp only at hc
    have hc' : vals (vs₀ ++ vs₁) ++ b :: (es₁ ++ rest) = vals us ++ a :: [] := by
      rw [← hc]; simp
    obtain ⟨rfl, rfl, h3⟩ := vals_append_cons_inj hb ha hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    obtain ⟨ih₁, ih₂⟩ := ih vs₁ _ hctx hcall hb rfl g hg
    exact ⟨.ctxtInstrs ih₁ hne, ih₂⟩
  | @call _ _ _ _ fi hx hf =>
    intro _ _ _ _ _ _ _ hg
    obtain ⟨fi', hga, hty⟩ := exists_funcs_of_types hg hf
    refine ⟨?_, rfl⟩
    dsimp only
    rw [← hty]
    exact .call hx hga
  | @returnCall _ _ _ _ fi hx hf =>
    intro _ _ _ _ _ _ _ hg
    obtain ⟨fi', hga, hty⟩ := exists_funcs_of_types hg hf
    refine ⟨?_, rfl⟩
    dsimp only
    rw [← hty]
    exact .returnCall hx hga
  | @throw s _ _ _ _ _ _ ht he hn =>
    intro _ _ _ _ _ _ g _
    exact ⟨Step.throw (s := s.setFuncs g) ht he hn, rfl⟩
  | brOnCastSucceed hr =>
    intro _ _ _ _ _ _ _ hg
    exact ⟨.brOnCastSucceed ((RefOk.setFuncs_iff hg).2 hr), rfl⟩
  | brOnCastFail hr =>
    intro _ _ _ _ _ _ _ hg
    exact ⟨.brOnCastFail (fun h' => hr ((RefOk.setFuncs_iff hg).1 h')), rfl⟩
  | brOnCastFailSucceed hr =>
    intro _ _ _ _ _ _ _ hg
    exact ⟨.brOnCastFailSucceed ((RefOk.setFuncs_iff hg).2 hr), rfl⟩
  | brOnCastFailFail hr =>
    intro _ _ _ _ _ _ _ hg
    exact ⟨.brOnCastFailFail (fun h' => hr ((RefOk.setFuncs_iff hg).1 h')), rfl⟩
  | _ =>
    intro _ _ hctx hcall _ hc _ _
    first
      | (have hl := congrArg List.getLast? hc
         simp at hl
         subst hl
         first | exact absurd trivial hctx | exact absurd ‹_› hcall)
      | exact ⟨.block ‹_› ‹_›, rfl⟩
      | exact ⟨.loop ‹_› ‹_›, rfl⟩
      | exact ⟨.ifTrue ‹_›, rfl⟩
      | exact ⟨.ifFalse, rfl⟩
      | exact ⟨.brIfTrue ‹_›, rfl⟩
      | exact ⟨.brIfFalse, rfl⟩
      | exact ⟨.brTableLt ‹_›, rfl⟩
      | exact ⟨.brTableGe ‹_›, rfl⟩
      | exact ⟨.brOnNullNull, rfl⟩
      | exact ⟨.brOnNullAddr ‹_›, rfl⟩
      | exact ⟨.brOnNonNullNull, rfl⟩
      | exact ⟨.brOnNonNullAddr ‹_›, rfl⟩
      | exact ⟨.callIndirect, rfl⟩
      | exact ⟨.returnCallIndirect, rfl⟩
      | exact ⟨.throwRefNull, rfl⟩
      | exact ⟨.throwRefInstrs ‹_›, rfl⟩
      | exact ⟨.tryTable ‹_› ‹_›, rfl⟩
      | exact ⟨.trapInstrs ‹_›, rfl⟩

/-- **Store transport.** A redex `val* a` whose head is neither a context nor a
call through a function reference reads function instances only through their
types, so its step is matched on any store with the same function types and the
same other components, with the same code, frame and a related store. -/
theorem Step.transport_storeRel {F : FuncInst H → FuncInst H → Prop}
    {s s' t : Store H} {f f' : Frame} {us : List Val} {a : Admin} {es' : List Admin}
    (hst : StoreRel F s t) (hctx : ¬ a.IsCtx) (hcall : ¬ a.IsCallRef)
    (h : Step P host ⟨s, f, vals us ++ [a]⟩ ⟨s', f', es'⟩) :
    ∃ t', Step P host ⟨t, f, vals us ++ [a]⟩ ⟨t', f', es'⟩ ∧ StoreRel F s' t' := by
  have ha : a.val? = none := by
    cases hv : a.val? with
    | none => rfl
    | some v =>
      exfalso
      obtain rfl := Admin.eq_of_val? hv
      have hv' : vals us ++ [v.toAdmin] = vals (us ++ [v]) := by simp [vals]
      rw [hv'] at h
      exact Step.not_vals h
  obtain ⟨hstep, hfuncs⟩ := Step.setFuncs_aux h us a hctx hcall ha rfl t.funcs hst.types.symm
  refine ⟨s'.setFuncs t.funcs, ?_, StoreRel.setFuncs_of hst hfuncs⟩
  rw [hst.eq_setFuncs]
  exact hstep

end Silmaril.Wasm.Execution.Core.Sim
