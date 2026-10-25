module

public import Silmaril.Wasm.Execution.Core.Soundness.Defs

@[expose] public section

/-! # Preservation for the exception and trap rules (spec 4.3)

`AdminsOk`-level preservation lemmas for the `throw`, `throw_ref-*` and `trap-*`
rules of `Step`, in the form

  `AdminsOk s C lhs it → wf hyps → AdminsOk s' C rhs it`

plus `StoreOk`/`Extend` for the store allocated by `throw`.

The helpers are self-contained (suffix `Exn`) so this file builds standalone.

Explicit hypotheses beyond `C.Wf` (see each lemma):
* `trapInstrs`/`throwRefInstrs`/the `frame` rules take `ResultOk C.toTypeCtx it.results`;
  the sequence rules also take that the locals initialised by `it` are already set in `C`
  (otherwise false: `trap; local.set x` has type `[] →_{x} []`, `trap` does not).
* `throwRefHandlerCatch`/`CatchRef` take that the exception's fields are typed at the
  parameters of the tag the catch clause names (`hE`).
* `throw`'s `StoreOk` lemma takes that the thrown values are typed at the tag's parameters.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Generic helpers -/

/-- Every administrative instruction of a typed sequence is typed (somewhere). -/
theorem AdminsOk.mem_okExn {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it →
      ∀ b ∈ as, ∃ C' it', AdminOk s C' b it'
  | _, _, _, .nil, _, hb => by simp at hb
  | _, _, _, .single h, _, hb => by
    simp only [List.mem_singleton] at hb; subst hb; exact ⟨_, _, h⟩
  | _, _, _, .seq h₁ _ h₂, b, hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact AdminsOk.mem_okExn h₁ b hb
    · exact AdminsOk.mem_okExn h₂ b hb
  | _, _, _, .cons ha _ hs, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, _, ha⟩
    · exact AdminsOk.mem_okExn hs b hb
  | _, _, _, .sub h _ _, b, hb => AdminsOk.mem_okExn h b hb
  | _, _, _, .frame h _, b, hb => AdminsOk.mem_okExn h b hb

theorem RefOk.exn_invExn {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    ∀ a, r = .exn a → ∃ e, s.exns[a]? = some e := by
  induction h with
  | exn h => intro a e; cases e; exact ⟨_, h⟩
  | sub _ _ _ ih => exact ih
  | _ => intro a e; cases e

theorem AdminOk.ref_exn_invExn {s : Store H} {C : Context} {a : Nat} {it : InstrType}
    (h : AdminOk s C (.ref (.exn a)) it) : ∃ e, s.exns[a]? = some e := by
  cases h with
  | ref h => exact h.exn_invExn a rfl

/-- The exception address of a typed `throwing a` (anywhere in a sequence) exists. -/
theorem AdminsOk.exn_existsExn {s : Store H} {C : Context} {as : List Admin} {it : InstrType}
    {a : Nat} (h : AdminsOk s C as it) (hm : Admin.ref (.exn a) ∈ as) :
    ∃ e, s.exns[a]? = some e := by
  obtain ⟨_, _, h'⟩ := h.mem_okExn _ hm
  exact h'.ref_exn_invExn

/-- `REF.EXN_ADDR a; THROW_REF` is typed at any valid instruction type. -/
theorem AdminsOk.throwingExn {s : Store H} {C : Context} {a : Nat} {t₁ t₂ : List CValType}
    (he : ∃ e, s.exns[a]? = some e) (hok : InstrTypeOk C (.plain t₁ t₂)) :
    AdminsOk s C (throwing a) (.plain t₁ t₂) := by
  obtain ⟨e, he⟩ := he
  have hr : RefOk s (.exn a) (.ref true (.abs .exn)) :=
    .sub (.exn he) (.ref (.abs .exn)) (.refNull .heapRefl)
  have h₁ : AdminsOk s C [.ref (.exn a)] ⟨t₁, [], t₁ ++ [.refv (.ref true (.abs .exn))]⟩ := by
    simpa using AdminsOk.frame (ts := t₁) (AdminsOk.single (AdminOk.ref (C := C) hr)) hok.1
  have h₂ : AdminsOk s (C.initLocals []) [.plain .throwRef]
      ⟨t₁ ++ [.refT true (.abs .exn)], [], t₂⟩ := .single (.plain (.throwRef hok))
  exact AdminsOk.seq h₁ (by simp) h₂

/-- Retyping at a supertype whose extra initialised locals are already set. -/
theorem AdminsOk.to_itExn {s : Store H} {C : Context} {as : List Admin} {it : InstrType}
    (h : AdminsOk s C as (.plain it.params it.results))
    (hp : ResultOk C.toTypeCtx it.params) (hr : ResultOk C.toTypeCtx it.results)
    (hi : ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩) : AdminsOk s C as it :=
  .sub h ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun x hx _ => hi x hx⟩
    ⟨hp, hr, fun x hx => let ⟨_, ht⟩ := hi x hx; ⟨_, ht⟩⟩

/-- If no instruction of a sequence initialises locals, the locals initialised by any
typing of the sequence are already set. -/
theorem AdminsOk.inits_setExn {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it →
      (∀ b ∈ as, ∀ C' it', AdminOk s C' b it' → it'.inits = []) →
      ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩
  | _, _, _, .nil, _ => by simp
  | _, _, _, .single h, hI => by rw [hI _ (by simp) _ _ h]; simp
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, hI => by
    have i₁ := AdminsOk.inits_setExn h₁ fun b hb => hI b (List.mem_append_left _ hb)
    have i₂ := AdminsOk.inits_setExn h₂ fun b hb => hI b (List.mem_append_right _ hb)
    rw [Context.initLocals_of_set i₁] at i₂
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact i₁ x hx
    · exact i₂ x hx
  | _, _, _, .cons ha _ hs, hI => by
    have i₂ := AdminsOk.inits_setExn hs fun b hb => hI b (List.mem_cons_of_mem _ hb)
    have h0 := hI _ (by simp) _ _ ha
    simp only at h0
    subst h0
    simpa using i₂
  | _, _, it', .sub (it := it) h hs _, hI => by
    have i := AdminsOk.inits_setExn h hI
    intro x hx
    by_cases hx' : x ∈ it.inits
    · exact i x hx'
    · exact hs.2.2 x hx hx'
  | _, _, _, .frame h _, hI => fun x hx => AdminsOk.inits_setExn h hI x hx

/-- The results of a sequence ending in an instruction with regular results are valid. -/
theorem AdminsOk.results_okExn {s : Store H} {a : Admin}
    (hlast : ∀ C' it', C'.Wf → AdminOk s C' a it' → ResultOk C'.toTypeCtx it'.results) :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → C.Wf →
      as.getLast? = some a → ResultOk C.toTypeCtx it.results
  | _, _, _, .nil, _, hl => by simp at hl
  | _, _, _, .single h, hC, hl => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl; exact hlast _ _ hC h
  | C, _, _, .seq (as₁ := as₁) (as₂ := as₂) (xs₁ := xs₁) h₁ _ h₂, hC, hl => by
    by_cases he : as₂ = []
    · subst he
      simp only [List.append_nil] at hl
      have r₁ := AdminsOk.results_okExn hlast h₁ hC hl
      have := (AdminsOk.nil_aux h₂ rfl (by rw [Context.initLocals_toTypeCtx]; exact hC.types)).2.1
      simpa using this
    · rw [List.getLast?_append_of_ne_nil _ he] at hl
      have := AdminsOk.results_okExn hlast h₂ (hC.initLocals _) hl
      simpa using this
  | C, _, _, .cons (as := as) (xs₁ := xs₁) ha _ hs, hC, hl => by
    by_cases he : as = []
    · subst he
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      have := (AdminsOk.nil_aux hs rfl (by rw [Context.initLocals_toTypeCtx]; exact hC.types)).2.1
      simpa using this
    · rw [List.getLast?_cons, List.getLast?_eq_some_getLast he] at hl
      simp only [Option.getD_some] at hl
      rw [← List.getLast?_eq_some_getLast he] at hl
      have := AdminsOk.results_okExn hlast hs (hC.initLocals _) hl
      simpa using this
  | _, _, _, .sub _ _ hok, _, _ => hok.2.1
  | _, _, _, .frame h hok, hC, hl => ResultOk.append hok (AdminsOk.results_okExn hlast h hC hl)

theorem AdminOk.plain_resultsExn {s : Store H} {i : Instr} :
    ∀ C' it', C'.Wf → AdminOk s C' (.plain i) it' → ResultOk C'.toTypeCtx it'.results := by
  intro C' it' hC h
  cases h with
  | plain h => exact (h.regular hC).2.1
  | throwRefInits hok => exact hok.2.1

theorem AdminOk.trap_resultsExn {s : Store H} :
    ∀ C' it', C'.Wf → AdminOk s C' .trap it' → ResultOk C'.toTypeCtx it'.results := by
  intro C' it' _ h
  cases h with
  | trap hok => exact hok.2.1

theorem AdminsOk.throwing_resultsExn {s : Store H} {C : Context} {a : Nat} {it : InstrType}
    (hC : C.Wf) (h : AdminsOk s C (throwing a) it) : ResultOk C.toTypeCtx it.results :=
  AdminsOk.results_okExn AdminOk.plain_resultsExn h hC rfl

theorem AdminsOk.trap1_resultsExn {s : Store H} {C : Context} {it : InstrType}
    (hC : C.Wf) (h : AdminsOk s C [.trap] it) : ResultOk C.toTypeCtx it.results :=
  AdminsOk.results_okExn AdminOk.trap_resultsExn h hC rfl

theorem Context.Wf.withLabelExn {C : Context} {t : List CValType} (hC : C.Wf)
    (ht : ResultOk C.toTypeCtx t) : (C.withLabel t).Wf :=
  ⟨hC.types, hC.tags, hC.globals, hC.tables, hC.funcs, hC.locals, fun ts h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ht
    · exact hC.labels ts h, hC.return_, hC.elems⟩

/-- Replacing a single administrative instruction by code with the same typings,
in any context satisfying an invariant `P` that is stable under `initLocals`. -/
theorem AdminsOk.replace1Exn {s s' : Store H} {a : Admin} {as' : List Admin}
    {P : Context → Prop} (hP : ∀ C xs, P C → P (C.initLocals xs))
    (hs0 : ∀ C it, AdminsOk s C [] it → AdminsOk s' C [] it)
    (hrep : ∀ C it, P C → AdminOk s C a it → AdminsOk s' C as' it) :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → P C → as = [a] →
      AdminsOk s' C as' it
  | _, _, _, .nil, _, e => by simp at e
  | _, _, _, .single h, hC, e => by
    simp only [List.cons.injEq, and_true] at e; subst e; exact hrep _ _ hC h
  | _, _, _, .seq (as₁ := as₁) (as₂ := as₂) h₁ hx h₂, hC, e => by
    rcases List.append_eq_singleton_iff.mp e with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · have r := AdminsOk.replace1Exn hP hs0 hrep h₂ (hP _ _ hC) e₂
      have h₁' := hs0 _ _ (e₁ ▸ h₁)
      simpa using AdminsOk.seq h₁' hx r
    · have r := AdminsOk.replace1Exn hP hs0 hrep h₁ hC e₁
      have h₂' := hs0 _ _ (e₂ ▸ h₂)
      simpa using AdminsOk.seq r hx h₂'
  | _, _, _, .cons (as := as) ha hx hs, hC, e => by
    simp only [List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    simpa using AdminsOk.seq (hrep _ _ hC ha) hx (hs0 _ _ hs)
  | _, _, _, .sub h hs hok, hC, e => .sub (AdminsOk.replace1Exn hP hs0 hrep h hC e) hs hok
  | _, _, _, .frame h hok, hC, e => .frame (AdminsOk.replace1Exn hP hs0 hrep h hC e) hok

theorem AdminsOk.nil_storeExn {s : Store H} (s' : Store H) : ∀ {C : Context} {as : List Admin}
    {it : InstrType}, AdminsOk s C as it → as = [] → AdminsOk s' C [] it
  | _, _, _, .nil, _ => .nil
  | _, _, _, .single _, he => by simp at he
  | _, _, _, .cons _ _ _, he => by simp at he
  | _, _, _, .seq h₁ hx h₂, he => by
    obtain ⟨e₁, e₂⟩ := List.append_eq_nil_iff.mp he
    exact AdminsOk.seq (AdminsOk.nil_storeExn s' h₁ e₁) hx (AdminsOk.nil_storeExn s' h₂ e₂)
  | _, _, _, .sub h hs hok, he => .sub (AdminsOk.nil_storeExn s' h he) hs hok
  | _, _, _, .frame h hok, he => .frame (AdminsOk.nil_storeExn s' h he) hok

/-- Wf-invariant for `replace1Exn`. -/
theorem Context.Wf.initLocals_PExn : ∀ (C : Context) (xs : List Nat), C.Wf → (C.initLocals xs).Wf :=
  fun _ xs hC => hC.initLocals xs

theorem Context.initLocals_tagsExn (C : Context) (xs : List Nat) :
    (C.initLocals xs).tags = C.tags := by
  obtain ⟨L, hL, -⟩ := C.initLocals_spec xs; rw [hL]

/-- Values and `THROW`/`THROW_REF` initialise no locals. -/
theorem AdminOk.toAdmin_initsExn {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminOk s C v.toAdmin it) : it.inits = [] := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · cases h with
    | plain h => (cases h <;> (try (rename_i hh; cases hh))); rfl
  · cases h with
    | plain h => (cases h <;> (try (rename_i hh; cases hh))); rfl
  · cases h with
    | plain h => (cases h <;> (try (rename_i hh; cases hh))); rfl
  · cases h with
    | ref h => rfl

theorem AdminOk.throw_initsExn {s : Store H} {C : Context} {x : TagIdx} {it : InstrType}
    (h : AdminOk s C (.plain (.throw x)) it) : it.inits = [] := by
  cases h with
  | plain h => (cases h <;> (try (rename_i hh; cases hh))); rfl

theorem AdminOk.ref_initsExn {s : Store H} {C : Context} {r : Ref} {it : InstrType}
    (h : AdminOk s C (.ref r) it) : it.inits = [] := by
  cases h with
  | ref h => rfl

/-- `vals vs ++ [br l]` with the values typed below the label type. -/
theorem AdminsOk.brValsExn {s : Store H} {C : Context} {vs : List Val}
    {F lt T : List CValType} {l : LabelIdx}
    (hv : List.Forall₂ (ValOk s) vs F) (hF : ResultOk C.toTypeCtx F)
    (hl : C.labels[l.toNat]? = some lt) (hs : ResultSub C.toTypeCtx F lt)
    (hT : ResultOk C.toTypeCtx T) :
    AdminsOk s C (vals vs ++ [.plain (.br l)]) (.plain [] T) := by
  have h₁ := AdminsOk.of_vals (C := C) hv hF
  have h₂ : AdminsOk s C [.plain (.br l)] ⟨F, [], T⟩ :=
    .sub (.single (.plain (InstrOk.br (t₁ := []) hl ⟨by simp, hT, by simp⟩)))
      ⟨by simpa using hs, ResultSub.refl _ _, by simp⟩ ⟨hF, hT, by simp⟩
  exact AdminsOk.seq h₁ (by simp) h₂

/-! ## Exception rules -/

/-- `Step_read/throw_ref-null`. -/
theorem AdminsOk.pres_throwRefNullExn {s : Store H} {C : Context} {it : InstrType}
    (h : AdminsOk s C [.ref .null, .plain .throwRef] it) (hC : C.Wf) :
    AdminsOk s C [.trap] it := by
  have hp := h.params_ok hC
  have hr : ResultOk C.toTypeCtx it.results :=
    AdminsOk.results_okExn AdminOk.plain_resultsExn h hC rfl
  exact AdminsOk.trap_it ⟨hp.1, hr, hp.2⟩

/-- `Step/throw` (typing part): the new exception address is typed in the new store. -/
theorem AdminsOk.pres_throwExn {s : Store H} {C : Context} {it : InstrType} {x : TagIdx}
    {vs : List Val} {ta : Nat}
    (h : AdminsOk s C (vals vs ++ [.plain (.throw x)]) it) (hC : C.Wf) :
    AdminsOk (s.addExn ⟨ta, vs⟩) C (throwing s.exns.length) it := by
  have hi := h.inits_setExn (by
    intro b hb C' it' hb'
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb
      exact hb'.toAdmin_initsExn
    · simp only [List.mem_singleton] at hb
      subst hb
      exact hb'.throw_initsExn)
  have hp := (h.params_ok hC).1
  have hr : ResultOk C.toTypeCtx it.results :=
    AdminsOk.results_okExn (a := .plain (.throw x)) AdminOk.plain_resultsExn h hC (by simp [vals])
  have he : ∃ e, (s.addExn ⟨ta, vs⟩).exns[s.exns.length]? = some e :=
    ⟨⟨ta, vs⟩, by simp [Store.addExn]⟩
  exact AdminsOk.throwing_it he ⟨hp, hr, fun x hx => (hi x hx).elim fun _ h => ⟨_, h⟩⟩

/-- `Step_read/throw_ref-instrs`. (Needs the results valid and the locals initialised
by `it` already set: the discarded `rest` may initialise locals.) -/
theorem AdminsOk.pres_throwRefInstrsExn {s : Store H} {C : Context} {it : InstrType}
    {vs : List Val} {a : Nat} {rest : List Admin}
    (h : AdminsOk s C (vals vs ++ throwing a ++ rest) it) (hC : C.Wf)
    (hr : ResultOk C.toTypeCtx it.results)
    (hi : ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩) :
    AdminsOk s C (throwing a) it := by
  have hp := (h.params_ok hC).1
  have he := h.exn_existsExn (a := a) (by simp)
  exact AdminsOk.throwing_it he ⟨hp, hr, fun x hx => (hi x hx).elim fun _ h => ⟨_, h⟩⟩

/-- `Step_read/throw_ref-label`. -/
theorem AdminsOk.pres_throwRefLabelExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {cont : List Instr} {a : Nat}
    (h : AdminsOk s C [.label n cont (throwing a)] it) (hC : C.Wf) :
    AdminsOk s C (throwing a) it := by
  refine AdminsOk.replace1Exn (P := Context.Wf) (fun C xs hC => hC.initLocals xs)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' hC' ha => ?_) h hC rfl
  cases ha with
  | label hn hc hb =>
    have ht := (AdminsOk.params_ok hC' hc).1
    have hts := hb.throwing_resultsExn (Context.Wf.withLabelExn hC' ht)
    exact AdminsOk.throwingExn (hb.exn_existsExn (by simp)) ⟨by simp, hts, by simp⟩

/-- `Step_read/throw_ref-frame`. (Needs the results valid: a frame's result type is
only valid in the empty context.) -/
theorem AdminsOk.pres_throwRefFrameExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {fi : Frame} {a : Nat}
    (h : AdminsOk s C [.frame n fi (throwing a)] it) (hC : C.Wf)
    (hr : ResultOk C.toTypeCtx it.results) :
    AdminsOk s C (throwing a) it := by
  have hi := h.inits_setExn (by
    intro b hb C' it' hb'
    simp only [List.mem_singleton] at hb
    subst hb
    cases hb'; rfl)
  have hp := (h.params_ok hC).1
  obtain ⟨_, _, ha⟩ := h.mem_okExn _ (List.mem_singleton_self _)
  cases ha with
  | frame hf hn hb hok =>
    exact (AdminsOk.throwingExn (hb.exn_existsExn (by simp)) ⟨hp, hr, by simp⟩).to_itExn hp hr hi

/-- `Step_read/throw_ref-handler-empty`. -/
theorem AdminsOk.pres_throwRefHandlerEmptyExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {a : Nat}
    (h : AdminsOk s C [.handler n [] (throwing a)] it) (hC : C.Wf) :
    AdminsOk s C (throwing a) it := by
  refine AdminsOk.replace1Exn (P := Context.Wf) (fun C xs hC => hC.initLocals xs)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' hC' ha => ?_) h hC rfl
  cases ha with
  | handler hc hb =>
    have hT := hb.throwing_resultsExn hC'
    exact AdminsOk.throwingExn (hb.exn_existsExn (by simp)) ⟨by simp, hT, by simp⟩

/-- `Step_read/throw_ref-handler-next`. -/
theorem AdminsOk.pres_throwRefHandlerNextExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {c : Catch} {cs : List Catch} {a : Nat}
    (h : AdminsOk s C [.handler n (c :: cs) (throwing a)] it) :
    AdminsOk s C [.handler n cs (throwing a)] it := by
  refine AdminsOk.replace1Exn (P := fun _ => True) (fun _ _ _ => trivial)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' _ ha => ?_) h trivial rfl
  cases ha with
  | handler hc hb =>
    exact .single (.handler (fun c' h' => hc c' (List.mem_cons_of_mem _ h')) hb)

/-- `Step_read/throw_ref-handler-catch`. (Needs `hE`: the exception's fields are typed
at the parameters of the tag the clause names.) -/
theorem AdminsOk.pres_throwRefHandlerCatchExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch} {a : Nat} {e : ExnInst}
    (h : AdminsOk s C [.handler n (.catch_ x l :: cs) (throwing a)] it) (hC : C.Wf)
    (hE : ∀ d ts, C.tags[x.toNat]? = some d → Expand d (.func ts .nil) →
      List.Forall₂ (ValOk s) e.fields ts.toList) :
    AdminsOk s C (vals e.fields ++ [.plain (.br l)]) it := by
  refine AdminsOk.replace1Exn (P := fun C' => C'.Wf ∧ C'.tags = C.tags)
    (fun C xs hC => ⟨hC.1.initLocals xs, by rw [Context.initLocals_tagsExn]; exact hC.2⟩)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' hC' ha => ?_) h ⟨hC, rfl⟩ rfl
  cases ha with
  | handler hc hb =>
    have hT := hb.throwing_resultsExn hC'.1
    cases hc _ (List.mem_cons_self ..) with
    | catch_ hx he hl hs =>
      have hv := hE _ _ (hC'.2 ▸ hx) he
      have hF := (Expand.func_ok (hC'.1.tags _ (List.mem_of_getElem? hx)) he).1
      exact AdminsOk.brValsExn hv hF hl hs hT

/-- `Step_read/throw_ref-handler-catch_ref`. -/
theorem AdminsOk.pres_throwRefHandlerCatchRefExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {x : TagIdx} {l : LabelIdx} {cs : List Catch} {a : Nat} {e : ExnInst}
    (h : AdminsOk s C [.handler n (.catchRef x l :: cs) (throwing a)] it) (hC : C.Wf)
    (hex : s.exns[a]? = some e)
    (hE : ∀ d ts, C.tags[x.toNat]? = some d → Expand d (.func ts .nil) →
      List.Forall₂ (ValOk s) e.fields ts.toList) :
    AdminsOk s C (vals e.fields ++ [.ref (.exn a), .plain (.br l)]) it := by
  refine AdminsOk.replace1Exn (P := fun C' => C'.Wf ∧ C'.tags = C.tags)
    (fun C xs hC => ⟨hC.1.initLocals xs, by rw [Context.initLocals_tagsExn]; exact hC.2⟩)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' hC' ha => ?_) h ⟨hC, rfl⟩ rfl
  cases ha with
  | handler hc hb =>
    have hT := hb.throwing_resultsExn hC'.1
    cases hc _ (List.mem_cons_self ..) with
    | catchRef hx he hl hs =>
      have hv := hE _ _ (hC'.2 ▸ hx) he
      have hF := (Expand.func_ok (hC'.1.tags _ (List.mem_of_getElem? hx)) he).1
      have hv' : List.Forall₂ (ValOk s) (e.fields ++ [.ref (.exn a)])
          (_ ++ [.refT false (.abs .exn)]) :=
        forall₂_append hv (.cons (.ref (.exn hex)) .nil)
      have := AdminsOk.brValsExn hv' (ResultOk.append hF (by simp)) hl hs hT
      rw [vals_append, List.append_assoc] at this
      exact this

/-- `Step_read/throw_ref-handler-catch_all`. -/
theorem AdminsOk.pres_throwRefHandlerCatchAllExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {l : LabelIdx} {cs : List Catch} {a : Nat}
    (h : AdminsOk s C [.handler n (.catchAll l :: cs) (throwing a)] it) (hC : C.Wf) :
    AdminsOk s C [.plain (.br l)] it := by
  refine AdminsOk.replace1Exn (P := Context.Wf) (fun C xs hC => hC.initLocals xs)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' hC' ha => ?_) h hC rfl
  cases ha with
  | handler hc hb =>
    have hT := hb.throwing_resultsExn hC'
    cases hc _ (List.mem_cons_self ..) with
    | catchAll hl hs =>
      exact AdminsOk.brValsExn (vs := []) .nil (by simp) hl hs hT

/-- `Step_read/throw_ref-handler-catch_all_ref`. -/
theorem AdminsOk.pres_throwRefHandlerCatchAllRefExn {s : Store H} {C : Context}
    {it : InstrType} {n : Nat} {l : LabelIdx} {cs : List Catch} {a : Nat}
    (h : AdminsOk s C [.handler n (.catchAllRef l :: cs) (throwing a)] it) (hC : C.Wf) :
    AdminsOk s C [.ref (.exn a), .plain (.br l)] it := by
  refine AdminsOk.replace1Exn (P := Context.Wf) (fun C xs hC => hC.initLocals xs)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' hC' ha => ?_) h hC rfl
  cases ha with
  | handler hc hb =>
    have hT := hb.throwing_resultsExn hC'
    obtain ⟨e, hex⟩ := hb.exn_existsExn (a := a) (by simp)
    cases hc _ (List.mem_cons_self ..) with
    | catchAllRef hl hs =>
      exact AdminsOk.brValsExn (vs := [.ref (.exn a)]) (.cons (.ref (.exn hex)) .nil)
        (by simp; exact .ref (.abs .exn)) hl hs hT

/-! ## Trap rules -/

/-- `Step_pure/trap-instrs`. (Needs the results valid and the locals initialised by `it`
already set: the discarded `rest` may initialise locals.) -/
theorem AdminsOk.pres_trapInstrsExn {s : Store H} {C : Context} {it : InstrType}
    {vs : List Val} {rest : List Admin}
    (h : AdminsOk s C (vals vs ++ [.trap] ++ rest) it) (hC : C.Wf)
    (hr : ResultOk C.toTypeCtx it.results)
    (hi : ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩) :
    AdminsOk s C [.trap] it := by
  have hp := (h.params_ok hC).1
  exact AdminsOk.trap_it ⟨hp, hr, fun x hx => (hi x hx).elim fun _ h => ⟨_, h⟩⟩

/-- `Step_pure/trap-label`. -/
theorem AdminsOk.pres_trapLabelExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {cont : List Instr}
    (h : AdminsOk s C [.label n cont [.trap]] it) (hC : C.Wf) :
    AdminsOk s C [.trap] it := by
  refine AdminsOk.replace1Exn (P := Context.Wf) (fun C xs hC => hC.initLocals xs)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' hC' ha => ?_) h hC rfl
  cases ha with
  | label hn hc hb =>
    have ht := (AdminsOk.params_ok hC' hc).1
    have hts := hb.trap1_resultsExn (Context.Wf.withLabelExn hC' ht)
    exact .single (.trap ⟨by simp, hts, by simp⟩)

/-- `Step_pure/trap-handler`. -/
theorem AdminsOk.pres_trapHandlerExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {cs : List Catch}
    (h : AdminsOk s C [.handler n cs [.trap]] it) (hC : C.Wf) :
    AdminsOk s C [.trap] it := by
  refine AdminsOk.replace1Exn (P := Context.Wf) (fun C xs hC => hC.initLocals xs)
    (fun _ _ h => h.nil_storeExn s rfl) (fun C' it' hC' ha => ?_) h hC rfl
  cases ha with
  | handler hc hb =>
    have hT := hb.trap1_resultsExn hC'
    exact .single (.trap ⟨by simp, hT, by simp⟩)

/-- `Step_pure/trap-frame`. (Needs the results valid.) -/
theorem AdminsOk.pres_trapFrameExn {s : Store H} {C : Context} {it : InstrType}
    {n : Nat} {fi : Frame}
    (h : AdminsOk s C [.frame n fi [.trap]] it) (hC : C.Wf)
    (hr : ResultOk C.toTypeCtx it.results) :
    AdminsOk s C [.trap] it := by
  have hi := h.inits_setExn (by
    intro b hb C' it' hb'
    simp only [List.mem_singleton] at hb
    subst hb
    cases hb'; rfl)
  have hp := (h.params_ok hC).1
  exact AdminsOk.trap_it ⟨hp, hr, fun x hx => (hi x hx).elim fun _ h => ⟨_, h⟩⟩

/-! ## The store allocated by `throw` -/

/-- A reference mentions only exception addresses below `n` (through `extern`). -/
def RefFreeExn (n : Nat) : Ref → Prop
  | .exn a => a < n
  | .extern r => RefFreeExn n r
  | _ => True

def FVFreeExn (n : Nat) : FieldVal → Prop
  | .val (.ref r) => RefFreeExn n r
  | _ => True

theorem RefOk.freeExn {s : Store H} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
    RefFreeExn s.exns.length r := by
  induction h with
  | exn h => obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h; exact hlt
  | extern _ _ ih => exact ih
  | sub _ _ _ ih => exact ih
  | _ => trivial

theorem ValOk.freeExn {s : Store H} {v : Val} {t : CValType} (h : ValOk s v t) :
    FVFreeExn s.exns.length (.val v) := by
  cases h with
  | ref h => exact h.freeExn
  | _ => trivial

theorem FieldValOk.freeExn {s : Store H} {v : FieldVal} {t : CStorageType}
    (h : FieldValOk s v t) : FVFreeExn s.exns.length v := by
  cases h with
  | val h => exact h.freeExn
  | _ => trivial

theorem forall₂_exists_leftExn {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hr hl, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hr⟩
    · exact forall₂_exists_leftExn hl a h

/-- Reachability in `s.addExn e` from a value not mentioning the new address stays in `s`. -/
theorem ImmutReachable.oldExn {s : Store H} {e : ExnInst} (hs : StoreOk s) {x y : FieldVal}
    (h : ImmutReachable (s.addExn e) x y) (hx : FVFreeExn s.exns.length x) :
    ImmutReachable s x y ∧ FVFreeExn s.exns.length y := by
  induction h with
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨r₁, f₁⟩ := ih₁ hx
    obtain ⟨r₂, f₂⟩ := ih₂ f₁
    exact ⟨.trans r₁ r₂, f₂⟩
  | refStruct hs' he hi hfv =>
    refine ⟨.refStruct hs' he hi hfv, ?_⟩
    obtain ⟨fs, -, hf⟩ := hs.structs _ (List.mem_of_getElem? hs')
    obtain ⟨_, ht⟩ := forall₂_exists_leftExn hf _ (List.mem_of_getElem? hfv)
    exact ht.freeExn
  | refArray hs' he hfv =>
    refine ⟨.refArray hs' he hfv, ?_⟩
    obtain ⟨ft, -, hf⟩ := hs.arrays _ (List.mem_of_getElem? hs')
    exact (hf _ (List.mem_of_getElem? hfv)).freeExn
  | @refExn a i e' v hs' hv =>
    have ha : a < s.exns.length := hx
    have hs'' : s.exns[a]? = some e' := by
      simpa [Store.addExn, List.getElem?_append_left ha] using hs'
    refine ⟨.refExn hs'' hv, ?_⟩
    obtain ⟨ti, ts, -, -, hf⟩ := hs.exns _ (List.mem_of_getElem? hs'')
    obtain ⟨_, ht⟩ := forall₂_exists_leftExn hf _ (List.mem_of_getElem? hv)
    exact ht.freeExn
  | refExtern r => exact ⟨.refExtern r, hx⟩

/-- Everything reachable from the new exception (or from an old value) avoids the new address. -/
theorem ImmutReachable.newExn {s : Store H} {e : ExnInst} (hs : StoreOk s)
    (hv : ∀ v ∈ e.fields, FVFreeExn s.exns.length (.val v)) {x y : FieldVal}
    (h : ImmutReachable (s.addExn e) x y)
    (hx : x = .val (.ref (.exn s.exns.length)) ∨ FVFreeExn s.exns.length x) :
    FVFreeExn s.exns.length y := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact ih₂ (.inr (ih₁ hx))
  | refStruct hs' he hi hfv =>
    rcases hx with hx | hx
    · cases hx
    · exact (ImmutReachable.oldExn hs (.refStruct hs' he hi hfv) hx).2
  | refArray hs' he hfv =>
    rcases hx with hx | hx
    · cases hx
    · exact (ImmutReachable.oldExn hs (.refArray hs' he hfv) hx).2
  | @refExn a i e' v hs' hv' =>
    rcases hx with hx | hx
    · cases hx
      have : e' = e := by simpa [Store.addExn] using hs'.symm
      subst this
      exact hv v (List.mem_of_getElem? hv')
    · exact (ImmutReachable.oldExn hs (.refExn hs' hv') hx).2
  | refExtern r =>
    rcases hx with hx | hx
    · cases hx
    · exact (ImmutReachable.oldExn (e := e) hs (.refExtern r) hx).2

theorem Extend.addExnExn {s : Store H} (hs : StoreOk s) (e : ExnInst) :
    Extend s (s.addExn e) :=
  { Extend.refl hs with
    exns := ⟨by simp [Store.addExn], fun i x hx => ⟨x, by
      have hlt : i < s.exns.length := (List.getElem?_eq_some_iff.mp hx).1
      simp [Store.addExn, List.getElem?_append_left hlt, hx], rfl⟩⟩ }

/-- Allocating a well-typed exception instance keeps the store valid. -/
theorem StoreOk.addExnExn {s : Store H} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)}
    {vs : List Val} (hs : StoreOk s) (ht : s.tags[ta]? = some ti)
    (hx : Expand ti.type (.func ts .nil)) (hv : List.Forall₂ (ValOk s) vs ts.toList) :
    StoreOk (s.addExn ⟨ta, vs⟩) ∧ Extend s (s.addExn ⟨ta, vs⟩) := by
  have he := Extend.addExnExn hs ⟨ta, vs⟩
  have hfree : ∀ v ∈ vs, FVFreeExn s.exns.length (.val v) := fun v hm => by
    obtain ⟨_, h⟩ := forall₂_exists_leftExn hv v hm
    exact h.freeExn
  refine ⟨{ tags := hs.tags
            globals := fun gi h => ⟨(hs.globals gi h).1, (hs.globals gi h).2.extend he⟩
            mems := hs.mems
            tables := fun ti h =>
              ⟨(hs.tables ti h).1, (hs.tables ti h).2.1,
                fun r hr => ((hs.tables ti h).2.2 r hr).extend he⟩
            funcs := fun fi h => by
              cases hs.funcs fi h with
              | wasm hdt hm hcode hf hsub => exact .wasm hdt (hm.extend hs he) hcode hf hsub
              | host hdt he' hcode => exact .host hdt he' hcode
            elems := fun ei h => (hs.elems ei h).extend he ⟨rfl, .inl rfl⟩
            structs := fun si h => by
              obtain ⟨fs, hx, hf⟩ := hs.structs si h
              exact ⟨fs, hx, hf.imp fun _ _ h => h.extend he⟩
            arrays := fun ai h => by
              obtain ⟨ft, hx, hf⟩ := hs.arrays ai h
              exact ⟨ft, hx, fun fv hfv => (hf fv hfv).extend he⟩
            exns := fun e' h => by
              simp only [Store.addExn, List.mem_append, List.mem_singleton] at h
              rcases h with h | rfl
              · obtain ⟨ti', ts', ht', hx', hf'⟩ := hs.exns e' h
                exact ⟨ti', ts', ht', hx', hf'.imp fun _ _ h => h.extend he⟩
              · exact ⟨ti, ts, ht, hx, hv.imp fun _ _ h => h.extend he⟩
            acyclicStructs := fun a ha hr =>
              hs.acyclicStructs a ha (ImmutReachable.oldExn hs hr trivial).1
            acyclicArrays := fun a ha hr =>
              hs.acyclicArrays a ha (ImmutReachable.oldExn hs hr trivial).1
            acyclicExns := fun a ha hr => by
              have hfa : FVFreeExn s.exns.length (.val (.ref (.exn a))) := by
                refine ImmutReachable.newExn hs hfree hr ?_
                by_cases h : a = s.exns.length
                · exact .inl (by rw [h])
                · refine .inr ?_
                  show a < s.exns.length
                  simp [Store.addExn] at ha
                  omega
              exact hs.acyclicExns a hfa (ImmutReachable.oldExn hs hr hfa).1
            structsClosed := hs.structsClosed
            arraysClosed := hs.arraysClosed }, he⟩

/-- `Step/throw` (store part), with the premises of the rule. -/
theorem StoreOk.throwExn {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat}
    {ti : TagInst} {ts : Ty (.list .val)} (hs : StoreOk s) (ht : s.tag? f x = some (ta, ti))
    (hx : Expand ti.type (.func ts .nil)) (hv : List.Forall₂ (ValOk s) vs ts.toList) :
    StoreOk (s.addExn ⟨ta, vs⟩) ∧ Extend s (s.addExn ⟨ta, vs⟩) := by
  have ht' : s.tags[ta]? = some ti := by
    simp only [Store.tag?] at ht
    cases h₁ : f.module.tags[x.toNat]? with
    | none => simp [h₁] at ht
    | some a =>
      cases h₂ : s.tags[a]? with
      | none => simp [h₁, h₂] at ht
      | some ti' =>
        simp [h₁, h₂] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact h₂
  exact StoreOk.addExnExn hs ht' hx hv

end Silmaril.Wasm.Execution.Core
