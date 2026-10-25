module

public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Execution.Core.Soundness.PureRedex
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryAux
public import Silmaril.Wasm.Execution.Core.Soundness.RefRetypeClosed
public import Silmaril.Wasm.Execution.Core.Soundness.CallRefDef
public import Silmaril.Wasm.Execution.Core.Soundness.ValToClosed
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping

@[expose] public section

/-! # Progress for Core 3.0: control, calls, exceptions and the code induction

Progress is proved by one induction on the typing derivation of administrative
code (`AdminsOk`, mutually with `AdminOk`), generalised over

* the frame (the body of a `FRAME` runs in its own frame),
* a prefix of values typed by (subtypes of) the parameters of the code, and
* the typing context, related to the frame by `CtxOk`: its labels and return
  type are those of the enclosing `LABEL`s / `FRAME`, which is what makes
  `br l` / `return` well-scoped.

The outcome (`Out`) of a typed piece of code is: a value sequence (typed by the
results), a step, or one of the *exit forms* that the enclosing administrative
instruction consumes: a trap, a thrown exception, a branch to an enclosing
label with enough operands, a `return` with enough operands, or a pending tail
call (`return_call_ref`) whose callee data the enclosing frame needs.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## List plumbing -/

theorem vals_snoc_append (vs : List Val) (v : Val) (l : List Admin) :
    vals (vs ++ [v]) ++ l = vals vs ++ (v.toAdmin :: l) := by
  simp [vals]

theorem vals_append_eq_vals {vs₀ vs₁ : List Val} {l : List Admin}
    (h : vals vs₀ ++ l = vals vs₁) : ∃ w, l = vals w := by
  unfold vals at h
  obtain ⟨_, l₂, -, -, e⟩ := List.map_eq_append_iff.mp h.symm
  exact ⟨l₂, e.symm⟩

theorem ValsTo.sub {s : Store H} {Δ : TypeCtx} {vs : List Val} {ts ts' : List CValType}
    (h : ValsTo s Δ vs ts) (hs : List.Forall₂ (Sub Δ) ts ts') : ValsTo s Δ vs ts' := by
  induction h generalizing ts' with
  | nil => cases hs; exact .nil
  | cons ha _ ih =>
    cases hs with
    | cons hb hs =>
      obtain ⟨t₀, hv, hc⟩ := ha
      exact .cons ⟨t₀, hv, hc.tail hb⟩ (ih hs)

theorem ValTo.addr_inv {s : Store H} {Δ : TypeCtx} {v : Val} {a : AddrType}
    (h : ValTo s Δ v a.valType) : ∃ i, v.toAdmin = aconst a i :=
  ValOk.addr_inv (h.valOk_of_numVec (by cases a <;> simp [numVec, AddrType.valType]))

theorem ValTo.i32_inv' {s : Store H} {Δ : TypeCtx} {v : Val} (h : ValTo s Δ v Ty.i32) :
    ∃ i, v.toAdmin = constI32 i :=
  ValOk.i32_inv (h.valOk_of_numVec (by simp [numVec, Ty.i32]))

/-! ## Context transport -/

theorem ctx_fields_eq {C Cf : Context} {L : List (List CValType)} {R : Option (List CValType)}
    {ls : List LocalType} (hC : C = { Cf with labels := L, return_ := R, locals := ls }) :
    C.toTypeCtx = Cf.toTypeCtx ∧ C.tags = Cf.tags ∧ C.funcs = Cf.funcs ∧
      C.globals = Cf.globals ∧ C.types = Cf.types := by
  subst hC; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

section Transport

variable {C Cf : Context} {L : List (List CValType)} {R : Option (List CValType)}
  {ls : List LocalType} {i : Instr} {it : InstrType}

theorem NumericInstrOk.transport' (hC : C = { Cf with labels := L, return_ := R, locals := ls })
    (h : NumericInstrOk C i it) : NumericInstrOk Cf i it := by
  subst hC; exact NumericInstrOk.transport h

theorem VectorInstrOk.transport' (hC : C = { Cf with labels := L, return_ := R, locals := ls })
    (h : VectorInstrOk C i it) : VectorInstrOk Cf i it := by
  subst hC; exact VectorInstrOk.transport h

theorem MemoryInstrOk.transport' (hC : C = { Cf with labels := L, return_ := R, locals := ls })
    (h : MemoryInstrOk C i it) : MemoryInstrOk Cf i it := by
  subst hC; exact MemoryInstrOk.transport h

theorem TableInstrOk.transport' (hC : C = { Cf with labels := L, return_ := R, locals := ls })
    (h : TableInstrOk C i it) : TableInstrOk Cf i it := by
  subst hC; exact TableInstrOk.transport h

theorem RefInstrOk.transport' (hC : C = { Cf with labels := L, return_ := R, locals := ls })
    (h : RefInstrOk C i it) : RefInstrOk Cf i it := by
  subst hC; exact RefInstrOk.transport h

end Transport

/-! ## Outcomes of typed code -/

/-- Callee data a frame needs for a pending tail call `vals vs ++ [ref r, return_call_ref]`. -/
def RCOk (s : Store H) (vs : List Val) (r : Ref) : Prop :=
  r = .null ∨ ∃ (a : Nat) (fn : FuncInst H) (ps rs : Ty (.list .val)), r = .func a ∧
    s.funcs[a]? = some fn ∧ Expand fn.type (.func ps rs) ∧ ps.length ≤ vs.length

/-- Non-value outcomes: a step, or an exit form. -/
def OutN (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (L : List (List CValType)) (R : Option (List CValType)) (code : List Admin) : Prop :=
  (∃ c', Step P host ⟨s, f, code⟩ c') ∨
  (∃ vs rest, code = vals vs ++ [.trap] ++ rest) ∨
  (∃ vs a rest, code = vals vs ++ throwing a ++ rest) ∨
  (∃ vs l rest tl, code = vals vs ++ [.plain (.br l)] ++ rest ∧ L[l.toNat]? = some tl ∧
    tl.length ≤ vs.length) ∨
  (∃ vs rest rt, code = vals vs ++ [.plain .return_] ++ rest ∧ R = some rt ∧
    rt.length ≤ vs.length) ∨
  (∃ vs r c rest rt, code = vals vs ++ [.ref r, c] ++ rest ∧ c.IsReturnCallRef ∧
    R = some rt ∧ RCOk s vs r)

/-- Outcomes of typed code: values of the result types, or a non-value outcome. -/
def Out (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (Δ : TypeCtx)
    (L : List (List CValType)) (R : Option (List CValType)) (code : List Admin)
    (ts : List CValType) : Prop :=
  (∃ vs, code = vals vs ∧ ValsTo s Δ vs ts) ∨ OutN P host s f L R code

section Outcomes

variable {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {L : List (List CValType)} {R : Option (List CValType)}

theorem RCOk.mono {vs : List Val} {r : Ref} (h : RCOk s vs r) (vs₀ : List Val) :
    RCOk s (vs₀ ++ vs) r := by
  rcases h with h | ⟨a, fn, ps, rs, h1, h2, h3, h4⟩
  · exact .inl h
  · exact .inr ⟨a, fn, ps, rs, h1, h2, h3, by simp; omega⟩

theorem RCOk.of_inv (va : List Val) {vb : List Val} {r : Ref}
    (h : r = .null ∨ ∃ (a : Nat) (fi : FuncInst H) (ps' rs' : Ty (.list .val)), r = .func a ∧
      s.funcs[a]? = some fi ∧ Expand fi.type (.func ps' rs') ∧
      List.Forall₂ (ValOk s) vb ps'.toList) :
    RCOk s (va ++ vb) r := by
  rcases h with rfl | ⟨a, fi, ps', rs', rfl, hfi, he, hv⟩
  · exact .inl rfl
  · refine .inr ⟨a, fi, ps', rs', rfl, hfi, he, ?_⟩
    have := hv.length_eq
    simp only [Ty.length, List.length_append]
    omega

theorem OutN.append {code : List Admin} (h : OutN P host s f L R code) (rest : List Admin) :
    OutN P host s f L R (code ++ rest) := by
  rcases h with ⟨c', hc⟩ | ⟨vs, r, rfl⟩ | ⟨vs, a, r, rfl⟩ | ⟨vs, l, r, tl, rfl, h1, h2⟩ |
    ⟨vs, r, rt, rfl, h1, h2⟩ | ⟨vs, rr, c, r, rt, rfl, h1, h2, h3⟩
  · obtain ⟨c'', h⟩ := Step.inCtx (vs := []) (rest := rest) hc
    exact .inl ⟨c'', by simpa [vals] using h⟩
  · exact .inr (.inl ⟨vs, r ++ rest, by simp⟩)
  · exact .inr (.inr (.inl ⟨vs, a, r ++ rest, by simp⟩))
  · exact .inr (.inr (.inr (.inl ⟨vs, l, r ++ rest, tl, by simp, h1, h2⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨vs, r ++ rest, rt, by simp, h1, h2⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨vs, rr, c, r ++ rest, rt, by simp, h1, h2, h3⟩))))

theorem OutN.prepend {code : List Admin} (h : OutN P host s f L R code) (vs₀ : List Val) :
    OutN P host s f L R (vals vs₀ ++ code) := by
  rcases h with ⟨c', hc⟩ | ⟨vs, r, rfl⟩ | ⟨vs, a, r, rfl⟩ | ⟨vs, l, r, tl, rfl, h1, h2⟩ |
    ⟨vs, r, rt, rfl, h1, h2⟩ | ⟨vs, rr, c, r, rt, rfl, h1, h2, h3⟩
  · obtain ⟨c'', h⟩ := Step.inCtx (vs := vs₀) (rest := []) hc
    exact .inl ⟨c'', by simpa using h⟩
  · exact .inr (.inl ⟨vs₀ ++ vs, r, by simp⟩)
  · exact .inr (.inr (.inl ⟨vs₀ ++ vs, a, r, by simp⟩))
  · exact .inr (.inr (.inr (.inl ⟨vs₀ ++ vs, l, r, tl, by simp, h1, by simp; omega⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨vs₀ ++ vs, r, rt, by simp, h1, by simp; omega⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨vs₀ ++ vs, rr, c, r, rt, by simp, h1, h2,
      h3.mono vs₀⟩))))

theorem Out.prepend {Δ : TypeCtx} {code : List Admin} {ts ts₀ : List CValType} {vs₀ : List Val}
    (h : Out P host s f Δ L R code ts) (hv : ValsTo s Δ vs₀ ts₀) :
    Out P host s f Δ L R (vals vs₀ ++ code) (ts₀ ++ ts) := by
  rcases h with ⟨vs, rfl, hv'⟩ | h
  · exact .inl ⟨vs₀ ++ vs, by simp, forall₂_append hv hv'⟩
  · exact .inr (h.prepend vs₀)

theorem Out.sub {Δ : TypeCtx} {code : List Admin} {ts ts' : List CValType}
    (h : Out P host s f Δ L R code ts) (hs : List.Forall₂ (Sub Δ) ts ts') :
    Out P host s f Δ L R code ts' := by
  rcases h with ⟨vs, e, hv⟩ | h
  · exact .inl ⟨vs, e, hv.sub hs⟩
  · exact .inr h

theorem trap_or_step (vs : List Val) (rest : List Admin) :
    (vs = [] ∧ rest = []) ∨ ∃ c', Step P host ⟨s, f, vals vs ++ [.trap] ++ rest⟩ c' := by
  by_cases h : vs = [] ∧ rest = []
  · exact .inl h
  · exact .inr ⟨_, .trapInstrs (not_and_or.mp h)⟩

theorem throw_or_step (vs : List Val) (a : Nat) (rest : List Admin) :
    (vs = [] ∧ rest = []) ∨ ∃ c', Step P host ⟨s, f, vals vs ++ throwing a ++ rest⟩ c' := by
  by_cases h : vs = [] ∧ rest = []
  · exact .inl h
  · exact .inr ⟨_, .throwRefInstrs (not_and_or.mp h)⟩

theorem value_out {C : Context} {Δ : TypeCtx} {a : Admin} {it : InstrType} {v : Val}
    {vs₀ : List Val} (ha : AdminOk s C a it) (hva : a.val? = some v)
    (hv : ValsTo s Δ vs₀ it.params) :
    Out P host s f Δ L R (vals vs₀ ++ [a]) it.results := by
  obtain rfl := Admin.eq_of_val? hva
  obtain ⟨hp, -, tv, hr, hvt⟩ := AdminOk.val_inv ha
  rw [hp] at hv
  cases hv
  rw [hr]
  exact .inl ⟨[v], rfl, .cons ⟨tv, hvt, .refl⟩ .nil⟩

end Outcomes

/-! ## Administrative instructions over stuck bodies -/

section Admin

variable {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {L : List (List CValType)} {R : Option (List CValType)}

theorem vals_ref_call_eq (vs : List Val) (r : Ref) (c : Admin) (rest : List Admin) :
    vals vs ++ [Admin.ref r, c] ++ rest = vals (vs ++ [.ref r]) ++ [c] ++ rest := by
  simp [vals, Val.toAdmin]

theorem label_step {Δ : TypeCtx} {n : Nat} {cont : List Instr} {body : List Admin}
    {t' ts : List CValType} (hn : t'.length = n) (h : Out P host s f Δ (t' :: L) R body ts) :
    ∃ c', Step P host ⟨s, f, [.label n cont body]⟩ c' := by
  rcases h with ⟨vs, rfl, -⟩ | ⟨⟨s', f', is'⟩, hc⟩ | ⟨vs, rest, rfl⟩ | ⟨vs, a, rest, rfl⟩ |
    ⟨vs, l, rest, tl, rfl, h1, h2⟩ | ⟨vs, rest, rt, rfl, h1, h2⟩ |
    ⟨vs, r, c, rest, rt, rfl, h1, h2, h3⟩
  · exact ⟨_, .labelVals⟩
  · exact ⟨_, .ctxtLabel hc⟩
  · rcases trap_or_step (P := P) (host := host) (s := s) (f := f) vs rest with
      ⟨rfl, rfl⟩ | ⟨⟨s', f', is'⟩, hc⟩
    · exact ⟨_, .trapLabel⟩
    · exact ⟨_, .ctxtLabel hc⟩
  · rcases throw_or_step (P := P) (host := host) (s := s) (f := f) vs a rest with
      ⟨rfl, rfl⟩ | ⟨⟨s', f', is'⟩, hc⟩
    · exact ⟨_, .throwRefLabel⟩
    · exact ⟨_, .ctxtLabel hc⟩
  · by_cases hl : l.toNat = 0
    · rw [hl] at h1
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
      subst h1
      obtain ⟨vs₁, vs₂, rfl, hlen⟩ := List.exists_split_right vs n (by omega)
      rw [vals_append]
      exact ⟨_, .brLabelZero hl hlen⟩
    · exact ⟨_, .brLabelSucc (by omega)⟩
  · exact ⟨_, .returnLabel⟩
  · rw [vals_ref_call_eq]
    exact ⟨_, .returnCallRefLabel h1⟩

theorem handler_throw (n : Nat) (cs : List Catch) (a : Nat) :
    ∃ c', Step P host ⟨s, f, [.handler n cs (throwing a)]⟩ c' := by
  cases cs with
  | nil => exact ⟨_, .throwRefHandlerEmpty⟩
  | cons c cs =>
    by_cases hm : CatchMatches s f a c
    · cases c with
      | catch_ x l =>
        obtain ⟨e, ta, he, ht, rfl⟩ := hm
        exact ⟨_, .throwRefHandlerCatch he ht⟩
      | catchRef x l =>
        obtain ⟨e, ta, he, ht, rfl⟩ := hm
        exact ⟨_, .throwRefHandlerCatchRef he ht⟩
      | catchAll l => exact ⟨_, .throwRefHandlerCatchAll⟩
      | catchAllRef l => exact ⟨_, .throwRefHandlerCatchAllRef⟩
    · exact ⟨_, .throwRefHandlerNext hm⟩

theorem handler_step {Δ : TypeCtx} {n : Nat} {cs : List Catch} {body : List Admin}
    {ts : List CValType} (h : Out P host s f Δ L R body ts) :
    ∃ c', Step P host ⟨s, f, [.handler n cs body]⟩ c' := by
  rcases h with ⟨vs, rfl, -⟩ | ⟨⟨s', f', is'⟩, hc⟩ | ⟨vs, rest, rfl⟩ | ⟨vs, a, rest, rfl⟩ |
    ⟨vs, l, rest, tl, rfl, h1, h2⟩ | ⟨vs, rest, rt, rfl, h1, h2⟩ |
    ⟨vs, r, c, rest, rt, rfl, h1, h2, h3⟩
  · exact ⟨_, .handlerVals⟩
  · exact ⟨_, .ctxtHandler hc⟩
  · rcases trap_or_step (P := P) (host := host) (s := s) (f := f) vs rest with
      ⟨rfl, rfl⟩ | ⟨⟨s', f', is'⟩, hc⟩
    · exact ⟨_, .trapHandler⟩
    · exact ⟨_, .ctxtHandler hc⟩
  · rcases throw_or_step (P := P) (host := host) (s := s) (f := f) vs a rest with
      ⟨rfl, rfl⟩ | ⟨⟨s', f', is'⟩, hc⟩
    · exact handler_throw n cs a
    · exact ⟨_, .ctxtHandler hc⟩
  · exact ⟨_, .brHandler⟩
  · exact ⟨_, .returnHandler⟩
  · rw [vals_ref_call_eq]
    exact ⟨_, .returnCallRefHandler h1⟩

theorem frame_step {fr : Frame} {Δ : TypeCtx} {n : Nat} {body : List Admin}
    {ts : List CValType} (hL : L = []) (hn : ts.length = n)
    (h : Out P host s fr Δ L (some ts) body ts) :
    ∃ c', Step P host ⟨s, f, [.frame n fr body]⟩ c' := by
  subst hL
  rcases h with ⟨vs, rfl, hv⟩ | ⟨⟨s', f', is'⟩, hc⟩ | ⟨vs, rest, rfl⟩ | ⟨vs, a, rest, rfl⟩ |
    ⟨vs, l, rest, tl, rfl, h1, h2⟩ | ⟨vs, rest, rt, rfl, h1, h2⟩ |
    ⟨vs, r, c, rest, rt, rfl, h1, h2, h3⟩
  · exact ⟨_, .frameVals (hv.length_eq.trans hn)⟩
  · exact ⟨_, .ctxtFrame hc⟩
  · rcases trap_or_step (P := P) (host := host) (s := s) (f := fr) vs rest with
      ⟨rfl, rfl⟩ | ⟨⟨s', f', is'⟩, hc⟩
    · exact ⟨_, .trapFrame⟩
    · exact ⟨_, .ctxtFrame hc⟩
  · rcases throw_or_step (P := P) (host := host) (s := s) (f := fr) vs a rest with
      ⟨rfl, rfl⟩ | ⟨⟨s', f', is'⟩, hc⟩
    · exact ⟨_, .throwRefFrame⟩
    · exact ⟨_, .ctxtFrame hc⟩
  · simp at h1
  · obtain rfl := Option.some.inj h1
    obtain ⟨vs₁, vs₂, rfl, hlen⟩ := List.exists_split_right vs n (by omega)
    rw [vals_append]
    exact ⟨_, .returnFrame hlen⟩
  · rcases h3 with rfl | ⟨a, fn, ps, rs, rfl, hfn, he, hle⟩
    · exact ⟨_, .returnCallRefFrameNull h1⟩
    · obtain ⟨vs₁, vs₂, rfl, hlen⟩ := List.exists_split_right vs ps.length hle
      rw [vals_append]
      exact ⟨_, .returnCallRefFrameAddr h1 hfn he hlen⟩

end Admin

/-! ## Per-instruction progress -/

section Instr

variable {P : Profile} {host : HostSemantics H}

/-- `call_ref` (either representation) on a typed callee. -/
theorem callRef_step {s : Store H} {f : Frame} (hhost : HostOk host) (hs : StoreOk s)
    {c : Admin} (hc : c.IsCallRef) {vs : List Val} {r : Ref}
    (h : r = .null ∨ ∃ (a : Nat) (fi : FuncInst H) (ps' rs' : Ty (.list .val)), r = .func a ∧
      s.funcs[a]? = some fi ∧ Expand fi.type (.func ps' rs') ∧
      List.Forall₂ (ValOk s) vs ps'.toList) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.ref r, c]⟩ c' := by
  rcases h with rfl | ⟨a, fi, ps', rs', rfl, hfi, he, hvs⟩
  · exact Step.under_vals vs (.callRefNull hc)
  · have hn : vs.length = ps'.length := hvs.length_eq
    cases hcode : fi.code with
    | wasm code => exact ⟨_, .callRefFunc hc hfi he hn hcode⟩
    | host h =>
      obtain ⟨⟨out, hout⟩, -⟩ :=
        hhost s fi h vs ps' rs' hs (List.mem_of_getElem? hfi) hcode he hvs
      cases out with
      | returned s' r => exact ⟨_, .callRefHost hc hfi he hn hcode hout⟩
      | diverged => exact ⟨_, .callRefHostDiv hc hfi he hn hcode hout⟩

/-- Parametric progress with operands typed up to subtyping chains. -/
theorem ParametricInstrOk.progressTo {s : Store H} {f : Frame} {Δ : TypeCtx} {C : Context}
    {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat} {vs : List Val}
    (hi : ParametricInstrOk C i ⟨t₁, xs, t₂⟩) (hvs : ValsTo s Δ vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | nop => cases hvs; exact ⟨_, .parametric .nop⟩
  | unreachable _ => exact Step.under_vals vs (.parametric .unreachable)
  | drop _ =>
    obtain ⟨v, rfl, -⟩ := forall₂_one hvs
    exact ⟨_, .parametric (.drop v)⟩
  | selectExpl _ =>
    obtain ⟨v₁, v₂, v₃, rfl, -, -, h3⟩ := forall₂_three hvs
    obtain ⟨b, rfl⟩ := ValTo.i32 h3
    by_cases hb : b = 0
    · subst hb; exact ⟨_, .parametric (.selectFalse _ _ _)⟩
    · exact ⟨_, .parametric (.selectTrue hb)⟩
  | selectImpl _ _ _ =>
    obtain ⟨v₁, v₂, v₃, rfl, -, -, h3⟩ := forall₂_three hvs
    obtain ⟨b, rfl⟩ := ValTo.i32 h3
    by_cases hb : b = 0
    · subst hb; exact ⟨_, .parametric (.selectFalse _ _ _)⟩
    · exact ⟨_, .parametric (.selectTrue hb)⟩

/-- Table progress with operands typed up to subtyping chains. -/
theorem TableInstrOk.progressTo {s : Store H} {f : Frame} {C : Context} {i : Instr}
    {t₁ t₂ : List CValType} {xs : List Nat} {vs : List Val} {Δ : TypeCtx}
    (hst : StateOk s f C) (hi : TableInstrOk C i ⟨t₁, xs, t₂⟩)
    (hvs : ValsTo s Δ vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | tableGet h =>
    obtain ⟨v, rfl, hv⟩ := forall₂_one hvs
    obtain ⟨b, hb⟩ := ValTo.addr_inv hv
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hlt : b.toNat < ti.refs.length
    · exact ⟨_, .table (.getVal ht (List.getElem?_eq_getElem hlt))⟩
    · exact ⟨_, .table (.getOob ht (by omega))⟩
  | tableSet h =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨b, hb⟩ := ValTo.addr_inv hv₁
    obtain ⟨r, rfl⟩ := ValTo.ref hv₂
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hlt : b.toNat < ti.refs.length
    · exact ⟨_, .table (.setVal ht hlt)⟩
    · exact ⟨_, .table (.setOob ht (by omega))⟩
  | tableSize h =>
    obtain ⟨⟩ := hvs
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    exact ⟨_, .table (.size ht)⟩
  | tableGrow h =>
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := forall₂_two hvs
    obtain ⟨r, rfl⟩ := ValTo.ref hv₁
    obtain ⟨b, hb⟩ := ValTo.addr_inv hv₂
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb]
    by_cases hf : P.growMayFail .table ta ti.refs.length b.toNat
    · exact ⟨_, .table (.growFail ht (.inl hf))⟩
    · cases hg : ti.grow? b.toNat r with
      | none => exact ⟨_, .table (.growFail ht (.inr hg))⟩
      | some ti' =>
        exact ⟨_, .table (.growSucceed ht hg (Profile.growMaySucceed_of_not_fail hf))⟩
  | tableFill h =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b, hb⟩ := ValTo.addr_inv hv₁
    obtain ⟨n, hn⟩ := ValTo.addr_inv hv₃
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb, hn]
    by_cases hoob : ti.refs.length < b.toNat + n.toNat
    · exact ⟨_, .table (.fillOob ht hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .table (.fillZero ht (by simp at hoob; omega))⟩
      · exact ⟨_, .table (.fillSucc ht (by omega) hz)⟩
  | tableCopy h₁ h₂ hs =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b₁, hb₁⟩ := ValTo.addr_inv hv₁
    obtain ⟨b₂, hb₂⟩ := ValTo.addr_inv hv₂
    obtain ⟨n, hn⟩ := ValTo.addr_inv hv₃
    obtain ⟨ta₁, ti₁, ht₁, -⟩ := hst.table h₁
    obtain ⟨ta₂, ti₂, ht₂, -⟩ := hst.table h₂
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb₁, hb₂,
      hn]
    by_cases hoob : ti₁.refs.length < b₁.toNat + n.toNat ∨ ti₂.refs.length < b₂.toNat + n.toNat
    · exact ⟨_, .table (.copyOob ht₁ ht₂ hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .table (.copyZero ht₁ ht₂ (by simp at hoob; omega))⟩
      · by_cases hle : b₁.toNat ≤ b₂.toNat
        · exact ⟨_, .table (.copyLe ht₁ ht₂ (by omega) hz hle)⟩
        · exact ⟨_, .table (.copyGt ht₁ ht₂ (by omega) hz (by omega))⟩
  | tableInit h he hs =>
    obtain ⟨v₁, v₂, v₃, rfl, hv₁, hv₂, hv₃⟩ := forall₂_three hvs
    obtain ⟨b, hb⟩ := ValTo.addr_inv hv₁
    obtain ⟨j, hj⟩ := ValTo.i32_inv' hv₂
    obtain ⟨n, hn⟩ := ValTo.i32_inv' hv₃
    obtain ⟨ta, ti, ht, -⟩ := hst.table h
    obtain ⟨ea, ei, hei, -⟩ := hst.elem he
    simp only [vals, List.map_cons, List.map_nil, List.cons_append, List.nil_append, hb, hj, hn]
    by_cases hoob : ti.refs.length < b.toNat + n.toNat ∨ ei.refs.length < j.toNat + n.toNat
    · exact ⟨_, .table (.initOob ht hei hoob)⟩
    · by_cases hz : n = 0
      · subst hz
        exact ⟨_, .table (.initZero ht hei (by simp at hoob; omega))⟩
      · have hn0 := BitVec.toNat_ne_zero hz
        exact ⟨_, .table (.initSucc ht hei (by omega) hz
          (List.getElem?_eq_getElem (by omega)))⟩
  | elemDrop he =>
    obtain ⟨⟩ := hvs
    obtain ⟨ea, ei, hei, -⟩ := hst.elem he
    exact ⟨_, .table (.elemDrop hei)⟩

/-- Variable instructions. -/
theorem variable_progress {s : Store H} {f : Frame} {C Cf : Context} (hst : StateOk s f Cf)
    (hc : CtxOk s f C) (hglobals : C.globals = Cf.globals) {i : Instr}
    {t₁ t₂ : List CValType} {xs : List Nat} {vs : List Val} {Δ : TypeCtx}
    (hi : VariableInstrOk C i ⟨t₁, xs, t₂⟩) (hv : ValsTo s Δ vs t₁) :
    ∃ c', Step P host ⟨s, f, vals vs ++ [.plain i]⟩ c' := by
  cases hi with
  | localGet h =>
    cases hv
    obtain ⟨v, hv⟩ := hc.set _ _ h
    exact ⟨_, .variable (.localGet hv)⟩
  | localSet h =>
    obtain ⟨v, rfl, -⟩ := forall₂_one hv
    have hlt := (List.getElem?_eq_some_iff.mp h).1
    exact ⟨_, .variable (.localSet (by rw [← hc.len]; exact hlt))⟩
  | localTee h =>
    obtain ⟨v, rfl, -⟩ := forall₂_one hv
    exact ⟨_, .variable .localTee⟩
  | globalGet h =>
    cases hv
    rw [hglobals] at h
    obtain ⟨a, g, hg⟩ := StateOk.global? hst h
    exact ⟨_, .variable (.globalGet hg)⟩
  | globalSet h =>
    obtain ⟨v, rfl, -⟩ := forall₂_one hv
    rw [hglobals] at h
    obtain ⟨a, g, hg⟩ := StateOk.global? hst h
    exact ⟨_, .variable (.globalSet hg)⟩

/-- A plain (non-value) instruction applied to operands of its parameter types. -/
theorem plain_progress {s : Store H} {f : Frame} (hhost : HostOk host) (hs : StoreOk s)
    {C : Context} {i : Instr} {t₁ t₂ : List CValType} {xs : List Nat}
    (hi : InstrOk C i ⟨t₁, xs, t₂⟩) (hnv : (Admin.plain i).val? = none) (hc : CtxOk s f C)
    {vs : List Val} (hv : ValsTo s C.toTypeCtx vs t₁) :
    OutN P host s f C.labels C.return_ (vals vs ++ [.plain i]) := by
  obtain ⟨Cf, hst, hC⟩ := hc.stateOk hs
  obtain ⟨hΔ, htags, hfuncs, hglobals, -⟩ := ctx_fields_eq hC
  have hty : C.types = f.module.types := hc.types
  rw [hΔ] at hv
  cases hi with
  | parametric h => exact .inl (ParametricInstrOk.progressTo h hv)
  | numeric h =>
    obtain ⟨_, _, _, h', hv'⟩ := NumericInstrOk.retype hst (NumericInstrOk.transport' hC h) hv
    exact .inl (NumericInstrOk.progress hst h' hv' hnv)
  | vector h =>
    obtain ⟨_, _, _, h', hv'⟩ := VectorInstrOk.retype hst (VectorInstrOk.transport' hC h) hv
    exact .inl (VectorInstrOk.progress hst h' hv' hnv)
  | memory h =>
    obtain ⟨_, _, _, h', hv'⟩ := MemoryInstrOk.retype hst (MemoryInstrOk.transport' hC h) hv
    exact .inl (MemoryInstrOk.progress hst h' hv')
  | table h => exact .inl (TableInstrOk.progressTo hst (TableInstrOk.transport' hC h) hv)
  | reference h =>
    obtain ⟨_, _, _, h', hv'⟩ := RefInstrOk.retype hst (RefInstrOk.transport' hC h) hv
    by_cases ha : i.IsAggregate
    · exact .inl (RefInstrOk.progress_aggregate hst h' ha hv')
    · exact .inl (RefInstrOk.progress_ref hst h' ha hv')
  | «variable» h => exact .inl (variable_progress hst hc hglobals h hv)
  | block hbt hb =>
    obtain ⟨t₁', t₂', hbt', hl₁, -⟩ := blockType_of_types hty hbt
    exact .inl ⟨_, .block hbt' (hv.length_eq.trans hl₁.symm)⟩
  | loop hbt hb =>
    obtain ⟨t₁', t₂', hbt', hl₁, -⟩ := blockType_of_types hty hbt
    exact .inl ⟨_, .loop hbt' (hv.length_eq.trans hl₁.symm)⟩
  | tryTable hbt hb hcs =>
    obtain ⟨t₁', t₂', hbt', hl₁, -⟩ := blockType_of_types hty hbt
    exact .inl ⟨_, .tryTable hbt' (hv.length_eq.trans hl₁.symm)⟩
  | if_ hbt h₁ h₂ =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvi⟩ := forall₂_one hvb
    obtain ⟨c, rfl⟩ := ValTo.i32 hvi
    rw [vals_snoc_append]
    by_cases hc0 : c = 0
    · subst hc0; exact .inl (Step.under_vals va .ifFalse)
    · exact .inl (Step.under_vals va (.ifTrue hc0))
  | br hl hok =>
    exact .inr (.inr (.inr (.inl ⟨vs, _, [], _, by simp, hl,
      by rw [hv.length_eq]; simp⟩)))
  | brIf hl =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvi⟩ := forall₂_one hvb
    obtain ⟨c, rfl⟩ := ValTo.i32 hvi
    rw [vals_snoc_append]
    by_cases hc0 : c = 0
    · subst hc0; exact .inl (Step.under_vals va .brIfFalse)
    · exact .inl (Step.under_vals va (.brIfTrue hc0))
  | @brTable _ ls l' _ _ _ hls hl' hok =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvi⟩ := forall₂_one hvb
    obtain ⟨c, rfl⟩ := ValTo.i32 hvi
    rw [vals_snoc_append]
    by_cases hlt : c.toNat < ls.length
    · exact .inl (Step.under_vals va (.brTableLt (List.getElem?_eq_getElem hlt)))
    · exact .inl (Step.under_vals va (.brTableGe (by omega)))
  | brOnNull hl hh =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvr⟩ := forall₂_one hvb
    obtain ⟨r, rfl⟩ := ValTo.ref hvr
    rw [vals_snoc_append]
    by_cases hr : r = .null
    · subst hr; exact .inl (Step.under_vals va .brOnNullNull)
    · exact .inl (Step.under_vals va (.brOnNullAddr (v := .ref r) (fun e => hr (by cases e; rfl))))
  | brOnNonNull hl =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvr⟩ := forall₂_one hvb
    obtain ⟨r, rfl⟩ := ValTo.ref hvr
    rw [vals_snoc_append]
    by_cases hr : r = .null
    · subst hr; exact .inl (Step.under_vals va .brOnNonNullNull)
    · exact .inl (Step.under_vals va
        (.brOnNonNullAddr (v := .ref r) (fun e => hr (by cases e; rfl))))
  | @brOnCast _ l rt₁ rt₂ _ _ hl h₁ h₂ h₂₁ h₂l =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvr⟩ := forall₂_one hvb
    obtain ⟨r, rfl⟩ := ValTo.ref hvr
    rw [vals_snoc_append]
    by_cases hr : RefOk s r (f.module.instRef rt₂)
    · exact .inl (Step.under_vals va (.brOnCastSucceed hr))
    · exact .inl (Step.under_vals va (.brOnCastFail hr))
  | @brOnCastFail _ l rt₁ rt₂ _ _ hl h₁ h₂ h₂₁ hdl =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvr⟩ := forall₂_one hvb
    obtain ⟨r, rfl⟩ := ValTo.ref hvr
    rw [vals_snoc_append]
    by_cases hr : RefOk s r (f.module.instRef rt₂)
    · exact .inl (Step.under_vals va (.brOnCastFailSucceed hr))
    · exact .inl (Step.under_vals va (.brOnCastFailFail hr))
  | call hf he =>
    rw [hfuncs] at hf
    obtain ⟨a, fi, ha, hfi⟩ := StateOk.func? hst hf
    exact .inl (Step.under_vals vs (.call ha hfi))
  | @callRef _ x d _ _ hd he =>
    have hd' : Cf.type? x = some d := by rw [hC] at hd; exact hd
    obtain ⟨va, vb, rfl, hva, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvr⟩ := forall₂_one hvb
    obtain ⟨r, rfl⟩ := ValTo.ref hvr
    rw [vals_snoc_append]
    exact .inl (callRef_step hhost hs (c := .plain (.callRef _)) trivial (callRef_inv_closed hst (TyOk.of_empty _ (hst.2.type_ok hd')) he hva hvr (fun _ _ h ht => hst.valTo_valOk h ht)))
  | callIndirect => exact .inl (Step.under_vals vs .callIndirect)
  | return_ hr hok =>
    exact .inr (.inr (.inr (.inr (.inl ⟨vs, [], _, by simp, hr,
      by rw [hv.length_eq]; simp⟩))))
  | returnCall hf he hr hsub hok =>
    rw [hfuncs] at hf
    obtain ⟨a, fi, ha, hfi⟩ := StateOk.func? hst hf
    exact .inl (Step.under_vals vs (.returnCall ha hfi))
  | @returnCallRef _ x d ps rs rs' t₃ t₄ hd he hr hsub hok =>
    have hd' : Cf.type? x = some d := by rw [hC] at hd; exact hd
    obtain ⟨vab, vr, rfl, hvab, hvr⟩ := forall₂_split hv
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hvab
    obtain ⟨v, rfl, hv1⟩ := forall₂_one hvr
    obtain ⟨r, rfl⟩ := ValTo.ref hv1
    exact .inr (.inr (.inr (.inr (.inr ⟨va ++ vb, r, .plain (.returnCallRef x), [], rs',
      by simp [vals, Val.toAdmin], trivial, hr, RCOk.of_inv va (callRef_inv_closed hst (TyOk.of_empty _ (hst.2.type_ok hd')) he hvb hv1 (fun _ _ h ht => hst.valTo_valOk h ht))⟩))))
  | returnCallIndirect => exact .inl (Step.under_vals vs .returnCallIndirect)
  | throw hx he hok =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    rw [htags] at hx
    obtain ⟨ta, ti, ts', ht, he', hn⟩ := throw_inv hst hx he hvb
    rw [vals_append, List.append_assoc]
    exact .inl (Step.under_vals va (.throw ht he' hn))
  | throwRef hok =>
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvr⟩ := forall₂_one hvb
    obtain ⟨r, rfl⟩ := ValTo.ref hvr
    rcases throwRef_inv hst hvr with rfl | ⟨a, rfl⟩
    · rw [vals_snoc_append]; exact .inl (Step.under_vals va .throwRefNull)
    · exact .inr (.inr (.inl ⟨va, a, [], by simp [vals, Val.toAdmin]⟩))

end Instr

/-! ## The code induction -/

section Main

variable {P : Profile} {host : HostSemantics H}

theorem progress_aux {s : Store H} (hhost : HostOk host) (hs : StoreOk s) {C : Context}
    {as : List Admin} {it : InstrType} (h : AdminsOk s C as it) :
    ∀ (f : Frame) (vs₀ : List Val), CtxOk s f C → ValsTo s C.toTypeCtx vs₀ it.params →
      Out P host s f C.toTypeCtx C.labels C.return_ (vals vs₀ ++ as) it.results := by
  refine AdminsOk.rec
    (motive_1 := fun C a it _ => ∀ (f : Frame) (vs₀ : List Val), CtxOk s f C →
      ValsTo s C.toTypeCtx vs₀ it.params →
      Out P host s f C.toTypeCtx C.labels C.return_ (vals vs₀ ++ [a]) it.results)
    (motive_2 := fun C as it _ => ∀ (f : Frame) (vs₀ : List Val), CtxOk s f C →
      ValsTo s C.toTypeCtx vs₀ it.params →
      Out P host s f C.toTypeCtx C.labels C.return_ (vals vs₀ ++ as) it.results)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  -- AdminOk.plain
  · intro C i it hi f vs₀ hc hv
    rcases it with ⟨t₁, xs, t₂⟩
    cases hnv : (Admin.plain i).val? with
    | none => exact .inr (plain_progress hhost hs hi hnv hc hv)
    | some v => exact value_out (.plain hi) hnv hv
  -- AdminOk.callRefType
  · intro C d ps rs hok he f vs₀ hc hv
    obtain ⟨Cf, hst, hC⟩ := hc.stateOk hs
    obtain ⟨hΔ, -⟩ := ctx_fields_eq hC
    rw [hΔ] at hv
    obtain ⟨va, vb, rfl, hva, hvb⟩ := forall₂_split hv
    obtain ⟨v, rfl, hvr⟩ := forall₂_one hvb
    obtain ⟨r, rfl⟩ := ValTo.ref hvr
    refine .inr (.inl ?_)
    rw [vals_snoc_append]
    exact callRef_step hhost hs (c := .callRefType d) trivial (callRef_inv_closed hst (wireCallRef_tyOk_of_empty _ hok) he hva hvr (fun _ _ h ht => hst.valTo_valOk h ht))
  -- AdminOk.returnCallRefType
  · intro C d ps rs rs' t₃ t₄ hok he hr hsub hit f vs₀ hc hv
    obtain ⟨Cf, hst, hC⟩ := hc.stateOk hs
    obtain ⟨hΔ, -⟩ := ctx_fields_eq hC
    rw [hΔ] at hv
    obtain ⟨vab, vr, rfl, hvab, hvr⟩ := forall₂_split hv
    obtain ⟨va, vb, rfl, -, hvb⟩ := forall₂_split hvab
    obtain ⟨v, rfl, hv1⟩ := forall₂_one hvr
    obtain ⟨r, rfl⟩ := ValTo.ref hv1
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨va ++ vb, r, .returnCallRefType d, [], rs',
      by simp [vals, Val.toAdmin], trivial, hr,
      RCOk.of_inv va (callRef_inv_closed hst (wireCallRef_tyOk_of_empty _ hok) he hvb hv1 (fun _ _ h ht => hst.valTo_valOk h ht))⟩)))))
  -- AdminOk.ref
  · intro C r rt hr f vs₀ hc hv
    exact value_out (C := C) (.ref hr) rfl hv
  -- AdminOk.label
  · intro C n cont body t' ts xs' xs hn hcont hb _ ihb f vs₀ hc hv
    cases hv
    exact .inr (.inl (label_step hn (ihb f [] (hc.withLabel t') .nil)))
  -- AdminOk.frame
  · intro C C' n fr body ts hf hn hb hok ihb f vs₀ hc hv
    cases hv
    exact .inr (.inl (frame_step (FrameOk.ctx_fields hf).1 hn
      (ihb fr [] (CtxOk.ofFrame hf ts) .nil)))
  -- AdminOk.handler
  · intro C n cs body ts xs hcs hb ihb f vs₀ hc hv
    cases hv
    exact .inr (.inl (handler_step (ihb f [] hc .nil)))
  -- AdminOk.trap
  · intro C t₁ t₂ _ hok f vs₀ hc hv
    exact .inr (.inr (.inl ⟨vs₀, [], by simp⟩))
  -- AdminOk.throwRefInits (divergent-inits deviation): as the plain `throw_ref`
  · intro C t₁ t₂ _ hok f vs₀ hc hv
    exact .inr (plain_progress hhost hs (InstrOk.throwRef (t₁ := t₁) (t₂ := t₂)
      ⟨fun t ht => hok.1 t (List.mem_append_left _ ht), hok.2.1, by simp⟩) rfl hc hv)
  -- AdminsOk.nil
  · intro C f vs₀ hc hv
    cases hv
    exact .inl ⟨[], rfl, .nil⟩
  -- AdminsOk.single
  · intro C a it ha iha f vs₀ hc hv
    exact iha f vs₀ hc hv
  -- AdminsOk.seq
  · intro C as₁ as₂ t₁ t₂ t₃ xs₁ xs₂ h₁ hx h₂ ih₁ ih₂ f vs₀ hc hv
    rcases ih₁ f vs₀ hc hv with ⟨vs₁, e, hv₁⟩ | hn
    · obtain ⟨w, rfl⟩ := vals_append_eq_vals e
      have hc' := hc.initLocals (AdminsOk.vals_inits h₁)
      have h' := ih₂ f vs₁ hc' (by rw [Context.initLocals_toTypeCtx]; exact hv₁)
      rw [Context.initLocals_toTypeCtx, Context.initLocals_labels,
        Context.initLocals_return] at h'
      rw [← List.append_assoc, e]
      exact h'
    · rw [← List.append_assoc]
      exact .inr (hn.append as₂)
  -- AdminsOk.cons
  · intro C a as t₁ t₂ t₃ xs₁ xs₂ ha hx hs' iha ihs f vs₀ hc hv
    have e0 : vals vs₀ ++ a :: as = (vals vs₀ ++ [a]) ++ as := by simp
    rw [e0]
    rcases iha f vs₀ hc hv with ⟨vs₁, e, hv₁⟩ | hn
    · obtain ⟨w, hw⟩ := vals_append_eq_vals e
      have h1 : AdminsOk s C (vals w) ⟨t₁, xs₁, t₂⟩ := hw ▸ AdminsOk.single ha
      have hc' := hc.initLocals (AdminsOk.vals_inits h1)
      have h' := ihs f vs₁ hc' (by rw [Context.initLocals_toTypeCtx]; exact hv₁)
      rw [Context.initLocals_toTypeCtx, Context.initLocals_labels,
        Context.initLocals_return] at h'
      rw [e]
      exact h'
    · exact .inr (hn.append as)
  -- AdminsOk.sub
  · intro C as it it' h hsub hok ih f vs₀ hc hv
    exact (ih f vs₀ hc (hv.sub hsub.1)).sub hsub.2.1
  -- AdminsOk.frame
  · intro C as ts t₁ t₂ xs h hok ih f vs₀ hc hv
    obtain ⟨va, vb, rfl, hva, hvb⟩ := forall₂_split hv
    have := (ih f vb hc hvb).prepend hva
    rw [vals_append, List.append_assoc]
    exact this

end Main

end Silmaril.Wasm.Execution.Core
