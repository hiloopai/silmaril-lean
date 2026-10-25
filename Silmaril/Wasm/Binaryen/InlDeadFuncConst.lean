module

public import Silmaril.Wasm.Binaryen.InlDeadFuncTypes
public import Silmaril.Wasm.Execution.Core.Soundness.ConstEval
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateComplete

@[expose] public section

/-! # Appending a dead function: constant initialisers

The initialisers of a module run in the provisional instance `ModuleInst.initial`, which for
the extended module has one more trailing function address. Constant code reduces only by the
constant rules (`Step.const_redex`), which read the function addresses of the instance only
through `ref.func`. So every run of constant code carries over to the extended instance
(`const_steps_fwd`), and back when every `ref.func` names an existing index
(`const_steps_back`); a valid module's initialisers only name existing indices
(`instrsOk_refFunc_lt`).
-/

namespace Silmaril.Wasm.Binaryen.InlDF

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Constant redexes -/

theorem constRedex_fext {s s' : Store H} {f : Frame} {w : List Val} {i : Instr} {out : List Admin}
    (h : ConstRedex s f w i s' out) (l : List Nat) : ConstRedex s (fext f l) w i s' out := by
  cases h with
  | refNull ht => exact .refNull ht
  | refFunc h => exact .refFunc (mext_funcs_get h)
  | refI31 i => exact .refI31 i
  | structNew hd he hn hp => exact .structNew hd he hn hp
  | structNewDefault hd he hdef => exact .structNewDefault hd he hdef
  | arrayNew v n => exact .arrayNew v n
  | arrayNewDefault hd he hv => exact .arrayNewDefault hd he hv
  | arrayNewFixed hd he hn hp => exact .arrayNewFixed hd he hn hp
  | externConvertNull => exact .externConvertNull
  | externConvertAddr h => exact .externConvertAddr h
  | anyConvertNull => exact .anyConvertNull
  | anyConvertAddr r => exact .anyConvertAddr r
  | globalGet h => exact .globalGet h
  | binop h => exact .binop h

theorem constRedex_unext {s s' : Store H} {f : Frame} {l : List Nat} {w : List Val} {i : Instr}
    {out : List Admin} (h : ConstRedex s (fext f l) w i s' out)
    (hi : ∀ x : FuncIdx, i = .refFunc x → x.toNat < f.module.funcs.length) :
    ConstRedex s f w i s' out := by
  cases h with
  | refNull ht => exact .refNull ht
  | @refFunc x a h =>
    have hx := hi x rfl
    refine .refFunc ?_
    have h' : (f.module.funcs ++ l)[x.toNat]? = some a := h
    rwa [List.getElem?_append_left hx] at h'
  | refI31 i => exact .refI31 i
  | structNew hd he hn hp => exact .structNew hd he hn hp
  | structNewDefault hd he hdef => exact .structNewDefault hd he hdef
  | arrayNew v n => exact .arrayNew v n
  | arrayNewDefault hd he hv => exact .arrayNewDefault hd he hv
  | arrayNewFixed hd he hn hp => exact .arrayNewFixed hd he hn hp
  | externConvertNull => exact .externConvertNull
  | externConvertAddr h => exact .externConvertAddr h
  | anyConvertNull => exact .anyConvertNull
  | anyConvertAddr r => exact .anyConvertAddr r
  | globalGet h => exact .globalGet h
  | binop h => exact .binop h

theorem constRedex_step {s s' : Store H} {f : Frame} {w : List Val} {i : Instr} {out : List Admin}
    (h : ConstRedex s f w i s' out) :
    Step P Det.noHost ⟨s, f, vals w ++ [.plain i]⟩ ⟨s', f, out⟩ := by
  cases h with
  | refNull ht => exact .reference (.refNull ht)
  | refFunc h => exact .reference (.refFunc h)
  | refI31 i => exact .reference (.refI31 i)
  | structNew hd he hn hp => exact .aggregate (.structNew hd he hn hp)
  | structNewDefault hd he hdef => exact .aggregate (.structNewDefault hd he hdef)
  | arrayNew v n => exact .aggregate (.arrayNew v n)
  | arrayNewDefault hd he hv => exact .aggregate (.arrayNewDefault hd he hv)
  | arrayNewFixed hd he hn hp => exact .aggregate (.arrayNewFixed hd he hn hp)
  | externConvertNull => exact .reference .externConvertNull
  | externConvertAddr h => exact .reference (.externConvertAddr h)
  | anyConvertNull => exact .reference .anyConvertNull
  | anyConvertAddr r => exact .reference (.anyConvertAddr r)
  | globalGet h => exact .variable (.globalGet h)
  | binop h => exact .numeric (.intBinOp h)

theorem constRedex_lift {s s' : Store H} {f : Frame} {w : List Val} {i : Instr} {out : List Admin}
    (h : ConstRedex s f w i s' out) (pre : List Val) (post : List Admin) :
    Step P host ⟨s, f, vals pre ++ vals w ++ .plain i :: post⟩
      ⟨s', f, vals pre ++ out ++ post⟩ := by
  have := Det.lift_instrs (P := P) pre post ⟨s, f, vals w ++ [.plain i]⟩ ⟨s', f, out⟩
    (constRedex_step h)
  simp only [List.append_assoc, List.singleton_append] at this ⊢
  exact Step.of_noHost host this

theorem refFunc_not_mem_vals (x : FuncIdx) (vs : List Val) :
    Admin.plain (.refFunc x) ∉ vals vs := by
  intro h
  simp only [vals, List.mem_map] at h
  obtain ⟨v, -, hv⟩ := h
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at hv

theorem refFunc_ne_toAdmin (v : Val) (x : FuncIdx) : Admin.plain (.refFunc x) ≠ v.toAdmin := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin]

theorem constRedex_out {s s' : Store H} {f : Frame} {w : List Val} {i : Instr} {out : List Admin}
    (h : ConstRedex s f w i s' out) (x : FuncIdx) : Admin.plain (.refFunc x) ∉ out := by
  cases h <;> simp [refFunc_not_mem_vals, refFunc_ne_toAdmin]

/-! ## Runs of constant code -/

theorem constOk_expression {e : Expr} (h : ∀ i ∈ e, i.IsConstI) :
    ∀ a ∈ expression e, a.ConstOk := by
  intro a ha
  simp only [expression, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact h i hi

/-- **Constant runs carry over to an extended instance.** -/
theorem const_steps_fwd {c c' : Config H} (h : Steps P host c c') (hc : ∀ a ∈ c.code, a.ConstOk)
    (l : List Nat) :
    Steps P host ⟨c.store, fext c.frame l, c.code⟩ ⟨c'.store, fext c'.frame l, c'.code⟩ := by
  induction h with
  | refl => exact .refl
  | @tail x x₁ hx hst ih =>
    have hxc := (Steps.const_shape hx hc).2.2.1
    obtain ⟨hfr, pre, w, i, post, out, e₁, e₂, hr⟩ := Step.const_redex hst hxc
    refine ih.tail ?_
    have := constRedex_lift (P := P) (host := host) (constRedex_fext hr l) pre post
    rw [e₁, e₂, hfr]
    exact this

/-- **Constant runs carry back from an extended instance**, when every `ref.func` names an
index of the original instance. -/
theorem const_steps_back {s : Store H} {f : Frame} {l : List Nat} {code : List Admin}
    (hc : ∀ a ∈ code, a.ConstOk)
    (hb : ∀ x : FuncIdx, Admin.plain (.refFunc x) ∈ code → x.toNat < f.module.funcs.length) :
    ∀ {c' : Config H}, Steps P host ⟨s, fext f l, code⟩ c' →
      Steps P host ⟨s, f, code⟩ ⟨c'.store, f, c'.code⟩ ∧ c'.frame = fext f l ∧
      ∀ x : FuncIdx, Admin.plain (.refFunc x) ∈ c'.code → x.toNat < f.module.funcs.length := by
  intro c' h
  induction h with
  | refl => exact ⟨.refl, rfl, hb⟩
  | @tail y y₁ hy hst ih =>
    obtain ⟨hL, hfr, hbnd⟩ := ih
    have hyc := (Steps.const_shape hy hc).2.2.1
    obtain ⟨hfr', pre, w, i, post, out, e₁, e₂, hr⟩ := Step.const_redex hst hyc
    rw [hfr] at hr
    have hr' := constRedex_unext hr (fun x hx => hbnd x (by rw [e₁, hx]; simp))
    have hst' := constRedex_lift (P := P) (host := host) hr' pre post
    refine ⟨?_, hfr'.trans hfr, ?_⟩
    · rw [e₂]
      rw [e₁] at hL
      exact hL.tail hst'
    · intro x hx
      rw [e₂] at hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact absurd hx (refFunc_not_mem_vals x pre)
      · exact absurd hx (constRedex_out hr x)
      · exact hbnd x (by rw [e₁]; simp [hx])

theorem refFunc_mem_expression {x : FuncIdx} {e : Expr}
    (h : Admin.plain (.refFunc x) ∈ expression e) : Instr.refFunc x ∈ e := by
  simp only [expression, List.mem_map] at h
  obtain ⟨i, hi, he⟩ := h
  cases he
  exact hi

/-! ## Initialiser evaluation -/

theorem evalGlobals_fwd {s s'' : Store H} {f f'' : Frame} {gts : List CGlobalType}
    {es : List Expr} {vs : List Val} (h : EvalGlobals P host s f gts es s'' f'' vs)
    (hc : ∀ e ∈ es, ∀ i ∈ e, i.IsConstI) (l : List Nat) :
    EvalGlobals P host s (fext f l) gts es s'' (fext f'' l) vs := by
  induction h with
  | nil => exact .nil
  | @cons s s' s'' f f' f'' g gs e es v vs he _ ih =>
    exact .cons (const_steps_fwd he (constOk_expression (hc e (by simp))) l)
      (ih (fun e' he' => hc e' (by simp [he'])))

theorem evalExprs_fwd {s s'' : Store H} {f f'' : Frame} {es : List Expr} {rs : List Ref}
    (h : EvalExprs P host s f es s'' f'' rs) (hc : ∀ e ∈ es, ∀ i ∈ e, i.IsConstI)
    (l : List Nat) : EvalExprs P host s (fext f l) es s'' (fext f'' l) rs := by
  induction h with
  | nil => exact .nil
  | @cons s s' s'' f f' f'' e es r rs he _ ih =>
    exact .cons (const_steps_fwd he (constOk_expression (hc e (by simp))) l)
      (ih (fun e' he' => hc e' (by simp [he'])))

theorem evalExprss_fwd {s s'' : Store H} {f f'' : Frame} {ess : List (List Expr)}
    {rss : List (List Ref)} (h : EvalExprss P host s f ess s'' f'' rss)
    (hc : ∀ es ∈ ess, ∀ e ∈ es, ∀ i ∈ e, i.IsConstI) (l : List Nat) :
    EvalExprss P host s (fext f l) ess s'' (fext f'' l) rss := by
  induction h with
  | nil => exact .nil
  | @cons s s' s'' f f' f'' es ess rs rss he _ ih =>
    exact .cons (evalExprs_fwd he (hc es (by simp)) l)
      (ih (fun es' he' => hc es' (by simp [he'])))

theorem evalGlobals_back {s s'' : Store H} {g g'' : Frame} {gts : List CGlobalType}
    {es : List Expr} {vs : List Val} (h : EvalGlobals P host s g gts es s'' g'' vs) :
    ∀ {f : Frame} {l : List Nat}, g = fext f l → (∀ e ∈ es, ∀ i ∈ e, i.IsConstI) →
      (∀ e ∈ es, ∀ x : FuncIdx, Instr.refFunc x ∈ e → x.toNat < f.module.funcs.length) →
      ∃ f'', g'' = fext f'' l ∧ EvalGlobals P host s f gts es s'' f'' vs := by
  induction h with
  | nil => intro f l hg _ _; exact ⟨f, hg, .nil⟩
  | @cons s s' s'' g g' g'' gt gts e es v vs he _ ih =>
    intro f l hg hc hb
    subst hg
    obtain ⟨hL, hfr, -⟩ := const_steps_back (constOk_expression (hc e (by simp)))
      (fun x hx => hb e (by simp) x (refFunc_mem_expression hx)) he
    have hfr' : g' = fext f l := hfr
    subst hfr'
    obtain ⟨f'', h1, h2⟩ := ih (f := { f with module := { f.module with
        globals := f.module.globals ++ [(allocGlobal s' gt v).2] } }) (l := l) rfl
      (fun e' he' => hc e' (by simp [he'])) (fun e' he' x hx => hb e' (by simp [he']) x hx)
    exact ⟨f'', h1, .cons hL h2⟩

theorem evalExprs_back {s s'' : Store H} {g g'' : Frame} {es : List Expr} {rs : List Ref}
    (h : EvalExprs P host s g es s'' g'' rs) :
    ∀ {f : Frame} {l : List Nat}, g = fext f l → (∀ e ∈ es, ∀ i ∈ e, i.IsConstI) →
      (∀ e ∈ es, ∀ x : FuncIdx, Instr.refFunc x ∈ e → x.toNat < f.module.funcs.length) →
      g'' = fext f l ∧ EvalExprs P host s f es s'' f rs := by
  induction h with
  | nil => intro f l hg _ _; exact ⟨hg, .nil⟩
  | @cons s s' s'' g g' g'' e es r rs he _ ih =>
    intro f l hg hc hb
    subst hg
    obtain ⟨hL, hfr, -⟩ := const_steps_back (constOk_expression (hc e (by simp)))
      (fun x hx => hb e (by simp) x (refFunc_mem_expression hx)) he
    have hfr' : g' = fext f l := hfr
    subst hfr'
    obtain ⟨h1, h2⟩ := ih rfl (fun e' he' => hc e' (by simp [he']))
      (fun e' he' x hx => hb e' (by simp [he']) x hx)
    exact ⟨h1, .cons hL h2⟩

theorem evalExprss_back {s s'' : Store H} {g g'' : Frame} {ess : List (List Expr)}
    {rss : List (List Ref)} (h : EvalExprss P host s g ess s'' g'' rss) :
    ∀ {f : Frame} {l : List Nat}, g = fext f l →
      (∀ es ∈ ess, ∀ e ∈ es, ∀ i ∈ e, i.IsConstI) →
      (∀ es ∈ ess, ∀ e ∈ es, ∀ x : FuncIdx, Instr.refFunc x ∈ e →
        x.toNat < f.module.funcs.length) →
      g'' = fext f l ∧ EvalExprss P host s f ess s'' f rss := by
  induction h with
  | nil => intro f l hg _ _; exact ⟨hg, .nil⟩
  | @cons s s' s'' g g' g'' es ess rs rss he _ ih =>
    intro f l hg hc hb
    subst hg
    obtain ⟨hfr, hL⟩ := evalExprs_back he rfl (hc es (by simp)) (hb es (by simp))
    subst hfr
    obtain ⟨h1, h2⟩ := ih rfl (fun es' he' => hc es' (by simp [he']))
      (fun es' he' => hb es' (by simp [he']))
    exact ⟨h1, .cons hL h2⟩

/-! ## `ref.func` in valid initialisers -/

theorem withLocals_funcs : ∀ (C : Context) (xs : List Nat) (lts : List LocalType),
    (C.withLocals xs lts).funcs = C.funcs
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | C, x :: xs, lt :: lts => withLocals_funcs (C.setLocal x lt) xs lts

theorem initLocals_funcs (C : Context) (xs : List Nat) : (C.initLocals xs).funcs = C.funcs :=
  withLocals_funcs _ _ _

theorem instrsOk_refFunc_lt {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) : ∀ x : FuncIdx, Instr.refFunc x ∈ is → x.toNat < C.funcs.length := by
  refine InstrsOk.ind (motive := fun C is _ _ =>
    ∀ x : FuncIdx, Instr.refFunc x ∈ is → x.toNat < C.funcs.length) ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro C x hx
    simp at hx
  · intro C i it hi x hx
    rw [List.mem_singleton] at hx
    subst hx
    obtain ⟨d, hd, -⟩ := hi.refFunc_inv
    exact (List.getElem?_eq_some_iff.mp hd).1
  · intro C is₁ is₂ t₁ t₂ t₃ xs₁ xs₂ _ _ _ ih₁ ih₂ x hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ih₁ x hm
    · rw [← initLocals_funcs C xs₁]
      exact ih₂ x hm
  · intro C i is t₁ t₂ t₃ xs₁ xs₂ hi _ _ ih x hm
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨d, hd, -⟩ := hi.refFunc_inv
      exact (List.getElem?_eq_some_iff.mp hd).1
    · rw [← initLocals_funcs C xs₁]
      exact ih x hm
  · intro C is it it' _ _ _ ih
    exact ih
  · intro C is ts t₁ t₂ xs _ _ ih
    exact ih

theorem exprOkConst_refFunc_lt {C : Context} {e : Expr} {t : CValType} (h : ExprOkConst C e t) :
    ∀ x : FuncIdx, Instr.refFunc x ∈ e → x.toNat < C.funcs.length :=
  instrsOk_refFunc_lt h.typed

theorem globalsOk_refFunc_lt {C : Context} {gs : List Global} {gts : List CGlobalType}
    (h : GlobalsOk C gs gts) :
    ∀ g ∈ gs, ∀ x : FuncIdx, Instr.refFunc x ∈ g.init → x.toNat < C.funcs.length := by
  induction h with
  | nil => intro g hg; simp at hg
  | cons hg _ ih =>
    intro g' hg' x hx
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact exprOkConst_refFunc_lt hg.2.2 x hx
    · exact ih g' hg' x hx

theorem forall₂_left {α β : Type} {R : α → β → Prop} {p : α → Prop}
    (hR : ∀ a b, R a b → p a) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, p a
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hab hs, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hR _ _ hab
    · exact forall₂_left hR hs a h

/-- The function indices a valid module's initialisers and exports name. -/
structure FuncBounds (M : Module) (N : Nat) : Prop where
  globals : ∀ e ∈ M.globals.map Global.init, ∀ x : FuncIdx, Instr.refFunc x ∈ e → x.toNat < N
  tables : ∀ e ∈ M.tables.map Table.init, ∀ x : FuncIdx, Instr.refFunc x ∈ e → x.toNat < N
  elems : ∀ es ∈ M.elems.map Elem.init, ∀ e ∈ es, ∀ x : FuncIdx, Instr.refFunc x ∈ e →
    x.toNat < N
  exports : ∀ ex ∈ M.exports, ∀ x : FuncIdx, ex.index = .func x → x.toNat < N

theorem moduleOk_funcBounds {M : Module} {xtI xtE : List CExternType} {s : Store H}
    {xas : List ExternAddr} (hM : ModuleOk M ⟨xtI, xtE⟩)
    (hxas : List.Forall₂ (ExternAddrOk s) xas xtI) :
    FuncBounds M ((ExternAddr.funcs xas).length + M.funcs.length) := by
  cases hM with
  | @mk _ _ _ _ _ _ _ _ C' C _ _ hC' hC _ hglobals _ htables hfuncs _ helems _ hexports _ =>
    have hN : C'.funcs.length = (ExternAddr.funcs xas).length + M.funcs.length := by
      rw [hC']
      simp only [List.length_append]
      rw [(ExternAddrOk.forall₂_funcs hxas).length_eq, hfuncs.length_eq]
    have hNC : C.funcs.length = C'.funcs.length := by rw [hC]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e he x hx
      simp only [List.mem_map] at he
      obtain ⟨g, hg, rfl⟩ := he
      rw [← hN]
      exact globalsOk_refFunc_lt hglobals g hg x hx
    · intro e he x hx
      simp only [List.mem_map] at he
      obtain ⟨t, ht, rfl⟩ := he
      rw [← hN]
      exact forall₂_left (p := fun t : Table => ∀ x : FuncIdx, Instr.refFunc x ∈ t.init →
        x.toNat < C'.funcs.length) (fun _ _ h => exprOkConst_refFunc_lt h.2.2) htables t ht x hx
    · intro es hes e he x hx
      simp only [List.mem_map] at hes
      obtain ⟨el, hel, rfl⟩ := hes
      rw [← hN, ← hNC]
      exact forall₂_left (p := fun el : Elem => ∀ e ∈ el.init, ∀ x : FuncIdx,
        Instr.refFunc x ∈ e → x.toNat < C.funcs.length)
        (fun _ _ h e he => exprOkConst_refFunc_lt (h.2.2.1 e he)) helems el hel e he x hx
    · intro ex hex x hx
      rw [← hN, ← hNC]
      exact forall₂_left (p := fun ex : Export => ∀ x : FuncIdx, ex.index = .func x →
        x.toNat < C.funcs.length) (fun ex xt h x hx => by
          have h' : ExternIdxOk C ex.index xt := h
          rw [hx] at h'
          cases h' with
          | func hf => exact (List.getElem?_eq_some_iff.mp hf).1) hexports ex hex x hx

end Silmaril.Wasm.Binaryen.InlDF
