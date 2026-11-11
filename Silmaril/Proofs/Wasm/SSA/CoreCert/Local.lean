module

public import Silmaril.Wasm.SSA.CoreCert.Leaf.Defs
public import Silmaril.Wasm.Behaviour.Semantics.V2.Defs

@[expose] public section

/-!
# Invocations of store-free leaf functions are local (proofs)

`step_swap`: a Core 3.0 step of store-free, call-free code (`PAdmins a`, frames `FrameP a`),
whose only function reference is to address `a`, holding a store-free leaf function
(`LeafAt`), keeps the store, and is a step from the same code and frame in **any** store that
holds the same function at `a`. New proofs, by induction on the rules of `Step`, in the style
of `Silmaril.Proofs.Wasm.Interp.Profile.step_profile`.
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA
open Silmaril.Wasm.SSA.CoreCert

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

section Simp

variable {a : Nat}

@[simp] theorem pAdmin_plain {i : Instr} : PAdmin a (.plain i) ↔ PInstr i := Iff.rfl
@[simp] theorem pAdmin_ref {r : Ref} : PAdmin a (.ref r) ↔ r = .null ∨ r = .func a := Iff.rfl
@[simp] theorem pAdmin_callRefType {d} : PAdmin a (.callRefType d) := trivial
@[simp] theorem pAdmin_returnCallRefType {d} : ¬ PAdmin a (.returnCallRefType d) := id
@[simp] theorem pAdmin_label {n : Nat} {cont : List Instr} {body : List Admin} :
    PAdmin a (.label n cont body) ↔ pureInstrs cont = true ∧ PAdmins a body := Iff.rfl
@[simp] theorem pAdmin_handler {n : Nat} {cs : List Catch} {body : List Admin} :
    PAdmin a (.handler n cs body) ↔ PAdmins a body := Iff.rfl
@[simp] theorem pAdmin_frame {n : Nat} {fr : Frame} {body : List Admin} :
    PAdmin a (.frame n fr body) ↔ FrameP a fr ∧ PAdmins a body := Iff.rfl
@[simp] theorem pAdmin_trap : PAdmin a .trap := trivial

@[simp] theorem pAdmin_toAdmin (v : Val) : PAdmin a v.toAdmin ↔ ValP a v := by
  cases v with
  | num nv =>
    obtain ⟨ty, b⟩ := nv
    cases ty with
    | int t => exact iff_of_true rfl trivial
    | float t => exact iff_of_true rfl trivial
  | vec b => exact iff_of_true rfl trivial
  | ref r => exact Iff.rfl

@[simp] theorem pAdmins_vals (vs : List Val) : PAdmins a (vals vs) ↔ ∀ v ∈ vs, ValP a v := by
  induction vs with
  | nil => simp [vals]
  | cons v vs ih => simp [vals] at ih ⊢; simp [ih]

@[simp] theorem pAdmin_constI32 (b : BitVec 32) : PAdmin a (constI32 b) :=
  (pAdmin_toAdmin (Val.i32 b)).mpr trivial

theorem pAdmins_expression {is : List Instr} (h : pureInstrs is = true) :
    PAdmins a (expression is) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    simp only [pureInstrs, Bool.and_eq_true] at h
    exact ⟨h.1, ih h.2⟩

@[simp] theorem pAdmins_expression_iff {is : List Instr} :
    PAdmins a (expression is) ↔ pureInstrs is = true := by
  induction is with
  | nil => exact iff_of_true trivial rfl
  | cons i is ih =>
    have e : expression (i :: is) = .plain i :: expression is := rfl
    rw [e, pAdmins_cons, ih, pAdmin_plain]
    simp only [PInstr, pureInstrs, Bool.and_eq_true]

theorem not_pAdmin_returnCallRef {c : Admin} (hc : c.IsReturnCallRef) : ¬ PAdmin a c := by
  unfold Admin.IsReturnCallRef at hc
  split at hc
  · simp [PInstr, pureInstr]
  · exact id
  · exact absurd hc id

theorem valP_num (v : Val) (h : ∀ r, v ≠ .ref r) : ValP a v := by
  rcases v with _ | _ | r
  · trivial
  · trivial
  · exact absurd rfl (h r)

end Simp

/-! ## One step -/

macro "p_simp" : tactic => `(tactic| simp_all [PInstr, pureInstr, pureInstrs, ValP, throwing,
  Admin.IsCallRef])

/-- The callee frame of a leaf function on leaf values. -/
theorem frameP_forCall {a : Nat} {mi : ModuleInst} {vs : List Val} {ls : List ValType}
    (hvs : ∀ v ∈ vs, ValP a v) (hls : intLocals ls = true) :
    FrameP a (Frame.forCall mi vs ls) := by
  intro v hv
  simp only [Frame.forCall, List.mem_append, List.mem_map] at hv
  rcases hv with ⟨w, hw, he⟩ | ⟨t, ht, he⟩
  · exact Option.some.inj he ▸ hvs w hw
  · have hint := List.all_eq_true.mp hls t ht
    rcases t with ⟨t | t⟩ | t | t
    · cases t
      · exact (Option.some.inj he) ▸ trivial
      · exact (Option.some.inj he) ▸ trivial
    all_goals simp at hint

/-- The local a leaf frame holds is a leaf value. -/
theorem frameP_local {a : Nat} {f : Frame} (hf : FrameP a f) {x : LocalIdx} {v : Val}
    (h : f.local? x = some (some v)) : ValP a v :=
  hf v (List.mem_of_getElem? h)

theorem frameP_setLocal {a : Nat} {f : Frame} (hf : FrameP a f) (x : LocalIdx) {v : Val}
    (hv : ValP a v) : FrameP a (f.setLocal x v) := by
  intro w hw
  simp only [Frame.setLocal] at hw
  rcases List.mem_or_eq_of_mem_set hw with hw | hw
  · exact hf w hw
  · cases hw
    exact hv

theorem pAdmin_of_mem {a : Nat} {l : List Admin} (h : PAdmins a l) {x : Admin} (hx : x ∈ l) :
    PAdmin a x := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 hx

/-- The function reference of a call in leaf code is `a`. -/
theorem callee_eq {a a' : Nat} {vs : List Val} {c₀ : Admin}
    (hp : PAdmins a (vals vs ++ [.ref (.func a'), c₀])) : (∀ v ∈ vs, ValP a v) ∧ a' = a := by
  have hl : PAdmins a (vals vs) ∧ PAdmins a [.ref (.func a'), c₀] := pAdmins_append.mp hp
  have hr : Ref.func a' = .null ∨ Ref.func a' = .func a := hl.2.1
  have ha : a' = a := by rcases hr with h | h <;> cases h; rfl
  exact ⟨(pAdmins_vals vs).mp hl.1, ha⟩

/-- A leaf function is not a host function. -/
theorem leaf_not_host {s : Store H} {a : Nat} (hL : LeafAt s a) {fi : FuncInst H} {hh : H}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) : False := by
  obtain ⟨fi₀, fn, hfi₀, hc₀, -⟩ := hL
  obtain rfl : fi = fi₀ := Option.some.inj (hf.symm.trans hfi₀)
  rw [hc₀] at hcode
  cases hcode

/-- The `call_ref` of the leaf function. -/
theorem swap_callRefFunc {a a' : Nat} {s t : Store H} {f : Frame} {c₀ : Admin} {vs : List Val}
    {fi : FuncInst H} {ps rs : Validation.Ty (.list .val)} {code : Func} (hc : c₀.IsCallRef)
    (hf : s.funcs[a']? = some fi) (he : Validation.Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .wasm code)
    (hp : PAdmins a (vals vs ++ [.ref (.func a'), c₀])) (hfr : FrameP a f) (hL : LeafAt s a)
    (ht : t.funcs[a]? = s.funcs[a]?) :
    Swap P host a t ⟨s, f, vals vs ++ [.ref (.func a'), c₀]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  obtain ⟨hvs, ha⟩ := callee_eq hp
  rw [ha] at hf
  obtain ⟨fi₀, fn, hfi₀, hc₀, hleaf⟩ := hL
  obtain rfl : fi = fi₀ := Option.some.inj (hf.symm.trans hfi₀)
  obtain rfl : code = fn := by rw [hc₀] at hcode; cases hcode; rfl
  have hl : pureInstrs code.body = true ∧ intLocals code.locals = true := by
    simpa only [leafFunc, Bool.and_eq_true] using hleaf
  have hres : PAdmins a [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]] :=
    ⟨⟨frameP_forCall hvs hl.2, ⟨rfl, (pAdmins_expression_iff).mpr hl.1⟩, trivial⟩, trivial⟩
  exact ⟨rfl, ha ▸ .callRefFunc hc (ht.trans hf) he hn hcode, hres, hfr⟩

/-- Local variable steps. -/
theorem swap_variable {a : Nat} {c c' : Config H} (h : VariableStep c c')
    (hp : PAdmins a c.code) (hfr : FrameP a c.frame) {t : Store H} :
    Swap P host a t c c' := by
  cases h with
  | localGet hv => exact ⟨rfl, .variable (.localGet hv), by simpa using frameP_local hfr hv, hfr⟩
  | @localSet s f x v hx =>
    have hv : ValP a v := (pAdmin_toAdmin v).mp hp.1
    exact ⟨rfl, .variable (.localSet hx), trivial, frameP_setLocal hfr _ hv⟩
  | @localTee s f x v =>
    have hv : ValP a v := (pAdmin_toAdmin v).mp hp.1
    exact ⟨rfl, .variable .localTee, by simp [hv, PInstr, pureInstr], hfr⟩
  | globalGet => exfalso; p_simp
  | globalSet => exfalso; p_simp

/-- A `return_call_ref` is not leaf code. -/
theorem no_returnCallRef {a : Nat} {l : List Admin} (hp : PAdmins a l) {c : Admin}
    (hc : c.IsReturnCallRef) (hm : c ∈ l) : False :=
  not_pAdmin_returnCallRef hc (pAdmin_of_mem hp hm)

/-- The body of a leaf label, handler or frame. -/
theorem body_label {a n : Nat} {cont : List Instr} {is : List Admin}
    (hp : PAdmins a [.label n cont is]) : PAdmins a is := hp.1.2

theorem body_handler {a n : Nat} {cs : List Catch} {is : List Admin}
    (hp : PAdmins a [.handler n cs is]) : PAdmins a is := hp.1

theorem body_frame {a n : Nat} {fi : Frame} {is : List Admin}
    (hp : PAdmins a [.frame n fi is]) : FrameP a fi ∧ PAdmins a is := hp.1

/-- **A step of leaf code is a step in any store holding the same function at `a`**, keeps the
store, and stays leaf code. -/
theorem step_swap {a : Nat} {c c' : Config H} (h : Step P host c c') (hp : PAdmins a c.code)
    (hfr : FrameP a c.frame) (hL : LeafAt c.store a) {t : Store H}
    (ht : t.funcs[a]? = c.store.funcs[a]?) : Swap P host a t c c' := by
  induction h with
  | parametric h => exact ⟨rfl, .parametric h, by cases h <;> p_simp, hfr⟩
  | numeric h => exact ⟨rfl, .numeric h, by cases h <;> p_simp, hfr⟩
  | vector h => exfalso; cases h <;> p_simp
  | «variable» h => exact swap_variable h hp hfr
  | table h => exfalso; cases h <;> p_simp
  | memory h => exfalso; cases h <;> p_simp
  | reference h => exfalso; cases h <;> p_simp
  | aggregate h => exfalso; cases h <;> p_simp
  | @ctxtInstrs s s' f f' vs is is' rest _ hne ih =>
    have hp₀ : (PAdmins a (vals vs) ∧ PAdmins a is) ∧ PAdmins a rest := by
      simpa only [pAdmins_append] using hp
    obtain ⟨hs, hst, hp₁, hf₁⟩ := ih hp₀.1.2 hfr hL ht
    have hres : PAdmins a (vals vs ++ is' ++ rest) :=
      pAdmins_append.mpr ⟨pAdmins_append.mpr ⟨hp₀.1.1, hp₁⟩, hp₀.2⟩
    exact ⟨hs, .ctxtInstrs hst hne, hres, hf₁⟩
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    obtain ⟨hs, hst, hp₁, hf₁⟩ := ih (body_label hp) hfr hL ht
    exact ⟨hs, .ctxtLabel hst, ⟨⟨hp.1.1, hp₁⟩, trivial⟩, hf₁⟩
  | @ctxtHandler s s' f f' n cs is is' _ ih =>
    obtain ⟨hs, hst, hp₁, hf₁⟩ := ih (body_handler hp) hfr hL ht
    exact ⟨hs, .ctxtHandler hst, ⟨hp₁, trivial⟩, hf₁⟩
  | @ctxtFrame s s' f fi fi' n is is' _ ih =>
    obtain ⟨hs, hst, hp₁, hf₁⟩ := ih (body_frame hp).2 (body_frame hp).1 hL ht
    exact ⟨hs, .ctxtFrame hst, ⟨⟨hf₁, hp₁⟩, trivial⟩, hfr⟩
  | block hbt hm => exact ⟨rfl, .block hbt hm, by p_simp, hfr⟩
  | loop hbt hm => exact ⟨rfl, .loop hbt hm, by p_simp, hfr⟩
  | ifTrue hc => exact ⟨rfl, .ifTrue hc, by p_simp, hfr⟩
  | ifFalse => exact ⟨rfl, .ifFalse, by p_simp, hfr⟩
  | labelVals => exact ⟨rfl, .labelVals, by p_simp, hfr⟩
  | brLabelZero hl hn => exact ⟨rfl, .brLabelZero hl hn, by p_simp, hfr⟩
  | brLabelSucc hl => exact ⟨rfl, .brLabelSucc hl, by p_simp, hfr⟩
  | brHandler => exact ⟨rfl, .brHandler, by p_simp, hfr⟩
  | brIfTrue hc => exact ⟨rfl, .brIfTrue hc, by p_simp, hfr⟩
  | brIfFalse => exact ⟨rfl, .brIfFalse, by p_simp, hfr⟩
  | brTableLt hi => exact ⟨rfl, .brTableLt hi, by p_simp, hfr⟩
  | brTableGe hi => exact ⟨rfl, .brTableGe hi, by p_simp, hfr⟩
  | callRefNull hc => exact ⟨rfl, .callRefNull hc, by p_simp, hfr⟩
  | frameVals hn => exact ⟨rfl, .frameVals hn, by p_simp, hfr⟩
  | returnFrame hn => exact ⟨rfl, .returnFrame hn, by p_simp, hfr⟩
  | returnLabel => exact ⟨rfl, .returnLabel, by p_simp, hfr⟩
  | returnHandler => exact ⟨rfl, .returnHandler, by p_simp, hfr⟩
  | handlerVals => exact ⟨rfl, .handlerVals, by p_simp, hfr⟩
  | trapInstrs hne => exact ⟨rfl, .trapInstrs hne, by p_simp, hfr⟩
  | trapLabel => exact ⟨rfl, .trapLabel, by p_simp, hfr⟩
  | trapHandler => exact ⟨rfl, .trapHandler, by p_simp, hfr⟩
  | trapFrame => exact ⟨rfl, .trapFrame, by p_simp, hfr⟩
  | callRefFunc hc hf he hn hcode => exact swap_callRefFunc hc hf he hn hcode hp hfr hL ht
  | callRefHost _ hf _ _ hcode _ =>
    exact (leaf_not_host hL ((callee_eq hp).2 ▸ hf) hcode).elim
  | callRefHostDiv _ hf _ _ hcode _ =>
    exact (leaf_not_host hL ((callee_eq hp).2 ▸ hf) hcode).elim
  | returnCallRefLabel hc => exact (no_returnCallRef (body_label hp) hc (by simp)).elim
  | returnCallRefHandler hc => exact (no_returnCallRef (body_handler hp) hc (by simp)).elim
  | returnCallRefFrameNull hc => exact (no_returnCallRef (body_frame hp).2 hc (by simp)).elim
  | returnCallRefFrameAddr hc => exact (no_returnCallRef (body_frame hp).2 hc (by simp)).elim
  | _ => exfalso; p_simp

/-! ## Runs, divergence and behaviours -/

theorem leafAt_of_eq {s t : Store H} {a : Nat} (hL : LeafAt s a)
    (ht : t.funcs[a]? = s.funcs[a]?) : LeafAt t a := by
  obtain ⟨fi, fn, hfi, hc, hl⟩ := hL
  exact ⟨fi, fn, ht.trans hfi, hc, hl⟩

/-- One step, with the invariant. -/
theorem step_swap' {a : Nat} {c c' : Config H} (h : Step P host c c') (hc : LeafConf a c)
    {t : Store H} (ht : t.funcs[a]? = c.store.funcs[a]?) :
    c'.store = c.store ∧ Step P host (swapStore t c) (swapStore t c') ∧ LeafConf a c' := by
  obtain ⟨hs, hst, hp, hf⟩ := step_swap h hc.1 hc.2.1 hc.2.2 ht
  exact ⟨hs, hst, hp, hf, hs ▸ hc.2.2⟩

/-- **Runs of leaf code are runs in any store holding the same function at `a`.** -/
theorem steps_swap {a : Nat} {c c' : Config H} (h : Steps P host c c') (hc : LeafConf a c)
    {t : Store H} (ht : t.funcs[a]? = c.store.funcs[a]?) :
    c'.store = c.store ∧ Steps P host (swapStore t c) (swapStore t c') ∧ LeafConf a c' := by
  induction h with
  | refl => exact ⟨rfl, .refl, hc⟩
  | tail _ hs ih =>
    obtain ⟨he, hst, hc'⟩ := ih
    obtain ⟨he', hst', hc''⟩ := step_swap' hs hc' (he ▸ ht)
    exact ⟨he'.trans he, hst.tail hst', hc''⟩

/-- **Divergence of leaf code is divergence in any store holding the same function at `a`.** -/
theorem diverges_swap {a : Nat} {c : Config H} (h : Diverges P host c) (hc : LeafConf a c)
    {t : Store H} (ht : t.funcs[a]? = c.store.funcs[a]?) :
    Diverges P host (swapStore t c) := by
  obtain ⟨g, hg0, hg⟩ := h
  have inv : ∀ n, (g n).store = c.store ∧ LeafConf a (g n) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [hg0], hg0 ▸ hc⟩
    | succ n ih =>
      obtain ⟨he, -, hc'⟩ := step_swap' (hg n) ih.2 (ih.1 ▸ ht)
      exact ⟨he.trans ih.1, hc'⟩
  refine ⟨fun n => swapStore t (g n), by show swapStore t (g 0) = _; rw [hg0], fun n => ?_⟩
  exact (step_swap' (hg n) (inv n).2 ((inv n).1 ▸ ht)).2.1

/-- The behaviours of a leaf configuration are included in those of its swap. -/
theorem behavioursOf_swap_sub {a : Nat} {c : Config H} (hc : LeafConf a c) {t : Store H}
    (ht : t.funcs[a]? = c.store.funcs[a]?) :
    behavioursOf P host c ⊆ behavioursOf P host (swapStore t c) := by
  rintro b (⟨c', r, hst, hcode, rfl⟩ | ⟨rfl, hd⟩)
  · obtain ⟨-, hst', -⟩ := steps_swap hst hc ht
    exact .inl ⟨swapStore t c', r, hst', hcode, rfl⟩
  · exact .inr ⟨rfl, diverges_swap hd hc ht⟩

/-- **Invocations of a store-free leaf function are local**: the behaviours of an invocation of
`a` on leaf values are the same in every store holding the same function at `a`. -/
theorem behaviours_local {a : Nat} {s t : Store H} (hL : LeafAt s a)
    (ht : t.funcs[a]? = s.funcs[a]?) {vs : List Val} (hvs : ∀ v ∈ vs, ValP a v) :
    behaviours P host s a vs = behaviours P host t a vs := by
  have hinv : ∀ {u : Store H}, LeafAt u a → LeafConf a (invoke u a vs) := fun hu =>
    ⟨by simpa [invoke] using hvs, ⟨fun _ h => (by simp [invoke] at h), hu⟩⟩
  have hcode : invoke t a vs = swapStore t (invoke s a vs) := by
    simp [invoke, swapStore, ht]
  have hcode' : invoke s a vs = swapStore s (invoke t a vs) := by
    simp [invoke, swapStore, ht]
  apply Set.Subset.antisymm
  · rw [behaviours_eq, behaviours_eq, hcode]
    exact behavioursOf_swap_sub (hinv hL) ht
  · rw [behaviours_eq, behaviours_eq, hcode']
    exact behavioursOf_swap_sub (hinv (leafAt_of_eq hL ht)) ht.symm

end Silmaril.Proofs.Wasm.SSA.CoreCert
