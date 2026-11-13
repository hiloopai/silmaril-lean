module

public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.NoHost

/-!
# Invoking a forwarding function

A *forwarding function* has no locals and a body `local.get j₁ … local.get jₙ`. Invoking it
at address `a` of a store `S` with arguments `vs` (none of them a function reference) runs
through four shapes (`Sh`), for every profile and every host:

* `s0`: the invocation `vs (ref.func a) (call_ref)`;
* `s1 k us`: the frame and label with the first `k` locals read (`us`);
* `s2 us`: the frame around the values;
* `s3 us`: the values.

Every step stays in `Sh` and decreases the measure (`Sh.step`), so:

* `Sh.result`: a run that reaches a result reaches `vals us` with `us` the projection
  `js.mapM (vs[·]?)` of the arguments, of the result arity, in the same store;
* `Sh.not_diverges`: no infinite run;
* `Sh.run`: the projection, when defined and of the result arity, is reached.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-- No argument is a function reference. -/
def NoFuncRef (vs : List Val) : Prop := ∀ v ∈ vs, ∀ b, v ≠ .ref (.func b)

/-- The projection of the arguments selected by the `local.get` indices. -/
def proj (js : List LocalIdx) (vs : List Val) : Option (List Val) :=
  js.mapM fun j => vs[j.toNat]?

/-- The code of a forwarding body. -/
def fwdCode (js : List LocalIdx) : List Admin := expression (js.map .localGet)

/-- The shapes of a forwarding invocation, with their measure. -/
inductive Sh (S : Store H) (a : Nat) (dt : DefType) (vs : List Val) (n : Nat) (F : Frame)
    (js : List LocalIdx) : Config H → Nat → Prop where
  | s0 : Sh S a dt vs n F js ⟨S, {}, vals vs ++ [.ref (.func a), .callRefType dt]⟩ (js.length + 3)
  | s1 (k : Nat) (us : List Val) (hk : k ≤ js.length) (hus : proj (js.take k) vs = some us) :
      Sh S a dt vs n F js
        ⟨S, {}, [.frame n F [.label n [] (vals us ++ fwdCode (js.drop k))]]⟩ (js.length - k + 2)
  | s2 (us : List Val) (hus : proj js vs = some us) :
      Sh S a dt vs n F js ⟨S, {}, [.frame n F (vals us)]⟩ 1
  | s3 (us : List Val) (hus : proj js vs = some us) (hn : us.length = n) :
      Sh S a dt vs n F js ⟨S, {}, vals us⟩ 0

/-! ## Head steps -/

theorem head_of_step {P : Profile} {s : Store H} {f : Frame} {code : List Admin} {c' : Config H}
    (h : Step P noHost ⟨s, f, code⟩ c') (htrap : Admin.trap ∉ code)
    (hthrow : Admin.plain .throwRef ∉ code) :
    ∃ vs args e rest c₀, fnv code = (vs ++ args, e :: rest) ∧ Head P s f args e c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ := by
  rcases Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hf, -, hh, hc⟩ := fnv_headDec hd
    exact ⟨vs, args, e, rest, c₀, hf, hh, hc⟩
  · obtain ⟨p, q, u, r, -, ⟨-, hc, -⟩ | ⟨a, -, hc, -⟩⟩ := fnv_bubble hb
    · exact absurd (by rw [show code = _ from hc]; simp) htrap
    · exact absurd (by rw [show code = _ from hc]; simp) hthrow

theorem not_mem_vals_of {x : Admin} (hx : x.val? = none) (vs : List Val) : x ∉ vals vs :=
  fun h => mem_vals h hx

theorem proj_mem {vs : List Val} : ∀ {js : List LocalIdx} {us : List Val},
    proj js vs = some us → ∀ u ∈ us, u ∈ vs
  | [], us, h => by
    simp only [proj, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | j :: js, us, h => by
    simp only [proj, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us', hus', h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact List.mem_of_getElem? hv
    · exact proj_mem hus' u hu

theorem proj_take_succ {js : List LocalIdx} {vs us : List Val} {k : Nat} (hk : k < js.length)
    (h : proj (js.take k) vs = some us) {v : Val} (hv : vs[js[k].toNat]? = some v) :
    proj (js.take (k + 1)) vs = some (us ++ [v]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [proj, Option.toList_some, List.mapM_append, List.mapM_cons, List.mapM_nil] at h ⊢
  simp [h, hv]

theorem toAdmin_ref {u : Val} {r : Ref} (h : u.toAdmin = .ref r) : u = .ref r := by
  have h' : (Admin.ref r).val? = some u := toAdmin_eq_iff.mp h
  simpa using h'.symm

theorem not_mem_plain {l : List Admin} (hl : ∀ x ∈ l, (∃ i, x = .plain i)) {a : Admin}
    (ha : ∀ i, a ≠ .plain i) : a ∉ l := fun h =>
  let ⟨i, hi⟩ := hl a h
  ha i hi

theorem noHostRef_vals {S : Store H} {us : List Val} (hus : NoFuncRef us) {l : List Admin}
    (hl : ∀ x ∈ l, (∃ i, x = .plain i)) : NoHostRef S (vals us ++ l) := by
  intro b hb
  cases hb with
  | here h =>
    have hv : Admin.ref (.func b) ∈ vals us :=
      (List.mem_append.mp h).resolve_right (not_mem_plain hl (by simp))
    obtain ⟨u, hu, hu'⟩ : ∃ u ∈ us, u.toAdmin = .ref (.func b) := List.mem_map.mp hv
    exact absurd (toAdmin_ref hu') (hus u hu b)
  | label h _ | handler h _ | frame h _ =>
    have hv := (List.mem_append.mp h).resolve_right (not_mem_plain hl (by simp))
    exact absurd rfl (mem_vals hv)

theorem noHostRef_label {S : Store H} {n : Nat} {cont : List Instr} {is : List Admin}
    (h : NoHostRef S is) : NoHostRef S [.label n cont is] := by
  intro b hb
  cases hb with
  | here h' => simp at h'
  | label h' hi => simp only [List.mem_singleton, Admin.label.injEq] at h'; rw [← h'.2.2] at h; exact h b hi
  | handler h' _ => simp at h'
  | frame h' _ => simp at h'

theorem noHostRef_frame {S : Store H} {n : Nat} {F : Frame} {is : List Admin}
    (h : NoHostRef S is) : NoHostRef S [.frame n F is] := by
  intro b hb
  cases hb with
  | here h' => simp at h'
  | label h' _ => simp at h'
  | handler h' _ => simp at h'
  | frame h' hi => simp only [List.mem_singleton, Admin.frame.injEq] at h'; rw [← h'.2.2] at h; exact h b hi

/-! ## Calm code: values, `local.get`s and labels -/

/-- Code made of values, `local.get`s and labels only. -/
def Calm (body : List Admin) : Prop :=
  ∀ x ∈ body, x.val? ≠ none ∨ (∃ j, x = .plain (.localGet j)) ∨ ∃ n cont is, x = .label n cont is

theorem Calm.absurd {body : List Admin} (hc : Calm body) {x : Admin} (hx : x ∈ body)
    (hbad : x = .trap ∨ x = .plain .return_ ∨ x = .plain .throwRef ∨ (∃ l, x = .plain (.br l)) ∨
      x.IsReturnCallRef) : False := by
  rcases hc x hx with h | ⟨j, rfl⟩ | ⟨n, cont, is, rfl⟩
  · rcases hbad with rfl | rfl | rfl | ⟨l, rfl⟩ | hr
    · exact h rfl
    · exact h rfl
    · exact h rfl
    · exact h rfl
    · exact h (IsReturnCallRef.val_none hr)
  · rcases hbad with h | h | h | ⟨l, h⟩ | h <;> simp_all [Admin.IsReturnCallRef]
  · rcases hbad with h | h | h | ⟨l, h⟩ | h <;> simp_all [Admin.IsReturnCallRef]

theorem Calm.absurd_app {body : List Admin} (hc : Calm body) {pre post : List Admin} {x : Admin}
    (hb : body = pre ++ [x] ++ post)
    (hbad : x = .trap ∨ x = .plain .return_ ∨ x = .plain .throwRef ∨ (∃ l, x = .plain (.br l)) ∨
      x.IsReturnCallRef) : False :=
  hc.absurd (by rw [hb]; simp) hbad

theorem calm_vals_fwd (us : List Val) (js : List LocalIdx) : Calm (vals us ++ fwdCode js) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact .inl (mem_vals hx)
  · simp only [fwdCode, expression, List.map_map, List.mem_map, Function.comp_apply] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact .inr (.inl ⟨j, rfl⟩)

theorem calm_label (n : Nat) (cont : List Instr) (is : List Admin) : Calm [.label n cont is] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  exact .inr (.inr ⟨n, cont, is, hx⟩)

/-! ## Inversions -/

theorem fam_absurd {e : Admin} {k : Fam} {args : List Val} (h : FamShape k (vals args ++ [e]))
    (he : famOf e ≠ k) : False :=
  he (famOf_of_shape h).2

/-- A host-free step of one non-value admin is a head step. -/
theorem head_single {P : Profile} {s : Store H} {f : Frame} {a : Admin} {c' : Config H}
    (hs : Step P noHost ⟨s, f, [a]⟩ c') (ha : a.val? = none) (ht : a ≠ .trap)
    (hth : a ≠ .plain .throwRef) : Head P s f [] a c' := by
  obtain ⟨vs, args, e, rest, c₀, hfnv, hh, hc⟩ := head_of_step hs (by simpa using ht.symm)
    (by simpa using hth.symm)
  have hf : fnv [a] = ([], [a]) := fnv_cons_of_none ha []
  have hv : vs ++ args = [] ∧ e :: rest = [a] := by
    rw [hf] at hfnv
    exact ⟨(Prod.mk.inj hfnv).1.symm, (Prod.mk.inj hfnv).2.symm⟩
  have hvs : vs = [] ∧ args = [] := List.append_eq_nil_iff.mp hv.1
  have he : e = a ∧ rest = [] := List.cons.inj hv.2
  rw [hvs.2, he.1] at hh
  rw [hc, hvs.1, he.2]
  simpa using hh

/-- A host-free step of values followed by a non-value is a head step. -/
theorem head_vals_cons {P : Profile} {s : Store H} {f : Frame} {us : List Val} {e : Admin}
    {rest : List Admin} {c' : Config H} (hs : Step P noHost ⟨s, f, vals us ++ e :: rest⟩ c')
    (he : e.val? = none) (ht : Admin.trap ∉ e :: rest) (hth : Admin.plain .throwRef ∉ e :: rest) :
    ∃ vs₀ args c₀, us = vs₀ ++ args ∧ Head P s f args e c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs₀ ++ c₀.code ++ rest⟩ := by
  obtain ⟨vs₀, args, e', rest', c₀, hfnv, hh, hc⟩ := head_of_step hs
    (by simpa [not_mem_vals_of (x := .trap) rfl] using ht)
    (by simpa [not_mem_vals_of (x := .plain .throwRef) rfl] using hth)
  have hf : fnv (vals us ++ e :: rest) = (us, e :: rest) := by
    simp [fnv_cons_of_none he]
  have hv : us = vs₀ ++ args ∧ e :: rest = e' :: rest' := by
    rw [hf] at hfnv
    exact ⟨(Prod.mk.inj hfnv).1, (Prod.mk.inj hfnv).2⟩
  have he' : e = e' ∧ rest = rest' := List.cons.inj hv.2
  refine ⟨vs₀, args, c₀, hv.1, he'.1 ▸ hh, ?_⟩
  rw [hc, he'.2]

/-- **A step of a label around calm code.** -/
theorem label_step {P : Profile} {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {body : List Admin} {c' : Config H} (hs : Step P noHost ⟨s, f, [.label n cont body]⟩ c')
    (hb : Calm body) :
    (∃ s' f' body', Step P noHost ⟨s, f, body⟩ ⟨s', f', body'⟩ ∧
      c' = ⟨s', f', [.label n cont body']⟩) ∨ (∃ us, body = vals us ∧ c' = ⟨s, f, vals us⟩) := by
  have hh : Head P s f [] (.label n cont body) c' := head_single hs rfl (by simp) (by simp)
  cases hh with
  | parametric h => exact (fam_absurd (ParametricStep.shape h) (by simp [famOf])).elim
  | numeric h => exact (fam_absurd (NumericStep.shape h) (by simp [famOf])).elim
  | vector h => exact (fam_absurd (VectorStep.shape h) (by simp [famOf])).elim
  | «variable» h => exact (fam_absurd (VariableStep.shape h) (by simp [famOf])).elim
  | table h => exact (fam_absurd (TableStep.shape h) (by simp [famOf])).elim
  | memory h => exact (fam_absurd (MemoryStep.shape h) (by simp [famOf])).elim
  | reference h => exact (fam_absurd (RefStep.shape h) (by simp [famOf])).elim
  | aggregate h => exact (fam_absurd (AggregateStep.shape h) (by simp [famOf])).elim
  | ctxtLabel h => exact .inl ⟨_, _, _, h, rfl⟩
  | labelVals hb' => exact .inr ⟨_, hb', rfl⟩
  | brLabelZero hb' => exact (hb.absurd_app hb' (by simp)).elim
  | brLabelSucc hb' => exact (hb.absurd_app hb' (by simp)).elim
  | returnLabel hb' => exact (hb.absurd_app hb' (by simp)).elim
  | callRefFunc _ hc => simp [Admin.IsCallRef] at hc
  | returnCallRefLabel hb' hc =>
    exact (hb.absurd (by rw [hb']; simp) (.inr (.inr (.inr (.inr hc))))).elim
  | trapLabel => exact (hb.absurd (x := .trap) (by simp) (by simp)).elim
  | throwRefLabel => exact (hb.absurd (x := .plain .throwRef) (by simp) (by simp)).elim

/-- **A step of a frame around calm code.** -/
theorem frame_step {P : Profile} {s : Store H} {f F : Frame} {n : Nat}
    {body : List Admin} {c' : Config H} (hs : Step P noHost ⟨s, f, [.frame n F body]⟩ c')
    (hb : Calm body) :
    (∃ s' F' body', Step P noHost ⟨s, F, body⟩ ⟨s', F', body'⟩ ∧
      c' = ⟨s', f, [.frame n F' body']⟩) ∨
      (∃ us, body = vals us ∧ us.length = n ∧ c' = ⟨s, f, vals us⟩) := by
  have hh : Head P s f [] (.frame n F body) c' := head_single hs rfl (by simp) (by simp)
  cases hh with
  | parametric h => exact (fam_absurd (ParametricStep.shape h) (by simp [famOf])).elim
  | numeric h => exact (fam_absurd (NumericStep.shape h) (by simp [famOf])).elim
  | vector h => exact (fam_absurd (VectorStep.shape h) (by simp [famOf])).elim
  | «variable» h => exact (fam_absurd (VariableStep.shape h) (by simp [famOf])).elim
  | table h => exact (fam_absurd (TableStep.shape h) (by simp [famOf])).elim
  | memory h => exact (fam_absurd (MemoryStep.shape h) (by simp [famOf])).elim
  | reference h => exact (fam_absurd (RefStep.shape h) (by simp [famOf])).elim
  | aggregate h => exact (fam_absurd (AggregateStep.shape h) (by simp [famOf])).elim
  | ctxtFrame h => exact .inl ⟨_, _, _, h, rfl⟩
  | frameVals hb' hn => exact .inr ⟨_, hb', hn, rfl⟩
  | returnFrame hb' => exact (hb.absurd_app hb' (by simp)).elim
  | callRefFunc _ hc => simp [Admin.IsCallRef] at hc
  | returnCallRefFrameNull hb' hc =>
    exact (hb.absurd (by rw [hb']; simp) (.inr (.inr (.inr (.inr hc))))).elim
  | returnCallRefFrameAddr hb' hc =>
    exact (hb.absurd (by rw [hb']; simp) (.inr (.inr (.inr (.inr hc))))).elim
  | trapFrame => exact (hb.absurd (x := .trap) (by simp) (by simp)).elim
  | throwRefFrame => exact (hb.absurd (x := .plain .throwRef) (by simp) (by simp)).elim

theorem localGet_inv {s : Store H} {f : Frame} {l : List Admin} {c : Config H}
    (h : VariableStep ⟨s, f, l⟩ c) {args : List Val} {j : LocalIdx}
    (hl : l = vals args ++ [.plain (.localGet j)]) :
    args = [] ∧ ∃ v, f.local? j = some (some v) ∧ c = ⟨s, f, [v.toAdmin]⟩ := by
  cases h with
  | localGet hloc =>
    have h2 := append_singleton_inj.mp (show [] ++ [_] = vals args ++ [_] from hl)
    simp only [Admin.plain.injEq, Instr.localGet.injEq] at h2
    obtain ⟨h1, rfl⟩ := h2
    exact ⟨List.map_eq_nil_iff.mp h1.symm, _, hloc, rfl⟩
  | localSet => have := congrArg List.getLast? hl; simp at this
  | localTee => have := congrArg List.getLast? hl; simp at this
  | globalGet => have := congrArg List.getLast? hl; simp at this
  | globalSet => have := congrArg List.getLast? hl; simp at this

/-- **A step of a forwarding body**: the next `local.get` reads a set local. -/
theorem seq_step {P : Profile} {s : Store H} {f : Frame} {us : List Val} {j : LocalIdx}
    {js : List LocalIdx} {c' : Config H}
    (hs : Step P noHost ⟨s, f, vals us ++ fwdCode (j :: js)⟩ c') :
    ∃ v, f.local? j = some (some v) ∧ c' = ⟨s, f, vals (us ++ [v]) ++ fwdCode js⟩ := by
  have hcalm : Calm (fwdCode (j :: js)) := by simpa using calm_vals_fwd [] (j :: js)
  have hcode : fwdCode (j :: js) = .plain (.localGet j) :: fwdCode js := rfl
  obtain ⟨vs₀, args, c₀, hus, hh, hceq⟩ : ∃ vs₀ args c₀, us = vs₀ ++ args ∧
      Head P s f args (.plain (.localGet j)) c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs₀ ++ c₀.code ++ fwdCode js⟩ :=
    head_vals_cons (hcode ▸ hs) rfl (fun hx => hcalm.absurd (hcode ▸ hx) (.inl rfl))
      (fun hx => hcalm.absurd (hcode ▸ hx) (.inr (.inr (.inl rfl))))
  cases hh with
  | parametric h => exact (fam_absurd (ParametricStep.shape h) (by simp [famOf])).elim
  | numeric h => exact (fam_absurd (NumericStep.shape h) (by simp [famOf])).elim
  | vector h => exact (fam_absurd (VectorStep.shape h) (by simp [famOf])).elim
  | «variable» h =>
    obtain ⟨hargs, v, hv, hc₀⟩ : args = [] ∧ ∃ v, f.local? j = some (some v) ∧
        c₀ = ⟨s, f, [v.toAdmin]⟩ := localGet_inv h rfl
    refine ⟨v, hv, ?_⟩
    rw [hceq, hc₀, hus, hargs]
    simp [vals]
  | table h => exact (fam_absurd (TableStep.shape h) (by simp [famOf])).elim
  | memory h => exact (fam_absurd (MemoryStep.shape h) (by simp [famOf])).elim
  | reference h => exact (fam_absurd (RefStep.shape h) (by simp [famOf])).elim
  | aggregate h => exact (fam_absurd (AggregateStep.shape h) (by simp [famOf])).elim
  | callRefNull hcr => simp [Admin.IsCallRef] at hcr
  | callRefFunc _ hcr => simp [Admin.IsCallRef] at hcr

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
