module

public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Run
public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# Invoking a forwarding function: the shapes are closed under steps

`FwdAt S a fi fn ps rs js vs`: address `a` of `S` holds the Wasm function `fn` (no locals, body
`local.get js`) of type `ps → rs`, and the arguments `vs` (as many as `ps`) contain no function
reference. Then, for every profile and every host:

* `Sh.step`: every step from a shape is to a shape of smaller measure;
* `invoke_result`: a run of the invocation that reaches a result reaches the projection
  `proj js vs`, of length `|rs|`, in the same store;
* `invoke_not_diverges`: the invocation does not diverge;
* `invoke_run`: the projection, when defined and of length `|rs|`, is reached.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-- The data of a forwarding invocation. -/
structure FwdAt (S : Store H) (a : Nat) (fi : FuncInst H) (fn : Func) (ps rs : Ty (.list .val))
    (js : List LocalIdx) (vs : List Val) : Prop where
  hf : S.funcs[a]? = some fi
  hcode : fi.code = .wasm fn
  he : Expand fi.type (.func ps rs)
  hloc : fn.locals = []
  hbody : fn.body = js.map .localGet
  hvs : vs.length = ps.length
  hnf : NoFuncRef vs

section
variable {S : Store H} {a : Nat} {fi : FuncInst H} {fn : Func} {ps rs : Ty (.list .val)}
  {js : List LocalIdx} {vs : List Val}

/-- The frame of the call. -/
abbrev callFrame (fi : FuncInst H) (vs : List Val) : Frame := Frame.forCall fi.module vs []

theorem callFrame_local (fi : FuncInst H) (vs : List Val) (j : LocalIdx) :
    (callFrame fi vs).local? j = vs[j.toNat]?.map some := by
  simp [callFrame, Frame.forCall, Frame.local?, List.getElem?_map]

/-- The shapes of the invocation. -/
abbrev ShF (hF : FwdAt S a fi fn ps rs js vs) : Config H → Nat → Prop :=
  let _ := hF
  Sh S a fi.type vs rs.length (callFrame fi vs) js

theorem not_hostAt (hF : FwdAt S a fi fn ps rs js vs) : ¬ HostAt S a := by
  rintro ⟨fi', hh, hf', hc'⟩
  have hfi : fi' = fi := Option.some.inj (hf'.symm.trans hF.hf)
  have hc : FuncCode.host hh = FuncCode.wasm fn := (hfi ▸ hc').symm.trans hF.hcode
  cases hc

theorem not_mem_s0 {x : Admin} (hx : x.val? = none) (hc : x ≠ .callRefType fi.type) :
    x ∉ vals vs ++ [.ref (.func a), .callRefType fi.type] := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact mem_vals h hx
  · rcases List.mem_cons.mp h with rfl | h
    · cases hx
    · exact hc (List.mem_singleton.mp h)

theorem noHostRef_s0 (hF : FwdAt S a fi fn ps rs js vs) :
    NoHostRef S (vals vs ++ [.ref (.func a), .callRefType fi.type]) := by
  intro b hb
  cases hb with
  | here h =>
    show ¬ HostAt S b
    rcases List.mem_append.mp h with h1 | h2
    · obtain ⟨u, hu, hu'⟩ : ∃ u ∈ vs, u.toAdmin = .ref (.func b) := List.mem_map.mp h1
      exact absurd (toAdmin_ref hu') (hF.hnf u hu b)
    · have hb' : b = a := by simpa using h2
      exact hb' ▸ not_hostAt hF
  | label h _ => exact absurd h (not_mem_s0 rfl (by simp))
  | handler h _ => exact absurd h (not_mem_s0 rfl (by simp))
  | frame h _ => exact absurd h (not_mem_s0 rfl (by simp))

/-- The data of the `call_ref` head step at `s0` are the invoked function's. -/
theorem callRefFunc_data (hF : FwdAt S a fi fn ps rs js vs) {vs₀ vs' : List Val} {a' : Nat}
    {fi' : FuncInst H} {ps' rs' : Ty (.list .val)} {code' : Func}
    (hus : vs ++ [.ref (.func a)] = vs₀ ++ (vs' ++ [.ref (.func a')]))
    (hf' : S.funcs[a']? = some fi') (he' : Expand fi'.type (.func ps' rs'))
    (hn' : vs'.length = ps'.length) (hcode' : fi'.code = .wasm code') :
    vs₀ = [] ∧ vs' = vs ∧ fi' = fi ∧ code' = fn ∧ rs' = rs := by
  have h1 : vs = vs₀ ++ vs' ∧ Val.ref (.func a) = .ref (.func a') :=
    append_singleton_inj.mp (by simpa using hus)
  have ha : a' = a := by simpa using h1.2.symm
  have hfi : fi' = fi := Option.some.inj ((ha ▸ hf').symm.trans hF.hf)
  have hcd : FuncCode.wasm code' = FuncCode.wasm fn := hcode'.symm.trans (hfi ▸ hF.hcode)
  have hE : (Ty.func ps' rs' : CCompType) = .func ps rs :=
    Expand.det (hfi ▸ he') hF.he
  have hps : ps' = ps ∧ rs' = rs := by simpa using hE
  have hl : vs₀.length + vs'.length = vs'.length := by
    have hlen : vs.length = vs₀.length + vs'.length := by rw [h1.1, List.length_append]
    rw [← hlen, hF.hvs, hn', hps.1]
  have hv0 : vs₀ = [] := List.eq_nil_of_length_eq_zero (by omega)
  refine ⟨hv0, ?_, hfi, by simpa using hcd, hps.2⟩
  rw [h1.1, hv0, List.nil_append]

theorem s0_step {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs)
    {c' : Config H} (hs : Step P host ⟨S, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ c') :
    c' = ⟨S, {}, [.frame rs.length (callFrame fi vs)
      [.label rs.length [] (vals [] ++ fwdCode (js.drop 0))]]⟩ := by
  have hcode : vals vs ++ [.ref (.func a), .callRefType fi.type] =
      vals (vs ++ [.ref (.func a)]) ++ [.callRefType fi.type] := by simp [vals, Val.toAdmin]
  have h' : Step P noHost ⟨S, {}, vals (vs ++ [.ref (.func a)]) ++ [.callRefType fi.type]⟩ c' :=
    hcode ▸ Step.noHost_of hs (noHostRef_s0 hF)
  obtain ⟨vs₀, args, c₀, hus, hh, hc⟩ : ∃ vs₀ args c₀, vs ++ [.ref (.func a)] = vs₀ ++ args ∧
      Head P S {} args (.callRefType fi.type) c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs₀ ++ c₀.code ++ []⟩ :=
    head_vals_cons h' rfl (by simp) (by simp)
  cases hh with
  | parametric h => exact (fam_absurd (ParametricStep.shape h) (by simp [famOf])).elim
  | numeric h => exact (fam_absurd (NumericStep.shape h) (by simp [famOf])).elim
  | vector h => exact (fam_absurd (VectorStep.shape h) (by simp [famOf])).elim
  | «variable» h => exact (fam_absurd (VariableStep.shape h) (by simp [famOf])).elim
  | table h => exact (fam_absurd (TableStep.shape h) (by simp [famOf])).elim
  | memory h => exact (fam_absurd (MemoryStep.shape h) (by simp [famOf])).elim
  | reference h => exact (fam_absurd (RefStep.shape h) (by simp [famOf])).elim
  | aggregate h => exact (fam_absurd (AggregateStep.shape h) (by simp [famOf])).elim
  | callRefNull _ => exact absurd (append_singleton_inj.mp hus).2 (by simp)
  | callRefFunc ha _ hf' he' hn' hcode' =>
    show c' = _
    obtain ⟨hv0, hvs, hfi, hcd, hrs⟩ := callRefFunc_data hF (ha ▸ hus) hf' he' hn' hcode'
    rw [hc, hv0, hvs, hfi, hcd, hrs]
    simp [callFrame, hF.hloc, hF.hbody, fwdCode]

theorem vals_inj {us us' : List Val} (h : vals us = vals us') : us = us' := by
  have := congrArg fnv h
  simpa using this

theorem fwd_plain (js : List LocalIdx) : ∀ x ∈ fwdCode js, ∃ i, x = .plain i := by
  intro x hx
  simp only [fwdCode, expression, List.map_map, List.mem_map, Function.comp_apply] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact ⟨_, rfl⟩

theorem calm_vals (us : List Val) : Calm (vals us) := by
  simpa [fwdCode, expression] using calm_vals_fwd us []

theorem noHostRef_vals' {S : Store H} {us : List Val} (hus : NoFuncRef us) :
    NoHostRef S (vals us) := by
  simpa using noHostRef_vals (S := S) hus (l := []) (by simp)

/-- A step of a frame around a label around calm code. -/
theorem frame_label_step {P : Profile} {s : Store H} {f F : Frame} {n : Nat} {X : List Admin}
    {c' : Config H} (hs : Step P noHost ⟨s, f, [.frame n F [.label n [] X]]⟩ c') (hX : Calm X) :
    (∃ s' F' X', Step P noHost ⟨s, F, X⟩ ⟨s', F', X'⟩ ∧
      c' = ⟨s', f, [.frame n F' [.label n [] X']]⟩) ∨
      (∃ us, X = vals us ∧ c' = ⟨s, f, [.frame n F (vals us)]⟩) := by
  rcases frame_step hs (calm_label _ _ _) with ⟨s', F', body', hin, hc⟩ | ⟨us', hb, -, -⟩
  · rcases label_step hin hX with ⟨s'', f'', X', hin2, hb2⟩ | ⟨us, hX', hc2⟩
    · have hcfg : s' = s'' ∧ F' = f'' ∧ body' = [.label n [] X'] := by simpa using hb2
      exact .inl ⟨s'', f'', X', hin2, by rw [hc, hcfg.1, hcfg.2.1, hcfg.2.2]⟩
    · have hcfg : s' = s ∧ F' = F ∧ body' = vals us := by simpa using hc2
      exact .inr ⟨us, hX', by rw [hc, hcfg.1, hcfg.2.1, hcfg.2.2]⟩
  · exact absurd (congrArg fnv hb) (by simp [fnv_cons_of_none (a := .label _ _ _) rfl])

theorem fwdCode_cons (j : LocalIdx) (js : List LocalIdx) :
    fwdCode (j :: js) = .plain (.localGet j) :: fwdCode js := rfl

theorem s1_step_cons {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs)
    {k : Nat} {us : List Val} {j : LocalIdx} {rest : List LocalIdx}
    (hus : proj (js.take k) vs = some us) (hd : js.drop k = j :: rest) {c' : Config H}
    (hs : Step P host ⟨S, {}, [.frame rs.length (callFrame fi vs)
      [.label rs.length [] (vals us ++ fwdCode (js.drop k))]]⟩ c') :
    ∃ v, vs[j.toNat]? = some v ∧ c' = ⟨S, {}, [.frame rs.length (callFrame fi vs)
      [.label rs.length [] (vals (us ++ [v]) ++ fwdCode rest)]]⟩ := by
  have hnr : NoFuncRef us := fun u hu => hF.hnf u (proj_mem hus u hu)
  have h' : Step P noHost ⟨S, {}, [.frame rs.length (callFrame fi vs)
      [.label rs.length [] (vals us ++ fwdCode (j :: rest))]]⟩ c' :=
    hd ▸ Step.noHost_of hs (noHostRef_frame (noHostRef_label (noHostRef_vals hnr (fwd_plain _))))
  rcases frame_label_step h' (calm_vals_fwd us _) with ⟨s', F', X', hin, hc⟩ | ⟨us', hX, -⟩
  · obtain ⟨v, hv, hin'⟩ : ∃ v, (callFrame fi vs).local? j = some (some v) ∧
        (⟨s', F', X'⟩ : Config H) = ⟨S, callFrame fi vs, vals (us ++ [v]) ++ fwdCode rest⟩ :=
      seq_step hin
    have hcfg : s' = S ∧ F' = callFrame fi vs ∧ X' = vals (us ++ [v]) ++ fwdCode rest := by
      simpa using hin'
    have hvj : vs[j.toNat]? = some v := by simpa [callFrame_local] using hv
    exact ⟨v, hvj, by rw [hc, hcfg.1, hcfg.2.1, hcfg.2.2]⟩
  · exact absurd (congrArg fnv hX)
      (by simp [fwdCode_cons, fnv_cons_of_none (a := .plain (.localGet j)) rfl])

theorem s1_step_nil {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs)
    {k : Nat} {us : List Val} (hus : proj (js.take k) vs = some us) (hd : js.drop k = [])
    {c' : Config H}
    (hs : Step P host ⟨S, {}, [.frame rs.length (callFrame fi vs)
      [.label rs.length [] (vals us ++ fwdCode (js.drop k))]]⟩ c') :
    c' = ⟨S, {}, [.frame rs.length (callFrame fi vs) (vals us)]⟩ := by
  have hnr : NoFuncRef us := fun u hu => hF.hnf u (proj_mem hus u hu)
  have hcode : vals us ++ fwdCode (js.drop k) = vals us := by simp [hd, fwdCode, expression]
  have h' : Step P noHost ⟨S, {}, [.frame rs.length (callFrame fi vs)
      [.label rs.length [] (vals us)]]⟩ c' :=
    hcode ▸ Step.noHost_of hs (noHostRef_frame (noHostRef_label (noHostRef_vals hnr (fwd_plain _))))
  rcases frame_label_step h' (calm_vals us) with ⟨s', F', X', hin, -⟩ | ⟨us', hX, hc⟩
  · exact (not_step_vals hin).elim
  · have hu : us' = us := (vals_inj hX).symm
    rw [hc, hu]

theorem s2_step {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs)
    {us : List Val} (hus : proj js vs = some us) {c' : Config H}
    (hs : Step P host ⟨S, {}, [.frame rs.length (callFrame fi vs) (vals us)]⟩ c') :
    us.length = rs.length ∧ c' = ⟨S, {}, vals us⟩ := by
  have hnr : NoFuncRef us := fun u hu => hF.hnf u (proj_mem hus u hu)
  have h' := Step.noHost_of hs (noHostRef_frame (noHostRef_vals' hnr))
  rcases frame_step h' (calm_vals us) with ⟨s', F', body', hin, -⟩ | ⟨us', hb, hn, hc⟩
  · exact (not_step_vals hin).elim
  · have hu : us' = us := (vals_inj hb).symm
    exact ⟨hu ▸ hn, hu ▸ hc⟩

/-- **Every step from a shape is to a shape of smaller measure.** -/
theorem Sh.step {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs)
    {c c' : Config H} {m : Nat} (hsh : Sh S a fi.type vs rs.length (callFrame fi vs) js c m)
    (hs : Step P host c c') :
    ∃ m', Sh S a fi.type vs rs.length (callFrame fi vs) js c' m' ∧ m' < m := by
  cases hsh with
  | s0 =>
    refine ⟨js.length - 0 + 2, ?_, by omega⟩
    rw [s0_step hF hs]
    exact .s1 0 [] (Nat.zero_le _) (by simp [proj])
  | s1 k us hk hus =>
    show ∃ m', Sh S a fi.type vs rs.length (callFrame fi vs) js c' m' ∧ m' < js.length - k + 2
    cases hd : js.drop k with
    | nil =>
      have hkl : k = js.length := by
        have : js.length ≤ k := List.drop_eq_nil_iff.mp hd
        omega
      have hus' : proj js vs = some us := by rw [← List.take_length (l := js), ← hkl]; exact hus
      refine ⟨1, ?_, by omega⟩
      rw [s1_step_nil hF hus hd hs]
      exact .s2 us hus'
    | cons j rest =>
      obtain ⟨v, hv, hc⟩ := s1_step_cons hF hus hd hs
      have hk' : js[k]? = some j := by rw [← List.head?_drop, hd]; rfl
      obtain ⟨hlt, hjk⟩ : ∃ h : k < js.length, js[k] = j := List.getElem?_eq_some_iff.mp hk'
      have hd' : js.drop (k + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      refine ⟨js.length - (k + 1) + 2, ?_, by omega⟩
      rw [hc, ← hd']
      exact .s1 (k + 1) (us ++ [v]) hlt (proj_take_succ hlt hus (hjk ▸ hv))
  | s2 us hus =>
    obtain ⟨hn, hc⟩ := s2_step hF hus hs
    refine ⟨0, ?_, by omega⟩
    rw [hc]
    exact .s3 us hus hn
  | s3 us hus hn =>
    have hnr : NoFuncRef us := fun u hu => hF.hnf u (proj_mem hus u hu)
    exact (not_step_vals (Step.noHost_of hs (noHostRef_vals' hnr))).elim

theorem Sh.steps {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs)
    {c d : Config H} {m : Nat} (hsh : Sh S a fi.type vs rs.length (callFrame fi vs) js c m)
    (hs : Steps P host c d) : ∃ m', Sh S a fi.type vs rs.length (callFrame fi vs) js d m' := by
  induction hs with
  | refl => exact ⟨m, hsh⟩
  | tail _ hst ih =>
    obtain ⟨m', hm'⟩ := ih
    obtain ⟨m'', hm'', -⟩ := Sh.step hF hm' hst
    exact ⟨m'', hm''⟩

theorem frame_ne_toAdmin {n : Nat} {F : Frame} {b : List Admin} (r : Result) :
    ([.frame n F b] : List Admin) ≠ r.toAdmin := by
  intro h
  have hf := congrArg fnv h
  cases r <;> simp [Result.toAdmin, fnv_cons_of_none (a := .frame _ _ _) rfl,
    fnv_cons_of_none (a := .plain .throwRef) rfl] at hf

theorem s0_ne_toAdmin (r : Result) :
    vals vs ++ [.ref (.func a), .callRefType fi.type] ≠ r.toAdmin := by
  intro h
  have hf := congrArg fnv h
  cases r <;> simp [Result.toAdmin, fnv_cons_of_none (a := .callRefType fi.type) rfl,
    fnv_cons_of_none (a := .plain .throwRef) rfl] at hf

theorem vals_eq_toAdmin {us : List Val} {r : Result} (h : vals us = r.toAdmin) :
    r = .values us := by
  have hf := congrArg fnv h
  cases r with
  | values ws =>
    have hw : us = ws := by simpa [Result.toAdmin] using hf
    rw [hw]
  | throw b => simp [Result.toAdmin, fnv_cons_of_none (a := .plain .throwRef) rfl] at hf
  | trap => simp [Result.toAdmin] at hf

theorem invoke_eq (hF : FwdAt S a fi fn ps rs js vs) :
    invoke S a vs = ⟨S, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
  simp [invoke, hF.hf]

/-- **The result of a forwarding invocation.** -/
theorem invoke_result {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs)
    {d : Config H} {r : Result} (hs : Steps P host (invoke S a vs) d) (hr : d.code = r.toAdmin) :
    ∃ us, proj js vs = some us ∧ us.length = rs.length ∧ d = ⟨S, {}, vals us⟩ ∧
      r = .values us := by
  obtain ⟨m, hm⟩ : ∃ m, Sh S a fi.type vs rs.length (callFrame fi vs) js d m :=
    Sh.steps hF (Sh.s0 (a := a) (n := rs.length) (F := callFrame fi vs)) (invoke_eq hF ▸ hs)
  cases hm with
  | s0 => exact absurd hr (s0_ne_toAdmin r)
  | s1 k us _ _ => exact absurd hr (frame_ne_toAdmin r)
  | s2 us _ => exact absurd hr (frame_ne_toAdmin r)
  | s3 us hus hn => exact ⟨us, hus, hn, rfl, vals_eq_toAdmin hr⟩

theorem Sh.not_diverges {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs) :
    ∀ (m : Nat) {c : Config H}, Sh S a fi.type vs rs.length (callFrame fi vs) js c m →
      ¬ Diverges P host c := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c hsh hd
    obtain ⟨b, hb, hd'⟩ := Silmaril.InfiniteTrace.unfold hd
    obtain ⟨m', hm', hlt⟩ := Sh.step hF hsh hb
    exact ih m' hlt hm' hd'

/-- **A forwarding invocation does not diverge.** -/
theorem invoke_not_diverges {P : Profile} {host : HostSemantics H}
    (hF : FwdAt S a fi fn ps rs js vs) : ¬ Diverges P host (invoke S a vs) := by
  rw [invoke_eq hF]
  exact Sh.not_diverges hF _ (Sh.s0 (a := a) (n := rs.length) (F := callFrame fi vs))


theorem step_lift {P : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {is is' : List Admin} (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (vs₀ : List Val)
    (rest : List Admin) : Step P host ⟨s, f, vals vs₀ ++ is ++ rest⟩ ⟨s', f', vals vs₀ ++ is' ++ rest⟩ := by
  by_cases hne : vs₀ ≠ [] ∨ rest ≠ []
  · exact .ctxtInstrs h hne
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    simpa [vals] using h

theorem body_run {P : Profile} {host : HostSemantics H} (S : Store H) (F : Frame)
    (vs : List Val) (hloc : ∀ j : LocalIdx, F.local? j = vs[j.toNat]?.map some) :
    ∀ (js' : List LocalIdx) (us₀ us' : List Val), proj js' vs = some us' →
      Steps P host ⟨S, F, vals us₀ ++ fwdCode js'⟩ ⟨S, F, vals (us₀ ++ us')⟩
  | [], us₀, us', h => by
    simp only [proj, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp only [fwdCode, List.map_nil, expression, List.append_nil]
    exact .refl
  | j :: js', us₀, us', h => by
    simp only [proj, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us'', hus'', h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    have hst : Step P host ⟨S, F, vals us₀ ++ [.plain (.localGet j)] ++ fwdCode js'⟩
        ⟨S, F, vals us₀ ++ [v.toAdmin] ++ fwdCode js'⟩ :=
      step_lift (.«variable» (.localGet (by rw [hloc, hv]; rfl))) us₀ (fwdCode js')
    have hrun := body_run (P := P) (host := host) S F vs hloc js' (us₀ ++ [v]) us'' hus''
    refine Relation.ReflTransGen.head ?_ (by simpa using hrun)
    simpa [fwdCode, expression] using hst

theorem steps_frame_label {P : Profile} {host : HostSemantics H} {n : Nat} {S S' : Store H}
    {F F' : Frame} {X Y : List Admin} (h : Steps P host ⟨S, F, X⟩ ⟨S', F', Y⟩) :
    Steps P host ⟨S, {}, [.frame n F [.label n [] X]]⟩ ⟨S', {}, [.frame n F' [.label n [] Y]]⟩ := by
  let g : Config H → Config H := fun c => ⟨c.store, {}, [.frame n c.frame [.label n [] c.code]]⟩
  have hg : ∀ {c d : Config H}, Steps P host c d → Steps P host (g c) (g d) := by
    intro c d hcd
    induction hcd with
    | refl => exact .refl
    | @tail b e _ hst ih =>
      rcases b with ⟨s₁, f₁, c₁⟩
      rcases e with ⟨s₂, f₂, c₂⟩
      exact ih.tail (.ctxtFrame (.ctxtLabel hst))
  exact hg h

/-- **The run of a forwarding invocation.** -/
theorem invoke_run {P : Profile} {host : HostSemantics H} (hF : FwdAt S a fi fn ps rs js vs)
    {us : List Val} (hus : proj js vs = some us) (hn : us.length = rs.length) :
    Steps P host (invoke S a vs) ⟨S, {}, vals us⟩ := by
  rw [invoke_eq hF]
  have h1 : Step P host ⟨S, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩
      ⟨S, {}, [.frame rs.length (callFrame fi vs) [.label rs.length [] (vals [] ++ fwdCode js)]]⟩ := by
    have := Step.callRefFunc (P := P) (host := host) (f := {}) (c := .callRefType fi.type)
      (vs := vs) trivial hF.hf hF.he hF.hvs hF.hcode
    simpa [callFrame, hF.hloc, hF.hbody, fwdCode] using this
  have h2 := steps_frame_label (n := rs.length)
    (body_run (P := P) (host := host) S (callFrame fi vs) vs (callFrame_local fi vs) js [] us hus)
  have h3 : Step P host ⟨S, {}, [.frame rs.length (callFrame fi vs) [.label rs.length [] (vals us)]]⟩
      ⟨S, {}, [.frame rs.length (callFrame fi vs) (vals us)]⟩ := .ctxtFrame .labelVals
  have h4 : Step P host ⟨S, {}, [.frame rs.length (callFrame fi vs) (vals us)]⟩ ⟨S, {}, vals us⟩ :=
    .frameVals hn
  exact (Relation.ReflTransGen.head h1 (by simpa using h2)).tail h3 |>.tail h4


end

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
