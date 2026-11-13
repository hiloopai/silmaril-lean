module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.HeadDet
public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.Beh

/-!
# Unique local steps of `StepFX'`

In the deterministic profile without host calls, each step that the encoding of a kernel
instruction takes (at the first non-value of a frame's code) is the only step of that code:

* `uniq_core`: a Core head step of a plain instruction (`nop`, `drop`, `local.get`, `call`,
  `ref.func`, a `prim`'s instruction);
* `uniq_dropCont`, `uniq_invoke`, `uniq_block`, `uniq_ifTrue`, `uniq_ifFalse`, `uniq_contNew`,
  `uniq_resume`: the FX rules (`resume` with no other value in front of the continuation);
* `uniq_labelVals`, `uniq_frameVals`, `uniq_handlerVals`, `uniq_brZero`, `uniq_brSucc`: leaving
  a label, frame or handler;
* `ustep_plug`: a unique step of quiet code lifts to a unique step under an isolated context.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append fvals_nil fvals_cons fval?_toAdmin
  fvals_append_cons_inj fnvF fnvF_fvals_append fnvF_cons_none fvals_inj no_step_fvals'
  not_head_drop)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head famOf Fam famOf_of_shape)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type}

/-- `a` steps, and only to `b`. -/
def UStep {A : Type} (R : A → A → Prop) (a b : A) : Prop := R a b ∧ ∀ b', R a b' → b' = b

theorem suffix_cases {α : Type} {U A V₁ B : List α} (h : U ++ A = V₁ ++ B) :
    (∃ p, B = p ++ A ∧ U = V₁ ++ p) ∨ (∃ p, A = p ++ B ∧ V₁ = U ++ p) := by
  rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · exact Or.inr ⟨a', h2, h1⟩
  · exact Or.inl ⟨c', h2, h1⟩

theorem liftV_eq_append {vs : List Val} {p A : List FVal} (h : liftV vs = p ++ A) :
    ∃ p' A', vs = p' ++ A' ∧ p = liftV p' ∧ A = liftV A' := by
  obtain ⟨p', A', rfl, h1, h2⟩ := List.map_eq_append_iff.mp h
  exact ⟨p', A', rfl, h1.symm, h2.symm⟩

theorem liftV_inj {vs ws : List Val} (h : liftV vs = liftV ws) : vs = ws :=
  List.map_injective_iff.mpr (fun _ _ h => FVal.val.inj h) h

theorem head_callRef_inv {P : Profile} {s : Store H} {f : Frame} {args : List Val} {c : Admin}
    {c₀ : Config H} (hc : c.IsCallRef) (h : Head P s f args c c₀) :
    args = [.ref .null] ∨ ∃ vs a fi code, args = vs ++ [.ref (.func a)] ∧
      s.funcs[a]? = some fi ∧ fi.code = FuncCode.wasm code := by
  have hk := Silmaril.Wasm.SingleThreaded.Det.IsCallRef.famOf hc
  cases h with
  | callRefNull => exact Or.inl rfl
  | callRefFunc ha _ hf _ _ hcode => exact Or.inr ⟨_, _, _, _, ha, hf, hcode⟩
  | parametric h => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.ParametricStep.shape h)).2.symm.trans hk) (by decide)
  | numeric h => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.NumericStep.shape h)).2.symm.trans hk) (by decide)
  | vector h => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.VectorStep.shape h)).2.symm.trans hk) (by decide)
  | «variable» h => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.VariableStep.shape h)).2.symm.trans hk) (by decide)
  | table h => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.TableStep.shape h)).2.symm.trans hk) (by decide)
  | memory h => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.MemoryStep.shape h)).2.symm.trans hk) (by decide)
  | reference h => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.RefStep.shape h)).2.symm.trans hk) (by decide)
  | aggregate h => exact absurd ((famOf_of_shape (Silmaril.Wasm.SingleThreaded.Det.AggregateStep.shape h)).2.symm.trans hk) (by decide)
  | _ => exact absurd hc (by simp [Admin.IsCallRef])

/-- `StepFX'` in the deterministic profile, without host calls. -/
abbrev SD (o : GrowKind → Nat → Nat → Nat → Bool) (fx : H → Option FuncFX) :=
  StepFX' (Profile.deterministic o) (noHost (H := H)) fx

variable {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX} {s : Store H}
  {K : List (Option ContFX)} {F : Frame}

theorem last_eq {α : Type} {A B : List α} {x y : α} (h : A ++ [x] = B ++ [y]) : x = y :=
  (List.append_inj' h rfl).2 |> fun h => List.singleton_inj.mp h

/-- Two Core head steps of `.plain i` at suffixes of the same values. -/
theorem core_arm {U V₁ : List FVal} {args args₀ : List Val} {i : Instr} {c c₀ : Config H}
    (h : Head (Profile.deterministic o) s F args (.plain i) c)
    (h₀ : Head (Profile.deterministic o) s F args₀ (.plain i) c₀)
    (hV : U ++ liftV args₀ = V₁ ++ liftV args) : V₁ = U ∧ c = c₀ := by
  rcases suffix_cases hV with ⟨p, hB, hU⟩ | ⟨p, hA, hV1⟩
  · obtain ⟨p', A', hargs, hp, hA'⟩ := liftV_eq_append hB
    have hA₀ : A' = args₀ := (liftV_inj hA').symm
    obtain ⟨hp', hc⟩ := head_plain_det h h₀ (hA₀ ▸ hargs)
    have hp0 : p = [] := by rw [hp, hp']; rfl
    exact ⟨by rw [hU, hp0, List.append_nil], hc⟩
  · obtain ⟨p', A', hargs, hp, hA'⟩ := liftV_eq_append hA
    have hA₀ : A' = args := (liftV_inj hA').symm
    obtain ⟨hp', hc⟩ := head_plain_det h₀ h (hA₀ ▸ hargs)
    have hp0 : p = [] := by rw [hp, hp']; rfl
    exact ⟨by rw [hV1, hp0, List.append_nil], hc.symm⟩

/-- A Core `drop` with Core values in front is not `dropCont`. -/
theorem drop_arm {U V₁ : List FVal} {args₀ : List Val} {c₀ : Config H} {k : Nat}
    (h₀ : Head (Profile.deterministic o) s F args₀ (.plain .drop) c₀)
    (hV : U ++ liftV args₀ = V₁ ++ [FVal.cont k]) : False := by
  rcases List.eq_nil_or_concat args₀ with h | ⟨L, v, hL⟩
  · exact not_head_drop (h ▸ h₀)
  · have h1 : U ++ liftV L ++ [FVal.val v] = V₁ ++ [FVal.cont k] := by
      rw [← hV, hL]; simp [liftV]
    cases last_eq h1

/-- A Core head step of a call is not an FX `invoke`. -/
theorem invoke_arm {U V₁ : List FVal} {args₀ ws : List Val} {c : Admin} {c₀ : Config H}
    {a : Nat} {fi : FuncInst H} {hh : H} (hc : c.IsCallRef)
    (h₀ : Head (Profile.deterministic o) s F args₀ c c₀) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh)
    (hV : U ++ liftV args₀ = V₁ ++ (liftV ws ++ [.val (.ref (.func a))])) : False := by
  rcases head_callRef_inv hc h₀ with rfl | ⟨vs, a', fi', code, rfl, hf', hcode'⟩
  · have h1 : U ++ [FVal.val (.ref .null)] = V₁ ++ liftV ws ++ [FVal.val (.ref (.func a))] := by
      simpa [liftV] using hV
    cases last_eq h1
  · have h1 : U ++ liftV vs ++ [FVal.val (.ref (.func a'))] =
        V₁ ++ liftV ws ++ [FVal.val (.ref (.func a))] := by simpa [liftV] using hV
    have ha : a' = a := by have := last_eq h1; injection this with h; injection h with h; injection h
    have hfi : fi' = fi := by rw [← ha] at hf; exact Option.some.inj (hf'.symm.trans hf)
    have : FuncCode.wasm code = FuncCode.host hh := by rw [← hcode', ← hcode, hfi]
    cases this

/-- **A Core head step of a plain instruction is the only step.** -/
theorem uniq_core {U : List FVal} {args₀ : List Val} {i : Instr} {c₀ : Config H}
    {T : List AdminFX} (h₀ : Head (Profile.deterministic o) s F args₀ (.plain i) c₀)
    (hi : i ≠ .throwRef) {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals (U ++ liftV args₀) ++ .core (.plain i) :: T⟩ d) :
    d = ⟨c₀.store, K, c₀.frame, fvals U ++ c₀.code.map .core ++ T⟩ := by
  have hv : fval? (.core (.plain i)) = none := by
    simp [(Silmaril.Wasm.SingleThreaded.Det.Head.good h₀).val_none]
  obtain ⟨V₁, V₂, d₀, hV, hh, hd⟩ := local_inv hv (by simp) (by simpa using hi) h
  generalize he : AdminFX.core (.plain i) = e at hh
  cases hh with
  | core h' =>
    injection he with he
    obtain ⟨hU, hc⟩ := core_arm (he ▸ h') h₀ hV
    rw [hd, hU, hc]
  | dropCont => injection he with he; injection he with he; exact (drop_arm (he ▸ h₀) hV).elim
  | invoke hc hf hcode =>
    injection he with he
    exact (invoke_arm hc (he ▸ h₀) hf hcode (by simpa using hV)).elim
  | _ => cases he

theorem uniq_dropCont {U : List FVal} {k : Nat} {T : List AdminFX} {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals (U ++ [.cont k]) ++ .core (.plain .drop) :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, rfl⟩ := local_inv rfl (by simp) (by simp) h
  generalize he : AdminFX.core (.plain .drop) = e at hh
  cases hh with
  | core h' =>
    cases he
    rename_i args c₀
    rcases List.eq_nil_or_concat args with rfl | ⟨L, v, rfl⟩
    · exact absurd h' not_head_drop
    · have h1 : U ++ [FVal.cont k] = V₁ ++ liftV L ++ [FVal.val v] := by simpa [liftV] using hV
      cases last_eq h1
  | dropCont =>
    cases he
    obtain ⟨rfl, -⟩ := List.append_inj' hV rfl
    simp
  | invoke hc => cases he; exact absurd hc (by simp [Admin.IsCallRef])
  | _ => cases he

/-- Two `invoke`s of the same code: the same split and the same frame. -/
theorem invoke_invoke {U V₁ : List FVal} {ws vs : List Val} {a a' : Nat} {fi fi' : FuncInst H}
    {hh h₂ : H} {Fn F₂ : FuncFX} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hfx : fx hh = some Fn) (hn : ws.length = Fn.nparams) (hf' : s.funcs[a']? = some fi')
    (hcode' : fi'.code = .host h₂) (hfx' : fx h₂ = some F₂) (hn' : vs.length = F₂.nparams)
    (hV : U ++ liftV ws ++ [FVal.val (.ref (.func a))] =
      V₁ ++ liftV vs ++ [FVal.val (.ref (.func a'))]) :
    V₁ = U ∧ vs = ws ∧ F₂ = Fn := by
  obtain ⟨h2, h3⟩ := List.append_inj' hV rfl
  have ha : a = a' := by
    have := List.singleton_inj.mp h3; injection this with h; injection h with h; injection h
  have hfi : fi = fi' := Option.some.inj (hf.symm.trans (ha ▸ hf'))
  have hh₂ : hh = h₂ := by
    have : FuncCode.host hh = FuncCode.host h₂ := by rw [← hcode, ← hcode', hfi]
    injection this
  have hF : Fn = F₂ := Option.some.inj (hfx.symm.trans (hh₂ ▸ hfx'))
  have hlen : (liftV ws).length = (liftV vs).length := by simp [liftV, hn, hn', hF]
  obtain ⟨hU, hw⟩ := List.append_inj' h2 hlen
  exact ⟨hU.symm, (liftV_inj hw).symm, hF.symm⟩

theorem uniq_invoke {U : List FVal} {ws : List Val} {a : Nat} {c : Admin} {fi : FuncInst H}
    {hh : H} {Fn : FuncFX} {T : List AdminFX} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hfx : fx hh = some Fn) (hn : ws.length = Fn.nparams)
    {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals (U ++ liftV ws ++ [.val (.ref (.func a))]) ++ .core c :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ [.frame Fn.nresults (Frame.forCall Fn.module ws Fn.locals)
          [.label Fn.nresults [] (Fn.body.map InstrFX.toAdmin)]] ++ T⟩ := by
  have hv : fval? (.core c) = none := isCallRef_fval hc
  have hct : c ≠ .trap := by rintro rfl; exact hc
  have hcr : c ≠ .plain .throwRef := by rintro rfl; exact hc
  obtain ⟨V₁, V₂, d₀, hV, hh', hd⟩ := local_inv hv (by simpa using hct) (by simpa using hcr) h
  generalize he : AdminFX.core c = e at hh'
  cases hh' with
  | core h' =>
    injection he with he
    exact (invoke_arm hc (he ▸ h') hf hcode (by simpa using hV.symm)).elim
  | dropCont => injection he with he; exact absurd (he ▸ hc) (by simp [Admin.IsCallRef])
  | invoke _ hf' hcode' hfx' hn' =>
    obtain ⟨hU, hw, hF⟩ := invoke_invoke hf hcode hfx hn hf' hcode' hfx' hn' (by simpa using hV)
    rw [hd, hU, hw, hF]
  | _ => cases he

theorem uniq_block {U vs : List FVal} {bt : BlockType} {body : List InstrFX}
    {t₁ t₂ : List CValType} {T : List AdminFX} (hbt : F.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals (U ++ vs) ++ .block bt body :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ [.label t₂.length [] (fvals vs ++ body.map InstrFX.toAdmin)] ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, rfl⟩ := local_inv rfl (by simp) (by simp) h
  generalize he : AdminFX.block bt body = e at hh
  cases hh with
  | block hbt' hm' =>
    cases he
    rw [hbt] at hbt'
    cases hbt'
    obtain ⟨rfl, rfl⟩ := List.append_inj' hV (by omega)
    rfl
  | _ => cases he

theorem uniq_ifTrue {U : List FVal} {c : BitVec 32} (hc : c ≠ 0) {bt : BlockType}
    {b₁ b₂ : List InstrFX} {T : List AdminFX} {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals (U ++ [.val (Val.i32 c)]) ++ .if_ bt b₁ b₂ :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ [.block bt b₁] ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, rfl⟩ := local_inv rfl (by simp) (by simp) h
  generalize he : AdminFX.if_ bt b₁ b₂ = e at hh
  cases hh with
  | ifTrue =>
    cases he
    obtain ⟨rfl, -⟩ := List.append_inj' hV rfl
    rfl
  | ifFalse =>
    cases he
    have h1 := last_eq hV
    simp only [Val.i32, FVal.val.injEq, Val.num.injEq] at h1
    exact absurd (by cases h1; rfl) hc
  | _ => cases he

theorem uniq_ifFalse {U : List FVal} {bt : BlockType} {b₁ b₂ : List InstrFX} {T : List AdminFX}
    {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals (U ++ [.val (Val.i32 0)]) ++ .if_ bt b₁ b₂ :: T⟩ d) :
    d = ⟨s, K, F, fvals U ++ [.block bt b₂] ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, rfl⟩ := local_inv rfl (by simp) (by simp) h
  generalize he : AdminFX.if_ bt b₁ b₂ = e at hh
  cases hh with
  | ifTrue hc =>
    cases he
    have h1 := last_eq hV
    simp only [Val.i32, FVal.val.injEq, Val.num.injEq] at h1
    exact absurd (by cases h1; rfl) hc
  | ifFalse =>
    cases he
    obtain ⟨rfl, -⟩ := List.append_inj' hV rfl
    rfl
  | _ => cases he

theorem uniq_contNew {U : List FVal} {a : Nat} {fi : FuncInst H} {ct : TypeIdx}
    {T : List AdminFX} (hf : s.funcs[a]? = some fi) {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals (U ++ [.val (.ref (.func a))]) ++ .fx (.contNew ct) :: T⟩ d) :
    d = ⟨s, K ++ [some ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩], F,
      fvals U ++ [.contRef K.length] ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, rfl⟩ := local_inv rfl (by simp) (by simp) h
  generalize he : AdminFX.fx (.contNew ct) = e at hh
  cases hh with
  | contNew hf' =>
    cases he
    obtain ⟨rfl, h2⟩ := List.append_inj' hV rfl
    simp only [List.cons.injEq, FVal.val.injEq, Val.ref.injEq, Ref.func.injEq, and_true] at h2
    subst h2
    rw [hf] at hf'
    cases hf'
    rfl
  | contNewNull =>
    cases he
    cases last_eq hV
  | _ => cases he

theorem cont_split {V₁ vs : List FVal} {k k' : Nat} (h : [FVal.cont k] = V₁ ++ (vs ++ [.cont k'])) :
    V₁ = [] ∧ vs = [] ∧ k' = k := by
  have h1 : [] ++ [FVal.cont k] = V₁ ++ vs ++ [FVal.cont k'] := by simpa using h
  obtain ⟨h2, h3⟩ := List.append_inj' h1 rfl
  have hk : k' = k := by have := List.singleton_inj.mp h3; injection this with h; exact h.symm
  obtain ⟨h4, h5⟩ := List.append_eq_nil_iff.mp h2.symm
  exact ⟨h4, h5, hk⟩

theorem uniq_resume {k : Nat} {C : ContFX} {ct : TypeIdx} {hs : List OnClause}
    {hs' : List HClause} {T : List AdminFX} (hk : K[k]? = some (some C))
    (hr : hs.mapM (resolve s F) = some hs') {d : ConfigFX H}
    (h : SD o fx ⟨s, K, F, fvals [.cont k] ++ .fx (.resume ct hs) :: T⟩ d) :
    d = ⟨s, K.set k none, F, [.handler hs' (C.plug [])] ++ T⟩ := by
  obtain ⟨V₁, V₂, d₀, hV, hh, hd⟩ := local_inv rfl (by simp) (by simp) h
  generalize he : AdminFX.fx (.resume ct hs) = e at hh
  cases hh with
  | resume hk' hr' =>
    injection he with he
    injection he with _ he
    obtain ⟨hV₁, hvs, hkk⟩ := cont_split hV
    have hC : _ := Option.some.inj (Option.some.inj ((hkk ▸ hk').symm.trans hk))
    have hH : _ := Option.some.inj ((he ▸ hr').symm.trans hr)
    rw [hd, hV₁, hvs, hkk, hC, hH]
    rfl
  | resumeNull =>
    have h1 := last_eq ((show [] ++ [FVal.cont k] = [FVal.cont k] from rfl).trans
      (hV.trans (List.append_assoc _ _ _).symm))
    cases h1
  | resumeUsed hk' =>
    obtain ⟨-, -, hkk⟩ := cont_split hV
    exact absurd ((hkk ▸ hk').symm.trans hk) (by simp)
  | _ => cases he

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
