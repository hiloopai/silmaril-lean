module

public import Silmaril.Proofs.Wasm.Game.Linking.Split.Rel4
public import Silmaril.Proofs.Wasm.Game.Linking.Setup

/-!
# Static linking, separation: the joint invariant

Original module documentation:

# The joint machine of the split world (M3 step B, #1977)

Game semantics of WebAssembly modules (tracking issue #1982), milestone M3, step (B).

The split world runs the consumer with stubs (store `κ`) and the provider (store `π`) as two
threads; the shared world runs both in one store `σ`. This file relates their configurations:

* `Static S`: the facts about the initial stores that the separation needs (ownership,
  disjointness, the stub functions, ownership of the export addresses);
* `World`: the three stores are related (`Rel4`) and their functions are the initial ones;
* `CRel σ ts π κ tc`: the consumer runs, the shared thread `ts` is the renamed consumer thread;
* `PRel σ ts π tp κ tc h args`: the consumer is stopped at the callout `h args`, the provider
  thread `tp` runs at top level, and the shared thread is the consumer's callout context filled
  with the renamed provider code.

Forward simulation, one host-free step at a time: `CRel.step` (consumer), `PRel.step`
(provider), `CRel.call` (a callout of the consumer starts the provider: one `call_ref` step of
the shared world, the first step of the provider's `$invoke`), `PRel.ret` (the provider's
result resumes the consumer), `CRel.result` (the consumer's result is the shared result), and
`Idle.start` (an export call).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

set_option linter.unusedSimpArgs false

namespace Silmaril.Proofs.Wasm.Game.Linking.Split

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.GamesAux Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Proofs.Wasm.Game.Linking

/-- The identity renaming. -/
def Ren.id : Ren := ⟨fun a => a, fun a => a⟩

/-! ### Scalar values are not renamed -/

theorem hasVal_ren {t : ScalarType} {v : Val} (h : t.HasVal v) (ρ : Ren) :
    ρ.val v = v := by
  cases t with
  | num t => obtain ⟨b, rfl⟩ := h; rfl
  | v128 => obtain ⟨b, rfl⟩ := h; rfl
  | i31 n => rcases h with ⟨b, rfl⟩ | ⟨-, rfl⟩ <;> rfl

theorem hasVal_good {t : ScalarType} {v : Val} (h : t.HasVal v) (O : Own) :
    O.GoodVal v := by
  cases t with
  | num t => obtain ⟨b, rfl⟩ := h; trivial
  | v128 => obtain ⟨b, rfl⟩ := h; trivial
  | i31 n => rcases h with ⟨b, rfl⟩ | ⟨-, rfl⟩ <;> trivial

theorem forall₂_hasVal_ren {ts : List ScalarType} {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal ts vs) (ρ : Ren) : vs.map ρ.val = vs := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [hasVal_ren h ρ, ih]

theorem forall₂_hasVal_good {ts : List ScalarType} {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal ts vs) (O : Own) : ∀ v ∈ vs, O.GoodVal v := by
  induction h with
  | nil => simp
  | cons h _ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hasVal_good h O
    · exact ih v hv

/-- A renamed reference typed `(ref null? i31)` was not renamed. -/
theorem ref_eq_of_hasVal_i31 {n : Bool} {r : Ref} {ρ : Ren}
    (hv : (ScalarType.i31 n).HasVal (.ref (ρ.ref r))) : ρ.ref r = r := by
  rcases hv with ⟨b, hb⟩ | ⟨-, hb⟩ <;> cases r <;> simp_all [Ren.ref]

/-- A renamed value list is scalar-typed only if it was not renamed. -/
theorem forall₂_hasVal_of_ren {ts : List ScalarType} {vs : List Val} {ρ : Ren}
    (h : List.Forall₂ ScalarType.HasVal ts (vs.map ρ.val)) : vs.map ρ.val = vs := by
  induction vs generalizing ts with
  | nil => rfl
  | cons v vs ih =>
    cases h with
    | cons hv hvs =>
      rw [List.map_cons, ih hvs]
      congr 1
      rename_i t _
      cases v with
      | ref r =>
        cases t with
        | num _ => obtain ⟨b, hb⟩ := hv; cases hb
        | v128 => obtain ⟨b, hb⟩ := hv; cases hb
        | i31 n =>
          show Val.ref (ρ.ref r) = Val.ref r
          rw [ref_eq_of_hasVal_i31 hv]
      | num => rfl
      | vec => rfl

variable (S : Setup)

/-- The facts about the initial stores that the separation needs. -/
structure Static where
  /-- What the provider owns. -/
  Op : Own
  /-- What the consumer owns. -/
  Oc : Own
  /-- The initial stores are related by the identity renamings. -/
  rel : Rel4 Op Oc Ren.id Op Ren.id Oc S.sc S.sp S.scs
  /-- Host functions of the consumer world are the stubs, owned by the provider. -/
  stub : ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), S.scs.funcs[a]? = some fi → fi.code = .host h →
    ∃ hlt : h < S.stubTypes.length, S.providerI.addr ⟨h, hlt⟩ = a ∧ Op.fn a
  /-- The provider world has no host function. -/
  pwasm : ∀ (a : Nat) (fi : FuncInst Nat), S.sp.funcs[a]? = some fi → ∃ c, fi.code = .wasm c
  /-- The export addresses are owned by the consumer. -/
  exports : ∀ j, Oc.fn (S.consumerI.addr j)

variable {S}

/-- The three stores are related, and their functions are the initial ones. -/
structure World (St : Static S) (σ π κ : Store Nat) (ρp : Ren) (Op : Own) (ρc : Ren) (Oc : Own) :
    Prop where
  rel : Rel4 St.Op St.Oc ρp Op ρc Oc σ π κ
  fσ : σ.funcs = S.sc.funcs
  fπ : π.funcs = S.sp.funcs
  fκ : κ.funcs = S.scs.funcs

/-- No export call is active. -/
def Idle (St : Static S) (σ π κ : Store Nat) : Prop :=
  ∃ ρp Op ρc Oc, World St σ π κ ρp Op ρc Oc

/-- The consumer runs; the shared thread is the renamed consumer thread. -/
def CRel (St : Static S) (σ : Store Nat) (ts : Thread) (π κ : Store Nat) (tc : Thread) : Prop :=
  ∃ ρp Op ρc Oc, World St σ π κ ρp Op ρc Oc ∧ Oc.FrameGood (tc.config κ).frame ∧
    Oc.CodeGood (tc.config κ).code ∧
    ts.config σ = ⟨σ, ρc.frame (tc.config κ).frame, ρc.code (tc.config κ).code⟩

/-- The consumer waits at the callout `h args`; the provider thread runs at top level inside
the callout context in the shared world. -/
def PRel (St : Static S) (σ : Store Nat) (ts : Thread) (π : Store Nat) (tp : Thread)
    (κ : Store Nat) (tc : Thread) (h : Nat) (args : List Val) : Prop :=
  ∃ ρp Op ρc Oc E a, World St σ π κ ρp Op ρc Oc ∧ Oc.FrameGood (tc.config κ).frame ∧
    Oc.CodeGood (tc.config κ).code ∧
    decompose? κ (tc.config κ).code = some (E, a, h, args) ∧
    (tp.config π).frame = {} ∧ TopOK (tp.config π).code ∧ Op.CodeGood (tp.config π).code ∧
    ts.config σ = ⟨σ, ρc.frame (tc.config κ).frame, (ρc.ctx E).fill (ρp.code (tp.config π).code)⟩

/-! ### The initial world -/

theorem Static.idle (St : Static S) : Idle St S.sc S.sp S.scs :=
  ⟨_, _, _, _, ⟨St.rel, rfl, rfl, rfl⟩⟩

/-! ### Consumer steps -/

theorem internal_config {P : Profile} {s s' : Store Nat} {t t' : Thread}
    (h : InternalP P (s, t) (s', t')) :
    ∃ f' c', t' = .active f' c' ∧
      Step P noHost ⟨s, (t.config s).frame, (t.config s).code⟩ ⟨s', f', c'⟩ := by
  obtain ⟨f', c', rfl, hst⟩ := h
  refine ⟨f', c', rfl, ?_⟩
  rw [← Thread.config_eta]
  exact hst

theorem internal_of_step {P : Profile} {s s' : Store Nat} {t : Thread} {F : Frame}
    {X : List Admin} {f' : Frame} {c' : List Admin} (ht : t.config s = ⟨s, F, X⟩)
    (h : Step P noHost ⟨s, F, X⟩ ⟨s', f', c'⟩) :
    InternalP P (s, t) (s', .active f' c') :=
  ⟨f', c', rfl, by rw [ht]; exact h⟩

/-- One consumer step is one shared step. -/
theorem CRel.step {St : Static S} {P : Profile} {σ π κ κ' : Store Nat} {ts tc tc' : Thread}
    (hR : CRel St σ ts π κ tc) (h : InternalP P (κ, tc) (κ', tc')) :
    ∃ σ' ts', InternalP P (σ, ts) (σ', ts') ∧ CRel St σ' ts' π κ' tc' := by
  obtain ⟨ρp, Op, ρc, Oc, hW, hf, hc, hts⟩ := hR
  have hfun := InternalP.funcs_prefix h
  obtain ⟨f', c', rfl, hst⟩ := internal_config h
  obtain ⟨ρc', Oc', σ', hst', hR', hf', hc', -, -, -⟩ := hW.rel.consumer_step hf hc hst
  have hi := internal_of_step hts hst'
  refine ⟨σ', _, hi, ρp, Op, ρc', Oc', ⟨hR', ?_, hW.fπ, ?_⟩, hf', hc', rfl⟩
  · rw [InternalP.funcs_prefix hi, hW.fσ]
  · rw [hfun, hW.fκ]

theorem CRel.reach {St : Static S} {P : Profile} {σ π κ κ' : Store Nat} {ts tc tc' : Thread}
    (hR : CRel St σ ts π κ tc) (h : Reach P (κ, tc) (κ', tc')) :
    ∃ σ' ts', Reach P (σ, ts) (σ', ts') ∧ CRel St σ' ts' π κ' tc' := by
  generalize hx : (κ, tc) = x at h
  generalize hy : (κ', tc') = y at h
  induction h generalizing κ' tc' with
  | refl => subst hx; cases hy; exact ⟨σ, ts, .refl, hR⟩
  | @tail y₁ y₂ _ hst ih =>
    subst hy
    obtain ⟨σ₁, ts₁, h₁, hR₁⟩ := ih (κ' := y₁.1) (tc' := y₁.2) rfl
    obtain ⟨σ₂, ts₂, h₂, hR₂⟩ := hR₁.step hst
    exact ⟨σ₂, ts₂, h₁.tail h₂, hR₂⟩

/-! ### Provider steps -/

/-- One provider step is one shared step. -/
theorem PRel.step {St : Static S} {P : Profile} {σ π π' κ : Store Nat} {ts tp tp' tc : Thread}
    {h : Nat} {args : List Val} (hR : PRel St σ ts π tp κ tc h args)
    (hs : InternalP P (π, tp) (π', tp')) :
    ∃ σ' ts', InternalP P (σ, ts) (σ', ts') ∧ PRel St σ' ts' π' tp' κ tc h args := by
  obtain ⟨ρp, Op, ρc, Oc, E, a, hW, hf, hc, hd, hF, htop, hcp, hts⟩ := hR
  have hfun := InternalP.funcs_prefix hs
  obtain ⟨f', c', rfl, hst⟩ := internal_config hs
  rw [hF] at hst
  obtain ⟨ρp', Op', σ', hst', hF', htop', hR', hcp', -, -, -⟩ :=
    provider_step_fill hW.rel hcp htop hst (ρc.ctx E) (ρc.frame (tc.config κ).frame)
  subst hF'
  have hi := internal_of_step hts hst'
  refine ⟨σ', _, hi, ρp', Op', ρc, Oc, E, a, ⟨hR', ?_, ?_, hW.fκ⟩, hf, hc, hd, rfl, htop', hcp',
    rfl⟩
  · rw [InternalP.funcs_prefix hi, hW.fσ]
  · rw [hfun, hW.fπ]

theorem PRel.reach {St : Static S} {P : Profile} {σ π π' κ : Store Nat} {ts tp tp' tc : Thread}
    {h : Nat} {args : List Val} (hR : PRel St σ ts π tp κ tc h args)
    (hs : Reach P (π, tp) (π', tp')) :
    ∃ σ' ts', Reach P (σ, ts) (σ', ts') ∧ PRel St σ' ts' π' tp' κ tc h args := by
  generalize hx : (π, tp) = x at hs
  generalize hy : (π', tp') = y at hs
  induction hs generalizing π' tp' with
  | refl => subst hx; cases hy; exact ⟨σ, ts, .refl, hR⟩
  | @tail y₁ y₂ _ hst ih =>
    subst hy
    obtain ⟨σ₁, ts₁, h₁, hR₁⟩ := ih (π' := y₁.1) (tp' := y₁.2) rfl
    obtain ⟨σ₂, ts₂, h₂, hR₂⟩ := hR₁.step hst
    exact ⟨σ₂, ts₂, h₁.tail h₂, hR₂⟩

/-! ### Switching between consumer and provider -/

/-- The code in the hole of a good callout context is good. -/
theorem Own.CodeGood.of_fill {O : Own} (E : Ctx) {xs : List Admin} (h : O.CodeGood (E.fill xs)) :
    O.CodeGood xs := by
  induction E with
  | top pre rest =>
    simp only [Ctx.fill] at h
    exact (O.codeGood_append.mp (O.codeGood_append.mp h).1).2
  | label pre n cont E rest ih =>
    simp only [Ctx.fill] at h
    exact ih ((O.codeGood_single_label ..).mp (O.codeGood_append.mp (O.codeGood_append.mp h).1).2)
  | handler pre n cs E rest ih =>
    simp only [Ctx.fill] at h
    exact ih ((O.codeGood_single_handler ..).mp
      (O.codeGood_append.mp (O.codeGood_append.mp h).1).2)
  | frame pre n f E rest ih =>
    simp only [Ctx.fill] at h
    exact ih ((O.codeGood_single_frame ..).mp
      (O.codeGood_append.mp (O.codeGood_append.mp h).1).2).2

theorem Own.codeGood_scalars {O : Own} {ts : List ScalarType} {vs : List Val}
    (h : List.Forall₂ ScalarType.HasVal ts vs) : O.CodeGood (vals vs) :=
  O.codeGood_vals.mpr (forall₂_hasVal_good h O)

/-- A single frame is not the code of a result. -/
private theorem frame_ne_toAdmin (n : Nat) (f : Frame) (b : List Admin) (r : Result) :
    [Admin.frame n f b] ≠ r.toAdmin := by
  intro hr
  cases r with
  | values vs =>
    rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩
    · simp [Result.toAdmin] at hr
    · rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Result.toAdmin, Val.toAdmin] at hr
    · simp [Result.toAdmin] at hr
  | trap => simp [Result.toAdmin] at hr
  | throw a => simp [Result.toAdmin] at hr

/-- **Call.** At a callout of the consumer, the provider's `$invoke` of the stub takes its
first step (`call_ref` into the provider function), and so does the shared world. -/
theorem CRel.call {St : Static S} {P : Profile} {σ π κ : Store Nat} {ts tc : Thread}
    {h : Nat} {args : List Val} {pts : List ScalarType}
    (hR : CRel St σ ts π κ tc) (hco : CalloutAt κ tc h args)
    (hargs : List.Forall₂ ScalarType.HasVal pts args) :
    ∃ (hlt : h < S.stubTypes.length) (tp ts' : Thread),
      InternalP P (π, .pending (S.providerI.addr ⟨h, hlt⟩) args) (π, tp) ∧
      InternalP P (σ, ts) (σ, ts') ∧ PRel St σ ts' π tp κ tc h args ∧
      ∀ r, ¬ ResultAt π tp r := by
  obtain ⟨ρp, Op, ρc, Oc, hW, hf, hc, hts⟩ := hR
  obtain ⟨E, a, hd⟩ := hco
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, he, hn, hX⟩ := decompose?_sound hd
  obtain ⟨hlt, haddr, hOp⟩ := St.stub a fi h (by rw [← hW.fκ]; exact hfi) hcode
  have hOp' : Op.fn a := by rw [hW.rel.fnp]; exact hOp
  obtain ⟨fp, hfp, fs, hfs, htyps, hwasm⟩ := hW.rel.rp.fn a hOp'
  obtain ⟨c, hc'⟩ := St.pwasm a fp (by rw [← hW.fπ]; exact hfp)
  obtain ⟨hfsp, hm⟩ := hwasm c hc'
  have hfsσ : σ.funcs[a]? = some fp := hfsp ▸ hfs
  have hOc : Oc.fn a := by
    have h1 : Oc.CodeGood (vals args ++ [.ref (.func a), yy]) := Own.CodeGood.of_fill E (hX ▸ hc)
    have h2 : Oc.CodeGood [.ref (.func a), yy] := (Oc.codeGood_append.mp h1).2
    exact h2.head_ref
  obtain ⟨fk, hfk, fs', hfs', htyk, -⟩ := hW.rel.rc.fn a hOc
  have hfki : fk = fi := Option.some.inj (hfk.symm.trans hfi)
  have hfs'p : fs' = fp := Option.some.inj (hfs'.symm.trans hfsσ)
  have he' : Expand fp.type (.func ps rs) := by rw [← hfs'p, htyk, hfki]; exact he
  -- the provider's first step
  let Y : List Admin := [.frame rs.length (Frame.forCall fp.module args c.locals)
    [.label rs.length [] (expression c.body)]]
  have hstp : Step P noHost (invoke π a args) ⟨π, {}, Y⟩ :=
    Step.callRefFunc (c := .callRefType ((π.funcs[a]?.map FuncInst.type).getD default))
      trivial hfp he' hn hc'
  -- the shared step
  have hcode' : (ts.config σ).code = (ρc.ctx E).fill (vals args ++ [.ref (.func a), yy]) := by
    rw [hts]
    simp only
    rw [hX, Ren.code_fill]
    simp [Ren.code_callRef ρc hyy, forall₂_hasVal_ren hargs]
  have hstep : Step P noHost
      ⟨σ, (ts.config σ).frame, (ts.config σ).code⟩
      ⟨σ, (ts.config σ).frame, (ρc.ctx E).fill Y⟩ := by
    rw [hcode']
    exact (ρc.ctx E).step_fill (fun g => Step.callRefFunc (P := P)
      (host := noHost) (s := σ) (f := g) hyy hfsσ he' hn hc') (ts.config σ).frame
  have heta : ts.config σ = ⟨σ, (ts.config σ).frame, (ts.config σ).code⟩ := by
    rw [Thread.config_eta σ ts]
  refine ⟨hlt, .active {} Y, .active (ts.config σ).frame ((ρc.ctx E).fill Y), ?_,
    internal_of_step heta hstep, ?_, ?_⟩
  · rw [haddr]; exact ⟨{}, Y, rfl, hstp⟩
  · show PRel St σ (.active (ts.config σ).frame ((ρc.ctx E).fill Y)) π (.active {} Y) κ tc h args
    refine ⟨ρp, Op, ρc, Oc, E, a, hW, hf, hc, hd, rfl, ?_, ?_, ?_⟩
    · show TopOK Y
      simp [Y, TopOK, TopAdmin]
    · show Op.CodeGood Y
      exact (Op.codeGood_single_frame ..).mpr ⟨Own.frameGood_forCall hm
        (forall₂_hasVal_good hargs Op) _, (Op.codeGood_single_label ..).mpr
          (Op.codeGood_expression _)⟩
    · show (⟨σ, (ts.config σ).frame, (ρc.ctx E).fill Y⟩ : Config Nat) =
        ⟨σ, ρc.frame (tc.config κ).frame, (ρc.ctx E).fill (ρp.code Y)⟩
      rw [hts]
      simp [Y, Ren.frame_forCall, forall₂_hasVal_ren hargs]
  · intro r hr
    exact frame_ne_toAdmin _ _ _ r hr

/-- **Return.** A result of the provider resumes the consumer; the shared world is already
there. The provider never throws: its code holds no exception reference. -/
theorem PRel.ret {St : Static S} {σ π κ : Store Nat} {ts tp tc : Thread} {h : Nat}
    {args : List Val} {r : Result} (hR : PRel St σ ts π tp κ tc h args) (hres : ResultAt π tp r)
    (hsc : ∀ vs, r = .values vs → ∃ rts, List.Forall₂ ScalarType.HasVal rts vs) :
    (∀ a, r ≠ .throw a) ∧ CRel St σ ts π κ (resumeResult κ tc r) := by
  obtain ⟨ρp, Op, ρc, Oc, E, a, hW, hf, hc, hd, hF, htop, hcp, hts⟩ := hR
  have hres' : (tp.config π).code = r.toAdmin := hres
  have hnt : ∀ a, r ≠ .throw a := by
    intro b hb
    have hcp' : Op.CodeGood (Result.throw b).toAdmin := by rw [← hb, ← hres']; exact hcp
    exact Own.not_codeGood_throwing (a := b) hcp' (by simp [Result.toAdmin])
  refine ⟨hnt, ρp, Op, ρc, Oc, hW, ?_, ?_, ?_⟩
  · rw [resumeResult_config hd]; exact hf
  · show Oc.CodeGood ((resumeResult κ tc r).config κ).code
    rw [resumeResult_config hd]
    obtain ⟨-, yy, -, -, -, -, -, -, -, hX⟩ := decompose?_sound hd
    refine Own.CodeGood.fill E (xs := vals args ++ [.ref (.func a), yy]) ?_ ?_
    · rw [← hX]; exact hc
    · cases r with
      | values vs =>
        obtain ⟨rts, hv⟩ := hsc vs rfl
        exact Own.codeGood_scalars hv
      | trap => simp [Result.toAdmin]
      | throw b => exact absurd rfl (hnt b)
  · rw [resumeResult_config hd, hts, hres', Ren.code_fill]
    congr 2
    cases r with
    | values vs =>
      obtain ⟨rts, hv⟩ := hsc vs rfl
      simp [Result.toAdmin, forall₂_hasVal_ren hv]
    | trap => simp [Result.toAdmin]
    | throw b => exact absurd rfl (hnt b)

/-- **Result.** A result of the consumer is (renamed) a result of the shared world, and the
stores are related again with no call active. -/
theorem CRel.result {St : Static S} {σ π κ : Store Nat} {ts tc : Thread} {r : Result}
    (hR : CRel St σ ts π κ tc) (hres : ResultAt κ tc r) :
    (∀ a, r ≠ .throw a) ∧ (∃ ρ : Ren, ResultAt σ ts (ρ.result r)) ∧ Idle St σ π κ := by
  obtain ⟨ρp, Op, ρc, Oc, hW, hf, hc, hts⟩ := hR
  unfold ResultAt at hres ⊢
  have hnt : ∀ a, r ≠ .throw a := by
    rintro b rfl
    rw [hres] at hc
    exact Own.not_codeGood_throwing (a := b) hc (by simp [Result.toAdmin])
  refine ⟨hnt, ⟨ρc, ?_⟩, ρp, Op, ρc, Oc, hW⟩
  rw [hts]
  simp only
  rw [hres, Ren.result_toAdmin ρc r hnt]

/-- **Start.** An export call starts related threads. -/
theorem Idle.start {St : Static S} {σ π κ : Store Nat} (hI : Idle St σ π κ)
    (f : S.consumerI.F.Op) :
    CRel St σ (S.sharedI.initThread f) π κ (S.consumerI.initThread f) := by
  obtain ⟨ρp, Op, ρc, Oc, hW⟩ := hI
  have hOc : Oc.fn (S.consumerI.addr f.1) := by rw [hW.rel.fnc]; exact St.exports f.1
  obtain ⟨fi, hfi, fi', hfi', hty, -⟩ := hW.rel.rc.fn _ hOc
  have hargs := f.2.2
  refine ⟨ρp, Op, ρc, Oc, hW, Oc.frameGood_empty, ?_, ?_⟩
  · simp only [ScalarInstance.initThread, Thread.config, invoke]
    exact Oc.codeGood_append.mpr ⟨Own.codeGood_scalars hargs,
      .cons_ref hOc (Oc.codeGood_single_callRefType _)⟩
  · simp only [ScalarInstance.initThread, Thread.config, invoke]
    have e : S.sharedI.addr f.1 = S.consumerI.addr f.1 := rfl
    rw [e, hfi, hfi']
    simp [forall₂_hasVal_ren hargs, hty]

end Silmaril.Proofs.Wasm.Game.Linking.Split
