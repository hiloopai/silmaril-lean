module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.USame

/-!
# Backward simulation: `push`, `prim`, `drop` and `contNew`

The converses of `sim_push`, `sim_prim`, `sim_drop` and `sim_contNew`: from the encoded top
frame, the `StepFX'` steps of the encoding are the only steps, so the next related
configuration is inevitable (`u_push`, `u_prim`, `u_drop`, `u_contNew`). `prim_head` extracts
the Core head step of a `prim`'s instruction from `PrimOk`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (outer SX FS code_top step_nop step_dropVal
  step_dropCont step_prim run_contNew top_module opsF_cons opsF_append opsF_vals fvals_vals_map
  freshK step_seq)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval?)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head fnv fnv_vals_append fnv_cons_of_none)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} (S : Setup H) {W : Prog (Ins Val)}

theorem toSD (hS : SX S = SD o S.fx) {F : Frame} {a b : List (Option ContFX) × List AdminFX}
    (h : FS S F a b) : SD o S.fx ⟨S.s, a.1, F, a.2⟩ ⟨S.s, b.1, F, b.2⟩ := by
  have h' : SX S ⟨S.s, a.1, F, a.2⟩ ⟨S.s, b.1, F, b.2⟩ := h
  rwa [hS] at h'

/-- A Core step from `i32` operands and a plain instruction. -/
abbrev PrimStep (o : GrowKind → Nat → Nat → Nat → Bool) (s : Store H) (F : Frame)
    (L : List Val) (i : Instr) (R : List Val) : Prop :=
  Step (Profile.deterministic o) noHost ⟨s, F, vals L ++ [.plain i]⟩ ⟨s, F, vals R⟩

theorem prim_plain_none {s : Store H} {F : Frame} {L R : List Val} {i : Instr}
    (h : PrimStep o s F L i R) : (Admin.plain i).val? = none := by
  cases hiv : (Admin.plain i).val? with
  | none => rfl
  | some v =>
    have hv : Admin.plain i = v.toAdmin := Silmaril.Wasm.SingleThreaded.Det.val?_eq_some.mp hiv
    have h₀ : Step (Profile.deterministic o) noHost ⟨s, F, vals L ++ [.plain i]⟩ ⟨s, F, vals R⟩ := h
    have h' : Step (Profile.deterministic o) noHost ⟨s, F, vals (L ++ [v])⟩ ⟨s, F, vals R⟩ := by
      rw [hv] at h₀
      simpa [vals] using h₀
    exact (Silmaril.Wasm.SingleThreaded.Det.not_step_vals h').elim

theorem prim_not_bubble {s : Store H} {F : Frame} {L : List Val} {i : Instr} {c : Config H}
    (hL : ∀ x ∈ L, ∃ b, x = Val.i32 b) (hiv : (Admin.plain i).val? = none)
    (hb : Silmaril.Wasm.SingleThreaded.Det.Bubble s F (vals L ++ [.plain i]) c) : False := by
  obtain ⟨p, q, u, r, -, ⟨hf, -⟩ | ⟨a, hf, -⟩⟩ :=
    Silmaril.Wasm.SingleThreaded.Det.fnv_bubble hb <;>
    rw [fnv_vals_append, fnv_cons_of_none hiv] at hf <;>
    simp only [List.append_nil, Prod.mk.injEq, List.cons.injEq] at hf
  · injection hf.2.1
  · obtain ⟨b, hb⟩ := hL (Val.ref (.exn a)) (by rw [hf.1]; simp)
    cases hb

/-- The head step of a `prim`'s Core step. -/
theorem prim_headDec {s : Store H} {F : Frame} {L R : List Val} {i : Instr}
    (hL : ∀ x ∈ L, ∃ b, x = Val.i32 b) (h : PrimStep o s F L i R) :
    ∃ vs args c₀, L = vs ++ args ∧ Head (Profile.deterministic o) s F args (.plain i) c₀ ∧
      c₀.store = s ∧ c₀.frame = F ∧ vals vs ++ c₀.code = vals R ∧ i ≠ .throwRef := by
  have hiv : (Admin.plain i).val? = none := prim_plain_none h
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp h with hd | hb
  · obtain ⟨vs, args, e, rest, c₀, hcode, hh, hc'⟩ := hd
    have hg := Silmaril.Wasm.SingleThreaded.Det.Head.good hh
    have hcode' : vals L ++ Admin.plain i :: [] = vals (vs ++ args) ++ e :: rest := by
      simpa [vals] using hcode
    obtain ⟨hL', he, hr⟩ :=
      Silmaril.Wasm.SingleThreaded.Det.vals_append_cons_inj hcode' hiv hg.val_none
    have hc'' : s = c₀.store ∧ F = c₀.frame ∧ vals R = vals vs ++ c₀.code ++ rest := by
      simpa using hc'
    refine ⟨vs, args, c₀, hL', he ▸ hh, hc''.1.symm, hc''.2.1.symm, by simpa [← hr] using hc''.2.2.symm, ?_⟩
    rintro rfl
    have ha : args = [.ref .null] := hg.throwRef he.symm
    obtain ⟨b, hb⟩ := hL (Val.ref .null) (by rw [hL', ha]; simp)
    cases hb
  · exact (prim_not_bubble hL hiv hb).elim

/-- The Core head step of a `prim`'s instruction. -/
theorem prim_head (hP : S.P = Profile.deterministic o) (hH : S.host = noHost) {n : Nat}
    {op : List Val → List Val} {i : Instr} (hi : PrimOk S n op i) {F : Frame}
    (hF : F.module = S.M) {bs : List (BitVec 32)} (hbs : bs.length = n) :
    ∃ vs args c₀, (bs.map Val.i32).reverse = vs ++ args ∧
      Head (Profile.deterministic o) S.s F args (.plain i) c₀ ∧ c₀.store = S.s ∧
      c₀.frame = F ∧ vals vs ++ c₀.code = vals (op (bs.map Val.i32)).reverse ∧
      i ≠ .throwRef := by
  have h : PrimStep o S.s F (bs.map Val.i32).reverse i (op (bs.map Val.i32)).reverse := by
    have h₀ := hi bs F hbs hF
    rwa [hP, hH, Silmaril.Proofs.Wasm.Models.FXLower.blockFX_noHost] at h₀
  have hnum : ∀ x ∈ (bs.map Val.i32).reverse, ∃ b, x = Val.i32 b := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    exact ⟨b, rfl⟩
  exact prim_headDec hnum h

variable {KK : List (Option (List (SFrame Val)))} {K : List (Option ContFX)} {fr : SFrame Val}
  {a : Ann} {rs : List (SFrame Val × Ann)}

/-- `push v`. -/
theorem u_push (hS : SX S = SD o S.fx) (hmain : MainOk S W ((fr, a) :: rs))
    (hK : List.Forall₂ (KRel S W) KK K) {v : Val} {i : Instr} {c : List (Ins Val)}
    {Y : List InstrFX} (hY : a.code = .core i :: .core .nop :: Y)
    (hv : Admin.plain i = v.toAdmin) (henc : EncI S W c Y) :
    InevP (SX S) TermFX
      (Rel S W ⟨KK, { fr with code := c, ops := .val v :: fr.ops } :: rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  refine usame S (p' := ({ fr with code := c, ops := .val v :: fr.ops }, { a with code := Y }))
    hS hmain ⟨henc, hfr.2⟩ rfl hK (.one ?_)
  let F := (outer S rs a.kind).frameAt S.f0
  have e₁ : fvals (opsF fr.ops) ++ adm a.code =
      fvals ((opsF fr.ops ++ [.val v]) ++ liftV []) ++ .core (.plain .nop) :: adm Y := by
    simp [hY, adm, InstrFX.toAdmin, hv, FVal.toAdmin, liftV]
  have e₂ : fvals (opsF (.val v :: fr.ops)) ++ adm Y =
      fvals (opsF fr.ops ++ [.val v]) ++ ([] : List Admin).map .core ++ adm Y := by
    simp [opsF_cons, toF]
  show LU o S.fx S.s F (K, fvals (opsF fr.ops) ++ adm a.code)
    (K, fvals (opsF (.val v :: fr.ops)) ++ adm Y)
  rw [e₁, e₂]
  refine lu_core (c₀ := ⟨S.s, F, []⟩) (.parametric .nop) (fun h => by cases h) rfl rfl ?_
  have h := toSD S hS (step_nop S (K := K) (F := F) (opsF fr.ops ++ [.val v]) (adm Y))
  simpa [liftV] using h

/-- `drop`. -/
theorem u_drop (hS : SX S = SD o S.fx) (hmain : MainOk S W ((fr, a) :: rs))
    (hK : List.Forall₂ (KRel S W) KK K) {x : SV Val} {o' : List (SV Val)} {c : List (Ins Val)}
    {Y : List InstrFX} (hops : fr.ops = x :: o') (hY : a.code = .core .drop :: Y)
    (henc : EncI S W c Y) :
    InevP (SX S) TermFX
      (Rel S W ⟨KK, { fr with code := c, ops := o' } :: rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  refine usame S (p' := ({ fr with code := c, ops := o' }, { a with code := Y }))
    hS hmain ⟨henc, hfr.2⟩ rfl hK (.one ?_)
  let F := (outer S rs a.kind).frameAt S.f0
  show LU o S.fx S.s F (K, fvals (opsF fr.ops) ++ adm a.code) (K, fvals (opsF o') ++ adm Y)
  match x with
  | .val v =>
    have e₁ : fvals (opsF fr.ops) ++ adm a.code =
        fvals (opsF o' ++ liftV [v]) ++ .core (.plain .drop) :: adm Y := by
      simp [hops, hY, adm, InstrFX.toAdmin, opsF_cons, toF, liftV]
    have e₂ : fvals (opsF o') ++ adm Y = fvals (opsF o') ++ ([] : List Admin).map .core ++ adm Y :=
      by simp
    rw [e₁, e₂]
    refine lu_core (c₀ := ⟨S.s, F, []⟩) (.parametric (.drop v)) (fun h => by cases h) rfl rfl ?_
    have h := toSD S hS (step_dropVal S (K := K) (F := F) (opsF o') (adm Y) v)
    simpa [liftV] using h
  | .cont k =>
    have e₁ : fvals (opsF fr.ops) ++ adm a.code =
        fvals (opsF o' ++ [.cont k]) ++ .core (.plain .drop) :: adm Y := by
      simp [hops, hY, adm, InstrFX.toAdmin, opsF_cons, toF]
    rw [e₁]
    refine ⟨toSD S hS (step_dropCont S (K := K) (F := F) (opsF o') (adm Y) k),
      fun d hd => uniq_dropCont hd, quiet_of rfl rfl trivial id trivial⟩

/-- `prim n op` on `i32` operands. -/
theorem u_prim (hS : SX S = SD o S.fx) (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (hok : Ok S W) (hmain : MainOk S W ((fr, a) :: rs))
    (hK : List.Forall₂ (KRel S W) KK K) {n : Nat} {op : List Val → List Val} {i : Instr}
    {c : List (Ins Val)} {Y : List InstrFX} {bs : List (BitVec 32)} {o' : List (SV Val)}
    (hops : fr.ops = (bs.map Val.i32).map .val ++ o') (hn : bs.length = n)
    (hY : a.code = .core i :: Y) (hi : PrimOk S n op i) (henc : EncI S W c Y) :
    InevP (SX S) TermFX
      (Rel S W ⟨KK, { fr with code := c, ops := (op (bs.map Val.i32)).map .val ++ o' } ::
        rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  refine usame S (p' := ({ fr with code := c, ops := (op (bs.map Val.i32)).map .val ++ o' },
    { a with code := Y })) hS hmain ⟨henc, hfr.2⟩ rfl hK (.one ?_)
  let F := (outer S rs a.kind).frameAt S.f0
  have hF : F.module = S.M := top_module S hok hmain
  obtain ⟨vs, args, c₀, hL, hh, hst, hfr₀, hres, hthr⟩ := prim_head S hP hH hi hF hn
  have hpre : fvals ((opsF o' ++ liftV vs) ++ liftV args) =
      fvals (opsF o') ++ fvals ((bs.map Val.i32).reverse.map .val) := by
    rw [hL]
    simp [liftV]
  have e₁ : fvals (opsF fr.ops) ++ adm a.code =
      fvals ((opsF o' ++ liftV vs) ++ liftV args) ++ .core (.plain i) :: adm Y := by
    rw [hpre, hops, opsF_append, opsF_vals, hY]
    simp [adm, InstrFX.toAdmin]
  have h3 : fvals (liftV vs) ++ c₀.code.map .core =
      fvals ((op (bs.map Val.i32)).reverse.map .val) := by
    rw [liftV_fvals, cvals, ← List.map_append, hres, fvals_vals_map]
  have e₂ : fvals (opsF ((op (bs.map Val.i32)).map .val ++ o')) ++ adm Y =
      fvals (opsF o' ++ liftV vs) ++ c₀.code.map .core ++ adm Y := by
    rw [opsF_append, opsF_vals]
    simp only [Silmaril.Proofs.Wasm.Models.FXVRuns.fvals_append, List.append_assoc, ← h3]
  show LU o S.fx S.s F (K, fvals (opsF fr.ops) ++ adm a.code)
    (K, fvals (opsF ((op (bs.map Val.i32)).map .val ++ o')) ++ adm Y)
  rw [e₁, e₂]
  refine lu_core hh hthr hst hfr₀ ?_
  have h := toSD S hS (step_prim S (K := K) (F := F) hi hF bs hn (opsF o') (adm Y))
  have q₂ : fvals (opsF o' ++ liftV vs) ++ c₀.code.map .core ++ adm Y =
      fvals (opsF o') ++ fvals ((op (bs.map Val.i32)).reverse.map .val) ++ adm Y := by
    simp only [Silmaril.Proofs.Wasm.Models.FXVRuns.fvals_append, List.append_assoc, ← h3]
  rw [hpre, q₂]
  simpa only [List.append_assoc] using h

/-- `contNew f`: `ref.func`, then `cont.new`. -/
theorem u_contNew (hS : SX S = SD o S.fx) (hok : Ok S W) (hmain : MainOk S W ((fr, a) :: rs))
    (hK : List.Forall₂ (KRel S W) KK K) {f : Nat} {bf : List (Ins Val)} {c : List (Ins Val)}
    {Y : List InstrFX} (hY : a.code = .core (.refFunc (S.xf f)) :: .fx (.contNew S.ct) :: Y)
    (hf : W f = some (0, bf)) (henc : EncI S W c Y) :
    InevP (SX S) TermFX
      (Rel S W ⟨KK ++ [some [⟨bf, [], none⟩]],
        { fr with code := c, ops := .cont KK.length :: fr.ops } :: rs.map Prod.fst⟩)
      ⟨S.s, K, S.f0, (stkCtx S ((fr, a) :: rs)).plug []⟩ := by
  have hfr : FrOk S W (fr, a) := hmain.1 _ (List.mem_cons_self ..)
  obtain ⟨-, fi, h, Yb, hx, hfi, -, -, -⟩ := hok.funcs f 0 bf hf
  have hlen : KK.length = K.length := hK.length_eq
  have hK' : List.Forall₂ (KRel S W) (KK ++ [some [⟨bf, [], none⟩]])
      (K ++ [some (freshK (S.fa f) fi)]) :=
    List.rel_append hK (.cons (Or.inl ⟨f, bf, fi, hf, hfi, rfl, rfl⟩) .nil)
  refine usame S (p' := ({ fr with code := c, ops := .cont KK.length :: fr.ops },
    { a with code := Y })) hS hmain ⟨henc, hfr.2⟩ rfl hK' ?_
  let F := (outer S rs a.kind).frameAt S.f0
  have hF : F.module = S.M := top_module S hok hmain
  have hx' : F.module.funcs[(S.xf f).toNat]? = some (S.fa f) := by rw [hF]; exact hx
  have e₀ : fvals (opsF fr.ops) ++ adm a.code = fvals (opsF fr.ops ++ liftV []) ++
      .core (.plain (.refFunc (S.xf f))) :: .fx (.contNew S.ct) :: adm Y := by
    simp [hY, adm, InstrFX.toAdmin, liftV]
  have e₁ : fvals (opsF fr.ops) ++ [Admin.ref (.func (S.fa f))].map .core ++
      (.fx (.contNew S.ct) :: adm Y) =
      fvals (opsF fr.ops ++ [.val (.ref (.func (S.fa f)))]) ++ .fx (.contNew S.ct) :: adm Y := by
    simp [FVal.toAdmin, Val.toAdmin]
  have e₂ : fvals (opsF (.cont KK.length :: fr.ops)) ++ adm Y =
      fvals (opsF fr.ops) ++ [.contRef K.length] ++ adm Y := by
    simp [opsF_cons, toF, hlen, FVal.toAdmin]
  show LPath o S.fx S.s F (K, fvals (opsF fr.ops) ++ adm a.code)
    (K ++ [some (freshK (S.fa f) fi)], fvals (opsF (.cont KK.length :: fr.ops)) ++ adm Y)
  rw [e₀, e₂]
  have hstep₁ : Step (Profile.deterministic o) (blockFX noHost S.fx)
      ⟨S.s, F, [.plain (.refFunc (S.xf f))]⟩ ⟨S.s, F, [.ref (.func (S.fa f))]⟩ :=
    .reference (.refFunc hx')
  have hst₁ := step_seq (opsF fr.ops) (.fx (.contNew S.ct) :: adm Y)
    (StepFX'.core (K := K) hstep₁)
  have l₁ : LU o S.fx S.s F (K, fvals (opsF fr.ops ++ liftV []) ++
        .core (.plain (.refFunc (S.xf f))) :: .fx (.contNew S.ct) :: adm Y)
      (K, fvals (opsF fr.ops) ++ [Admin.ref (.func (S.fa f))].map .core ++
        (.fx (.contNew S.ct) :: adm Y)) :=
    lu_core (c₀ := ⟨S.s, F, [.ref (.func (S.fa f))]⟩) (.reference (.refFunc hx'))
      (fun h => by cases h) rfl rfl (by simpa [liftV] using hst₁)
  rw [e₁] at l₁
  refine .cons l₁ (.one ⟨?_, fun d hd => ?_, quiet_of rfl rfl trivial id trivial⟩)
  · have h2 := step_seq (opsF fr.ops) (adm Y)
      (StepFX'.contNew (P := Profile.deterministic o) (host := noHost) (fx := S.fx) (K := K)
        (f := F) (ct := S.ct) hfi)
    simpa [freshK, FVal.toAdmin, Val.toAdmin] using h2
  · rw [uniq_contNew hfi hd]
    rfl

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
