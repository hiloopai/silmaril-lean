module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Adequacy

/-!
# Derived rules: instructions followed by code

The rules of `Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Total` take one instruction at the end of the
code; programs are read one instruction at a time with the code after it. These rules combine
each instruction rule with sequencing (`tsafe_cons`), for a postcondition `Q` with `Inv Q`:

* values and Core: `tsafe_nop`, `tsafe_refFunc`, `tsafe_i32Add`, `tsafe_call`;
* structured control: `tsafe_block_seq`, `tsafe_label_seq`, `tsafe_frame_seq`,
  `tsafe_handler_seq`;
* stack switching: `tsafe_contNew_seq`, `tsafe_resume_seq`, `tsafe_invoke_seq`,
  `tsafe_dropCont_seq`, and `tsafe_suspend_seq`: an unhandled `suspend` with the values `V`
  below it stops with every split `V = V₁ ++ vs`, the payload `vs` and the context `V₁ · rest`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts newCont)
open Silmaril.Wasm.FX.Logic.EveryRun (Unhandled suspCode switchCode Stops TSafe Inv seqPost
  labelPost framePost handlerPost totJ)
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval? fvals_append_cons_inj)
open Silmaril.Proofs.Wasm.Models.FXAsyncSus (canon)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (IsWrap)
open Silmaril.Wasm.SingleThreaded.Det (noHost Head)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {Q : PostFX H} {s : Store H}
  {K : Conts} {f : Frame}

/-- **One instruction, then code.** -/
theorem tsafe_cons (hQ : Inv Q) {V : List FVal} {a : AdminFX} {rest : List AdminFX}
    (h : TSafe P fx (seqPost (totJ P fx Q) rest Q) ⟨s, K, f, fvals V ++ [a]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ a :: rest⟩ := by
  simpa using tsafe_seq' (c₂ := rest) hQ h

/-- Values, then code: continue with the code. -/
theorem tsafe_vals_seq {V : List FVal} {rest : List AdminFX}
    (h : TSafe P fx Q ⟨s, K, f, fvals V ++ rest⟩) :
    TSafe P fx (seqPost (totJ P fx Q) rest Q) ⟨s, K, f, fvals V⟩ :=
  tsafe_vals h

theorem inert_nop : Silmaril.Wasm.Logic.Hoare.Inert .nop := ⟨rfl, by simp, rfl⟩

theorem tsafe_nop (hQ : Inv Q) {V : List FVal} {rest : List AdminFX}
    (h : TSafe P fx Q ⟨s, K, f, fvals V ++ rest⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ .core (.plain .nop) :: rest⟩ := by
  refine tsafe_cons hQ (tsafe_inert inert_nop (by simp) (by simp) (by simp) ?_)
  intro V₁ args c₀ hV hh
  obtain ⟨rfl, rfl⟩ := head_nop hh
  have hV' : V = V₁ := by simpa [liftV] using hV
  show TSafe P fx _ ⟨s, K, f, fvals V₁ ++ []⟩
  rw [List.append_nil, ← hV']
  exact tsafe_vals_seq h

theorem tsafe_refFunc (hQ : Inv Q) {V : List FVal} {x : FuncIdx} {a : Nat} {rest : List AdminFX}
    (hx : f.module.funcs[x.toNat]? = some a)
    (h : TSafe P fx Q ⟨s, K, f, fvals (V ++ [.val (.ref (.func a))]) ++ rest⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ .core (.plain (.refFunc x)) :: rest⟩ := by
  refine tsafe_cons hQ (tsafe_inert ⟨rfl, by simp, rfl⟩ (by simp) (by simp) (by simp) ?_)
  intro V₁ args c₀ hV hh
  obtain ⟨rfl, a', ha', rfl⟩ := head_refFunc hh
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans hx)
  have hV' : V = V₁ := by simpa [liftV] using hV
  have e : fvals V₁ ++ [Admin.ref (.func a')].map AdminFX.core = fvals (V ++ [.val (.ref (.func a'))]) := by
    rw [hV']; simp [FVal.toAdmin, Val.toAdmin]
  show TSafe P fx _ ⟨s, K, f, fvals V₁ ++ [Admin.ref (.func a')].map AdminFX.core⟩
  rw [e]
  exact tsafe_vals_seq h

theorem i32Add_args {V V₁ : List FVal} {a b : BitVec 32} {args : List Val} {x y : BitVec 32}
    (hV : V ++ [.val (Val.i32 a), .val (Val.i32 b)] = V₁ ++ liftV args)
    (hargs : args = [.num ⟨.int .i32, x⟩, .num ⟨.int .i32, y⟩]) : V₁ = V ∧ x = a ∧ y = b := by
  rw [hargs] at hV
  have h' : V ++ [.val (Val.i32 a), .val (Val.i32 b)] =
      V₁ ++ [.val (.num ⟨.int .i32, x⟩), .val (.num ⟨.int .i32, y⟩)] := by simpa [liftV] using hV
  obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
  have h3 : (⟨.int .i32, a⟩ : NumVal) = ⟨.int .i32, x⟩ ∧ (⟨.int .i32, b⟩ : NumVal) = ⟨.int .i32, y⟩ := by
    simpa [Val.i32] using h2
  exact ⟨h1.symm, (Silmaril.Wasm.Logic.Hoare.numVal_int_inj h3.1).symm,
    (Silmaril.Wasm.Logic.Hoare.numVal_int_inj h3.2).symm⟩

/-- **`i32.add`.** -/
theorem tsafe_i32Add (hQ : Inv Q) {V : List FVal} {a b : BitVec 32} {rest : List AdminFX}
    (h : TSafe P fx Q ⟨s, K, f, fvals (V ++ [.val (Val.i32 (a + b))]) ++ rest⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.val (Val.i32 a), .val (Val.i32 b)]) ++
      .core (.plain (.intBinOp .i32 .add)) :: rest⟩ := by
  refine tsafe_cons hQ (tsafe_inert ⟨rfl, by simp, rfl⟩ (by simp) (by simp) (by simp) ?_)
  intro V₁ args c₀ hV hh
  obtain ⟨x, y, hargs, ⟨z, hz, rfl⟩ | ⟨e, he, -⟩⟩ := Silmaril.Wasm.Logic.Hoare.head_intBinOp hh
  · obtain ⟨rfl, rfl, rfl⟩ := i32Add_args hV hargs
    have hz' : x + y = z := by simpa [Silmaril.Wasm.Numerics.intBinOp] using hz
    have e : fvals V₁ ++ [Admin.plain (.intConst .i32 z)].map AdminFX.core =
        fvals (V₁ ++ [.val (Val.i32 (x + y))]) := by
      rw [← hz']; simp [FVal.toAdmin, Val.toAdmin, Val.i32]
    show TSafe P fx _ ⟨s, K, f, fvals V₁ ++ [Admin.plain (.intConst .i32 z)].map AdminFX.core⟩
    rw [e]
    exact tsafe_vals_seq h
  · simp [Silmaril.Wasm.Numerics.intBinOp] at he

/-- **A call of an FX function** through `call_ref` (`invoke`), then code. -/
theorem tsafe_invoke_seq (hQ : Inv Q) {V : List FVal} {a : Nat} {fi : FuncInst H} {hh : H}
    {F : FuncFX} {c : Admin} {rest : List AdminFX} (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hfx : fx hh = some F)
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs → vs.length = F.nparams →
      TSafe P fx (framePost F.nresults f V₁ (seqPost (totJ P fx Q) rest Q))
        ⟨s, K, Frame.forCall F.module vs F.locals,
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.val (.ref (.func a))]) ++ .core c :: rest⟩ :=
  tsafe_cons hQ (tsafe_invoke hc hf hcode hfx fun V₁ vs hV hn =>
    tsafe_frame (inv_seqPost hQ _ _) (h V₁ vs hV hn))

/-- **`call`** of an FX function, then code. -/
theorem tsafe_call (hQ : Inv Q) {V : List FVal} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    {hh : H} {F : FuncFX} {rest : List AdminFX} (hx : f.module.funcs[x.toNat]? = some a)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh) (hfx : fx hh = some F)
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs → vs.length = F.nparams →
      TSafe P fx (framePost F.nresults f V₁ (seqPost (totJ P fx Q) rest Q))
        ⟨s, K, Frame.forCall F.module vs F.locals,
          [.label F.nresults [] (F.body.map InstrFX.toAdmin)]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ .core (.plain (.call x)) :: rest⟩ := by
  refine tsafe_cons hQ (tsafe_inert ⟨rfl, by simp, rfl⟩ (by simp) (by simp) (by simp) ?_)
  intro V₁ args c₀ hV hh'
  obtain ⟨rfl, a', fi', ha', hf', rfl⟩ := Silmaril.Wasm.Logic.Hoare.head_call hh'
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  have hV' : V₁ = V := by simpa [liftV] using hV.symm
  have h1 := tsafe_invoke (Q := seqPost (totJ P fx Q) rest Q) (V := V) (K := K)
    (c := .callRefType fi'.type) (by simp [Admin.IsCallRef]) hf hcode hfx fun V₂ vs hV₂ hn =>
      tsafe_frame (inv_seqPost hQ _ _) (h V₂ vs hV₂ hn)
  rw [hV']
  simpa [FVal.toAdmin, Val.toAdmin] using h1

/-- **`block`**, then code. -/
theorem tsafe_block_seq (hQ : Inv Q) {V : List FVal} {bt : BlockType} {body : List InstrFX}
    {t₁ t₂ : List Silmaril.Wasm.Validation.CValType} {rest : List AdminFX}
    (hbt : f.module.blockType? bt = some (t₁, t₂))
    (h : ∀ V₁ vs, V = V₁ ++ vs → vs.length = t₁.length →
      TSafe P fx (labelPost (totJ P fx (seqPost (totJ P fx Q) rest Q)) t₂.length [] V₁
        (seqPost (totJ P fx Q) rest Q)) ⟨s, K, f, fvals vs ++ body.map InstrFX.toAdmin⟩) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ .block bt body :: rest⟩ :=
  tsafe_cons hQ (tsafe_block hbt fun V₁ vs hV hm => tsafe_label (inv_seqPost hQ _ _) (h V₁ vs hV hm))

/-- **A label**, then code. -/
theorem tsafe_label_seq (hQ : Inv Q) {us : List FVal} {n : Nat} {k : List InstrFX}
    {b rest : List AdminFX}
    (h : TSafe P fx (labelPost (totJ P fx (seqPost (totJ P fx Q) rest Q)) n k us
      (seqPost (totJ P fx Q) rest Q)) ⟨s, K, f, b⟩) :
    TSafe P fx Q ⟨s, K, f, fvals us ++ .label n k b :: rest⟩ :=
  tsafe_cons hQ (tsafe_label (inv_seqPost hQ _ _) h)

/-- **A handler**, then code. -/
theorem tsafe_handler_seq (hQ : Inv Q) {us : List FVal} {hs : List HClause}
    {b rest : List AdminFX}
    (h : TSafe P fx (handlerPost (totJ P fx (seqPost (totJ P fx Q) rest Q)) hs us
      (seqPost (totJ P fx Q) rest Q)) ⟨s, K, f, b⟩) :
    TSafe P fx Q ⟨s, K, f, fvals us ++ .handler hs b :: rest⟩ :=
  tsafe_cons hQ (tsafe_handler (inv_seqPost hQ _ _) h)

/-- **`cont.new`**, then code. -/
theorem tsafe_contNew_seq (hQ : Inv Q) {V : List FVal} {a : Nat} {fi : FuncInst H}
    {ct : TypeIdx} {rest : List AdminFX} (hf : s.funcs[a]? = some fi)
    (h : TSafe P fx Q ⟨s, K ++ [some (newCont a fi)], f, fvals (V ++ [.cont K.length]) ++ rest⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.val (.ref (.func a))]) ++ .fx (.contNew ct) :: rest⟩ :=
  tsafe_cons hQ (tsafe_contNew hf (by
    have e : fvals V ++ [AdminFX.contRef K.length] = fvals (V ++ [.cont K.length]) := by
      simp [FVal.toAdmin]
    rw [e]
    exact tsafe_vals_seq h))

/-- **`resume`**, then code, for every payload split. -/
theorem tsafe_resume_seq (hQ : Inv Q) {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {hos : List OnClause} {hs' : List HClause} {rest : List AdminFX} (hk : K[k]? = some (some C))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      TSafe P fx (handlerPost (totJ P fx (seqPost (totJ P fx Q) rest Q)) hs' V₁
        (seqPost (totJ P fx Q) rest Q)) ⟨s, K.set k none, f, C.plug (fvals vs)⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ .fx (.resume ct hos) :: rest⟩ :=
  tsafe_cons hQ (tsafe_resume hk hr fun V₁ vs hV => tsafe_handler (inv_seqPost hQ _ _) (h V₁ vs hV))

/-- **Dropping a continuation**, then code. -/
theorem tsafe_dropCont_seq (hQ : Inv Q) {V : List FVal} {k : Nat} {rest : List AdminFX}
    (h : TSafe P fx Q ⟨s, K, f, fvals V ++ rest⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ .core (.plain .drop) :: rest⟩ :=
  tsafe_cons hQ (tsafe_dropCont (tsafe_vals_seq h))

/-- Plugging `suspend` into a context of values only. -/
theorem plug_vals_only {e : AdminFX} (he : fval? e = none) (hw : ¬ IsWrap e) {vs : List FVal} :
    ∀ (E : CtxV) {V : List FVal}, E.plug (fvals vs ++ [e]) = fvals V ++ [e] → ∃ V₁, V = V₁ ++ vs
  | .hole, V, h => ⟨[], by simpa using (fvals_append_cons_inj h he he).1.symm⟩
  | .seq us E rest, V, h => by
    obtain ⟨V', a, R, hp, ha, -⟩ := plug_cases (vs := vs) he E
    have h' : fvals (us ++ V') ++ a :: (R ++ rest) = fvals V ++ e :: [] := by
      rw [← h]; simp [CtxV.plug, hp]
    obtain ⟨hV, rfl, hR⟩ := fvals_append_cons_inj h' ha he
    obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.mp hR
    obtain ⟨V₁, rfl⟩ := plug_vals_only he hw E hp
    exact ⟨us ++ V₁, by rw [← hV]; simp⟩
  | .label n k E, V, h => absurd ((fvals_append_cons_inj (V₁ := []) h rfl he).2.1 ▸ trivial) hw
  | .frame n fi E, V, h => absurd ((fvals_append_cons_inj (V₁ := []) h rfl he).2.1 ▸ trivial) hw
  | .handler hs E, V, h => absurd ((fvals_append_cons_inj (V₁ := []) h rfl he).2.1 ▸ trivial) hw

/-- **An unhandled `suspend`**, then code: it stops with every split of the values below it. -/
theorem tsafe_suspend_seq (hQ : Inv Q) {V : List FVal} {x : TagIdx} {rest : List AdminFX}
    (h : ∀ V₁ vs, V = V₁ ++ vs → Q s K f (.susp (.seq V₁ .hole rest) vs x)) :
    TSafe P fx Q ⟨s, K, f, fvals V ++ .fx (.suspend x) :: rest⟩ := by
  refine tsafe_cons hQ (tsafe_suspend fun E vs hE _ => ?_)
  obtain ⟨V₁, rfl⟩ := plug_vals_only (e := .fx (.suspend x)) rfl id E hE
  have hp : (CtxV.seq V₁ .hole rest).plug (suspCode vs x) =
      (CtxV.seq [] E rest).plug (suspCode vs x) := by
    have hE' : E.plug (fvals vs ++ [.fx (.suspend x)]) = fvals (V₁ ++ vs) ++ [.fx (.suspend x)] := hE
    simp only [CtxV.plug, suspCode]
    rw [hE']; simp
  exact hQ.1 s K f _ _ vs x hp (h V₁ vs rfl)

/-- `tsafe_label` at an explicit configuration. -/
theorem tsafe_label' (hQ : Inv Q) {n : Nat} {k : List InstrFX} {us : List FVal}
    {b : List AdminFX} (h : TSafe P fx (labelPost (totJ P fx Q) n k us Q) ⟨s, K, f, b⟩) :
    TSafe P fx Q ⟨s, K, f, fvals us ++ [.label n k b]⟩ :=
  tsafe_label hQ h

/-- `tsafe_frame` at an explicit configuration. -/
theorem tsafe_frame' (hQ : Inv Q) {n : Nat} {F : Frame} {us : List FVal} {b : List AdminFX}
    (h : TSafe P fx (framePost n f us Q) ⟨s, K, F, b⟩) :
    TSafe P fx Q ⟨s, K, f, fvals us ++ [.frame n F b]⟩ :=
  tsafe_frame hQ h

/-- `tsafe_handler` at an explicit configuration. -/
theorem tsafe_handler' (hQ : Inv Q) {hs : List HClause} {us : List FVal} {b : List AdminFX}
    (h : TSafe P fx (handlerPost (totJ P fx Q) hs us Q) ⟨s, K, f, b⟩) :
    TSafe P fx Q ⟨s, K, f, fvals us ++ [.handler hs b]⟩ :=
  tsafe_handler hQ h

/-- **An unhandled `switch`** to the continuation `k` stops, for every split of the values
below its target. -/
theorem tsafe_switch {V : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx}
    (h : ∀ E vs, E.plug (switchCode vs k ct x) = fvals (V ++ [.cont k]) ++ [.fx (.switch ct x)] →
      Unhandled s f E x → Q s K f (.swtch E vs k ct x)) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.switch ct x)]⟩ := by
  refine .intro (fun o ho => ?_) fun y hy => ?_
  · have hfoc := stops_focus rfl ho
    cases o with
    | swtch E vs k' ct' x' =>
      rcases hfoc with hx | hw
      · obtain ⟨hct, hxx⟩ : ct' = ct ∧ x' = x := by simpa using hx.symm
        rw [hct, hxx] at ho ⊢
        have h1 : E.plug (fvals (vs ++ [.cont k']) ++ [.fx (.switch ct x)]) =
            fvals (V ++ [.cont k]) ++ [.fx (.switch ct x)] := by rw [← switchCode_eq]; exact ho.1.symm
        obtain ⟨V₁, hV⟩ := plug_vals_only rfl id E h1
        obtain rfl : k' = k := by
          have := (List.append_inj' (show V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k'] by rw [hV]; simp) rfl).2
          simpa using this.symm
        exact h E vs ho.1.symm ho.2
      · exact hw.elim
    | susp E vs x' => exact (hfoc.elim (by simp) id).elim
    | _ => simp_all [FocusOf]
  · obtain ⟨V₁, V₂, y', -, hroot, -⟩ := lastRes_y hy rfl
    cases hroot

/-- A `switch` without a continuation below it neither steps nor stops. -/
theorem tsafe_switch_nil {ct : TypeIdx} {x : TagIdx} :
    TSafe P fx Q ⟨s, K, f, fvals [] ++ [.fx (.switch ct x)]⟩ := by
  refine .intro (fun o ho => ?_) fun y hy => ?_
  · have hfoc := stops_focus rfl ho
    cases o with
    | swtch E vs k' ct' x' =>
      rcases hfoc with hx | hw
      · obtain ⟨hct, hxx⟩ : ct' = ct ∧ x' = x := by simpa using hx.symm
        rw [hct, hxx] at ho
        have h1 : E.plug (fvals (vs ++ [.cont k']) ++ [.fx (.switch ct x)]) =
            fvals [] ++ [.fx (.switch ct x)] := by rw [← switchCode_eq]; exact ho.1.symm
        obtain ⟨V₁, hV⟩ := plug_vals_only rfl id E h1
        simp at hV
      · exact hw.elim
    | susp E vs x' => exact (hfoc.elim (by simp) id).elim
    | _ => simp_all [FocusOf]
  · obtain ⟨V₁, V₂, y', -, hroot, -⟩ := lastRes_y hy rfl
    cases hroot

/-- **An unhandled `switch`**, then code. -/
theorem tsafe_switch_seq (hQ : Inv Q) {V : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx}
    {rest : List AdminFX}
    (h : ∀ V₁ vs, V = V₁ ++ vs → Q s K f (.swtch (.seq V₁ .hole rest) vs k ct x)) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ .fx (.switch ct x) :: rest⟩ := by
  refine tsafe_cons hQ (tsafe_switch fun E vs hE _ => ?_)
  have hE' : E.plug (fvals (vs ++ [.cont k]) ++ [.fx (.switch ct x)]) =
      fvals (V ++ [.cont k]) ++ [.fx (.switch ct x)] := by rw [← switchCode_eq]; exact hE
  obtain ⟨V₁, hV₁⟩ := plug_vals_only rfl id E hE'
  have hV : V = V₁ ++ vs :=
    (List.append_inj' (show V ++ [.cont k] = (V₁ ++ vs) ++ [.cont k] by rw [hV₁]; simp) rfl).1
  have hp : (CtxV.seq V₁ .hole rest).plug (switchCode vs k ct x) =
      (CtxV.seq [] E rest).plug (switchCode vs k ct x) := by
    have hE'' : E.plug (switchCode vs k ct x) = fvals (V₁ ++ vs ++ [.cont k]) ++ [.fx (.switch ct x)] := by
      rw [hE, hV]
    simp only [CtxV.plug]
    rw [hE'']; simp [switchCode, FVal.toAdmin]
  exact hQ.2 s K f _ _ vs k ct x hp (h V₁ vs hV)

/-- A `switch` without a continuation below it, then code. -/
theorem tsafe_switch_nil_seq (hQ : Inv Q) {ct : TypeIdx} {x : TagIdx} {rest : List AdminFX} :
    TSafe P fx Q ⟨s, K, f, fvals [] ++ .fx (.switch ct x) :: rest⟩ :=
  tsafe_cons hQ tsafe_switch_nil

end Silmaril.Proofs.Wasm.FX.Logic.EveryRun
