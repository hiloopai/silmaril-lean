module

public import Silmaril.Wasm.Binaryen.Pass.RUMESim.Head

@[expose] public section

/-! # Simulation under address maps: the head-step simulation -/

namespace Silmaril.Wasm.Binaryen.RUMESim

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

theorem flatF_of_fam {n0 : Nat} {e : Admin} (h : famOf e ≠ .control) : flatF n0 e := by
  cases e with
  | plain i => trivial
  | _ => exact absurd rfl h

theorem CodeR.trap_inv {X : SimCtx} {m : Mode} {ys : List Admin} (h : CodeR X m [.trap] ys) :
    ys = [.trap] := by
  have h' : CodeR X m (vals [] ++ .trap :: []) ys := h
  obtain ⟨x', rest', rfl, -, hx, hr⟩ := CodeR.split_nc h' rfl (by simp)
  rw [ARel.trap_inv hx]
  cases hr
  rfl

theorem ARel.same_of_rcr {X : SimCtx} {c : Admin} (hc : c.IsReturnCallRef) : ARel X .same c c := by
  rcases IsReturnCallRef.cases hc with ⟨y, rfl⟩ | ⟨d, rfl⟩
  · exact .plainS
  · exact .returnCallRefType

theorem famOf_callRefType (d : DefType) : famOf (.callRefType d) = .control := rfl

/-- The arguments of a head step at a `CALL_REF` end with a reference. -/
theorem head_callRefType_args {S : Store H} {f : Frame} {args : List Val} {d : DefType}
    {c₀ : Config H} (h : Head P S f args (.callRefType d) c₀) :
    ∃ vs r, args = vs ++ [.ref r] := by
  generalize hE : Admin.callRefType d = E at h
  cases h with
  | parametric hp =>
    have := (famOf_of_shape (ParametricStep.shape hp)).2
    rw [← hE] at this; cases this
  | numeric hp =>
    have := (famOf_of_shape (NumericStep.shape hp)).2
    rw [← hE] at this; cases this
  | vector hp =>
    have := (famOf_of_shape (VectorStep.shape hp)).2
    rw [← hE] at this; cases this
  | «variable» hp =>
    have := (famOf_of_shape (VariableStep.shape hp)).2
    rw [← hE] at this; cases this
  | table hp =>
    have := (famOf_of_shape (TableStep.shape hp)).2
    rw [← hE] at this; cases this
  | memory hp =>
    have := (famOf_of_shape (MemoryStep.shape hp)).2
    rw [← hE] at this; cases this
  | reference hp =>
    have := (famOf_of_shape (RefStep.shape hp)).2
    rw [← hE] at this; cases this
  | aggregate hp =>
    have := (famOf_of_shape (AggregateStep.shape hp)).2
    rw [← hE] at this; cases this
  | callRefNull hc => exact ⟨[], .null, rfl⟩
  | callRefFunc ha => exact ⟨_, _, ha⟩
  | _ => cases hE

/-- **Head steps.** -/
theorem head_sim {X : SimCtx} (hX : X.WF) {m : Mode} {S T : Store H} {f f' : Frame}
    {args : List Val} {e e' : Admin} {c₀ : Config H}
    (ih : ∀ (S₁ : Store H) (fi : Frame) (body : List Admin) (c : Config H),
      sizeOf body < sizeOf e → Step P noHost ⟨S₁, fi, body⟩ c →
      ∀ (T₁ : Store H) (fi' : Frame) (body' : List Admin) (m' : Mode),
      StoreRel X S₁ T₁ → FrameRel X m' fi fi' → CodeR X m' body body' →
      ∃ c', Step P noHost ⟨T₁, fi', body'⟩ c' ∧ ConfRel X m' c c')
    (h : Head P S f args e c₀) (hargs : ∀ v ∈ args, valF X.n0 v) (he : ARel X m e e')
    (hS : StoreRel X S T) (hf : FrameRel X m f f') :
    ∃ c₀', Step P noHost ⟨T, f', vals args ++ [e']⟩ c₀' ∧ ConfRel X m c₀ c₀' := by
  have hgood := h.good
  cases h with
  | parametric hp =>
    have hk := (famOf_of_shape (ParametricStep.shape hp)).2
    obtain rfl := ARel.fam_pure he (.inl hk)
    exact ⟨_, .parametric hp, hS, hf,
      CodeR.of_valTrap (parametric_out hp (flat_args hargs (flatF_of_fam (by rw [hk]; decide))))⟩
  | numeric hp =>
    have hk := (famOf_of_shape (NumericStep.shape hp)).2
    obtain rfl := ARel.fam_pure he (.inr (.inl hk))
    exact ⟨_, .numeric hp, hS, hf, CodeR.of_valTrap (numeric_out hp)⟩
  | vector hp =>
    have hk := (famOf_of_shape (VectorStep.shape hp)).2
    obtain rfl := ARel.fam_pure he (.inr (.inr (.inl hk)))
    exact ⟨_, .vector hp, hS, hf, CodeR.of_valTrap (vector_out hp)⟩
  | table hp =>
    have hk := (famOf_of_shape (TableStep.shape hp)).2
    obtain ⟨rfl, rfl⟩ := ARel.fam_same he (.inl hk)
    obtain ⟨rfl, hfs⟩ := hf
    have hfl := flat_args hargs (flatF_of_fam (n0 := X.n0) (by rw [hk]; decide))
    obtain ⟨hfun, hglob, hfr⟩ := tableStep_fg hp
    obtain ⟨hF, hout⟩ := tableStep_fgn hp hS.fgn hfl
    have hst := Step.table (host := noHost) (tableStep_withFG hp T.funcs T.globals)
    rw [← hS.T_eq] at hst
    exact ⟨_, hst, hS.withFG_of hfun hglob hF, ⟨rfl, by rw [hfr]; exact hfs⟩, CodeR.of_flat hout⟩
  | memory hp =>
    have hk := (famOf_of_shape (MemoryStep.shape hp)).2
    obtain rfl := ARel.fam_pure he (.inr (.inr (.inr hk)))
    have hfl := flat_args hargs (flatF_of_fam (n0 := X.n0) (by rw [hk]; decide))
    obtain ⟨hfun, hglob, hfr⟩ := memoryStep_fg hp
    obtain ⟨hF, -⟩ := memoryStep_fgn hp hS.fgn hfl
    have hst := Step.memory (host := noHost)
      (memoryStep_withFG (memoryStep_frame (hf.mems hX) (hf.datas hX) hp) T.funcs T.globals)
    rw [← hS.T_eq] at hst
    refine ⟨_, hst, hS.withFG_of hfun hglob hF, ?_, memoryStep_code hp hfl⟩
    simpa only [hfr] using hf
  | reference hp =>
    have hk := (famOf_of_shape (RefStep.shape hp)).2
    obtain ⟨rfl, rfl⟩ := ARel.fam_same he (.inr (.inl hk))
    obtain ⟨rfl, hfs⟩ := hf
    have hfl := flat_args hargs (flatF_of_fam (n0 := X.n0) (by rw [hk]; decide))
    obtain ⟨hst0, hfr⟩ := refStep_fg hp
    obtain ⟨hF, hout⟩ := refStep_fgn hp hS.fgn hfs.1 hfl
    have hst := Step.reference (host := noHost) (P := P) (refStep_withFG hp T.funcs T.globals hfl
      (fun r t hr => refOk_withFG_iff (fun a ha => hS.funcs a ha) hr))
    rw [← hS.T_eq] at hst
    exact ⟨_, hst, hS.withFG_of (by rw [hst0]) (by rw [hst0]) hF, ⟨rfl, by rw [hfr]; exact hfs⟩,
      CodeR.of_flat hout⟩
  | aggregate hp =>
    have hk := (famOf_of_shape (AggregateStep.shape hp)).2
    obtain ⟨rfl, rfl⟩ := ARel.fam_same he (.inr (.inr hk))
    obtain ⟨rfl, hfs⟩ := hf
    have hfl := flat_args hargs (flatF_of_fam (n0 := X.n0) (by rw [hk]; decide))
    obtain ⟨hfun, hglob, hfr⟩ := aggregateStep_fg hp
    obtain ⟨hF, hout⟩ := aggregateStep_fgn hp hS.fgn hfl
    have hst := Step.aggregate (host := noHost) (P := P) (aggregateStep_withFG hp T.funcs T.globals)
    rw [← hS.T_eq] at hst
    exact ⟨_, hst, hS.withFG_of hfun hglob hF, ⟨rfl, by rw [hfr]; exact hfs⟩, CodeR.of_flat hout⟩
  | «variable» hv =>
    generalize hl : vals args ++ [e] = l at hv
    cases hv with
    | localGet hx =>
      obtain ⟨rfl, rfl⟩ := snoc_inv (B := []) hl hgood.val_none rfl
      obtain rfl := ARel.plain_simple rfl he
      obtain ⟨hx', hv⟩ := local?_val hf hx
      exact ⟨_, .variable (.localGet hx'), hS, hf, .cons (ARel.val hv) .nil⟩
    | localSet hx =>
      obtain ⟨rfl, rfl⟩ := snoc_inv (B := [_]) hl hgood.val_none rfl
      obtain rfl := ARel.plain_simple rfl he
      have hv : valF X.n0 _ := hargs _ (List.mem_singleton_self _)
      exact ⟨_, .variable (.localSet (by rw [← hf.locals]; exact hx)), hS, hf.setLocal _ hv, .nil⟩
    | localTee =>
      obtain ⟨rfl, rfl⟩ := snoc_inv (B := [_]) hl hgood.val_none rfl
      obtain rfl := ARel.plain_simple rfl he
      have hv : valF X.n0 _ := hargs _ (List.mem_singleton_self _)
      exact ⟨_, .variable .localTee, hS, hf,
        .cons (ARel.val hv) (.cons (ARel.val hv) (CodeR.plain_simple rfl))⟩
    | globalGet hg =>
      obtain ⟨rfl, rfl⟩ := snoc_inv (B := []) hl hgood.val_none rfl
      cases he with
      | plainS =>
        obtain ⟨rfl, hfs⟩ := hf
        obtain ⟨-, hgT⟩ := hS.global_lo hfs.1 hg
        have hv := hS.fgn.globals _ (List.mem_of_getElem? (global?_some hg).2)
        exact ⟨_, .variable (.globalGet hgT), hS, ⟨rfl, hfs⟩, .cons (ARel.val hv) .nil⟩
      | plainO hj =>
        cases hj with
        | globalGet hk =>
          obtain ⟨h1, h2⟩ := global?_some hg
          rw [hf.1] at h1
          obtain ⟨b, hb, hab⟩ := hX.kg _ _ _ hk h1
          obtain ⟨-, -, g', hg1, hg2⟩ := hS.gpair _ b hab
          rw [h2] at hg1
          cases hg1
          have hv := hS.fgn.globals _ (List.mem_of_getElem? h2)
          exact ⟨_, .variable (.globalGet (global?_of (by rw [hf.2.1]; exact hb) hg2)), hS, hf,
            .cons (ARel.val hv) .nil⟩
        | simple h => simp [simpleI] at h
    | globalSet hg =>
      obtain ⟨rfl, rfl⟩ := snoc_inv (B := [_]) hl hgood.val_none rfl
      have hv : valF X.n0 _ := hargs _ (List.mem_singleton_self _)
      cases he with
      | plainS =>
        obtain ⟨rfl, hfs⟩ := hf
        obtain ⟨ha, hgT⟩ := hS.global_lo hfs.1 hg
        exact ⟨_, .variable (.globalSet hgT), hS.setGlobal_lo ha hv, ⟨rfl, hfs⟩, .nil⟩
      | plainO hj =>
        cases hj with
        | globalSet hk =>
          obtain ⟨h1, h2⟩ := global?_some hg
          rw [hf.1] at h1
          obtain ⟨b, hb, hab⟩ := hX.kg _ _ _ hk h1
          obtain ⟨-, -, g', hg1, hg2⟩ := hS.gpair _ b hab
          exact ⟨_, .variable (.globalSet (global?_of (by rw [hf.2.1]; exact hb) hg2)),
            hS.setGlobal_pair hX hab hv, hf, .nil⟩
        | simple h => simp [simpleI] at h
  | ctxtLabel hst =>
    obtain ⟨cont', b', rfl, hc, hb⟩ := ARel.label_inv he
    obtain ⟨⟨T', f₁, b''⟩, hst', hS', hf', hb'⟩ :=
      ih _ _ _ _ (sizeOf_label_lt _ _ _) hst T f' b' m hS hf hb
    exact ⟨_, .ctxtLabel hst', hS', hf', .cons (ARel.label_of hc hb') .nil⟩
  | ctxtHandler hst =>
    obtain ⟨rfl, b', rfl, hb⟩ := ARel.handler_inv he
    obtain ⟨⟨T', f₁, b''⟩, hst', hS', hf', hb'⟩ :=
      ih _ _ _ _ (sizeOf_handler_lt _ _ _) hst T f' b' .same hS hf hb
    exact ⟨_, .ctxtHandler hst', hS', hf', .cons (.handler hb') .nil⟩
  | ctxtFrame hst =>
    obtain ⟨m', fr', b', rfl, hfr, hb⟩ := ARel.frame_inv he
    obtain ⟨⟨T', fr'', b''⟩, hst', hS', hfr', hb'⟩ :=
      ih _ _ _ _ (sizeOf_frame_lt _ _ _) hst T fr' b' m' hS hfr hb
    exact ⟨_, .ctxtFrame hst', hS', hf, .cons (ARel.frame_of hfr' hb') .nil⟩
  | block hbt hm =>
    have hbt' := hbt
    rw [blockType?_congr (hf.types hX)] at hbt'
    cases he with
    | plainS =>
      exact ⟨_, .block hbt' hm, hS, hf,
        .cons (.labelS (CodeR.append (CodeR.ofVals hargs) (CodeR.expression_same _))) .nil⟩
    | plainO hj =>
      cases hj with
      | block hb =>
        exact ⟨_, .block hbt' hm, hS, hf,
          .cons (.labelO .nil (CodeR.append (CodeR.ofVals hargs) (IRels.expression hb))) .nil⟩
      | simple h => simp [simpleI] at h
  | loop hbt hm =>
    have hbt' := hbt
    rw [blockType?_congr (hf.types hX)] at hbt'
    cases he with
    | plainS =>
      exact ⟨_, .loop hbt' hm, hS, hf,
        .cons (.labelS (CodeR.append (CodeR.ofVals hargs) (CodeR.expression_same _))) .nil⟩
    | plainO hj =>
      cases hj with
      | loop hb =>
        exact ⟨_, .loop hbt' hm, hS, hf,
          .cons (.labelO (.cons (.loop hb) .nil)
            (CodeR.append (CodeR.ofVals hargs) (IRels.expression hb))) .nil⟩
      | simple h => simp [simpleI] at h
  | ifTrue hc =>
    cases he with
    | plainS => exact ⟨_, .ifTrue hc, hS, hf, .cons .plainS .nil⟩
    | plainO hj =>
      cases hj with
      | if_ h₁ h₂ => exact ⟨_, .ifTrue hc, hS, hf, .cons (.plainO (.block h₁)) .nil⟩
      | simple h => simp [simpleI] at h
  | ifFalse hc =>
    subst hc
    cases he with
    | plainS => exact ⟨_, .ifFalse, hS, hf, .cons .plainS .nil⟩
    | plainO hj =>
      cases hj with
      | if_ h₁ h₂ => exact ⟨_, .ifFalse, hS, hf, .cons (.plainO (.block h₂)) .nil⟩
      | simple h => simp [simpleI] at h
  | labelVals hb =>
    subst hb
    obtain ⟨cont', b', rfl, -, hb'⟩ := ARel.label_inv he
    obtain ⟨rfl, hvs⟩ := CodeR.vals_inv hb'
    exact ⟨_, .labelVals, hS, hf, CodeR.ofVals hvs⟩
  | brLabelZero hb hl hn =>
    subst hb
    obtain ⟨cont', b', rfl, hc, hb'⟩ := ARel.label_inv he
    obtain ⟨x', R', rfl, -, hB, hx, -⟩ := CodeR.split2 hb' rfl (by simp)
    obtain rfl := ARel.plain_simple rfl hx
    exact ⟨_, .brLabelZero hl hn, hS, hf, CodeR.append (CodeR.ofVals hB) hc.expression⟩
  | brLabelSucc hb hl =>
    subst hb
    obtain ⟨cont', b', rfl, hc, hb'⟩ := ARel.label_inv he
    obtain ⟨x', R', rfl, hA, hx, -⟩ := CodeR.split1 hb' rfl (by simp)
    obtain rfl := ARel.plain_simple rfl hx
    exact ⟨_, .brLabelSucc hl, hS, hf, CodeR.append (CodeR.ofVals hA) (CodeR.plain_simple rfl)⟩
  | brHandler hb =>
    subst hb
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    obtain ⟨x', R', rfl, hA, hx, -⟩ := CodeR.split1 hb' rfl (by simp)
    obtain rfl := ARel.plain_simple rfl hx
    exact ⟨_, .brHandler, hS, hf, CodeR.append (CodeR.ofVals hA) (CodeR.plain_simple rfl)⟩
  | brIfTrue hc =>
    obtain rfl := ARel.plain_simple rfl he
    exact ⟨_, .brIfTrue hc, hS, hf, CodeR.plain_simple rfl⟩
  | brIfFalse hc =>
    subst hc
    obtain rfl := ARel.plain_simple rfl he
    exact ⟨_, .brIfFalse, hS, hf, .nil⟩
  | brTableLt hi =>
    obtain rfl := ARel.plain_simple rfl he
    exact ⟨_, .brTableLt hi, hS, hf, CodeR.plain_simple rfl⟩
  | brTableGe hi =>
    obtain rfl := ARel.plain_simple rfl he
    exact ⟨_, .brTableGe hi, hS, hf, CodeR.plain_simple rfl⟩
  | brOnNullNull =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    exact ⟨_, .brOnNullNull, hS, hf, .cons .plainS .nil⟩
  | brOnNullAddr hv =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    exact ⟨_, .brOnNullAddr hv, hS, hf, .cons (ARel.val (hargs _ (by simp))) .nil⟩
  | brOnNonNullNull =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    exact ⟨_, .brOnNonNullNull, hS, hf, .nil⟩
  | brOnNonNullAddr hv =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    exact ⟨_, .brOnNonNullAddr hv, hS, hf,
      .cons (ARel.val (hargs _ (by simp))) (.cons .plainS .nil)⟩
  | brOnCastSucceed h =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    obtain ⟨rfl, hfs⟩ := hf
    have hr : refF X.n0 _ := hargs _ (List.mem_singleton_self _)
    exact ⟨_, .brOnCastSucceed ((hS.refOk_iff hr).1 h), hS, ⟨rfl, hfs⟩,
      .cons (.ref hr) (.cons .plainS .nil)⟩
  | brOnCastFail h =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    obtain ⟨rfl, hfs⟩ := hf
    have hr : refF X.n0 _ := hargs _ (List.mem_singleton_self _)
    exact ⟨_, .brOnCastFail (fun h' => h ((hS.refOk_iff hr).2 h')), hS, ⟨rfl, hfs⟩,
      .cons (.ref hr) .nil⟩
  | brOnCastFailSucceed h =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    obtain ⟨rfl, hfs⟩ := hf
    have hr : refF X.n0 _ := hargs _ (List.mem_singleton_self _)
    exact ⟨_, .brOnCastFailSucceed ((hS.refOk_iff hr).1 h), hS, ⟨rfl, hfs⟩, .cons (.ref hr) .nil⟩
  | brOnCastFailFail h =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    obtain ⟨rfl, hfs⟩ := hf
    have hr : refF X.n0 _ := hargs _ (List.mem_singleton_self _)
    exact ⟨_, .brOnCastFailFail (fun h' => h ((hS.refOk_iff hr).2 h')), hS, ⟨rfl, hfs⟩,
      .cons (.ref hr) (.cons .plainS .nil)⟩
  | @call _ x a fi hx hfi =>
    cases he with
    | plainS =>
      obtain ⟨rfl, hfs⟩ := hf
      have ha : a < X.n0 := hfs.1.1 a (List.mem_of_getElem? hx)
      exact ⟨_, .call hx (hS.func_lo ha hfi), hS, ⟨rfl, hfs⟩,
        .cons (.ref ha) (.cons .callRefType .nil)⟩
    | plainO hj =>
      cases hj with
      | call hk =>
        rw [hf.1] at hx
        obtain ⟨b, hb, hab⟩ := hX.kf _ _ _ hk hx
        have hb' := hb
        rw [← hf.2.1] at hb'
        rcases hS.fpair a b hab with ⟨ha, rfl⟩ | ⟨-, -, fA, fB, cA, cB, h1, h2, h3, -⟩
        · exact ⟨_, .call hb' (hS.func_lo ha hfi), hS, hf, .pair hab .nil⟩
        · rw [hfi] at h1
          cases h1
          refine ⟨_, .call hb' h2, hS, hf, ?_⟩
          rw [← h3]
          exact .pair hab .nil
      | simple h => simp [simpleI] at h
  | callRefNull hc =>
    obtain rfl := ARel.callRef_eq hc he
    exact ⟨_, .callRefNull hc, hS, hf, CodeR.trap⟩
  | @callRefFunc _ c _ vs a fi ps rs code ha hc hfi hexp hn hcode =>
    subst ha
    obtain rfl := ARel.callRef_eq hc he
    have hra : a < X.n0 := by simpa using hargs (.ref (.func a)) (by simp)
    have hvs : ∀ v ∈ vs, valF X.n0 v := fun v hv => hargs v (by simp [hv])
    have hm : modF X.n0 X.g0 fi.module := hS.fgn.funcs a hra fi hfi _ hcode
    rw [vals_snoc_append]
    exact ⟨_, .callRefFunc hc (hS.func_lo hra hfi) hexp hn hcode, hS, hf,
      .cons (.frameS (frameS_forCall hm hvs) (.cons (.labelS (CodeR.expression_same _)) .nil)) .nil⟩
  | returnCall hx hfi =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    obtain ⟨rfl, hfs⟩ := hf
    have ha : _ < X.n0 := hfs.1.1 _ (List.mem_of_getElem? hx)
    exact ⟨_, .returnCall hx (hS.func_lo ha hfi), hS, ⟨rfl, hfs⟩,
      .cons (.ref ha) (.cons .returnCallRefType .nil)⟩
  | returnCallRefLabel hb hc =>
    subst hb
    obtain ⟨cont', b', rfl, -, hb'⟩ := ARel.label_inv he
    obtain ⟨c', R', rfl, hA, hcc, -⟩ :=
      CodeR.split1 hb' (IsReturnCallRef.val_none hc) (IsReturnCallRef.ne_callRefType hc)
    obtain ⟨rfl, rfl⟩ := ARel.returnCall_same hc hcc
    exact ⟨_, .returnCallRefLabel hc, hS, hf,
      CodeR.append (CodeR.ofVals hA) (.cons (ARel.same_of_rcr hc) .nil)⟩
  | returnCallRefHandler hb hc =>
    subst hb
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    obtain ⟨c', R', rfl, hA, hcc, -⟩ :=
      CodeR.split1 hb' (IsReturnCallRef.val_none hc) (IsReturnCallRef.ne_callRefType hc)
    obtain ⟨-, rfl⟩ := ARel.returnCall_same hc hcc
    exact ⟨_, .returnCallRefHandler hc, hS, hf,
      CodeR.append (CodeR.ofVals hA) (.cons (ARel.same_of_rcr hc) .nil)⟩
  | returnCallRefFrameNull hb hc =>
    subst hb
    obtain ⟨m', fr', b', rfl, hfr, hb'⟩ := ARel.frame_inv he
    obtain ⟨c', R', rfl, -, -, hcc, -⟩ := CodeR.split3 (v := .ref .null) hb'
      (IsReturnCallRef.val_none hc) (IsReturnCallRef.ne_callRefType hc)
    obtain ⟨rfl, rfl⟩ := ARel.returnCall_same hc hcc
    exact ⟨_, .returnCallRefFrameNull hc, hS, hf, CodeR.trap⟩
  | returnCallRefFrameAddr hb hc hfn hexp hn =>
    subst hb
    obtain ⟨m', fr', b', rfl, hfr, hb'⟩ := ARel.frame_inv he
    obtain ⟨c', R', rfl, hB, hra, hcc, -⟩ := CodeR.split4 (v := .ref (.func _)) hb'
      (IsReturnCallRef.val_none hc) (IsReturnCallRef.ne_callRefType hc)
    obtain ⟨rfl, rfl⟩ := ARel.returnCall_same hc hcc
    obtain ⟨rfl, -⟩ := hfr
    exact ⟨_, .returnCallRefFrameAddr hc (hS.func_lo hra hfn) hexp hn, hS, hf,
      CodeR.append (CodeR.ofVals hB) (.cons (.ref hra) (.cons (ARel.retToCallIn hc _) .nil))⟩
  | callIndirect =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    exact ⟨_, .callIndirect, hS, hf, .cons .plainS (.cons .plainS (.cons .plainS .nil))⟩
  | returnCallIndirect =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    exact ⟨_, .returnCallIndirect, hS, hf, .cons .plainS (.cons .plainS (.cons .plainS .nil))⟩
  | frameVals hb hn =>
    subst hb
    obtain ⟨m', fr', b', rfl, hfr, hb'⟩ := ARel.frame_inv he
    obtain ⟨rfl, hvs⟩ := CodeR.vals_inv hb'
    exact ⟨_, .frameVals hn, hS, hf, CodeR.ofVals hvs⟩
  | returnFrame hb hn =>
    subst hb
    obtain ⟨m', fr', b', rfl, hfr, hb'⟩ := ARel.frame_inv he
    obtain ⟨x', R', rfl, -, hB, hx, -⟩ := CodeR.split2 hb' rfl (by simp)
    obtain rfl := ARel.plain_simple rfl hx
    exact ⟨_, .returnFrame hn, hS, hf, CodeR.ofVals hB⟩
  | returnLabel hb =>
    subst hb
    obtain ⟨cont', b', rfl, -, hb'⟩ := ARel.label_inv he
    obtain ⟨x', R', rfl, hA, hx, -⟩ := CodeR.split1 hb' rfl (by simp)
    obtain rfl := ARel.plain_simple rfl hx
    exact ⟨_, .returnLabel, hS, hf, CodeR.append (CodeR.ofVals hA) (CodeR.plain_simple rfl)⟩
  | returnHandler hb =>
    subst hb
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    obtain ⟨x', R', rfl, hA, hx, -⟩ := CodeR.split1 hb' rfl (by simp)
    obtain rfl := ARel.plain_simple rfl hx
    exact ⟨_, .returnHandler, hS, hf, CodeR.append (CodeR.ofVals hA) (CodeR.plain_simple rfl)⟩
  | throw ht hexp hn =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    obtain ⟨rfl, hfs⟩ := hf
    refine ⟨_, .throw ((tag?_congr hS.tags_eq _ _).symm.trans ht) hexp hn, hS.addExn _ hargs,
      ⟨rfl, hfs⟩, ?_⟩
    rw [← hS.exns_eq]
    exact CodeR.throwing _
  | throwRefNull =>
    obtain rfl := ARel.plain_simple rfl he
    exact ⟨_, .throwRefNull, hS, hf, CodeR.trap⟩
  | throwRefLabel =>
    obtain ⟨cont', b', rfl, -, hb'⟩ := ARel.label_inv he
    rw [CodeR.throwing_inv hb']
    exact ⟨_, .throwRefLabel, hS, hf, CodeR.throwing _⟩
  | throwRefFrame =>
    obtain ⟨m', fr', b', rfl, hfr, hb'⟩ := ARel.frame_inv he
    rw [CodeR.throwing_inv hb']
    exact ⟨_, .throwRefFrame, hS, hf, CodeR.throwing _⟩
  | throwRefHandlerEmpty =>
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    rw [CodeR.throwing_inv hb']
    exact ⟨_, .throwRefHandlerEmpty, hS, hf, CodeR.throwing _⟩
  | @throwRefHandlerCatch _ n x l cs a ex hexn ht =>
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    rw [CodeR.throwing_inv hb']
    obtain ⟨rfl, hfs⟩ := hf
    have hexn' : T.exns[a]? = some ex := by rw [← hS.exns_eq]; exact hexn
    have hv : ∀ v ∈ ex.fields, valF X.n0 v := hS.fgn.exns ex (List.mem_of_getElem? hexn)
    exact ⟨_, .throwRefHandlerCatch hexn' ht, hS, ⟨rfl, hfs⟩,
      CodeR.append (CodeR.ofVals hv) (.cons .plainS .nil)⟩
  | @throwRefHandlerCatchRef _ n x l cs a ex hexn ht =>
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    rw [CodeR.throwing_inv hb']
    obtain ⟨rfl, hfs⟩ := hf
    have hexn' : T.exns[a]? = some ex := by rw [← hS.exns_eq]; exact hexn
    have hv : ∀ v ∈ ex.fields, valF X.n0 v := hS.fgn.exns ex (List.mem_of_getElem? hexn)
    exact ⟨_, .throwRefHandlerCatchRef hexn' ht, hS, ⟨rfl, hfs⟩,
      CodeR.append (CodeR.ofVals hv) (.cons (.ref trivial) (.cons .plainS .nil))⟩
  | throwRefHandlerCatchAll =>
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    rw [CodeR.throwing_inv hb']
    exact ⟨_, .throwRefHandlerCatchAll, hS, hf, .cons .plainS .nil⟩
  | throwRefHandlerCatchAllRef =>
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    rw [CodeR.throwing_inv hb']
    exact ⟨_, .throwRefHandlerCatchAllRef, hS, hf, .cons (.ref trivial) (.cons .plainS .nil)⟩
  | throwRefHandlerNext hcm =>
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    rw [CodeR.throwing_inv hb']
    obtain ⟨rfl, hfs⟩ := hf
    exact ⟨_, .throwRefHandlerNext (fun h' => hcm ((catchMatches_congr hS.exns_eq).2 h')), hS,
      ⟨rfl, hfs⟩, .cons (.handler (CodeR.throwing _)) .nil⟩
  | tryTable hbt hm =>
    obtain ⟨rfl, rfl⟩ := ARel.plain_other rfl rfl he
    obtain ⟨rfl, hfs⟩ := hf
    exact ⟨_, .tryTable hbt hm, hS, ⟨rfl, hfs⟩,
      .cons (.handler (.cons (.labelS (CodeR.append (CodeR.ofVals hargs)
        (CodeR.expression_same _))) .nil)) .nil⟩
  | handlerVals hb =>
    subst hb
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    obtain ⟨rfl, hvs⟩ := CodeR.vals_inv hb'
    exact ⟨_, .handlerVals, hS, hf, CodeR.ofVals hvs⟩
  | trapLabel =>
    obtain ⟨cont', b', rfl, -, hb'⟩ := ARel.label_inv he
    rw [CodeR.trap_inv hb']
    exact ⟨_, .trapLabel, hS, hf, CodeR.trap⟩
  | trapHandler =>
    obtain ⟨rfl, b', rfl, hb'⟩ := ARel.handler_inv he
    rw [CodeR.trap_inv hb']
    exact ⟨_, .trapHandler, hS, hf, CodeR.trap⟩
  | trapFrame =>
    obtain ⟨m', fr', b', rfl, hfr, hb'⟩ := ARel.frame_inv he
    rw [CodeR.trap_inv hb']
    exact ⟨_, .trapFrame, hS, hf, CodeR.trap⟩

/-- **The call of a related function address.** -/
theorem head_sim_pair {X : SimCtx} (hX : X.WF) {m : Mode} {S T : Store H} {f f' : Frame}
    {vs : List Val} {a b : Nat} {d : DefType} {c₀ : Config H}
    (h : Head P S f (vs ++ [.ref (.func a)]) (.callRefType d) c₀) (hvs : ∀ v ∈ vs, valF X.n0 v)
    (hab : X.F a b) (hS : StoreRel X S T) (hf : FrameRel X m f f') :
    ∃ c₀', Step P noHost ⟨T, f', vals vs ++ [.ref (.func b), .callRefType d]⟩ c₀' ∧
      ConfRel X m c₀ c₀' := by
  generalize hA : vs ++ [Val.ref (.func a)] = A at h
  generalize hE : Admin.callRefType d = E at h
  cases h with
  | parametric hp =>
    have := (famOf_of_shape (ParametricStep.shape hp)).2
    rw [← hE] at this; cases this
  | numeric hp =>
    have := (famOf_of_shape (NumericStep.shape hp)).2
    rw [← hE] at this; cases this
  | vector hp =>
    have := (famOf_of_shape (VectorStep.shape hp)).2
    rw [← hE] at this; cases this
  | «variable» hp =>
    have := (famOf_of_shape (VariableStep.shape hp)).2
    rw [← hE] at this; cases this
  | table hp =>
    have := (famOf_of_shape (TableStep.shape hp)).2
    rw [← hE] at this; cases this
  | memory hp =>
    have := (famOf_of_shape (MemoryStep.shape hp)).2
    rw [← hE] at this; cases this
  | reference hp =>
    have := (famOf_of_shape (RefStep.shape hp)).2
    rw [← hE] at this; cases this
  | aggregate hp =>
    have := (famOf_of_shape (AggregateStep.shape hp)).2
    rw [← hE] at this; cases this
  | callRefNull hc =>
    have := congrArg List.getLast? hA
    simp at this
  | @callRefFunc _ c _ vs₂ a₂ fi ps rs code ha hc hfi hexp hn hcode =>
    subst hE
    rw [ha] at hA
    obtain ⟨rfl, h2⟩ := append_singleton_inj.1 hA
    have ea : a = a₂ := by cases h2; rfl
    subst a₂
    rcases hS.fpair a b hab with ⟨ha', rfl⟩ |
        ⟨-, -, fA, fB, cA, cB, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    · have hm : modF X.n0 X.g0 fi.module := hS.fgn.funcs _ ha' fi hfi _ hcode
      exact ⟨_, .callRefFunc hc (hS.func_lo ha' hfi) hexp hn hcode, hS, hf,
        .cons (.frameS (frameS_forCall hm hvs) (.cons (.labelS (CodeR.expression_same _)) .nil)) .nil⟩
    · rw [hfi] at h1
      cases h1
      rw [h6] at hcode
      cases hcode
      refine ⟨_, .callRefFunc hc h2 (h3 ▸ hexp) hn h7, hS, hf, .cons (.frameO ?_ ?_) .nil⟩
      · refine ⟨by simp [Frame.forCall, h4], by simp [Frame.forCall, h5], ?_, localsF_forCall hvs⟩
        simp only [Frame.forCall, h4, h5, h8, hX.types]
      · exact .cons (.labelO .nil (IRels.expression h9)) .nil
  | _ => cases hE

end Silmaril.Wasm.Binaryen.RUMESim
