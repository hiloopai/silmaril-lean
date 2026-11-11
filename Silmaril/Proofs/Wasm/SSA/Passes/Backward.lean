module

public import Silmaril.Proofs.Wasm.SSA.Passes.Regions

/-!
# Completeness of the passes

The converse of `Regions`: every evaluation of a simplified region is an
evaluation of the original (`simpR_complete`, under the facts and the types),
and the same for dead-binding elimination (`dce_complete`). The typing guard of
the algebraic rules (`atomTy`) supplies the operand values the original needs,
and `dce` only removes bindings of total terms (`Tm.total`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Passes

open Silmaril.Wasm (IntType IntBinOp IntRelOp Signedness)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend Env)
open Silmaril.DeBruijn (lift liftN)

/-! ## Types -/

theorem type_ofInt (t : IntType) (x : BitVec t.width) : (WVal.ofInt t x).type = t := by
  cases t <;> rfl

theorem asInt_of_type {w : WVal} {t : IntType} (h : w.type = t) : ∃ x, w.asInt t = some x := by
  subst h; cases w <;> exact ⟨_, rfl⟩

/-- A conversion that does not trap returns the target constructor. -/
private theorem convert_ok_inv {ε : Type} {n : Nat} {e : Except ε (BitVec n)}
    {mk : BitVec n → WVal} {w : WVal}
    (h : (match e with | .ok y => some (mk y) | .error _ => none) = some w) : ∃ y, w = mk y := by
  cases e with
  | ok y => exact ⟨y, (Option.some.inj h).symm⟩
  | error _ => cases h

/-- The result of a unary operator has its static type. -/
private theorem un_staticTy_sound {o : UnOp} {a w : WVal} {ty : IntType}
    (he : o.eval a = some w) (hs : (Op.un o).staticTy = some ty) : w.type = ty := by
  match o, a with
  | .int t op, a =>
      have hty : t = ty := Option.some.inj hs
      obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.mp he
      rw [← hx, ← hty]
      exact type_ofInt _ _
  | .test t, a =>
      have hty : IntType.i32 = ty := Option.some.inj hs
      obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.mp he
      rw [← hx, ← hty]
      rfl
  | .wrap, .i64 x =>
      have hty : IntType.i32 = ty := Option.some.inj hs
      obtain ⟨y, hy⟩ : ∃ y, w = .i32 y :=
        convert_ok_inv (e := Silmaril.Wasm.Numerics.convert .wrap x) he
      rw [hy, ← hty]
      rfl
  | .extend .signed, .i32 x =>
      have hty : IntType.i64 = ty := Option.some.inj hs
      obtain ⟨y, hy⟩ : ∃ y, w = .i64 y :=
        convert_ok_inv (e := Silmaril.Wasm.Numerics.convert (.extend .signed) x) he
      rw [hy, ← hty]
      rfl
  | .extend .unsigned, .i32 x =>
      have hty : IntType.i64 = ty := Option.some.inj hs
      obtain ⟨y, hy⟩ : ∃ y, w = .i64 y :=
        convert_ok_inv (e := Silmaril.Wasm.Numerics.convert (.extend .unsigned) x) he
      rw [hy, ← hty]
      rfl
  | .wrap, .i32 _ | .extend _, .i64 _ => exact absurd he (by simp [UnOp.eval])

/-- The result of a binary operator has its static type. -/
private theorem bin_staticTy_sound {o : BinOp} {a b w : WVal} {ty : IntType}
    (he : o.eval a b = some (.val w)) (hs : (Op.bin o).staticTy = some ty) : w.type = ty := by
  match o with
  | .int t op =>
      have hty : t = ty := Option.some.inj hs
      obtain ⟨_, _, z, _, _, _, hw⟩ := binInt_inv he
      rw [hw, ← hty]
      exact type_ofInt _ _
  | .rel t op =>
      have hty : IntType.i32 = ty := Option.some.inj hs
      have hw : ∃ c, w = .i32 c := by
        simp only [BinOp.eval] at he
        split at he
        · exact ⟨_, (Res.val.inj (Option.some.inj he)).symm⟩
        · cases he
      obtain ⟨c, hc⟩ := hw
      rw [hc, ← hty]
      rfl

theorem staticTy_sound {o : Op} {ws : List WVal} {w : WVal} {ty : IntType}
    (he : o.eval ws = some (.val w)) (hs : o.staticTy = some ty) : w.type = ty := by
  match o, ws with
  | .const c, [] =>
      have hc : c = w := Res.val.inj (Option.some.inj he)
      have hty : c.type = ty := Option.some.inj hs
      exact hc ▸ hty
  | .un o, [a] =>
      have ha : o.eval a = some w := by simpa [Op.eval] using he
      exact un_staticTy_sound ha hs
  | .bin o, [a, b] => exact bin_staticTy_sound he hs
  | .select, _ => exact absurd hs (by simp [Op.staticTy])
  | .const _, _ :: _ | .un _, [] | .un _, _ :: _ :: _ | .bin _, [] | .bin _, [_]
  | .bin _, _ :: _ :: _ :: _ => exact absurd he (by simp [Op.eval])

theorem stTy_sound {T : Tys} {env : Env WVal} (hT : TysOK T env) {t : Tm Prim} {v : SVal}
    {ty : IntType} (h : Semantics.Tm.Eval instr env t () v ()) (hs : stTy T t = some ty) :
    ∃ w, v = .atom w ∧ w.type = ty := by
  match t, h with
  | .var i, .var => exact hT i ty hs
  | .op (.op o) a, .op _ hrun =>
      obtain ⟨ws, w, -, hev, rfl⟩ := run_op_inv hrun
      exact ⟨w, rfl, staticTy_sound hev hs⟩
  | .op (.opT _) _, _ | .op .truthy _, _ | .unit, _ | .pair _ _, _ | .let₁ _ _, _
  | .let₂ _ _, _ | .inl _, _ | .inr _, _ | .case _ _ _, _ => simp [stTy] at hs

theorem atomTy_eval {T : Tys} {env : Env WVal} (hT : TysOK T env) {x : Tm Prim} {ty : IntType}
    (hs : atomTy T x = some ty) : ∃ w, Semantics.Tm.Eval instr env x () (.atom w) () ∧ w.type = ty := by
  unfold atomTy at hs
  split at hs
  · rename_i i
    obtain ⟨w, hw, hty⟩ := hT i ty hs
    exact ⟨w, .var_of_eq hw, hty⟩
  · rename_i w
    simp only [Option.some.injEq] at hs
    exact ⟨w, eval_constTm env w, hs⟩
  · cases hs

theorem _root_.Silmaril.Wasm.SSA.TysOK.push {T : Tys} {env : Env WVal} (hT : TysOK T env) (v : SVal) (ty : Option IntType)
    (h : ∀ t, ty = some t → ∃ w, v = .atom w ∧ w.type = t) : TysOK (ty :: T) (extend env v) := by
  intro i t ht
  cases i with
  | zero => simp only [Tys.get, List.getElem?_cons_zero, Option.join_some] at ht; exact h t ht
  | succ i => simp only [Tys.get, List.getElem?_cons_succ] at ht; exact hT i t ht

theorem _root_.Silmaril.Wasm.SSA.TysOK.none {T : Tys} {env : Env WVal} (hT : TysOK T env) (v : SVal) :
    TysOK (Option.none :: T) (extend env v) :=
  hT.push v Option.none fun _ h => by cases h

theorem _root_.Silmaril.Wasm.SSA.TysOK.stTy {T : Tys} {env : Env WVal} (hT : TysOK T env) {t : Tm Prim} {v : SVal}
    (h : Semantics.Tm.Eval instr env t () v ()) : TysOK (stTy T t :: T) (extend env v) :=
  hT.push v _ fun _ hs => stTy_sound hT h hs

theorem tysOK_params {params : List IntType} {args : List WVal} (h : args.map WVal.type = params) :
    TysOK (params.reverse.map some) (argEnv args) := by
  intro i t ht
  subst h
  simp only [Tys.get, ← List.map_reverse, List.getElem?_map] at ht
  cases ha : args.reverse[i]? with
  | none => simp [ha] at ht
  | some a =>
      simp [ha] at ht
      exact ⟨a, by simp [argEnv, ha], ht⟩

/-! ## Terms -/

theorem eval_tmTuple_consts : ∀ {ts : List (Tm Prim)} {ws : List WVal} (env : Env WVal),
    ts.mapM constOf? = some ws → Semantics.Tm.Eval instr env (tmTuple ts) () (encodeList ws) ()
  | [], ws, env, h => by simp at h; subst h; exact .unit
  | t :: ts, ws, env, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨w, h1, ws', h2, rfl⟩ := h
      rw [constOf?_eq h1]
      exact .pair (eval_constTm env w) (eval_tmTuple_consts env h2)

theorem eval_consts_of {env : Env WVal} {a : Tm Prim} {ws : List WVal}
    (hc : ((tmArgs? a).bind fun ts => ts.mapM constOf?) = some ws) :
    Semantics.Tm.Eval instr env a () (encodeList ws) () := by
  obtain ⟨ts, hts, hmap⟩ := Option.bind_eq_some_iff.mp hc
  rw [tmArgs?_eq hts]
  exact eval_tmTuple_consts env hmap

theorem algBin_total {t : IntType} {op : IntBinOp} {x y r : Tm Prim} (h : algBin t op x y = some r)
    {ax ay : WVal} (hx : ax.type = t) (hy : ay.type = t) :
    ∃ w, BinOp.eval (.int t op) ax ay = some (.val w) := by
  obtain ⟨bx, hbx⟩ := asInt_of_type hx
  obtain ⟨b2, hby⟩ := asInt_of_type hy
  suffices ∃ z, Silmaril.Wasm.Numerics.intBinOp t op bx b2 = .ok z by
    obtain ⟨z, hz⟩ := this
    exact ⟨WVal.ofInt t z, by simp [BinOp.eval, hbx, hby, hz]⟩
  cases op <;> (try cases ‹Signedness›) <;> first
    | exact ⟨_, rfl⟩
    | simp [algBin] at h

theorem algRel_total {t : IntType} {op : IntRelOp} {ax ay : WVal} (hx : ax.type = t)
    (hy : ay.type = t) : ∃ w, BinOp.eval (.rel t op) ax ay = some (.val w) := by
  obtain ⟨bx, hbx⟩ := asInt_of_type hx
  obtain ⟨b2, hby⟩ := asInt_of_type hy
  simp [BinOp.eval, hbx, hby]

theorem orElse_getD_cases {α : Type} {P : α → Prop} {G : Prop} (x y : Option α) (d : α)
    (hx : ∀ r, x = some r → P r → G) (hy : x = none → ∀ r, y = some r → P r → G) (hd : P d → G)
    (h : P ((x.orElse fun _ => y).getD d)) : G := by
  cases ex : x with
  | some r => rw [ex] at h; exact hx r ex h
  | none =>
    rw [ex] at h
    cases ey : y with
    | some r => rw [ey] at h; exact hy ex r ey h
    | none => rw [ey] at h; exact hd h

theorem run_op_val {o : Op} {ws : List WVal} {w : WVal} (h : o.eval ws = some (.val w)) :
    Prim.run (.op o) (encodeList ws) = some (.atom w) := by
  simp [Prim.run, decodeList_encodeList, h]

private theorem run_opT_val {o : Op} {ws : List WVal} {w : WVal} (h : o.eval ws = some (.val w)) :
    Prim.run (.opT o) (encodeList ws) = some (.inl (.atom w)) := by
  simp [Prim.run, decodeList_encodeList, h]

private theorem run_opT_trap {o : Op} {ws : List WVal} (h : o.eval ws = some .trap) :
    Prim.run (.opT o) (encodeList ws) = some (.inr .unit) := by
  simp [Prim.run, decodeList_encodeList, h]

private theorem run_opT_of_op {o : Op} {va u : SVal} (h : Prim.run (.op o) va = some u) :
    Prim.run (.opT o) va = some (.inl u) := by
  obtain ⟨ws, w, hdec, hev, rfl⟩ := run_op_inv h
  simp [Prim.run, hdec, hev]

/-- A binary operator applied to a tuple of two operands that evaluate to atoms. -/
private theorem eval_op2 {env : Env WVal} {o : BinOp} {a x y : Tm Prim} {ax ay w : WVal}
    (hxy : tmArgs? a = some [x, y]) (hx : Semantics.Tm.Eval instr env x () (.atom ax) ())
    (hy : Semantics.Tm.Eval instr env y () (.atom ay) ()) (hw : o.eval ax ay = some (.val w)) :
    Semantics.Tm.Eval instr env (.op (.op (.bin o)) a) () (.atom w) () := by
  rw [tmArgs?_eq hxy]
  exact .op (va := encodeList [ax, ay]) (.pair hx (.pair hy .unit)) (run_op_val hw)

/-- Operands typed by `atomTy` evaluate to atoms of that type. -/
private theorem atomTy_eval₂ {T : Tys} {env : Env WVal} (hT : TysOK T env) {x y : Tm Prim}
    {t : IntType} (hty : atomTy T x = some t ∧ atomTy T y = some t) :
    ∃ ax ay, Semantics.Tm.Eval instr env x () (.atom ax) () ∧
      Semantics.Tm.Eval instr env y () (.atom ay) () ∧ ax.type = t ∧ ay.type = t := by
  obtain ⟨ax, hx, htx⟩ := atomTy_eval hT hty.1
  obtain ⟨ay, hy, hty'⟩ := atomTy_eval hT hty.2
  exact ⟨ax, ay, hx, hy, htx, hty'⟩

/-- The folding branch of `rewriteOp` on `.op o` only returns the operator's value. -/
private theorem rewriteOp_op_fold_complete {cfg : SimpCfg} {env : Env WVal} {o : Op}
    {a : Tm Prim} {v : SVal} (r : Tm Prim)
    (hr : (if cfg.fold then
          match (tmArgs? a).bind fun ts => ts.mapM constOf? with
          | some ws =>
              match o.eval ws with
              | some (.val w) => some (constTm w)
              | _ => none
          | none => none
        else none) = some r) :
    Semantics.Tm.Eval instr env r () v () → Semantics.Tm.Eval instr env (.op (.op o) a) () v () := by
  intro hrv
  split at hr
  · split at hr
    next ws hws =>
      split at hr
      next w hw =>
        have hv : v = .atom w := eval_const_inv rfl (Option.some.inj hr ▸ hrv)
        exact hv ▸ .op (eval_consts_of hws) (run_op_val hw)
      next => cases hr
    next => cases hr
  · cases hr

/-- The algebraic branch of `rewriteOp` on `.op o`: typed operands make the
original operator evaluate, to the same value by `algBin_sound`/`algRel_sound`. -/
private theorem rewriteOp_op_alg_complete {cfg : SimpCfg} {T : Tys} {env : Env WVal}
    (hT : TysOK T env) {o : Op} {a : Tm Prim} {v : SVal} (r : Tm Prim)
    (hr : (if cfg.alg then
          match o, tmArgs? a with
          | .bin (.int t op), some [x, y] =>
              if atomTy T x = some t ∧ atomTy T y = some t then algBin t op x y else none
          | .bin (.rel t op), some [x, y] =>
              if atomTy T x = some t ∧ atomTy T y = some t then algRel op x y else none
          | _, _ => none
        else none) = some r) :
    Semantics.Tm.Eval instr env r () v () → Semantics.Tm.Eval instr env (.op (.op o) a) () v () := by
  intro hrv
  split at hr
  · split at hr
    next t op x y hxy =>
      obtain ⟨hty, hr'⟩ := Option.ite_none_right_eq_some.mp hr
      obtain ⟨ax, ay, hx, hy, htx, hty'⟩ := atomTy_eval₂ hT hty
      obtain ⟨w, hw⟩ := algBin_total hr' htx hty'
      have hv : v = .atom w := tm_det hrv (algBin_sound hr' hx hy hw)
      exact hv ▸ eval_op2 hxy hx hy hw
    next t op x y hxy =>
      obtain ⟨hty, hr'⟩ := Option.ite_none_right_eq_some.mp hr
      obtain ⟨ax, ay, hx, hy, htx, hty'⟩ := atomTy_eval₂ hT hty
      obtain ⟨w, hw⟩ := algRel_total (op := op) htx hty'
      have hv : v = .atom w := tm_det hrv (algRel_sound hr' hx hy hw)
      exact hv ▸ eval_op2 hxy hx hy hw
    next => cases hr
  · cases hr

/-- The folding branch of `rewriteOp` on `.opT o` only returns the operator's
value or trap. -/
private theorem rewriteOp_opT_fold_complete {cfg : SimpCfg} {env : Env WVal} {o : Op}
    {a : Tm Prim} {v : SVal} (r : Tm Prim)
    (hr : (if cfg.fold then
          match (tmArgs? a).bind fun ts => ts.mapM constOf? with
          | some ws =>
              match o.eval ws with
              | some (.val w) => some (.inl (constTm w))
              | some .trap => some (.inr .unit)
              | none => none
          | none => none
        else none) = some r) :
    Semantics.Tm.Eval instr env r () v () →
      Semantics.Tm.Eval instr env (.op (.opT o) a) () v () := by
  intro hrv
  split at hr
  · split at hr
    next ws hws =>
      split at hr
      next w hw =>
        cases Option.some.inj hr ▸ hrv with
        | inl hc => exact eval_const_inv rfl hc ▸ .op (eval_consts_of hws) (run_opT_val hw)
      next hw =>
        cases Option.some.inj hr ▸ hrv with
        | inr hc => cases hc; exact .op (eval_consts_of hws) (run_opT_trap hw)
      next => cases hr
    next => cases hr
  · cases hr

/-- The safe-division branch of `rewriteOp` on `.opT o` only wraps the
non-trapping operator. -/
private theorem rewriteOp_opT_safe_complete {cfg : SimpCfg} {env : Env WVal} {o : Op}
    {a : Tm Prim} {v : SVal} (r : Tm Prim)
    (hr : (if cfg.alg then
          match o, tmArgs? a with
          | .bin (.int t op), some [_, y] =>
              match constOf? y with
              | some d => if safeDivisor t op d then some (.inl (.op (.op o) a)) else none
              | none => none
          | _, _ => none
        else none) = some r) :
    Semantics.Tm.Eval instr env r () v () →
      Semantics.Tm.Eval instr env (.op (.opT o) a) () v () := by
  intro hrv
  split at hr
  · split at hr
    · split at hr
      next =>
        obtain ⟨-, hr'⟩ := Option.ite_none_right_eq_some.mp hr
        cases Option.some.inj hr' ▸ hrv with
        | inl hop =>
          cases hop with
          | op ha hrun => exact .op ha (run_opT_of_op hrun)
      next => cases hr
    · cases hr
  · cases hr

/-- A `truthy` of a constant, decided when the constant is an `i32`. -/
private theorem truthy_const_complete {env : Env WVal} {w : WVal} {a : Tm Prim} {v : SVal}
    (ha : a = constTm w)
    (h : Semantics.Tm.Eval instr env
      (match w.truthy with
        | some true => .inl .unit
        | some false => .inr .unit
        | none => (.op .truthy a : Tm Prim)) () v ()) :
    Semantics.Tm.Eval instr env (.op .truthy a) () v () := by
  split at h
  next ht =>
    cases h with
    | inl hu =>
      cases hu
      exact ha ▸ .op (eval_constTm env w)
        (show Prim.run .truthy (.atom w) = some (.inl .unit) by simp [Prim.run, ht])
  next ht =>
    cases h with
    | inr hu =>
      cases hu
      exact ha ▸ .op (eval_constTm env w)
        (show Prim.run .truthy (.atom w) = some (.inr .unit) by simp [Prim.run, ht])
  next => exact h

/-- `rewriteOp` on `.truthy` only decides constants. -/
private theorem rewriteOp_truthy_complete {cfg : SimpCfg} {T : Tys} {env : Env WVal}
    {a : Tm Prim} {v : SVal} (h : Semantics.Tm.Eval instr env (rewriteOp cfg T .truthy a) () v ()) :
    Semantics.Tm.Eval instr env (.op .truthy a) () v () := by
  simp only [rewriteOp] at h
  split at h
  · split at h
    next w hw => exact truthy_const_complete (constOf?_eq hw) h
    next => exact h
  · exact h

theorem rewriteOp_complete (cfg : SimpCfg) {T : Tys} {env : Env WVal} (hT : TysOK T env)
    {p : Prim} {a : Tm Prim} {v : SVal}
    (h : Semantics.Tm.Eval instr env (rewriteOp cfg T p a) () v ()) :
    Semantics.Tm.Eval instr env (.op p a) () v () := by
  cases p with
  | op o =>
    exact orElse_getD_cases (P := fun r => Semantics.Tm.Eval instr env r () v ()) _ _ _
      rewriteOp_op_fold_complete (fun _ => rewriteOp_op_alg_complete hT) id h
  | opT o =>
    exact orElse_getD_cases (P := fun r => Semantics.Tm.Eval instr env r () v ()) _ _ _
      rewriteOp_opT_fold_complete (fun _ => rewriteOp_opT_safe_complete) id h
  | truthy => exact rewriteOp_truthy_complete h

theorem resolveVar_complete (cfg : SimpCfg) {F : Facts} {env : Env WVal} (hF : FactsOK F env)
    {i : Nat} {v : SVal} (h : Semantics.Tm.Eval instr env (resolveVar cfg F i) () v ()) :
    Semantics.Tm.Eval instr env (.var i) () v () := by
  rw [tm_det h (resolveVar_sound cfg hF i)]
  exact .var

theorem simpTm_complete (cfg : SimpCfg) {F : Facts} {T : Tys} {env : Env WVal}
    (hF : FactsOK F env) (hT : TysOK T env) :
    ∀ (t : Tm Prim) {v : SVal}, Semantics.Tm.Eval instr env (simpTm cfg F T t) () v () →
      Semantics.Tm.Eval instr env t () v ()
  | .var i, v, h => resolveVar_complete cfg hF h
  | .op p a, v, h => by
      have h' := rewriteOp_complete cfg hT h
      cases h' with
      | op ha hrun =>
        cases ‹Unit›
        exact .op (simpTm_complete cfg hF hT a ha) hrun
  | .pair a b, v, h => by
      cases h with
      | pair ha hb =>
        cases ‹Unit›
        exact .pair (simpTm_complete cfg hF hT a ha) (simpTm_complete cfg hF hT b hb)
  | .unit, _, h | .let₁ _ _, _, h | .let₂ _ _, _, h | .inl _, _, h | .inr _, _, h
  | .case _ _ _, _, h | .abort _, _, h => h

theorem cseTm_complete (cfg : SimpCfg) {F : Facts} {env : Env WVal} (hF : FactsOK F env)
    {a : Tm Prim} {v : SVal} (h : Semantics.Tm.Eval instr env (cseTm cfg F a) () v ()) :
    Semantics.Tm.Eval instr env a () v () := by
  unfold cseTm at h
  split at h
  · split at h
    · split at h
      · rename_i p hp
        obtain ⟨t, ht, hre⟩ := cseFind_spec hp
        have h1 := (hF p t ht).rename (env' := env) (ρ := (· + (p + 1))) (fun _ => rfl)
        rw [hre] at h1
        cases h
        exact h1
      · exact h
    · exact h
  · exact h

/-! ## Regions -/

/-- CFG executions over blocks that are each complete for the original ones. -/
theorem follow_complete {env : Env WVal} {n : Nat} {G : Fin n → Region Prim} {first : Nat}
    {init : SVal} {s s' : Unit} {l : Nat} {v : SVal}
    (h : Semantics.Region.Follow instr env G first init s l v s') :
    ∀ (bs : Fin n → Region Prim),
      (∀ i cur l v, Semantics.Region.Eval instr (extend env cur) (G i) () l v () →
        Semantics.Region.Eval instr (extend env cur) (bs i) () l v ()) →
      Semantics.Region.Follow instr env bs first init s l v s' := by
  exact Semantics.Region.Follow.rec (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun env n blocks first init s l v s' _ =>
      ∀ (bs : Fin n → Region Prim),
        (∀ i cur l v, Semantics.Region.Eval instr (extend env cur) (blocks i) () l v () →
          Semantics.Region.Eval instr (extend env cur) (bs i) () l v ()) →
        Semantics.Region.Follow instr env bs first init s l v s')
    (by intros; trivial) (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial)
    (fun outside _ _ => .exit outside)
    (fun inside he _ _ ih bs hG => by
      cases ‹Unit›; cases ‹Unit›; cases ‹Unit›
      exact .step inside (hG _ _ _ _ he) (ih bs hG))
    h

/-- `simpR_complete` for one region: what the induction hypotheses say. -/
private abbrev SimpRComplete (cfg : SimpCfg) (r : Region Prim) : Prop :=
  ∀ {F : Facts} {T : Tys} {env : Env WVal} {l : Nat} {v : SVal}, FactsOK F env → TysOK T env →
    Semantics.Region.Eval instr env (simpR cfg F T r) () l v () →
    Semantics.Region.Eval instr env r () l v ()

/-- A `case` whose scrutinee simplified to `inl t` ran its left branch. -/
private theorem simpR_case_inl_complete (cfg : SimpCfg) {F : Facts} {T : Tys} {env : Env WVal}
    {a t : Tm Prim} {l : Region Prim} (r : Region Prim) {lab : Nat} {v : SVal}
    (hF : FactsOK F env) (hT : TysOK T env) (heq : simpTm cfg F T a = .inl t)
    (ihl : SimpRComplete cfg l)
    (h : Semantics.Region.Eval instr env
      (.let₁ t (simpR cfg (some t :: F) (stTy T t :: T) l)) () lab v ()) :
    Semantics.Region.Eval instr env (.case a l r) () lab v () := by
  cases h with
  | let₁ ht hb =>
    cases ‹Unit›
    have ha : Semantics.Tm.Eval instr env (simpTm cfg F T a) () (.inl _) () := heq ▸ Semantics.Tm.Eval.inl ht
    exact .case_inl (simpTm_complete cfg hF hT a ha)
      (ihl (hF.push _ _ fun _ e => Option.some.inj e ▸ ht) (hT.stTy ht) hb)

/-- A `case` whose scrutinee simplified to `inr t` ran its right branch. -/
private theorem simpR_case_inr_complete (cfg : SimpCfg) {F : Facts} {T : Tys} {env : Env WVal}
    {a t : Tm Prim} (l : Region Prim) {r : Region Prim} {lab : Nat} {v : SVal}
    (hF : FactsOK F env) (hT : TysOK T env) (heq : simpTm cfg F T a = .inr t)
    (ihr : SimpRComplete cfg r)
    (h : Semantics.Region.Eval instr env
      (.let₁ t (simpR cfg (some t :: F) (stTy T t :: T) r)) () lab v ()) :
    Semantics.Region.Eval instr env (.case a l r) () lab v () := by
  cases h with
  | let₁ ht hb =>
    cases ‹Unit›
    have ha : Semantics.Tm.Eval instr env (simpTm cfg F T a) () (.inr _) () := heq ▸ Semantics.Tm.Eval.inr ht
    exact .case_inr (simpTm_complete cfg hF hT a ha)
      (ihr (hF.push _ _ fun _ e => Option.some.inj e ▸ ht) (hT.stTy ht) hb)

/-- `simpR` on a `case`: either a branch was selected statically, or the
`case` stays and runs one of its simplified branches. -/
private theorem simpR_case_complete (cfg : SimpCfg) {a : Tm Prim} {l r : Region Prim}
    (ihl : SimpRComplete cfg l) (ihr : SimpRComplete cfg r) : SimpRComplete cfg (.case a l r) := by
  intro F T env lab v hF hT h
  simp only [simpR] at h
  split at h
  next t heq => exact simpR_case_inl_complete cfg r hF hT heq ihl h
  next t heq => exact simpR_case_inr_complete cfg l hF hT heq ihr h
  next =>
    cases h with
    | case_inl ha hb =>
      cases ‹Unit›
      exact .case_inl (simpTm_complete cfg hF hT a ha) (ihl (hF.none _) (hT.none _) hb)
    | case_inr ha hb =>
      cases ‹Unit›
      exact .case_inr (simpTm_complete cfg hF hT a ha) (ihr (hF.none _) (hT.none _) hb)

theorem simpR_complete (cfg : SimpCfg) (r : Region Prim) :
    ∀ {F : Facts} {T : Tys} {env : Env WVal} {l : Nat} {v : SVal}, FactsOK F env → TysOK T env →
      Semantics.Region.Eval instr env (simpR cfg F T r) () l v () →
      Semantics.Region.Eval instr env r () l v () := by
  induction r with
  | br l a =>
      intro F T env l' v hF hT h
      cases h with
      | br ha => exact .br (simpTm_complete cfg hF hT a ha)
  | let₁ a b ih =>
      intro F T env l v hF hT h
      cases h with
      | let₁ ha hb =>
        cases ‹Unit›
        exact .let₁ (simpTm_complete cfg hF hT a (cseTm_complete cfg hF ha))
          (ih (hF.push _ _ fun t ht => by cases ht; exact ha) (hT.stTy ha) hb)
  | let₂ a b ih =>
      intro F T env l v hF hT h
      cases h with
      | let₂ ha hb =>
        cases ‹Unit›
        exact .let₂ (simpTm_complete cfg hF hT a ha) (ih ((hF.none _).none _) ((hT.none _).none _) hb)
  | case a l r ihl ihr => exact simpR_case_complete cfg ihl ihr
  | cfg e n bs ihe ihb =>
      intro F T env l v hF hT h
      cases h with
      | cfg he hf =>
        cases ‹Unit›
        exact .cfg (ihe hF hT he)
          (follow_complete hf bs fun i cur l v h => ihb i (hF.none cur) (hT.none cur) h)

/-! ## Dead bindings -/

theorem lift_fix {ρ : Nat → Nat} {P : Nat → Prop} (h : ∀ i, P (i + 1) → ρ i = i) :
    ∀ i, P i → lift ρ i = i
  | 0, _ => rfl
  | i + 1, hi => by show ρ i + 1 = i + 1; rw [h i hi]

theorem Tm.rename_fix : ∀ (a : Tm Prim) {ρ : Nat → Nat},
    (∀ i, Tm.mentions i a = true → ρ i = i) → a.rename ρ = a
  | .var j, ρ, h => by simp only [Tm.rename]; rw [h j (by simp [Tm.mentions])]
  | .op p a, ρ, h => by
      simp only [Tm.rename]
      rw [Tm.rename_fix a fun i hi => h i (by simpa [Tm.mentions] using hi)]
  | .let₁ a b, ρ, h => by
      simp only [Tm.rename]
      rw [Tm.rename_fix a fun i hi => h i (by simp [Tm.mentions, hi]),
        Tm.rename_fix b (lift_fix (P := fun i => Tm.mentions i b = true)
          fun i hi => h i (by simp [Tm.mentions, hi]))]
  | .pair a b, ρ, h => by
      simp only [Tm.rename]
      rw [Tm.rename_fix a fun i hi => h i (by simp [Tm.mentions, hi]),
        Tm.rename_fix b fun i hi => h i (by simp [Tm.mentions, hi])]
  | .unit, _, _ => rfl
  | .let₂ a b, ρ, h => by
      simp only [Tm.rename]
      show Tm.let₂ (a.rename ρ) (b.rename (lift (lift ρ))) = _
      rw [Tm.rename_fix a fun i hi => h i (by simp [Tm.mentions, hi]),
        Tm.rename_fix b (lift_fix (P := fun i => Tm.mentions i b = true)
          (lift_fix (P := fun i => Tm.mentions (i + 1) b = true)
            fun i hi => h i (by simp [Tm.mentions, hi])))]
  | .inl a, ρ, h => by
      simp only [Tm.rename]; rw [Tm.rename_fix a fun i hi => h i (by simpa [Tm.mentions] using hi)]
  | .inr a, ρ, h => by
      simp only [Tm.rename]; rw [Tm.rename_fix a fun i hi => h i (by simpa [Tm.mentions] using hi)]
  | .case a l r, ρ, h => by
      simp only [Tm.rename]
      rw [Tm.rename_fix a fun i hi => h i (by simp [Tm.mentions, hi]),
        Tm.rename_fix l (lift_fix (P := fun i => Tm.mentions i l = true)
          fun i hi => h i (by simp [Tm.mentions, hi])),
        Tm.rename_fix r (lift_fix (P := fun i => Tm.mentions i r = true)
          fun i hi => h i (by simp [Tm.mentions, hi]))]
  | .abort a, ρ, h => by
      simp only [Tm.rename]; rw [Tm.rename_fix a fun i hi => h i (by simpa [Tm.mentions] using hi)]

theorem Region.renameVars_fix (r : Region Prim) :
    ∀ {ρ : Nat → Nat}, (∀ i, Region.mentions i r = true → ρ i = i) → r.renameVars ρ = r := by
  induction r with
  | br l a =>
      intro ρ h; simp only [Region.renameVars]
      rw [Tm.rename_fix a fun i hi => h i (by simpa [Region.mentions] using hi)]
  | let₁ a b ih =>
      intro ρ h; simp only [Region.renameVars]
      rw [Tm.rename_fix a fun i hi => h i (by simp [Region.mentions, hi]),
        ih (lift_fix (P := fun i => Region.mentions i b = true)
          fun i hi => h i (by simp [Region.mentions, hi]))]
  | let₂ a b ih =>
      intro ρ h; simp only [Region.renameVars]
      show Region.let₂ (a.rename ρ) (b.renameVars (lift (lift ρ))) = _
      rw [Tm.rename_fix a fun i hi => h i (by simp [Region.mentions, hi]),
        ih (lift_fix (P := fun i => Region.mentions i b = true)
          (lift_fix (P := fun i => Region.mentions (i + 1) b = true)
            fun i hi => h i (by simp [Region.mentions, hi])))]
  | case a l r ihl ihr =>
      intro ρ h; simp only [Region.renameVars]
      rw [Tm.rename_fix a fun i hi => h i (by simp [Region.mentions, hi]),
        ihl (lift_fix (P := fun i => Region.mentions i l = true)
          fun i hi => h i (by simp [Region.mentions, hi])),
        ihr (lift_fix (P := fun i => Region.mentions i r = true)
          fun i hi => h i (by simp [Region.mentions, hi]))]
  | cfg e n bs ihe ihb =>
      intro ρ h; simp only [Region.renameVars]
      rw [ihe fun i hi => h i (by simp [Region.mentions, hi])]
      congr 1
      funext j
      refine ihb j (lift_fix (P := fun i => Region.mentions i (bs j) = true) fun i hi => h i ?_)
      simp only [Region.mentions, Bool.or_eq_true, List.any_eq_true]
      exact .inr ⟨j, List.mem_finRange j, hi⟩

theorem Tm.total_eval : ∀ {t : Tm Prim}, Tm.total t = true → ∀ env : Env WVal,
    ∃ v, Semantics.Tm.Eval instr env t () v ()
  | .var i, _, env => ⟨_, .var⟩
  | .unit, _, env => ⟨_, .unit⟩
  | .op (.op (.const w)) .unit, _, env => ⟨_, eval_constTm env w⟩
  | .pair a b, h, env => by
      simp only [Tm.total, Bool.and_eq_true] at h
      obtain ⟨va, ha⟩ := Tm.total_eval h.1 env
      obtain ⟨vb, hb⟩ := Tm.total_eval h.2 env
      exact ⟨_, .pair ha hb⟩
  | .inl a, h, env => by
      obtain ⟨va, ha⟩ := Tm.total_eval (t := a) h env; exact ⟨_, .inl ha⟩
  | .inr a, h, env => by
      obtain ⟨va, ha⟩ := Tm.total_eval (t := a) h env; exact ⟨_, .inr ha⟩

/-- Removing an unused binding: the body, shifted down, evaluates as before. -/
theorem eval_unshift {env : Env WVal} {b : Region Prim} {k : Nat} {l : Nat} {v : SVal}
    (env' : Env WVal) (hk : ∀ i, env' (i + k) = env i)
    (hm : ∀ i, Region.mentions i b = true → k ≤ i)
    (h : Semantics.Region.Eval instr env (b.renameVars (· - k)) () l v ()) :
    Semantics.Region.Eval instr env' b () l v () := by
  have h' := Region.Eval.rename_mentions h (env' := env') (ρ := (· + k)) fun i _ => hk i
  rwa [Region.renameVars_comp, Region.renameVars_fix b fun i hi => by
    have := hm i hi; simp only [Function.comp]; omega] at h'

/-- `dce_complete` for one region: what the induction hypotheses say. -/
private abbrev DceComplete (r : Region Prim) : Prop :=
  ∀ {env : Env WVal} {l : Nat} {v : SVal}, Semantics.Region.Eval instr env (dce r) () l v () →
    Semantics.Region.Eval instr env r () l v ()

/-- A kept `let₁` binding. -/
private theorem let₁_of_dce {a : Tm Prim} {b : Region Prim} (ih : DceComplete b) {env : Env WVal}
    {l : Nat} {v : SVal} (h : Semantics.Region.Eval instr env (.let₁ a (dce b)) () l v ()) :
    Semantics.Region.Eval instr env (.let₁ a b) () l v () := by
  cases h with
  | let₁ ha hb =>
    cases ‹Unit›
    exact .let₁ ha (ih hb)

/-- A kept `let₂` binding. -/
private theorem let₂_of_dce {a : Tm Prim} {b : Region Prim} (ih : DceComplete b) {env : Env WVal}
    {l : Nat} {v : SVal} (h : Semantics.Region.Eval instr env (.let₂ a (dce b)) () l v ()) :
    Semantics.Region.Eval instr env (.let₂ a b) () l v () := by
  cases h with
  | let₂ ha hb =>
    cases ‹Unit›
    exact .let₂ ha (ih hb)

/-- A dropped `let₁` of a total term: the term evaluates, and the body, which
does not mention it, ran one variable lower. -/
private theorem dce_drop₁_complete {a : Tm Prim} {b : Region Prim} (ih : DceComplete b)
    {env : Env WVal} {l : Nat} {v : SVal} (hm : ¬Region.mentions 0 (dce b) = true)
    (ht : Tm.total a = true)
    (h : Semantics.Region.Eval instr env ((dce b).renameVars (· - 1)) () l v ()) :
    Semantics.Region.Eval instr env (.let₁ a b) () l v () := by
  obtain ⟨va, ha⟩ := Tm.total_eval ht env
  have hk : ∀ i, Region.mentions i (dce b) = true → 1 ≤ i := fun i hi => by
    cases i with
    | zero => exact absurd hi hm
    | succ i => omega
  exact .let₁ ha (ih (eval_unshift (k := 1) _ (fun i => rfl) hk h))

/-- A dropped `let₂` of a pair of total terms. -/
private theorem dce_drop₂_complete {x y : Tm Prim} {b : Region Prim} (ih : DceComplete b)
    {env : Env WVal} {l : Nat} {v : SVal}
    (hm : ¬Region.mentions 0 (dce b) = true ∧ ¬Region.mentions 1 (dce b) = true)
    (ht : Tm.total x = true ∧ Tm.total y = true)
    (h : Semantics.Region.Eval instr env ((dce b).renameVars (· - 2)) () l v ()) :
    Semantics.Region.Eval instr env (.let₂ (.pair x y) b) () l v () := by
  obtain ⟨vx, hx⟩ := Tm.total_eval ht.1 env
  obtain ⟨vy, hy⟩ := Tm.total_eval ht.2 env
  have hk : ∀ i, Region.mentions i (dce b) = true → 2 ≤ i := fun i hi => by
    match i, hi with
    | 0, hi => exact absurd hi hm.1
    | 1, hi => exact absurd hi hm.2
    | i + 2, _ => omega
  exact .let₂ (.pair hx hy) (ih (eval_unshift (k := 2) _ (fun i => rfl) hk h))

/-- `dce` at a `let₁`: the binding is kept, or dropped as unused and total. -/
private theorem dce_let₁_complete {a : Tm Prim} {b : Region Prim} (ih : DceComplete b) :
    DceComplete (.let₁ a b) := by
  intro env l v h
  simp only [dce] at h
  split at h
  · exact let₁_of_dce ih h
  next hm =>
    split at h
    next ht => exact dce_drop₁_complete ih hm ht h
    next => exact let₁_of_dce ih h

/-- `dce` at a `let₂`: the binding is kept, or dropped as an unused pair of
total terms. -/
private theorem dce_let₂_complete {a : Tm Prim} {b : Region Prim} (ih : DceComplete b) :
    DceComplete (.let₂ a b) := by
  intro env l v h
  simp only [dce] at h
  split at h
  · exact let₂_of_dce ih h
  next hm =>
    have hm' : ¬Region.mentions 0 (dce b) = true ∧ ¬Region.mentions 1 (dce b) = true := by
      simpa only [Bool.or_eq_true, not_or] using hm
    split at h
    next x y =>
      split at h
      next ht => exact dce_drop₂_complete ih hm' (by simpa only [Bool.and_eq_true] using ht) h
      next => exact let₂_of_dce ih h
    next => exact let₂_of_dce ih h

theorem dce_complete (r : Region Prim) :
    ∀ {env : Env WVal} {l : Nat} {v : SVal}, Semantics.Region.Eval instr env (dce r) () l v () →
      Semantics.Region.Eval instr env r () l v () := by
  induction r with
  | br l a => intro env l' v h; exact h
  | let₁ a b ih => exact dce_let₁_complete ih
  | let₂ a b ih => exact dce_let₂_complete ih
  | case a l r ihl ihr =>
      intro env l' v h
      cases h with
      | case_inl ha hb => cases ‹Unit›; exact .case_inl ha (ihl hb)
      | case_inr ha hb => cases ‹Unit›; exact .case_inr ha (ihr hb)
  | cfg e n bs ihe ihb =>
      intro env l v h
      cases h with
      | cfg he hf =>
        cases ‹Unit›
        exact .cfg (ihe he) (follow_complete hf bs fun i cur l v h => ihb i h)

/-! ## Functions -/

theorem simp_complete (cfg : SimpCfg) {f : SFunc} {args : List WVal} {o : FOut}
    (h : (f.simp cfg).Run args o) : f.Run args o := by
  obtain ⟨hl, l, v, he, hd⟩ := h
  exact ⟨hl, l, v, simpR_complete cfg f.body (FactsOK.nil _) (tysOK_params hl) he, hd⟩

theorem dce_complete_run {f : SFunc} {args : List WVal} {o : FOut}
    (h : f.dce.Run args o) : f.Run args o := by
  obtain ⟨hl, l, v, he, hd⟩ := h
  exact ⟨hl, l, v, dce_complete f.body he, hd⟩

end Silmaril.Proofs.Wasm.SSA.Passes
