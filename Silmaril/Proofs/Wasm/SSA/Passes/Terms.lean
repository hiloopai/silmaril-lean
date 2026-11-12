module

public import Silmaril.Wasm.SSA.Passes.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-!
# Soundness of the term simplifier

Every evaluation of a term is an evaluation of its simplification
(`simpTm_sound`), for environments satisfying the facts (`FactsOK`); common
subexpression replacement is sound by determinism (`cseTm_sound`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Passes

open Silmaril.Wasm (IntType IntBinOp IntRelOp Signedness)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (extend Env InstrDeterministic)

/-! ## Basics -/

theorem instr_deterministic : InstrDeterministic instr := by
  intro f a s b s' c s'' h1 h2
  exact ⟨Option.some.inj (h1.symm.trans h2), Subsingleton.elim _ _⟩

theorem tm_det {env : Env WVal} {t : Tm Prim} {v₁ v₂ : SVal}
    (h₁ : Semantics.Tm.Eval instr env t () v₁ ()) (h₂ : Semantics.Tm.Eval instr env t () v₂ ()) :
    v₁ = v₂ :=
  (Semantics.Tm.Eval.deterministic instr_deterministic h₁ h₂).1

theorem eval_constTm (env : Env WVal) (w : WVal) :
    Semantics.Tm.Eval instr env (constTm w) () (.atom w) () :=
  .op .unit rfl

theorem constOf?_eq {t : Tm Prim} {w : WVal} (h : constOf? t = some w) : t = constTm w := by
  unfold constOf? at h
  split at h
  · cases h; rfl
  · cases h

theorem eval_const_inv {env : Env WVal} {t : Tm Prim} {w : WVal} {v : SVal}
    (hc : constOf? t = some w) (h : Semantics.Tm.Eval instr env t () v ()) : v = .atom w := by
  rw [constOf?_eq hc] at h
  exact tm_det h (eval_constTm env w)

theorem tmArgs?_eq : ∀ {a : Tm Prim} {ts : List (Tm Prim)}, tmArgs? a = some ts → a = tmTuple ts
  | .unit, ts, h => by simp [tmArgs?] at h; subst h; rfl
  | .pair x r, ts, h => by
      simp only [tmArgs?, Option.map_eq_some_iff] at h
      obtain ⟨ts', h', rfl⟩ := h
      rw [tmArgs?_eq h']; rfl
  | .var _, _, h | .op _ _, _, h | .let₁ _ _, _, h | .let₂ _ _, _, h | .inl _, _, h
  | .inr _, _, h | .case _ _ _, _, h | .abort _, _, h => by simp [tmArgs?] at h

theorem decodeList_eq : ∀ {v : SVal} {ws : List WVal}, decodeList v = some ws → v = encodeList ws
  | .unit, ws, h => by simp [decodeList] at h; subst h; rfl
  | .pair (.atom a) r, ws, h => by
      simp only [decodeList, Option.map_eq_some_iff] at h
      obtain ⟨ws', h', rfl⟩ := h
      rw [decodeList_eq h']; rfl
  | .atom _, _, h | .inl _, _, h | .inr _, _, h => by simp [decodeList] at h
  | .pair .unit _, _, h | .pair (.pair _ _) _, _, h | .pair (.inl _) _, _, h
  | .pair (.inr _) _, _, h => by simp [decodeList] at h

theorem decodeList_encodeList : ∀ ws : List WVal, decodeList (encodeList ws) = some ws
  | [] => rfl
  | w :: ws => by simp [encodeList, decodeList, decodeList_encodeList ws]

theorem encodeList_injective {ws ws' : List WVal} (h : encodeList ws = encodeList ws') : ws = ws' := by
  have := decodeList_encodeList ws
  rw [h, decodeList_encodeList] at this
  exact (Option.some.inj this).symm

/-- Constant arguments evaluate to their tuple. -/
theorem eval_consts : ∀ {ts : List (Tm Prim)} {ws : List WVal} {env : Env WVal} {va : SVal},
    ts.mapM constOf? = some ws → Semantics.Tm.Eval instr env (tmTuple ts) () va () →
    va = encodeList ws
  | [], ws, env, va, hw, h => by
      simp at hw; subst hw; cases h; rfl
  | t :: ts, ws, env, va, hw, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hw
      obtain ⟨w, hw1, ws', hw2, rfl⟩ := hw
      cases h with
      | pair h1 h2 =>
          rw [eval_const_inv hw1 h1, eval_consts hw2 h2]; rfl

/-- The run of a non-trapping primitive. -/
theorem run_op_inv {o : Op} {va v : SVal} (h : Prim.run (.op o) va = some v) :
    ∃ ws w, decodeList va = some ws ∧ o.eval ws = some (.val w) ∧ v = .atom w := by
  simp only [Prim.run] at h
  split at h
  · rename_i w hw
    cases h
    simp only [Option.bind_eq_some_iff] at hw
    obtain ⟨ws, h1, h2⟩ := hw
    exact ⟨ws, w, h1, h2, rfl⟩
  · cases h

theorem run_opT_inv {o : Op} {va v : SVal} (h : Prim.run (.opT o) va = some v) :
    ∃ ws, decodeList va = some ws ∧
      ((∃ w, o.eval ws = some (.val w) ∧ v = .inl (.atom w)) ∨
        (o.eval ws = some .trap ∧ v = .inr .unit)) := by
  simp only [Prim.run] at h
  split at h
  · rename_i w hw
    cases h
    simp only [Option.bind_eq_some_iff] at hw
    obtain ⟨ws, h1, h2⟩ := hw
    exact ⟨ws, h1, .inl ⟨w, h2, rfl⟩⟩
  · rename_i hw
    cases h
    simp only [Option.bind_eq_some_iff] at hw
    obtain ⟨ws, h1, h2⟩ := hw
    exact ⟨ws, h1, .inr ⟨h2, rfl⟩⟩
  · cases h

theorem getD_orElse_sound {α : Type} {P : α → Prop} (x y : Option α) (d : α)
    (hx : ∀ r, x = some r → P r) (hy : ∀ r, y = some r → P r) (hd : P d) :
    P ((x.orElse fun _ => y).getD d) := by
  cases x with
  | some r => exact hx r rfl
  | none =>
    cases y with
    | some r => exact hy r rfl
    | none => exact hd

/-! ## Arithmetic -/

theorem binInt_inv {t : IntType} {op : IntBinOp} {a b w : WVal}
    (h : BinOp.eval (.int t op) a b = some (.val w)) :
    ∃ x y z, a.asInt t = some x ∧ b.asInt t = some y ∧ Silmaril.Wasm.Numerics.intBinOp t op x y = .ok z ∧
      w = .ofInt t z := by
  simp only [BinOp.eval] at h
  split at h
  · rename_i x y hx hy
    split at h
    · rename_i z hz
      cases h
      exact ⟨x, y, z, hx, hy, hz, rfl⟩
    · cases h
  · cases h

theorem const_any {env : Env WVal} {t : IntType} {c : BitVec t.width} {y : Tm Prim} {a : WVal}
    (h : (constOf? y).any (isInt t c) = true) (hy : Semantics.Tm.Eval instr env y () (.atom a) ()) :
    a.asInt t = some c := by
  cases hc : constOf? y with
  | none => simp [hc] at h
  | some d =>
    simp only [hc, Option.any_some, isInt, decide_eq_true_eq] at h
    have := eval_const_inv hc hy
    cases this
    exact h

theorem tm_beq {x y : Tm Prim} (h : (x == y) = true) : x = y := beq_iff_eq.mp h

theorem eval_zeroTm (env : Env WVal) (t : IntType) :
    Semantics.Tm.Eval instr env (zeroTm t) () (.atom (.ofInt t 0)) () := eval_constTm env _

theorem asInt_inj {t : IntType} {a : WVal} {x y : BitVec t.width} (hx : a.asInt t = some x)
    (hy : a.asInt t = some y) : x = y := Option.some.inj (hx.symm.trans hy)

macro "fin_bin" : tactic => `(tactic| (
  simp [Silmaril.Wasm.Numerics.intBinOp, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero,
    BitVec.zero_mul, BitVec.mul_zero] at *
  first | (subst_vars; rfl) | (exact hop.symm) | exact hop))

/-- Algebraic identities of binary operators. -/
theorem algBin_sound {env : Env WVal} {t : IntType} {op : IntBinOp} {x y r : Tm Prim}
    {ax ay w : WVal} (h : algBin t op x y = some r)
    (hx : Semantics.Tm.Eval instr env x () (.atom ax) ())
    (hy : Semantics.Tm.Eval instr env y () (.atom ay) ())
    (he : BinOp.eval (.int t op) ax ay = some (.val w)) :
    Semantics.Tm.Eval instr env r () (.atom w) () := by
  obtain ⟨bx, b2, bz, hbx, hby, hop, hw⟩ := binInt_inv he
  have hx' : Semantics.Tm.Eval instr env x () (.atom (.ofInt t bx)) () :=
    WVal.eq_ofInt_of_asInt hbx ▸ hx
  have hy' : Semantics.Tm.Eval instr env y () (.atom (.ofInt t b2)) () :=
    WVal.eq_ofInt_of_asInt hby ▸ hy
  -- the three kinds of result
  have toX : bz = bx → Semantics.Tm.Eval instr env x () (.atom w) () := fun e => by
    simpa only [hw, e] using hx'
  have toY : bz = b2 → Semantics.Tm.Eval instr env y () (.atom w) () := fun e => by
    simpa only [hw, e] using hy'
  have toZ : bz = 0 → Semantics.Tm.Eval instr env (zeroTm t) () (.atom w) () := fun e => by
    simpa only [hw, e] using eval_zeroTm env t
  -- what the guards of `algBin` say about the operands
  have cy : ∀ {c}, (constOf? y).any (isInt t c) = true → b2 = c := fun hc =>
    asInt_inj hby (const_any hc hy)
  have cx : ∀ {c}, (constOf? x).any (isInt t c) = true → bx = c := fun hc =>
    asInt_inj hbx (const_any hc hx)
  have same : x = y → bx = b2 := fun hxy => by
    have e : ax = ay := Value.atom.inj (tm_det hx (hxy ▸ hy))
    exact asInt_inj hbx (e ▸ hby)
  unfold algBin at h
  cases op <;> simp only [Bool.or_eq_true] at h
  all_goals ((try split_ifs at h) <;> (cases h))
  all_goals (try (cases ‹Signedness›))
  all_goals first
    | (refine toX ?_; obtain rfl := cy ‹_›; fin_bin)
    | (refine toX ?_; obtain rfl := same (tm_beq ‹_›); fin_bin)
    | (refine toY ?_; obtain rfl := cx ‹_›; fin_bin)
    | (refine toZ ?_; obtain rfl := same (tm_beq ‹_›); fin_bin)
    | (refine toZ ?_; rcases ‹_ ∨ _› with h0 | h0
       · obtain rfl := cy h0; fin_bin
       · obtain rfl := cx h0; fin_bin)


theorem algRel_sound {env : Env WVal} {t : IntType} {op : IntRelOp} {x y r : Tm Prim}
    {ax ay w : WVal} (h : algRel op x y = some r)
    (hx : Semantics.Tm.Eval instr env x () (.atom ax) ())
    (hy : Semantics.Tm.Eval instr env y () (.atom ay) ())
    (he : BinOp.eval (.rel t op) ax ay = some (.val w)) :
    Semantics.Tm.Eval instr env r () (.atom w) () := by
  unfold algRel at h
  split at h
  · rename_i hxy
    obtain rfl := tm_beq hxy
    have e := tm_det hx hy
    injection e with e
    subst e
    simp only [BinOp.eval] at he
    split at he
    · rename_i a b ha hb
      obtain rfl := asInt_inj ha hb
      cases he
      cases op <;> simp at h <;> subst h <;>
        simpa [Silmaril.Wasm.Numerics.intRelOp, Silmaril.Wasm.Numerics.bool32] using
          eval_constTm env _
    · cases he
  · cases h

theorem safe_no_trap {t : IntType} {op : IntBinOp} {a d : WVal}
    (hs : safeDivisor t op d = true) : BinOp.eval (.int t op) a d ≠ some .trap := by
  intro h
  simp only [BinOp.eval] at h
  split at h
  · rename_i x y _ hy
    split at h
    · cases h
    · rename_i e he
      simp only [safeDivisor, hy] at hs
      cases op <;> (try cases ‹Signedness›) <;>
        simp_all [Silmaril.Wasm.Numerics.intBinOp]
  · cases h

theorem args2_inv {env : Env WVal} {x y : Tm Prim} {va : SVal} {ws : List WVal}
    (h : Semantics.Tm.Eval instr env (tmTuple [x, y]) () va ())
    (hd : decodeList va = some ws) :
    ∃ ax ay, ws = [ax, ay] ∧ Semantics.Tm.Eval instr env x () (.atom ax) () ∧
      Semantics.Tm.Eval instr env y () (.atom ay) () := by
  have e := decodeList_eq hd
  simp only [tmTuple] at h
  cases h with
  | pair h1 h2 =>
    cases h2 with
    | pair h2 h3 =>
      cases h3
      rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, ws⟩⟩⟩ <;> simp [encodeList] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨a, b, rfl, h1, h2⟩

/-- Folding constant arguments. -/
theorem consts_inv {env : Env WVal} {a : Tm Prim} {va : SVal} {ws ws' : List WVal}
    (h : Semantics.Tm.Eval instr env a () va ())
    (hc : ((tmArgs? a).bind fun ts => ts.mapM constOf?) = some ws')
    (hd : decodeList va = some ws) : ws = ws' := by
  obtain ⟨ts, hts, hmap⟩ := Option.bind_eq_some_iff.mp hc
  rw [tmArgs?_eq hts] at h
  have := eval_consts hmap h
  subst this
  rw [decodeList_encodeList] at hd
  exact (Option.some.inj hd).symm

/-- A two-argument tuple of terms evaluates componentwise. -/
private theorem args2_of_tmArgs {env : Env WVal} {a x y : Tm Prim} {va : SVal} {ws : List WVal}
    (hxy : tmArgs? a = some [x, y]) (ha : Semantics.Tm.Eval instr env a () va ())
    (hd : decodeList va = some ws) :
    ∃ ax ay, ws = [ax, ay] ∧ Semantics.Tm.Eval instr env x () (.atom ax) () ∧
      Semantics.Tm.Eval instr env y () (.atom ay) () :=
  args2_inv (tmArgs?_eq hxy ▸ ha) hd

/-- The folding branch of `rewriteOp` on `.op o` returns the constant result. -/
private theorem rewriteOp_op_fold_sound {cfg : SimpCfg} {env : Env WVal} {o : Op} {a : Tm Prim}
    {va : SVal} {ws : List WVal} {w : WVal} (ha : Semantics.Tm.Eval instr env a () va ())
    (hdec : decodeList va = some ws) (hev : o.eval ws = some (.val w)) :
    ∀ r, (if cfg.fold then
          match (tmArgs? a).bind fun ts => ts.mapM constOf? with
          | some ws =>
              match o.eval ws with
              | some (.val w) => some (constTm w)
              | _ => none
          | none => none
        else none) = some r → Semantics.Tm.Eval instr env r () (.atom w) () := by
  intro r hr
  split at hr
  · split at hr
    next ws' hws' =>
      have hws : ws = ws' := consts_inv ha hws' hdec
      rw [← hws, hev] at hr
      cases hr
      exact eval_constTm _ _
    next => cases hr
  · cases hr

/-- The algebraic branch of `rewriteOp` on `.op o` is sound by `algBin_sound`/`algRel_sound`. -/
private theorem rewriteOp_op_alg_sound {cfg : SimpCfg} {T : Tys} {env : Env WVal} {o : Op}
    {a : Tm Prim} {va : SVal} {ws : List WVal} {w : WVal}
    (ha : Semantics.Tm.Eval instr env a () va ())
    (hdec : decodeList va = some ws) (hev : o.eval ws = some (.val w)) :
    ∀ r, (if cfg.alg then
          match o, tmArgs? a with
          | .bin (.int t op), some [x, y] =>
              if atomTy T x = some t ∧ atomTy T y = some t then algBin t op x y else none
          | .bin (.rel t op), some [x, y] =>
              if atomTy T x = some t ∧ atomTy T y = some t then algRel op x y else none
          | _, _ => none
        else none) = some r → Semantics.Tm.Eval instr env r () (.atom w) () := by
  intro r hr
  split at hr
  · split at hr
    next t op x y hxy =>
      obtain ⟨ax, ay, rfl, hx, hy⟩ := args2_of_tmArgs hxy ha hdec
      exact algBin_sound (Option.ite_none_right_eq_some.mp hr).2 hx hy hev
    next t op x y hxy =>
      obtain ⟨ax, ay, rfl, hx, hy⟩ := args2_of_tmArgs hxy ha hdec
      exact algRel_sound (Option.ite_none_right_eq_some.mp hr).2 hx hy hev
    next => cases hr
  · cases hr

/-- The folding branch of `rewriteOp` on `.opT o` returns the injected result or trap. -/
private theorem rewriteOp_opT_fold_sound {cfg : SimpCfg} {env : Env WVal} {o : Op} {a : Tm Prim}
    {va v : SVal} {ws : List WVal} (ha : Semantics.Tm.Eval instr env a () va ())
    (hdec : decodeList va = some ws)
    (hres : (∃ w, o.eval ws = some (.val w) ∧ v = .inl (.atom w)) ∨
      (o.eval ws = some .trap ∧ v = .inr .unit)) :
    ∀ r, (if cfg.fold then
          match (tmArgs? a).bind fun ts => ts.mapM constOf? with
          | some ws =>
              match o.eval ws with
              | some (.val w) => some (.inl (constTm w))
              | some .trap => some (.inr .unit)
              | none => none
          | none => none
        else none) = some r → Semantics.Tm.Eval instr env r () v () := by
  intro r hr
  split at hr
  · split at hr
    next ws' hws' =>
      have hws : ws = ws' := consts_inv ha hws' hdec
      rw [← hws] at hr
      rcases hres with ⟨w, hw, hv⟩ | ⟨hw, hv⟩
      · rw [hw] at hr
        cases hr
        exact hv ▸ .inl (eval_constTm _ _)
      · rw [hw] at hr
        cases hr
        exact hv ▸ .inr .unit
    next => cases hr
  · cases hr

/-- Division by a constant that cannot trap never takes the trap exit. -/
private theorem opT_safe_sound {env : Env WVal} {t : IntType} {op : IntBinOp} {a x y : Tm Prim}
    {va v : SVal} {ws : List WVal} {d : WVal} (ha : Semantics.Tm.Eval instr env a () va ())
    (hxy : tmArgs? a = some [x, y]) (hd : constOf? y = some d) (hs : safeDivisor t op d = true)
    (hdec : decodeList va = some ws)
    (hres : (∃ w, (Op.bin (.int t op)).eval ws = some (.val w) ∧ v = .inl (.atom w)) ∨
      ((Op.bin (.int t op)).eval ws = some .trap ∧ v = .inr .unit)) :
    Semantics.Tm.Eval instr env (.inl (.op (.op (.bin (.int t op))) a)) () v () := by
  obtain ⟨ax, ay, rfl, -, hy⟩ := args2_of_tmArgs hxy ha hdec
  have hay : ay = d := Value.atom.inj (eval_const_inv hd hy)
  rcases hres with ⟨w, hw, hv⟩ | ⟨hw, -⟩
  · rw [hv]
    refine .inl (.op ha ?_)
    show Prim.run _ _ = _
    simp only [Prim.run, hdec, Option.bind_some, hw]
  · exact absurd (hay ▸ hw) (safe_no_trap hs)

/-- The safe-division branch of `rewriteOp` on `.opT o`. -/
private theorem rewriteOp_opT_safe_sound {cfg : SimpCfg} {env : Env WVal} {o : Op} {a : Tm Prim}
    {va v : SVal} {ws : List WVal} (ha : Semantics.Tm.Eval instr env a () va ())
    (hdec : decodeList va = some ws)
    (hres : (∃ w, o.eval ws = some (.val w) ∧ v = .inl (.atom w)) ∨
      (o.eval ws = some .trap ∧ v = .inr .unit)) :
    ∀ r, (if cfg.alg then
          match o, tmArgs? a with
          | .bin (.int t op), some [_, y] =>
              match constOf? y with
              | some d => if safeDivisor t op d then some (.inl (.op (.op o) a)) else none
              | none => none
          | _, _ => none
        else none) = some r → Semantics.Tm.Eval instr env r () v () := by
  intro r hr
  split at hr
  · split at hr
    next t op x y hxy =>
      split at hr
      next d hd =>
        obtain ⟨hs, hr'⟩ := Option.ite_none_right_eq_some.mp hr
        exact Option.some.inj hr' ▸ opT_safe_sound ha hxy hd hs hdec hres
      next => cases hr
    next => cases hr
  · cases hr

/-- `rewriteOp` on `.truthy` decides a constant condition. -/
private theorem rewriteOp_truthy_sound {cfg : SimpCfg} {T : Tys} {env : Env WVal} {a : Tm Prim}
    {va v : SVal} (ha : Semantics.Tm.Eval instr env a () va ())
    (hrun : Prim.run .truthy va = some v) :
    Semantics.Tm.Eval instr env (rewriteOp cfg T .truthy a) () v () := by
  simp only [rewriteOp]
  split
  · split
    next w hw =>
      have hv : va = .atom w := eval_const_inv hw ha
      have hrun' : (w.truthy.map fun b => if b then Value.inl .unit else .inr .unit) = some v := by
        simpa only [hv, Prim.run] using hrun
      split
      next ht =>
        have hv' : v = .inl .unit := by simpa [ht] using hrun'.symm
        exact hv' ▸ .inl .unit
      next ht =>
        have hv' : v = .inr .unit := by simpa [ht] using hrun'.symm
        exact hv' ▸ .inr .unit
      next => exact .op ha hrun
    next => exact .op ha hrun
  · exact .op ha hrun

theorem rewriteOp_sound (cfg : SimpCfg) (T : Tys) {env : Env WVal} {p : Prim} {a : Tm Prim}
    {va v : SVal} (ha : Semantics.Tm.Eval instr env a () va ()) (hrun : p.run va = some v) :
    Semantics.Tm.Eval instr env (rewriteOp cfg T p a) () v () := by
  cases p with
  | op o =>
    obtain ⟨ws, w, hdec, hev, hv⟩ : ∃ ws w, decodeList va = some ws ∧
        o.eval ws = some (.val w) ∧ v = .atom w := run_op_inv hrun
    rw [hv]
    exact getD_orElse_sound (P := fun r => Semantics.Tm.Eval instr env r () (.atom w) ()) _ _ _
      (rewriteOp_op_fold_sound ha hdec hev) (rewriteOp_op_alg_sound ha hdec hev)
      (hv ▸ .op ha hrun)
  | opT o =>
    obtain ⟨ws, hdec, hres⟩ := run_opT_inv hrun
    exact getD_orElse_sound (P := fun r => Semantics.Tm.Eval instr env r () v ()) _ _ _
      (rewriteOp_opT_fold_sound ha hdec hres) (rewriteOp_opT_safe_sound ha hdec hres)
      (.op ha hrun)
  | truthy => exact rewriteOp_truthy_sound ha hrun

/-! ## Terms under facts -/

theorem resolveVar_sound (cfg : SimpCfg) {F : Facts} {env : Env WVal} (hF : FactsOK F env)
    (i : Nat) : Semantics.Tm.Eval instr env (resolveVar cfg F i) () (env i) () := by
  unfold resolveVar
  split
  · rename_i j hj
    split
    · have h1 := hF i _ hj
      have h2 : Semantics.Tm.Eval instr (fun j => env (j + (i + 1))) (.var j) () (env (j + (i + 1))) () :=
        .var
      have e := tm_det h1 h2
      exact .var_of_eq (by rw [e]; congr 1; omega)
    · exact .var
  · rename_i _ t _ ht
    split
    · rename_i w hw
      split
      · rw [eval_const_inv hw (hF i t ht)]
        exact eval_constTm _ _
      · exact .var
    · exact .var
  · exact .var

theorem simpTm_sound (cfg : SimpCfg) {F : Facts} {T : Tys} {env : Env WVal} {t : Tm Prim}
    {s s' : Unit} {v : SVal} (h : Semantics.Tm.Eval instr env t s v s') :
    FactsOK F env → Semantics.Tm.Eval instr env (simpTm cfg F T t) s v s' := by
  induction h with
  | var => intro hF; exact resolveVar_sound cfg hF _
  | op ha hstep ih =>
      intro hF
      cases ‹Unit›; cases ‹Unit›; cases ‹Unit›
      exact rewriteOp_sound cfg T (ih hF) hstep
  | pair ha hb iha ihb => intro hF; exact .pair (iha hF) (ihb hF)
  | unit => intro _; exact .unit
  | let₁ ha hb => intro _; exact .let₁ ha hb
  | let₂ ha hb => intro _; exact .let₂ ha hb
  | inl ha => intro _; exact .inl ha
  | inr ha => intro _; exact .inr ha
  | case_inl ha hb => intro _; exact .case_inl ha hb
  | case_inr ha hb => intro _; exact .case_inr ha hb

theorem cseFind_spec {F : Facts} {a : Tm Prim} {p : Nat} (h : cseFind F a = some p) :
    ∃ t, F.get p = some t ∧ t.rename (· + (p + 1)) = a := by
  unfold cseFind at h
  have := List.find?_some h
  simp only [Option.any_eq_true, beq_iff_eq] at this
  exact this

theorem cseTm_sound (cfg : SimpCfg) {F : Facts} {env : Env WVal} (hF : FactsOK F env)
    {a : Tm Prim} {v : SVal} (h : Semantics.Tm.Eval instr env a () v ()) :
    Semantics.Tm.Eval instr env (cseTm cfg F a) () v () := by
  unfold cseTm
  split
  · split
    · split
      · rename_i p hp
        obtain ⟨t, ht, hre⟩ := cseFind_spec hp
        have h1 := (hF p t ht).rename (env' := env) (ρ := (· + (p + 1))) (fun _ => rfl)
        rw [hre] at h1
        rw [tm_det h h1]
        exact .var
      · exact h
    · exact h
  · exact h

theorem simpTm_sound' (cfg : SimpCfg) {F : Facts} {T : Tys} {env : Env WVal} (hF : FactsOK F env)
    {t : Tm Prim} {s s' : Unit} {v : SVal} (h : Semantics.Tm.Eval instr env t s v s') :
    Semantics.Tm.Eval instr env (cseTm cfg F (simpTm cfg F T t)) s v s' := by
  cases s; cases s'
  exact cseTm_sound cfg hF (simpTm_sound cfg h hF)

/-! ## Facts under binders -/

theorem _root_.Silmaril.Wasm.SSA.FactsOK.nil (env : Env WVal) : FactsOK [] env := by
  intro i t h; simp [Facts.get] at h

theorem _root_.Silmaril.Wasm.SSA.FactsOK.push {F : Facts} {env : Env WVal} (hF : FactsOK F env) (v : SVal)
    (f : Option (Tm Prim))
    (hf : ∀ t, f = some t → Semantics.Tm.Eval instr env t () v ()) :
    FactsOK (f :: F) (extend env v) := by
  intro i t ht
  cases i with
  | zero =>
    simp only [Facts.get, List.getElem?_cons_zero, Option.join_some] at ht
    exact hf t ht
  | succ i =>
    simp only [Facts.get, List.getElem?_cons_succ] at ht
    exact hF i t ht

theorem _root_.Silmaril.Wasm.SSA.FactsOK.none {F : Facts} {env : Env WVal} (hF : FactsOK F env) (v : SVal) :
    FactsOK (none :: F) (extend env v) :=
  hF.push v Option.none (fun _ h => by cases h)

end Silmaril.Proofs.Wasm.SSA.Passes
