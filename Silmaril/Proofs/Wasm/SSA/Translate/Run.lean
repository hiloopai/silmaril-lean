module

public import Silmaril.Proofs.Wasm.SSA.Translate.Sim

/-!
# The translation simulates the fragment: loops, branches and the induction

Loops go through `LoopSim` (`loopSim_exit`, `loopSim_back`, `sim_loop`).
`simE_of`, `simArgs_of`, `simSeq_of` and `simLoop_of` are the mutual
induction over fragment derivations; `compileFunc_sound` is the function-level
result.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm (IntType)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

/-! ## Branches -/

theorem eval_jump {c c' : Ctx} {env env' : Env WVal} {ls' : List WVal} {l : Nat} {lk : LabelK}
    {rl : Option Nat} {r : Option WVal} {m : Nat} {v : SVal} {α : Type}
    (hext : Ext c env c' env') (hag : Agree c' env' ls') (hres : ResOK c' env' rl r)
    (hlab : c.labels[l]? = some lk) (ht : TgtL c (Out.brk (α := α) l ls' r) = some (m, v)) :
    REval env' (jump c' lk rl) (c'.lbl m) v := by
  cases lk with
  | join m' =>
      simp only [TgtL, hlab, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      exact .br (eval_pack hag hres)
  | ret =>
      simp only [TgtL, hlab, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      simp only [jump, hext.ret, hext.fty]
      refine .br (eval_resTm ?_)
      split
      · exact hres
      · trivial

theorem eval_ret {c c' : Ctx} {env env' : Env WVal} {rl : Option Nat} {r : Option WVal} {m : Nat}
    {v : SVal} {α : Type} (hext : Ext c env c' env') (hres : ResOK c' env' rl r)
    (ht : TgtL c (Out.ret (α := α) r) = some (m, v)) : REval env' (jump c' .ret rl) (c'.lbl m) v := by
  simp only [TgtL, Option.some.injEq, Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl⟩ := ht
  simp only [jump, hext.ret, hext.fty]
  refine .br (eval_resTm ?_)
  split
  · exact hres
  · trivial

theorem sim_br {ls ls' : List WVal} {l : Nat} {args : List Expr} {vs : List WVal}
    (ha : SimArgs ls args (.ok ls' vs)) : SimE ls (.br l args) (.brk l ls' vs.head?) := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine ha c env _ m v hwf hag hm ?_
  intro c' env' lvls hext hag' hl
  cases hlab : c.labels[l]? with
  | none => simp [Post, TgtL, hlab] at hpost
  | some lk =>
      simp only
      exact eval_jump hext hag' (resOK_head? hl) hlab hpost

theorem sim_return {ls ls' : List WVal} {args : List Expr} {vs : List WVal}
    (ha : SimArgs ls args (.ok ls' vs)) : SimE ls (.return_ args) (.ret vs.head?) := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine ha c env _ m v hwf hag hm ?_
  intro c' env' lvls hext hag' hl
  exact eval_ret hext (resOK_head? hl) hpost

theorem sim_brIf {ls ls' : List WVal} {l : Nat} {args : List Expr} {vs : List WVal} {cv : WVal}
    {b : Bool} (ha : SimArgs ls args (.ok ls' vs)) (hc : vs.getLast? = some cv)
    (hb : cv.truthy = some b) :
    SimE ls (.brIf l args) (if b then .brk l ls' vs.dropLast.head? else .ok ls' vs.dropLast.head?) := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  refine ha c env _ m v hwf hag hm ?_
  intro c' env' lvls hext hag' hl
  obtain ⟨cl, hcl, hvcl⟩ := forall₂_getLast? hl hc
  simp only [hcl]
  have hT : TEval env' (.op .truthy (c'.var cl)) (if b then .inl .unit else .inr .unit) :=
    teval_op (eval_var hvcl) (by simp [Prim.run, hb])
  have hres : ResOK c'.bind (extend env' .unit) lvls.dropLast.head? vs.dropLast.head? :=
    ResOK.ext (Ext.bind c' env' _) (resOK_head? (forall₂_dropLast hl))
  have hext' := hext.trans (Ext.bind c' env' .unit)
  cases b with
  | true =>
      refine reval_case_inl hT ?_
      cases hlab : c.labels[l]? with
      | none => simp [Post, TgtL, hlab] at hpost
      | some lk =>
          simp only
          exact eval_jump hext' (hag'.bind _) hres hlab hpost
  | false =>
      exact reval_case_inr hT (hpost _ _ _ hext' (hag'.bind _) hres)

theorem sim_args_abrupt_of {ls : List WVal} {args : List Expr} {out : Out (List WVal)}
    (ha : SimArgs ls args out) (hab : out.Abrupt) (e : Expr)
    (he : ∀ c k, ∃ K, cE e c k = cArgs args c K) : SimE ls e out.cast := by
  intro c env k m v hwf hag hm hpost
  rw [post_abrupt (Out.cast_abrupt _ hab)] at hpost
  obtain ⟨K, hK⟩ := he c k
  rw [hK]
  exact simArgs_abrupt ha hab hwf hag hm hpost _

/-! ## Operands and bodies -/

theorem args_nil {ls : List WVal} : SimArgs ls [] (.ok ls []) := by
  intro c env k m v hwf hag hm hpost
  rw [cArgs]
  exact hpost c env [] (Ext.refl c env) hag .nil

theorem args_cons {ls ls₁ ls₂ : List WVal} {e : Expr} {es : List Expr} {w : WVal}
    {vs : List WVal} (he : SimE ls e (.ok ls₁ (some w))) (ha : SimArgs ls₁ es (.ok ls₂ vs)) :
    SimArgs ls (e :: es) (.ok ls₂ (w :: vs)) := by
  intro c env k m v hwf hag hm hpost
  rw [cArgs]
  refine he c env _ m v hwf hag hm ?_
  intro c' env' rl hext hag' hres
  match rl, hres with
  | some l, hv =>
    simp only
    refine ha c' env' _ m v (hwf.ext hext) hag' (lt_of_lt_of_le hm hext.ldepth) ?_
    intro c'' env'' lvls hext' hag'' hl
    exact hpost c'' env'' (l :: lvls) (hext.trans hext') hag'' (.cons (VarOK.ext hext' hv) hl)

theorem args_head_abrupt {ls : List WVal} {e : Expr} {es : List Expr} {out : Out (Option WVal)}
    (he : SimE ls e out) (hab : out.Abrupt) : SimArgs ls (e :: es) out.cast := by
  intro c env k m v hwf hag hm hpost
  rw [post_abrupt (Out.cast_abrupt _ hab), TgtL_cast hab] at hpost
  rw [cArgs]
  exact sim_abrupt_cont he hab hwf hag hm hpost _

theorem args_tail_abrupt {ls ls₁ : List WVal} {e : Expr} {es : List Expr} {w : WVal}
    {out : Out (List WVal)} (he : SimE ls e (.ok ls₁ (some w))) (ha : SimArgs ls₁ es out)
    (hab : out.Abrupt) : SimArgs ls (e :: es) out := by
  intro c env k m v hwf hag hm hpost
  rw [post_abrupt hab] at hpost
  rw [cArgs]
  refine he c env _ m v hwf hag hm ?_
  intro c' env' rl hext hag' hres
  match rl, hres with
  | some l, hv =>
    simp only
    refine ha c' env' _ m v (hwf.ext hext) hag' (lt_of_lt_of_le hm hext.ldepth) ?_
    rw [post_abrupt hab, TgtL_ext hext]
    exact hpost

theorem seq_nil {ls : List WVal} {r : Option WVal} : SimSeq ls r [] (.ok ls r) := by
  intro c env k rl m v hwf hag hres hm hpost
  rw [cSeq]
  exact hpost c env rl (Ext.refl c env) hag hres

theorem seq_cons {ls ls₁ : List WVal} {r r₁ : Option WVal} {e : Expr} {es : List Expr}
    {out : Out (Option WVal)} (he : SimE ls e (.ok ls₁ r₁)) (hs : SimSeq ls₁ r₁ es out) :
    SimSeq ls r (e :: es) out := by
  intro c env k rl m v hwf hag hres hm hpost
  rw [cSeq]
  refine he c env _ m v hwf hag hm ?_
  intro c' env' rl' hext hag' hres'
  refine hs c' env' k rl' m v (hwf.ext hext) hag' hres' (lt_of_lt_of_le hm hext.ldepth) ?_
  cases out with
  | ok ls' a => exact KOK.ext hext hpost
  | _ => simp only [Post] at hpost ⊢; rw [TgtL_ext hext]; exact hpost

theorem seq_abrupt {ls : List WVal} {r : Option WVal} {e : Expr} {es : List Expr}
    {out : Out (Option WVal)} (he : SimE ls e out) (hab : out.Abrupt) :
    SimSeq ls r (e :: es) out := by
  intro c env k rl m v hwf hag hres hm hpost
  rw [post_abrupt hab] at hpost
  rw [cSeq]
  exact sim_abrupt_cont he hab hwf hag hm hpost _

/-! ## Loops -/

/-- The loop header runs the body and leaves to the exit join, the header
itself, or an outer label. -/
theorem eval_header {ls : List WVal} {body : List Expr} {out : Out (Option WVal)}
    (hs : SimSeq ls none body out) {c : Ctx} {env : Env WVal} {r₀ : Option WVal} (hwf : WF c)
    (hlen : ls.length = c.locals.length) {m : Nat} {v : SVal} (hm : m < c.ldepth + 2)
    (hp : Post out (fun ls' r => m = c.ldepth ∧ v = packV ls' r)
      (TgtL (headerCtx c) out = some (m, v))) :
    REval (extend env (packV ls r₀)) (loopBlocks c body ⟨0, Nat.one_pos⟩) (c.ldepth + 1 - m) v := by
  unfold loopBlocks
  rw [show c.locals.length = ls.length from hlen.symm]
  refine eval_unpack ls (headerCtx c) c.depth _ (resV r₀) _ (c.depth + 1 + 2 * ls.length) _ _ rfl
    (Nat.lt_succ_self _) (by show extend _ _ (c.depth + 1 - 1 - c.depth) = _; simp [packV]) ?_
  intro lvls tl env' hlv _ _ _
  have := hs { headerCtx c with depth := c.depth + 1 + 2 * ls.length, locals := lvls } env'
    (fun c'' r => .br (c''.lbl c.ldepth) (c''.pack r)) none m v hwf.headerCtx hlv trivial
    (by show m < c.ldepth + 2; omega) ?_
  · have e : ({ headerCtx c with depth := c.depth + 1 + 2 * ls.length, locals := lvls } : Ctx).lbl m =
        c.ldepth + 1 - m := by simp [Ctx.lbl, headerCtx]
    rwa [e] at this
  · cases out with
    | ok ls' r =>
        obtain ⟨rfl, rfl⟩ := hp
        intro c'' env'' rl hext hag hres
        exact .br (eval_pack hag hres)
    | _ => exact hp

theorem TgtL_header_succ (c : Ctx) {α : Type} (l : Nat) (ls : List WVal) (r : Option WVal) :
    TgtL (headerCtx c) (Out.brk (α := α) (l + 1) ls r) = TgtL c (Out.brk (α := α) l ls r) := rfl

/-- An abrupt body outcome that leaves the loop at an outer level `m`. -/
private theorem loopSim_exit_outer {ls : List WVal} {body : List Expr} {out : Out (Option WVal)}
    (hs : SimSeq ls none body out) {c : Ctx} {env : Env WVal} {r₀ : Option WVal} (hwf : WF c)
    (hlen : ls.length = c.locals.length) {m : Nat} {v : SVal} (hm : m < c.ldepth)
    (hp : Post out (fun ls' r => m = c.ldepth ∧ v = packV ls' r)
      (TgtL (headerCtx c) out = some (m, v))) :
    Follow1 env (loopBlocks c body) 0 (packV ls r₀) (c.ldepth - m) v := by
  have hh : REval (extend env (packV ls r₀)) (loopBlocks c body ⟨0, Nat.one_pos⟩)
      (c.ldepth + 1 - m) v := eval_header hs hwf hlen (by omega) hp
  have h2 : c.ldepth + 1 - m - 1 = c.ldepth - m := by omega
  exact h2 ▸ .step Nat.one_pos hh (.exit (by omega))

theorem loopSim_exit {ls : List WVal} {ty : Option IntType} {body : List Expr}
    {out o : Out (Option WVal)} (hs : SimSeq ls none body out) (hx : LoopExit ty out o) :
    LoopSim ls ty body o := by
  intro c env r₀ hwf hlen
  cases hx with
  | @ok ls' r hok =>
      refine ⟨r, hok, rfl, .step Nat.one_pos ?_ (.exit (le_refl 1))⟩
      have hh : REval (extend env (packV ls r₀)) (loopBlocks c body ⟨0, Nat.one_pos⟩)
          (c.ldepth + 1 - c.ldepth) (packV ls' r) :=
        eval_header hs hwf hlen (by omega) ⟨rfl, rfl⟩
      simpa only [Nat.add_sub_cancel_left] using hh
  | brk =>
      intro m v ht
      exact loopSim_exit_outer hs hwf hlen (hwf.tgt ht) ((TgtL_header_succ c _ _ _).trans ht)
  | ret =>
      intro m v ht
      exact loopSim_exit_outer hs hwf hlen (hwf.tgt ht) ht
  | trap =>
      intro m v ht
      exact loopSim_exit_outer hs hwf hlen (hwf.tgt ht) ht

theorem loopSim_back {ls ls' : List WVal} {ty : Option IntType} {body : List Expr}
    {r : Option WVal} {o : Out (Option WVal)} (hs : SimSeq ls none body (.brk 0 ls' r))
    (hr : LoopSim ls' ty body o) (hlen' : ls'.length = ls.length) : LoopSim ls ty body o := by
  intro c env r₀ hwf hlen
  have hh := eval_header hs (env := env) (r₀ := r₀) hwf hlen (m := c.ldepth + 1)
    (v := packV ls' r) (by omega) (by simp [Post, TgtL, headerCtx])
  rw [Nat.sub_self] at hh
  have H := hr c env r hwf (hlen'.trans hlen)
  cases o with
  | ok ls'' rr =>
      obtain ⟨r', h1, h2, hf⟩ := H
      exact ⟨r', h1, h2, .step Nat.one_pos hh hf⟩
  | _ => intro m v ht; exact .step Nat.one_pos hh (H m v ht)

theorem sim_loop {ls : List WVal} {ty : Option IntType} {body : List Expr} {o : Out (Option WVal)}
    (hl : LoopSim ls ty body o) (hlen : LenOK ls o) : SimE ls (.loop ty body) o := by
  intro c env k m v hwf hag hm hpost
  rw [cE]
  show REval env (.cfg (.cfg (.br 0 (c.pack none)) 1 (loopBlocks c body)) 1 _) _ _
  have hentry : REval env (.br 0 (c.pack none)) 0 (packV ls none) :=
    .br (eval_pack hag (rl := none) (r := none) trivial)
  have H := hl c env none hwf hag.length.symm
  rw [← lbl_sub]
  cases o with
  | ok ls' rr =>
      obtain ⟨r, hok, rfl, hf⟩ := H
      refine cfg_join (by omega) (.cfg hentry hf) (eval_join ?_ hok hpost)
      simp [LenOK] at hlen; rw [hlen]; exact hag.length.symm
  | _ =>
      exact cfg_exit (by omega) (.cfg hentry (H m v hpost))

/-! ## The induction -/

/-- The induction's motive for expressions: simulation, and for loops `LoopSim`. -/
def SimE' (ls : List WVal) (e : Expr) (o : Out (Option WVal)) : Prop :=
  SimE ls e o ∧ ∀ ty body, e = .loop ty body → LoopSim ls ty body o

mutual

theorem simE_of : ∀ {ls : List WVal} {e : Expr} {o : Out (Option WVal)}, Exec ls e o → SimE' ls e o
  | _, _, _, .op ha hev => ⟨sim_op_ok (simArgs_of ha) hev, fun _ _ h => nomatch h⟩
  | _, _, _, .op_trap ha hev => ⟨sim_op_trap (simArgs_of ha) hev, fun _ _ h => nomatch h⟩
  | _, _, _, .op_abrupt ha hab => ⟨sim_op_abrupt (simArgs_of ha) hab, fun _ _ h => nomatch h⟩
  | _, _, _, .localGet h => ⟨sim_localGet h, fun _ _ h => nomatch h⟩
  | _, _, _, .localSet he => ⟨sim_localSet (simE_of he).1, fun _ _ h => nomatch h⟩
  | _, _, _, .localSet_abrupt he hab =>
      ⟨sim_localSet_abrupt (simE_of he).1 hab, fun _ _ h => nomatch h⟩
  | _, _, _, .localTee he => ⟨sim_localTee (simE_of he).1, fun _ _ h => nomatch h⟩
  | _, _, _, .localTee_abrupt he hab =>
      ⟨sim_localTee_abrupt (simE_of he).1 hab, fun _ _ h => nomatch h⟩
  | _, _, _, .drop he => ⟨sim_drop (simE_of he).1, fun _ _ h => nomatch h⟩
  | _, _, _, .drop_abrupt he hab => ⟨sim_drop_abrupt (simE_of he).1 hab, fun _ _ h => nomatch h⟩
  | _, _, _, .nop => ⟨sim_nop, fun _ _ h => nomatch h⟩
  | _, _, _, .unreachable => ⟨sim_unreachable, fun _ _ h => nomatch h⟩
  | _, _, _, .block hs hx => ⟨sim_block (simSeq_of hs) hx (seq_len hs), fun _ _ h => nomatch h⟩
  | _, _, _, .loop hs hx =>
      ⟨sim_loop (loopSim_exit (simSeq_of hs) hx) (exec_len (.loop hs hx)), fun _ _ h => by
        cases h; exact loopSim_exit (simSeq_of hs) hx⟩
  | _, _, _, .loop_back hs hr =>
      ⟨sim_loop (loopSim_back (simSeq_of hs) ((simE_of hr).2 _ _ rfl)
          (by simpa [LenOK] using seq_len hs)) (exec_len (.loop_back hs hr)), fun _ _ h => by
        cases h
        exact loopSim_back (simSeq_of hs) ((simE_of hr).2 _ _ rfl)
          (by simpa [LenOK] using seq_len hs)⟩
  | _, _, _, .if_ hc hb hs hx =>
      ⟨sim_if (simE_of hc).1 hb (simSeq_of hs) hx (seq_len hs), fun _ _ h => nomatch h⟩
  | _, _, _, .if_abrupt hc hab => ⟨by
      intro c env k m v hwf hag hm hpost
      rw [post_abrupt hab] at hpost
      rw [cE]
      exact sim_abrupt_cont (simE_of hc).1 hab hwf hag hm hpost _, fun _ _ h => nomatch h⟩
  | _, _, _, .br ha => ⟨sim_br (simArgs_of ha), fun _ _ h => nomatch h⟩
  | _, _, _, .br_abrupt ha hab =>
      ⟨sim_args_abrupt_of (simArgs_of ha) hab _ fun c k => ⟨_, by rw [cE]⟩, fun _ _ h => nomatch h⟩
  | _, _, _, .brIf ha hc hb => ⟨sim_brIf (simArgs_of ha) hc hb, fun _ _ h => nomatch h⟩
  | _, _, _, .brIf_abrupt ha hab =>
      ⟨sim_args_abrupt_of (simArgs_of ha) hab _ fun c k => ⟨_, by rw [cE]⟩, fun _ _ h => nomatch h⟩
  | _, _, _, .return_ ha => ⟨sim_return (simArgs_of ha), fun _ _ h => nomatch h⟩
  | _, _, _, .return_abrupt ha hab =>
      ⟨sim_args_abrupt_of (simArgs_of ha) hab _ fun c k => ⟨_, by rw [cE]⟩, fun _ _ h => nomatch h⟩

theorem simArgs_of : ∀ {ls : List WVal} {es : List Expr} {o : Out (List WVal)},
    Args ls es o → SimArgs ls es o
  | _, _, _, .nil => args_nil
  | _, _, _, .cons he ha => args_cons (simE_of he).1 (simArgs_of ha)
  | _, _, _, .head_abrupt he hab => args_head_abrupt (simE_of he).1 hab
  | _, _, _, .tail_abrupt he ha hab => args_tail_abrupt (simE_of he).1 (simArgs_of ha) hab

theorem simSeq_of : ∀ {ls : List WVal} {r : Option WVal} {es : List Expr} {o : Out (Option WVal)},
    Seq ls r es o → SimSeq ls r es o
  | _, _, _, _, .nil => seq_nil
  | _, _, _, _, .cons he hs => seq_cons (simE_of he).1 (simSeq_of hs)
  | _, _, _, _, .abrupt he hab => seq_abrupt (simE_of he).1 hab

end

/-! ## Functions -/

theorem agree_initial (args : List WVal) (fty : Option IntType) :
    Agree (Ctx.initial args.length fty) (argEnv args) args := by
  unfold Agree
  rw [List.forall₂_iff_get]
  refine ⟨by simp [Ctx.initial], fun i h₁ h₂ => ⟨by simp [Ctx.initial] at h₁ ⊢; omega, ?_⟩⟩
  simp only [Ctx.initial, List.get_eq_getElem, List.getElem_range, argEnv]
  have hi : i < args.length := by simpa [Ctx.initial] using h₁
  rw [List.getElem?_reverse (by omega)]
  simp only [show args.length - 1 - (args.length - 1 - i) = i by omega, List.getElem?_eq_getElem hi]

theorem wf_initial (p : Nat) (fty : Option IntType) : WF (Ctx.initial p fty) := by
  refine ⟨fun m hm => ?_, by simp [Ctx.initial], by simp [Ctx.initial]⟩
  simp [Ctx.initial] at hm

theorem TgtL_fields {c c' : Ctx} (h2 : c'.labels = c.labels) (h3 : c'.ret = c.ret)
    (h4 : c'.trap = c.trap) (h5 : c'.fty = c.fty) {α : Type} (o : Out α) : TgtL c' o = TgtL c o := by
  cases o <;> simp [TgtL, h2, h3, h4, h5]

theorem decodeOut_resV (x : Option WVal) : decodeOut 0 (resV x) = some (.ret x) := by
  cases x <;> rfl

/-- The function body reaches the exit of each body outcome. -/
theorem eval_body {f : FragFunc} {args : List WVal} {out : Out (Option WVal)}
    (hlen : args.length = f.params.length)
    (hs : SimSeq (f.initLocals args) none f.body out) {m : Nat} {v : SVal}
    (hp : Post out (fun _ r => m = 1 ∧ v = resV (blockRes f.result r))
      (TgtL (Ctx.initial f.params.length f.result) out = some (m, v))) :
    REval (argEnv args) (compileFunc f).body (1 - m) v := by
  have hag₀ : Agree (Ctx.initial f.params.length f.result) (argEnv args) args :=
    hlen ▸ agree_initial args f.result
  refine eval_initZeros f.locals _ (argEnv args) args _ (1 - m) v hag₀ ?_
  intro c' env' h1 h2 h3 h4 h5 hag'
  have hwf : WF c' := ⟨fun m hm => by rw [h1]; exact (wf_initial _ _).1 m (h2 ▸ hm),
    by rw [h1, h3]; exact (wf_initial _ _).2.1, by rw [h1, h4]; exact (wf_initial _ _).2.2⟩
  have hm : m < 2 := by
    cases out with
    | ok => exact hp.1 ▸ by omega
    | _ => exact (wf_initial f.params.length f.result).tgt hp
  have hk : Post out (fun ls' r => KOK c' env' (fun c r => jump c .ret r) ls' r m v)
      (TgtL c' out = some (m, v)) := by
    cases out with
    | ok ls' r =>
        show KOK c' env' (fun c r => jump c .ret r) ls' r m v
        obtain ⟨hm1, hv⟩ := hp
        intro c'' env'' rl hext hag'' hres
        refine eval_ret (α := Unit) hext hres ?_
        rw [hm1, hv]
        simp [TgtL, h3, h5, blockRes, Ctx.initial]
    | _ =>
        show TgtL c' _ = some (m, v)
        rw [TgtL_fields h2 h3 h4 h5]
        exact hp
  have hb : REval env' (cSeq f.body c' none fun c r => jump c .ret r) (c'.lbl m) v :=
    hs c' env' _ none m v hwf hag' trivial (by rw [h1]; simpa [Ctx.initial]) hk
  have hl : c'.lbl m = 1 - m := by simp [Ctx.lbl, h1, Ctx.initial]
  rw [← hl]
  exact hb

/-- **Correctness of the translation**: every terminating run of a fragment
function is a run of its translation, with the same outcome. -/
theorem compileFunc_sound {f : FragFunc} {args : List WVal} {o : FOut} (h : f.Run args o) :
    (compileFunc f).Run args o := by
  obtain ⟨hty, out, hseq, hexit⟩ := h
  have hlen : args.length = f.params.length := by rw [← hty]; simp
  refine ⟨hty, ?_⟩
  have hs : SimSeq (f.initLocals args) none f.body out := simSeq_of hseq
  cases out with
  | ok ls r =>
      have ho : o = .ret (blockRes f.result r) := (Option.some.inj hexit).symm
      rw [ho]
      exact ⟨_, _, eval_body hlen hs (m := 1) ⟨rfl, rfl⟩, decodeOut_resV _⟩
  | brk l ls r =>
      cases l with
      | succ => exact absurd hexit (by simp [funcExit])
      | zero =>
          have ho : o = .ret (blockRes f.result r) := (Option.some.inj hexit).symm
          rw [ho]
          exact ⟨_, _, eval_body hlen hs (m := 1) (v := resV (blockRes f.result r))
            (by simp [Post, TgtL, Ctx.initial, blockRes]; rfl), decodeOut_resV _⟩
  | ret r =>
      have ho : o = .ret (blockRes f.result r) := (Option.some.inj hexit).symm
      rw [ho]
      exact ⟨_, _, eval_body hlen hs (m := 1) (v := resV (blockRes f.result r))
        (by simp [Post, TgtL, Ctx.initial, blockRes]; rfl), decodeOut_resV _⟩
  | trap =>
      have ho : o = .trap := (Option.some.inj hexit).symm
      rw [ho]
      exact ⟨_, _, eval_body hlen hs (m := 0) (v := .unit) (by simp [Post, TgtL, Ctx.initial]), rfl⟩

end Silmaril.Proofs.Wasm.SSA.Translate
