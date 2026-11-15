module

public import Silmaril.Proofs.Wasm.Abstract.FullObsNative.Prod

/-!
Proofs for `Silmaril.Wasm.Abstract.FullObsNative.Thms`: **local divergence is silent
divergence or an infinite answered run**, any oracle (`exposed_of_localDivO`).

The oracle need not be functional, so the closed-oracle argument of `StoreCall` (answered
pending prefixes are comparable) does not apply. Instead the run is built by *following the
witness*: a problem that diverges within its function, in any continuation `K`, either makes
its tree silent (`diverge`), or reaches, after at least one answered call, the tree of another
locally diverging problem in some continuation (`W`, `local_step`). The proof of `local_step`
is by well-founded recursion on the code: every unfolding step either descends into a
subtree, advances past a finished prefix to a shorter list, or makes an answered call; the
only exception is a loop iteration that finishes silently and continues, and a loop doing so
forever runs to `diverge` (`iter_chain`, the Elgot uniformity law against a silent counter).
Repeating `local_step`, a run either ends silent after finitely many answered calls or makes
infinitely many (`exposed_of_localDivO`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FullObsNative

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree
open Silmaril.Wasm.Interp (Problem)

variable {H : Type}

/-! ## Reaching a tree along answered calls -/

/-- `TReach t cs t'`: the tree `t` makes the calls `cs` (with their answers) and is then `t'`. -/
inductive TReach {E : Sig.{0}} {Y : Type 1} :
    Silmaril.Elgot.ITree.Tree (SigEv E) Y → List (Call E) → Silmaril.Elgot.ITree.Tree (SigEv E) Y →
      Prop
  | nil {t} : TReach t [] t
  | vis {t : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {R : Type} {e : SigEv E R}
      {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {n : R} {cs t'} :
      t = vis e k → TReach (k n) cs t' → TReach t (⟨e.1, cast e.2.symm n⟩ :: cs) t'

section
variable {E : Sig.{0}} {Y Z : Type 1}

theorem TReach.trans {a b c : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs₁ cs₂ : List (Call E)}
    (h₁ : TReach a cs₁ b) (h₂ : TReach b cs₂ c) : TReach a (cs₁ ++ cs₂) c := by
  induction h₁ with
  | nil => exact h₂
  | vis ht _ ih => exact .vis ht (ih h₂)

theorem TReach.congr {a b b' : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs : List (Call E)}
    (h : TReach a cs b) (hb : b = b') : TReach a cs b' := hb ▸ h

theorem TReach.nil_inv {a b : Silmaril.Elgot.ITree.Tree (SigEv E) Y} (h : TReach a [] b) : a = b := by
  cases h; rfl

theorem TReach.cons_inv {a b : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {c : Call E} {cs : List (Call E)}
    (h : TReach a (c :: cs) b) :
    ∃ (R : Type) (e : SigEv E R) (k : R → Silmaril.Elgot.ITree.Tree (SigEv E) Y) (n : R),
      a = Silmaril.Elgot.ITree.vis e k ∧ c = ⟨e.1, cast e.2.symm n⟩ ∧ TReach (k n) cs b := by
  cases h with
  | vis ht h => exact ⟨_, _, _, _, ht, rfl, h⟩

theorem treach_of_path {t : Silmaril.Elgot.ITree.Tree (SigEv E) Z}
    {K : Z → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs : List (Call E)} {v : Z}
    (h : Path t cs (.val v)) : TReach (t >>= K) cs (K v) := by
  generalize hw : (PathEnd.val v : PathEnd Z) = e at h
  induction h with
  | ret ht => cases hw; subst ht; rw [ret_bind']; exact .nil
  | div => cases hw
  | vis ht _ ih => subst ht; rw [vis_bind]; exact .vis rfl (ih hw)

theorem path_of_treach {a b : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs cs' : List (Call E)}
    {r : PathEnd Y} (h : TReach a cs b) (hp : Path b cs' r) : Path a (cs ++ cs') r := by
  induction h with
  | nil => exact hp
  | vis ht _ ih => exact .vis ht (ih hp)

theorem path_nil_val {t : Silmaril.Elgot.ITree.Tree (SigEv E) Y} {v : Y} (h : Path t [] (.val v)) :
    t = ret v := by
  cases h with
  | ret h => exact h

/-- **A loop that continues silently forever diverges.** -/
theorem iter_chain {X B : Type 1} (G : X → Silmaril.Elgot.ITree.Tree (SigEv E) (B ⊕ X))
    (x : Nat → X) (hx : ∀ n, G (x n) = ret (.inr (x (n + 1)))) :
    (Silmaril.Elgot.iter G (x 0) : Silmaril.Elgot.ITree.Tree (SigEv E) B) = diverge := by
  have hu := Silmaril.Elgot.LawfulElgotMonad.uniformity (m := Silmaril.Elgot.ITree.Tree (SigEv E))
    (fun n : ULift.{1} Nat => (pure (.inr ⟨n.down + 1⟩) : Silmaril.Elgot.ITree.Tree (SigEv E)
      (B ⊕ ULift.{1} Nat))) G (fun n => x n.down) (by
      funext n
      simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_apply,
        LawfulMonad.pure_bind, Sum.map_inr]
      exact (hx n.down).symm)
  have h0 := congrFun hu ⟨0⟩
  simp only [Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_apply,
    LawfulMonad.pure_bind] at h0
  rw [← h0]
  exact iterate_pure_loop (fun n : ULift.{1} Nat => (⟨n.down + 1⟩ : ULift.{1} Nat)) ⟨0⟩

end

/-! ## Trees of the constructs, in a continuation -/

section
variable (K : Ex H Res → TT H (Ex H Res))

theorem bind_assoc' {X Y Z : Type 1} (t : TT H X) (g : X → TT H Y) (k : Y → TT H Z) :
    (t >>= g) >>= k = t >>= fun x => g x >>= k :=
  LawfulMonad.bind_assoc t g k

/-- The rest of an operator after its operands, then the list, then `K`. -/
noncomputable def opRest (i : Instr) (es : List BExpr) : Ex H Res → TT H (Ex H Res) :=
  fun v => bc (fun p => tr (thenK (opC callEv i) p.1) p.2) v >>= fun x => contK es x >>= K

theorem tree_op (i : Instr) (args es : List BExpr) (f : Frame) (stk : List Val) (s : Store H) :
    tr (denListE (.op i args :: es) f stk) ⟨s⟩ >>= K =
      tr (denListE args f stk) ⟨s⟩ >>= opRest K i es := by
  rw [tree_cons, denC, tr_bind, bind_assoc', bind_assoc']; rfl

/-- The rest of a block after its body. -/
noncomputable def blockRest (np nr : Nat) (stk : List Val) (es : List BExpr) :
    Ex H Res → TT H (Ex H Res) :=
  fun v => bc (fun p => tr (blockK np nr stk p.1) p.2) v >>= fun x => contK es x >>= K

theorem tree_block {bt : BlockType} {body es : List BExpr} {f : Frame} {stk : List Val}
    {np nr : Nat} (har : arity f bt = some (np, nr)) (s : Store H) :
    tr (denListE (.block bt body :: es) f stk) ⟨s⟩ >>= K =
      tr (denListE body f (stk.take np)) ⟨s⟩ >>= blockRest K np nr stk es := by
  rw [tree_cons, denC]
  simp only [har]
  rw [tr_bind, bind_assoc', bind_assoc']; rfl

/-- The rest of a loop after one iteration's body. -/
noncomputable def loopRest (bt : BlockType) (body : List BExpr) (np nr : Nat) (stk : List Val)
    (es : List BExpr) : Ex H Res → TT H (Ex H Res) :=
  fun v => bc (fun p => tr (loopK np nr stk p.1) p.2) v >>= fun x =>
    bc (fun p => tr (Sum.elim pure (Silmaril.Elgot.iter (LB bt body)) p.1) p.2) x >>= fun x =>
      contK es x >>= K

theorem tree_loop {bt : BlockType} {body es : List BExpr} {f : Frame} {stk : List Val}
    {np nr : Nat} (har : arity f bt = some (np, nr)) (s : Store H) :
    tr (denListE (.loop bt body :: es) f stk) ⟨s⟩ >>= K =
      tr (denListE body f (stk.take np)) ⟨s⟩ >>= loopRest K bt body np nr stk es := by
  rw [tree_cons, denC_loop_eq, iter_LB_unfold, tr_bind]
  simp only [LB, loopBodyC, har]
  rw [tr_bind, bind_assoc', bind_assoc', bind_assoc']; rfl

theorem blockRest_ok {np nr : Nat} {stk : List Val} {es : List BExpr} {f₁ : Frame} {fl : Flow}
    {vs : List Val} (hvs : fl.blockVals = some vs) (σ : St H) :
    blockRest K np nr stk es (.ok (⟨(f₁, fl)⟩, σ)) =
      tr (denListE es f₁ (vs.take nr ++ stk.drop np)) σ >>= K := by
  have : tr (blockK np nr stk ⟨(f₁, fl)⟩ : M (CallSig H) H Res) σ =
      ret (.ok (⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, σ)) := by
    cases fl with
    | normal ws => cases hvs; exact tr_pure _ _
    | brk n ws =>
      cases n with
      | zero => cases hvs; exact tr_pure _ _
      | succ n => cases hvs
    | _ => cases hvs
  simp only [blockRest, bc_ok]
  rw [this, ret_bind', contK_normal]

theorem loopRest_normal {bt : BlockType} {body : List BExpr} {np nr : Nat} {stk : List Val}
    {es : List BExpr} (f₁ : Frame) (vs : List Val) (σ : St H) :
    loopRest K bt body np nr stk es (.ok (⟨(f₁, .normal vs)⟩, σ)) =
      tr (denListE es f₁ (vs.take nr ++ stk.drop np)) σ >>= K := by
  simp only [loopRest, bc_ok]
  rw [show tr (loopK np nr stk ⟨(f₁, .normal vs)⟩ : M (CallSig H) H _) σ =
    ret (.ok (.inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, σ)) from tr_pure _ _, ret_bind',
    bc_ok]
  rw [show tr (Sum.elim pure (Silmaril.Elgot.iter (LB bt body))
      (.inl ⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩ : Res ⊕ _) : M (CallSig H) H Res) σ =
    ret (.ok (⟨(f₁, .normal (vs.take nr ++ stk.drop np))⟩, σ)) from tr_pure _ _, ret_bind',
    contK_normal]

theorem loopRest_brk {bt : BlockType} {body : List BExpr} {np nr : Nat} {stk : List Val}
    {es : List BExpr} (f₁ : Frame) (vs : List Val) (s₁ : Store H) :
    loopRest K bt body np nr stk es (.ok (⟨(f₁, .brk 0 vs)⟩, ⟨s₁⟩)) =
      tr (denListE (.loop bt body :: es) f₁ (vs.take np ++ stk.drop np)) ⟨s₁⟩ >>= K := by
  simp only [loopRest, bc_ok]
  rw [show tr (loopK np nr stk ⟨(f₁, .brk 0 vs)⟩ : M (CallSig H) H _) ⟨s₁⟩ =
    ret (.ok (.inr ⟨(f₁, vs.take np ++ stk.drop np)⟩, ⟨s₁⟩)) from tr_pure _ _, ret_bind', bc_ok,
    tree_cons, denC_loop_eq]
  exact (bind_assoc' _ _ _).symm

theorem opC_flat {i : Instr} (hi : ∀ x, i ≠ .call x) :
    (opC callEv i : Frame → List Val → M (CallSig H) H Res) = flatK i := by
  have : callIdx? i = none := by
    cases i <;> first | rfl | exact absurd rfl (hi _)
  funext f stk
  simp only [opC, this]

theorem opRest_flat {i : Instr} {es : List BExpr} (hi : ∀ x, i ≠ .call x) {s₁ s₂ : Store H}
    {f₁ f₂ : Frame} {stk₁ stk₂ : List Val}
    (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, .normal stk₂)) :
    opRest K i es (.ok (⟨(f₁, .normal stk₁)⟩, ⟨s₁⟩)) = tr (denListE es f₂ stk₂) ⟨s₂⟩ >>= K := by
  simp only [opRest, bc_ok]
  show tr (opC callEv i f₁ stk₁) ⟨s₁⟩ >>= (fun x => contK es x >>= K) = _
  rw [opC_flat hi, tr, run_flatK, hflat]
  show ret (.ok (⟨(f₂, .normal stk₂)⟩, ⟨s₂⟩)) >>= (fun x => contK es x >>= K) = _
  rw [ret_bind', contK_normal]

end

/-! ## Following the witness -/

/-- After answered calls the tree is silent, or it reaches, after at least one answered call,
the tree of a locally diverging problem in some continuation. -/
def W (C : CallRel H) (u : TT H (Ex H Res)) : Prop :=
  (∃ cs, Answered C cs ∧ TReach u cs diverge) ∨
    ∃ cs, cs ≠ [] ∧ Answered C cs ∧ ∃ (s : Store H) (f : Frame) (stk : List Val)
      (es : List BExpr) (K : Ex H Res → TT H (Ex H Res)),
      LocalDivO C s f stk es ∧ TReach u cs (tr (denListE es f stk) ⟨s⟩ >>= K)

theorem W_reach {C : CallRel H} {u u' : TT H (Ex H Res)} {cs : List (Call (CallSig H))}
    (h : TReach u cs u') (hA : Answered C cs) (hW : W C u') : W C u := by
  rcases hW with ⟨cs', hA', h'⟩ | ⟨cs', hne, hA', s, f, stk, es, K, hL, h'⟩
  · exact .inl ⟨cs ++ cs', answered_append.2 ⟨hA, hA'⟩, h.trans h'⟩
  · exact .inr ⟨cs ++ cs', by simp [hne], answered_append.2 ⟨hA, hA'⟩, s, f, stk, es, K, hL,
      h.trans h'⟩

theorem W_adv {C : CallRel H} {u : TT H (Ex H Res)} {cs : List (Call (CallSig H))} {s : Store H}
    {f : Frame} {stk : List Val} {es : List BExpr} {K : Ex H Res → TT H (Ex H Res)}
    (h : TReach u cs (tr (denListE es f stk) ⟨s⟩ >>= K)) (hne : cs ≠ []) (hA : Answered C cs)
    (hL : LocalDivO C s f stk es) : W C u :=
  .inr ⟨cs, hne, hA, s, f, stk, es, K, hL, h⟩

theorem W_diverge {C : CallRel H} : W C diverge := .inl ⟨[], answered_nil, .nil⟩

/-- A fallthrough prefix, as a path of its tree. -/
theorem path_of_normal {C : CallRel H} {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val}
    {es : List BExpr} (h : EvalO C s f stk es (s₁, f₁, .normal stk₁)) :
    ∃ cs, Answered C cs ∧
      Path (tr (denListE es f stk) ⟨s⟩) cs (.val (.ok (⟨(f₁, .normal stk₁)⟩, ⟨s₁⟩))) := by
  obtain ⟨cs, hA, hp⟩ := evalO_path h
  exact ⟨cs, hA, by rw [endR_ok (by simp)] at hp; exact hp⟩

/-- A prefix that ends as a non-trap flow, as a path of its tree. -/
theorem path_of_ok {C : CallRel H} {s s₁ : Store H} {f f₁ : Frame} {stk : List Val} {fl : Flow}
    {es : List BExpr} (h : EvalO C s f stk es (s₁, f₁, fl)) (hfl : fl ≠ .trap) :
    ∃ cs, Answered C cs ∧ Path (tr (denListE es f stk) ⟨s⟩) cs (.val (.ok (⟨(f₁, fl)⟩, ⟨s₁⟩))) := by
  obtain ⟨cs, hA, hp⟩ := evalO_path h
  exact ⟨cs, hA, by rw [endR_ok hfl] at hp; exact hp⟩

theorem blockVals_ne_trap {fl : Flow} {vs : List Val} (h : fl.blockVals = some vs) : fl ≠ .trap := by
  rintro rfl; cases h

/-- An answered call, then the rest of the list. -/
theorem treach_call {C : CallRel H} {x : FuncIdx} {es : List BExpr} {s₁ s₂ : Store H} {f₁ : Frame}
    {stk₁ vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType} {fl : Flow}
    (K : Ex H Res → TT H (Ex H Res))
    (hfi : s₁.func? f₁ x = some (a, fi)) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hcall : C s₁ a (stk₁.take ps.length).reverse (s₂, fl)) (hvs : fl.retVals = some vs) :
    ∃ c, Answered C [c] ∧ TReach (opRest K (.call x) es (.ok (⟨(f₁, .normal stk₁)⟩, ⟨s₁⟩))) [c]
      (tr (denListE es f₁ (vs.take rs.length ++ stk₁.drop ps.length)) ⟨s₂⟩ >>= K) := by
  have ht : opRest K (.call x) es (.ok (⟨(f₁, .normal stk₁)⟩, ⟨s₁⟩)) =
      vis (E := SigEv (CallSig H)) (R := Store H × Flow)
        ⟨(a, (stk₁.take ps.length).reverse, s₁), rfl⟩
        fun n => tr (callAns f₁ stk₁ ps rs n) ⟨s₁⟩ >>= fun x => contK es x >>= K := by
    simp only [opRest, bc_ok]
    show tr (callEv x f₁ stk₁) ⟨s₁⟩ >>= (fun x => contK es x >>= K) = _
    rw [tr_callEv, hfi]
    dsimp only
    rw [hty]
    dsimp only
    exact vis_bind _ _ _
  refine ⟨_, fun c hc => ?_, .vis (n := (s₂, fl)) ht (TReach.nil.congr ?_)⟩
  · rw [List.mem_singleton] at hc
    subst hc
    exact hcall
  · rw [tr_callAns_ok hvs, ret_bind', contK_normal]

/-- One problem state of a loop. -/
abbrev LoopSt (H : Type) : Type := Store H × Frame × List Val

/-- A loop iteration that finishes silently and continues. -/
def SilentNext (bt : BlockType) (body : List BExpr) (y y' : LoopSt H) : Prop :=
  tr (LB bt body ⟨(y.2.1, y.2.2)⟩) ⟨y.1⟩ = ret (.ok (.inr ⟨(y'.2.1, y'.2.2)⟩, ⟨y'.1⟩))

theorem tree_silentNext {bt : BlockType} {body es : List BExpr} {y y' : LoopSt H}
    (h : SilentNext bt body y y') :
    tr (denListE (.loop bt body :: es) y.2.1 y.2.2) ⟨y.1⟩ =
      tr (denListE (.loop bt body :: es) y'.2.1 y'.2.2) ⟨y'.1⟩ := by
  rw [tree_cons, tree_cons, denC_loop_eq, denC_loop_eq, iter_LB_unfold, tr_bind]
  rw [show tr (LB bt body ⟨(y.2.1, y.2.2)⟩) ⟨y.1⟩ = _ from h, ret_bind', bc_ok]
  rfl

theorem loopTree_silentNext {bt : BlockType} {body : List BExpr} {y y' : LoopSt H}
    (h : SilentNext bt body y y') :
    loopTree (LB bt body) (⟨(y.2.1, y.2.2)⟩, ⟨y.1⟩) =
      ret (.inr (⟨(y'.2.1, y'.2.2)⟩, ⟨y'.1⟩)) := by
  unfold loopTree
  rw [show ((LB bt body ⟨(y.2.1, y.2.2)⟩).run ⟨y.1⟩).run = _ from h, ret_bind']
  rfl

/-- **The loop case**: given the property for the body and the rest. -/
theorem loop_case {C : CallRel H} {bt : BlockType} {body es : List BExpr}
    (ihb : ∀ (s : Store H) (f : Frame) (stk : List Val) (K : Ex H Res → TT H (Ex H Res)),
      LocalDivO C s f stk body → W C (tr (denListE body f stk) ⟨s⟩ >>= K))
    (ihe : ∀ (s : Store H) (f : Frame) (stk : List Val) (K : Ex H Res → TT H (Ex H Res)),
      LocalDivO C s f stk es → W C (tr (denListE es f stk) ⟨s⟩ >>= K))
    {s : Store H} {f : Frame} {stk : List Val} (K : Ex H Res → TT H (Ex H Res))
    (h : LocalDivO C s f stk (.loop bt body :: es)) :
    W C (tr (denListE (.loop bt body :: es) f stk) ⟨s⟩ >>= K) := by
  let P : LoopSt H → Prop := fun y => LocalDivO C y.1 y.2.1 y.2.2 (.loop bt body :: es)
  let tY : LoopSt H → TT H (Ex H Res) := fun y =>
    tr (denListE (.loop bt body :: es) y.2.1 y.2.2) ⟨y.1⟩ >>= K
  have one : ∀ y, P y → W C (tY y) ∨ ∃ y', SilentNext bt body y y' ∧ P y' := by
    rintro ⟨s, f, stk⟩ hP
    have hP' := localDivO_iff_step.1 hP
    cases hP' with
    | loop har hb =>
      left
      show W C (tr (denListE (.loop bt body :: es) f stk) ⟨s⟩ >>= K)
      rw [tree_loop K har]
      exact ihb _ _ _ _ hb
    | loopK har hbody hk =>
      left
      show W C (tr (denListE (.loop bt body :: es) f stk) ⟨s⟩ >>= K)
      obtain ⟨cs, hA, hp⟩ := path_of_normal hbody
      rw [tree_loop K har]
      exact W_reach (treach_of_path hp) hA (by rw [loopRest_normal]; exact ihe _ _ _ _ hk)
    | @loopBack _ s₁ _ f₁ _ vs _ _ _ np nr har hbody hk =>
      obtain ⟨cs, hA, hp⟩ := path_of_ok hbody (by simp)
      cases cs with
      | nil =>
        right
        refine ⟨(s₁, f₁, vs.take np ++ stk.drop np), ?_, hk⟩
        show tr (LB bt body ⟨(f, stk)⟩) ⟨s⟩ = _
        simp only [LB, loopBodyC, har]
        rw [tr_bind, path_nil_val hp, ret_bind', bc_ok]
        exact tr_pure _ _
      | cons c cs =>
        left
        show W C (tr (denListE (.loop bt body :: es) f stk) ⟨s⟩ >>= K)
        rw [tree_loop K har]
        exact W_adv ((treach_of_path hp).congr (loopRest_brk K f₁ vs s₁)) (by simp) hA hk
  by_contra hW
  let S := {y : LoopSt H // P y ∧ ¬ W C (tY y)}
  have hnext : ∀ y : S, ∃ y' : S, SilentNext bt body y.1 y'.1 := by
    rintro ⟨y, hP, hnW⟩
    rcases one y hP with hw | ⟨y', hs, hP'⟩
    · exact absurd hw hnW
    · refine ⟨⟨y', hP', fun hw => hnW ?_⟩, hs⟩
      show W C (tr (denListE (.loop bt body :: es) y.2.1 y.2.2) ⟨y.1⟩ >>= K)
      rw [tree_silentNext hs]
      exact hw
  choose nx hnx using hnext
  let y₀ : S := ⟨(s, f, stk), h, hW⟩
  let ch : Nat → LoopSt H := fun n => (nx^[n] y₀).1
  have hch : ∀ n, SilentNext bt body (ch n) (ch (n + 1)) := by
    intro n
    simp only [ch, Function.iterate_succ_apply']
    exact hnx _
  have hdiv := iter_chain (loopTree (LB bt body)) (fun n => (⟨((ch n).2.1, (ch n).2.2)⟩, ⟨(ch n).1⟩))
    (fun n => loopTree_silentNext (hch n))
  apply hW
  rw [tree_cons, denC_loop_eq,
    show tr (Silmaril.Elgot.iter (LB bt body) ⟨(f, stk)⟩) ⟨s⟩ = _ from BodyTrace.run_iter _ _ _]
  have h0 : ch 0 = (s, f, stk) := rfl
  rw [h0] at hdiv
  rw [hdiv, diverge_bind, diverge_bind]
  exact W_diverge

/-- **One step of the witness.** A locally diverging problem, in any continuation, makes its
tree silent after answered calls, or reaches after at least one answered call the tree of a
locally diverging problem. -/
theorem local_step {C : CallRel H} : ∀ (es : List BExpr) (s : Store H) (f : Frame)
    (stk : List Val) (K : Ex H Res → TT H (Ex H Res)),
    LocalDivO C s f stk es → W C (tr (denListE es f stk) ⟨s⟩ >>= K)
  | [], s, f, stk, K, h => by
    have := localDivO_iff_step.1 h; cases this
  | .op i args :: es, s, f, stk, K, h => by
    have hs := localDivO_iff_step.1 h
    rw [tree_op]
    cases hs with
    | args ha => exact local_step args s f stk _ ha
    | callee _ _ _ _ hy => exact hy.elim
    | callRet hargs hfi hty hcall hvs hk =>
      obtain ⟨cs, hA, hp⟩ := path_of_normal hargs
      obtain ⟨c, hc, hr⟩ := treach_call (es := es) K hfi hty hcall hvs
      exact W_adv ((treach_of_path hp).trans hr) (by simp) (answered_append.2 ⟨hA, hc⟩) hk
    | opK hi hargs hflat hk =>
      obtain ⟨cs, hA, hp⟩ := path_of_normal hargs
      exact W_reach (treach_of_path hp) hA
        (by rw [opRest_flat K hi hflat]; exact local_step es _ _ _ K hk)
  | .block bt body :: es, s, f, stk, K, h => by
    have hs := localDivO_iff_step.1 h
    cases hs with
    | block har hb => rw [tree_block K har]; exact local_step body _ _ _ _ hb
    | blockK har hbody hvs hk =>
      obtain ⟨cs, hA, hp⟩ := path_of_ok hbody (blockVals_ne_trap hvs)
      rw [tree_block K har]
      exact W_reach (treach_of_path hp) hA
        (by rw [blockRest_ok K hvs]; exact local_step es _ _ _ K hk)
  | .loop bt body :: es, s, f, stk, K, h =>
    loop_case (fun s f stk K h => local_step body s f stk K h)
      (fun s f stk K h => local_step es s f stk K h) K h
  | .if_ bt c t el :: es, s, f, stk, K, h => by
    have hs := localDivO_iff_step.1 h
    rw [tree_cons, denC, tr_bind, bind_assoc', bind_assoc']
    cases hs with
    | cond hc => exact local_step c s f stk _ hc
    | @arm _ s₁ _ f₁ _ stk₁ cv b _ _ _ _ _ np nr hc hb har ha =>
      obtain ⟨cs, hA, hp⟩ := path_of_normal hc
      refine W_reach (treach_of_path hp) hA ?_
      simp only [bc_ok]
      rw [hb, har]
      dsimp only
      rw [tr_bind, bind_assoc']
      cases b with
      | true => exact local_step t _ _ _ _ ha
      | false => exact local_step el _ _ _ _ ha
    | @ifK _ s₁ s₂ _ f₁ f₂ _ stk₁ vs cv b _ _ _ _ _ np nr fl hc hb har harm hvs hk =>
      obtain ⟨cs, hA, hp⟩ := path_of_normal hc
      obtain ⟨cs₂, hA₂, hp₂⟩ := path_of_ok harm (blockVals_ne_trap hvs)
      refine W_reach (treach_of_path hp) hA ?_
      simp only [bc_ok]
      rw [hb, har]
      dsimp only
      rw [tr_bind, bind_assoc']
      have hp₂' : Path (tr (if b then denListC callEv t f₁ (stk₁.take np)
          else denListC callEv el f₁ (stk₁.take np)) ⟨s₁⟩) cs₂
          (.val (.ok (⟨(f₂, fl)⟩, ⟨s₂⟩))) := by
        cases b <;> exact hp₂
      refine W_reach (treach_of_path hp₂') hA₂ ?_
      show W C (blockRest K np nr stk₁ es (.ok (⟨(f₂, fl)⟩, ⟨s₂⟩)))
      rw [blockRest_ok K hvs]
      exact local_step es _ _ _ K hk
  | .tryTable .. :: es, s, f, stk, K, h => by
    have := localDivO_iff_step.1 h; cases this
termination_by es => sizeOf es

/-! ## Assembling the run -/

/-- An answered call. -/
def AnsC (C : CallRel H) (c : Call (CallSig H)) : Prop := C c.1.2.2 c.1.1 c.1.2.1 c.2

/-- After answered calls, silent, or at the tree of a locally diverging problem. -/
def G (C : CallRel H) (u : TT H (Ex H Res)) : Prop :=
  ∃ cs, Answered C cs ∧ (TReach u cs diverge ∨ ∃ (s : Store H) (f : Frame) (stk : List Val)
    (es : List BExpr) (K : Ex H Res → TT H (Ex H Res)),
    LocalDivO C s f stk es ∧ TReach u cs (tr (denListE es f stk) ⟨s⟩ >>= K))

theorem G_cons {C : CallRel H} {u t' : TT H (Ex H Res)} {c : Call (CallSig H)}
    {cs : List (Call (CallSig H))} (hA : Answered C (c :: cs)) (h : TReach u (c :: cs) t')
    (hG : ∀ u', TReach u' cs t' → Answered C cs → G C u') :
    ∃ (R : Type) (e : SigEv (CallSig H) R) (k : R → TT H (Ex H Res)) (n : R),
      u = vis e k ∧ AnsC C ⟨e.1, cast e.2.symm n⟩ ∧ G C (k n) := by
  obtain ⟨R, e, k, n, hu, rfl, hk⟩ := h.cons_inv
  obtain ⟨h1, h2⟩ := answered_cons.1 hA
  exact ⟨R, e, k, n, hu, h1, hG _ hk h2⟩

theorem G_step {C : CallRel H} {u : TT H (Ex H Res)} (hG : G C u) :
    u = diverge ∨ ∃ (R : Type) (e : SigEv (CallSig H) R) (k : R → TT H (Ex H Res)) (n : R),
      u = vis e k ∧ AnsC C ⟨e.1, cast e.2.symm n⟩ ∧ G C (k n) := by
  obtain ⟨cs, hA, h⟩ := hG
  cases cs with
  | nil =>
    rcases h with h | ⟨s, f, stk, es, K, hL, h⟩
    · exact .inl h.nil_inv
    · rw [h.nil_inv]
      rcases local_step es s f stk K hL with ⟨cs', hA', h'⟩ | ⟨cs', hne, hA', s', f', stk', es', K',
        hL', h'⟩
      · cases cs' with
        | nil => exact .inl h'.nil_inv
        | cons c cs' => exact .inr (G_cons hA' h' fun u' hu hA'' => ⟨cs', hA'', .inl hu⟩)
      · cases cs' with
        | nil => exact absurd rfl hne
        | cons c cs' =>
          exact .inr (G_cons hA' h' fun u' hu hA'' => ⟨cs', hA'', .inr ⟨s', f', stk', es', K', hL', hu⟩⟩)
  | cons c cs =>
    rcases h with h | ⟨s, f, stk, es, K, hL, h⟩
    · exact .inr (G_cons hA h fun u' hu hA'' => ⟨cs, hA'', .inl hu⟩)
    · exact .inr (G_cons hA h fun u' hu hA'' => ⟨cs, hA'', .inr ⟨s, f, stk, es, K, hL, hu⟩⟩)

/-- **Local divergence is silent divergence after answered calls, or an infinite answered
run**, any oracle. -/
theorem exposed_of_localDivO {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (hL : LocalDivO C s f stk es) :
    (∃ cs, Answered C cs ∧ Path (tr (denListE es f stk) ⟨s⟩) cs .div) ∨
      ∃ ω, AnsweredS C ω ∧ InfPath (tr (denListE es f stk) ⟨s⟩) ω := by
  classical
  let t₀ := tr (denListE es f stk) ⟨s⟩
  have hG₀ : G C t₀ :=
    ⟨[], answered_nil, .inr ⟨s, f, stk, es, pure, hL, TReach.nil.congr (bind_pure t₀).symm⟩⟩
  let Sg := {u : TT H (Ex H Res) // G C u}
  have hstep : ∀ u : Sg, u.1 ≠ diverge → ∃ (R : Type) (e : SigEv (CallSig H) R)
      (k : R → TT H (Ex H Res)) (n : R),
      u.1 = vis e k ∧ AnsC C ⟨e.1, cast e.2.symm n⟩ ∧ G C (k n) :=
    fun u hu => (G_step u.2).resolve_left hu
  choose R e k n hu hc hk using hstep
  let nx : Sg → Sg := fun u => if h : u.1 = diverge then u else ⟨k u h (n u h), hk u h⟩
  have hnx : ∀ (u : Sg) (h : u.1 ≠ diverge), (nx u).1 = k u h (n u h) := by
    intro u h
    show (if h : u.1 = diverge then u else ⟨k u h (n u h), hk u h⟩).1 = _
    rw [dite_eq_right_of_eq_false (eq_false h)]
  let u₀ : Sg := ⟨t₀, hG₀⟩
  by_cases hd : ∃ m, (nx^[m] u₀).1 = diverge
  · left
    obtain ⟨m, hm⟩ := hd
    have key : ∀ m (u : Sg), (nx^[m] u).1 = diverge →
        ∃ cs, Answered C cs ∧ Path u.1 cs .div := by
      intro m
      induction m with
      | zero => intro u hu; exact ⟨[], answered_nil, .div hu⟩
      | succ m ih =>
        intro u hm
        by_cases h : u.1 = diverge
        · exact ⟨[], answered_nil, .div h⟩
        · rw [Function.iterate_succ_apply] at hm
          obtain ⟨cs, hA, hp⟩ := ih (nx u) hm
          rw [hnx u h] at hp
          exact ⟨_ :: cs, answered_cons.2 ⟨hc u h, hA⟩, .vis (hu u h) hp⟩
    exact key m u₀ hm
  · right
    push Not at hd
    refine ⟨fun m => ⟨(e _ (hd m)).1, cast (e _ (hd m)).2.symm (n _ (hd m))⟩,
      fun m => hc _ (hd m), fun m => (nx^[m] u₀).1, rfl, fun m => ?_⟩
    refine ⟨R _ (hd m), e _ (hd m), k _ (hd m), n _ (hd m), hu _ (hd m), rfl, ?_⟩
    show (nx^[m + 1] u₀).1 = _
    rw [Function.iterate_succ_apply']
    exact hnx _ (hd m)

end Silmaril.Proofs.Wasm.Abstract.FullObsNative
