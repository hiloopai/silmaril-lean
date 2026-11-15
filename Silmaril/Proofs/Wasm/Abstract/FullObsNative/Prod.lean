module

public import Silmaril.Proofs.Wasm.Abstract.FullObsNative.Tree
public import Silmaril.Wasm.Abstract.DivO.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.FullObsNative.Thms`: **productive local divergence**, any
oracle. An infinite run of the exposed native body whose call events are all answered by `C`
is local divergence `LocalDivO C` of the problem (`localDivO_of_prod`), by coinduction on
`LocalDivO`. The closed-oracle case is `StoreCall.localDiv_of_exposedInf`; the proof here
uses public headers only.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FullObsNative

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree
open Silmaril.Wasm.Interp (Problem)

variable {H : Type}

/-! ## Ends of `EvalO` outcomes -/

theorem endR_ok {s₁ : Store H} {f₁ : Frame} {fl : Flow} (h : fl ≠ .trap) :
    endR (s₁, f₁, fl) = .val (.ok (⟨(f₁, fl)⟩, ⟨s₁⟩)) := by
  cases fl <;> first | exact absurd rfl h | rfl

theorem endR_ok_inv {r : Store H × Frame × Flow} {f₁ : Frame} {fl : Flow} {σ : St H}
    (h : endR r = .val (.ok (⟨(f₁, fl)⟩, σ))) : r = (σ.down, f₁, fl) ∧ fl ≠ .trap := by
  obtain ⟨s', f', fl'⟩ := r
  obtain ⟨s₁⟩ := σ
  cases fl' with
  | trap => cases h
  | _ =>
    simp only [endR, PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq, ULift.up.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, by simp⟩

theorem endR_err_inv {r : Store H × Frame × Flow} (h : endR r = .val (.error ⟨⟩)) :
    r.2.2 = .trap := by
  obtain ⟨s', f', fl'⟩ := r
  cases fl' <;> first | rfl | cases h

/-! ## One tree as a list -/

theorem tr_single (e : BExpr) (f : Frame) (stk : List Val) (σ : St H) :
    tr (denListE (H := H) [e] f stk) σ = tr (denC callEv e f stk) σ := by
  show tr (denListC callEv [e] f stk) σ = _
  rw [denListC_single]

/-- A finished answered path of one tree is an `EvalO` outcome of the singleton list. -/
theorem evalO_of_path1 {C : CallRel H} {e : BExpr} {s : Store H} {f : Frame} {stk : List Val}
    {cs : List (Call (CallSig H))} {v : Ex H Res} (hA : Answered C cs)
    (h : Path (tr (denC callEv e f stk) ⟨s⟩) cs (.val v)) :
    ∃ r, EvalO C s f stk [e] r ∧ endR r = .val v :=
  path_evalO hA (by show Path (tr (denListE [e] f stk) ⟨s⟩) cs (.val v); rw [tr_single]; exact h)
    (by simp)

/-- A finished answered path of a list is an `EvalO` outcome. -/
theorem evalO_of_path {C : CallRel H} {es : List BExpr} {s : Store H} {f : Frame} {stk : List Val}
    {cs : List (Call (CallSig H))} {v : Ex H Res} (hA : Answered C cs)
    (h : Path (tr (denListE es f stk) ⟨s⟩) cs (.val v)) :
    ∃ r, EvalO C s f stk es r ∧ endR r = .val v :=
  path_evalO hA h (by simp)

/-- A fallthrough of a list, from a finished answered path. -/
theorem evalO_of_path_ok {C : CallRel H} {es : List BExpr} {s : Store H} {f : Frame}
    {stk : List Val} {cs : List (Call (CallSig H))} {f₁ : Frame} {fl : Flow} {σ : St H}
    (hA : Answered C cs) (h : Path (tr (denListE es f stk) ⟨s⟩) cs (.val (.ok (⟨(f₁, fl)⟩, σ)))) :
    EvalO C s f stk es (σ.down, f₁, fl) := by
  obtain ⟨r, hev, hend⟩ := evalO_of_path hA h
  obtain ⟨rfl, -⟩ := endR_ok_inv hend
  exact hev

/-! ## Advancing past a finished tree -/

/-- **A finished tree, then the rest.** A tree that falls through by `EvalO C`, followed by the
rest of the list in `X`, is an unfolding step; a loop that falls through after iterating is
read by `hloop`. -/
theorem adv {C : CallRel H} {X : Problem H} {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val}
    {e : BExpr} {es : List BExpr} (hev : EvalO C s f stk [e] (s₁, f₁, .normal stk₁))
    (hX : X s₁ f₁ stk₁ es)
    (hloop : ∀ (bt : BlockType) (body : List BExpr) (s' : Store H) (f' : Frame) (stk' : List Val),
      EvalO C s' f' stk' [.loop bt body] (s₁, f₁, .normal stk₁) → X s' f' stk' (.loop bt body :: es)) :
    DivStepO C X ⊥ s f stk (e :: es) := by
  cases hev with
  | argsAbort _ hfl => exact absurd trivial hfl
  | callOk hargs hfi hty hcall hvs hk => cases hk; exact .callRet hargs hfi hty hcall hvs hX
  | opOk hi hargs hflat hk => cases hk; exact .opK hi hargs hflat hX
  | opStop _ _ _ hfl => exact absurd trivial hfl
  | blockOk har hbody hvs hk => cases hk; exact .blockK har hbody hvs hX
  | blockEsc _ _ hfl => exact hfl.elim
  | loopOk har hbody hk => cases hk; exact .loopK har hbody hX
  | loopBack har hbody hk => exact .loopBack har hbody (hloop _ _ _ _ _ hk)
  | loopEsc _ _ hfl => exact hfl.elim
  | ifOk hc hb har harm hvs hk => cases hk; exact .ifK hc hb har harm hvs hX
  | ifEsc _ _ _ _ hfl => exact hfl.elim
  | ifAbort _ hfl => exact absurd trivial hfl

/-! ## Event-free continuations -/

theorem quiet_blockK (np nr : Nat) (stk : List Val) (r : Res) (σ : St H) :
    Quiet (tr (blockK np nr stk r : M (CallSig H) H Res) σ) := by
  obtain ⟨⟨f, fl⟩⟩ := r
  cases fl with
  | brk n vs => cases n <;> exact .inr ⟨_, tr_pure _ _⟩
  | _ => exact .inr ⟨_, tr_pure _ _⟩

theorem quiet_loopK (np nr : Nat) (stk : List Val) (r : Res) (σ : St H) :
    Quiet (tr (loopK np nr stk r : M (CallSig H) H _) σ) := by
  obtain ⟨⟨f, fl⟩⟩ := r
  cases fl with
  | brk n vs => cases n <;> exact .inr ⟨_, tr_pure _ _⟩
  | _ => exact .inr ⟨_, tr_pure _ _⟩

theorem not_infPath_bc {X Y : Type 1} {g : X × St H → TT H (Ex H Y)} {v : Ex H X}
    {ω : Stream' (Call (CallSig H))} (hg : ∀ p ω, ¬ InfPath (g p) ω) : ¬ InfPath (bc g v) ω := by
  cases v with
  | error e => exact not_infPath_ret
  | ok p => exact hg p ω

theorem not_infPath_thenK {k : Frame → List Val → M (CallSig H) H Res}
    (hk : ∀ f stk σ ω, ¬ InfPath (tr (k f stk) σ) ω) (r : Res) (σ : St H)
    {ω : Stream' (Call (CallSig H))} : ¬ InfPath (tr (thenK k r) σ) ω := by
  obtain ⟨⟨f, fl⟩⟩ := r
  cases fl with
  | normal stk => exact hk f stk σ ω
  | _ => exact not_infPath_ret

/-- A loop iteration that continues: its body ended in `br 0`. -/
theorem loopK_inr {np nr : Nat} {stk : List Val} {r : Res} {σ σ₁ : St H}
    {c : ULift.{1} (Frame × List Val)} {cs : List (Call (CallSig H))}
    (h : Path (tr (loopK np nr stk r : M (CallSig H) H _) σ) cs (.val (.ok (.inr c, σ₁)))) :
    ∃ f₁ vs, r = ⟨(f₁, .brk 0 vs)⟩ ∧ c = ⟨(f₁, vs.take np ++ stk.drop np)⟩ ∧ σ₁ = σ := by
  obtain ⟨⟨f, fl⟩⟩ := r
  cases fl with
  | brk n vs =>
    cases n with
    | zero =>
      rw [show tr (loopK np nr stk ⟨(f, .brk 0 vs)⟩ : M (CallSig H) H _) σ =
        ret (.ok (.inr ⟨(f, vs.take np ++ stk.drop np)⟩, σ)) from tr_pure _ _, path_ret_iff] at h
      obtain ⟨-, h⟩ := h
      simp only [PathEnd.val.injEq, Except.ok.injEq, Prod.mk.injEq, Sum.inr.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨f, vs, rfl, rfl, rfl⟩
    | succ n =>
      rw [show tr (loopK np nr stk ⟨(f, .brk (n + 1) vs)⟩ : M (CallSig H) H _) σ =
        ret (.ok (.inl ⟨(f, .brk n vs)⟩, σ)) from tr_pure _ _, path_ret_iff] at h
      simp at h
  | normal vs =>
    rw [show tr (loopK np nr stk ⟨(f, .normal vs)⟩ : M (CallSig H) H _) σ =
      ret (.ok (.inl ⟨(f, .normal (vs.take nr ++ stk.drop np))⟩, σ)) from tr_pure _ _,
      path_ret_iff] at h
    simp at h
  | ret vs =>
    rw [show tr (loopK np nr stk ⟨(f, .ret vs)⟩ : M (CallSig H) H _) σ =
      ret (.ok (.inl ⟨(f, .ret vs)⟩, σ)) from tr_pure _ _, path_ret_iff] at h
    simp at h
  | trap =>
    rw [show tr (loopK np nr stk ⟨(f, .trap)⟩ : M (CallSig H) H _) σ =
      ret (.ok (.inl ⟨(f, .trap)⟩, σ)) from tr_pure _ _, path_ret_iff] at h
    simp at h
  | throw t =>
    rw [show tr (loopK np nr stk ⟨(f, .throw t)⟩ : M (CallSig H) H _) σ =
      ret (.ok (.inl ⟨(f, .throw t)⟩, σ)) from tr_pure _ _, path_ret_iff] at h
    simp at h

/-! ## Productive runs -/

/-- The exposed body has an infinite run with every call event answered by `C`. -/
def ProdO (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) : Prop :=
  ∃ ω, AnsweredS C ω ∧ InfPath (tr (denListE es f stk) ⟨s⟩) ω

/-- A loop iteration, as a body. -/
noncomputable abbrev LB (bt : BlockType) (body : List BExpr) :
    ULift.{1} (Frame × List Val) → M (CallSig H) H (Res ⊕ ULift.{1} (Frame × List Val)) :=
  loopBodyC callEv bt body

theorem denC_loop_eq (bt : BlockType) (body : List BExpr) (f : Frame) (stk : List Val) :
    (denC callEv (.loop bt body) f stk : M (CallSig H) H Res) =
      Silmaril.Elgot.iter (LB bt body) ⟨(f, stk)⟩ := by
  rw [denC]; rfl

theorem iter_LB_unfold (bt : BlockType) (body : List BExpr) (c : ULift.{1} (Frame × List Val)) :
    (Silmaril.Elgot.iter (LB (H := H) bt body) c : M (CallSig H) H Res) =
      LB bt body c >>= Sum.elim pure (Silmaril.Elgot.iter (LB bt body)) :=
  congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint (LB bt body)) c

/-- A finished iteration that continues: its body ended in `br 0`. -/
theorem lb_cont {C : CallRel H} {bt : BlockType} {body : List BExpr} {f : Frame} {stk : List Val}
    {s : Store H} {cs : List (Call (CallSig H))} {c : ULift.{1} (Frame × List Val)} {σ₁ : St H}
    (hA : Answered C cs)
    (h : Path (tr (LB bt body ⟨(f, stk)⟩) ⟨s⟩) cs (.val (.ok (.inr c, σ₁)))) :
    ∃ np nr f₁ vs, arity f bt = some (np, nr) ∧
      EvalO C s f (stk.take np) body (σ₁.down, f₁, .brk 0 vs) ∧
      c = ⟨(f₁, vs.take np ++ stk.drop np)⟩ := by
  simp only [LB, loopBodyC] at h
  cases har : arity f bt with
  | none =>
    simp only [har] at h
    obtain ⟨-, h⟩ := path_diverge_inv h
    cases h
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    rw [tr_bind] at h
    obtain ⟨cs₁, cs₂, w, rfl, h₁, h₂⟩ := path_bind_val_inv h
    cases w with
    | error e =>
      obtain ⟨-, h⟩ := path_ret_iff.1 h₂
      cases h
    | ok p =>
      obtain ⟨rb, σb⟩ := p
      obtain ⟨f₁, vs, rfl, rfl, rfl⟩ := loopK_inr h₂
      exact ⟨np, nr, f₁, vs, rfl,
        evalO_of_path_ok (answered_append.1 hA).1 h₁, rfl⟩

theorem prod_op {C : CallRel H} {i : Instr} {args es : List BExpr} {s : Store H} {f : Frame}
    {stk : List Val} {ω : Stream' (Call (CallSig H))} (hA : AnsweredS C ω)
    (h : InfPath (tr (denC callEv (.op i args) f stk) ⟨s⟩) ω) :
    DivStepO C (ProdO C) ⊥ s f stk (.op i args :: es) := by
  rw [denC, tr_bind] at h
  rcases infPath_bind_iff.1 h with h₁ | ⟨cs, v, ω', -, h₂, -⟩
  · exact .args ⟨ω, hA, h₁⟩
  · exact absurd h₂ (not_infPath_bc fun p _ => not_infPath_thenK
      (fun f stk σ _ => not_infPath_opC i f stk σ) p.1 p.2)

theorem prod_block {C : CallRel H} {bt : BlockType} {body es : List BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {ω : Stream' (Call (CallSig H))} (hA : AnsweredS C ω)
    (h : InfPath (tr (denC callEv (.block bt body) f stk) ⟨s⟩) ω) :
    DivStepO C (ProdO C) ⊥ s f stk (.block bt body :: es) := by
  rw [denC] at h
  cases har : arity f bt with
  | none => simp only [har] at h; exact absurd h not_infPath_diverge
  | some p =>
    obtain ⟨np, nr⟩ := p
    simp only [har] at h
    rw [tr_bind] at h
    rcases infPath_bind_iff.1 h with h₁ | ⟨cs, v, ω', -, h₂, -⟩
    · exact .block har ⟨ω, hA, h₁⟩
    · exact absurd h₂ (not_infPath_bc fun p _ => (quiet_blockK np nr stk p.1 p.2).not_infPath)

theorem prod_if {C : CallRel H} {bt : BlockType} {c t el es : List BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {ω : Stream' (Call (CallSig H))} (hA : AnsweredS C ω)
    (h : InfPath (tr (denC callEv (.if_ bt c t el) f stk) ⟨s⟩) ω) :
    DivStepO C (ProdO C) ⊥ s f stk (.if_ bt c t el :: es) := by
  rw [denC, tr_bind] at h
  rcases infPath_bind_iff.1 h with h₁ | ⟨cs, v, ω', hp, h₂, rfl⟩
  · exact .cond ⟨ω, hA, h₁⟩
  · obtain ⟨hcs, hω'⟩ := answeredS_append.1 hA
    cases v with
    | error e => exact absurd h₂ not_infPath_ret
    | ok p =>
      obtain ⟨⟨⟨f₁, fl⟩⟩, σ₁⟩ := p
      have hev := evalO_of_path_ok hcs hp
      rw [bc_ok] at h₂
      cases fl with
      | normal vs =>
        cases vs with
        | nil => exact absurd h₂ not_infPath_diverge
        | cons cv stk₁ =>
          dsimp only at h₂
          cases hb : truthy cv with
          | none => simp only [hb] at h₂; exact absurd h₂ not_infPath_diverge
          | some b =>
            cases har : arity f₁ bt with
            | none => simp only [hb, har] at h₂; exact absurd h₂ not_infPath_diverge
            | some q =>
              obtain ⟨np, nr⟩ := q
              simp only [hb, har] at h₂
              rw [tr_bind] at h₂
              rcases infPath_bind_iff.1 h₂ with h₃ | ⟨_, v', _, -, h₄, -⟩
              · refine .arm hev hb har ⟨ω', hω', ?_⟩
                cases b <;> exact h₃
              · exact absurd h₄
                  (not_infPath_bc fun p _ => (quiet_blockK np nr stk₁ p.1 p.2).not_infPath)
      | _ => exact absurd h₂ not_infPath_ret

theorem prod_loop {C : CallRel H} {bt : BlockType} {body es : List BExpr} {s : Store H}
    {f : Frame} {stk : List Val} {ω : Stream' (Call (CallSig H))} (hA : AnsweredS C ω)
    (h : InfPath (tr (denC callEv (.loop bt body) f stk) ⟨s⟩) ω) :
    DivStepO C (ProdO C) ⊥ s f stk (.loop bt body :: es) := by
  rw [denC_loop_eq, iter_LB_unfold, tr_bind] at h
  rcases infPath_bind_iff.1 h with h₁ | ⟨cs, v, ω', hp, h₂, rfl⟩
  · simp only [LB, loopBodyC] at h₁
    cases har : arity f bt with
    | none => simp only [har] at h₁; exact absurd h₁ not_infPath_diverge
    | some p =>
      obtain ⟨np, nr⟩ := p
      simp only [har] at h₁
      rw [tr_bind] at h₁
      rcases infPath_bind_iff.1 h₁ with h₃ | ⟨_, _, _, -, h₄, -⟩
      · exact .loop har ⟨ω, hA, h₃⟩
      · exact absurd h₄ (not_infPath_bc fun p _ => (quiet_loopK np nr stk p.1 p.2).not_infPath)
  · obtain ⟨hcs, hω'⟩ := answeredS_append.1 hA
    cases v with
    | error e => exact absurd h₂ not_infPath_ret
    | ok p =>
      obtain ⟨y | c', σ₁⟩ := p
      · exact absurd h₂ not_infPath_ret
      · rw [bc_ok] at h₂
        obtain ⟨np, nr, f₁, vs, har, hbody, rfl⟩ := lb_cont hcs hp
        refine .loopBack har hbody ⟨ω', hω', ?_⟩
        rw [tree_cons]
        refine infPath_bind_left ?_
        rw [denC_loop_eq]
        exact h₂

theorem prod_head {C : CallRel H} {e : BExpr} {es : List BExpr} {s : Store H} {f : Frame}
    {stk : List Val} {ω : Stream' (Call (CallSig H))} (hA : AnsweredS C ω)
    (h : InfPath (tr (denC callEv e f stk) ⟨s⟩) ω) :
    DivStepO C (ProdO C) ⊥ s f stk (e :: es) := by
  cases e with
  | op i args => exact prod_op hA h
  | block bt body => exact prod_block hA h
  | loop bt body => exact prod_loop hA h
  | if_ bt c t el => exact prod_if hA h
  | tryTable bt cs body => rw [denC] at h; exact absurd h not_infPath_diverge

/-- A loop that falls through after iterating, followed by a productive rest. -/
theorem prod_loop_rest {C : CallRel H} {bt : BlockType} {body es : List BExpr} {s s₁ : Store H}
    {f f₁ : Frame} {stk stk₁ : List Val}
    (hev : EvalO C s f stk [.loop bt body] (s₁, f₁, .normal stk₁)) (hX : ProdO C s₁ f₁ stk₁ es) :
    ProdO C s f stk (.loop bt body :: es) := by
  obtain ⟨ω, hA, h⟩ := hX
  obtain ⟨cs, hcs, hp⟩ := evalO_path hev
  change Path (tr (denListE [_] f stk) ⟨s⟩) cs _ at hp
  rw [tr_single, endR_ok (by simp)] at hp
  refine ⟨cs ++ₛ ω, answeredS_append.2 ⟨hcs, hA⟩, ?_⟩
  rw [tree_cons]
  exact infPath_bind_right hp (by rw [contK_normal]; exact h)

theorem prod_step {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : ProdO C s f stk es) : DivStepO C (ProdO C) ⊥ s f stk es := by
  obtain ⟨ω, hA, h⟩ := h
  cases es with
  | nil =>
    show DivStepO C (ProdO C) ⊥ s f stk []
    rw [show tr (denListE (H := H) [] f stk) ⟨s⟩ = ret (.ok (⟨(f, .normal stk)⟩, ⟨s⟩)) from by
      show tr (denListC callEv [] f stk) ⟨s⟩ = _
      rw [denListC_nil]; rfl] at h
    exact absurd h not_infPath_ret
  | cons e es =>
    rw [tree_cons] at h
    rcases infPath_bind_iff.1 h with h₁ | ⟨cs, v, ω', hp, h₂, rfl⟩
    · exact prod_head hA h₁
    · obtain ⟨hcs, hω'⟩ := answeredS_append.1 hA
      cases v with
      | error e => exact absurd h₂ not_infPath_ret
      | ok p =>
        obtain ⟨⟨⟨f₁, fl⟩⟩, σ₁⟩ := p
        obtain ⟨r, hev, hend⟩ := evalO_of_path1 hcs hp
        obtain ⟨rfl, -⟩ := endR_ok_inv hend
        by_cases hn : fl.IsNormal
        · obtain ⟨stk₁, rfl⟩ : ∃ stk₁, fl = .normal stk₁ := by
            cases fl <;> first | exact ⟨_, rfl⟩ | exact absurd hn id
          rw [contK_normal] at h₂
          exact adv hev ⟨ω', hω', h₂⟩ fun _ _ _ _ _ hl => prod_loop_rest hl ⟨ω', hω', h₂⟩
        · rw [contK_pass es hn] at h₂
          exact absurd h₂ not_infPath_ret

/-- **Productive local divergence, any oracle.** -/
theorem localDivO_of_prod {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} (h : ProdO C s f stk es) : LocalDivO C s f stk es :=
  localDivO_of_coind (X := ProdO C) (fun _ _ _ _ h => prod_step h) s f stk es h

end Silmaril.Proofs.Wasm.Abstract.FullObsNative
