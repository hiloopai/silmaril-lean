module

public import Silmaril.Wasm.Abstract.StoreCall.Thms
public import Silmaril.Wasm.Abstract.StoreBody.Thms
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Semantics.ITree.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.FullObsNative.Thms`: tree-level tools for the exposed native
body `StoreCall.denListE`, from public headers only. Paths and infinite runs through binds,
answered streams, the tree of one construct of a list (`tree_cons`), and the event-free pieces
(`flatK`, `callAns`, `stuck`, `pure`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FullObsNative

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree

variable {H : Type}

/-- Trees of exposed bodies. -/
abbrev TT (H : Type) : Type 1 → Type 1 := Silmaril.Elgot.ITree.Tree (SigEv (CallSig H))

/-- The results of an exposed body's tree. -/
abbrev Ex (H : Type) (X : Type 1) : Type 1 := Except PUnit.{2} (X × St H)

/-- Trees of exposed bodies with results in `X`. -/
abbrev T (H : Type) (X : Type 1) : Type 1 := TT H (Ex H X)

theorem ret_bind' {E : Type → Type} {Y Z : Type 1} (a : Z) (k : Z → Silmaril.Elgot.ITree.Tree E Y) :
    (ret a >>= k) = k a :=
  LawfulMonad.pure_bind a k

/-- The tree of a body from a state. -/
noncomputable abbrev tr {X : Type 1} (x : M (CallSig H) H X) (σ : St H) : TT H (Ex H X) :=
  (x.run σ).run

/-- The continuation of a bind at the tree level. -/
noncomputable def bc {X Y : Type 1} (g : X × St H → TT H (Ex H Y)) : Except PUnit.{2} (X × St H) → TT H (Ex H Y)
  | .ok p => g p
  | .error e => ret (.error e)

theorem tr_bind {X Y : Type 1} (x : M (CallSig H) H X) (k : X → M (CallSig H) H Y) (σ : St H) :
    tr (x >>= k) σ = tr x σ >>= bc (fun p => tr (k p.1) p.2) := by
  show (ExceptT.run ((x >>= k).run σ)) = _
  simp only [StateT.run_bind, ExceptT.run_bind]
  congr 1
  funext r
  cases r <;> rfl

theorem tr_pure {X : Type 1} (a : X) (σ : St H) : tr (pure a : M (CallSig H) H X) σ = ret (Except.ok (a, σ)) :=
  rfl

theorem tr_stuck {X : Type 1} (σ : St H) : tr (stuck : M (CallSig H) H X) σ = diverge := rfl

theorem tr_getState (σ : St H) : tr (getState : M (CallSig H) H (St H)) σ = ret (.ok (σ, σ)) := rfl

theorem tr_setState (σ σ' : St H) :
    tr (setState σ' : M (CallSig H) H PUnit) σ = ret (.ok (⟨⟩, σ')) := rfl

theorem tr_trap {X : Type 1} (σ : St H) : tr (trap ⟨⟩ : M (CallSig H) H X) σ = ret (.error ⟨⟩) := by
  simp [tr, trap, throw, throwThe, MonadExceptOf.throw]; rfl

theorem tr_callImport (m : (CallSig H).Op) (σ : St H) :
    tr (callImport m : M (CallSig H) H _) σ =
      vis (E := SigEv (CallSig H)) (R := (CallSig H).Ar m) ⟨m, rfl⟩ fun n => ret (.ok (ULift.up n, σ)) :=
  rfl

theorem bc_ok {X Y : Type 1} (g : X × St H → TT H (Ex H Y)) (p : X × St H) : bc g (.ok p) = g p := rfl

/-! ## Paths and infinite runs -/

section
variable {E : Sig.{0}} {Y Z : Type 1}

theorem not_path_diverge_val {cs : List (Call E)} {v : Y} :
    ¬ Path (diverge : Silmaril.Elgot.ITree.Tree (SigEv E) Y) cs (.val v) := by
  intro h
  cases h with
  | ret h => exact ret_ne_diverge _ h.symm
  | vis h => exact vis_ne_diverge _ _ h.symm

theorem path_diverge_inv {cs : List (Call E)} {r : PathEnd Y}
    (h : Path (diverge : Silmaril.Elgot.ITree.Tree (SigEv E) Y) cs r) : cs = [] ∧ r = .div := by
  cases h with
  | ret h => exact absurd h.symm (ret_ne_diverge _)
  | div => exact ⟨rfl, rfl⟩
  | vis h => exact absurd h.symm (vis_ne_diverge _ _)

theorem not_infPath_ret {v : Y} {ω : Stream' (Call E)} :
    ¬ InfPath (ret v : Silmaril.Elgot.ITree.Tree (SigEv E) Y) ω := by
  rintro ⟨τ, h0, hτ⟩
  obtain ⟨R, e, k, r, h1, -, -⟩ := hτ 0
  rw [h0] at h1
  exact ret_ne_vis _ _ _ h1

theorem not_infPath_diverge {ω : Stream' (Call E)} :
    ¬ InfPath (diverge : Silmaril.Elgot.ITree.Tree (SigEv E) Y) ω := by
  rintro ⟨τ, h0, hτ⟩
  obtain ⟨R, e, k, r, h1, -, -⟩ := hτ 0
  rw [h0] at h1
  exact vis_ne_diverge _ _ h1.symm

theorem vis_heq' {R R' : Type} {e : SigEv E R} {e' : SigEv E R'}
    {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {k' : R' → Silmaril.Elgot.ITree.Tree (SigEv E) Y} (h : vis e k = vis e' k') :
    ∃ _ : R = R', HEq e e' ∧ HEq k k' := by
  have h2 := congrArg out h
  rw [out_vis, out_vis] at h2
  have h3 := Part.some_injective h2
  injection h3 with hR he hk
  exact ⟨hR, he, hk⟩

theorem infPath_vis_inv {R : Type} {e : SigEv E R} {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) Y}
    {ω : Stream' (Call E)} (h : InfPath (vis e k) ω) :
    ∃ r, ω 0 = ⟨e.1, cast e.2.symm r⟩ ∧ InfPath (k r) (fun n => ω (n + 1)) := by
  obtain ⟨τ, h0, hτ⟩ := h
  obtain ⟨R', e', k', r, h1, h2, h3⟩ := hτ 0
  rw [h0] at h1
  obtain ⟨hR, he, hk⟩ := vis_heq' h1
  subst hR
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq he
  exact ⟨r, h2, ⟨fun n => τ (n + 1), h3, fun n => hτ (n + 1)⟩⟩

theorem infPath_vis {R : Type} {e : SigEv E R} {k : R → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {r : R}
    {ω : Stream' (Call E)} (h : InfPath (k r) ω) :
    InfPath (vis e k) (Stream'.cons ⟨e.1, cast e.2.symm r⟩ ω) := by
  obtain ⟨τ, h0, hτ⟩ := h
  refine ⟨fun n => Nat.casesOn n (vis e k) τ, rfl, fun n => ?_⟩
  cases n with
  | zero => exact ⟨R, e, k, r, rfl, rfl, by simpa using h0⟩
  | succ n => exact hτ n

/-- Finished paths through a bind. -/
theorem path_bind_inv (cs : List (Call E)) : ∀ {t : Silmaril.Elgot.ITree.Tree (SigEv E) Z}
    {k : Z → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {r : PathEnd Y}, Path (t >>= k) cs r →
    (∃ cs₁ cs₂ w, cs = cs₁ ++ cs₂ ∧ Path t cs₁ (.val w) ∧ Path (k w) cs₂ r) ∨
      (r = .div ∧ Path t cs .div) := by
  induction cs with
  | nil =>
    intro t k r h
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k', rfl⟩
    · rw [diverge_bind] at h
      obtain ⟨-, rfl⟩ := path_diverge_inv h
      exact .inr ⟨rfl, .div rfl⟩
    · exact .inl ⟨[], [], a, rfl, .ret rfl, by rwa [ret_bind'] at h⟩
    · rw [vis_bind] at h
      obtain ⟨n, cs', h1, -⟩ := path_vis_inv h
      cases h1
  | cons c cs ih =>
    intro t k r h
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k', rfl⟩
    · rw [diverge_bind] at h
      obtain ⟨h1, -⟩ := path_diverge_inv h
      cases h1
    · exact .inl ⟨[], c :: cs, a, rfl, .ret rfl, by rwa [ret_bind'] at h⟩
    · rw [vis_bind] at h
      obtain ⟨n, cs', h1, h'⟩ := path_vis_inv h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h1
      rcases ih h' with ⟨cs₁, cs₂, w, rfl, h2, h3⟩ | ⟨rfl, h2⟩
      · exact .inl ⟨_ :: cs₁, cs₂, w, rfl, .vis rfl h2, h3⟩
      · exact .inr ⟨rfl, .vis rfl h2⟩

theorem path_bind_val_inv {cs : List (Call E)} {t : Silmaril.Elgot.ITree.Tree (SigEv E) Z}
    {k : Z → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {v : Y} (h : Path (t >>= k) cs (.val v)) :
    ∃ cs₁ cs₂ w, cs = cs₁ ++ cs₂ ∧ Path t cs₁ (.val w) ∧ Path (k w) cs₂ (.val v) := by
  rcases path_bind_inv cs h with h | ⟨h, -⟩
  · exact h
  · cases h

/-- Paths compose through a bind. -/
theorem path_bind {t : Silmaril.Elgot.ITree.Tree (SigEv E) Z} {k : Z → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs₁ cs₂ : List (Call E)}
    {w : Z} {r : PathEnd Y} (h₁ : Path t cs₁ (.val w)) (h₂ : Path (k w) cs₂ r) :
    Path (t >>= k) (cs₁ ++ cs₂) r := by
  generalize hw : (PathEnd.val w : PathEnd Z) = e at h₁
  induction h₁ with
  | ret ht =>
    cases hw
    subst ht
    rwa [ret_bind']
  | div => cases hw
  | vis ht _ ih =>
    subst ht
    rw [vis_bind]
    exact .vis rfl (ih hw)

/-- A silent divergence of the first part of a bind. -/
theorem path_bind_div {t : Silmaril.Elgot.ITree.Tree (SigEv E) Z} {k : Z → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs : List (Call E)}
    (h : Path t cs .div) : Path (t >>= k) cs .div := by
  generalize hw : (PathEnd.div : PathEnd Z) = e at h
  induction h with
  | ret _ => cases hw
  | div ht => subst ht; rw [diverge_bind]; exact .div rfl
  | vis ht _ ih => subst ht; rw [vis_bind]; exact .vis rfl (ih hw)

theorem infPath_bind_left {t : Silmaril.Elgot.ITree.Tree (SigEv E) Z} {k : Z → Silmaril.Elgot.ITree.Tree (SigEv E) Y}
    {ω : Stream' (Call E)} (h : InfPath t ω) : InfPath (t >>= k) ω :=
  infPath_bind_iff.2 (.inl h)

theorem infPath_bind_right {t : Silmaril.Elgot.ITree.Tree (SigEv E) Z} {k : Z → Silmaril.Elgot.ITree.Tree (SigEv E) Y} {cs : List (Call E)}
    {w : Z} {ω : Stream' (Call E)} (h₁ : Path t cs (.val w)) (h₂ : InfPath (k w) ω) :
    InfPath (t >>= k) (cs ++ₛ ω) :=
  infPath_bind_iff.2 (.inr ⟨cs, w, ω, h₁, h₂, rfl⟩)

end

/-! ## Answered calls -/

theorem answered_nil {C : CallRel H} : Answered C [] := fun _ h => absurd h List.not_mem_nil

theorem answered_append {C : CallRel H} {a b : List (Call (CallSig H))} :
    Answered C (a ++ b) ↔ Answered C a ∧ Answered C b := by
  simp only [Answered, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩,
    fun ⟨h1, h2⟩ c hc => hc.elim (h1 c) (h2 c)⟩

theorem answered_cons {C : CallRel H} {c : Call (CallSig H)} {cs : List (Call (CallSig H))} :
    Answered C (c :: cs) ↔ C c.1.2.2 c.1.1 c.1.2.1 c.2 ∧ Answered C cs := by
  simp only [Answered, List.mem_cons]
  exact ⟨fun h => ⟨h c (.inl rfl), fun c' hc => h c' (.inr hc)⟩,
    fun ⟨h1, h2⟩ c' hc => hc.elim (fun e => e ▸ h1) (h2 c')⟩

theorem answeredS_append {C : CallRel H} :
    ∀ {cs : List (Call (CallSig H))} {ω : Stream' (Call (CallSig H))},
      AnsweredS C (cs ++ₛ ω) ↔ Answered C cs ∧ AnsweredS C ω
  | [], ω => by simp [answered_nil]
  | c :: cs, ω => by
    rw [Stream'.cons_append_stream, answered_cons]
    have ih := answeredS_append (C := C) (cs := cs) (ω := ω)
    constructor
    · intro h
      have h' : AnsweredS C (cs ++ₛ ω) := fun n => h (n + 1)
      exact ⟨⟨h 0, (ih.1 h').1⟩, (ih.1 h').2⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩ n
      cases n with
      | zero => exact h0
      | succ n => exact ih.2 ⟨h1, h2⟩ n

/-! ## Trees of the pieces -/

theorem denListC_nil (cK : FuncIdx → Frame → List Val → M (CallSig H) H Res) (f : Frame)
    (stk : List Val) : denListC cK [] f stk = pure ⟨(f, .normal stk)⟩ := by
  rw [denListC]

theorem denListC_cons (cK : FuncIdx → Frame → List Val → M (CallSig H) H Res) (e : BExpr)
    (es : List BExpr) (f : Frame) (stk : List Val) :
    denListC cK (e :: es) f stk = denC cK e f stk >>= thenK (denListC cK es) := by
  rw [denListC]

theorem thenK_nil (cK : FuncIdx → Frame → List Val → M (CallSig H) H Res) :
    thenK (denListC cK []) = (pure : Res → M (CallSig H) H Res) := by
  funext r
  obtain ⟨⟨f, fl⟩⟩ := r
  cases fl <;> simp [thenK, denListC_nil]

theorem denListC_single (cK : FuncIdx → Frame → List Val → M (CallSig H) H Res) (e : BExpr)
    (f : Frame) (stk : List Val) : denListC cK [e] f stk = denC cK e f stk := by
  rw [denListC_cons, thenK_nil, bind_pure]

/-- The tree of a list: its first tree, then the rest on a fallthrough. -/
noncomputable def contK (es : List BExpr) : Except PUnit.{2} (Res × St H) → TT H (Ex H Res) :=
  bc (fun p => tr (thenK (denListE es) p.1) p.2)

theorem tree_cons (e : BExpr) (es : List BExpr) (f : Frame) (stk : List Val) (σ : St H) :
    tr (denListE (H := H) (e :: es) f stk) σ = tr (denC callEv e f stk) σ >>= contK es := by
  show tr (denListC callEv (e :: es) f stk) σ = _
  rw [denListC_cons]; exact tr_bind _ _ _

theorem contK_normal (es : List BExpr) (f : Frame) (stk : List Val) (σ : St H) :
    contK es (.ok (⟨(f, .normal stk)⟩, σ)) = tr (denListE es f stk) σ := rfl

theorem contK_pass (es : List BExpr) {f : Frame} {fl : Flow} (hfl : ¬ fl.IsNormal) (σ : St H) :
    contK es (.ok (⟨(f, fl)⟩, σ)) = ret (.ok (⟨(f, fl)⟩, σ)) := by
  cases fl <;> first | exact absurd trivial hfl | rfl

theorem contK_error (es : List BExpr) (e : PUnit.{2}) :
    contK (H := H) es (.error e) = ret (.error e) := rfl

/-- A tree with no visible event. -/
def Quiet {X : Type 1} (t : TT H (Ex H X)) : Prop := t = diverge ∨ ∃ v, t = ret v

theorem Quiet.not_infPath {X : Type 1} {t : TT H (Ex H X)} (h : Quiet t) {ω : Stream' (Call (CallSig H))} :
    ¬ InfPath t ω := by
  rcases h with rfl | ⟨v, rfl⟩
  · exact not_infPath_diverge
  · exact not_infPath_ret

theorem quiet_evalTree (o : Option (Store H × Frame × Flow)) :
    Quiet (evalTree (E := CallSig H) o) := by
  rcases o with _ | ⟨s, f, fl⟩
  · exact .inl rfl
  · cases fl <;> exact .inr ⟨_, rfl⟩

theorem quiet_flatK (i : Instr) (f : Frame) (stk : List Val) (σ : St H) :
    Quiet (tr (flatK i f stk : M (CallSig H) H Res) σ) := by
  obtain ⟨s⟩ := σ
  rw [tr, run_flatK]
  exact quiet_evalTree _

theorem tr_callAns_ok {f : Frame} {stk : List Val} {ps rs : List Validation.CValType} {s₂ : Store H}
    {fl : Flow} {vs : List Val} (hvs : fl.retVals = some vs) (σ : St H) :
    tr (callAns f stk ps rs (s₂, fl)) σ =
      ret (.ok (⟨(f, .normal (vs.take rs.length ++ stk.drop ps.length))⟩, ⟨s₂⟩)) := by
  cases fl with
  | normal ws => cases hvs; simp only [callAns, Flow.retVals, tr_bind, tr_setState, ret_bind', bc_ok, tr_pure]
  | ret ws => cases hvs; simp only [callAns, Flow.retVals, tr_bind, tr_setState, ret_bind', bc_ok, tr_pure]
  | brk n ws => cases n with
    | zero => cases hvs; simp only [callAns, Flow.retVals, tr_bind, tr_setState, ret_bind', bc_ok, tr_pure]
    | succ n => cases hvs
  | trap => cases hvs
  | throw t => cases hvs

theorem tr_callAns_trap {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {s₂ : Store H} (σ : St H) : tr (callAns f stk ps rs (s₂, .trap)) σ = ret (.error ⟨⟩) := by
  simp only [callAns, tr_trap]

theorem tr_callAns_throw {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {s₂ : Store H} {t : Nat} (σ : St H) :
    tr (callAns f stk ps rs (s₂, .throw t)) σ = ret (.ok (⟨(f, .throw t)⟩, ⟨s₂⟩)) := by
  simp only [callAns, tr_bind, tr_setState, ret_bind', bc_ok, tr_pure]

theorem tr_callAns_none {f : Frame} {stk : List Val} {ps rs : List Validation.CValType}
    {s₂ : Store H} {fl : Flow} (hvs : fl.retVals = none) (htr : fl ≠ .trap)
    (hth : ∀ t, fl ≠ .throw t) (σ : St H) : tr (callAns f stk ps rs (s₂, fl)) σ = diverge := by
  cases fl with
  | normal ws => cases hvs
  | ret ws => cases hvs
  | brk n ws => cases n with
    | zero => cases hvs
    | succ n => simp only [callAns, Flow.retVals]; rfl
  | trap => exact absurd rfl htr
  | throw t => exact absurd rfl (hth t)

theorem quiet_callAns (f : Frame) (stk : List Val) (ps rs : List Validation.CValType)
    (o : Store H × Flow) (σ : St H) : Quiet (tr (callAns f stk ps rs o) σ) := by
  obtain ⟨s₂, fl⟩ := o
  by_cases htr : fl = .trap
  · subst htr; exact .inr ⟨_, tr_callAns_trap σ⟩
  by_cases hth : ∃ t, fl = .throw t
  · obtain ⟨t, rfl⟩ := hth; exact .inr ⟨_, tr_callAns_throw σ⟩
  push Not at hth
  cases hvs : fl.retVals with
  | none => exact .inl (tr_callAns_none hvs htr hth σ)
  | some vs => exact .inr ⟨_, tr_callAns_ok hvs σ⟩

/-- The tree of an exposed call. -/
theorem tr_callEv (x : FuncIdx) (f : Frame) (stk : List Val) (s : Store H) :
    tr (callEv x f stk : M (CallSig H) H Res) ⟨s⟩ =
      match s.func? f x with
      | some (a, fi) =>
        match Validation.DefType.funcType? fi.type with
        | some (ps, rs) =>
          vis (E := SigEv (CallSig H)) (R := Store H × Flow) ⟨(a, (stk.take ps.length).reverse, s), rfl⟩
            fun n => tr (callAns f stk ps rs n) ⟨s⟩
        | none => diverge
      | none => diverge := by
  simp only [callEv, tr_bind, tr_getState, ret_bind', bc_ok]
  rcases s.func? f x with _ | ⟨a, fi⟩
  · rfl
  · dsimp only
    rcases Validation.DefType.funcType? fi.type with _ | ⟨ps, rs⟩
    · rfl
    · dsimp only
      rw [tr_bind]
      show (vis _ fun n => ret (Except.ok (ULift.up n, _))) >>= _ = _
      refine (vis_bind _ _ _).trans ?_
      congr 1
      funext n
      exact ret_bind' _ _

theorem not_infPath_callEv (x : FuncIdx) (f : Frame) (stk : List Val) (σ : St H)
    {ω : Stream' (Call (CallSig H))} : ¬ InfPath (tr (callEv x f stk : M (CallSig H) H Res) σ) ω := by
  obtain ⟨s⟩ := σ
  rw [tr_callEv]
  rcases s.func? f x with _ | ⟨a, fi⟩
  · exact not_infPath_diverge
  · dsimp only
    rcases Validation.DefType.funcType? fi.type with _ | ⟨ps, rs⟩
    · exact not_infPath_diverge
    · intro h
      obtain ⟨r, -, h'⟩ := infPath_vis_inv h
      exact (quiet_callAns f stk ps rs r ⟨s⟩).not_infPath h'

theorem not_infPath_opC (i : Instr) (f : Frame) (stk : List Val) (σ : St H)
    {ω : Stream' (Call (CallSig H))} : ¬ InfPath (tr (opC callEv i f stk : M (CallSig H) H Res) σ) ω := by
  unfold opC
  cases callIdx? i with
  | none => exact (quiet_flatK i f stk σ).not_infPath
  | some x => exact not_infPath_callEv x f stk σ

end Silmaril.Proofs.Wasm.Abstract.FullObsNative
