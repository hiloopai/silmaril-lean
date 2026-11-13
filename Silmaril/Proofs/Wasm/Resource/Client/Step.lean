module

public import Silmaril.Proofs.Wasm.Resource.Client.Basic
public import Silmaril.Wasm.Verify.Flow.Thms

/-!
# The client typestate analysis: preservation by every Core step

`CPost C L L' c c'` says what a step `c ⟶ c'` keeps of the client invariant, from the live list
`L` to `L'`: from the store invariant, sound facts and a check of the code followed by any
continuation `l` (in the prefix, with any incoming top), the store invariant holds after the
step and the new code followed by `l` is checked from some sound facts (incoming top `other`).

`Step.client` proves `CPost C L L` for every Core 3.0 rule (every profile, host-free), by
induction on `Step`, given the reachability invariant before and after the step (so that a
`call` reaching it is not a call of the three imports):

* most rules replace values and one instruction keeping the facts by elements keeping them
  (`post_keep`), or end the facts and run requirement-free code (`post_kill`);
* `global.get` (`post_globalGet`, the semantic top `getTop_sound`), `global.set`
  (`post_globalSet`, `setF_sound`: the only rule changing the globals);
* `if` (`post_ifTrue`, `post_ifFalse`: the branch facts `on k`/`off k`), `block`, `loop`,
  `try_table`, branches to a label, calls of Wasm functions (bodies checked from no facts);
* the context rules (`post_ctxtInstrs`, `post_ctxtLabel`, `post_ctxtHandler`, `post_ctxtFrame`),
  for any `L L'`: outer sequences are robust (their prefix ends at the nested element).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource.Client

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Verify (CfgIn CodeIn FrameIn StoreIn RefIn PlOK refFuncs)

variable {H : Type} {C : Cfg}

/-- What a step keeps of the client invariant (see the module docstring). -/
def CPost (C : Cfg) (L L' : List Val) (c c' : Config H) : Prop :=
  ∀ (F : List Fact) (t : CTop) (l : List Admin), t ≠ .ex → Sigma C.ps L c.store.globals →
    SoundF C.ps L c.store.globals c.frame.locals F →
    okA C L c.store.globals c.frame.module.globals c.frame.locals ⟨F, t, true⟩ (c.code ++ l) →
    Sigma C.ps L' c'.store.globals ∧ ∃ F', SoundF C.ps L' c'.store.globals c'.frame.locals F' ∧
      okA C L' c'.store.globals c'.frame.module.globals c'.frame.locals ⟨F', .other, true⟩
        (c'.code ++ l)

/-! ## Frames keep their module -/

theorem Step.module_eq {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : c'.frame.module = c.frame.module := by
  induction h with
  | «variable» h => cases h <;> rfl
  | table h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | _ => rfl

/-! ## Walking prefixes -/

section
variable {L : List Val} {gl : List GlobalInst} {gs : List Nat} {lc : List (Option Val)}

theorem okA_valsA : ∀ (V : List Admin) {F : List Fact} {t : CTop} {l : List Admin},
    (∀ y ∈ V, y.val? ≠ none) → t ≠ .ex → okA C L gl gs lc ⟨F, t, true⟩ (V ++ l) →
    ∃ t', t' ≠ .ex ∧ okA C L gl gs lc ⟨F, t', true⟩ l
  | [], _, t, _, _, ht, h => ⟨t, ht, h⟩
  | y :: V, F, t, l, hV, ht, h => by
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hV y List.mem_cons_self)
    obtain rfl := val?_eq_some hv
    rw [List.cons_append, okA_val_pre ht] at h
    obtain ⟨t', hab, h⟩ := h
    exact okA_valsA V (fun z hz => hV z (List.mem_cons_of_mem _ hz)) (by rintro rfl; exact hab) h

theorem okA_valsA_other : ∀ (V : List Admin) {F : List Fact} {l : List Admin},
    (∀ y ∈ V, y.val? ≠ none) → okA C L gl gs lc ⟨F, .other, true⟩ l →
    ∀ t, okA C L gl gs lc ⟨F, t, true⟩ (V ++ l)
  | [], _, l, _, h, t => okA_mono l h (Or.inr ⟨fun _ h => h, .inr (.inl rfl), fun h => h⟩)
  | y :: V, F, l, hV, h, t => by
    by_cases ht : t = .ex
    · subst ht; exact okA_cons_ex _ _ _ _
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hV y List.mem_cons_self)
    obtain rfl := val?_eq_some hv
    rw [List.cons_append, okA_val_pre ht]
    exact ⟨.other, trivial, okA_valsA_other V (fun z hz => hV z (List.mem_cons_of_mem _ hz)) h _⟩

theorem split_last {α : Type} : ∀ {l : List α} {x : α}, l.getLast? = some x → l = l.dropLast ++ [x]
  | [], _, h => by simp at h
  | [a], x, h => by simp at h; simp [h]
  | a :: b :: l, x, h => by
    have ih := split_last (l := b :: l) (x := x) (by simpa using h)
    simp only [List.dropLast_cons_cons, List.cons_append]
    exact congrArg (a :: ·) ih

theorem okA_throwing (F : List Fact) (t : CTop) (a : Nat) (l : List Admin) :
    okA C L gl gs lc ⟨F, t, true⟩ (throwing a ++ l) := by
  by_cases ht : t = .ex
  · subst ht; exact okA_cons_ex _ _ _ _
  have h₁ : okA C L gl gs lc ⟨F, .other, true⟩ (Admin.plain .throwRef :: l) := by
    rw [okA_plain (t := .other) (i := .throwRef) (by decide) (.inr rfl)]
    cases l with
    | nil => exact ⟨rfl, trivial⟩
    | cons x l => exact ⟨rfl, okA_cons_ex _ _ _ _⟩
  have h₂ := (okA_val_pre (C := C) (L := L) (gl := gl) (gs := gs) (F := F) ht (.ref (.exn a))
    (Admin.plain .throwRef :: l)).2 ⟨.other, trivial, h₁⟩
  exact h₂

end

/-! ## The common shapes -/

/-- **Values and one instruction keeping the facts**, replaced by elements keeping them. -/
theorem post_keep {L : List Val} {s s' : Store H} {f f' : Frame} {Lc R : List Admin} {i : Instr}
    (hg : s'.globals = s.globals) (hm : f'.module.globals = f.module.globals)
    (hl : f'.locals = f.locals) (hV : ∀ y ∈ Lc.dropLast, y.val? ≠ none) (hlast : Lc.getLast? = some (.plain i))
    (hiv : (Admin.plain i).val? = none) (hi : ∀ (C : Cfg) gs F t, nextI C gs F t i = (F, .other))
    (hR : ∀ x ∈ R, KeepE x) : CPost C L L (⟨s, f, Lc⟩ : Config H) ⟨s', f', R⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [hg, hm, hl]
  refine ⟨hS, F, hF, ?_⟩
  rw [split_last hlast, List.append_assoc] at h
  obtain ⟨t', ht', h⟩ := okA_valsA _ hV ht h
  rw [List.singleton_append, okA_plain ht' (.inr hiv), hi] at h
  exact okA_keep h.2 R hR _ _

/-- `post_keep` with the value prefix given as a list of values. -/
theorem post_keep' {L : List Val} {s s' : Store H} {f f' : Frame} {vs : List Val} {R : List Admin}
    {i : Instr} (hg : s'.globals = s.globals) (hm : f'.module.globals = f.module.globals)
    (hl : f'.locals = f.locals) (hiv : (Admin.plain i).val? = none) (hi : ∀ (C : Cfg) gs F t, nextI C gs F t i = (F, .other))
    (hR : ∀ x ∈ R, KeepE x) :
    CPost C L L (⟨s, f, vals vs ++ [.plain i]⟩ : Config H) ⟨s', f', R⟩ :=
  post_keep hg hm hl (by simp [vals]) (by simp) hiv hi hR

/-- Code ending the facts. -/
def KillP (C : Cfg) (Lc : List Admin) : Prop :=
  ∀ (L : List Val) (gl : List GlobalInst) (gs : List Nat) (lc : List (Option Val)) (F : List Fact)
    (t : CTop) (l : List Admin), t ≠ .ex → okA C L gl gs lc ⟨F, t, true⟩ (Lc ++ l) →
    okA C L gl gs lc ⟨[], .other, false⟩ l

/-- Requirement-free code. -/
def FreeP (C : Cfg) (R : List Admin) : Prop :=
  ∀ (L : List Val) (gl : List GlobalInst) (gs : List Nat) (lc : List (Option Val)) (F : List Fact)
    (l : List Admin), okA C L gl gs lc ⟨[], .other, false⟩ l →
      okA C L gl gs lc ⟨F, .other, true⟩ (R ++ l)

/-- **Code ending the facts**, replaced by requirement-free code. -/
theorem post_kill {L : List Val} {s s' : Store H} {f f' : Frame} {Lc R : List Admin}
    (hg : s'.globals = s.globals) (hm : f'.module.globals = f.module.globals)
    (hl : f'.locals = f.locals) (hL : KillP C Lc) (hR : FreeP C R) :
    CPost C L L (⟨s, f, Lc⟩ : Config H) ⟨s', f', R⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [hg, hm, hl]
  exact ⟨hS, [], SoundF_nil, hR _ _ _ _ [] l (hL _ _ _ _ F t l ht h)⟩

/-- A trap. -/
theorem post_trapR {L : List Val} {s s' : Store H} {f f' : Frame} {Lc : List Admin}
    (hg : s'.globals = s.globals) : CPost C L L (⟨s, f, Lc⟩ : Config H) ⟨s', f', [.trap]⟩ := by
  intro F t l _ hS hF _
  simp only at hS hF ⊢
  rw [hg]
  exact ⟨hS, [], SoundF_nil, okA_trap _ _⟩

/-- An exception thrown. -/
theorem post_throwingR {L : List Val} {s s' : Store H} {f f' : Frame} {Lc : List Admin}
    (hg : s'.globals = s.globals) (a : Nat) :
    CPost C L L (⟨s, f, Lc⟩ : Config H) ⟨s', f', throwing a⟩ := by
  intro F t l _ hS hF _
  simp only at hS hF ⊢
  rw [hg]
  exact ⟨hS, [], SoundF_nil, okA_throwing _ _ _ _⟩

theorem killP_nest {y : Admin} (hy : NestA y) : KillP C [y] :=
  fun _ _ _ _ _ _ l ht h => ((okA_nest_pre ht hy l).1 h).2

theorem killP_plain {i : Instr} (hiv : (Admin.plain i).val? = none)
    (hi : ∀ gs F t, nextI C gs F t i = ([], .other)) : KillP C [.plain i] := by
  intro _ _ gs _ F t l ht h
  rw [List.singleton_append, okA_plain ht (.inr hiv), hi] at h
  exact h.2

theorem killP_vals {V Lc : List Admin} (hV : ∀ y ∈ V, y.val? ≠ none) (h : KillP C Lc) :
    KillP C (V ++ Lc) := by
  intro L gl gs lc F t l ht h'
  rw [List.append_assoc] at h'
  obtain ⟨t', ht', h''⟩ := okA_valsA V hV ht h'
  exact h L gl gs lc F t' l ht' h''

theorem killP_callRef {c : Admin} (hc : c.IsCallRef) : KillP C [c] := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsCallRef]
  · rename_i i
    cases i <;> simp_all
    exact killP_plain rfl fun _ _ _ => rfl
  · exact killP_nest trivial

theorem killP_retCallRef {c : Admin} (hc : c.IsReturnCallRef) : KillP C [c] := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsReturnCallRef]
  · rename_i i
    cases i <;> simp_all
    exact killP_plain rfl fun _ _ _ => rfl
  · exact killP_nest trivial

theorem freeP_of_free {R : List Admin} (h : ∀ x ∈ R, FreeE x) : FreeP C R :=
  fun _ _ _ _ F _ hl => okA_free hl R h F .other true

theorem freeP_vals {V R : List Admin} (hV : ∀ y ∈ V, y.val? ≠ none) (h : FreeP C R) :
    FreeP C (V ++ R) := by
  intro L gl gs lc F l hl
  rw [List.append_assoc]
  exact okA_valsA_other V hV (h L gl gs lc F l hl) _

theorem freeP_nest {y : Admin} (hy : NestA y)
    (hx : ∀ (L : List Val) (gl : List GlobalInst) (gs : List Nat) (lc : List (Option Val)),
      okX C L gl gs lc y) :
    FreeP C [y] :=
  fun L gl gs lc _ l hl => (okA_nest_pre (t := .other) (by decide) hy l).2 ⟨hx L gl gs lc, hl⟩

theorem freeP_retCallRef {c : Admin} (hc : c.IsReturnCallRef) : FreeP C [c] := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsReturnCallRef]
  · rename_i i
    cases i <;> simp_all
    exact freeP_of_free fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact Or.inr (Or.inr ⟨_, rfl, fun _ _ _ _ => rfl⟩)
  · exact freeP_nest trivial fun _ _ _ _ => trivial

theorem freeP_retToCallIn {c : Admin} (m : ModuleInst) (hc : c.IsReturnCallRef) :
    FreeP C [c.retToCallIn m] := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsReturnCallRef]
  · rename_i i
    cases i <;> simp_all [Admin.retToCallIn]
    split
    · exact freeP_nest trivial fun _ _ _ _ => trivial
    · exact freeP_of_free fun x hx => by
        simp only [List.mem_singleton] at hx
        subst hx
        exact Or.inr (Or.inr ⟨_, rfl, fun _ _ _ _ => rfl⟩)
  · exact freeP_nest trivial fun _ _ _ _ => trivial

/-! ## Tactics for the common shapes -/

@[simp] theorem val?_ref (r : Ref) : (Admin.ref r).val? = some (.ref r) := rfl
@[simp] theorem val?_intConst (t : IntType) (c : BitVec t.width) :
    (Admin.plain (.intConst t c)).val? = some (.num ⟨.int t, c⟩) := rfl
@[simp] theorem val?_floatConst (t : FloatType) (c : BitVec t.width) :
    (Admin.plain (.floatConst t c)).val? = some (.num ⟨.float t, c⟩) := rfl
@[simp] theorem val?_vecConst (c : BitVec 128) :
    (Admin.plain (.vecConst c)).val? = some (.vec c) := rfl

/-- One element keeps the facts. -/
macro "client_keep_one" : tactic => `(tactic| first
  | (refine Or.inl ?_; simp [constI32, aconst, arrRef]; done)
  | exact Or.inr (Or.inl rfl)
  | exact Or.inr (Or.inr ⟨_, rfl, rfl, fun _ _ _ _ => ⟨rfl, rfl, nofun⟩⟩)
  | (intro _ _; refine Or.inl ?_; simp; done)
  | (intro _; refine Or.inl ?_; simp; done))

/-- One element has no requirement. -/
macro "client_free_one" : tactic => `(tactic| first
  | (refine Or.inl ?_; simp [constI32, aconst, arrRef]; done)
  | exact Or.inr (Or.inl rfl)
  | exact Or.inr (Or.inr ⟨_, rfl, fun _ _ _ _ => rfl⟩)
  | (intro _ _; refine Or.inl ?_; simp; done)
  | (intro _; refine Or.inl ?_; simp; done))

/-- Close a `CPost` goal of the keeping shape on explicit code lists. -/
macro "client_keep_tac" : tactic => `(tactic| (
  first
    | refine post_keep' rfl rfl rfl rfl (fun _ _ _ _ => rfl) ?_
    | (refine post_keep rfl rfl rfl ?_ rfl rfl (fun _ _ _ _ => rfl) ?_
       · simp [constI32, aconst, arrRef, vals])
  verify_mem_split
  all_goals first
    | client_keep_one
    | (refine Or.inr ?_; client_keep_one)))

/-- Close a `CPost` goal of a nested element replaced by requirement-free code. -/
macro "client_nest_tac" : tactic => `(tactic| (
  refine post_kill rfl rfl rfl (killP_nest trivial) (freeP_of_free ?_)
  verify_mem_split
  all_goals client_free_one))

/-! ## The families -/

section
variable {P : Numerics.Profile} {L : List Val}

theorem ParametricStep.client {s : Store H} {f : Frame} {is is' : List Admin}
    (h : ParametricStep is is') : CPost C L L (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> first | exact post_trapR rfl | client_keep_tac

theorem NumericStep.client {s : Store H} {f : Frame} {is is' : List Admin}
    (h : NumericStep P is is') : CPost C L L (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> first | exact post_trapR rfl | client_keep_tac

theorem VectorStep.client {s : Store H} {f : Frame} {is is' : List Admin}
    (h : VectorStep P is is') : CPost C L L (⟨s, f, is⟩ : Config H) ⟨s, f, is'⟩ := by
  cases h <;> first | exact post_trapR rfl | client_keep_tac

theorem TableStep.client {c c' : Config H} (h : TableStep P c c') : CPost C L L c c' := by
  cases h <;> first | exact post_trapR rfl | client_keep_tac

theorem MemoryStep.client {c c' : Config H} (h : MemoryStep P c c') : CPost C L L c c' := by
  cases h <;> first | exact post_trapR rfl | client_keep_tac

theorem RefStep.client {c c' : Config H} (h : RefStep c c') : CPost C L L c c' := by
  cases h <;> first | exact post_trapR rfl | client_keep_tac

theorem AggregateStep.client {c c' : Config H} (h : AggregateStep c c') : CPost C L L c c' := by
  cases h <;> first | exact post_trapR rfl | client_keep_tac

end

/-! ## Globals -/

section Sem
variable {L : List Val} {lc : List (Option Val)}

theorem gval_setGlobal {s : Store H} {a : Nat} {g : GlobalInst} (hg : s.globals[a]? = some g)
    (v : Val) (b : Nat) :
    gval (s.setGlobal a v).globals b = if b = a then some v else gval s.globals b := by
  simp only [Store.setGlobal, gval, List.getElem?_modify]
  by_cases hb : b = a
  · subst hb; simp [hg]
  · simp [Ne.symm hb, hb]

theorem On_congr {gl gl' : List GlobalInst} {q : Nat × Nat} (h : gval gl' q.1 = gval gl q.1) :
    On gl' q ↔ On gl q := by
  simp only [On, h]

/-- The pairs of distinct addresses. -/
theorem pairs_uniq {ps : List (Nat × Nat)} (hP : PairsOK ps) {j k : Nat} {p q : Nat × Nat}
    (hj : ps[j]? = some p) (hk : ps[k]? = some q) :
    (p.1 = q.1 → j = k) ∧ (p.2 = q.2 → j = k) ∧ p.1 ≠ q.2 := by
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 hk
  have h := hP ⟨j, hj'⟩ ⟨k, hk'⟩
  exact ⟨fun e => Fin.mk.inj_iff.1 (h.1 e), fun e => Fin.mk.inj_iff.1 (h.2.1 e), h.2.2⟩

theorem handFr_sound {gl : List GlobalInst} {F : List Fact} (hF : SoundF C.ps L gl lc F) {k : Nat}
    {p : Nat × Nat} (hp : C.ps[k]? = some p) {v : Val} (hv : gval gl p.2 = some v)
    (hlive : Fact.live k ∈ F) (hoff : Fact.off k ∈ F) : Ab C.ps L gl .fr v := by
  obtain ⟨p₁, hp₁, w, hw, hwL, hoth⟩ := hF _ hlive
  obtain ⟨p₂, hp₂, h0⟩ := hF _ hoff
  rw [hp] at hp₁ hp₂
  cases hp₁; cases hp₂
  rw [hv] at hw; cases hw
  refine ⟨hwL, fun q hq hon => ?_⟩
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hq
  by_cases hjk : j = k
  · subst hjk
    rw [hp] at hj; cases hj
    obtain ⟨u, hu, hu0⟩ := hon
    rw [h0] at hu; cases hu; exact absurd rfl hu0
  · exact hoth j q hjk hj hon

theorem handGg_sound {gl : List GlobalInst} (hS : Sigma C.ps L gl) {F : List Fact}
    (hF : SoundF C.ps L gl lc F) {k : Nat} {p : Nat × Nat} (hp : C.ps[k]? = some p) {v : Val}
    (hv : gval gl p.2 = some v) (h : Fact.on k ∈ F ∨ Fact.live k ∈ F) : Ab C.ps L gl .gg v := by
  rcases h with h | h
  · obtain ⟨p₁, hp₁, hon⟩ := hF _ h
    rw [hp] at hp₁; cases hp₁
    obtain ⟨w, hw, hwL⟩ := hS p (List.mem_of_getElem? hp) hon
    rw [hv] at hw; cases hw; exact hwL
  · obtain ⟨p₁, hp₁, w, hw, hwL, -⟩ := hF _ h
    rw [hp] at hp₁; cases hp₁
    rw [hv] at hw; cases hw; exact hwL

/-- **The semantic top of `global.get`.** -/
theorem getTop_sound {gl : List GlobalInst} (hS : Sigma C.ps L gl) {F : List Fact}
    (hF : SoundF C.ps L gl lc F) {a : Nat} {v : Val} (hv : gval gl a = some v) :
    Ab C.ps L gl (getTop C F a) v := by
  unfold getTop
  split
  · rename_i k hk
    obtain ⟨p, hp, rfl⟩ := pairOf_true hk
    exact ⟨p, hp, hv⟩
  · rename_i k hk
    obtain ⟨p, hp, rfl⟩ := pairOf_false hk
    unfold handTop
    split
    · rename_i h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      exact handFr_sound hF hp hv h.1 h.2
    · split
      · rename_i h
        simp only [Bool.or_eq_true, List.contains_iff_mem] at h
        exact handGg_sound hS hF hp hv h
      · trivial
  · trivial

theorem i32_ne_zero {c : BitVec 32} (hc : c ≠ 0) : Val.i32 c ≠ Val.i32 0 := by
  intro h; apply hc; cases h; rfl

/-! ### `global.set`: globals outside the pairs -/

section Unchanged
variable {gl gl' : List GlobalInst}
  (hq : ∀ q ∈ C.ps, gval gl' q.1 = gval gl q.1 ∧ gval gl' q.2 = gval gl q.2)
include hq

theorem sigma_congr (hS : Sigma C.ps L gl) : Sigma C.ps L gl' := by
  intro q hqm hon
  obtain ⟨w, hw, hwL⟩ := hS q hqm ((On_congr (hq q hqm).1).1 hon)
  exact ⟨w, (hq q hqm).2.trans hw, hwL⟩

theorem loc_congr {i : Nat} (h : FactSem C.ps L gl lc (.loc i)) :
    FactSem C.ps L gl' lc (.loc i) := by
  obtain ⟨w, hw, hwL, hoth⟩ := h
  refine ⟨w, hw, hwL, fun r hr hon => ?_⟩
  rw [(hq r hr).2]
  exact hoth r hr ((On_congr (hq r hr).1).1 hon)

theorem soundF_congr {F : List Fact} (hF : SoundF C.ps L gl lc F) : SoundF C.ps L gl' lc F := by
  intro f hf
  have h₁ := hF f hf
  cases f with
  | on j =>
    obtain ⟨q, hqj, hon⟩ := h₁
    exact ⟨q, hqj, (On_congr (hq q (List.mem_of_getElem? hqj)).1).2 hon⟩
  | off j =>
    obtain ⟨q, hqj, h0⟩ := h₁
    exact ⟨q, hqj, (hq q (List.mem_of_getElem? hqj)).1.trans h0⟩
  | live j =>
    obtain ⟨q, hqj, w, hw, hwL, hoth⟩ := h₁
    refine ⟨q, hqj, w, (hq q (List.mem_of_getElem? hqj)).2.trans hw, hwL, ?_⟩
    intro i r hij hr hon
    rw [(hq r (List.mem_of_getElem? hr)).2]
    exact hoth i r hij hr ((On_congr (hq r (List.mem_of_getElem? hr)).1).1 hon)
  | loc i => exact loc_congr hq h₁

end Unchanged

/-! ### `global.set` of the handle of pair `k` -/

section Hand
variable {gl gl' : List GlobalInst} {k : Nat} {p : Nat × Nat} {v : Val}
  (hp : C.ps[k]? = some p) (hself : gval gl' p.2 = some v)
  (hflag : ∀ (j : Nat) (q : Nat × Nat), C.ps[j]? = some q → gval gl' q.1 = gval gl q.1)
  (hother : ∀ (j : Nat) (q : Nat × Nat), j ≠ k → C.ps[j]? = some q → gval gl' q.2 = gval gl q.2)
include hp hself hflag hother

theorem hand_sigma (hS : Sigma C.ps L gl) (hvL : v ∈ L) : Sigma C.ps L gl' := by
  intro q hqm hon
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hqm
  have hon' := (On_congr (hflag j q hj)).1 hon
  by_cases hjk : j = k
  · subst hjk; rw [hp] at hj; cases hj
    exact ⟨v, hself, hvL⟩
  · obtain ⟨w, hw, hwL⟩ := hS q hqm hon'
    exact ⟨w, (hother j q hjk hj).trans hw, hwL⟩

theorem hand_sound {F : List Fact} (hF : SoundF C.ps L gl lc F) (hvL : v ∈ L)
    (hfree : ∀ q ∈ C.ps, On gl q → gval gl q.2 ≠ some v) :
    SoundF C.ps L gl' lc (.live k :: F.filter fun f => !isLive f) := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  · refine ⟨p, hp, v, hself, hvL, fun j q hjk hq hon => ?_⟩
    rw [hother j q hjk hq]
    exact hfree q (List.mem_of_getElem? hq) ((On_congr (hflag j q hq)).1 hon)
  · obtain ⟨hf, hl⟩ := List.mem_filter.1 hf
    have h₁ := hF f hf
    cases f with
    | on j =>
      obtain ⟨q, hqj, hon⟩ := h₁
      exact ⟨q, hqj, (On_congr (hflag j q hqj)).2 hon⟩
    | off j =>
      obtain ⟨q, hqj, h0⟩ := h₁
      exact ⟨q, hqj, (hflag j q hqj).trans h0⟩
    | live j => simp [isLive] at hl
    | loc j => simp [isLive] at hl

end Hand

/-! ### `global.set` of the flag of pair `k` -/

section Flag
variable {gl gl' : List GlobalInst} {k : Nat} {p : Nat × Nat} {v : Val} {F : List Fact}
  (hp : C.ps[k]? = some p) (hself : gval gl' p.1 = some v)
  (hhand : ∀ (j : Nat) (q : Nat × Nat), C.ps[j]? = some q → gval gl' q.2 = gval gl q.2)
  (hother : ∀ (j : Nat) (q : Nat × Nat), j ≠ k → C.ps[j]? = some q → gval gl' q.1 = gval gl q.1)
  (hS : Sigma C.ps L gl) (hF : SoundF C.ps L gl lc F)
include hp hself hhand hother hS hF

theorem flag_sigma {t : CTop} (hreq : t = .zero ∨ Fact.live k ∈ F)
    (hzero : t = .zero → v = Val.i32 0) : Sigma C.ps L gl' := by
  intro q hqm hon
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hqm
  by_cases hjk : j = k
  · subst hjk; rw [hp] at hj; cases hj
    obtain ⟨u, hu, hu0⟩ := hon
    rw [hself] at hu; cases hu
    rcases hreq with h | h
    · exact absurd (hzero h) hu0
    · obtain ⟨p₁, hp₁, w, hw, hwL, -⟩ := hF _ h
      rw [hp] at hp₁; cases hp₁
      exact ⟨w, (hhand _ p hp).trans hw, hwL⟩
  · obtain ⟨w, hw, hwL⟩ := hS q hqm ((On_congr (hother j q hjk hj)).1 hon)
    exact ⟨w, (hhand j q hj).trans hw, hwL⟩

omit hself in
theorem flag_live (hon : Fact.on k ∈ F) (hoff : ∀ j < C.ps.length, j = k ∨ Fact.off j ∈ F) :
    FactSem C.ps L gl' lc (.live k) := by
  obtain ⟨p₁, hp₁, hon₁⟩ := hF _ hon
  rw [hp] at hp₁; cases hp₁
  obtain ⟨w, hw, hwL⟩ := hS p (List.mem_of_getElem? hp) hon₁
  refine ⟨p, hp, w, (hhand k p hp).trans hw, hwL, fun j q hjk hq hon' => ?_⟩
  exfalso
  rcases hoff j (List.getElem?_eq_some_iff.1 hq).1 with h | h
  · exact hjk h
  · obtain ⟨q₁, hq₁, h0⟩ := hF _ h
    rw [hq] at hq₁; cases hq₁
    obtain ⟨u, hu, hu0⟩ := hon'
    rw [hother j q hjk hq, h0] at hu; cases hu; exact hu0 rfl

theorem flag_pre_zero (h0 : v = Val.i32 0) :
    ∀ f ∈ Fact.off k :: (if liveAfterClear C F k then [Fact.live k] else []),
      FactSem C.ps L gl' lc f := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  · exact ⟨p, hp, by rw [hself, h0]⟩
  · by_cases hl : liveAfterClear C F k = true
    · rw [ite_t hl, List.mem_singleton] at hf
      subst hf
      simp only [liveAfterClear, Bool.and_eq_true, List.contains_iff_mem,
        List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hl
      exact flag_live hp hhand hother hS hF hl.1 hl.2
    · rw [ite_f hl] at hf; simp at hf

omit hS hF in
theorem flag_filt_live {t : CTop} {j : Nat} (hzero : t = .zero → v = Val.i32 0)
    (h₁ : FactSem C.ps L gl lc (.live j))
    (hlive : (t = .zero ∨ isLive (.live j) = false) ∨ Fact.live j = .live k) :
    FactSem C.ps L gl' lc (.live j) := by
  obtain ⟨q, hqj, w, hw, hwL, hoth⟩ := h₁
  refine ⟨q, hqj, w, (hhand j q hqj).trans hw, hwL, fun i r hij hr hon => ?_⟩
  rw [hhand i r hr]
  by_cases hik : i = k
  · subst hik; rw [hp] at hr; cases hr
    obtain ⟨u, hu, hu0⟩ := hon
    rw [hself] at hu; cases hu
    rcases hlive with (h | h) | h
    · exact absurd (hzero h) hu0
    · simp [isLive] at h
    · cases h; exact absurd rfl hij
  · exact hoth i r hij hr ((On_congr (hother i r hik hr)).1 hon)

omit hS hF in
theorem flag_filt_loc {t : CTop} {j : Nat} (hzero : t = .zero → v = Val.i32 0)
    (h₁ : FactSem C.ps L gl lc (.loc j))
    (hlive : (t = .zero ∨ isLive (.loc j) = false) ∨ Fact.loc j = .live k) :
    FactSem C.ps L gl' lc (.loc j) := by
  have htz : t = .zero := by
    rcases hlive with (h | h) | h
    · exact h
    · simp [isLive] at h
    · cases h
  obtain ⟨w, hw, hwL, hoth⟩ := h₁
  refine ⟨w, hw, hwL, fun r hr hon => ?_⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hr
  rw [hhand i r hi]
  by_cases hik : i = k
  · subst hik; rw [hp] at hi; cases hi
    obtain ⟨u, hu, hu0⟩ := hon
    rw [hself] at hu; cases hu
    exact absurd (hzero htz) hu0
  · exact hoth r hr ((On_congr (hother i r hik hi)).1 hon)

omit hS in
theorem flag_filt {t : CTop} (hzero : t = .zero → v = Val.i32 0) :
    ∀ f ∈ F.filter (fun f => f != .on k && f != .off k && (t == .zero || !isLive f || f == .live k)),
      FactSem C.ps L gl' lc f := by
  intro f hf
  obtain ⟨hf, hl⟩ := List.mem_filter.1 hf
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hl
  obtain ⟨⟨hon_ne, hoff_ne⟩, hlive⟩ := hl
  have h₁ := hF f hf
  cases f with
  | on j =>
    obtain ⟨q, hqj, hon⟩ := h₁
    exact ⟨q, hqj, (On_congr (hother j q (fun e => hon_ne (e ▸ rfl)) hqj)).2 hon⟩
  | off j =>
    obtain ⟨q, hqj, h0⟩ := h₁
    exact ⟨q, hqj, (hother j q (fun e => hoff_ne (e ▸ rfl)) hqj).trans h0⟩
  | live j => exact flag_filt_live hp hself hhand hother hzero h₁ hlive
  | loc j => exact flag_filt_loc hp hself hhand hother hzero h₁ hlive

theorem flag_sound {t : CTop} (hab : Ab C.ps L gl t v) :
    SoundF C.ps L gl' lc ((if t == .zero then Fact.off k ::
      (if liveAfterClear C F k then [Fact.live k] else [])
      else if t == .nz then [Fact.on k] else []) ++
      F.filter fun f => f != .on k && f != .off k && (t == .zero || !isLive f || f == .live k)) := by
  have hzero : t = .zero → v = Val.i32 0 := fun h => by subst h; exact hab
  intro f hf
  rcases List.mem_append.1 hf with hf | hf
  · by_cases htz : t = .zero
    · subst htz
      exact flag_pre_zero hp hself hhand hother hS hF (hzero rfl) f (by simpa using hf)
    · by_cases htn : t = .nz
      · subst htn
        simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, List.mem_singleton] at hf
        subst hf
        obtain ⟨c, rfl, hc⟩ := hab
        exact ⟨p, hp, Val.i32 c, hself, i32_ne_zero hc⟩
      · simp [beq_iff_eq, htz, htn] at hf
  · exact flag_filt hp hself hhand hother hF hzero f hf

end Flag

theorem setF_sound_hand (hP : PairsOK C.ps) {s : Store H} {a k : Nat} {g : GlobalInst}
    (hg : s.globals[a]? = some g) (hk : pairOf C.ps a = some (k, false)) {F : List Fact}
    {t : CTop} {v : Val} (hS : Sigma C.ps L s.globals) (hF : SoundF C.ps L s.globals lc F)
    (hab : Ab C.ps L s.globals t v) (hreq : setReq C F t a = true) :
    Sigma C.ps L (s.setGlobal a v).globals ∧
      SoundF C.ps L (s.setGlobal a v).globals lc (setF C F t a) := by
  have hgv := gval_setGlobal hg v
  obtain ⟨p, hp, rfl⟩ := pairOf_false hk
  have hfr : t = .fr := by simpa [setReq, hk] using hreq
  subst hfr
  have hflag : ∀ (j : Nat) (q : Nat × Nat), C.ps[j]? = some q →
      gval (s.setGlobal p.2 v).globals q.1 = gval s.globals q.1 := fun j q hq => by
    rw [hgv, ite_f (pairs_uniq hP hq hp).2.2]
  have hother : ∀ (j : Nat) (q : Nat × Nat), j ≠ k → C.ps[j]? = some q →
      gval (s.setGlobal p.2 v).globals q.2 = gval s.globals q.2 := fun j q hjk hq => by
    rw [hgv, ite_f fun e => hjk ((pairs_uniq hP hq hp).2.1 e)]
  have hself : gval (s.setGlobal p.2 v).globals p.2 = some v := by rw [hgv, ite_t rfl]
  simp only [setF, hk]
  exact ⟨hand_sigma hp hself hflag hother hS hab.1, hand_sound hp hself hflag hother hF hab.1 hab.2⟩

theorem setF_sound_flag (hP : PairsOK C.ps) {s : Store H} {a k : Nat} {g : GlobalInst}
    (hg : s.globals[a]? = some g) (hk : pairOf C.ps a = some (k, true)) {F : List Fact}
    {t : CTop} {v : Val} (hS : Sigma C.ps L s.globals) (hF : SoundF C.ps L s.globals lc F)
    (hab : Ab C.ps L s.globals t v) (hreq : setReq C F t a = true) :
    Sigma C.ps L (s.setGlobal a v).globals ∧
      SoundF C.ps L (s.setGlobal a v).globals lc (setF C F t a) := by
  have hgv := gval_setGlobal hg v
  obtain ⟨p, hp, rfl⟩ := pairOf_true hk
  have hreq' : t = .zero ∨ Fact.live k ∈ F := by
    simpa [setReq, hk, List.contains_iff_mem] using hreq
  have hhand : ∀ (j : Nat) (q : Nat × Nat), C.ps[j]? = some q →
      gval (s.setGlobal p.1 v).globals q.2 = gval s.globals q.2 := fun j q hq => by
    rw [hgv, ite_f fun e => (pairs_uniq hP hp hq).2.2 e.symm]
  have hother : ∀ (j : Nat) (q : Nat × Nat), j ≠ k → C.ps[j]? = some q →
      gval (s.setGlobal p.1 v).globals q.1 = gval s.globals q.1 := fun j q hjk hq => by
    rw [hgv, ite_f fun e => hjk ((pairs_uniq hP hq hp).1 e)]
  have hself : gval (s.setGlobal p.1 v).globals p.1 = some v := by rw [hgv, ite_t rfl]
  have hzero : t = .zero → v = Val.i32 0 := fun h => by subst h; exact hab
  simp only [setF, hk]
  exact ⟨flag_sigma hp hself hhand hother hS hF hreq' hzero,
    flag_sound hp hself hhand hother hS hF hab⟩

/-- **`global.set` keeps the store invariant and the facts it computes.** -/
theorem setF_sound (hP : PairsOK C.ps) {s : Store H} {a : Nat} {g : GlobalInst}
    (hg : s.globals[a]? = some g) {F : List Fact} {t : CTop} {v : Val}
    (hS : Sigma C.ps L s.globals) (hF : SoundF C.ps L s.globals lc F)
    (hab : Ab C.ps L s.globals t v) (hreq : setReq C F t a = true) :
    Sigma C.ps L (s.setGlobal a v).globals ∧
      SoundF C.ps L (s.setGlobal a v).globals lc (setF C F t a) := by
  rcases hk : pairOf C.ps a with _ | ⟨k, b⟩
  · have hq : ∀ q ∈ C.ps, gval (s.setGlobal a v).globals q.1 = gval s.globals q.1 ∧
        gval (s.setGlobal a v).globals q.2 = gval s.globals q.2 := fun q hq => by
      obtain ⟨h₁, h₂⟩ := pairOf_none hk q hq
      simp [gval_setGlobal hg, h₁, h₂]
    simp only [setF, hk]
    exact ⟨sigma_congr hq hS, soundF_congr hq hF⟩
  · cases b
    · exact setF_sound_hand hP hg hk hS hF hab hreq
    · exact setF_sound_flag hP hg hk hS hF hab hreq

end Sem

/-! ## Variables, `if`, blocks, branches, calls -/

section Rules
variable {L : List Val} {lc : List (Option Val)}

theorem okX_label {gl : List GlobalInst} {gs : List Nat} {n : Nat} {cont : List Instr}
    {b : List Admin} : okX C L gl gs lc (.label n cont b) ↔ (okL C gs [] .other cont = true ∧
      ∃ F, SoundF C.ps L gl lc F ∧ okA C L gl gs lc ⟨F, .other, true⟩ b) := by
  rw [okX]

theorem okX_handler {gl : List GlobalInst} {gs : List Nat} {n : Nat} {cs : List Catch}
    {b : List Admin} : okX C L gl gs lc (.handler n cs b) ↔
      ∃ F, SoundF C.ps L gl lc F ∧ okA C L gl gs lc ⟨F, .other, true⟩ b := by
  rw [okX]

theorem okX_frame {gl : List GlobalInst} {gs : List Nat} {n : Nat} {fr : Frame}
    {b : List Admin} : okX C L gl gs lc (.frame n fr b) ↔
      ∃ F, SoundF C.ps L gl fr.locals F ∧ okA C L gl fr.module.globals fr.locals ⟨F, .other, true⟩ b := by
  rw [okX]

theorem global?_some {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : s.global? f x = some (a, g)) : f.module.globals[x.toNat]? = some a ∧
      s.globals[a]? = some g := by
  unfold Store.global? at h
  cases h1 : f.module.globals[x.toNat]? with
  | none => simp [h1] at h
  | some a' =>
    cases h2 : s.globals[a']? with
    | none => simp [h1, h2] at h
    | some g' =>
      simp [h1, h2] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, h2⟩

theorem other_ne_ex : CTop.other ≠ CTop.ex := nofun

theorem okA_label_pre {gl : List GlobalInst} {gs : List Nat} {F : List Fact} {t : CTop}
    (ht : t ≠ .ex) {n : Nat} {cont : List Instr} {b : List Admin} (l : List Admin) :
    okA C L gl gs lc ⟨F, t, true⟩ (.label n cont b :: l) ↔ okX C L gl gs lc (.label n cont b) ∧
      okA C L gl gs lc ⟨[], .other, false⟩ l := okA_nest_pre (x := .label n cont b) ht trivial l

theorem okA_handler_pre {gl : List GlobalInst} {gs : List Nat} {F : List Fact} {t : CTop}
    (ht : t ≠ .ex) {n : Nat} {cs : List Catch} {b : List Admin} (l : List Admin) :
    okA C L gl gs lc ⟨F, t, true⟩ (.handler n cs b :: l) ↔ okX C L gl gs lc (.handler n cs b) ∧
      okA C L gl gs lc ⟨[], .other, false⟩ l := okA_nest_pre (x := .handler n cs b) ht trivial l

theorem okA_frame_pre {gl : List GlobalInst} {gs : List Nat} {F : List Fact} {t : CTop}
    (ht : t ≠ .ex) {n : Nat} {fr : Frame} {b : List Admin} (l : List Admin) :
    okA C L gl gs lc ⟨F, t, true⟩ (.frame n fr b :: l) ↔ okX C L gl gs lc (.frame n fr b) ∧
      okA C L gl gs lc ⟨[], .other, false⟩ l := okA_nest_pre (x := .frame n fr b) ht trivial l

/-- **`global.get`**: the value gets the top computed by the check, semantically. -/
theorem post_globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hx : s.global? f x = some (a, g)) :
    CPost C L L (⟨s, f, [.plain (.globalGet x)]⟩ : Config H) ⟨s, f, [g.value.toAdmin]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  obtain ⟨hx₁, hx₂⟩ := global?_some hx
  rw [List.singleton_append, okA_plain ht (.inr rfl)] at h
  have hn : nextI C f.module.globals F t (.globalGet x) = (F, getTop C F a) := by
    simp [nextI, hx₁]
  rw [hn] at h
  have hgv : gval s.globals a = some g.value := by simp [gval, hx₂]
  exact ⟨hS, F, hF, (okA_val_pre other_ne_ex g.value l).2
    ⟨_, getTop_sound hS hF hgv, okA_pre_of_npre h.2⟩⟩

/-- **`global.set`**: the requirement keeps the store invariant (`setF_sound`). -/
theorem post_globalSet (hP : PairsOK C.ps) {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat}
    {g : GlobalInst} {v : Val} (hx : s.global? f x = some (a, g)) :
    CPost C L L (⟨s, f, [v.toAdmin, .plain (.globalSet x)]⟩ : Config H) ⟨s.setGlobal a v, f, []⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  obtain ⟨hx₁, hx₂⟩ := global?_some hx
  rw [List.cons_append, okA_val_pre ht] at h
  obtain ⟨t₁, hab, h⟩ := h
  have ht₁ : t₁ ≠ .ex := by rintro rfl; exact hab
  rw [List.singleton_append, okA_plain ht₁ (.inr rfl)] at h
  have hreq : setReq C F t₁ a = true := by simpa [okI, hx₁] using h.1
  have hn : nextI C f.module.globals F t₁ (.globalSet x) = (setF C F t₁ a, .other) := by
    simp [nextI, hx₁]
  rw [hn] at h
  obtain ⟨hS', hF'⟩ := setF_sound hP hx₂ hS hF hab hreq
  exact ⟨hS', _, hF', okA_pre_of_npre (okA_npre_indep l h.2)⟩

theorem thenF_sound {gl : List GlobalInst} {F : List Fact} {t : CTop} {c : BitVec 32}
    (hc : c ≠ 0) (hab : Ab C.ps L gl t (Val.i32 c)) (hF : SoundF C.ps L gl lc F) :
    SoundF C.ps L gl lc (thenF F t) := by
  cases t with
  | flag k =>
    obtain ⟨p, hp, hv⟩ := hab
    exact SoundF_cons ⟨p, hp, Val.i32 c, hv, i32_ne_zero hc⟩ hF
  | _ => exact hF

theorem elseF_sound {gl : List GlobalInst} {F : List Fact} {t : CTop}
    (hab : Ab C.ps L gl t (Val.i32 0)) (hF : SoundF C.ps L gl lc F) :
    SoundF C.ps L gl lc (elseF F t) := by
  cases t with
  | flag k =>
    obtain ⟨p, hp, hv⟩ := hab
    exact SoundF_cons ⟨p, hp, hv⟩ hF
  | _ => exact hF

theorem post_ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} (hc : c ≠ 0) :
    CPost C L L (⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩ : Config H)
      ⟨s, f, [.plain (.block bt b₁)]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [constI32, List.cons_append, okA_val_pre ht] at h
  obtain ⟨t₁, hab, h⟩ := h
  have ht₁ : t₁ ≠ .ex := by rintro rfl; exact hab
  rw [List.singleton_append, okA_plain ht₁ (.inr rfl)] at h
  have hz : t₁ ≠ .zero := by
    rintro rfl; exact i32_ne_zero hc hab
  have hb : okL C f.module.globals (thenF F t₁) .other b₁ = true := by
    have h₁ := h.1
    simp only [okI, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h₁
    exact h₁.1.resolve_left hz
  refine ⟨hS, _, thenF_sound hc hab hF, ?_⟩
  rw [List.singleton_append, okA_plain other_ne_ex (.inr rfl)]
  exact ⟨hb, h.2⟩

theorem post_ifFalse {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr} :
    CPost C L L (⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩ : Config H)
      ⟨s, f, [.plain (.block bt b₂)]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [constI32, List.cons_append, okA_val_pre ht] at h
  obtain ⟨t₁, hab, h⟩ := h
  have ht₁ : t₁ ≠ .ex := by rintro rfl; exact hab
  rw [List.singleton_append, okA_plain ht₁ (.inr rfl)] at h
  have hz : t₁ ≠ .nz := by
    rintro rfl
    obtain ⟨c, hc, hc0⟩ := hab
    exact i32_ne_zero hc0 hc.symm
  have hb : okL C f.module.globals (elseF F t₁) .other b₂ = true := by
    have h₁ := h.1
    simp only [okI, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h₁
    exact h₁.2.resolve_left hz
  refine ⟨hS, _, elseF_sound hab hF, ?_⟩
  rw [List.singleton_append, okA_plain other_ne_ex (.inr rfl)]
  exact ⟨hb, h.2⟩

/-- A block-like instruction after values: its check and the continuation. -/
theorem okA_vals_instr {gl : List GlobalInst} {gs : List Nat} {F : List Fact} {t : CTop}
    (ht : t ≠ .ex) {vs : List Val} {i : Instr} (hiv : (Admin.plain i).val? = none)
    {l : List Admin} (h : okA C L gl gs lc ⟨F, t, true⟩ (vals vs ++ [.plain i] ++ l)) :
    ∃ t', okI C gs F t' i = true ∧
      okA C L gl gs lc ⟨(nextI C gs F t' i).1, (nextI C gs F t' i).2, false⟩ l := by
  rw [List.append_assoc] at h
  obtain ⟨t₁, ht₁, h⟩ := okA_vals_pre vs ht h
  rw [List.singleton_append, okA_plain ht₁ (.inr hiv)] at h
  exact ⟨t₁, h⟩

theorem post_block {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {body : List Instr} {n : Nat} :
    CPost C L L (⟨s, f, vals vs ++ [.plain (.block bt body)]⟩ : Config H)
      ⟨s, f, [.label n [] (vals vs ++ expression body)]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  obtain ⟨t₁, hb, hl⟩ := okA_vals_instr ht rfl h
  refine ⟨hS, F, hF, ?_⟩
  rw [List.singleton_append, okA_label_pre other_ne_ex]
  exact ⟨okX_label.2 ⟨rfl, F, hF, okA_body hb .other vs⟩, hl⟩

theorem post_loop {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {body : List Instr} {n : Nat} :
    CPost C L L (⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩ : Config H)
      ⟨s, f, [.label n [.loop bt body] (vals vs ++ expression body)]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  obtain ⟨t₁, hb, hl⟩ := okA_vals_instr ht rfl h
  have hb' : okL C f.module.globals [] .other body = true := hb
  refine ⟨hS, F, hF, ?_⟩
  rw [List.singleton_append, okA_label_pre other_ne_ex]
  exact ⟨okX_label.2 ⟨by simp [okL, okI, hb'], [], SoundF_nil, okA_body hb' .other vs⟩, hl⟩

theorem post_tryTable {s : Store H} {f : Frame} {vs : List Val} {bt : BlockType}
    {cs : List Catch} {body : List Instr} {n : Nat} :
    CPost C L L (⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩ : Config H)
      ⟨s, f, [.handler n cs [.label n [] (vals vs ++ expression body)]]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  obtain ⟨t₁, hb, hl⟩ := okA_vals_instr ht rfl h
  refine ⟨hS, F, hF, ?_⟩
  rw [List.singleton_append, okA_handler_pre other_ne_ex]
  refine ⟨okX_handler.2 ⟨F, hF, ?_⟩, hl⟩
  rw [okA_label_pre other_ne_ex]
  exact ⟨okX_label.2 ⟨rfl, F, hF, okA_body hb .other vs⟩, trivial⟩

theorem post_brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs' vs : List Val} {lb : LabelIdx} {rest : List Admin} :
    CPost C L L
      (⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br lb)] ++ rest)]⟩ : Config H)
      ⟨s, f, vals vs ++ expression cont⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.singleton_append, okA_label_pre ht, okX_label] at h
  obtain ⟨⟨hcont, -⟩, hl⟩ := h
  refine ⟨hS, [], SoundF_nil, ?_⟩
  rw [List.append_assoc]
  exact okA_vals_other (okA_pre_of_npre (okA_expr hl cont hcont)) .other vs

theorem post_callRefFunc {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a k : Nat}
    {fi : FuncInst H} {lts : List ValType} {code : Func} (hc : c.IsCallRef)
    (hb : okL C fi.module.globals [] .other code.body = true) :
    CPost C L L (⟨s, f, vals vs ++ [.ref (.func a), c]⟩ : Config H)
      ⟨s, f, [.frame k (Frame.forCall fi.module vs lts) [.label k [] (expression code.body)]]⟩ := by
  refine post_kill rfl rfl rfl (killP_vals (by simp [vals])
    (killP_vals (V := [.ref (.func a)]) (by simp) (killP_callRef hc))) ?_
  refine freeP_nest trivial fun L gl gs _ => okX_frame.2 ⟨[], SoundF_nil, ?_⟩
  rw [okA_label_pre other_ne_ex]
  refine ⟨okX_label.2 ⟨rfl, [], SoundF_nil, ?_⟩, trivial⟩
  have h₀ := okA_body (L := L) (gl := gl) (lc := (Frame.forCall fi.module vs lts).locals) hb
    .other []
  simp only [vals, List.map_nil, List.nil_append] at h₀
  exact h₀

/-! ### Locals -/

/-- **`local.get`**: a local known to hold a live handle held by no flagged pair gives `fr`. -/
theorem post_localGet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hx : f.local? x = some (some v)) :
    CPost C L L (⟨s, f, [.plain (.localGet x)]⟩ : Config H) ⟨s, f, [v.toAdmin]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.singleton_append, okA_plain ht (.inr rfl)] at h
  refine ⟨hS, F, hF, (okA_val_pre other_ne_ex v l).2 ⟨_, ?_, okA_pre_of_npre h.2⟩⟩
  simp only [nextI]
  by_cases hc : F.contains (.loc x.toNat) = true
  · rw [ite_t hc]
    obtain ⟨w, hw, hwL, hoth⟩ := hF _ (List.contains_iff_mem.1 hc)
    have hx' : f.locals[x.toNat]? = some (some v) := hx
    rw [hx'] at hw; cases hw
    exact ⟨hwL, hoth⟩
  · rw [ite_f hc]; trivial

theorem locF_sound {gl : List GlobalInst} {lc : List (Option Val)} {F : List Fact} {t : CTop}
    {i : Nat} {v : Val} (hi : i < lc.length) (hF : SoundF C.ps L gl lc F)
    (hab : Ab C.ps L gl t v) : SoundF C.ps L gl (lc.set i (some v)) (locF F t i) := by
  intro f hf
  rcases List.mem_append.1 hf with hf | hf
  · by_cases htf : t = .fr
    · subst htf
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_singleton] at hf
      subst hf
      exact ⟨v, by simp [hi], hab.1, hab.2⟩
    · simp [htf] at hf
  · obtain ⟨hf, hne⟩ := List.mem_filter.1 hf
    have h₁ := hF f hf
    cases f with
    | on j => exact h₁
    | off j => exact h₁
    | live j => exact h₁
    | loc j =>
      have hj : j ≠ i := by
        rintro rfl; simp at hne
      obtain ⟨w, hw, hwL, hoth⟩ := h₁
      exact ⟨w, by rw [List.getElem?_set_ne (Ne.symm hj)]; exact hw, hwL, hoth⟩

/-- **`local.set`**: the local gets the facts of the value written. -/
theorem post_localSet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (hx : x.toNat < f.locals.length) :
    CPost C L L (⟨s, f, [v.toAdmin, .plain (.localSet x)]⟩ : Config H) ⟨s, f.setLocal x v, []⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.cons_append, okA_val_pre ht] at h
  obtain ⟨t₁, hab, h⟩ := h
  have ht₁ : t₁ ≠ .ex := by rintro rfl; exact hab
  rw [List.singleton_append, okA_plain ht₁ (.inr rfl)] at h
  exact ⟨hS, _, locF_sound hx hF hab, okA_pre_of_npre (okA_npre_indep l h.2)⟩

/-- **`local.tee`**: unfolds to a duplicated value and a `local.set` with the same check. -/
theorem post_localTee {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} :
    CPost C L L (⟨s, f, [v.toAdmin, .plain (.localTee x)]⟩ : Config H)
      ⟨s, f, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.cons_append, okA_val_pre ht] at h
  obtain ⟨t₁, hab, h⟩ := h
  have ht₁ : t₁ ≠ .ex := by rintro rfl; exact hab
  rw [List.singleton_append, okA_plain ht₁ (.inr rfl)] at h
  refine ⟨hS, F, hF, ?_⟩
  rw [List.cons_append, okA_val_pre other_ne_ex]
  refine ⟨t₁, hab, ?_⟩
  rw [List.cons_append, okA_val_pre ht₁]
  refine ⟨t₁, hab, ?_⟩
  rw [List.singleton_append, okA_plain ht₁ (.inr rfl)]
  exact ⟨rfl, h.2⟩

theorem post_call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {d : DefType}
    (hx : C.fs[x.toNat]? = some a) (hnb : C.isU a = false ∧ C.isF a = false ∧ C.isA a = false) :
    CPost C L L (⟨s, f, [.plain (.call x)]⟩ : Config H) ⟨s, f, [.ref (.func a), .callRefType d]⟩ :=
  post_kill rfl rfl rfl (killP_plain rfl fun _ _ _ => by simp [nextI, callNext, hx, hnb])
    (freeP_vals (V := [.ref (.func a)]) (by simp) (freeP_nest trivial fun _ _ _ _ => trivial))

theorem post_returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {d : DefType} :
    CPost C L L (⟨s, f, [.plain (.returnCall x)]⟩ : Config H)
      ⟨s, f, [.ref (.func a), .returnCallRefType d]⟩ :=
  post_kill rfl rfl rfl (killP_plain rfl fun _ _ _ => rfl)
    (freeP_vals (V := [.ref (.func a)]) (by simp) (freeP_nest trivial fun _ _ _ _ => trivial))

theorem post_handlerNext {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch}
    {a : Nat} : CPost C L L (⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ : Config H)
      ⟨s, f, [.handler n cs (throwing a)]⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.singleton_append, okA_handler_pre ht, okX_handler] at h
  refine ⟨hS, F, hF, ?_⟩
  rw [List.singleton_append, okA_handler_pre other_ne_ex, okX_handler]
  exact h

end Rules

/-! ## Context rules -/

section Ctxt
variable {L L' : List Val}

theorem post_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (ih : CPost C L L' (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩) :
    CPost C L L' (⟨s, f, vals vs ++ is ++ rest⟩ : Config H) ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨t₁, ht₁, h⟩ := okA_vals_pre vs ht h
  obtain ⟨hS', F', hF', h'⟩ := ih F t₁ (rest ++ l) ht₁ hS hF h
  refine ⟨hS', F', hF', ?_⟩
  rw [List.append_assoc, List.append_assoc]
  exact okA_vals_other h' .other vs

theorem post_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (ih : CPost C L L' (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩)
    (hm : f'.module.globals = f.module.globals) :
    CPost C L L' (⟨s, f, [.label n cont is]⟩ : Config H) ⟨s', f', [.label n cont is']⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.singleton_append, okA_label_pre ht, okX_label] at h
  obtain ⟨⟨hcont, Fb, hFb, hb⟩, hl⟩ := h
  obtain ⟨hS', Fb', hFb', hb'⟩ := ih Fb .other [] other_ne_ex hS hFb (by simpa using hb)
  refine ⟨hS', [], SoundF_nil, ?_⟩
  rw [List.singleton_append, okA_label_pre other_ne_ex, okX_label, hm]
  exact ⟨⟨hcont, Fb', hFb', by simpa [hm] using hb'⟩, okA_npre_indep l hl⟩

theorem post_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (ih : CPost C L L' (⟨s, f, is⟩ : Config H) ⟨s', f', is'⟩)
    (hm : f'.module.globals = f.module.globals) :
    CPost C L L' (⟨s, f, [.handler n cs is]⟩ : Config H) ⟨s', f', [.handler n cs is']⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.singleton_append, okA_handler_pre ht, okX_handler] at h
  obtain ⟨⟨Fb, hFb, hb⟩, hl⟩ := h
  obtain ⟨hS', Fb', hFb', hb'⟩ := ih Fb .other [] other_ne_ex hS hFb (by simpa using hb)
  refine ⟨hS', [], SoundF_nil, ?_⟩
  rw [List.singleton_append, okA_handler_pre other_ne_ex, okX_handler, hm]
  exact ⟨⟨Fb', hFb', by simpa [hm] using hb'⟩, okA_npre_indep l hl⟩

theorem post_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (ih : CPost C L L' (⟨s, fi, is⟩ : Config H) ⟨s', fi', is'⟩) :
    CPost C L L' (⟨s, f, [.frame n fi is]⟩ : Config H) ⟨s', f, [.frame n fi' is']⟩ := by
  intro F t l ht hS hF h
  simp only at hS hF h ⊢
  rw [List.singleton_append, okA_frame_pre ht, okX_frame] at h
  obtain ⟨⟨Fb, hFb, hb⟩, hl⟩ := h
  obtain ⟨hS', Fb', hFb', hb'⟩ := ih Fb .other [] other_ne_ex hS hFb (by simpa using hb)
  refine ⟨hS', [], SoundF_nil, ?_⟩
  rw [List.singleton_append, okA_frame_pre other_ne_ex, okX_frame]
  exact ⟨⟨Fb', hFb', by simpa using hb'⟩, okA_npre_indep l hl⟩

end Ctxt

/-! ## Every step -/

set_option linter.unusedTactic false in
/-- **Every host-free Core 3.0 step keeps the client invariant** (every profile), when the
reachability invariant holds before and after the step and the reachable functions are not the
three imports. -/
theorem Step.client {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop}
    {P : Numerics.Profile} {L : List Val} {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') (hP : PairsOK C.ps) (hfs : C.fs = fs)
    (hG : ∀ a, G a → C.isU a = false ∧ C.isF a = false ∧ C.isA a = false)
    (hc : CfgIn G fs Pl c) (hc' : CfgIn G fs Pl c') (hbf : BodiesC G C c.store.funcs) :
    CPost C L L c c' := by
  induction h with
  | parametric h => exact ParametricStep.client h
  | numeric h => exact NumericStep.client h
  | vector h => exact VectorStep.client h
  | «variable» h =>
    cases h with
    | localGet hx => exact post_localGet hx
    | localSet hx => exact post_localSet hx
    | localTee => exact post_localTee
    | globalGet hx => exact post_globalGet hx
    | globalSet hx => exact post_globalSet hP hx
  | table h => exact TableStep.client h
  | memory h => exact MemoryStep.client h
  | reference h => exact RefStep.client h
  | aggregate h => exact AggregateStep.client h
  | ctxtInstrs _ _ ih =>
    exact post_ctxtInstrs (ih ⟨hc.1, hc.2.1, (CodeIn.append.1 (CodeIn.append.1 hc.2.2).1).2⟩
      ⟨hc'.1, hc'.2.1, (CodeIn.append.1 (CodeIn.append.1 hc'.2.2).1).2⟩ hbf)
  | ctxtLabel hst ih =>
    exact post_ctxtLabel (ih ⟨hc.1, hc.2.1, (CodeIn.label_iff.1 hc.2.2).2⟩
      ⟨hc'.1, hc'.2.1, (CodeIn.label_iff.1 hc'.2.2).2⟩ hbf)
      (congrArg ModuleInst.globals (Step.module_eq hst))
  | ctxtHandler hst ih =>
    exact post_ctxtHandler (ih ⟨hc.1, hc.2.1, CodeIn.handler_iff.1 hc.2.2⟩
      ⟨hc'.1, hc'.2.1, CodeIn.handler_iff.1 hc'.2.2⟩ hbf)
      (congrArg ModuleInst.globals (Step.module_eq hst))
  | ctxtFrame _ ih =>
    exact post_ctxtFrame
      (ih ⟨hc.1, (CodeIn.frame_iff.1 hc.2.2).1, (CodeIn.frame_iff.1 hc.2.2).2⟩
        ⟨hc'.1, (CodeIn.frame_iff.1 hc'.2.2).1, (CodeIn.frame_iff.1 hc'.2.2).2⟩ hbf)
  | block => exact post_block
  | loop => exact post_loop
  | tryTable => exact post_tryTable
  | ifTrue hc₀ => exact post_ifTrue hc₀
  | ifFalse => exact post_ifFalse
  | brLabelZero => exact post_brLabelZero
  | @call _ f₀ x a _ hx _ =>
    have ha : G a := by simpa [refFuncs] using hc'.2.2.ref_of_mem (r := .func a) (by simp)
    have hx' : C.fs[x.toNat]? = some a := by
      rcases hc.2.1.1 with hm | hm
      · rw [hfs, ← hm]; exact hx
      · have hm' : f₀.module.funcs = [] := hm
        simp [hm'] at hx
    exact post_call hx' (hG a ha)
  | @callRefFunc _ _ _ _ a _ _ _ _ hcr hf _ _ hcode =>
    have ha : G a := by simpa [refFuncs] using hc.2.2.ref_of_mem (r := .func a) (by simp)
    exact post_callRefFunc hcr (hbf _ _ _ ha hf hcode)
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCall => exact post_returnCall
  | throw => exact post_throwingR rfl _
  | throwRefInstrs => exact post_throwingR rfl _
  | throwRefLabel => exact post_throwingR rfl _
  | throwRefFrame => exact post_throwingR rfl _
  | throwRefHandlerEmpty => exact post_throwingR rfl _
  | throwRefHandlerNext => exact post_handlerNext
  | returnCallRefLabel hcr =>
    exact post_kill rfl rfl rfl (killP_nest trivial) (freeP_vals (by simp [vals]) (freeP_retCallRef hcr))
  | returnCallRefHandler hcr =>
    exact post_kill rfl rfl rfl (killP_nest trivial) (freeP_vals (by simp [vals]) (freeP_retCallRef hcr))
  | returnCallRefFrameAddr hcr =>
    exact post_kill rfl rfl rfl (killP_nest trivial) (freeP_vals (by simp [vals])
      (freeP_vals (V := [.ref (.func _)]) (by simp) (freeP_retToCallIn _ hcr)))
  | callIndirect =>
    exact post_kill rfl rfl rfl (killP_plain rfl fun _ _ _ => rfl)
      (freeP_of_free (by verify_mem_split; all_goals client_free_one))
  | returnCallIndirect =>
    exact post_kill rfl rfl rfl (killP_plain rfl fun _ _ _ => rfl)
      (freeP_of_free (by verify_mem_split; all_goals client_free_one))
  | _ =>
    first
      | (exact post_trapR rfl; done)
      | (client_keep_tac; done)
      | (client_nest_tac; done)

end Silmaril.Wasm.Resource.Client
