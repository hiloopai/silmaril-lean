module

public import Silmaril.Proofs.Wasm.Verify.Check.Basic
public import Silmaril.Proofs.Wasm.Verify.Guard.Plays

/-!
# Soundness of the verifier for assertions

The Boolean checks of the guarded-call analysis imply the hypotheses of `GuardIn`
(`guardedB_sound`, `closedBA_sound`, `arityOne_sound`, `guardIn_of_closedBA`). On an instance the
verifier for assertions is the decision on its store (`check_assert_cases`); a `proved` decision
passed the guarded-call check or the flow check (`decideAssert_proved`), a `refuted` one found a
counterexample (`decideAssert_refuted`). The soundness theorem `check_assert_sound` combines both
analyses in `Silmaril.Proofs.Wasm.Verify.Check.Flow`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Spec Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-! ## Guards -/

theorem isHost_iff {s : Store Nat} {i a : Nat} : isHost s i a = true ↔ HostOf s.funcs i a := by
  unfold isHost HostOf
  constructor
  · intro h
    split at h
    · rename_i fi hfi
      split at h
      · rename_i h' hc
        exact ⟨fi, hfi, by rw [hc, beq_iff_eq.1 h]⟩
      · cases h
    · cases h
  · rintro ⟨fi, hfi, hc⟩
    simp [hfi, hc]

theorem gdI_of_isGuard {j : Instr} (h : isGuard (some j) = true) : GdI j := by
  unfold isGuard at h
  split at h
  · rename_i c heq
    cases heq
    exact ⟨c, rfl, bne_iff_ne.1 h⟩
  · cases h

theorem guardedB_cons {bad : Nat → Bool} {fs : List Nat} {prev : Option Instr} {j : Instr}
    {is : List Instr} (h : guardedB bad fs prev (j :: is) = true) :
    (∀ (y : FuncIdx) a, j = .call y → fs[y.toNat]? = some a → bad a = true → isGuard prev = true) ∧
      guardedB bad fs (some j) is = true := by
  simp only [guardedB, Bool.and_eq_true] at h
  refine ⟨fun y a hj hy hb => ?_, h.2⟩
  have h₁ := h.1
  subst hj
  simp only [hy, hb, Bool.not_true, Bool.false_or] at h₁
  exact h₁

/-- **The guard check is sound.** -/
theorem guardedB_sound {s : Store Nat} {fs : List Nat} {i : Nat} :
    ∀ {b : List Instr} {prev : Option Instr}, guardedB (isHost s i) fs prev b = true →
      ∀ l₁ j l₂, b = l₁ ++ j :: l₂ → BadI (HostOf s.funcs i) fs j →
        isGuard (l₁.getLast?.or prev) = true
  | [], _, _, l₁, j, l₂, hb, _ => by simp at hb
  | k :: b, prev, h, l₁, j, l₂, hb, hbad => by
    obtain ⟨hk, hrest⟩ := guardedB_cons h
    rcases l₁ with _ | ⟨x, l₁⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hb
      obtain ⟨y, a, rfl, hy, ha⟩ := hbad
      simpa using hk y a rfl hy (isHost_iff.2 ha)
    · obtain ⟨rfl, hb'⟩ := List.cons.inj hb
      have hih := guardedB_sound hrest l₁ j l₂ hb' hbad
      rcases l₁ with _ | ⟨z, l₁⟩
      · simpa using hih
      · obtain ⟨g, hg⟩ : ∃ g, (z :: l₁).getLast? = some g :=
          Option.isSome_iff_exists.1 (by simp)
        rw [hg, Option.some_or] at hih
        rw [List.getLast?_cons_cons, hg, Option.some_or]
        exact hih

theorem guarded_of_guardedB {s : Store Nat} {fs : List Nat} {i : Nat} {b : List Instr}
    (h : guardedB (isHost s i) fs none b = true) : Guarded (HostOf s.funcs i) fs b := by
  intro l₁ j l₂ hb hbad
  have hg := guardedB_sound h l₁ j l₂ hb hbad
  rcases hl : l₁.getLast? with _ | g
  · simp [hl, isGuard] at hg
  · exact ⟨g, rfl, gdI_of_isGuard (by simpa [hl] using hg)⟩

/-! ## The certificate check -/

theorem funcOkA_sound {s : Store Nat} {fs G : List Nat} {i a : Nat} {fi : FuncInst Nat}
    {code : Func} (h : funcOkA s fs G i a = true) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) :
    fi.module.funcs = fs ∧ (∀ ins ∈ code.body, PlOK (GuardPl (· ∈ G) (HostOf s.funcs i) fs) ins) ∧
      Guarded (HostOf s.funcs i) fs code.body := by
  simp only [funcOkA, hf, hcode, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hm, hrf⟩, hcall⟩, hgd⟩ := h
  refine ⟨hm, fun ins hins => .inr ⟨fun x hx b hb => ?_, fun x hx b hb => ?_, fun k hk => ?_⟩,
    guarded_of_guardedB (hgd _ (by simp))⟩
  · simpa [hb] using hrf x (mem_exprRF hins hx)
  · have h₁ := hcall x (mem_exprCalls hins hx)
    simp only [hb, Bool.or_eq_true, List.contains_iff_mem] at h₁
    exact h₁.imp id isHost_iff.1
  · exact guarded_of_guardedB (hgd k (by simp [mem_exprBodies hins hk]))

theorem closedBA_sound {s : Store Nat} {fs G : List Nat} {i : Nat} (h : closedBA s fs G i = true) :
    FuncsClosed (· ∈ G) fs (GuardPl (· ∈ G) (HostOf s.funcs i) fs) s.funcs ∧
      BodiesGuarded (· ∈ G) (HostOf s.funcs i) fs s.funcs := by
  refine ⟨fun a fi code ha hf hcode => ?_, fun a fi code ha hf hcode => ?_⟩
  · have hok := funcOkA_sound (List.all_eq_true.1 h a ha) hf hcode
    exact ⟨hok.1, hok.2.1⟩
  · exact (funcOkA_sound (List.all_eq_true.1 h a ha) hf hcode).2.2

theorem decideAssert_proved {s : Store Nat} {fs addrs : List Nat} {i : Nat}
    {imp : Option FnType} (h : (decideAssert s fs addrs i imp).verdict = .proved) :
    (∃ G, closedBA s fs G i = true ∧ rootsB G (rootsOf s addrs) = true ∧ avoidsB s G i = true) ∨
      ∃ G, closedBF s fs G i = true ∧ rootsB G (rootsOf s addrs) = true ∧
        avoidsB s G i = true := by
  unfold decideAssert at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact .inl ⟨_, hc.1.1, hc.1.2, hc.2⟩
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      exact .inr ⟨_, hc.1.1, hc.1.2, hc.2⟩
    · split at h
      · cases h
      · split at h <;> cases h

/-- A `refuted` decision for an assertion found a counterexample, and reports it. -/
theorem decideAssert_refuted {s : Store Nat} {fs addrs : List Nat} {i : Nat}
    {imp : Option FnType} (h : (decideAssert s fs addrs i imp).verdict = .refuted) :
    ∃ x, refuteOpt s addrs imp i falseCall = some x ∧
      decideAssert s fs addrs i imp = ⟨.refuted, .counterexample x⟩ := by
  unfold decideAssert at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i h₁
    simp only [h₁, Bool.false_eq_true, ↓reduceIte]
    split at h
    · cases h
    · rename_i h₂
      simp only [h₂, Bool.false_eq_true, ↓reduceIte]
      split at h
      · rename_i x hx
        exact ⟨x, hx, rfl⟩
      · split at h <;> cases h

/-! ## The arity of the assertion -/

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {k : Nat} {a : α} {b : β},
      l₁[k]? = some a → l₂[k]? = some b → R a b
  | [], [], .nil, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, .cons hab hrest, 0, _, _, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
    exact h₁ ▸ h₂ ▸ hab
  | _ :: _, _ :: _, .cons _ hrest, k + 1, _, _, h₁, h₂ => by
    simp only [List.getElem?_cons_succ] at h₁ h₂
    exact forall₂_getElem? hrest h₁ h₂

theorem arityOne_sound {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} (h : arityOne mt i = true) (hi : i < I.imports.length) :
    (I.imports.get ⟨i, hi⟩).params.length = 1 := by
  unfold arityOne at h
  split at h
  · rename_i d hd
    split at h
    · rename_i ft hft
      have hR : FnType.ofDefType? d = some (I.imports.get ⟨i, hi⟩) :=
        forall₂_getElem? hI.importTypes hd (by simp)
      rw [hR] at hft
      cases hft
      simpa using h
    · cases h
  · cases h

/-! ## Verdicts -/

/-- **On an instance, the verifier for assertions is the decision on its store** (or a
pre-check fails). -/
theorem check_assert_cases {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) (i : Nat) :
    (check m (.assertNeverFalse i)).verdict = .unknown ∨ arityOne mt i = true ∧
      ∃ fs, check m (.assertNeverFalse i) = decideAssert I.store fs I.addrs i (importType? mt i) := by
  obtain ⟨f, hinst, haddrs⟩ := hI.instantiated
  have hall : mt.imports.all isFuncImport = true := all_isFuncImport hI
  by_cases hi : mt.imports.length ≤ i
  · left
    simp only [check, hI.valid, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi]
  · by_cases har : arityOne mt i = true
    · right
      refine ⟨har, f.module.funcs, ?_⟩
      simp only [check, hI.valid, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, har,
        hinst, haddrs]
    · left
      have har' : arityOne mt i = false := by simpa using har
      simp only [check, hI.valid, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, har',
        Bool.not_false]

theorem check_assert_inv {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} (h : (check m (.assertNeverFalse i)).verdict = .proved) :
    arityOne mt i = true ∧ ∃ fs, (decideAssert I.store fs I.addrs i (importType? mt i)).verdict =
      .proved := by
  rcases check_assert_cases hI i with hc | ⟨har, fs, hc⟩
  · rw [hc] at h
    cases h
  · rw [hc] at h
    exact ⟨har, fs, h⟩

/-- The export addresses of a well-formed instance are among the roots. -/
theorem addr_mem_roots {I : ScalarInstance} (hok : I.Ok) {G : List Nat}
    (hr : rootsB G (rootsOf I.store I.addrs) = true) (j : Fin I.exports.length) : I.addr j ∈ G := by
  have hj : j.val < I.addrs.length := by rw [hok.addrs_length]; exact j.isLt
  have hmem : I.addr j ∈ I.addrs := by
    simp only [ScalarInstance.addr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]
    exact List.getElem_mem hj
  exact rootsB_mem hr _ (by simp [rootsOf, hmem])

/-- A `proved` decision with the guarded-call check gives `GuardIn`. -/
theorem guardIn_of_closedBA {m : Module} {mt : CModuleType} {I : ScalarInstance}
    (hI : IsInstance m mt I) {i : Nat} (har : arityOne mt i = true) {fs G : List Nat}
    (hc : closedBA I.store fs G i = true) (hr : rootsB G (rootsOf I.store I.addrs) = true)
    (ha : avoidsB I.store G i = true) : GuardIn I (· ∈ G) fs i := by
  have hok : I.Ok := hI.ok
  have hcl : FuncsClosed (· ∈ G) fs (GuardPl (· ∈ G) (HostOf I.store.funcs i) fs) I.store.funcs ∧
      BodiesGuarded (· ∈ G) (HostOf I.store.funcs i) fs I.store.funcs := closedBA_sound hc
  exact ⟨hok, hcl.1, hcl.2, storeIn_of_rootsB hr, addr_mem_roots hok hr,
    avoidsB_sound ha, arityOne_sound hI har⟩

end Silmaril.Wasm.Verify
