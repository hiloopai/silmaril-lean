module

public import Silmaril.Raw.Wasm.Auto.Equiv.Ext.Run

/-!
# Soundness of the extended checks

* `wp_xsexec`: a symbolic run gives the weakest precondition of the code as `XOut` of the final
  state (the trap postcondition at the first failing guard, or the final configuration);
* **`segEquivX_of_checkX`**: the equivalence check is sound;
* **`segRefinesX_of_refinesX`**: the refinement check is sound (trapping code refined by code
  that traps at most where it does);
* `SegEquivX.cequiv`: without globals and memory, `SegEquivX` gives the typed-context
  equivalence `CEquiv` of `Silmaril.Wasm.Auto.Equiv`, so the congruence rules for `block`,
  `if`, `br_if` and `loop` apply.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem firstFail_append_none {ρ : Env} {B0 : ByteArray} :
    ∀ {G : List (Guard × XState)} (G' : List (Guard × XState)), firstFail ρ B0 G = none →
      firstFail ρ B0 (G ++ G') = firstFail ρ B0 G'
  | [], _, _ => rfl
  | (g, T) :: G, G', h => by
    simp only [firstFail] at h ⊢
    split at h
    · rename_i hg
      simp only [List.cons_append, firstFail, hg, ↓reduceIte]
      exact firstFail_append_none G' h
    · cases h

theorem firstFail_append_some {ρ : Env} {B0 : ByteArray} {T : XState} :
    ∀ {G : List (Guard × XState)} (G' : List (Guard × XState)), firstFail ρ B0 G = some T →
      firstFail ρ B0 (G ++ G') = some T
  | [], _, h => by cases h
  | (g, T') :: G, G', h => by
    simp only [firstFail] at h
    simp only [List.cons_append, firstFail]
    split at h
    · rename_i hg
      simp only [hg, ↓reduceIte]
      exact firstFail_append_some G' h
    · rename_i hg
      simp only [hg]
      exact h

theorem xsexec_guards {mem : Bool} : ∀ {S S' : XState} {a : List Instr}, xsexec mem S a = some S' →
    ∃ G, S'.guards = S.guards ++ G
  | S, S', [], h => by cases h; exact ⟨[], by simp⟩
  | S, S', i :: is, h => by
    simp only [xsexec] at h
    split at h
    · rename_i S₁ h₁
      obtain ⟨G, hG⟩ := xsexec_guards h
      rcases xstep_guards h₁ with h₂ | ⟨g, h₂⟩
      · exact ⟨G, by rw [hG, h₂]⟩
      · exact ⟨(g, { S with guards := [] }) :: G, by rw [hG, h₂]; simp⟩
    · cases h

theorem xsexec_globs {mem : Bool} : ∀ {S S' : XState} {a : List Instr}, xsexec mem S a = some S' →
    S'.globs.length = S.globs.length
  | S, S', [], h => by cases h; rfl
  | S, S', i :: is, h => by
    simp only [xsexec] at h
    split at h
    · rename_i S₁ h₁
      rw [xsexec_globs h, xstep_globs h₁]
    · cases h

/-- **A symbolic run.** -/
theorem wp_xsexec {m : Corr} {mem : Bool} {c : XCtx H} (hc : c.Good mem) (us : List Val)
    (rest : List Admin) (Q : Post H) :
    ∀ (a : List Instr) {S S' : XState}, S.globs.length = c.ga.length →
      firstFail c.ρ c.mi.bytes S.guards = none → xsexec mem S a = some S' →
      (Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ expression a ++ rest) Q ↔
        XOut m P host c mem S' us rest Q)
  | [], S, S', _, hf, h => by
    cases h
    simp [XOut, hf, expression]
  | i :: is, S, S', hl, hf, h => by
    simp only [xsexec] at h
    split at h
    · rename_i S₁ h₁
      have e : vals (us ++ (c.stackOf S).reverse) ++ expression (i :: is) ++ rest =
          vals (us ++ (c.stackOf S).reverse) ++ .plain i :: (expression is ++ rest) := by
        simp [expression]
      rw [e, wp_xstep hc hl h₁]
      have hl₁ : S₁.globs.length = c.ga.length := by rw [xstep_globs h₁, hl]
      rcases xstep_guards h₁ with hg | ⟨g, hg⟩
      · rw [xstepOut_noGuard hg]
        rw [← List.append_assoc]
        exact wp_xsexec hc us rest Q is hl₁ (by rw [hg]; exact hf) h
      · show XStepOut m P host c mem S S₁ us (expression is ++ rest) Q ↔
          XOut m P host c mem S' us rest Q
        rw [xstepOut_guard hg]
        by_cases hgh : g.holds c.ρ c.mi.bytes = true
        · rw [ite_eq_left hgh]
          have hf₁ : firstFail c.ρ c.mi.bytes S₁.guards = none := by
            rw [hg, firstFail_append_none _ hf]; simp [firstFail, hgh]
          rw [← List.append_assoc]
          exact wp_xsexec hc us rest Q is hl₁ hf₁ h
        · rw [ite_eq_right hgh]
          have hf₁ : firstFail c.ρ c.mi.bytes S₁.guards = some { S with guards := [] } := by
            rw [hg, firstFail_append_none _ hf]; simp [firstFail, hgh]
          obtain ⟨G, hG⟩ := xsexec_guards h
          have hf' : firstFail c.ρ c.mi.bytes S'.guards = some { S with guards := [] } := by
            rw [hG]; exact firstFail_append_some G hf₁
          simp only [XOut, hf']
          rfl
    · cases h

/-! ## Equal keys, equal concrete states -/

theorem map_denX_canonSlots (ρ : Env) (B0 : ByteArray) (l : List (IntType × XT)) :
    (canonSlots l).map (denX ρ B0) = l.map (denX ρ B0) := by
  simp [canonSlots, denX, evX_canon]

theorem frameOf_eq_of_key (c : XCtx H) {S T : XState}
    (h : canonSlots S.locals = canonSlots T.locals) : c.frameOf S = c.frameOf T := by
  have := congrArg (List.map (denX c.ρ c.mi.bytes)) h
  rw [map_denX_canonSlots, map_denX_canonSlots] at this
  have h' := congrArg (List.map some) this
  simp only [List.map_map] at h'
  simp only [XCtx.frameOf]
  rw [show (fun p => some (denX c.ρ c.mi.bytes p)) = some ∘ denX c.ρ c.mi.bytes from rfl, h']

theorem storeOf_eq_of_key (c : XCtx H) (mem : Bool) {S T : XState}
    (hg : canonSlots S.globs = canonSlots T.globs) (hm : canonM S.mem = canonM T.mem) :
    c.storeOf mem S = c.storeOf mem T := by
  have h₁ := congrArg (List.map (denX c.ρ c.mi.bytes)) hg
  rw [map_denX_canonSlots, map_denX_canonSlots] at h₁
  have h₂ := congrArg (evM c.ρ c.mi.bytes) hm
  rw [evM_canonM, evM_canonM] at h₂
  simp [XCtx.storeOf, h₁, h₂]

theorem stackOf_eq (c : XCtx H) {S T : XState} (h : canonSlots S.stack = canonSlots T.stack) :
    c.stackOf S = c.stackOf T := by
  have := congrArg (List.map (denX c.ρ c.mi.bytes)) h
  rw [map_denX_canonSlots, map_denX_canonSlots] at this
  exact this

theorem key_eq_parts {S T : XState} (h : S.key = T.key) :
    canonSlots S.locals = canonSlots T.locals ∧ canonSlots S.globs = canonSlots T.globs ∧
      canonM S.mem = canonM T.mem := by
  simp only [XState.key, Prod.mk.injEq] at h
  exact h

/-- Equal guard keys: the first failing guards correspond. -/
theorem firstFail_of_keys {ρ : Env} {B0 : ByteArray} :
    ∀ {G G' : List (Guard × XState)},
      G.map (fun g => (g.1.canon, g.2.key)) = G'.map (fun g => (g.1.canon, g.2.key)) →
      (firstFail ρ B0 G = none ∧ firstFail ρ B0 G' = none) ∨
        ∃ T T', firstFail ρ B0 G = some T ∧ firstFail ρ B0 G' = some T' ∧ T.key = T'.key
  | [], [], _ => Or.inl ⟨rfl, rfl⟩
  | (g, T) :: G, (g', T') :: G', h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hg, hT⟩, hG⟩ := h
    have hh : g.holds ρ B0 = g'.holds ρ B0 := by rw [← holds_canon, hg, holds_canon]
    simp only [firstFail]
    by_cases h₁ : g.holds ρ B0 = true
    · have h₂ : g'.holds ρ B0 = true := hh ▸ h₁
      simp only [h₁, h₂, ↓reduceIte]
      exact firstFail_of_keys hG
    · have h₂ : ¬ g'.holds ρ B0 = true := hh ▸ h₁
      simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
      exact Or.inr ⟨T, T', rfl, rfl, hT⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The initial state of a typed context. -/
theorem wp_init_iff {m : Corr} {lt st gt : List IntType} {mem : Bool} {c : XCtx H}
    (hc : c.Ok lt st gt mem) {a : List Instr} {A : XState} (ha : xsexec mem (initX lt st gt) a = some A)
    (us : List Val) (rest : List Admin) (Q : Post H) :
    Wp m P host c.s c.f (c.code lt st gt us a rest) Q ↔ XOut m P host c mem A us rest Q := by
  have h := wp_xsexec (m := m) (P := P) (host := host) (XCtx.Ok.good hc) us rest Q a
    (S := initX lt st gt) (by simp [initX, hc.2.2.1]) rfl ha
  rw [hc.1, hc.2.1] at h
  exact h

/-- **The equivalence check is sound.** -/
theorem segEquivX_of_checkX {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : checkX lt st gt mem a b = true) : SegEquivX lt st gt mem a b := by
  intro m P H host c us rest Q hc
  unfold checkX at h
  split at h
  · rename_i A B ha hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hgk, hk⟩, hs⟩ := h
    rw [wp_init_iff hc ha, wp_init_iff hc hb]
    obtain ⟨hl, hgl, hm⟩ := key_eq_parts hk
    unfold XOut
    rcases firstFail_of_keys (ρ := c.ρ) (B0 := c.mi.bytes) hgk with ⟨hA, hB⟩ | ⟨T, T', hA, hB, hT⟩
    · simp only [hA, hB]
      rw [frameOf_eq_of_key c hl, storeOf_eq_of_key c mem hgl hm, stackOf_eq c hs]
    · simp only [hA, hB]
      obtain ⟨hl', hgl', hm'⟩ := key_eq_parts hT
      rw [frameOf_eq_of_key c hl', storeOf_eq_of_key c mem hgl' hm']
  · cases h

theorem firstFail_none_iff {ρ : Env} {B0 : ByteArray} :
    ∀ {G : List (Guard × XState)}, firstFail ρ B0 G = none ↔ ∀ g ∈ G, g.1.holds ρ B0 = true
  | [] => by simp [firstFail]
  | (g, T) :: G => by
    simp only [firstFail, List.mem_cons, forall_eq_or_imp]
    split
    · rename_i hg
      simp only [hg, true_and]
      exact firstFail_none_iff
    · rename_i hg
      simp [hg]

/-- The guards of `B` all among the canonical guards of `A`: when `A`'s guards hold, so do
`B`'s. -/
theorem firstFail_none_of_sub {c : XCtx H} {A B : XState}
    (hsub : ∀ g ∈ B.guards, (A.guards.map fun h => h.1.canon).contains g.1.canon = true)
    (hA : firstFail c.ρ c.mi.bytes A.guards = none) : firstFail c.ρ c.mi.bytes B.guards = none := by
  refine firstFail_none_iff.mpr fun g hg => ?_
  have hmem : ∃ a ∈ A.guards, a.1.canon = g.1.canon := by
    simpa only [List.contains_iff_mem, List.mem_map] using hsub g hg
  obtain ⟨g', hg', heq⟩ := hmem
  rw [← holds_canon, ← heq, holds_canon]
  exact firstFail_none_iff.mp hA g' hg'

/-- The conditions of the refinement check on two runs `A`, `B` give the refinement of their
outcomes. -/
theorem xout_of_refinesX_parts {m : Corr} {c : XCtx H} {mem : Bool} {A B : XState} {us : List Val}
    {rest : List Admin} {Q : Post H}
    (hsub : ∀ g ∈ B.guards, (A.guards.map fun h => h.1.canon).contains g.1.canon = true)
    (hk : A.key = B.key) (hs : canonSlots A.stack = canonSlots B.stack)
    (hb' : XOut m P host c mem B us rest Q) : XOut m P host c mem A us rest (TrapOr Q) := by
  obtain ⟨hl, hgl, hm⟩ := key_eq_parts hk
  unfold XOut at hb' ⊢
  cases hA : firstFail c.ρ c.mi.bytes A.guards with
  | some T => exact Or.inl rfl
  | none =>
    have hB : firstFail c.ρ c.mi.bytes B.guards = none := firstFail_none_of_sub hsub hA
    simp only [hB] at hb'
    rw [frameOf_eq_of_key c hl, storeOf_eq_of_key c mem hgl hm, stackOf_eq c hs]
    exact Silmaril.Proofs.Wasm.Auto.Equiv.wp_mono (fun _ _ _ hq => Or.inr hq) hb'

/-- **The refinement check is sound.** -/
theorem segRefinesX_of_refinesX {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : refinesX lt st gt mem a b = true) : SegRefinesX lt st gt mem a b := by
  intro m P H host c us rest Q hc hb'
  cases ha : xsexec mem (initX lt st gt) a with
  | none => simp [refinesX, ha] at h
  | some A =>
    cases hb : xsexec mem (initX lt st gt) b with
    | none => simp [refinesX, ha, hb] at h
    | some B =>
      have h' : ((∀ g ∈ B.guards, (A.guards.map fun h => h.1.canon).contains g.1.canon = true) ∧
          A.key = B.key) ∧ canonSlots A.stack = canonSlots B.stack := by
        simpa only [refinesX, ha, hb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using h
      obtain ⟨⟨hsub, hk⟩, hs⟩ := h'
      rw [wp_init_iff hc ha]
      exact xout_of_refinesX_parts hsub hk hs ((wp_init_iff hc hb _ _ _).mp hb')

/-! ## Results (function bodies) -/

theorem firstFail_of_outKeys {ρ : Env} {B0 : ByteArray} :
    ∀ {G G' : List (Guard × XState)},
      G.map (fun g => (g.1.canon, g.2.outKey)) = G'.map (fun g => (g.1.canon, g.2.outKey)) →
      (firstFail ρ B0 G = none ∧ firstFail ρ B0 G' = none) ∨
        ∃ T T', firstFail ρ B0 G = some T ∧ firstFail ρ B0 G' = some T' ∧ T.outKey = T'.outKey
  | [], [], _ => Or.inl ⟨rfl, rfl⟩
  | (g, T) :: G, (g', T') :: G', h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hg, hT⟩, hG⟩ := h
    have hh : g.holds ρ B0 = g'.holds ρ B0 := by rw [← holds_canon, hg, holds_canon]
    simp only [firstFail]
    by_cases h₁ : g.holds ρ B0 = true
    · have h₂ : g'.holds ρ B0 = true := hh ▸ h₁
      simp only [h₁, h₂, ↓reduceIte]
      exact firstFail_of_outKeys hG
    · have h₂ : ¬ g'.holds ρ B0 = true := hh ▸ h₁
      simp only [h₁, h₂, ↓reduceIte, Bool.false_eq_true]
      exact Or.inr ⟨T, T', rfl, rfl, hT⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem wp_vals_iff' {m : Corr} {s : Store H} {F : Frame} {vs : List Val} {Q : Post H} :
    Wp m P host s F (vals vs) Q ↔ Q s F (.normal vs) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_vals_iff s F vs

/-- **The result check is sound.** -/
theorem outEquivX_of_checkOutX {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : checkOutX lt st gt mem a b = true) : OutEquivX lt st gt mem a b := by
  intro m P H host c us Q hc hQ
  unfold checkOutX at h
  split at h
  · rename_i A B ha hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hgk, hk⟩, hs⟩ := h
    rw [wp_init_iff hc ha, wp_init_iff hc hb]
    simp only [XState.outKey, Prod.mk.injEq] at hk
    unfold XOut
    rcases firstFail_of_outKeys (ρ := c.ρ) (B0 := c.mi.bytes) hgk with ⟨hA, hB⟩ | ⟨T, T', hA, hB, hT⟩
    · simp only [hA, hB, List.append_nil]
      rw [wp_vals_iff', wp_vals_iff', storeOf_eq_of_key c mem hk.1 hk.2, stackOf_eq c hs]
      exact hQ _ _ _ _ rfl
    · simp only [hA, hB]
      simp only [XState.outKey, Prod.mk.injEq] at hT
      rw [storeOf_eq_of_key c mem hT.1 hT.2]
      exact hQ _ _ _ _ rfl
  · cases h

/-! ## Without globals and memory: the typed-context equivalence -/

theorem map_denX_init (ρ : Env) (B0 : ByteArray) : ∀ (ts : List IntType) (k : Nat),
    (ts.mapIdx fun i t => (t, XT.var (k + i))).map (denX ρ B0) =
      (ts.mapIdx fun i t => (t, Term.var (k + i))).map (Silmaril.Wasm.Auto.Equiv.den ρ)
  | [], _ => rfl
  | t :: ts, k => by
    simp only [List.mapIdx_cons, List.map_cons, Nat.add_zero]
    have e₁ : (ts.mapIdx fun i t => (t, XT.var (k + (i + 1)))) = ts.mapIdx fun i t => (t, XT.var (k + 1 + i)) := by
      congr 1; funext i t; congr 2; omega
    have e₂ : (ts.mapIdx fun i t => (t, Term.var (k + (i + 1)))) = ts.mapIdx fun i t => (t, Term.var (k + 1 + i)) := by
      congr 1; funext i t; congr 2; omega
    rw [e₁, e₂, map_denX_init ρ B0 ts (k + 1)]
    rfl

/-- **`SegEquivX` without globals and memory gives `CEquiv`**, so the congruence rules of
`Silmaril.Wasm.Auto.Equiv` (`block`, `if`, `br_if`, `loop`) apply to it. -/
theorem SegEquivX.cequiv {lt st : List IntType} {a b : List Instr}
    (h : SegEquivX lt st [] false a b) : Silmaril.Wasm.Auto.Equiv.CEquiv lt st a b := by
  intro m P H host s f rs us rest Q hf hrs _
  obtain ⟨ls, hls, hlt⟩ := hf
  let c : XCtx H := ⟨s, f, envOfVals (ls ++ rs), [], 0, noMem⟩
  have hloc : (initX lt st []).locals.map (denX c.ρ c.mi.bytes) = ls := by
    have h₀ : List.map (denX c.ρ c.mi.bytes) (List.mapIdx (fun i t => (t, XT.var i)) lt) =
        List.map (den c.ρ) (List.mapIdx (fun i t => (t, Term.var i)) lt) := by
      simpa only [Nat.zero_add] using map_denX_init c.ρ c.mi.bytes lt 0
    simp only [initX]
    rw [h₀]
    exact locals_envOfVals hlt rs
  have hstk : c.stackOf (initX lt st []) = rs := by
    have h₁ : List.map (denX c.ρ c.mi.bytes)
        (List.mapIdx (fun i t => (t, XT.var (lt.length + i))) st) =
        List.map (den c.ρ) (List.mapIdx (fun i t => (t, Term.var (lt.length + i))) st) :=
      map_denX_init c.ρ c.mi.bytes st lt.length
    simp only [XCtx.stackOf, initX]
    rw [h₁]
    have h2 : List.map (den (envOfVals (ls ++ rs ++ [])))
        (List.mapIdx (fun i t => (t, Term.var (ls.length + i))) st) = rs :=
      map_den_envOfVals hrs ls []
    simpa [hlt.1] using h2
  have hc : c.Ok lt st [] false := by
    refine ⟨rfl, ?_, rfl, List.nodup_nil, fun k hk => by simp [c] at hk, fun h => by cases h⟩
    have h' : (initX lt st []).locals.map (fun p => some (denX c.ρ c.mi.bytes p)) = f.locals := by
      rw [hls, ← hloc, List.map_map]
      rfl
    simp only [XCtx.frameOf]
    rw [h']
  have hab : Wp m P host c.s c.f (c.code lt st [] us a rest) Q ↔
      Wp m P host c.s c.f (c.code lt st [] us b rest) Q := h m P host c us rest Q hc
  simpa [XCtx.code, hstk, Silmaril.Wasm.Auto.Equiv.cfgCode] using hab

end Silmaril.Proofs.Wasm.Auto.Equiv